import OAI.Computability.Scheduling.Padding

namespace OAI

section

namespace ThreeMachine.Structure
namespace Formula
variable {A B C : Type}

def map (f : A → B) : Formula A → Formula B
  | .leaf a s => .leaf (f a) s
  | .conj p q => .conj (p.map f) (q.map f)
  | .disj p q => .disj (p.map f) (q.map f)

@[simp] theorem leaves_map (f : A → B) (p : Formula A) : (p.map f).leaves = p.leaves := by
  induction p with
  | leaf => rfl
  | conj p q hp hq | disj p q hp hq => simp only [map, leaves, hp, hq]

@[simp] theorem map_comp (f : A → B) (g : B → C) (p : Formula A) :
    (p.map f).map g = p.map (g ∘ f) := by
  induction p with
  | leaf => rfl
  | conj p q hp hq | disj p q hp hq => simp only [map, hp, hq]

@[simp] theorem map_id (p : Formula A) : p.map id = p := by
  induction p with
  | leaf => rfl
  | conj p q hp hq | disj p q hp hq => simp only [map, hp, hq]

theorem occurrence_representation (p : Formula A) :
    ∃ (s : Formula (Fin p.leaves)) (f : Fin p.leaves → A),
      s.leaves = p.leaves ∧ s.map f = p := by
  induction p with
  | leaf a sign =>
    exact ⟨.leaf ⟨0, by simp [leaves]⟩ sign, fun _ => a, rfl, rfl⟩
  | conj p q hp hq =>
    obtain ⟨p', fp, hlp, hep⟩ := hp
    obtain ⟨q', fq, hlq, heq⟩ := hq
    refine ⟨.conj (p'.map (Fin.castAdd q.leaves)) (q'.map (Fin.natAdd p.leaves)),
      Fin.addCases fp fq, ?_, ?_⟩
    · simp only [leaves, leaves_map, hlp, hlq]
    · change ((p'.map (Fin.castAdd q.leaves)).map (Fin.addCases fp fq)).conj
        ((q'.map (Fin.natAdd p.leaves)).map (Fin.addCases fp fq)) = p.conj q
      rw [map_comp, map_comp]
      have hfp : (Fin.addCases fp fq) ∘ (Fin.castAdd q.leaves) = fp := by funext i; simp
      have hfq : (Fin.addCases fp fq) ∘ (Fin.natAdd p.leaves) = fq := by funext i; simp
      rw [hfp, hfq, hep, heq]
  | disj p q hp hq =>
    obtain ⟨p', fp, hlp, hep⟩ := hp
    obtain ⟨q', fq, hlq, heq⟩ := hq
    refine ⟨.disj (p'.map (Fin.castAdd q.leaves)) (q'.map (Fin.natAdd p.leaves)),
      Fin.addCases fp fq, ?_, ?_⟩
    · simp only [leaves, leaves_map, hlp, hlq]
    · change ((p'.map (Fin.castAdd q.leaves)).map (Fin.addCases fp fq)).disj
        ((q'.map (Fin.natAdd p.leaves)).map (Fin.addCases fp fq)) = p.disj q
      rw [map_comp, map_comp]
      have hfp : (Fin.addCases fp fq) ∘ (Fin.castAdd q.leaves) = fp := by funext i; simp
      have hfq : (Fin.addCases fp fq) ∘ (Fin.natAdd p.leaves) = fq := by funext i; simp
      rw [hfp, hfq, hep, heq]

def depthEnum (alphabet : List A) : ℕ → List (Formula A)
  | 0 => []
  | n+1 => alphabet.flatMap (fun a => [.leaf a false, .leaf a true]) ++
    (depthEnum alphabet n).flatMap (fun p =>
      (depthEnum alphabet n).flatMap (fun q => [.conj p q, .disj p q]))

theorem mem_depthEnum (alphabet : List A) (hA : ∀ a, a ∈ alphabet)
    (n : ℕ) (p : Formula A) (hp : p.leaves ≤ n) : p ∈ depthEnum alphabet n := by
  induction n generalizing p with
  | zero => have := p.leaves_pos; omega
  | succ n ih =>
    cases p with
    | leaf a sign =>
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      exact ⟨a, hA a, by cases sign <;> simp⟩
    | conj p q =>
      have hposp := p.leaves_pos
      have hposq := q.leaves_pos
      simp only [leaves] at hp
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨p, ih p (by omega), List.mem_flatMap.mpr ⟨q, ih q (by omega), ?_⟩⟩
      simp
    | disj p q =>
      have hposp := p.leaves_pos
      have hposq := q.leaves_pos
      simp only [leaves] at hp
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨p, ih p (by omega), List.mem_flatMap.mpr ⟨q, ih q (by omega), ?_⟩⟩
      simp

def templates (K : ℕ) : List (Formula (Fin K)) :=
  (depthEnum (List.finRange K) K).filter (fun p => p.leaves ≤ K)

theorem mem_templates {K : ℕ} (s : Formula (Fin K)) (hs : s.leaves ≤ K) :
    s ∈ templates K := by
  exact List.mem_filter.mpr ⟨mem_depthEnum _ (fun _ => List.mem_finRange _) K s hs,
    by simpa using hs⟩

theorem template_representation {K : ℕ} (p : Formula A) (hp : p.leaves ≤ K) :
    ∃ (s : Formula (Fin K)) (f : Fin K → A), s ∈ templates K ∧ s.map f = p := by
  obtain ⟨s, f, hs, hf⟩ := occurrence_representation p
  let default : A := f ⟨0, p.leaves_pos⟩
  let g : Fin K → A := fun i => if hi : i.val < p.leaves then f ⟨i.val, hi⟩ else default
  let s' := s.map (Fin.castLE hp)
  have hcomp : g ∘ (Fin.castLE hp) = f := by
    funext i
    simp only [Function.comp_apply, g, Fin.val_castLE, dite_eq_left i.isLt]
  refine ⟨s', g, ?_, ?_⟩
  · exact mem_templates s' (by simpa only [s', leaves_map, hs] using hp)
  · change (s.map (Fin.castLE hp)).map g = p
    rw [map_comp, hcomp, hf]

end Formula

def assignments {A : Type} (alphabet : List A) : (k : ℕ) → List (Fin k → A)
  | 0 => [Fin.elim0]
  | k+1 => alphabet.flatMap (fun a => (assignments alphabet k).map (Fin.cons a))

theorem assignments_length {A : Type} (alphabet : List A) (k : ℕ) :
    (assignments alphabet k).length = alphabet.length ^ k := by
  induction k with
  | zero => simp [assignments]
  | succ k ih => simp [assignments, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

theorem mem_assignments {A : Type} (alphabet : List A) (hA : ∀ a, a ∈ alphabet)
    (k : ℕ) (f : Fin k → A) : f ∈ assignments alphabet k := by
  induction k with
  | zero =>
    have he : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [assignments, he]
  | succ k ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, hA _, List.mem_map.mpr ⟨fun i => f i.succ, ih _, ?_⟩⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def formulaFamily {A J : Type} (alphabet : List A) (atoms : A → Set J) (K : ℕ) : List (Set J) :=
  (assignments alphabet K).flatMap (fun f => (Formula.templates K).map (fun s => (s.map f).eval atoms))

theorem mem_formulaFamily_iff {A J : Type} (alphabet : List A)
    (hA : ∀ a, a ∈ alphabet) (atoms : A → Set J) (K : ℕ) (W : Set J) :
    W ∈ formulaFamily alphabet atoms K ↔ Described atoms W K := by
  constructor
  · intro h
    obtain ⟨f, _, h⟩ := List.mem_flatMap.mp h
    obtain ⟨s, hs, he⟩ := List.mem_map.mp h
    refine ⟨s.map f, he, ?_⟩
    have hsk := (List.mem_filter.mp hs).2
    simpa only [Formula.leaves_map, decide_eq_true_eq] using hsk
  · rintro ⟨p, hp, hk⟩
    obtain ⟨s, f, hs, hf⟩ := Formula.template_representation p hk
    apply List.mem_flatMap.mpr
    refine ⟨f, mem_assignments alphabet hA K f, List.mem_map.mpr ⟨s, hs, ?_⟩⟩
    exact (congrArg (Formula.eval atoms) hf).trans hp

theorem formulaFamily_length {A J : Type} (alphabet : List A) (atoms : A → Set J) (K : ℕ) :
    (formulaFamily alphabet atoms K).length =
      alphabet.length ^ K * (Formula.templates K).length := by
  simp [formulaFamily, List.length_flatMap, assignments_length]

end ThreeMachine.Structure

namespace ThreeMachine.Structure
section EffectiveAlphabet
variable {J : Type} [Fintype J] [DecidableEq J]

def tripleList (jobs : List J) : List (Triple J) :=
  (jobs.flatMap (fun a => jobs.flatMap (fun b => jobs.map (fun c => ({a,b,c} : Finset J))))).filterMap
    (fun Z => if h : Z.card = 3 then some ⟨Z, h⟩ else none)

omit [Fintype J] in
theorem mem_tripleList (jobs : List J) (hjobs : ∀ x, x ∈ jobs) (Z : Triple J) :
    Z ∈ tripleList jobs := by
  obtain ⟨a,b,c,_,_,_,he⟩ := Finset.card_eq_three.mp Z.property
  apply List.mem_filterMap.mpr
  refine ⟨Z.val, List.mem_flatMap.mpr ⟨a, hjobs a,
    List.mem_flatMap.mpr ⟨b, hjobs b, List.mem_map.mpr ⟨c, hjobs c, he.symm⟩⟩⟩, ?_⟩
  simp only [dite_eq_left Z.property]

omit [Fintype J] in
theorem tripleList_length (jobs : List J) : (tripleList jobs).length ≤ jobs.length ^ 3 := by
  calc
    _ ≤ (jobs.flatMap (fun a => jobs.flatMap (fun b => jobs.map
          (fun c => ({a,b,c} : Finset J))))).length := List.length_filterMap_le _ _
    _ = jobs.length ^ 3 := by simp [List.length_flatMap, pow_succ, Nat.mul_assoc]

def Atomic.alphabet (jobs : List J) : List (Atomic J) :=
  [.constant false, .constant true] ++
  [false,true].flatMap (fun frame => [false,true].flatMap (fun upper =>
    (List.finRange (Fintype.card J + 2)).map (.threshold frame upper))) ++
  [false,true].flatMap (fun frame => (List.finRange 5).flatMap (fun kind =>
    (tripleList jobs).map (.cone frame kind)))

theorem Atomic.mem_alphabet (jobs : List J) (hjobs : ∀ x, x ∈ jobs) (a : Atomic J) :
    a ∈ alphabet jobs := by
  cases a with
  | constant b => cases b <;> simp [alphabet]
  | threshold frame upper k =>
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨frame, by cases frame <;> simp, List.mem_flatMap.mpr
      ⟨upper, by cases upper <;> simp, List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩⟩⟩
  | cone frame kind Z =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨frame, by cases frame <;> simp, List.mem_flatMap.mpr
      ⟨kind, List.mem_finRange _, List.mem_map.mpr ⟨Z, mem_tripleList jobs hjobs Z, rfl⟩⟩⟩

theorem Atomic.alphabet_length (jobs : List J) :
    (alphabet jobs).length ≤ 2 + 4*(Fintype.card J+2) + 10*jobs.length^3 := by
  have h := tripleList_length jobs
  have he : (alphabet jobs).length = 2 + 4*(Fintype.card J+2) + 10*(tripleList jobs).length := by
    simp [alphabet, List.finRange_succ, Nat.mul_add]
    omega
  rw [he]
  omega

theorem Atomic.alphabet_polynomial (n : ℕ) :
    (alphabet (List.finRange n)).length ≤ 20*(n+2)^3 := by
  have h := alphabet_length (List.finRange n)
  simp only [Fintype.card_fin, List.length_finRange] at h
  nlinarith [sq_nonneg (n : ℤ)]

end EffectiveAlphabet
end ThreeMachine.Structure

end

end OAI
