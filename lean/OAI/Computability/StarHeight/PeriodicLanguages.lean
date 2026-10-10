import OAI.Computability.StarHeight.EndSearch

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uM uQ uQ2 uM2

namespace PeriodicTemplates

open scoped Computability Classical

variable {Alphabet : Type u}

def wordPower (c : List Alphabet) (i : ℕ) : List Alphabet :=
  ((FreeMonoid.ofList c) ^ i).toList

@[simp] lemma wordPower_zero (c : List Alphabet) : wordPower c 0 = [] := rfl

lemma wordPower_add (c : List Alphabet) (i j : ℕ) :
    wordPower c (i + j) = wordPower c i ++ wordPower c j := by
  simp only [wordPower, pow_add, FreeMonoid.toList_mul]

@[simp] lemma wordPower_one (c : List Alphabet) : wordPower c 1 = c := by
  simp [wordPower]

lemma wordPower_mul (c : List Alphabet) (i j : ℕ) :
    wordPower (wordPower c i) j = wordPower c (i * j) := by
  simp only [wordPower, FreeMonoid.ofList_toList, pow_mul]

lemma wordPower_replicate (c : List Alphabet) (i : ℕ) :
    wordPower c i = (List.replicate i c).flatten := by
  induction i with
  | zero => rfl
  | succ i hi => simp [wordPower_add, List.replicate_add, hi]

lemma singleton_star (c : List Alphabet) (w : List Alphabet) :
    w ∈ ({c} : Language Alphabet)∗ ↔ ∃ i, w = wordPower c i := by
  rw [Language.mem_kstar]
  constructor
  · rintro ⟨pieces, rfl, hp⟩
    have he : pieces = List.replicate pieces.length c :=
      List.eq_replicate_iff.mpr ⟨rfl, fun v hv => hp v hv⟩
    exact ⟨pieces.length, by rw [wordPower_replicate, he]; simp⟩
  · rintro ⟨i, rfl⟩
    refine ⟨List.replicate i c, wordPower_replicate c i, ?_⟩
    intro v hv
    change v = c
    exact (List.mem_replicate.mp hv).2

 def progression (a c b : List Alphabet) (i p : ℕ) : Language Alphabet :=
  {a ++ wordPower c i} * ({wordPower c p} : Language Alphabet)∗ * {b}

lemma mem_progression (a c b : List Alphabet) (i p : ℕ) (w : List Alphabet) :
    w ∈ progression a c b i p ↔ ∃ q, w = a ++ wordPower c (i + q * p) ++ b := by
  simp only [progression, Language.mem_mul]
  constructor
  · rintro ⟨v, ⟨a', ha, mid, hm, rfl⟩, b', hb, rfl⟩
    subst a'
    subst b'
    obtain ⟨q, rfl⟩ := (singleton_star _ _).mp hm
    exact ⟨q, by rw [wordPower_mul, wordPower_add, Nat.mul_comm q p]; simp only [List.append_assoc]⟩
  · rintro ⟨q, rfl⟩
    refine ⟨(a ++ wordPower c i) ++ wordPower c (p * q), ?_, b, rfl, ?_⟩
    · refine ⟨a ++ wordPower c i, rfl, wordPower c (p * q), ?_, rfl⟩
      apply (singleton_star _ _).mpr
      exact ⟨q, (wordPower_mul c p q).symm⟩
    · rw [wordPower_add, Nat.mul_comm q p]
      simp only [List.append_assoc]

lemma progression_height (a c b : List Alphabet) (i p : ℕ) :
    HasHeightAtMost (progression a c b i p) 1 :=
  ((HasHeightAtMost.singleton _ 1).concat
    ((HasHeightAtMost.singleton _ 0).star)).concat (HasHeightAtMost.singleton _ 1)

 def accepted (a c b : List Alphabet) (P : ℕ → Prop) : Language Alphabet :=
  {w | ∃ i, P i ∧ w = a ++ wordPower c i ++ b}

lemma accepted_height (a c b : List Alphabet) (P : ℕ → Prop) (N p : ℕ)
    (hp : 0 < p) (hperiod : ∀ i, N ≤ i → ∀ q, P (i + q * p) ↔ P i) :
    HasHeightAtMost (accepted a c b P) 1 := by
  classical
  let small := (Finset.range N).filter P
  let residues := (Finset.range p).filter (fun r => P (N + r))
  let L₀ : Language Alphabet := ⨆ i ∈ small, {a ++ wordPower c i ++ b}
  let L₁ : Language Alphabet := ⨆ r ∈ residues, progression a c b (N + r) p
  have h₀ : HasHeightAtMost L₀ 1 := HasHeightAtMost.finset_iSup small _
    (fun i _ => HasHeightAtMost.singleton _ 1)
  have h₁ : HasHeightAtMost L₁ 1 := HasHeightAtMost.finset_iSup residues _
    (fun r _ => progression_height a c b (N + r) p)
  have he : accepted a c b P = L₀ + L₁ := by
    ext w
    change (∃ i, P i ∧ w = a ++ wordPower c i ++ b) ↔ w ∈ L₀ ∨ w ∈ L₁
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases hsmall : i < N
      · left
        exact Language.mem_iSup.mpr ⟨i, Language.mem_iSup.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsmall, hi⟩, rfl⟩⟩
      · right
        let r := (i - N) % p
        let q := (i - N) / p
        have hir : i = N + r + q * p := by
          have hd := Nat.mod_add_div (i - N) p
          rw [Nat.mul_comm p] at hd
          dsimp [r, q]
          omega
        have hr : r < p := Nat.mod_lt _ hp
        have hrP : P (N + r) := by
          apply (hperiod (N + r) (by omega) q).mp
          rwa [← hir]
        exact Language.mem_iSup.mpr ⟨r, Language.mem_iSup.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hrP⟩,
            (mem_progression _ _ _ _ _ _).mpr ⟨q, by rw [← hir]⟩⟩⟩
    · rintro (hw | hw)
      · obtain ⟨i, hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨hi, he⟩ := Language.mem_iSup.mp hw
        exact ⟨i, (Finset.mem_filter.mp hi).2, he⟩
      · obtain ⟨r, hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨hr, hw⟩ := Language.mem_iSup.mp hw
        obtain ⟨q, he⟩ := (mem_progression _ _ _ _ _ _).mp hw
        exact ⟨N + r + q * p, (hperiod _ (by omega) q).mpr
          (Finset.mem_filter.mp hr).2, he⟩
  rw [he]
  exact h₀.union h₁

lemma recognized_template_height {M : Type uM} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) (F : Set M) (a c b : List Alphabet) :
    HasHeightAtMost (accepted a c b (fun i =>
      T (FreeMonoid.ofList a) * (T (FreeMonoid.ofList c)) ^ i * T (FreeMonoid.ofList b) ∈ F)) 1 := by
  apply accepted_height a c b _ (Fintype.card M) (Fintype.card M).factorial
    (Nat.factorial_pos _)
  intro i hi q
  rw [FiniteMonoidPeriod.pow_factorial _ hi]

end PeriodicTemplates

namespace FiniteRecognition

open scoped Computability

variable {Alphabet : Type u}

def transition {Q : Type uQ} (A : DFA Alphabet Q) :
    FreeMonoid Alphabet →* (Function.End Q)ᵐᵒᵖ where
  toFun w := MulOpposite.op (fun q => A.evalFrom q w.toList)
  map_one' := by apply MulOpposite.unop_injective; funext q; rfl
  map_mul' x y := by
    apply MulOpposite.unop_injective
    funext q
    exact A.evalFrom_of_append q x.toList y.toList

@[simp] lemma transition_apply {Q : Type uQ2} (A : DFA Alphabet Q) (w : List Alphabet) (q : Q) :
    (transition A (FreeMonoid.ofList w)).unop q = A.evalFrom q w := rfl

lemma of_regular {L : Language Alphabet} (hL : L.IsRegular) :
    ∃ (M : Type) (_ : Monoid M) (_ : Fintype M) (T : FreeMonoid Alphabet →* M) (F : Set M),
      ∀ w, w ∈ L ↔ T (FreeMonoid.ofList w) ∈ F := by
  classical
  obtain ⟨Q, hQ, A, rfl⟩ := hL
  let : Fintype Q := hQ
  let : Fintype (Function.End Q)ᵐᵒᵖ :=
    Fintype.ofEquiv (Q → Q) (Equiv.refl _ |>.trans MulOpposite.opEquiv)
  exact ⟨(Function.End Q)ᵐᵒᵖ, inferInstance, inferInstance, transition A,
    {f | f.unop A.start ∈ A.accept}, fun _ => Iff.rfl⟩

end FiniteRecognition

namespace PeriodicTemplates

open scoped Computability Classical

variable {Alphabet : Type u}

abbrev Template (Alphabet : Type u) := List Alphabet × List Alphabet × List Alphabet

def instanceWord (t : Template Alphabet) (i : ℕ) : List Alphabet :=
  t.1 ++ wordPower t.2.1 i ++ t.2.2

lemma recognized_cover_height {M : Type uM2} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) (F : Set M)
    (L : Language Alphabet) (hL : ∀ w, w ∈ L ↔ T (FreeMonoid.ofList w) ∈ F)
    (templates : Finset (Template Alphabet))
    (hcover : ∀ w ∈ L, ∃ t ∈ templates, ∃ i, w = instanceWord t i) :
    HasHeightAtMost L 1 := by
  let component := fun t : Template Alphabet => accepted t.1 t.2.1 t.2.2 (fun i =>
    T (FreeMonoid.ofList t.1) * (T (FreeMonoid.ofList t.2.1)) ^ i *
      T (FreeMonoid.ofList t.2.2) ∈ F)
  have hc : ∀ t ∈ templates, HasHeightAtMost (component t) 1 :=
    fun t _ => recognized_template_height T F t.1 t.2.1 t.2.2
  have beq : ∀ t i, T (FreeMonoid.ofList (instanceWord t i)) =
      T (FreeMonoid.ofList t.1) * (T (FreeMonoid.ofList t.2.1)) ^ i *
        T (FreeMonoid.ofList t.2.2) := by
    intro t i
    simp only [instanceWord, wordPower, FreeMonoid.ofList_append,
      FreeMonoid.ofList_toList, map_mul, map_pow]
  have he : L = ⨆ t ∈ templates, component t := by
    ext w
    constructor
    · intro hw
      obtain ⟨t, ht, i, rfl⟩ := hcover w hw
      refine Language.mem_iSup.mpr ⟨t, Language.mem_iSup.mpr ⟨ht, i, ?_, rfl⟩⟩
      change T (FreeMonoid.ofList t.1) * T (FreeMonoid.ofList t.2.1) ^ i *
        T (FreeMonoid.ofList t.2.2) ∈ F
      rw [← beq]
      exact (hL _).mp hw
    · intro hw
      obtain ⟨t, hw⟩ := Language.mem_iSup.mp hw
      obtain ⟨ht, i, hi, rfl⟩ := Language.mem_iSup.mp hw
      apply (hL _).mpr
      exact (beq t i).symm ▸ hi
  rw [he]
  exact HasHeightAtMost.finset_iSup templates component hc

lemma regular_cover_height (L : Language Alphabet) (hL : L.IsRegular)
    (templates : Finset (Template Alphabet))
    (hcover : ∀ w ∈ L, ∃ t ∈ templates, ∃ i, w = instanceWord t i) :
    HasHeightAtMost L 1 := by
  obtain ⟨M, hM, hF, T, F, hT⟩ := FiniteRecognition.of_regular hL
  exact recognized_cover_height T F L hT templates hcover

end PeriodicTemplates

end GeneralizedStarHeight

end OAI
