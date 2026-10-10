import OAI.Computability.Scheduling.DynamicProgram

namespace OAI

section

namespace ThreeMachine.Algorithm
section Closure
variable {n : ℕ}

def closureStep (E R : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  R ∪ Finset.univ.filter (fun p => ∃ v : Fin n, (p.1,v) ∈ R ∧ (v,p.2) ∈ E)

def closureTable (G : Instance n) (k : ℕ) : Finset (Fin n × Fin n) :=
  (closureStep G.edges.toFinset)^[k] G.edges.toFinset

def reachable (G : Instance n) (x y : Fin n) : Prop := (x,y) ∈ closureTable G n

instance (G : Instance n) : DecidableRel (reachable G) := fun x y =>
  inferInstanceAs (Decidable ((x,y) ∈ closureTable G n))

@[simp] theorem closureTable_zero (G : Instance n) : closureTable G 0 = G.edges.toFinset := rfl
@[simp] theorem closureTable_succ (G : Instance n) (k : ℕ) :
    closureTable G (k+1) = closureStep G.edges.toFinset (closureTable G k) :=
  Function.iterate_succ_apply' _ _ _

theorem closureStep_mono (E R : Finset (Fin n × Fin n)) : R ⊆ closureStep E R :=
  Finset.subset_union_left

theorem closureTable_mono (G : Instance n) {k l : ℕ} (h : k ≤ l) :
    closureTable G k ⊆ closureTable G l := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact Finset.Subset.refl _
  | succ d ih =>
    change closureTable G k ⊆ closureTable G ((k+d)+1)
    rw [closureTable_succ]
    exact ih.trans (closureStep_mono G.edges.toFinset (closureTable G (k+d)))

theorem closureTable_sound (G : Instance n) (k : ℕ) {x y : Fin n}
    (h : (x,y) ∈ closureTable G k) : G.order x y := by
  induction k generalizing x y with
  | zero => exact .single (by simpa [Instance.edge] using h)
  | succ k ih =>
    rw [closureTable_succ, closureStep, Finset.mem_union] at h
    rcases h with h | h
    · exact ih h
    · obtain ⟨v,hv,he⟩ := (Finset.mem_filter.mp h).2
      exact (ih hv).tail (by simpa [Instance.edge] using he)

theorem walk_closure (G : Instance n) {k : ℕ} {x y : Fin n}
    (h : Walk G.edge (k+1) x y) : (x,y) ∈ closureTable G k := by
  generalize he : k+1 = l at h
  induction h generalizing k with
  | refl => omega
  | @tail m x y z hp hz ih =>
    cases k with
    | zero =>
      have hm : m = 0 := by omega
      subst m
      cases hp
      simpa [Instance.edge] using hz
    | succ k =>
      have hm : k+1 = m := by omega
      have hh := ih hm
      rw [closureTable_succ, closureStep]
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hh,by simpa [Instance.edge] using hz⟩

theorem transGen_walk (G : Instance n) {x y : Fin n} (h : G.order x y) :
    ∃ k, Walk G.edge (k+1) x y := by
  induction h with
  | single he => exact ⟨0,.tail (.refl _) he⟩
  | tail _ he ih => obtain ⟨k,hk⟩ := ih; exact ⟨k+1,.tail hk he⟩

theorem reachable_iff (G : Instance n) (hG : G.acyclic) (x y : Fin n) :
    reachable G x y ↔ G.order x y := by
  classical
  constructor
  · exact closureTable_sound G n
  · intro h
    obtain ⟨k,hk⟩ := transGen_walk G h
    have hr : ∀ a b, G.edge a b → Structure.jobRank G.order a < Structure.jobRank G.order b :=
      fun _ _ he => Structure.jobRank_strict G.order hG
        (fun {_ _ _} h₁ h₂ => h₁.trans h₂) (.single he)
    have hb := hk.rank_bound hr
    have hy := Structure.jobRank_bounds G.order y
    apply closureTable_mono G (show k ≤ n by omega)
    exact walk_closure G hk

end Closure
end ThreeMachine.Algorithm

namespace ThreeMachine.Structure
section EffectiveFamily
variable {J : Type} [Fintype J] [DecidableEq J]

def Atomic.finsetEval (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) : Atomic J → Finset J
  | .constant b => if b then Finset.univ else ∅
  | .threshold frame upper k =>
    let ρ := if frame then reverseRank else rank
    Finset.univ.filter (fun x => if upper then ρ x ≤ k.val else k.val ≤ ρ x)
  | .cone frame kind Z =>
    let R := fun x y => if frame then r y x else r x y
    letI : DecidableRel R := fun x y => inferInstanceAs (Decidable (if frame then r y x else r x y))
    match kind.val with
    | 0 => Z.val
    | 1 => Finset.univ.filter (fun x => ∃ y ∈ Z.val, R x y)
    | 2 => Finset.univ.filter (fun x => ∃ y ∈ Z.val, R y x)
    | 3 => (Finset.univ.filter (fun x => ∃ y ∈ Z.val, R x y)) ∪ Z.val
    | _ => (Finset.univ.filter (fun x => ∃ y ∈ Z.val, R y x)) ∪ Z.val

theorem Atomic.coe_finsetEval (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (a : Atomic J) :
    (finsetEval r rank reverseRank a : Set J) = eval r rank reverseRank a := by
  cases a with
  | constant b => cases b <;> simp [finsetEval,eval]
  | threshold frame upper k =>
    cases frame <;> cases upper <;> ext x <;> simp [finsetEval,eval]
  | cone frame kind Z =>
    fin_cases kind <;> cases frame <;> ext x <;>
      simp [finsetEval,eval,Boundary.pred,Boundary.desc,Boundary.weakPred,Boundary.weakDesc]

instance Atomic.decideEval (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (a : Atomic J) : DecidablePred (eval r rank reverseRank a) :=
  fun x => decidable_of_iff (x ∈ finsetEval r rank reverseRank a) (by
    change x ∈ (finsetEval r rank reverseRank a : Set J) ↔ _
    rw [coe_finsetEval]
    rfl)

def Formula.evalFinset {A : Type} (atoms : A → Finset J) : Formula A → Finset J
  | .leaf a b => if b then (atoms a)ᶜ else atoms a
  | .conj p q => p.evalFinset atoms ∩ q.evalFinset atoms
  | .disj p q => p.evalFinset atoms ∪ q.evalFinset atoms

theorem Formula.coe_evalFinset {A : Type} (atoms : A → Finset J) (p : Formula A) :
    (p.evalFinset atoms : Set J) = p.eval (fun a => (atoms a : Set J)) := by
  induction p with
  | leaf a b => cases b <;> simp [evalFinset, eval]
  | conj p q ihp ihq | disj p q ihp ihq => simp [evalFinset, eval, ihp, ihq]

def effectiveFamily (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (jobs : List J) (K : ℕ) : List (Finset J) :=
  (assignments (Atomic.alphabet jobs) K).flatMap (fun f =>
    (Formula.templates K).map (fun s =>
      (s.map f).evalFinset (fun a => Finset.univ.filter (Atomic.eval r rank reverseRank a))))

open scoped Classical in
theorem effectiveFamily_complete (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (jobs : List J) (hjobs : ∀ x, x ∈ jobs)
    (K : ℕ) (W : Set J) (hW : Described (Atomic.eval r rank reverseRank) W K) :
    W.toFinset ∈ effectiveFamily r rank reverseRank jobs K := by
  classical
  obtain ⟨p,hp,hpk⟩ := hW
  obtain ⟨s,f,hs,he⟩ := Formula.template_representation p hpk
  apply List.mem_flatMap.mpr
  refine ⟨f,mem_assignments _ (Atomic.mem_alphabet jobs hjobs) K f,
    List.mem_map.mpr ⟨s,hs,?_⟩⟩
  apply Finset.coe_injective
  rw [Formula.coe_evalFinset,he]
  have ha : (fun a => (↑(Finset.univ.filter (Atomic.eval r rank reverseRank a)) : Set J)) =
      Atomic.eval r rank reverseRank := by
    funext a; ext x
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x))
  rw [ha,hp]
  simp

theorem effectiveFamily_length (r : J → J → Prop) [DecidableRel r]
    (rank reverseRank : J → ℕ) (jobs : List J) (K : ℕ) :
    (effectiveFamily r rank reverseRank jobs K).length =
      (Atomic.alphabet jobs).length^K * (Formula.templates K).length := by
  simp [effectiveFamily,List.length_flatMap,assignments_length]

end EffectiveFamily
end ThreeMachine.Structure

namespace ThreeMachine
instance {n m : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r] :
    DecidableRel (paddedOrder r m) := fun x y =>
  inferInstanceAs (Decidable (∃ a b : Fin n, x.val = a.val ∧ y.val = b.val ∧ r a b))
end ThreeMachine

namespace ThreeMachine.Algorithm
open Structure

def fullSolve {m : ℕ} (r : Fin m → Fin m → Prop) [DecidableRel r] : Option (Block (Fin m)) :=
  lookup (layers r
    (effectiveFamily r (jobRank r) (reverseJobRank r) (List.finRange m) 10000)
    ((tripleList (List.finRange m)).map Subtype.val) m) Finset.univ

theorem fullSolve_sound {m : ℕ} (r : Fin m → Fin m → Prop) [DecidableRel r]
    {s : Block (Fin m)} (hs : fullSolve r = some s) : s.Valid r Finset.univ :=
  layers_good r _ _ m _ _ (lookup_mem hs)

theorem fullSolve_complete {m : ℕ} (r : Fin m → Fin m → Prop) [DecidableRel r]
    (hirr : ∀ x, ¬r x x) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (h : ∃ p : Layout (Fin m), p.Full r) : ∃ s, fullSolve r = some s := by
  classical
  have ha := (accepted_iff_full_layout r (jobRank r) (reverseJobRank r) htrans
    (fun x => by simpa using (jobRank_bounds r x).2)
    (fun x => by simpa using (reverseJobRank_bounds r x).2)
    (jobRank_injective r) (reverseJobRank_injective r)
    (fun _ _ hxy => jobRank_strict r hirr htrans hxy)
    (fun _ _ hxy => reverseJobRank_strict r hirr htrans hxy)).mpr h
  have hh := layers_complete r (Atomic.eval r (jobRank r) (reverseJobRank r))
    (effectiveFamily r (jobRank r) (reverseJobRank r) (List.finRange m) 10000)
    ((tripleList (List.finRange m)).map Subtype.val)
    (fun F hF => effectiveFamily_complete r _ _ _ (fun _ => List.mem_finRange _) 10000 F hF)
    (fun Z => List.mem_map.mpr ⟨Z,mem_tripleList _ (fun _ => List.mem_finRange _) Z,rfl⟩) m
    (by simpa only [Fintype.card_fin] using ha)
  simpa only [Set.toFinset_univ,fullSolve,Has] using hh

theorem reachable_trans {n : ℕ} (G : Instance n) (hG : G.acyclic) :
    ∀ ⦃x y z⦄, reachable G x y → reachable G y z → reachable G x z := by
  intro x y z hxy hyz
  exact (reachable_iff G hG x z).mpr
    (((reachable_iff G hG x y).mp hxy).trans ((reachable_iff G hG y z).mp hyz))

theorem reachable_irrefl {n : ℕ} (G : Instance n) (hG : G.acyclic) :
    ∀ x, ¬reachable G x x := fun x hx => hG x ((reachable_iff G hG x x).mp hx)

def scheduleAt {n : ℕ} (G : Instance n) (T : ℕ) : Option (Fin n → ℕ) :=
  if hn : n ≤ 3*T then
    (fullSolve (paddedOrder (reachable G) (3*T))).map
      (fun s x => s.time (Fin.castLE hn x))
  else none

theorem Block.restrict_feasible {n T : ℕ} (G : Instance n) (hG : G.acyclic) (hn : n ≤ 3*T)
    {s : Block (Fin (3*T))} (hs : s.Valid (paddedOrder (reachable G) (3*T)) Finset.univ) :
    Feasible G T (fun x => s.time (Fin.castLE hn x)) := by
  obtain ⟨b,hbl,hbt⟩ := hs
  have hbT : b.length = T := by
    have hc := b.size
    simp only [Finset.coe_univ,Set.ncard_univ,Nat.card_eq_fintype_card,Fintype.card_fin] at hc
    omega
  have hbcap (t : ℕ) : (Finset.univ.filter (fun x => b.time x = t)).card ≤ 3 := by
    have hc := b.capacity t
    have he : {x | x ∈ (↑(Finset.univ : Finset (Fin (3*T))) : Set (Fin (3*T))) ∧ b.time x = t} =
        (Finset.univ.filter (fun x => b.time x = t) : Set (Fin (3*T))) := by ext x; simp
    rw [he,Set.ncard_coe_finset] at hc
    exact hc
  rw [← hbt]
  refine ⟨?_,?_,?_⟩
  · intro x
    simpa only [hbT] using b.bounds (Fin.castLE hn x) (by simp)
  · intro t
    apply le_trans _ (hbcap t)
    apply Finset.card_le_card_of_injOn (Fin.castLE hn)
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
    · intro x _ y _ hxy
      exact Fin.castLE_injective hn hxy
  · intro x y he
    apply b.respects _ (by simp) _ (by simp)
    apply (paddedOrder_castLE hn x y).mpr
    exact (reachable_iff G hG x y).mpr (.single he)

theorem scheduleAt_sound {n T : ℕ} (G : Instance n) (hG : G.acyclic)
    {time : Fin n → ℕ} (h : scheduleAt G T = some time) : Feasible G T time := by
  unfold scheduleAt at h
  split_ifs at h with hn
  · obtain ⟨s,hs,hstime⟩ := Option.map_eq_some_iff.mp h
    subst time
    exact Block.restrict_feasible G hG hn (fullSolve_sound _ hs)

theorem scheduleAt_complete {n T : ℕ} (G : Instance n) (hG : G.acyclic)
    (hf : ∃ time, Feasible G T time) : ∃ time, scheduleAt G T = some time := by
  obtain ⟨time,htime⟩ := hf
  have hn := htime.size_bound
  have hp := (feasible_iff_padded_layout G hn).mp ⟨time,htime⟩
  have hrel : paddedOrder (reachable G) (3*T) = paddedOrder G.order (3*T) := by
    have hr : reachable G = G.order := by funext x y; exact propext (reachable_iff G hG x y)
    rw [hr]
  obtain ⟨s,hs⟩ := fullSolve_complete (paddedOrder (reachable G) (3*T))
    (paddedOrder_irrefl (reachable_irrefl G hG)) (paddedOrder_trans (reachable_trans G hG))
    (by simpa only [hrel] using hp)
  exact ⟨fun x => s.time (Fin.castLE hn x),by simp [scheduleAt,hn,hs]⟩

theorem scheduleAt_none_iff {n T : ℕ} (G : Instance n) (hG : G.acyclic) :
    scheduleAt G T = none ↔ ¬∃ time, Feasible G T time := by
  constructor
  · intro hn he
    obtain ⟨time,htime⟩ := scheduleAt_complete G hG he
    rw [hn] at htime
    contradiction
  · intro he
    cases h : scheduleAt G T with
    | none => rfl
    | some time => exact (he ⟨time,scheduleAt_sound G hG h⟩).elim

end ThreeMachine.Algorithm

namespace ThreeMachine.Algorithm
open Structure

def best {n : ℕ} (G : Instance n) : ℕ → Option (ℕ × (Fin n → ℕ))
  | 0 => none
  | k+1 => match best G k with
    | some a => some a
    | none => (scheduleAt G (k+1)).map (fun time => (k+1,time))

def BestSpec {n : ℕ} (G : Instance n) (k : ℕ) : Option (ℕ × (Fin n → ℕ)) → Prop
  | none => ∀ T, 1 ≤ T → T ≤ k → ¬∃ time, Feasible G T time
  | some (T,time) => 1 ≤ T ∧ T ≤ k ∧ Feasible G T time ∧
      ∀ T' time', 1 ≤ T' → T' ≤ k → Feasible G T' time' → T ≤ T'

theorem best_spec {n : ℕ} (G : Instance n) (hG : G.acyclic) (k : ℕ) :
    BestSpec G k (best G k) := by
  induction k with
  | zero => intro T hT hTk; omega
  | succ k ih =>
    dsimp only [best]
    cases hb : best G k with
    | some a =>
      rw [hb] at ih
      rcases a with ⟨T,time⟩
      obtain ⟨hT,hTk,hfeas,hmin⟩ := ih
      refine ⟨hT,by omega,hfeas,?_⟩
      intro T' time' hT' hT'k hf'
      by_cases hh : T' ≤ k
      · exact hmin T' time' hT' hh hf'
      · omega
    | none =>
      rw [hb] at ih
      change ∀ T, 1 ≤ T → T ≤ k → ¬∃ time, Feasible G T time at ih
      cases hs : scheduleAt G (k+1) with
      | none =>
        intro T hT hTk
        by_cases he : T = k+1
        · subst T
          exact (scheduleAt_none_iff G hG).mp hs
        · exact ih T hT (by omega)
      | some time =>
        refine ⟨by omega,le_rfl,scheduleAt_sound G hG hs,?_⟩
        intro T' time' hT' hT'k hf'
        by_contra hlt
        exact ih T' hT' (by omega) ⟨time',hf'⟩

theorem serial_feasible {n : ℕ} (G : Instance n) (hG : G.acyclic) :
    Feasible G n (jobRank (reachable G)) := by
  refine ⟨jobRank_bounds _,?_,?_⟩
  · intro t
    apply le_trans (show _ ≤ 1 from ?_) (by omega : 1 ≤ 3)
    apply Finset.card_le_one.mpr
    intro x hx y hy
    apply jobRank_injective (reachable G)
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  · intro x y he
    exact jobRank_strict (reachable G) (reachable_irrefl G hG) (reachable_trans G hG)
      ((reachable_iff G hG x y).mpr (.single he))

theorem best_optimum {n : ℕ} (G : Instance n) (hn : 1 ≤ n) (hG : G.acyclic) :
    ∃ T time, best G n = some (T,time) ∧ Feasible G T time ∧
      ∀ T' time', Feasible G T' time' → T ≤ T' := by
  have hs := best_spec G hG n
  cases hb : best G n with
  | none =>
    rw [hb] at hs
    exact (hs n hn le_rfl ⟨_,serial_feasible G hG⟩).elim
  | some a =>
    rw [hb] at hs
    rcases a with ⟨T,time⟩
    obtain ⟨_,hTn,hf,hmin⟩ := hs
    refine ⟨T,time,rfl,hf,?_⟩
    intro T' time' hf'
    have hT' : 1 ≤ T' := by
      have := hf'.1 ⟨0,by omega⟩
      omega
    by_cases hle : T' ≤ n
    · exact hmin T' time' hT' hle hf'
    · omega

def output {n : ℕ} (G : Instance n) : Option ℕ → List Bool
  | some T => encodeAnswer ((scheduleAt G T).map slots)
  | none => encodeAnswer ((best G n).map (fun a => slots a.2))

theorem output_correct {n : ℕ} (G : Instance n) (hn : 1 ≤ n) (hG : G.acyclic)
    (deadline : Option ℕ) : CorrectOutput G deadline (output G deadline) := by
  cases deadline with
  | none =>
    obtain ⟨T,time,hbest,hf,hmin⟩ := best_optimum G hn hG
    exact ⟨T,time,hf,hmin,by simp [output,hbest]⟩
  | some T =>
    cases hs : scheduleAt G T with
    | none => exact Or.inl ⟨by simp [output,hs],(scheduleAt_none_iff G hG).mp hs⟩
    | some time => exact Or.inr ⟨time,scheduleAt_sound G hG hs,by simp [output,hs]⟩

end ThreeMachine.Algorithm

end

end OAI
