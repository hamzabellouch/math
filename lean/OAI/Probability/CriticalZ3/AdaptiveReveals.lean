import OAI.Probability.CriticalZ3.Coarse

namespace OAI

universe uF

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace AdaptiveReveals
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]

structure Scheme (E V S : Type) where
  reveal : S → Finset E
  parameter : S → E → Set.Icc (0 : ℝ) 1
  vertex : S → Option V
  bad : (s : S) → (reveal s → Bool) → Bool
  child : (s : S) → (reveal s → Bool) → S
  parameter_child : ∀ s a, parameter (child s a) =
    fixedParameter (parameter s) (reveal s) (ProductCylinder.extend (reveal s) a)

namespace Scheme
variable (P : Scheme E V S)

noncomputable def weight (s : S) (a : P.reveal s → Bool) : ℝ :=
  (ProductCylinder.law (P.parameter s)).real
    (pattern (P.reveal s) (ProductCylinder.extend (P.reveal s) a))

noncomputable def badMass (s : S) : ℝ :=
  ∑ a : P.reveal s → Bool, if P.bad s a = true then P.weight s a else 0

omit [Countable E] [DecidableEq V] in
theorem weight_nonneg (s : S) (a : P.reveal s → Bool) : 0 ≤ P.weight s a := measureReal_nonneg

omit [DecidableEq V] in
theorem weight_sum (s : S) : ∑ a : P.reveal s → Bool, P.weight s a = 1 :=
  sum_pattern_real _ _

/-- Every target must first be tested by the time limit, and its first test
must have declared it bad.  Removing it prevents multiple visits from ever
being counted as distinct successes in this estimate. -/
noncomputable def hit : ℕ → S → Finset V → Set (E → Bool)
  | 0, _, U => if U = ∅ then Set.univ else ∅
  | n+1, s, U => match P.vertex s with
    | none => if U = ∅ then Set.univ else ∅
    | some v => {ω | (v ∈ U → P.bad s ((P.reveal s).restrict ω) = true) ∧
        ω ∈ hit n (P.child s ((P.reveal s).restrict ω)) (U.erase v)}

theorem measurableSet_hit (n : ℕ) (s : S) (U : Finset V) : MeasurableSet (P.hit n s U) := by
  induction n generalizing s U with
  | zero => simp only [hit]; split_ifs <;> simp
  | succ n ih =>
    simp only [hit]
    split
    · split_ifs <;> simp
    · rename_i v hv
      apply measurableSet_select (P.reveal s)
        (fun a => {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)})
      intro a
      by_cases h : v ∈ U → P.bad s a = true
      · convert ih (P.child s a) (U.erase v) using 1
        ext ω; exact and_iff_right h
      · simp only [h,false_and,Set.ofPred_false]; exact MeasurableSet.empty

omit [Countable E] in
theorem hit_empty (n : ℕ) (s : S) : P.hit n s ∅ = Set.univ := by
  induction n generalizing s with
  | zero => simp [hit]
  | succ n ih =>
    simp only [hit]
    cases P.vertex s <;> simp [ih]

/-- The only probabilistic hypotheses are the local bad probability and the
exact next-history product law.  Invalid zero-mass histories need no promise. -/
theorem hit_bound (I : S → Prop) (f : ℝ) (hf : 0 ≤ f)
    (hbad : ∀ s, I s → P.badMass s ≤ f)
    (hchild : ∀ s, I s → ∀ a, 0 < P.weight s a → I (P.child s a))
    (n : ℕ) (s : S) (hs : I s) (U : Finset V) :
    (ProductCylinder.law (P.parameter s)).real (P.hit n s U) ≤ f^U.card := by
  induction n generalizing s U with
  | zero =>
    by_cases hu : U = ∅
    · simp [hit,hu,probReal_univ]
    · simp only [hit,ite_eq_right hu,measureReal_empty]
      exact pow_nonneg hf _
  | succ n ih =>
    cases hv : P.vertex s with
    | none =>
      by_cases hu : U = ∅
      · simp [hit,hv,hu,probReal_univ]
      · simp only [hit,hv,ite_eq_right hu,measureReal_empty]
        exact pow_nonneg hf _
    | some v =>
      let A : (P.reveal s → Bool) → Set (E → Bool) :=
        fun a => {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)}
      have hA (a) : MeasurableSet (A a) := by
        by_cases ha : v ∈ U → P.bad s a = true
        · convert P.measurableSet_hit n (P.child s a) (U.erase v) using 1
          ext ω; exact and_iff_right ha
        · simp only [A,ha,false_and,Set.ofPred_false]; exact MeasurableSet.empty
      simp only [hit,hv]
      change (ProductCylinder.law (P.parameter s)).real
        {ω | ω ∈ A ((P.reveal s).restrict ω)} ≤ _
      rw [measure_select _ _ A hA]
      change (∑ a, P.weight s a *
        (ProductCylinder.law (fixedParameter (P.parameter s) (P.reveal s)
          (ProductCylinder.extend (P.reveal s) a))).real (A a)) ≤ _
      simp_rw [←P.parameter_child]
      have hterm (a) : P.weight s a *
          (ProductCylinder.law (P.parameter (P.child s a))).real (A a) ≤
          (if v ∈ U → P.bad s a = true then P.weight s a else 0) * f^(U.erase v).card := by
        by_cases hw : P.weight s a = 0
        · simp [hw]
        have hpos : 0 < P.weight s a := lt_of_le_of_ne (P.weight_nonneg s a) (Ne.symm hw)
        by_cases ha : v ∈ U → P.bad s a = true
        · have heqA : A a = P.hit n (P.child s a) (U.erase v) := by
            ext ω; exact and_iff_right ha
          rw [heqA,ite_eq_left ha]
          exact mul_le_mul_of_nonneg_left (ih (P.child s a) (hchild s hs a hpos) (U.erase v))
            (P.weight_nonneg s a)
        · simp only [A,ha,false_and,Set.ofPred_false,measureReal_empty,ite_false,mul_zero,zero_mul]
          exact le_rfl
      apply (Finset.sum_le_sum (fun a _ => hterm a)).trans
      rw [←Finset.sum_mul]
      by_cases hmem : v ∈ U
      · simp only [hmem,true_implies]
        change P.badMass s * f^(U.erase v).card ≤ f^U.card
        have hcard : (U.erase v).card + 1 = U.card := Finset.card_erase_add_one hmem
        rw [←hcard,pow_succ']
        exact mul_le_mul_of_nonneg_right (hbad s hs) (pow_nonneg hf _)
      · simp only [hmem,false_implies,ite_true,P.weight_sum,one_mul,Finset.erase_eq_of_notMem hmem]
        exact le_rfl

omit [DecidableEq V] in
theorem badMass_eq_probability (s : S) : P.badMass s =
    (ProductCylinder.law (P.parameter s)).real
      {ω | P.bad s ((P.reveal s).restrict ω) = true} := by
  have h := measure_select (P.parameter s) (P.reveal s)
    (fun a => if P.bad s a = true then Set.univ else ∅)
    (fun a => by split_ifs <;> simp)
  have heq : {ω : E → Bool | ω ∈ if P.bad s ((P.reveal s).restrict ω) = true then Set.univ else ∅} =
      {ω | P.bad s ((P.reveal s).restrict ω) = true} := by aesop
  rw [heq] at h
  rw [h]
  unfold badMass
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.bad s a = true <;> simp [weight,ha,probReal_univ]

omit [Countable E] in
theorem hit_subset_succ (n : ℕ) (s : S) (U : Finset V) :
    P.hit n s U ⊆ P.hit (n+1) s U := by
  induction n generalizing s U with
  | zero =>
    by_cases hU : U = ∅
    · subst U; rw [P.hit_empty,P.hit_empty]
    · simp only [hit,ite_eq_right hU]; exact Set.empty_subset _
  | succ n ih =>
    cases hv : P.vertex s with
    | none => simp only [hit,hv]; exact Set.Subset.rfl
    | some v =>
      simp only [hit,hv]
      intro ω hω
      exact ⟨hω.1,ih _ _ hω.2⟩

omit [Countable E] in
theorem hit_monotone (s : S) (U : Finset V) : Monotone (fun n => P.hit n s U) :=
  monotone_nat_of_le_succ (fun n => P.hit_subset_succ n s U)

/-- Uniform control survives an unbounded possible processing time. -/
theorem everHit_bound (I : S → Prop) (f : ℝ) (hf : 0 ≤ f)
    (hbad : ∀ s, I s → P.badMass s ≤ f)
    (hchild : ∀ s, I s → ∀ a, 0 < P.weight s a → I (P.child s a))
    (s : S) (hs : I s) (U : Finset V) :
    (ProductCylinder.law (P.parameter s)).real (⋃ n, P.hit n s U) ≤ f^U.card := by
  have hlim := (ENNReal.tendsto_toReal (measure_ne_top (ProductCylinder.law (P.parameter s))
    (⋃ n, P.hit n s U))).comp
    (tendsto_measure_iUnion_atTop (μ := ProductCylinder.law (P.parameter s)) (P.hit_monotone s U))
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun n => P.hit_bound I f hf hbad hchild n s hs U)

end Scheme
end AdaptiveReveals

namespace InfiniteConditioning
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem fixedParameter_merge (p : E → Set.Icc (0:ℝ) 1) (J K : Finset E)
    (ξ ω : E → Bool) : fixedParameter (fixedParameter p J ξ) K ω =
      fixedParameter p (J ∪ K) (replace K ω ξ) := by
  funext e
  by_cases hK : e ∈ K <;> by_cases hJ : e ∈ J <;>
    simp [fixedParameter,replace,hK,hJ]

structure History (E : Type) where
  known : Finset E
  values : E → Bool

namespace History
noncomputable def parameter (h : History E) (q : Set.Icc (0:ℝ) 1) :=
  fixedParameter (fun _ => q) h.known h.values
noncomputable def observe (h : History E) (R : Finset E) (ω : E → Bool) : History E :=
  ⟨h.known ∪ R,replace R ω h.values⟩
noncomputable def freeze (h : History E) (ω : E → Bool) := replace h.known h.values ω

omit [Countable E] in
theorem parameter_observe (h : History E) (q : Set.Icc (0:ℝ) 1) (R : Finset E) (ω : E → Bool) :
    (h.observe R ω).parameter q = fixedParameter (h.parameter q) R ω :=
  (fixedParameter_merge _ _ _ _ _).symm

omit [Countable E] in
theorem freeze_determined (h : History E) {J R : Finset E} {F : Sort uF}
    (f : (E → Bool) → F) (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hJ : J ⊆ h.known ∪ R) :
    ∀ ω ω', (∀ e ∈ R, ω' e = ω e) → f (h.freeze ω') = f (h.freeze ω) := by
  intro ω ω' he
  apply hf
  intro e heJ
  by_cases hk : e ∈ h.known
  · simp only [freeze,replace,ite_eq_left hk]
  · have hr := (Finset.mem_union.mp (hJ heJ)).resolve_left hk
    simp only [freeze,replace,ite_eq_right hk,he e hr]

omit [Countable E] in
theorem observe_outcome (h : History E) {J R : Finset E} {F : Sort uF}
    (f : (E → Bool) → F) (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hJ : J ⊆ h.known ∪ R) (hR : Disjoint R h.known) (ω : E → Bool) :
    f (h.observe R ω).values = f (h.freeze ω) := by
  apply hf
  intro e he
  rcases Finset.mem_union.mp (hJ he) with hk|hr
  · have hn : e ∉ R := fun hh => Finset.disjoint_left.mp hR hh hk
    simp only [observe,freeze,replace,ite_eq_right hn,ite_eq_left hk]
  · have hn : e ∉ h.known := fun hh => Finset.disjoint_left.mp hR hr hh
    simp only [observe,freeze,replace,ite_eq_right hn,ite_eq_left hr]

theorem ae_freeze (h : History E) (q : Set.Icc (0:ℝ) 1) :
    ∀ᵐ ω ∂ProductCylinder.law (h.parameter q), h.freeze ω = ω := by
  filter_upwards [ae_fixed_pattern (fun _ => q) h.known h.values] with ω hω
  exact replace_eq_of_pattern hω

theorem probability_freeze (h : History E) (q : Set.Icc (0:ℝ) 1) (A : Set (E → Bool)) :
    (ProductCylinder.law (h.parameter q)).real {ω | h.freeze ω ∈ A} =
      (ProductCylinder.law (h.parameter q)).real A := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [h.ae_freeze q] with ω hω
  rw [hω]
end History
end InfiniteConditioning

end OAI
