import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetMeasurable

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeBudgetWordLaw_zero_univ {d k : ℕ} (e f : Direction d) (r : ℝ) (hr : 0 ≤ r)
    (ω : Environment d) (x : Fin k → Lattice d) :
    relativeBudgetWordLaw e f 0 r ω x Set.univ = 1 := by
  apply le_antisymm (relativeBudgetWordLaw_le_one e f 0 r ω x)
  let w : Fin k → List (Direction d) := fun _ => []
  have hb : TupleRelativeBudget e f x 0 r w := by
    intro s hs i j
    have : s=0 := by omega
    subst s
    simpa [relativeWordDisplacement,wordFirstHitPosition,wordFirstHitTime_zero,w] using hr
  have hw (j : Fin k) : wordPath (x j) (w j) ∈ HitAt
      (Strip (realPosition (step e)) (x j) (0:ℕ))
      (Upper (realPosition (step e)) (x j) (0:ℕ)) (w j).length := by
    constructor
    · simp [w,Upper,wordPath_zero]
    · intro n hn; simp [w] at hn
  have ha : relativeBudgetWordLaw e f 0 r ω x {w}=1 := by
    rw [relativeBudgetWordLaw_singleton,ite_eq_left hb,rawTupleWordLaw_singleton]
    simp only [rawWordLaw_singleton,hw,ite_eq_left,w,wordWeight,ENNReal.ofReal_one,Finset.prod_const_one]
  rw [← ha]
  exact measure_mono (Set.subset_univ _)

lemma relativeBudgetMassENN_zero {d k : ℕ} (e f : Direction d) (r : ℝ) (hr : 0 ≤ r)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    relativeBudgetMassENN e f 0 r π ω=1 := by
  simp only [relativeBudgetMassENN,relativeBudgetWordLaw_zero_univ e f r hr]
  simp

lemma relativeBudgetWordLaw_mono {d k : ℕ} (e f : Direction d) (H : ℕ) {r q : ℝ} (hrq : r ≤ q)
    (ω : Environment d) (x : Fin k → Lattice d) :
    relativeBudgetWordLaw e f H r ω x ≤ relativeBudgetWordLaw e f H q ω x := by
  apply Measure.restrict_mono_set
  intro w hw s hs i j
  exact (hw s hs i j).trans hrq

lemma relativeBudgetMassENN_mono {d k : ℕ} (e f : Direction d) (H : ℕ) {r q : ℝ} (hrq : r ≤ q)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    relativeBudgetMassENN e f H r π ω ≤ relativeBudgetMassENN e f H q π ω :=
  lintegral_mono fun x => relativeBudgetWordLaw_mono e f H hrq ω x Set.univ

lemma relativeBudgetMassENN_restart_comp {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (a G r q : ℝ) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (π : BudgetProfile (k:=k) e f a G) (ω : Environment d) :
    relativeBudgetMassENN e f h r π.val ω *
      relativeBudgetMassENN e f m q (nextBudgetProfile e f h a G r hr π ω).val ω ≤
        relativeBudgetMassENN e f (h+m) (r+q) π.val ω := by
  have ht := budgetEndpointMixture_comp_le e f h m r q hq π.val ω Set.univ
  rw [budgetEndpointMixture_univ,budgetEndpointMixture_univ] at ht
  rw [← nextBudgetProfile_mass e f h a G r hr π ω] at ht
  simpa only [relativeBudgetMassENN,lintegral_smul_measure,smul_eq_mul] using ht

lemma budgetFirstThreat_eq_measurable {d k : ℕ} (e f : Direction d) (a G r s : ℝ)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H h : ℕ) : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+h))]
      {ω | budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω = h} := by
  have ht := budgetFirstThreat_stopping e f a r s _
    ((BudgetProfile.measurable_toSupported e f a G).comp hπ) H
  have he : {ω | (budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω : WithTop ℕ) = (h : WithTop ℕ)} =
      {ω | budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω = h} := by
    ext ω
    exact WithTop.coe_eq_coe
  have hm : @MeasurableSet (Environment d) (rowHeightFiltration (realPosition (step e)) a h)
      {ω | (budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω : WithTop ℕ) = (h : WithTop ℕ)} := ht.measurableSet_eq h
  rw [he] at hm
  exact hm

lemma budgetFirstThreat_lt_threat {d k : ℕ} (e f : Direction d) (a G r s : ℝ)
    (π : Environment d → BudgetProfile (k:=k) e f a G) (H : ℕ) (ω : Environment d)
    (hlt : budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω < H) :
    ω ∈ budgetThreatEvent e f H r (π ω).val s := by
  let τ := budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω
  have hH : 1 ≤ H := by omega
  have hτ : 1 ≤ τ := le_hittingBtwn hH ω
  have hhit := hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  change budgetTraversalMass e f a r (fun ω => (π ω).toSupported) τ ω < ENNReal.ofReal s at hhit
  have hm : relativeBudgetMassENN e f τ r (π ω).val ω < ENNReal.ofReal s := by
    simpa only [budgetTraversalMass,ite_eq_right (show τ≠0 by omega),Set.mem_Iio,BudgetProfile.toSupported] using hhit
  refine ⟨τ,(hittingBtwn_le ω),?_⟩
  rw [← relativeBudgetMassENN_toReal]
  exact ENNReal.toReal_lt_of_lt_ofReal hm

lemma budgetFirstThreat_mass_lower {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G r s : ℝ) (hr : 0 ≤ r) (hs : s ≤ 1)
    (π : Environment d → BudgetProfile (k:=k) e f a G) (H : ℕ) (hH : 1 ≤ H)
    (ω : Environment d) (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ:ℝ≥0∞)^k * ENNReal.ofReal s ≤ relativeBudgetMassENN e f
      (budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω) r (π ω).val ω := by
  let τ := budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω
  have ht : 1 ≤ τ := le_hittingBtwn hH ω
  have hp : ENNReal.ofReal s ≤ relativeBudgetMassENN e f (τ-1) r (π ω).val ω := by
    by_cases h0 : τ-1=0
    · rw [h0,relativeBudgetMassENN_zero e f r hr]
      exact ENNReal.ofReal_le_one.mpr hs
    · have hh : τ-1 < τ := by omega
      exact before_budgetFirstThreat_pass e f a r s (fun ω => (π ω).toSupported) H ω (j:=τ-1) (by omega) hh
  have hu := relativeBudgetMassENN_upward e f hef (τ-1) r ω (π ω).val κ hκ
  rw [Nat.sub_add_cancel ht] at hu
  exact (mul_le_mul_right hp _).trans hu

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def budgetRetryEvent {d k : ℕ} (e f : Direction d) (r s : ℝ) (hr : 0 ≤ r) :
    (n H : ℕ) → (a G : ℝ) → (Environment d → BudgetProfile (k:=k) e f a G) → Set (Environment d)
  | 0,_,_,_,_ => Set.univ
  | n+1,H,a,G,π => ⋃ h : {h : ℕ // 0<h ∧ h<H},
      {ω | budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω = h.val} ∩
        budgetRetryEvent e f r s hr n (H-h.val) (a+h.val) (G-r)
          (fun ω => nextBudgetProfile e f h.val a G r hr (π ω) ω)

lemma rowSigma_below_mono_nat {d : ℕ} (e : Direction d) (a : ℝ) (h : ℕ) :
    rowSigma (BelowHeight (realPosition (step e)) a) ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+h)) :=
  rowSigma_mono fun x hx =>
    show dot (realPosition x) (realPosition (step e)) < a+h from
      lt_of_lt_of_le (show dot (realPosition x) (realPosition (step e)) < a from hx)
        (le_add_of_nonneg_right (Nat.cast_nonneg h))

lemma budgetRetryEvent_probability {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (r s g : ℝ) (hr : 0 ≤ r) (Hmax : ℕ) (c : ℝ≥0∞)
    (hb : ∀ (H : ℕ), H ≤ Hmax → ∀ (a G : ℝ), g ≤ G →
      ∀ π : BudgetProfile (k:=k) e f a G,
        environmentLaw ν (budgetThreatEvent e f H r π.val s) ≤ c)
    (n H : ℕ) (hH : H ≤ Hmax) (a G : ℝ) (hG : g+n*r ≤ G)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A) :
    environmentLaw ν (A ∩ budgetRetryEvent e f r s hr n H a G π) ≤ c^n*environmentLaw ν A := by
  induction n generalizing H a G A with
  | zero => simp [budgetRetryEvent]
  | succ n ih =>
    let τ := budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H
    let I := {h : ℕ // 0<h ∧ h<H}
    let E (h : I) : Set (Environment d) := A ∩ {ω | τ ω=h.val}
    have hE (h : I) : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+h.val))] (E h) :=
      ((rowSigma_below_mono_nat e a h.val) A hA).inter
        (budgetFirstThreat_eq_measurable e f a G r s π hπ H h.val)
    have hEm (h : I) : MeasurableSet (E h) := (rowSigma_le _) _ (hE h)
    have hEd : Pairwise (Function.onFun Disjoint E) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      rintro ω ⟨_,hi⟩ ⟨_,hj⟩
      exact hij (Subtype.ext (hi.symm.trans hj))
    have hnext (h : I) : environmentLaw ν
        (E h ∩ budgetRetryEvent e f r s hr n (H-h.val) (a+h.val) (G-r)
          (fun ω => nextBudgetProfile e f h.val a G r hr (π ω) ω)) ≤ c^n*environmentLaw ν (E h) := by
      apply ih (H-h.val) (Nat.sub_le _ _ |>.trans hH) (a+h.val) (G-r) _ _
        (nextBudgetProfile_measurable_below e f a G r hr h.val π hπ) (E h) (hE h)
      have hcast : (n+1:ℕ)=n+1 := rfl
      push_cast at hG
      nlinarith
    have hs : (⋃ h : I, E h) ⊆ {ω | ω ∈ A ∧ ω ∈ budgetThreatEvent e f H r (π ω).val s} := by
      intro ω hω
      obtain ⟨h,ha,ht⟩ := Set.mem_iUnion.mp hω
      refine ⟨ha,budgetFirstThreat_lt_threat e f a G r s π H ω ?_⟩
      change τ ω < H
      rw [ht]
      exact h.property.2
    have hGs : g ≤ G := by
      have hn : 0 ≤ (n+1:ℕ)*r := mul_nonneg (Nat.cast_nonneg _) hr
      linarith
    have hsum : (∑' h : I, environmentLaw ν (E h)) ≤ c*environmentLaw ν A := by
      rw [← measure_iUnion hEd hEm]
      exact (measure_mono hs).trans (fresh_random_budget_threat ν e f a G r s H π hπ A hA c
        (fun η _ => hb H hH a G hGs (π η)))
    have he : A ∩ budgetRetryEvent e f r s hr (n+1) H a G π =
        ⋃ h : I, E h ∩ budgetRetryEvent e f r s hr n (H-h.val) (a+h.val) (G-r)
          (fun ω => nextBudgetProfile e f h.val a G r hr (π ω) ω) := by
      simp only [budgetRetryEvent,Set.inter_iUnion,Set.inter_assoc,E,τ,I]
    rw [he]
    calc
      _ ≤ ∑' h : I, environmentLaw ν
          (E h ∩ budgetRetryEvent e f r s hr n (H-h.val) (a+h.val) (G-r)
            (fun ω => nextBudgetProfile e f h.val a G r hr (π ω) ω)) := measure_iUnion_le _
      _ ≤ ∑' h : I, c^n*environmentLaw ν (E h) := ENNReal.tsum_le_tsum hnext
      _ = c^n * ∑' h : I, environmentLaw ν (E h) := ENNReal.tsum_mul_left
      _ ≤ c^n*(c*environmentLaw ν A) := mul_le_mul_right hsum _
      _ = c^(n+1)*environmentLaw ν A := by rw [pow_succ,mul_assoc]

end DirectionalTransience

end

end OAI
