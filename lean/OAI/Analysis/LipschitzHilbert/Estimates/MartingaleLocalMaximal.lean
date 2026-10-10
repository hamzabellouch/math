import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

namespace OAI

/-! Restriction and time shift for a martingale, and the local weak-L1
maximal estimate used in the dyadic John--Nirenberg stopping argument. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

def timeShiftFiltration (ℱ : Filtration ℕ m) (n : ℕ) : Filtration ℕ m where
  seq i := ℱ (n + i)
  mono' := fun _ _ hij => ℱ.mono (Nat.add_le_add_left hij n)
  le' i := ℱ.le (n + i)

omit [IsFiniteMeasure μ] in
theorem martingale_timeShift (hF : Martingale F ℱ μ) (n : ℕ) :
    Martingale (fun i => F (n + i)) (timeShiftFiltration ℱ n) μ :=
  ⟨fun i => hF.stronglyMeasurable (n + i),
    fun _i _j hij => hF.condExp_ae_eq (Nat.add_le_add_left hij n)⟩

theorem martingale_restrict_initial (hF : Martingale F ℱ μ)
    {s : Set X} (hs : MeasurableSet[ℱ 0] s) : Martingale F ℱ (μ.restrict s) := by
  apply martingale_of_setIntegral_eq_succ hF.stronglyAdapted
    (fun i => (hF.integrable i).integrableOn)
  intro i t ht
  rw [Measure.restrict_restrict (ℱ.le i t ht)]
  exact hF.setIntegral_eq (Nat.le_succ i) (ht.inter (ℱ.mono (Nat.zero_le i) _ hs))

omit [IsFiniteMeasure μ] in
theorem martingale_abs (hF : Martingale F ℱ μ) :
    Submartingale (fun i x => |F i x|) ℱ μ := by
  have heq : (fun i x => |F i x|) = F ⊔ -F := by
    funext i x
    exact abs_eq_max_neg
  rw [heq]
  exact hF.submartingale.sup hF.neg.submartingale

theorem martingale_maximal_L1 (hF : Martingale F ℱ μ)
    {lambda : ℝ} (hlambda : 0 < lambda) (N : ℕ) :
    μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤ lambda⁻¹ * ∫ x, |F N x| ∂μ := by
  have hmax := maximal_ineq (martingale_abs hF) (fun i x => abs_nonneg (F i x))
    (ε := ⟨lambda,hlambda.le⟩) N
  change _ * μ {x | lambda ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun i => |F i x|)} ≤
    ENNReal.ofReal (∫ x in {x | lambda ≤ (Finset.range (N + 1)).sup'
      Finset.nonempty_range_add_one (fun i => |F i x|)}, |F N x| ∂μ) at hmax
  have hevent : {x | lambda ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun i => |F i x|)} = {x | ∃ i ≤ N, lambda ≤ |F i x|} := by
    ext x
    simp only [mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
  rw [hevent] at hmax
  have hwhole : (∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ) ≤
      ∫ x, |F N x| ∂μ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => abs_nonneg (F N x)) (hF.integrable N).abs
  have hsetnonneg : 0 ≤ ∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ :=
    integral_nonneg (fun x => abs_nonneg (F N x))
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  have hreal : lambda * μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤
      ∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hsetnonneg] at ht
    exact ht
  have hfinal : μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤
      (∫ x, |F N x| ∂μ) / lambda := by
    apply (le_div_iff₀ hlambda).mpr
    simpa only [mul_comm] using hreal.trans hwhole
  simpa only [div_eq_mul_inv, mul_comm] using hfinal

theorem martingale_local_maximal_L1 (hF : Martingale F ℱ μ) (n N : ℕ)
    {s : Set X} (hs : MeasurableSet[ℱ n] s) {lambda : ℝ} (hlambda : 0 < lambda) :
    (μ.restrict s).real {x | ∃ i ≤ N, lambda ≤ |F (n + i) x - F n x|} ≤
      lambda⁻¹ * ∫ x in s, |F (n + N) x - F n x| ∂μ := by
  have hshift := martingale_timeShift hF n
  have hconst : Martingale (fun _ => F n) (timeShiftFiltration ℱ n) μ :=
    martingale_const_fun _ _ (by
      change StronglyMeasurable[ℱ n] (F n)
      exact hF.stronglyMeasurable n) (hF.integrable n)
  have hcenter : Martingale (fun i x => F (n + i) x - F n x)
      (timeShiftFiltration ℱ n) μ := hshift.sub hconst
  exact martingale_maximal_L1 (martingale_restrict_initial hcenter
    (by change MeasurableSet[ℱ n] s; exact hs)) hlambda N

end LipschitzHilbert

end

end OAI
