import OAI.Analysis.CircleDomains.Selection.MarkedConfigurations
import OAI.Analysis.CircleDomains.Modulus.ConfigurationNorm
import Mathlib.Topology.MetricSpace.Infsep

namespace OAI

/-! Testing all sizes and reciprocal separation scales is sufficient to control
the full square norm of the point-hit probabilities. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, Y)]
  (ι : C(X, Y)) (μ : ProbabilityMeasure C(PathTime, Y)) {B : ℝ}

/-- The square norm is tested only on the marked compact space. -/
def HasHitNormBound (B : ℝ) : Prop :=
  ∀ F : Finset X, ∑ x ∈ F, pathHitReal ι μ x ^ 2 ≤ B ^ 2

theorem HasHitNormBound.summable_sq (h : HasHitNormBound ι μ B) :
    Summable (fun x => pathHitReal ι μ x ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) h

theorem HasHitNormBound.countable_positive_support (h : HasHitNormBound ι μ B) :
    {x | 0 < pathHitProbability ι μ x}.Countable := by
  apply h.summable_sq.countable_support.mono
  intro x hx
  change pathHitReal ι μ x ^ 2 ≠ 0
  apply pow_ne_zero
  exact ne_of_gt (ENNReal.toReal_pos (ne_of_gt hx)
    (ne_of_lt (lt_of_le_of_lt (pathHitProbability_le_one ι μ x) (by simp))))

/-- This hypothesis runs over a countable list of compact configuration spaces. -/
def HasConfigurationBounds (B : ℝ) : Prop :=
  ∀ n m : ℕ, ∀ p : HitConfiguration X n (1 / ((m : ℝ) + 1)),
    weightedConfigurationHits ι (fun _ : Unit => μ) () p ≤ B

theorem configuration_bound_of_injective
    (h : HasConfigurationBounds ι μ B) {n : ℕ} (x : Fin n → X) (hx : Injective x)
    (w : Fin n → Icc (0 : ℝ) 1) (hw : (∑ i, (w i : ℝ) ^ 2) ≤ 1) :
    ∑ i, (w i : ℝ) * pathHitReal ι μ (x i) ≤ B := by
  obtain ⟨m, hm⟩ := exists_reciprocal_separation x hx
  exact h n m ⟨(x, w), hw, hm⟩

theorem configuration_square_sum_le
    (h : HasConfigurationBounds ι μ B) (hB : 0 ≤ B)
    {n : ℕ} (x : Fin n → X) (hx : Injective x) :
    ∑ i, pathHitReal ι μ (x i) ^ 2 ≤ B ^ 2 := by
  let v : Fin n → ℝ := fun i => pathHitReal ι μ (x i)
  let s : ℝ := Real.sqrt (∑ i, v i ^ 2)
  have hv (i) : 0 ≤ v i := pathHitReal_nonneg ι _ _
  have hsum : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs : s ^ 2 = ∑ i, v i ^ 2 := Real.sq_sqrt hsum
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  by_cases hsz : s = 0
  · have hz : (∑ i, v i ^ 2) = 0 := by nlinarith
    change (∑ i, v i ^ 2) ≤ B ^ 2
    rw [hz]
    positivity
  have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsz)
  have hvi (i) : v i ≤ s := by
    have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith
  let w : Fin n → Icc (0 : ℝ) 1 := fun i =>
    ⟨v i / s, div_nonneg (hv i) hs0, (div_le_one hsp).mpr (hvi i)⟩
  have hw : (∑ i, (w i : ℝ) ^ 2) ≤ 1 := by
    change (∑ i, (v i / s) ^ 2) ≤ 1
    simp_rw [div_pow]
    rw [← Finset.sum_div, ← hs, div_self (pow_ne_zero 2 hsz)]
  have hb := configuration_bound_of_injective ι μ h x hx w hw
  have heq : (∑ i, (w i : ℝ) * pathHitReal ι μ (x i)) = s := by
    change (∑ i, (v i / s) * v i) = s
    calc
      _ = (∑ i, v i ^ 2) / s := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = s := by rw [← hs]; field_simp
  rw [heq] at hb
  change (∑ i, v i ^ 2) ≤ B ^ 2
  nlinarith

theorem hasHitNormBound_of_configuration_bounds
    (h : HasConfigurationBounds ι μ B) (hB : 0 ≤ B) : HasHitNormBound ι μ B := by
  classical
  change ∀ F : Finset X, ∑ x ∈ F, pathHitReal ι μ x ^ 2 ≤ B ^ 2
  intro F
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  have he : Injective (fun i : Fin (Fintype.card F) => (e i).val) :=
    Subtype.val_injective.comp e.injective
  have hb := configuration_square_sum_le ι μ h hB (fun i => (e i).val) he
  rw [e.sum_comp (fun a : F => pathHitReal ι μ a.val ^ 2)] at hb
  rw [Finset.sum_coe_sort F (fun x : X => pathHitReal ι μ x ^ 2)] at hb
  exact hb

end CircleDomainRigidity.MarkedHit

end

end OAI
