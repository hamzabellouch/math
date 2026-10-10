import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightIntegral
import OAI.Analysis.LipschitzHilbert.Estimates.TopAreaAverage
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The two different mass budgets used in the assembly: integrating
the top count on the testing set costs N|F|, whereas integrating all
weights on the plane costs N²|F|. Their polynomial losses are explicit. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert

theorem source_testing_weight_integral {τ : Type*} (tops : Finset τ) (T : τ → SlopeBox)
    (K D L c Nmass Fmass : ℝ) (hK : 0 < K) (hD : 2 < D) (hL : 0 < L)
    (hN : 0 ≤ Nmass) (good : Set (ℝ×ℝ)) (hgood : MeasurableSet good)
    (hfinite : (volume.prod volume) good ≠ ∞)
    (hmeasure : (volume.prod volume).real good ≤ Fmass)
    (hcount : ∀ x ∈ good, (∑ t ∈ tops, (T t).weight K D x) ≤ L^c*Nmass) :
    IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight K D x) good (volume.prod volume) ∧
      (∫ x in good, ∑ t ∈ tops, (T t).weight K D x ∂volume.prod volume) ≤ L^c*Nmass*Fmass := by
  have hi : IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight K D x) good (volume.prod volume) :=
    (integrable_finsetSum _ (fun t _ => (T t).weight_integrable hK hD)).integrableOn
  refine ⟨hi,?_⟩
  have hb := setIntegral_mono_on hi
    (integrableOn_const hfinite : IntegrableOn (fun _ : ℝ×ℝ => L^c*Nmass) good (volume.prod volume))
    hgood hcount
  calc
    _ ≤ (volume.prod volume).real good*(L^c*Nmass) := by
      simpa only [setIntegral_const,smul_eq_mul] using hb
    _ ≤ Fmass*(L^c*Nmass) := mul_le_mul_of_nonneg_right hmeasure
      (mul_nonneg (Real.rpow_nonneg hL.le _) hN)
    _ = _ := by ring

theorem eventually_source_global_weight_integral (D k s : ℝ) (_hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ : Type*) (tops : Finset τ) (T : τ → SlopeBox)
      (Nmass Fmass : ℝ), 0 ≤ Nmass → 0 ≤ Fmass →
      (∑ t ∈ tops, (T t).area) ≤ L^s*Nmass^2*Fmass →
      (∑ t ∈ tops, ∫ x, (T t).weight (L^k) D x ∂volume.prod volume) ≤
        L^(s+2*k+1)*Nmass^2*Fmass := by
  let C := (2:ℝ)^D*∫ x, topProfile D x ∂volume.prod volume
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (integral_nonneg (topProfile_nonnegative D))
  filter_upwards [eventually_ge_atTop (max 1 C)] with L hL
  intro τ tops T Nmass Fmass hN hF harea
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hCL : C ≤ L := (le_max_right _ _).trans hL
  have hK : 0 < L^k := Real.rpow_pos_of_pos hL0 _
  have heq : (∑ t ∈ tops, ∫ x, (T t).weight (L^k) D x ∂volume.prod volume) =
      C*(L^k)^2*(∑ t ∈ tops, (T t).area) := by
    simp_rw [SlopeBox.integral_weight _ hK D]
    unfold SlopeBox.area
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [C]
    ring
  have hpower : L*(L^k)^2*L^s = L^(s+2*k+1) := by
    calc
      _ = L^((1:ℝ))*((L^k)^((2:ℝ)))*L^s := by rw [Real.rpow_one,Real.rpow_two]
      _ = L^(1+k*2+s) := by rw [←Real.rpow_mul hL0.le,←Real.rpow_add hL0,←Real.rpow_add hL0]
      _ = _ := by congr 1; ring
  rw [heq]
  calc
    _ ≤ C*(L^k)^2*(L^s*Nmass^2*Fmass) :=
      mul_le_mul_of_nonneg_left harea (mul_nonneg hC (sq_nonneg _))
    _ ≤ L*(L^k)^2*(L^s*Nmass^2*Fmass) := by gcongr
    _ = _ := by rw [show L*(L^k)^2*(L^s*Nmass^2*Fmass) =
        (L*(L^k)^2*L^s)*Nmass^2*Fmass by ring,hpower]

end LipschitzHilbert

end

end OAI
