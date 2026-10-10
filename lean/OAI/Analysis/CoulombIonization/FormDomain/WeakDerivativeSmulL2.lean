import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.HalfScaleNormSq

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma weak_derivative_smul_L2 {f g : Lp ℂ 2 (volume : Measure V)} {v : V}
    (h : HasWeakDirectionalDerivative f g v) (c : ℂ) :
    HasWeakDirectionalDerivative (c • f : Lp ℂ 2 volume) (c • g : Lp ℂ 2 volume) v := by
  intro φ hφ hcφ
  have he (w : Lp ℂ 2 (volume : Measure V)) (a : V → ℝ) :
      (∫ x, (c • w : Lp ℂ 2 volume) x * (a x : ℂ)) =
        c * ∫ x, w x * (a x : ℂ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c w] with x hx
    simp only [hx,Pi.smul_apply,smul_eq_mul,mul_assoc]
  rw [he,he,h φ hφ hcφ,mul_neg]
end CoulombAtom

namespace CoulombLT

section
open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def fermionDensity {N : ℕ} (ψ : fermionL2 (V := V) (N+1)) (x : V) : ℝ≥0∞ :=
  ∑ i : Fin (N+1), ∑ s : Fin 2, ∫⁻ y,
    ENNReal.ofReal (‖splitFermion i ψ ((x,s),y)‖^2)
      ∂(configMeasure N (spinSpaceMeasure (V := V)))

lemma fermionDensity_eq_family {N : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space)))))
    (ψ : fermionL2 (V := Space) (N+1)) :
    ∀ᵐ x ∂(volume : Measure Space),
      fermionDensity ψ x = 2 * infiniteDensity (fermionFamily b ψ) x := by
  have he (p : Fin (N+1) × Fin 2 × κ) :
      (fun x => fermionFamily b ψ p x) =ᵐ[volume]
        (fun x => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          spinMarginal (splitFermion p.1 ψ) p.2.1 (b p.2.2) x) := by
    exact Lp.coeFn_smul _ _
  filter_upwards [ae_all_iff.mpr he,
    ae_all_iff.mpr (fun i : Fin (N+1) => spinMarginal_slice_parseval b (splitFermion i ψ))]
      with x hx hy
  have hs : infiniteDensity (fermionFamily b ψ) x =
      ENNReal.ofReal (1/2:ℝ) * fermionDensity ψ x := by
    unfold infiniteDensity
    simp_rw [hx,half_scale_norm_sq,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    rw [ENNReal.tsum_mul_left,ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_prod',hy,tsum_fintype]
    rfl
  rw [hs,← mul_assoc]
  have hc : (2:ℝ≥0∞)*ENNReal.ofReal (1/2:ℝ) = 1 := by
    rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hc,one_mul]
end

open CoulombPauli CoulombPackets CoulombAtom
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

lemma fermion_lt_numeric {N : ℕ} (u : Fin (N+1) → Fin 3 → fermionL2 (V := Space) (N+1)) :
    (4:ℝ≥0∞)*(16*ENNReal.ofReal ((N+1:ℝ)/2) + ENNReal.ofReal (1024/3:ℝ)*
        (∑ a : Fin 3, ENNReal.ofReal ((1/2:ℝ)*∑ i, ‖u i a‖^2))) =
      ENNReal.ofReal (32*(N+1:ℝ) + (2048/3:ℝ) * ∑ i, ∑ a, ‖u i a‖^2) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← Finset.mul_sum,
    Finset.sum_comm]
  have h4 : (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) := by norm_num
  have h16 : (16:ℝ≥0∞) = ENNReal.ofReal (16:ℝ) := by norm_num
  rw [h4,h16,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1024/3),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  congr 1
  ring

theorem fermion_lieb_thirring {N : ℕ}
    (ψ : fermionL2 (V := Space) (N+1))
    (u : Fin (N+1) → Fin 3 → fermionL2 (V := Space) (N+1))
    (hw : ∀ i a, HasWeakSpinPartialDerivative (splitFermion i ψ)
      (splitFermion i (u i a)) (EuclideanSpace.single a 1))
    (hn : ‖ψ‖^2 = 1)
    (ha : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ) :
    (∫⁻ x, fermionDensity ψ x ^ (5/3:ℝ)) ≤
      ENNReal.ofReal (32*(N+1:ℝ) + (2048/3:ℝ) * ∑ i, ∑ a, ‖u i a‖^2) := by
  let : MeasureTheory.IsSeparable (configMeasure N (spinSpaceMeasure (V := Space))) :=
    MeasureTheory.isSeparable_of_sigmaFinite _
  obtain ⟨κ,b,-⟩ := exists_hilbertBasis ℂ
    (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := Space))))
  let : Countable κ := hilbertBasis_countable b
  let f := fermionFamily b ψ
  let g (a : Fin 3) (p : Fin (N+1) × Fin 2 × κ) : Lp ℂ 2 (volume : Measure Space) :=
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • spinMarginal (splitFermion p.1 (u p.1 a)) p.2.1 (b p.2.2)
  have hg (a : Fin 3) (p : Fin (N+1) × Fin 2 × κ) :
      HasWeakDirectionalDerivative (f p) (g a p) (EuclideanSpace.single a 1) :=
    weak_derivative_smul_L2 (spinMarginal_weak_derivative (hw p.1 a) p.2.1 (b p.2.2)) _
  have hb := weak_family_lieb_thirring (fermionFamily_bessel b ψ hn ha) hg
  have hftrace : (∑' j, ENNReal.ofReal (‖f j‖^2)) = ENNReal.ofReal ((N+1:ℝ)/2) := by
    simpa only [hn,mul_one] using fermionFamily_trace b ψ
  have hgtrace (a : Fin 3) :
      (∑' j, ENNReal.ofReal (‖g a j‖^2)) = ENNReal.ofReal ((1/2:ℝ)*∑ i, ‖u i a‖^2) :=
    marginal_family_trace b (fun i => u i a)
  rw [hftrace] at hb
  simp_rw [hgtrace] at hb
  have hc : (2:ℝ≥0∞)^(5/3:ℝ) ≤ 4 := by
    calc
      _ ≤ (2:ℝ≥0∞)^(2:ℝ) := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  calc
    _ = ∫⁻ x, (2*infiniteDensity f x)^(5/3:ℝ) :=
      by
      apply lintegral_congr_ae
      filter_upwards [fermionDensity_eq_family b ψ] with x hx
      exact congrArg (fun t : ℝ≥0∞ => t^(5/3:ℝ)) hx
    _ ≤ ∫⁻ x, 4*(infiniteDensity f x)^(5/3:ℝ) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 5/3)]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4 * ∫⁻ x, infiniteDensity f x^(5/3:ℝ) := lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 4*(16*ENNReal.ofReal ((N+1:ℝ)/2) + ENNReal.ofReal (1024/3:ℝ)*
        (∑ a : Fin 3, ENNReal.ofReal ((1/2:ℝ)*∑ i, ‖u i a‖^2))) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := fermion_lt_numeric u
end CoulombLT

end

end OAI
