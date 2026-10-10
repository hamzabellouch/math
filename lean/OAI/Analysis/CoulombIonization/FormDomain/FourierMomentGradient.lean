import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.FormBody
import OAI.Analysis.CoulombIonization.Localization.FermionL2
import OAI.Analysis.CoulombIonization.Localization.PacketFourier
import OAI.Analysis.CoulombIonization.Fermionic.InfiniteDensity

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
namespace CoulombLT

section
open CoulombAtom
lemma fourierMoment_le_gradient {f : Lp ℂ 2 (volume : Measure Space)}
    {g : Fin 3 → Lp ℂ 2 (volume : Measure Space)}
    (hw : ∀ a, HasWeakDirectionalDerivative f (g a) (EuclideanSpace.single a 1)) :
    fourierMoment f ≤ ENNReal.ofReal (∑ a, ‖g a‖^2) := by
  have he := weak_fourier_kinetic (EuclideanSpace.basisFun (Fin 3) ℝ)
    (Lp.memLp f) (fun a => Lp.memLp (g a)) (fun a => by simpa using hw a)
  simp only [Lp.toLp_coeFn] at he
  have hp : 1 ≤ (2*Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ∫⁻ ξ, ENNReal.ofReal ((2*Real.pi)^2*‖ξ‖^2*‖(𝓕 f : Lp ℂ 2 volume) ξ‖^2) := by
      apply lintegral_mono
      intro ξ
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_nonneg (sq_nonneg ‖ξ‖) (sq_nonneg ‖(𝓕 f : Lp ℂ 2 volume) ξ‖)]
    _ = ENNReal.ofReal (∑ a, ∫ x, ‖g a x‖^2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal he.1
        (Filter.Eventually.of_forall (fun _ => by positivity)), he.2]
    _ = _ := by simp only [← l2_norm_sq_eq_integral]

variable {ι : Type*} [Countable ι]
theorem weak_family_lieb_thirring {f : ι → Lp ℂ 2 (volume : Measure Space)}
    {g : Fin 3 → ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : ∀ s : Finset ι, BesselFamily (fun j : s => f j))
    (hw : ∀ a j, HasWeakDirectionalDerivative (f j) (g a j) (EuclideanSpace.single a 1)) :
    (∫⁻ x, infiniteDensity f x ^ (5/3:ℝ)) ≤
      16*(∑' j, ENNReal.ofReal (‖f j‖^2)) +
        ENNReal.ofReal (1024/3:ℝ)*(∑ a, ∑' j, ENNReal.ofReal (‖g a j‖^2)) := by
  apply (countable_lieb_thirring_lintegral hf).trans
  apply add_le_add_right
  gcongr
  calc
    _ ≤ ∑' j, ENNReal.ofReal (∑ a, ‖g a j‖^2) :=
      ENNReal.tsum_le_tsum (fun j => fourierMoment_le_gradient (fun a => hw a j))
    _ = _ := by
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
      simpa only [tsum_fintype] using (ENNReal.tsum_comm (f := fun j a => ENNReal.ofReal (‖g a j‖^2)))
end

open CoulombPauli CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma besselFamily_of_unit {ι : Type*} [Fintype ι]
    {f : ι → Lp ℂ 2 (volume : Measure V)}
    (h : ∀ u : Lp ℂ 2 (volume : Measure V), ‖u‖ = 1 →
      (∑ j, ‖inner ℂ u (f j)‖^2) ≤ 1) : BesselFamily f := by
  intro u
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  let v : Lp ℂ 2 (volume : Measure V) := ((‖u‖⁻¹ : ℝ) : ℂ) • u
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]
  have hh := h v hv
  have hi (j : ι) : ‖inner ℂ v (f j)‖^2 = ‖u‖⁻¹^2 * ‖inner ℂ u (f j)‖^2 := by
    simp only [v, inner_smul_left, norm_mul, starRingEnd_apply, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), mul_pow]
  simp_rw [hi, ← Finset.mul_sum] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖u‖)
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn, one_pow, one_mul, mul_one] at hh'
  exact hh'

lemma spinMarginal_coefficient {B : Type*} [MeasurableSpace B] {ν : Measure B}
    [SigmaFinite ν] (ψ : Lp ℂ 2 ((spinSpaceMeasure (V := V)).prod ν))
    (u : Lp ℂ 2 (volume : Measure V)) (s : Fin 2) (w : Lp ℂ 2 ν) :
    inner ℂ u (spinMarginal ψ s w) =
      inner ℂ w ((tensorLeft (tensor u (spinVector s))).adjoint ψ) := by
  simp only [spinMarginal, ContinuousLinearMap.adjoint_inner_right,
    tensorRight_apply, tensorLeft_apply]

lemma sum_insert_adjoint_sq_le {N : ℕ}
    (u : Lp ℂ 2 (spinSpaceMeasure (V := V))) (hu : ‖u‖ = 1)
    (ψ : fermionL2 (V := V) (N+1))
    (ha : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ) :
    (∑ i : Fin (N+1), ‖(insertOrbital i u).adjoint ψ‖^2) ≤ ‖ψ‖^2 := by
  have h := sum_project_norm_sq_le u hu ψ ha
  simpa only [projectOrbital, ContinuousLinearMap.comp_apply, insertOrbital_norm,
    hu, one_mul] using h

variable {N : ℕ} {κ : Type*}
def fermionFamily (b : HilbertBasis κ ℂ
    (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : fermionL2 (V := V) (N+1))
    (p : Fin (N+1) × Fin 2 × κ) : Lp ℂ 2 (volume : Measure V) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • spinMarginal (splitFermion p.1 ψ) p.2.1 (b p.2.2)

lemma fermionFamily_coefficient_sum
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : fermionL2 (V := V) (N+1)) (u : Lp ℂ 2 (volume : Measure V)) :
    (∑' p, ENNReal.ofReal (‖inner ℂ u (fermionFamily b ψ p)‖^2)) =
      ENNReal.ofReal ((1/2:ℝ) * ∑ i : Fin (N+1), ∑ s : Fin 2,
        ‖(insertOrbital i (tensor u (spinVector s))).adjoint ψ‖^2) := by
  have hc : ((Real.sqrt 2)⁻¹)^2 = (1/2:ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hi (i : Fin (N+1)) (s : Fin 2) (j : κ) :
      ‖inner ℂ u (fermionFamily b ψ (i,s,j))‖^2 = (1/2:ℝ) *
        ‖inner ℂ (b j) ((insertOrbital i (tensor u (spinVector s))).adjoint ψ)‖^2 := by
    simp only [fermionFamily, inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hc,
      spinMarginal_coefficient, insert_adjoint_split]
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_prod', hi]
  have he (i : Fin (N+1)) (s : Fin 2) :
      (∑' j, ENNReal.ofReal ((1/2:ℝ) *
        ‖inner ℂ (b j) ((insertOrbital i (tensor u (spinVector s))).adjoint ψ)‖^2)) =
      ENNReal.ofReal ((1/2:ℝ) * ‖(insertOrbital i (tensor u (spinVector s))).adjoint ψ‖^2) := by
    have h := (basis_parseval b ((insertOrbital i (tensor u (spinVector s))).adjoint ψ)).mul_left (1/2:ℝ)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable, h.tsum_eq]
  simp_rw [he, tsum_fintype]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]

lemma fermionFamily_bessel
    (b : HilbertBasis κ ℂ (Lp ℂ 2 (configMeasure N (spinSpaceMeasure (V := V)))))
    (ψ : fermionL2 (V := V) (N+1)) (hn : ‖ψ‖^2 = 1)
    (ha : ∀ i j : Fin (N+1), i ≠ j → permute (Equiv.swap i j) ψ = -ψ)
    (F : Finset (Fin (N+1) × Fin 2 × κ)) :
    BesselFamily (fun p : F => fermionFamily b ψ p) := by
  classical
  apply besselFamily_of_unit
  intro u hu
  have hs (s : Fin 2) := sum_insert_adjoint_sq_le (tensor u (spinVector s))
    (by rw [tensor_norm, hu, spinVector_orthonormal.norm_eq_one, one_mul]) ψ ha
  have hb : (1/2:ℝ) * (∑ i : Fin (N+1), ∑ s : Fin 2,
        ‖(insertOrbital i (tensor u (spinVector s))).adjoint ψ‖^2) ≤ 1 := by
    rw [Finset.sum_comm]
    have hh := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin 2))) => hs s)
    simp only [hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    norm_num only [Nat.cast_ofNat, mul_one] at hh
    linarith
  apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 1)).mp
  calc
    _ = ∑ p ∈ F, ENNReal.ofReal (‖inner ℂ u (fermionFamily b ψ p)‖^2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      exact Finset.sum_coe_sort F (fun p => ENNReal.ofReal (‖inner ℂ u (fermionFamily b ψ p)‖^2))
    _ ≤ ∑' p, ENNReal.ofReal (‖inner ℂ u (fermionFamily b ψ p)‖^2) := ENNReal.sum_le_tsum F
    _ = _ := fermionFamily_coefficient_sum b ψ u
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb
end CoulombLT

end

end OAI
