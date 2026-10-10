import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.OrthonormalLocalizedModes
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneElectronClosure

namespace OAI

/-! Symmetric Gram correction preserves the actual orbital span and hence its
orthogonal complement. The inverse coefficients are obtained from the proved
Gram identity, without adding a spectral hypothesis. -/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace ContinuumCoulomb

theorem correctedLocalizedCoefficients_leftInverse {D : ℝ} {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) :
    (localizedModeGram u*correctedLocalizedCoefficients u)*
      correctedLocalizedCoefficients u = 1 := by
  have h := correctedLocalizedCoefficients_gram u hsep hs
  have ht : (correctedLocalizedCoefficients u)ᵀ = correctedLocalizedCoefficients u :=
    GramCorrection.correction_transpose (localizedModeGram_isHermitian u)
  rw [ht, Matrix.mul_assoc] at h
  exact mul_eq_one_comm.mp h

theorem continuumLocalizedMode_expand_corrected {D : ℝ} {m : ℕ} (freq : ℝ)
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (i : Fin m) (x : Position) :
    continuumLocalizedMode freq (u i) x =
      ∑ j, (localizedModeGram u*correctedLocalizedCoefficients u) i j *
        correctedLocalizedMode freq u j x := by
  symm
  unfold correctedLocalizedMode localizedLinearOrbital
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, ← Matrix.mul_apply]
  rw [correctedLocalizedCoefficients_leftInverse u hsep hs]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem corrected_orthogonal_implies_raw {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2)
    (f : Position → ℂ) (hf : MemLp f 2)
    (ho : ∀ j, (∫ x, f x*(correctedLocalizedMode freq u j x : ℂ)) = 0)
    (i : Fin m) : (∫ x, f x*(continuumLocalizedMode freq (u i) x : ℂ)) = 0 := by
  have hi (j : Fin m) : Integrable (fun x =>
      ((localizedModeGram u*correctedLocalizedCoefficients u) i j : ℂ)*
        (f x*(correctedLocalizedMode freq u j x : ℂ))) :=
    (hf.integrable_mul (correctedLocalizedMode_memLp hfreq u j).ofReal).const_mul _
  have he (x : Position) : f x*(continuumLocalizedMode freq (u i) x : ℂ) =
      ∑ j, ((localizedModeGram u*correctedLocalizedCoefficients u) i j : ℂ)*
        (f x*(correctedLocalizedMode freq u j x : ℂ)) := by
    rw [continuumLocalizedMode_expand_corrected freq u hsep hs]
    simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [integral_const_mul,ho,mul_zero,Finset.sum_const_zero]

theorem corrected_graph_orthogonal_implies_raw {freq D : ℝ} (hfreq : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (v : Coulomb.H1Vector 1)
    (ho : ∀ s i, inner ℂ
      (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) = 0) :
    graphOrbitalMass (fun i => oneElectronOrbitalLp (continuumLocalizedMode freq (u i))
      (continuumLocalizedMode_memLp hfreq (u i))) (h1Coordinates v) = 0 := by
  apply graphOrbitalMass_eq_zero
  intro s i
  rw [oneElectron_inner_real_orbital]
  have hf : MemLp (oneElectronPullback (v.value s)) 2 :=
    (v.value_L2 s).comp_measurePreserving oneElectronCoordinates.symm.measurePreserving
  have hh (j : Fin m) :
      (∫ x, oneElectronPullback (v.value s) x*(correctedLocalizedMode freq u j x : ℂ)) = 0 := by
    have h := ho s j
    rw [oneElectron_inner_real_orbital] at h
    have he := oneElectronPullback_integral_complex
      (fun x => v.value s x*(correctedLocalizedMode freq u j (oneElectronCoordinates x) : ℂ))
    simpa only [oneElectronPullback,LinearIsometryEquiv.apply_symm_apply] using he.trans h
  have h := corrected_orthogonal_implies_raw hfreq u hsep hs _ hf hh i
  have he := oneElectronPullback_integral_complex
    (fun x => v.value s x*(continuumLocalizedMode freq (u i) (oneElectronCoordinates x) : ℂ))
  have he' : (∫ x, oneElectronPullback (v.value s) x*(continuumLocalizedMode freq (u i) x : ℂ)) =
      ∫ x, v.value s x*(continuumLocalizedMode freq (u i) (oneElectronCoordinates x) : ℂ) := by
    simpa only [oneElectronPullback,LinearIsometryEquiv.apply_symm_apply] using he
  exact he'.symm.trans h

end ContinuumCoulomb

end

end OAI
