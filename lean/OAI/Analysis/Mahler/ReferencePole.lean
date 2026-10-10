import OAI.Analysis.Mahler.UnitaryReference

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def referencePole (k : ℕ) : ComplexEuclidean (k+1) :=
  EuclideanSpace.single 0 1

lemma referencePole_norm (k : ℕ) : ‖referencePole k‖ = 1 := by
  simp [referencePole]

lemma referencePole_inner {k : ℕ} (v : ComplexEuclidean (k+1)) :
    inner ℝ (referencePole k) v = (v 0).re := by
  simp [referencePole, PiLp.inner_apply, Complex.inner]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0; simp [hj0]
  · simp

lemma referencePole_tangent_iff {k : ℕ} (v : ComplexEuclidean (k+1)) :
    v ∈ sphereTangent (referencePole k) ↔ (v 0).re = 0 := by
  rw [sphereTangent, Submodule.mem_orthogonal_singleton_iff_inner_right, referencePole_inner]

lemma covectorVolume_compLinearMap {T S ι : Type*} [AddCommGroup T] [Module ℝ T]
    [AddCommGroup S] [Module ℝ S] [Fintype ι] [DecidableEq ι]
    (p : ι → T →ₗ[ℝ] ℂ) (L : S →ₗ[ℝ] T) :
    (covectorVolume p).compLinearMap L = covectorVolume (fun i => (p i).comp L) := by
  ext v
  simp only [AlternatingMap.compLinearMap_apply, covectorVolume_apply, LinearMap.comp_apply]

lemma referencePole_pair_zero (k : ℕ) :
    (covectorVolume (coordinatePair (0 : Fin (k+1)))).compLinearMap
      (sphereTangent (referencePole k)).subtype = 0 := by
  ext v
  simp only [AlternatingMap.compLinearMap_apply, covectorVolume_apply, Matrix.det_fin_two, Matrix.of_apply,
    coordinatePair, Matrix.cons_val_zero, Matrix.cons_val_one, realCoordinate_apply,
    imagCoordinate_apply, AlternatingMap.zero_apply]
  have h0 := (referencePole_tangent_iff _).mp (v 0).property
  have h1 := (referencePole_tangent_iff _).mp (v 1).property
  simp [h0,h1]

lemma referencePole_twoForm (k : ℕ) :
    tangentForm (referencePole k)
      (extDeriv (oneForm (dcLinear (normEnergy (k+1)))) (referencePole k)).toAlternatingMap =
      ∑ j : Fin k, covectorVolume (fun i =>
        (coordinatePair j.succ i).comp (sphereTangent (referencePole k)).subtype) := by
  rw [extDeriv_normEnergy_covectors, Fin.sum_univ_succ]
  change ((covectorVolume (coordinatePair 0) + ∑ j : Fin k, covectorVolume (coordinatePair j.succ))).compLinearMap _ = _
  ext v
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.add_apply,
    alternatingMap_sum_apply]
  have hz := congrArg (fun a => a v) (referencePole_pair_zero k)
  change covectorVolume (coordinatePair 0) (fun i => (v i : ComplexEuclidean (k+1))) = 0 at hz
  simp only [Submodule.subtype_apply]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [covectorVolume_apply, LinearMap.comp_apply, Submodule.subtype_apply]

lemma oneForm_covectorVolume {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    [NormedSpace ℝ T] [IsScalarTower ℝ ℂ T]
    (a : T → T →L[ℝ] ℂ) (x : T) :
    (oneForm a x).toAlternatingMap = covectorVolume (fun _ : Fin 1 => (a x).toLinearMap) := by
  ext v
  simp [covectorVolume_apply, Matrix.det_unique, oneForm_apply]

lemma referencePole_oneForm (k : ℕ) :
    tangentForm (referencePole k) (oneForm (dcLinear (normEnergy (k+1))) (referencePole k)).toAlternatingMap =
      (1/2 : ℂ) • covectorVolume (fun _ : Fin 1 =>
        (imagCoordinate (0 : Fin (k+1))).comp (sphereTangent (referencePole k)).subtype) := by
  ext v
  change dcLinear (normEnergy (k+1)) (referencePole k) (v 0) = _
  rw [dcLinear_apply, dc_normEnergy, referencePole_inner]
  simp [covectorVolume_apply, Matrix.det_unique, Complex.mul_re]
  ring

/-- At the standard pole, the reference boundary form is the determinant of
the positively ordered tangent covectors, with the exact k!/2 coefficient. -/
theorem referencePole_boundary (k : ℕ) :
    wedge (tangentForm (referencePole k)
      (oneForm (dcLinear (normEnergy (k+1))) (referencePole k)).toAlternatingMap)
      (wedgePower (tangentForm (referencePole k)
        (extDeriv (oneForm (dcLinear (normEnergy (k+1)))) (referencePole k)).toAlternatingMap) k) =
    ((k.factorial : ℂ)/2) • covectorVolume
      (Sum.elim
        (fun _ : Fin 1 => (imagCoordinate (0 : Fin (k+1))).comp (sphereTangent (referencePole k)).subtype)
        (pairedCovectors (fun j : Fin k => fun i =>
          (coordinatePair j.succ i).comp (sphereTangent (referencePole k)).subtype))) := by
  rw [referencePole_oneForm, referencePole_twoForm, wedgePower_sum_pairs_top,
    wedge_smul_left, wedge_smul_right, wedge_covectorVolume, smul_smul]
  congr 1
  ring

end Mahler

end OAI
