import Mathlib
import OAI.Analysis.CoulombIonization.Variational.Slices
import OAI.Analysis.CoulombIonization.Fermionic.SlaterTwoBody

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterSymmetry_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate

variable {α : Type*} {n : ℕ}

lemma slaterRaw_perm (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    slaterRaw φ (x ∘ σ) = ((σ.sign : ℤ) : ℂ) * slaterRaw φ x := by
  rw [slaterRaw_eq_det, slaterRaw_eq_det]
  exact Matrix.det_permute' σ (Matrix.of (fun i j => φ i (x j)))

lemma slater_perm (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    slater φ (x ∘ σ) = ((σ.sign : ℤ) : ℂ) * slater φ x := by
  rw [slater, slaterRaw_perm, slater]
  ring

end Work_SlaterSymmetry_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

abbrev SlaterParticle := Fin 2 × Space

def slaterParticles {n : ℕ} (s : Spins n) (x : Configuration n) : Fin n → SlaterParticle :=
  fun i => (s i, x i)

def spatialOrbitalDerivative {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (a : Fin 3) (i : Fin n) (z : SlaterParticle) : ℂ :=
  fderiv ℝ (fun x : Space => φ i (z.1,x)) z.2 (EuclideanSpace.single a 1)

lemma slaterCoordinateTensor_eq {α : Type*} {n : ℕ} (φ ψ : Fin n → α → ℂ)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    slaterCoordinateTensor φ ψ j σ x =
      ψ (σ j) (x j) * ∏ i ∈ Finset.univ.erase j, φ (σ i) (x i) := by
  rw [slaterCoordinateTensor, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [ite_eq_right (Finset.mem_erase.mp hi).1]

lemma slater_spatial_tensor_smooth {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (s : Spins n) (σ : Equiv.Perm (Fin n)) :
    ContDiff ℝ ∞ (fun x : Configuration n => slaterTensor φ σ (slaterParticles s x)) := by
  unfold slaterTensor slaterParticles
  apply contDiff_prod
  intro i _
  exact (hφ (σ i) (s i)).comp (f := fun y : Configuration n => y i)
    (ContinuousLinearMap.proj i : Configuration n →L[ℝ] Space).contDiff

lemma slater_spatial_tensor_compact {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (s : Spins n) (σ : Equiv.Perm (Fin n)) :
    HasCompactSupport (fun x : Configuration n => slaterTensor φ σ (slaterParticles s x)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ_pi (fun i => hφ (σ i) (s i)))
  intro x hx i _
  apply subset_tsupport (fun t : Space => φ (σ i) (s i,t))
  exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)

lemma slater_spatial_raw_smooth {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x))) (s : Spins n) :
    ContDiff ℝ ∞ (fun x : Configuration n => slaterRaw φ (slaterParticles s x)) := by
  apply ContDiff.sum
  intro σ _
  exact contDiff_const.mul (slater_spatial_tensor_smooth hφ s σ)

lemma slater_spatial_smooth {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x))) (s : Spins n) :
    ContDiff ℝ ∞ (fun x : Configuration n => slater φ (slaterParticles s x)) :=
  contDiff_const.mul (slater_spatial_raw_smooth hφ s)

lemma slater_spatial_compact {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) (s : Spins n) :
    HasCompactSupport (fun x : Configuration n => slater φ (slaterParticles s x)) := by
  have h (σ : Equiv.Perm (Fin n)) : HasCompactSupport (fun x : Configuration n =>
      ((σ.sign : ℤ) : ℂ) * slaterTensor φ σ (slaterParticles s x)) :=
    (slater_spatial_tensor_compact hφ s σ).mul_left
  have hs := HasCompactSupport.finset_sum (s := Finset.univ) (fun σ _ => h σ)
  have he : (∑ σ : Equiv.Perm (Fin n), fun x : Configuration n =>
      ((σ.sign : ℤ) : ℂ) * slaterTensor φ σ (slaterParticles s x)) =
      (fun x : Configuration n => slaterRaw φ (slaterParticles s x)) := by
    ext x
    simp only [Finset.sum_apply, slaterRaw]
  have hh : HasCompactSupport (fun x : Configuration n => slaterRaw φ (slaterParticles s x)) :=
    he ▸ hs
  exact hh.mul_left

lemma slater_spatial_tensor_derivative {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (s : Spins n) (σ : Equiv.Perm (Fin n)) (x : Configuration n) (j : Fin n) (a : Fin 3) :
    fderiv ℝ (fun y : Configuration n => slaterTensor φ σ (slaterParticles s y)) x
        (direction j a) =
      slaterCoordinateTensor φ (spatialOrbitalDerivative φ a) j σ (slaterParticles s x) := by
  have hd (i : Fin n) : DifferentiableAt ℝ
      (fun y : Configuration n => φ (σ i) (s i,y i)) x :=
    ((hφ (σ i) (s i)).comp (f := fun y : Configuration n => y i)
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] Space).contDiff).differentiable
        (by simp) x
  have he (i : Fin n) : fderiv ℝ (fun y : Configuration n => φ (σ i) (s i,y i)) x
      (direction j a) = if i=j then spatialOrbitalDerivative φ a (σ j) (s j,x j) else 0 := by
    rw [show (fun y : Configuration n => φ (σ i) (s i,y i)) =
      (fun z : Space => φ (σ i) (s i,z)) ∘ (ContinuousLinearMap.proj i : Configuration n →L[ℝ] Space) from rfl,
      fderiv_comp x ((hφ (σ i) (s i)).differentiable (by simp) (x i))
        (ContinuousLinearMap.proj i : Configuration n →L[ℝ] Space).differentiableAt,
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
    by_cases hij : i=j
    · subst i
      simp only [ContinuousLinearMap.proj_apply, direction, Pi.single_eq_same]
      rfl
    · simp only [ite_eq_right hij, ContinuousLinearMap.proj_apply, direction,
        Pi.single_eq_of_ne hij, map_zero]
  change fderiv ℝ (fun y : Configuration n => ∏ i, φ (σ i) (s i,y i)) x _ = _
  rw [fderiv_finsetProd (fun i _ => hd i), sum_apply]
  simp only [smul_apply, smul_eq_mul, he]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl, slaterCoordinateTensor_eq, mul_comm]
    rfl
  · intro i _ hij
    rw [ite_eq_right hij, mul_zero]
  · simp

lemma slater_spatial_derivative {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (s : Spins n) (x : Configuration n) (j : Fin n) (a : Fin 3) :
    fderiv ℝ (fun y : Configuration n => slater φ (slaterParticles s y)) x (direction j a) =
      slaterCoordinate φ (spatialOrbitalDerivative φ a) j (slaterParticles s x) := by
  change fderiv ℝ (fun y : Configuration n => (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ *
    slaterRaw φ (slaterParticles s y)) x _ = _
  rw [fderiv_const_mul ((slater_spatial_raw_smooth hφ s).differentiable (by simp) x),
    smul_apply, smul_eq_mul]
  unfold slaterRaw
  rw [fderiv_fun_sum (fun σ _ => ((slater_spatial_tensor_smooth hφ s σ).differentiable
    (by simp) x).const_mul _), sum_apply]
  simp_rw [fderiv_const_mul ((slater_spatial_tensor_smooth hφ s _).differentiable
    (by simp) x), smul_apply, smul_eq_mul, slater_spatial_tensor_derivative hφ]
  rfl

def slaterForm {n : ℕ} (φ : Fin n → SlaterParticle → ℂ) : FormVector n where
  value s x := slater φ (slaterParticles s x)
  gradient s j a x := slaterCoordinate φ (spatialOrbitalDerivative φ a) j (slaterParticles s x)

lemma slaterForm_sobolevFermion {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) :
    SobolevFermion (slaterForm φ) := by
  have hd (s : Spins n) (j : Fin n) (a : Fin 3) :
      (slaterForm φ).gradient s j a = fun x =>
        fderiv ℝ (fun y : Configuration n => slater φ (slaterParticles s y)) x (direction j a) :=
    funext (fun x => (slater_spatial_derivative hφ s x j a).symm)
  refine ⟨fun s => (slater_spatial_smooth hφ s).continuous.memLp_of_hasCompactSupport
    (slater_spatial_compact hc s), ?_, ?_, ?_⟩
  · intro s j a
    rw [hd]
    exact (smooth_derivative_continuous (slater_spatial_smooth hφ s) _).memLp_of_hasCompactSupport
      (compact_derivative (slater_spatial_compact hc s) _)
  · intro s j a f hf hcf
    rw [hd]
    exact smooth_weak_gradient (slater_spatial_smooth hφ s) (slater_spatial_compact hc s) hf hcf _
  · intro π s
    exact Eventually.of_forall fun x => slater_perm φ π (slaterParticles s x)

end CoulombAtom

end

end OAI
