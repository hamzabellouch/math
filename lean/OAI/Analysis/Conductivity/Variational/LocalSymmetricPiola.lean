import Mathlib
import OAI.Analysis.Conductivity.Flux.PiolaFluxAdd

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def localPiolaTensor (X : OpenPartialHomeomorph Coord3 Coord3)
    (B : Coord3 → Mat3) (y : Coord3) : Mat3 := by
  classical
  exact if y∈X.target then
    |(fderiv ℝ X (X.symm y)).det|⁻¹ •
      (operatorMatrix (fderiv ℝ X (X.symm y))*B (X.symm y)*
        (operatorMatrix (fderiv ℝ X (X.symm y)))ᵀ)
  else 0

lemma localPiolaTensor_isSymm (X : OpenPartialHomeomorph Coord3 Coord3)
    (B : Coord3 → Mat3) (hB : ∀ x,(B x).IsSymm) (y : Coord3) :
    (localPiolaTensor X B y).IsSymm := by
  by_cases hy : y∈X.target
  · simp only [localPiolaTensor,ite_eq_left hy]
    apply Matrix.IsSymm.smul
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,(hB _).eq]
    simp only [Matrix.mul_assoc]
  · simp only [localPiolaTensor,ite_eq_right hy]
    exact (Matrix.isSymm_zero (n := Fin 3) (α := ℝ))

lemma localPiolaTensor_support (X : OpenPartialHomeomorph Coord3 Coord3)
    (B : Coord3 → Mat3) :
    Function.support (localPiolaTensor X B)⊆X '' (Function.support B∩X.source) := by
  intro y hy
  by_cases hyt : y∈X.target
  · refine ⟨X.symm y,⟨?_,X.map_target hyt⟩,X.right_inv hyt⟩
    intro hz
    exact hy (by simp [localPiolaTensor,hyt,hz])
  · exact False.elim (hy (by simp [localPiolaTensor,hyt]))

lemma localPiolaTensor_compact (X : OpenPartialHomeomorph Coord3 Coord3)
    (B : Coord3 → Mat3) (hc : HasCompactSupport B) (hs : tsupport B⊆X.source) :
    HasCompactSupport (localPiolaTensor X B) ∧ tsupport (localPiolaTensor X B)⊆X.target := by
  have hci : IsCompact (X '' tsupport B) := hc.image_of_continuousOn (X.continuousOn.mono hs)
  have hsub : tsupport (localPiolaTensor X B)⊆X '' tsupport B :=
    closure_minimal ((localPiolaTensor_support X B).trans
      (image_mono (fun _ hx => subset_closure hx.1))) hci.isClosed
  exact ⟨hci.of_isClosed_subset isClosed_closure hsub,hsub.trans (by
    rintro y ⟨x,hx,rfl⟩; exact X.map_source (hs hx))⟩

lemma localPiolaTensor_smooth (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (B : Coord3 → Mat3) (hB : ContDiff ℝ (↑(⊤ : ℕ∞)) B)
    (hc : HasCompactSupport B) (hs : tsupport B⊆X.source) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (localPiolaTensor X B) := by
  apply contDiff_of_contDiffOn_tsupport X.open_target _ (localPiolaTensor_compact X B hc hs).2
  apply X.open_target.contDiffOn_iff.mpr
  intro y hy
  have hxi := hXi.contDiffAt (X.open_target.mem_nhds hy)
  have hx := hX.contDiffAt (X.open_source.mem_nhds (X.map_target hy))
  have hd : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun z => fderiv ℝ X (X.symm z)) y :=
    (hx.fderiv_right (by simp)).comp y hxi
  have hd0 := local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
    (hXi.differentiableOn (by simp)) (X.map_target hy)
  have hdM := (operatorMatrix_contDiff (m := Fin 3) (n := Fin 3)).contDiffAt.comp y hd
  have hdet := ((contDiff_clm_det (E := Coord3) (↑(⊤ : ℕ∞))).contDiffAt.comp y hd).abs hd0
  have hformula := (hdet.inv (abs_ne_zero.mpr hd0)).smul
    (contDiffAt_matrix_mul (contDiffAt_matrix_mul hdM (hB.contDiffAt.comp y hxi))
      (contDiffAt_matrix_transpose hdM))
  apply hformula.congr_of_eventuallyEq
  filter_upwards [X.open_target.mem_nhds hy] with z hz
  simp only [localPiolaTensor,ite_eq_left hz]
  rfl

lemma operatorMatrix_local_inverse_fderiv (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    {x : Coord3} (hx : x∈X.source) :
    operatorMatrix (fderiv ℝ X.symm (X x))=(operatorMatrix (fderiv ℝ X x))⁻¹ := by
  have h := congrArg operatorMatrix (local_fderiv_symm_comp X hX hXi hx)
  rw [operatorMatrix_comp,operatorMatrix_id] at h
  exact (Matrix.inv_eq_left_inv h).symm

lemma gradientColumns_local_recomposition (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    (u : Coord3 → Fin 2 → ℝ) (hu : DifferentiableOn ℝ u X.source)
    {x : Coord3} (hx : x∈X.source) :
    gradientColumns (fderiv ℝ (u∘X.symm) (X x))=
      pushGradient (operatorMatrix (fderiv ℝ X x)) (gradientColumns (fderiv ℝ u x)) := by
  have hux : DifferentiableAt ℝ u (X.symm (X x)) := by
    rw [X.left_inv hx]
    exact (hu x hx).differentiableAt (X.open_source.mem_nhds hx)
  have hix := (hXi _ (X.map_source hx)).differentiableAt (X.open_target.mem_nhds (X.map_source hx))
  rw [fderiv_comp (X x) hux hix,X.left_inv hx]
  change (operatorMatrix ((fderiv ℝ u x).comp (fderiv ℝ X.symm (X x))))ᵀ=_
  rw [operatorMatrix_comp,Matrix.transpose_mul,operatorMatrix_local_inverse_fderiv X hX hXi hx]
  rfl

theorem localPiolaTensor_columns (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    (B : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ)
    (hu : DifferentiableOn ℝ u X.source) (j : Fin 2) (y : Coord3) :
    (localPiolaTensor X B y*gradientColumns (fderiv ℝ (u∘X.symm) y)).col j=
      localPiolaFlux X (fun x => (B x*gradientColumns (fderiv ℝ u x)).col j) y := by
  by_cases hy : y∈X.target
  · let x := X.symm y
    have hx : x∈X.source := X.map_target hy
    have hxy : X x=y := X.right_inv hy
    rw [←hxy,gradientColumns_local_recomposition X hX hXi u hu hx]
    have hd : (operatorMatrix (fderiv ℝ X x)).det≠0 := by
      rw [operatorMatrix_det]
      exact local_fderiv_det_ne_zero X hX hXi hx
    simp only [localPiolaTensor,ite_eq_left (X.map_source hx),X.left_inv hx,
      Matrix.smul_mul,Matrix.mul_assoc,pushGradient_leftInverse _ hd]
    simp only [localPiolaFlux,ite_eq_left (X.map_source hx),X.left_inv hx]
    change (|(fderiv ℝ X x).det|⁻¹ •
      (operatorMatrix (fderiv ℝ X x)*(B x*gradientColumns (fderiv ℝ u x)))).col j=_
    change |(fderiv ℝ X x).det|⁻¹ •
      ((operatorMatrix (fderiv ℝ X x)*(B x*gradientColumns (fderiv ℝ u x))).col j)=_
    congr 1
    exact (operatorMatrix_mulVec (fderiv ℝ X x) ((B x*gradientColumns (fderiv ℝ u x)).col j))
  · simp only [localPiolaTensor,localPiolaFlux,ite_eq_right hy,Matrix.zero_mul]
    rfl

end ScalarConductivity

end

end OAI
