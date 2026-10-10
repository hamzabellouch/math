import Mathlib
import OAI.Analysis.AffineBernstein.ParametricNormalization

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parametricFrame_decomposition {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E) (ξ : E) (x : Space n)
    (hd : b.det (parametricFrame X ξ x) ≠ 0) (z : E) :
    ∃ w : Space n, ∃ c : ℝ, z = fderiv ℝ X x w+c • ξ := by
  obtain ⟨hi,hs⟩ := (b.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hd)
  let B : Module.Basis (Fin n ⊕ Unit) ℝ E := Module.Basis.mk hi hs.ge
  let w : Space n := ∑ i : Fin n, B.repr z (Sum.inl i) • coordinateVector n i
  refine ⟨w,B.repr z (Sum.inr ()),?_⟩
  have hh := B.sum_repr z
  simp only [Fintype.sum_sum_type,Fintype.sum_unique] at hh
  have he (i : Fin n ⊕ Unit) : B i = parametricFrame X ξ x i := Module.Basis.mk_apply _ _ _
  simp only [he,parametricFrame,Sum.elim_inl,Sum.elim_inr] at hh
  exact hh.symm.trans (by simp [w,map_sum,map_smul])

lemma parametric_conormal_unique {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E) (ξ : E) (x : Space n)
    (hd : b.det (parametricFrame X ξ x) ≠ 0) (ν ν' : E →L[ℝ] ℝ)
    (hν : ν.comp (fderiv ℝ X x) = 0) (hν' : ν'.comp (fderiv ℝ X x) = 0)
    (hξ : ν ξ = 1) : ν' = (ν' ξ) • ν := by
  ext z
  obtain ⟨w,c,rfl⟩ := parametricFrame_decomposition b X ξ x hd z
  have h0 : ν (fderiv ℝ X x w) = 0 := congrArg (fun f : Space n →L[ℝ] ℝ => f w) hν
  have h0' : ν' (fderiv ℝ X x w) = 0 := congrArg (fun f : Space n →L[ℝ] ℝ => f w) hν'
  simp [h0,h0',hξ,mul_comm]

lemma parametric_kernel_is_tangent {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E) (ξ : E) (x : Space n)
    (hd : b.det (parametricFrame X ξ x) ≠ 0) (ν : E →L[ℝ] ℝ)
    (hν : ν.comp (fderiv ℝ X x) = 0) (hξ : ν ξ = 1) {z : E} (hz : ν z = 0) :
    ∃ w : Space n, z = fderiv ℝ X x w := by
  obtain ⟨w,c,he⟩ := parametricFrame_decomposition b X ξ x hd z
  have h0 : ν (fderiv ℝ X x w) = 0 := congrArg (fun f : Space n →L[ℝ] ℝ => f w) hν
  rw [he,map_add,map_smul,hξ,h0,smul_eq_mul,mul_one,zero_add] at hz
  exact ⟨w,by simpa [hz] using he⟩

/- The literal affine area is independent of both allowed choices of
conormal and transverse vector. All transversality and orientation properties
are explicit; no intrinsic-area object is postulated. -/
theorem parametricAreaDensity_choices {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) {U : Set (Space n)} (hU : IsOpen U)
    {X : Space n → E} (hX : ContDiffOn ℝ ∞ X U) {x : Space n} (hx : x ∈ U)
    (ν ν' : E →L[ℝ] ℝ) (ξ ξ' : E)
    (hd : b.det (parametricFrame X ξ x) ≠ 0)
    (hν : ν.comp (fderiv ℝ X x) = 0) (hν' : ν'.comp (fderiv ℝ X x) = 0)
    (hξ : ν ξ = 1) (hξ' : ν' ξ' = 1) (hc : 0 < ν' ξ)
    (hH : 0 ≤ (parametricSecondForm X ν x).det) :
    parametricAreaDensity b X ν' ξ' x = parametricAreaDensity b X ν ξ x := by
  have he := parametric_conormal_unique b X ξ x hd ν ν' hν hν' hξ
  have hξν : ν ξ' = (ν' ξ)⁻¹ := by
    have hh := hξ'
    rw [he,smul_apply,smul_eq_mul] at hh
    have hh' : ν ξ' = 1 / (ν' ξ) := (eq_div_iff hc.ne').mpr (by simpa [mul_comm] using hh)
    simpa only [one_div] using hh'
  have hz : ν (ξ'-(ν' ξ)⁻¹ • ξ) = 0 := by simp [hξν,hξ]
  obtain ⟨w,hw⟩ := parametric_kernel_is_tangent b X ξ x hd ν hν hξ hz
  have hξe : ξ' = (ν' ξ)⁻¹ • ξ + fderiv ℝ X x w := by rw [← hw]; abel
  rw [hξe,parametricAreaDensity_add_tangent,he]
  simp only [smul_apply,smul_eq_mul,hξ,mul_one]
  exact parametricAreaDensity_normalize b hU hX ν ξ hc hx hH

lemma parametricAreaDensity_congr {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X Y : Space n → E} {x : Space n} (h : X =ᶠ[nhds x] Y)
    (ν : E →L[ℝ] ℝ) (ξ : E) :
    parametricAreaDensity b X ν ξ x = parametricAreaDensity b Y ν ξ x := by
  have he : (fun y => ν (X y)) =ᶠ[nhds x] (fun y => ν (Y y)) := h.mono (fun _ hy => congrArg ν hy)
  simp only [parametricAreaDensity,parametricSecondForm,parametricFrame,hessian_eq_of_eventuallyEq he,h.fderiv_eq]

end AffineBernstein
end

end OAI
