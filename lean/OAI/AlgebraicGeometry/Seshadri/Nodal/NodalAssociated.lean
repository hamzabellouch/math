import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Lattice.NodePolygon

namespace OAI


                                         
section

namespace MaximalSeshadri.NodalLocal
noncomputable section
open PowerSeries

lemma bivariateCoeff_unit_ne_zero (u : Bivariate ℂ) (hu : IsUnit u) :
    bivariateCoeff u (0,0) ≠ 0 := by
  simpa only [bivariateCoeff,coeff_zero_eq_constantCoeff_apply,RingHom.comp_apply] using
    (hu.map ((constantCoeff : PowerSeries ℂ →+* ℂ).comp
      (constantCoeff : Bivariate ℂ →+* PowerSeries ℂ))).ne_zero

lemma lexInitial_associated {f g : Bivariate ℂ} (h : Associated f g)
    (t : ℝ) (ht : 0 < t) (e : Exponent) (he : LexInitial (bivariateCoeff f) t e) :
    LexInitial (bivariateCoeff g) t e := by
  obtain ⟨u,hu⟩ := h
  rw [← hu,mul_comm]
  exact lexInitial_unit_mul u f t ht e he (bivariateCoeff_unit_ne_zero u u.isUnit)

theorem nodal_associated_quadrilateral (u f g : Bivariate ℂ) (j : ℕ)
    (d H t k n : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) (hk : 0 < k)
    (hu : IsUnit u) (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0)
    (hcolength : (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ) ≤ n*d*H)
    (hdegree : n+(j:ℝ)*d=k) (hassoc : Associated ((u*nodeEquation ℂ)^j*f) g)
    (p : Exponent) (hp : LexInitial (bivariateCoeff g) t p) :
    ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
      (k*(d*H*t/(1+t))) (k*(d*H/(1+t))) (k/d) := by
  have hf : f ≠ 0 := fun h => hx (by rw [h,map_zero])
  have hc : bivariateCoeff f ≠ 0 := by
    intro h
    apply hf
    apply bivariateCoeffEquiv.injective
    change bivariateCoeff f = bivariateCoeff 0
    rw [h]
    funext p
    simp [bivariateCoeff]
  obtain ⟨e,he⟩ := exists_lexInitial _ t ht hc
  exact nodal_factor_quadrilateral u f j d H t k n hd hH ht hk e he
    (bivariateCoeff_unit_ne_zero u hu) hx hz hcolength hdegree p
    (lexInitial_associated hassoc.symm t ht p hp)
end
end MaximalSeshadri.NodalLocal

end



end OAI
