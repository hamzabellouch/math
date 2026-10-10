import OAI.Geometry.NodalSets.Elliptic.RealWeightedCommutator

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

theorem real_weighted_symmetric_shift (gamma q v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (t k : ℝ) :
    (∫ x, gamma x*(realWeightedElliptic gamma B v x+t^2*q x*v x)^2) =
      (∫ x, gamma x*(realWeightedElliptic gamma B v x+t^2*q x*v x+k*v x)^2) +
      2*k*(∫ x, gamma x*realMatrixEnergy B v v x) -
      2*k*t^2*(∫ x, gamma x*q x*v x^2) - k^2*(∫ x, gamma x*v x^2) := by
  let L := realWeightedElliptic gamma B v
  let S := fun x ↦ L x+t^2*q x*v x
  have hL := realWeightedElliptic_smooth gamma B v hg hgn hB hv
  have hLc := realWeightedElliptic_compact gamma B v hc
  have hS : ContDiff ℝ ∞ S := hL.add ((contDiff_const.mul hq).mul hv)
  have hSc : HasCompactSupport S := hLc.add hc.mul_left
  have hH : ContDiff ℝ ∞ (fun x ↦ S x+k*v x) := hS.add (contDiff_const.mul hv)
  have hHc : HasCompactSupport (fun x ↦ S x+k*v x) := hSc.add hc.mul_left
  have hHsq : HasCompactSupport (fun x ↦ (S x+k*v x)^2) := by
    convert hHc.mul_right (f' := fun point ↦ S point+k*v point) using 1
    first | rfl | (ext point; simp [pow_two])
  have hvsq : HasCompactSupport (fun x ↦ v x^2) := by
    convert hc.mul_right (f' := v) using 1
    first | rfl | (ext point; simp [pow_two])
  have hiH : Integrable (fun x ↦ gamma x*(S x+k*v x)^2) :=
    (hg.mul (hH.pow 2)).continuous.integrable_of_hasCompactSupport hHsq.mul_left
  have hiL := Yau.compact_weighted_product_integrable gamma v L hg.continuous hv.continuous hL.continuous hc
  have hiq : Integrable (fun x ↦ gamma x*q x*v x^2) :=
    ((hg.mul hq).mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hiv : Integrable (fun x ↦ gamma x*v x^2) :=
    (hg.mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hp : (fun x ↦ gamma x*(S x)^2) =
      (fun x ↦ ((gamma x*(S x+k*v x)^2-2*k*(gamma x*v x*L x)) -
        2*k*t^2*(gamma x*q x*v x^2)) - k^2*(gamma x*v x^2)) := by
    funext x; dsimp [S]; ring
  change (∫ x, gamma x*(S x)^2) = _
  rw [hp,integral_sub
      (f := fun x ↦ gamma x*(S x+k*v x)^2-2*k*(gamma x*v x*L x)-2*k*t^2*(gamma x*q x*v x^2))
      (g := fun x ↦ k^2*(gamma x*v x^2))
      ((hiH.sub (hiL.const_mul (2*k))).sub (hiq.const_mul (2*k*t^2))) (hiv.const_mul (k^2)),
    integral_sub (f := fun x ↦ gamma x*(S x+k*v x)^2-2*k*(gamma x*v x*L x))
      (g := fun x ↦ 2*k*t^2*(gamma x*q x*v x^2))
      (hiH.sub (hiL.const_mul (2*k))) (hiq.const_mul (2*k*t^2)),
    integral_sub hiH (hiL.const_mul (2*k))]
  simp only [integral_const_mul]
  have he := (real_weighted_elliptic_green gamma B v v hg hgn hB hv hv hc).2.2
  change (∫ x, gamma x*v x*L x) = _ at he
  rw [he]
  change (∫ x, gamma x*(S x+k*v x)^2) - _ - _ - _ = (∫ x, gamma x*(S x+k*v x)^2) + _ - _ - _
  ring

end
end Yau.Geometry

end OAI
