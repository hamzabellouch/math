import OAI.Geometry.NodalSets.Charts.ChartOperatorIdentity
import OAI.Geometry.NodalSets.Elliptic.RealWeightedElliptic

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

theorem realWeightedElliptic_complex (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (w : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hw : ContDiff ℝ ∞ w)
    (x : Yau.Jets.Coord) :
    (realWeightedElliptic gamma B w x : ℂ) =
      Yau.Jets.smoothSecondOrder (fun i j y ↦ (B y i j : ℂ))
        (fun j y ↦ (Yau.realEllipticDrift gamma B y j : ℂ)) (fun y ↦ (w y : ℂ)) x := by
  have hd (j : Fin 4) : Yau.Jets.coordPartial j (fun y ↦ (w y : ℂ)) =
      fun y ↦ (Yau.coordPartial w y j : ℂ) :=
    funext (fun y ↦ coordPartial_ofReal_at w y (hw.differentiable (by simp) y) j)
  unfold realWeightedElliptic realMatrixFlux
  rw [Yau.real_weighted_elliptic_expansion gamma hg hgn B hB w hw]
  simp only [Yau.Jets.smoothSecondOrder,hd]
  simp_rw [coordPartial_ofReal_at _ x
    ((Yau.real_coordPartial_smooth w hw _).differentiable (by simp) x)]
  simp only [Yau.coordPartial,Complex.ofReal_add,Complex.ofReal_sum,Complex.ofReal_mul]

lemma realMatrixEnergy_cross_sum (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀ x i j, B x i j = B x j i) (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    (∑ i, ∑ j, B x i j*(Yau.coordPartial u x i*Yau.coordPartial v x j +
      Yau.coordPartial u x j*Yau.coordPartial v x i)) = 2*realMatrixEnergy B u v x := by
  have hswap : (∑ i, ∑ j, B x i j*Yau.coordPartial u x j*Yau.coordPartial v x i) =
      (∑ i, ∑ j, B x i j*Yau.coordPartial u x i*Yau.coordPartial v x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hs x j i]
  simp only [mul_add,← mul_assoc,Finset.sum_add_distrib,hswap,realMatrixEnergy_apply]
  simp only [mul_assoc,mul_comm]
  ring

theorem real_weighted_elliptic_product (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (u v : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : Yau.Jets.Coord) :
    realWeightedElliptic gamma B (fun y ↦ u y*v y) x =
      u x*realWeightedElliptic gamma B v x + v x*realWeightedElliptic gamma B u x +
      2*realMatrixEnergy B u v x := by
  have h := Yau.Jets.smoothSecondOrder_mul (fun i j y ↦ (B y i j : ℂ))
    (fun j y ↦ (Yau.realEllipticDrift gamma B y j : ℂ))
    (f := fun y ↦ (u y:ℂ)) (u := fun y ↦ (v y:ℂ))
    (Complex.ofRealCLM.contDiff.comp hu) (Complex.ofRealCLM.contDiff.comp hv) x
  have hp : (fun y ↦ (u y:ℂ)*(v y:ℂ)) = fun y ↦ ((u y*v y:ℝ):ℂ) := by
    funext y; simp only [Complex.ofReal_mul]
  change Yau.Jets.smoothSecondOrder _ _ (fun y ↦ (u y:ℂ)*(v y:ℂ)) x = _ at h
  rw [hp,← realWeightedElliptic_complex gamma B _ hg hgn hB (hu.mul hv),
    ← realWeightedElliptic_complex gamma B v hg hgn hB hv,
    ← realWeightedElliptic_complex gamma B u hg hgn hB hu] at h
  simp only [coordPartial_ofReal_at u x (hu.differentiable (by simp) x),
    coordPartial_ofReal_at v x (hv.differentiable (by simp) x)] at h
  have hreal : realWeightedElliptic gamma B (fun y ↦ u y*v y) x =
      u x*realWeightedElliptic gamma B v x + v x*realWeightedElliptic gamma B u x +
      ∑ i, ∑ j, B x i j*(Yau.coordPartial u x i*Yau.coordPartial v x j +
        Yau.coordPartial u x j*Yau.coordPartial v x i) := by
    exact_mod_cast h
  rw [realMatrixEnergy_cross_sum B hs u v] at hreal
  exact hreal

theorem real_weighted_elliptic_exp (gamma phi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hphi : ContDiff ℝ ∞ phi) (t : ℝ) (x : Yau.Jets.Coord) :
    realWeightedElliptic gamma B (fun y ↦ Real.exp (t*phi y)) x =
      (t*realWeightedElliptic gamma B phi x + t^2*realMatrixEnergy B phi phi x)*Real.exp (t*phi x) := by
  have he : Yau.Jets.waveExp (fun y ↦ (phi y:ℂ)) t = fun y ↦ (Real.exp (t*phi y):ℂ) := by
    funext y
    simp only [Yau.Jets.waveExp,← Complex.ofReal_mul,Complex.ofReal_exp]
  have h := Yau.Jets.smoothSecondOrder_waveExp (fun i j y ↦ (B y i j:ℂ))
    (fun j y ↦ (Yau.realEllipticDrift gamma B y j:ℂ))
    (phi := fun y ↦ (phi y:ℂ)) (Complex.ofRealCLM.contDiff.comp hphi) t x
  change Yau.Jets.smoothSecondOrder _ _ (Yau.Jets.waveExp (fun y ↦ (phi y:ℂ)) t) x = _ at h
  rw [he,← realWeightedElliptic_complex gamma B _ hg hgn hB ((contDiff_const.mul hphi).exp),
    ← realWeightedElliptic_complex gamma B phi hg hgn hB hphi] at h
  simp only [Yau.Jets.smoothEikonal,add_sub_cancel_right,
    coordPartial_ofReal_at phi x (hphi.differentiable (by simp) x)] at h
  have heik : (∑ i, ∑ j, (B x i j:ℂ)*
      (Yau.coordPartial phi x i:ℂ)*(Yau.coordPartial phi x j:ℂ)) =
      (realMatrixEnergy B phi phi x:ℂ) := by
    simp only [realMatrixEnergy_apply,Complex.ofReal_sum,Complex.ofReal_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  change _ = (((t:ℂ)*(realWeightedElliptic gamma B phi x:ℂ) + (t:ℂ)^2*
    (∑ i, ∑ j, (B x i j:ℂ)*(Yau.coordPartial phi x i:ℂ)*(Yau.coordPartial phi x j:ℂ)))*
      (Real.exp (t*phi x):ℂ)) at h
  rw [heik] at h
  exact_mod_cast h

end
end Yau.Geometry

end OAI
