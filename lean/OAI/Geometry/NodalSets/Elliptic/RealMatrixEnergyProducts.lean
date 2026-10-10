import OAI.Geometry.NodalSets.Elliptic.RealMatrixTransport

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma realMatrixEnergy_add_left (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (f u v : Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ f y+u y) v x = realMatrixEnergy B f v x+realMatrixEnergy B u v x := by
  have he : realCoordGradient (fun y ↦ f y+u y) x = realCoordGradient f x+realCoordGradient u x := by
    ext i; exact Yau.real_coordPartial_add f u hf hu x i
  simp only [realMatrixEnergy,he,map_add,_root_.add_apply]

lemma realMatrixEnergy_mul_left (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (f u v : Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ f y*u y) v x =
      u x*realMatrixEnergy B f v x+f x*realMatrixEnergy B u v x := by
  have he : realCoordGradient (fun y ↦ f y*u y) x =
      u x • realCoordGradient f x+f x • realCoordGradient u x := by
    ext i
    simp only [realCoordGradient,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Yau.real_coordPartial_mul f u hf hu]
    ring
  simp only [realMatrixEnergy,he,map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul]

lemma realMatrixEnergy_const_mul_left (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (a : ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ a*u y) v x = a*realMatrixEnergy B u v x := by
  have he : realCoordGradient (fun y ↦ a*u y) x = a • realCoordGradient u x := by
    ext i; exact Yau.real_coordPartial_const_mul u hu a x i
  simp only [realMatrixEnergy,he,map_smul,_root_.smul_apply,smul_eq_mul]

lemma realTransportDeformation_smooth (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hV : ∀ k, ContDiff ℝ ∞ (fun x ↦ V x k)) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (realTransportDeformation B V v) := by
  apply ContDiff.sum; intro i _
  apply ContDiff.sum; intro j _
  apply ContDiff.sum; intro k _
  exact ((((contDiff_const.mul (hB i j)).mul (Yau.real_coordPartial_smooth _ (hV k) i)).mul
    (Yau.real_coordPartial_smooth v hv k)).mul (Yau.real_coordPartial_smooth v hv j)).sub
      ((((hV k).mul (Yau.real_coordPartial_smooth _ (hB i j) k)).mul
        (Yau.real_coordPartial_smooth v hv i)).mul (Yau.real_coordPartial_smooth v hv j))

lemma realTransportDeformation_compact (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ)
    (hc : HasCompactSupport v) : HasCompactSupport (realTransportDeformation B V v) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦
    HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ ↦
    HasCompactSupport.finset_sum (s := Finset.univ) (fun k _ ↦
      ((hc.fderiv_apply ℝ (Pi.single j 1)).mul_left
        (f := fun x ↦ 2*B x i j*Yau.coordPartial (fun y ↦ V y k) x i*Yau.coordPartial v x k)).sub
      ((hc.fderiv_apply ℝ (Pi.single j 1)).mul_left
        (f := fun x ↦ V x k*Yau.coordPartial (fun y ↦ B y i j) x k*Yau.coordPartial v x i)))))
  exact h

theorem realMatrixEnergy_skew_transport (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ k, ContDiff ℝ ∞ (fun x ↦ V x k)) (hv : ContDiff ℝ ∞ v) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (Yau.weightedSkewTransport gamma V v) v x =
      Yau.pairing (realMatrixEnergy B v v) V x + realTransportDeformation B V v x +
      Yau.weightedDiv gamma V x*realMatrixEnergy B v v x +
      v x*realMatrixEnergy B (Yau.weightedDiv gamma V) v x := by
  unfold Yau.weightedSkewTransport
  rw [realMatrixEnergy_add_left _ _ _ _ (contDiff_const.mul (Yau.pairing_smooth hv hV))
      ((Yau.weightedDiv_smooth hg hgn hV).mul hv),
    realMatrixEnergy_const_mul_left _ _ _ (Yau.pairing_smooth hv hV),
    realMatrixEnergy_mul_left _ _ _ _ (Yau.weightedDiv_smooth hg hgn hV) hv,
    realMatrixEnergy_transport B V v hB hs hV hv]
  ring

end
end Yau.Geometry

end OAI
