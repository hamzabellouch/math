import OAI.Geometry.Relativity.CKS.LogPhysicalMassJet
import OAI.Geometry.Relativity.CKS.CollarLapseCoefficient
import OAI.Geometry.Relativity.CKS.ConeSupport

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def lapseVField (z : ℝ) (T F : Point → ℝ) (y : Point) : ℝ :=
  (1/(1+z^2))*(2*T y+z^3*(T y*T y)-2*F y)
def lapseRadField (z : ℝ) (T F : Point → ℝ) (y : Point) : ℝ := 1+z^3*lapseVField z T F y
def lapseDField (z : ℝ) (d : Point → ℝ) (y : Point) : ℝ := 1+z^3*d y
def lapseAField (z : ℝ) (T F d : Point → ℝ) (y : Point) : ℝ :=
  (lapseVField z T F y*(1/(Real.sqrt (lapseRadField z T F y)+1))-d y)*(1/lapseDField z d y)
def lapseNormalizedField (z : ℝ) (T F d : Point → ℝ) (y : Point) : ℝ :=
  Real.sqrt ((z^2+(1+z^3*T y)^2-2*z^3*F y)/(1+z^2))/(1+z^3*d y)

lemma lapseVField_diff (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 2 (lapseVField z T F) x := by
  exact (((hT.const_smul (2:ℝ)).add ((hT.mul hT).const_smul (z^3))).sub
    (hF.const_smul (2:ℝ))).const_smul (1/(1+z^2))
lemma lapseRadField_diff (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 2 (lapseRadField z T F) x :=
  contDiffAt_const.add ((lapseVField_diff z hT hF).const_smul (z^3))
lemma lapseDField_diff (z : ℝ) {d : Point → ℝ} {x : Point} (hd : ContDiffAt ℝ 2 d x) :
    ContDiffAt ℝ 2 (lapseDField z d) x := contDiffAt_const.add (hd.const_smul (z^3))
lemma lapseAField_diff (z : ℝ) {T F d : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (hd : ContDiffAt ℝ 2 d x)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    ContDiffAt ℝ 2 (lapseAField z T F d) x := by
  have hv := lapseVField_diff z hT hF
  have hs := ((lapseRadField_diff z hT hF).sqrt hr.ne').add (contDiffAt_const (c := (1:ℝ)))
  have hs0 : Real.sqrt (lapseRadField z T F x)+1 ≠ 0 := by positivity
  exact ((hv.mul (contDiffAt_const.div hs hs0)).sub hd).mul
    (contDiffAt_const.div (lapseDField_diff z hd) h0)

lemma actual_lapseVField (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (d : ScalarJet) :
    actualScalarJet (lapseVField z T F) x = lapseV (z,actualScalarJet T x,actualScalarJet F x,d) := by
  unfold lapseVField
  erw [actualScalarJet_smul _ (((hT.const_smul (2:ℝ)).add ((hT.mul hT).const_smul (z^3))).sub
      (hF.const_smul (2:ℝ))),
    actualScalarJet_sub ((hT.const_smul (2:ℝ)).add ((hT.mul hT).const_smul (z^3))) (hF.const_smul (2:ℝ)),
    actualScalarJet_add (hT.const_smul (2:ℝ)) ((hT.mul hT).const_smul (z^3)),
    actualScalarJet_smul _ hT,actualScalarJet_smul _ (hT.mul hT),actualScalarJet_mul hT hT,
    actualScalarJet_smul _ hF]
  rfl
lemma actual_lapseRadField (z : ℝ) {T F : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (d : ScalarJet) :
    actualScalarJet (lapseRadField z T F) x = lapseRad (z,actualScalarJet T x,actualScalarJet F x,d) := by
  unfold lapseRadField
  erw [actualScalarJet_add contDiffAt_const ((lapseVField_diff z hT hF).const_smul (z^3)),
    actualScalarJet_const,actualScalarJet_smul _ (lapseVField_diff z hT hF),actual_lapseVField z hT hF d]
  rfl
lemma actual_lapseDField (z : ℝ) {d : Point → ℝ} {x : Point}
    (hd : ContDiffAt ℝ 2 d x) (T F : ScalarJet) :
    actualScalarJet (lapseDField z d) x = lapseD (z,T,F,actualScalarJet d x) := by
  unfold lapseDField
  erw [actualScalarJet_add contDiffAt_const (hd.const_smul (z^3)),actualScalarJet_const,actualScalarJet_smul _ hd]
  rfl
lemma actual_lapseAField (z : ℝ) {T F d : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (hd : ContDiffAt ℝ 2 d x)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    actualScalarJet (lapseAField z T F d) x =
      lapseA (z,actualScalarJet T x,actualScalarJet F x,actualScalarJet d x) := by
  have hv := lapseVField_diff z hT hF
  have hs := ((lapseRadField_diff z hT hF).sqrt hr.ne').add (contDiffAt_const (c := (1:ℝ)))
  have hs0 : Real.sqrt (lapseRadField z T F x)+1 ≠ 0 := by positivity
  have hi := (contDiffAt_const (c := (1:ℝ))).div hs hs0
  have hid := (contDiffAt_const (c := (1:ℝ))).div (lapseDField_diff z hd) h0
  unfold lapseAField
  erw [actualScalarJet_mul ((hv.mul hi).sub hd) hid,actualScalarJet_sub (hv.mul hi) hd,
    actualScalarJet_mul hv hi,actual_reciprocal hs hs0,
    actualScalarJet_add ((lapseRadField_diff z hT hF).sqrt hr.ne') contDiffAt_const,
    actualScalarJet_sqrt (lapseRadField_diff z hT hF) hr,actualScalarJet_const,
    actual_reciprocal (lapseDField_diff z hd) h0,
    actual_lapseVField z hT hF (actualScalarJet d x),
    actual_lapseRadField z hT hF (actualScalarJet d x),
    actual_lapseDField z hd (actualScalarJet T x) (actualScalarJet F x)]
  rfl

lemma lapseAField_identity (z : ℝ) (T F d : Point → ℝ) (x : Point)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    lapseNormalizedField z T F d x = 1+z^3*lapseAField z T F d x := by
  have hp : (z,constantJet (T x),constantJet (F x),constantJet (d x)) ∈ lapseCoefficientRegion := ⟨hr,h0⟩
  exact lapseA_identity hp

theorem actual_normalized_lapse_coefficient (z : ℝ) {T F d : Point → ℝ} {x : Point}
    (hT : ContDiffAt ℝ 2 T x) (hF : ContDiffAt ℝ 2 F x) (hd : ContDiffAt ℝ 2 d x)
    (hr : 0 < lapseRadField z T F x) (h0 : lapseDField z d x ≠ 0) :
    actualScalarJet (lapseNormalizedField z T F d) x = constantJet 1+
      z^3 • lapseA (z,actualScalarJet T x,actualScalarJet F x,actualScalarJet d x) := by
  have her : ∀ᶠ y in 𝓝 x, 0 < lapseRadField z T F y :=
    (lapseRadField_diff z hT hF).continuousAt.eventually (eventually_gt_nhds hr)
  have hed : ∀ᶠ y in 𝓝 x, lapseDField z d y ≠ 0 :=
    (lapseDField_diff z hd).continuousAt.eventually (eventually_ne_nhds h0)
  have he : lapseNormalizedField z T F d =ᶠ[𝓝 x] (fun y => 1+z^3*lapseAField z T F d y) := by
    filter_upwards [her,hed] with y hyr hyd
    exact lapseAField_identity z T F d y hyr hyd
  erw [actualScalarJet_congr he,actualScalarJet_add contDiffAt_const
    ((lapseAField_diff z hT hF hd hr h0).const_smul (z^3)),actualScalarJet_const,
    actualScalarJet_smul _ (lapseAField_diff z hT hF hd hr h0),actual_lapseAField z hT hF hd hr h0]

end
end CKSAngularGeometry

end

end OAI
