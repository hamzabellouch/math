import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticRemainder
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSpatialContinuity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingSmooth
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAutomorphicSections

namespace OAI

/-! The arithmetic Eisenstein-minus-incoming difference is a genuine
continuous automorphic section in the initial convergence half-plane. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticRemainder_continuousAt {s : ℂ} (hs : 2<s.re)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (fun q => cubicThetaArithmeticRemainder q s) p := by
  have hi := (cubicThetaIncomingEisenstein_contDiffOn s).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  exact (cubicThetaEisenstein_continuousAt hs hp).sub hi.continuousAt

def cubicThetaArithmeticSection (s : ℂ) (hs : 2<s.re) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaArithmeticRemainder p.val s,by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaArithmeticRemainder_continuousAt hs p.property).comp
      continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaArithmeticRemainder_automorphy g p.property s⟩

lemma cubicThetaArithmeticSection_norm (s : ℂ) (hs : 2<s.re) (p : CubicThetaPoint) :
    cubicThetaSectionNorm (cubicThetaArithmeticSection s hs) (cubicThetaQuotientMap p)=
      ‖cubicThetaArithmeticRemainder p.val s‖ :=
  cubicThetaSectionNorm_apply _ p

end CubicFirstMoment

end

end OAI
