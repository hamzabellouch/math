import OAI.Analysis.LipschitzHilbert.Fourier.NarrowBandCutoff
import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValueBound
import OAI.Analysis.LipschitzHilbert.Estimates.PlaneSlopeLipschitz

namespace OAI

/-!
# The precise published band-to-full input

Di Plinio, Guo, Thiele and Zorin-Kranich, *Square functions for bi-Lipschitz
maps and directional operators*, J. Funct. Anal. 275 (2018), 2015--2058,
DOI 10.1016/j.jfa.2018.07.005, author version arXiv:1706.07111,
Corollary 1.4, p₀=2 (printed p. 2), following Corollary 1.3.

We use only its conclusion for the fixed real, even, nonnegative and
nonzero narrow cutoff. Its frequency
support is ±[1,101/100]. This is the inverse Fourier transform of the
paper's Ψ, up to the harmless scalar normalization in the reproducing
formula. We require the hypothesis for all positive widths, which is
stronger than the paper's requirement 0<t<t₀.

The proposition below records the rescaled specialization at R<=1/10000:
set (x,y)=R(X,Y). The resulting field is u(RX,RY), whose vertical
Lipschitz constant is at most R, hence at most 1/100. The width changes
from w to w/R and the same two-dimensional L2 scaling occurs on both
sides. Our sampling uses a minus sign instead of the paper's plus sign;
the symmetric principal values differ by an overall minus sign.

-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def BandToFullInput : Prop :=
  ∀ B : ℝ, 0<B → ∃ C : ℝ, 0<C ∧
    ∀ R : ℝ, 0<R → R≤1/10000 →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
      (∀ w : ℝ, 0<w → ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
        MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
          (schwartzVerticalProjection narrowBandProfile w 0 f)) 2 planeMeasure ∧
        eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
          (schwartzVerticalProjection narrowBandProfile w 0 f)) 2 planeMeasure≤
            ENNReal.ofReal (B*‖f.toLp 2 planeMeasure‖)) →
      ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
        MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f) 2 planeMeasure ∧
        eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f) 2 planeMeasure≤
          ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖)

end LipschitzHilbert.PacketRepresentation

end

end OAI
