import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerIdentitySaturation

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "q" => normToTracial (A := A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "L" => familyLimitTrace (fun τ : TracialState A => τ) U

 theorem comparison_property_SI_projection_large
    (hA : IsNuclear.{0,0} A) (hsimple : TopologicallySimple A) (hcmp : StrictComparison A)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hec : ∀ a : A,Commute E (ι a))
    (hf : 0≤F) (hfn : ‖F‖≤1) (hfc : ∀ a : A,Commute F (ι a))
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → TracialState A,2*t ≤ ((L s).functional (q F)).re) :
    ∃ z : N,‖z‖≤1 ∧ star z*z=E ∧ F*z=z ∧
      (∀ a : A,star z*ι a*z=ι a*E) ∧ (∀ a : A,Commute z (ι a)) := by
  apply NormUltra.identity_excision_saturation U hfree E F hen
  intro m a ε hε
  exact finite_nuclear_identity_excision U hA hsimple hcmp hfree E F he hen hsmall hec
    hf hfn hfc hprojection ht hlarge a hε

end DirectComparison

end
end

end OAI
