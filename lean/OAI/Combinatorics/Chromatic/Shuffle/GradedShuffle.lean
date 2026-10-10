import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ShuffleFiltration
import OAI.Combinatorics.Chromatic.Walls.LinearFiltrationBilinear

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def gradeShuffle (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : d≠0) (he : e≠0) (hdθ : slope c η d=θ) (heθ : slope c η e=θ)
    (U V : ℤ) : SourceAssociatedGrade a c η hc θ d U →ₗ[ℚ]
      SourceAssociatedGrade a c η hc θ e V →ₗ[ℚ]
        SourceAssociatedGrade a c η hc θ (d+e) (U+V) :=
  LinearFiltration.bilinear (sourceFiltration a c η hc θ d U)
    (sourceFiltration a c η hc θ d (U+1))
    (sourceFiltration a c η hc θ e V) (sourceFiltration a c η hc θ e (V+1))
    (sourceFiltration a c η hc θ (d+e) (U+V))
    (sourceFiltration a c η hc θ (d+e) (U+V+1))
    (shuffleB a c η hc d e (hdθ.trans heθ.symm))
    (fun f hf g hg=>shuffleB_filtered a c η hc θ hχ d e hd he hdθ heθ U V f g hf hg)
    (fun f hf g hg=>by
      simpa only [add_assoc,add_comm (1:ℤ) V] using
        shuffleB_filtered a c η hc θ hχ d e hd he hdθ heθ (U+1) V f g hf hg)
    (fun f hf g hg=>by
      simpa only [add_assoc] using
        shuffleB_filtered a c η hc θ hχ d e hd he hdθ heθ U (V+1) f g hf hg)

lemma gradeShuffle_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : d≠0) (he : e≠0) (hdθ : slope c η d=θ) (heθ : slope c η e=θ)
    (U V : ℤ) (f : sourceFiltration a c η hc θ d U) (g : sourceFiltration a c η hc θ e V) :
    gradeShuffle a c η hc θ hχ d e hd he hdθ heθ U V
      (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)=
      (Submodule.Quotient.mk ⟨shuffleB a c η hc d e (hdθ.trans heθ.symm) f.val g.val,
        shuffleB_filtered a c η hc θ hχ d e hd he hdθ heθ U V f.val g.val f.property g.property⟩ :
        SourceAssociatedGrade a c η hc θ (d+e) (U+V)) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
