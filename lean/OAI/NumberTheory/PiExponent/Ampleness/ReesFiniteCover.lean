import OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional
import OAI.NumberTheory.PiExponent.Ampleness.ReesPolynomialPresentation

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace PiExponent.ReesFiniteCover
open PiExponentSeshadri.ReesGrading
variable {R J : Type} [CommRing R] (I : Ideal R) (a : J → I)
variable (ha : Ideal.span (Set.range fun j => (a j).val) = I)
local instance chartOpenImmersion (j : J) : IsOpenImmersion ((chartCover I).f (a j)) :=
  (chartCover I).map_prop (a j)
include ha

theorem adjoin_eq_top : Algebra.adjoin R (Set.range fun j => generator I (a j)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  apply top_unique
  intro z hz
  exact ReesPolynomialPresentation.presentation_surjective I a ha z

theorem adjoin_zero_eq_top :
    Algebra.adjoin (piece I 0) (Set.range fun j => generator I (a j)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  have hh : z ∈ Algebra.adjoin R (Set.range fun j => generator I (a j)) := by
    rw [adjoin_eq_top I a ha]
    trivial
  induction hh using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact (Algebra.adjoin (piece I 0) (Set.range fun j => generator I (a j))).algebraMap_mem
      (zeroEquiv I r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem iSup_generator_basicOpen :
    (⨆ j, Proj.basicOpen (piece I) (generator I (a j))) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (piece I) (fun j => generator I (a j))
    (fun j => ⟨1, generator_mem I (a j)⟩) (adjoin_zero_eq_top I a ha)

theorem iSup_generator_opensRange :
    (⨆ j, ((chartCover I).f (a j)).opensRange) = ⊤ := by
  have h j : ((chartCover I).f (a j)).opensRange =
      Proj.basicOpen (piece I) (generator I (a j)) :=
    Proj.opensRange_awayι (piece I) _ (generator_mem I (a j)) (by decide)
  simp_rw [h]
  exact iSup_generator_basicOpen I a ha

def cover : (affineBlowup I).AffineOpenCover where
  I₀ := J
  X j := CommRingCat.of (chart I (a j))
  f j := (chartCover I).f (a j)
  map_prop j := (chartCover I).map_prop (a j)
  idx x := (Opens.mem_iSup.mp ((iSup_generator_opensRange I a ha).ge (Set.mem_univ x))).choose
  covers x :=
    (Opens.mem_iSup.mp ((iSup_generator_opensRange I a ha).ge (Set.mem_univ x))).choose_spec

end PiExponent.ReesFiniteCover
end

end OAI
