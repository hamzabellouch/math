import OAI.NumberTheory.PiExponent.Cohomology.CechHigher

namespace OAI

namespace PiExponent.ProjectiveTwistCech

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open PiExponent.ProjectiveMonomialCech

universe u
variable {X : Scheme.{u}} {ι K : Type u} [Fintype ι] [AddCommGroup K]

private abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

structure LaurentCechPresentation (U : ι → X.Opens) (M : X.Modules) (d : ℤ) where
  coefficient : ∀ q (t : Fin (q + 1) → ι),
    (schemeFreeOpen (GeometrySupport.CechHigher.intersection U t) ⟶ M) →+
      Laurent ι K d
  injective : ∀ q t, Function.Injective (coefficient q t)
  regular : ∀ q t b, RegularOn (Set.range t) (coefficient q t b)
  surjective : ∀ q t p, RegularOn (Set.range t) p → ∃ b, coefficient q t b = p
  restriction : ∀ q (t : Fin (q + 2) → ι) (k : Fin (q + 2)) b,
    coefficient (q + 1) t
      (GeometrySupport.CechOne.restrictHom X.ringCatSheaf
        (GeometrySupport.CechHigher.faceLE U t k) b) =
      coefficient q (t ∘ k.succAbove) b

namespace LaurentCechPresentation

variable {U : ι → X.Opens} {M : X.Modules} {d : ℤ}
    (P : LaurentCechPresentation (K := K) U M d)

def toLaurent {q : ℕ} (c : GeometrySupport.CechHigher.Cochain X.ringCatSheaf U M q) :
    ProjectiveMonomialCechHigher.Cochain ι (Laurent ι K d) q :=
  fun t => P.coefficient q t (c t)

theorem toLaurent_differential {q : ℕ}
    (c : GeometrySupport.CechHigher.Cochain X.ringCatSheaf U M q) :
    P.toLaurent (GeometrySupport.CechHigher.differential X.ringCatSheaf U M c) =
      ProjectiveMonomialCechHigher.differential (P.toLaurent c) := by
  funext t
  simp only [toLaurent, GeometrySupport.CechHigher.differential,
    ProjectiveMonomialCechHigher.differential]
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, P.restriction]

include P in

theorem hasPrimitives (hd : 0 ≤ d) (q : ℕ) :
    GeometrySupport.CechHigher.HasPrimitives X.ringCatSheaf U M q := by
  intro c hc
  have hregular : ProjectiveMonomialCechHigher.Regular (P.toLaurent c) :=
    fun t => P.regular _ t _
  have hclosed : ProjectiveMonomialCechHigher.differential (P.toLaurent c) = 0 := by
    rw [← P.toLaurent_differential, hc]
    funext t
    exact map_zero _
  obtain ⟨B, hB, hCB⟩ :=
    ProjectiveMonomialCechHigher.nonnegative_twist_cech_exact_all_positive hd
      (P.toLaurent c) hregular hclosed
  choose b hb using fun t => P.surjective q t (B t) (hB t)
  refine ⟨b, ?_⟩
  funext t
  apply P.injective (q + 1) t
  have hcochain : P.toLaurent b = B := funext hb
  have h := congrFun (P.toLaurent_differential b) t
  rw [hcochain, hCB] at h
  exact h

end LaurentCechPresentation

end
end PiExponent.ProjectiveTwistCech

end OAI
