import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedMaps
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomNaturality

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} (n : ℤ)
include k

theorem fullHomPostcomp_congr {f g : L ⟶ M}
    (h : (HomotopyCategory.quotient C _).map f = (HomotopyCategory.quotient C _).map g)
    (x : CohomologyClass K L n) : fullHomPostcomp f n x = fullHomPostcomp g n x := by
  apply (fullHomShiftedHomotopyEquiv k K M n).injective
  rw [fullHomShiftedHomotopyEquiv_postcomp, fullHomShiftedHomotopyEquiv_postcomp, h]

theorem fullHomPrecomp_congr {f g : K ⟶ L}
    (h : (HomotopyCategory.quotient C _).map f = (HomotopyCategory.quotient C _).map g)
    (x : CohomologyClass L M n) : fullHomPrecomp f n x = fullHomPrecomp g n x := by
  apply (fullHomShiftedHomotopyEquiv k K M n).injective
  rw [fullHomShiftedHomotopyEquiv_precomp, fullHomShiftedHomotopyEquiv_precomp, h]

theorem fullHomPostcomp_id (x : CohomologyClass K L n) :
    fullHomPostcomp (𝟙 L) n x = x := by
  apply (fullHomShiftedHomotopyEquiv k K L n).injective
  rw [fullHomShiftedHomotopyEquiv_postcomp, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

theorem fullHomPrecomp_id (x : CohomologyClass K L n) :
    fullHomPrecomp (𝟙 K) n x = x := by
  apply (fullHomShiftedHomotopyEquiv k K L n).injective
  rw [fullHomShiftedHomotopyEquiv_precomp, CategoryTheory.Functor.map_id, Category.id_comp]

theorem fullHomPostcomp_homotopy_inverse (f : L ⟶ M) (g : M ⟶ L)
    (h : (HomotopyCategory.quotient C _).map (f ≫ g) = 𝟙 _)
    (x : CohomologyClass K L n) : fullHomPostcomp g n (fullHomPostcomp f n x) = x := by
  rw [fullHomPostcomp_comp]
  rw [fullHomPostcomp_congr k n (h.trans (CategoryTheory.Functor.map_id _ _).symm),
    fullHomPostcomp_id k n]

theorem fullHomPostcomp_bijective (f : L ⟶ M) (g : M ⟶ L)
    (hfg : (HomotopyCategory.quotient C _).map (f ≫ g) = 𝟙 _)
    (hgf : (HomotopyCategory.quotient C _).map (g ≫ f) = 𝟙 _) :
    Function.Bijective (fullHomPostcomp (K := K) f n) := by
  constructor
  · intro x y h
    have hh := congrArg (fullHomPostcomp g n) h
    simpa only [fullHomPostcomp_homotopy_inverse k n f g hfg] using hh
  · intro x
    exact ⟨fullHomPostcomp g n x, fullHomPostcomp_homotopy_inverse k n g f hgf x⟩

end ArExplicit

end

end OAI
