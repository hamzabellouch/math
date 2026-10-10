import OAI.Algebra.AuslanderReiten.Homology.VectorCochainKunnethNaturality

namespace OAI

noncomputable section
namespace ArExplicit.VectorCochain
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (k : Type u) [Field k]
variable (P : CochainComplex (ModuleCat.{u} k) ℕ)

abbrev gradedCycles := zeroDifferential k (fun n => P.cycles n)

def cyclesInclusion : gradedCycles k P ⟶ P where
  f n := P.iCycles n
  comm' _ _ _ := by simp [gradedCycles, zeroDifferential]

def cyclesQuotient : gradedCycles k P ⟶ gradedHomology k P where
  f n := P.homologyπ n
  comm' _ _ _ := by simp [gradedCycles, gradedHomology, zeroDifferential]

theorem cyclesMap_cyclesInclusion (n : ℕ) :
    cyclesMap (cyclesInclusion k P) n = (gradedCycles k P).iCycles n := by
  apply (cancel_mono (P.iCycles n)).1
  simp [cyclesInclusion]

theorem homologyMap_cyclesInclusion (n : ℕ) :
    homologyMap (cyclesInclusion k P) n =
      (zeroHomologyIso k (fun i => P.cycles i) n).hom ≫ P.homologyπ n := by
  apply (cancel_epi ((gradedCycles k P).homologyπ n)).1
  rw [homologyπ_naturality, cyclesMap_cyclesInclusion, ← Category.assoc, zeroHomologyIso_π]

theorem cyclesInclusion_comp_splitting_inv :
    cyclesInclusion k P ≫ (splitting k P).inv = cyclesQuotient k P := by
  ext n : 1
  apply (cancel_epi (zeroHomologyIso k (fun i => P.cycles i) n).hom).1
  calc
    (zeroHomologyIso k (fun i => P.cycles i) n).hom ≫
        (cyclesInclusion k P ≫ (splitting k P).inv).f n =
      homologyMap (cyclesInclusion k P ≫ (splitting k P).inv) n ≫
        (zeroHomologyIso k (fun i => P.homology i) n).hom :=
      (zeroHomologyIso_natural k _ n).symm
    _ = (zeroHomologyIso k (fun i => P.cycles i) n).hom ≫ (cyclesQuotient k P).f n := by
      simp only [homologyMap_comp, homologyMap_cyclesInclusion, homologyMap_splitting_inv,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, cyclesQuotient]

def cyclesInclusionHomotopy :
    Homotopy (cyclesInclusion k P) (cyclesQuotient k P ≫ representatives k P) := by
  have hh := ((splitting k P).homotopyInvHomId.compLeftId (cyclesInclusion k P)).symm
  have he : cyclesInclusion k P ≫ ((splitting k P).inv ≫ (splitting k P).hom) =
      cyclesQuotient k P ≫ representatives k P := by
    rw [splitting_hom, ← Category.assoc, cyclesInclusion_comp_splitting_inv]
  exact hh.trans (Homotopy.ofEq he)

variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]
variable (Q : CochainComplex (ModuleCat.{u} k) ℕ)

def tensorCyclesInclusionHomotopy :
    Homotopy (mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) F (.up ℕ))
      (mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) F (.up ℕ) ≫
        mapBifunctorMap (representatives k P) (representatives k Q) F (.up ℕ)) :=
  (mapBifunctorMapHomotopy₁ (cyclesInclusionHomotopy k P)
    (cyclesInclusion k Q) F (.up ℕ)).trans
    ((mapBifunctorMapHomotopy₂ (cyclesQuotient k P ≫ representatives k P)
      (cyclesInclusionHomotopy k Q) F (.up ℕ)).trans
      (Homotopy.ofEq (totalMap_comp F _ _ _ _).symm))

@[reassoc] theorem tensorRepresentatives_kunneth (n : ℕ) :
    homologyMap (mapBifunctorMap (representatives k P) (representatives k Q) F (.up ℕ)) n ≫
      (kunnethIso k F P Q n).hom =
        (totalZeroHomologyIso k F (fun i => P.homology i) (fun i => Q.homology i) n).hom := by
  apply (cancel_epi (totalZeroHomologyIso k F
    (fun i => P.homology i) (fun i => Q.homology i) n).inv).1
  rw [← Category.assoc, ← kunnethIso_inv, Iso.inv_hom_id, Iso.inv_hom_id]

@[reassoc] theorem tensorCycles_kunneth (n : ℕ) :
    homologyMap (mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) F (.up ℕ)) n ≫
      (kunnethIso k F P Q n).hom =
        (totalZeroHomologyIso k F (fun i => P.cycles i) (fun i => Q.cycles i) n).hom ≫
          (mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) F (.up ℕ)).f n := by
  rw [(tensorCyclesInclusionHomotopy k P F Q).homologyMap_eq,
    homologyMap_comp, Category.assoc, tensorRepresentatives_kunneth,
    totalZeroHomologyIso_natural]

end ArExplicit.VectorCochain

end

end OAI
