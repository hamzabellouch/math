import OAI.Algebra.AuslanderReiten.Homology.VectorCochainKunneth

namespace OAI

noncomputable section
namespace ArExplicit.VectorCochain
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (k : Type u) [Field k]

@[reassoc] theorem zeroHomologyIso_natural {X Y : ℕ → ModuleCat.{u} k}
    (f : zeroDifferential k X ⟶ zeroDifferential k Y) (n : ℕ) :
    homologyMap f n ≫ (zeroHomologyIso k Y n).hom =
      (zeroHomologyIso k X n).hom ≫ f.f n := by
  apply (cancel_epi ((zeroDifferential k X).homologyπ n)).1
  rw [homologyπ_naturality_assoc, zeroHomologyIso_π, ← Category.assoc,
    zeroHomologyIso_π]
  simp

variable {P Q : CochainComplex (ModuleCat.{u} k) ℕ}

def gradedMap (f : P ⟶ Q) : gradedHomology k P ⟶ gradedHomology k Q where
  f n := homologyMap f n
  comm' _ _ _ := by simp [gradedHomology, zeroDifferential]

@[simp] theorem homologyMap_splitting_inv (n : ℕ) :
    homologyMap (splitting k P).inv n =
      (zeroHomologyIso k (fun i => P.homology i) n).inv := by
  have he : (splitting k P).toHomologyIso n =
      zeroHomologyIso k (fun i => P.homology i) n := by
    apply Iso.ext
    change homologyMap (splitting k P).hom n = _
    rw [splitting_hom, homologyMap_representatives]
  exact congrArg Iso.inv he

theorem representatives_comp_splitting_inv (f : P ⟶ Q) :
    representatives k P ≫ f ≫ (splitting k Q).inv = gradedMap k f := by
  ext n : 1
  apply (cancel_epi (zeroHomologyIso k (fun i => P.homology i) n).hom).1
  calc
    (zeroHomologyIso k (fun i => P.homology i) n).hom ≫
        (representatives k P ≫ f ≫ (splitting k Q).inv).f n =
      homologyMap (representatives k P ≫ f ≫ (splitting k Q).inv) n ≫
        (zeroHomologyIso k (fun i => Q.homology i) n).hom :=
      (zeroHomologyIso_natural k _ n).symm
    _ = (zeroHomologyIso k (fun i => P.homology i) n).hom ≫ (gradedMap k f).f n := by
      simp only [homologyMap_comp, homologyMap_representatives, homologyMap_splitting_inv,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, gradedMap]

def representativesNaturality (f : P ⟶ Q) :
    Homotopy (representatives k P ≫ f) (gradedMap k f ≫ representatives k Q) := by
  have hh := ((splitting k Q).homotopyInvHomId.compLeftId
    (representatives k P ≫ f)).symm
  have he : (representatives k P ≫ f) ≫
      ((splitting k Q).inv ≫ (splitting k Q).hom) =
      gradedMap k f ≫ representatives k Q := by
    rw [splitting_hom, ← Category.assoc, Category.assoc (representatives k P) f,
      representatives_comp_splitting_inv]
  exact hh.trans (Homotopy.ofEq he)

end ArExplicit.VectorCochain

end

end OAI
