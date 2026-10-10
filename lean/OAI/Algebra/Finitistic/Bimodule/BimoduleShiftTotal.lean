import OAI.Algebra.Finitistic.Bimodule.BimoduleShiftHorizontal

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

def shiftTermIso (s n : ℤ) :
    (total k B P p hp (Z⟦s⟧)).X n ≅ ((total k B P p hp Z)⟦s⟧).X n :=
  (LinearEquiv.piCongrRight (fun i : Fin l =>
    (HomologicalComplex.Hom.isoApp (shiftColumnIso k B P Z s (p i)) n).toLinearEquiv)).toModuleIso

@[simp] theorem shiftTerm_hom_apply (s n : ℤ)
    (x : TotalTerm k B P p (Z⟦s⟧) n) (i : Fin l) :
    (shiftTermIso k B P p hp Z s n).hom.hom x i =
      (((shiftColumnIso k B P Z s (p i)).hom).f n).hom (x i) := rfl

/-- The complete signed total commutes with every integer shift, with the actual horizontal maps. -/
def shiftTotalIso (s : ℤ) : total k B P p hp (Z⟦s⟧) ≅ (total k B P p hp Z)⟦s⟧ :=
  HomologicalComplex.Hom.isoOfComponents (shiftTermIso k B P p hp Z s) (by
    intro n m h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    have hv := congrArg (fun f => f.hom (x j)) ((shiftColumnIso k B P Z s (p j)).hom.comm n m)
    have hh (i : Fin l) := congrArg (fun f => f.hom (x i))
      (entry_shift k B P Z s n m (p i) (p j) h)
    change s.negOnePow • (((total k B P p hp Z).d (n+s) (m+s)).hom
      ((shiftTermIso k B P p hp Z s n).hom.hom x) j) =
      (((shiftColumnIso k B P Z s (p j)).hom).f m).hom
        (((total k B P p hp (Z⟦s⟧)).d n m).hom x j)
    erw [total_d_apply k B P Z p hp (n+s) (m+s) (by change n+1=m at h; omega),
      total_d_apply k B P (Z⟦s⟧) p hp n m h]
    erw [map_add, map_sum, smul_add, Finset.smul_sum]
    refine congrArg₂ HAdd.hAdd ?_ ?_
    · change s.negOnePow • ((((columnFunctor k B P (p j)).obj Z).d (n+s) (m+s)).hom
          (((shiftColumnIso k B P Z s (p j)).hom.f n).hom (x j))) =
        ((shiftColumnIso k B P Z s (p j)).hom.f m).hom
          ((((columnFunctor k B P (p j)).obj (Z⟦s⟧)).d n m).hom (x j)) at hv
      exact (congrArg (s.negOnePow • ·)
        (fullColumn_d k B P Z (p j) (n+s) (m+s)
          (((shiftColumnIso k B P Z s (p j)).hom.f n).hom (x j)))).symm.trans
        (hv.trans (congrArg (((shiftColumnIso k B P Z s (p j)).hom.f m).hom)
          (fullColumn_d k B P (Z⟦s⟧) (p j) n m (x j))))
    · apply Finset.sum_congr rfl
      intro i _
      exact hh i |>.symm)
end LittleFinitistic.BimoduleTotal

end

end OAI
