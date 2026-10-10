import OAI.Algebra.Finitistic.Bimodule.BimoduleShiftColumns
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalDifferential

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {Z : CochainComplex (ModuleCat.{u} B) ℤ}

/-- Reindexing the unchanged input degree commutes with the original bimodule map. -/
theorem termMap_transport {a b q₁ q₂ q₃ q₄ : ℤ} (f : P.X a ⟶ P.X b)
    (h₁₂ : q₁=q₂) (h₃₄ : q₃=q₄) (h₁₃ : q₁=q₃) (h₂₄ : q₂=q₄) :
    ModuleCat.ofHom (termMap (Z := Z) (Z' := Z) f (eqToHom (congrArg Z.X h₁₂))) ≫
      eqToHom (congrArg (fun q => ModuleCat.of B (Term k B P Z b q)) h₂₄) =
    eqToHom (congrArg (fun q => ModuleCat.of B (Term k B P Z a q)) h₁₃) ≫
      ModuleCat.ofHom (termMap (Z := Z) (Z' := Z) f (eqToHom (congrArg Z.X h₃₄))) := by
  subst q₂ q₃ q₄
  simp

variable (k B P Z)

theorem horizontal_shift_reindex (s n m a b : ℤ) (h : n+1=m) (hab : a+1=b) :
    ModuleCat.ofHom (horizontalBetween k B P (Z⟦s⟧) n m a b h hab) ≫
      (shiftReindex k B P Z s b m).hom =
    (shiftReindex k B P Z s a n).hom ≫
      ModuleCat.ofHom (horizontalBetween k B P Z (n+s) (m+s) a b (by omega) hab) :=
  termMap_transport (k := k) (B := B) (P := P) (Z := Z)
    (q₁ := n + -a + s) (q₂ := m + -b + s)
    (q₃ := n+s + -a) (q₄ := m+s + -b)
    (P.d a b) (by omega) (by omega) (by omega) (by omega)

/-- The Koszul sign compensates exactly for the sign on the shifted horizontal differential. -/
theorem entry_shift (s n m a b : ℤ) (h : n+1=m) :
    ModuleCat.ofHom (entryBetween k B P (Z⟦s⟧) n m a b h) ≫
      ((shiftColumnIso k B P Z s b).hom).f m =
    ((shiftColumnIso k B P Z s a).hom).f n ≫
      (s.negOnePow • ModuleCat.ofHom (entryBetween k B P Z (n+s) (m+s) a b (by omega))) := by
  rw [shiftColumn_hom_f,shiftColumn_hom_f]
  unfold entryBetween
  split_ifs with hab
  · erw [Linear.comp_units_smul,Linear.units_smul_comp,Linear.comp_units_smul,
      smul_smul,horizontal_shift_reindex]
    congr 1
    rw [← Int.negOnePow_add]
    congr 1
    rw [← hab]
    simp [mul_add,add_comm]
  · erw [CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
    rfl
end LittleFinitistic.BimoduleTotal

end

end OAI
