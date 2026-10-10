import OAI.Algebra.AuslanderReiten.Resolutions.BinaryKoszul
import OAI.Algebra.AuslanderReiten.Ext.ExtCentralGeneration

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {X : ModuleCat.{u} R}
variable (a b : Ext X X 3)
variable (e : ∀ n : ℕ, Ext X X (3*n) ≃ₗ[k] BinaryKoszul.Piece k n)
variable
  (ha : ∀ (n : ℕ) (x : Ext X X (3*n)),
    e (n+1) (a.comp x (by omega)) = BinaryKoszul.mulX k n (e n x))
  (hb : ∀ (n : ℕ) (x : Ext X X (3*n)),
    e (n+1) (b.comp x (by omega)) = BinaryKoszul.mulY k n (e n x))
include ha hb

theorem cubicCommute_of_coefficients : a.comp b rfl = b.comp a rfl := by
  have h0a := ha 0 (Ext.mk₀ (𝟙 X))
  have h0b := hb 0 (Ext.mk₀ (𝟙 X))
  simp only [Ext.comp_mk₀_id] at h0a h0b
  apply (e 2).injective
  rw [ha, hb, h0a, h0b]
  exact LinearMap.congr_fun (BinaryKoszul.mul_commute k 0) _

theorem cubicGeneration_of_coefficients (n : ℕ) (x : Ext X X (3*(n+1))) :
    ∃ u v : Ext X X (3*n),
      x = a.comp u (by omega) + b.comp v (by omega) := by
  obtain ⟨⟨u,v⟩,huv⟩ := BinaryKoszul.row_surjective k n (e (n+1) x)
  refine ⟨(e n).symm u, (e n).symm v, ?_⟩
  apply (e (n+1)).injective
  rw [map_add, ha, hb, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact huv.symm

theorem cubicCentral_of_coefficients
    (hzero : ∀ x : Ext X X 0,
      a.comp x (by omega : 3+0=3) = x.comp a (by omega : 0+3=3) ∧
      b.comp x (by omega : 3+0=3) = x.comp b (by omega : 0+3=3)) :
    ∀ (n : ℕ) (x : Ext X X (3*n)),
      a.comp x (by omega : 3+3*n=3*(n+1)) = x.comp a (by omega) ∧
      b.comp x (by omega : 3+3*n=3*(n+1)) = x.comp b (by omega) :=
  cubicCentral_of_generation a b (cubicCommute_of_coefficients a b e ha hb)
    hzero (cubicGeneration_of_coefficients a b e ha hb)

omit hb in
theorem cubicFirst_right_of_coefficients (n : ℕ) (x : Ext X X (3*n))
    (hc : a.comp x (by omega : 3+3*n=3*(n+1)) = x.comp a (by omega)) :
    e (n+1) (x.comp a (by omega)) = BinaryKoszul.mulX k n (e n x) :=
  (congrArg (e (n+1)) hc.symm).trans (ha n x)

omit ha in
theorem cubicSecond_right_of_coefficients (n : ℕ) (x : Ext X X (3*n))
    (hc : b.comp x (by omega : 3+3*n=3*(n+1)) = x.comp b (by omega)) :
    e (n+1) (x.comp b (by omega)) = BinaryKoszul.mulY k n (e n x) :=
  (congrArg (e (n+1)) hc.symm).trans (hb n x)

end ArExplicit.ResolutionProducts

end

end OAI
