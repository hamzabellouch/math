import OAI.Algebra.AuslanderReiten.Ext.ExtPolynomialTransfer

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R]
variable {X : ModuleCat.{u} R}
variable (a b : Ext X X 3)
variable (e : ∀ n : ℕ, Ext X X (3*n) → BinaryKoszul.Piece k n)
variable (hi : ∀ n, Function.Injective (e n))
variable (ha : ∀ (n : ℕ) (x : Ext X X (3*n)),
    e (n+1) (a.comp x (by omega)) = BinaryKoszul.mulX k n (e n x))
variable (hb : ∀ (n : ℕ) (x : Ext X X (3*n)),
    e (n+1) (b.comp x (by omega)) = BinaryKoszul.mulY k n (e n x))
include hi ha hb

theorem cubicCommute_of_functions : a.comp b rfl = b.comp a rfl := by
  have h0a := ha 0 (Ext.mk₀ (𝟙 X))
  have h0b := hb 0 (Ext.mk₀ (𝟙 X))
  simp only [Ext.comp_mk₀_id] at h0a h0b
  apply hi 2
  rw [ha, hb, h0a, h0b]
  exact LinearMap.congr_fun (BinaryKoszul.mul_commute k 0) _

theorem cubicGeneration_of_functions
    (hs : ∀ n, Function.Surjective (e n))
    (hadd : ∀ n x y, e n (x+y) = e n x + e n y)
    (n : ℕ) (x : Ext X X (3*(n+1))) :
    ∃ u v : Ext X X (3*n), x = a.comp u (by omega) + b.comp v (by omega) := by
  obtain ⟨⟨u,v⟩,huv⟩ := BinaryKoszul.row_surjective k n (e (n+1) x)
  obtain ⟨u',hu⟩ := hs n u
  obtain ⟨v',hv⟩ := hs n v
  refine ⟨u',v', hi (n+1) ?_⟩
  rw [hadd,ha,hb,hu,hv]
  exact huv.symm

end ArExplicit.ResolutionProducts

end

end OAI
