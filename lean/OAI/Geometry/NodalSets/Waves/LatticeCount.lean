import Mathlib.SetTheory.Cardinal.Finite
import OAI.Geometry.NodalSets.Waves.LatticeGeometry

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma lattice_scale_eq_inv_sqrt (n : ℕ) : (n:ℝ)^(-1/2:ℝ) = (Real.sqrt n)⁻¹ := by
  rw [show (-1/2:ℝ) = -(1/2) by ring,Real.rpow_neg,Real.sqrt_eq_rpow]
  positivity

theorem source_grid_card_bound {U : Set Coord} (hU : Bornology.IsBounded U) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → (Nat.card (SourceGrid U n) : ℝ) ≤ C*(n:ℝ)^2 := by
  obtain ⟨B,hB,hbound⟩ := hU.exists_pos_norm_le
  refine ⟨(2*B+3)^4,by positivity,?_⟩
  intro n hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
  have hs2 : (Real.sqrt n)^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
  let M : ℤ := ⌈B*Real.sqrt n⌉
  have hM0 : 0 ≤ M := Int.ceil_nonneg (by positivity)
  have hMc : (M:ℝ) < B*Real.sqrt n+1 := Int.ceil_lt_add_one _
  have hcoords (z : SourceGrid U n) (i : Fin 4) : z.val i ∈ Icc (-M) M := by
    have hi := (norm_le_pi_norm (scaledLatticePoint n z) i).trans (hbound _ z.property)
    change |(n:ℝ)^(-1/2:ℝ)*(z.val i:ℝ)| ≤ B at hi
    rw [lattice_scale_eq_inv_sqrt,abs_mul,abs_of_pos (inv_pos.mpr hs)] at hi
    have hmul := mul_le_mul_of_nonneg_left hi hs.le
    have hcancel : Real.sqrt n * ((Real.sqrt n)⁻¹ * |(z.val i:ℝ)|) = |(z.val i:ℝ)| := by
      field_simp
    rw [hcancel] at hmul
    have ha : |(z.val i:ℝ)| ≤ (M:ℝ) := hmul.trans (by simpa [mul_comm] using Int.le_ceil (B*Real.sqrt n))
    have hp := abs_le.mp ha
    exact ⟨by exact_mod_cast hp.1,by exact_mod_cast hp.2⟩
  let f : SourceGrid U n → (Fin 4 → Icc (-M) M) := fun z i ↦ ⟨z.val i,hcoords z i⟩
  have hfi : Function.Injective f := by
    intro z w h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have hc := Nat.card_le_card_of_injective f hfi
  have hbox : Nat.card (Fin 4 → Icc (-M) M) = ((2*M+1).toNat)^4 := by
    rw [Nat.card_fun]
    simp [Nat.card_eq_fintype_card,Int.card_Icc,show M+1- -M = 2*M+1 by ring]
  rw [hbox] at hc
  have hcR : (Nat.card (SourceGrid U n):ℝ) ≤ ((2*M+1).toNat:ℝ)^4 := by exact_mod_cast hc
  have hcast : ((2*M+1).toNat:ℝ) = 2*(M:ℝ)+1 := by
    have hi : ((2*M+1).toNat:ℤ) = 2*M+1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hi
  rw [hcast] at hcR
  have hmnon : (0:ℝ) ≤ 2*(M:ℝ)+1 := by exact_mod_cast (show (0:ℤ) ≤ 2*M+1 by omega)
  have hmle : 2*(M:ℝ)+1 ≤ (2*B+3)*Real.sqrt n := by nlinarith
  have hpow := pow_le_pow_left₀ hmnon hmle 4
  calc
    _ ≤ (2*(M:ℝ)+1)^4 := hcR
    _ ≤ ((2*B+3)*Real.sqrt n)^4 := hpow
    _ = (2*B+3)^4*(n:ℝ)^2 := by
      rw [mul_pow,show (Real.sqrt n)^4 = ((Real.sqrt n)^2)^2 by ring,hs2]

theorem source_coefficient_card_bound {U : Set Coord} (hU : Bornology.IsBounded U) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → (Nat.card (SourceGrid U n × Fin 3):ℝ) ≤ C*(n:ℝ)^2 := by
  obtain ⟨C,hC,hb⟩ := source_grid_card_bound hU
  refine ⟨3*C,by positivity,?_⟩
  intro n hn
  have h := hb n hn
  rw [Nat.card_prod]
  norm_num
  nlinarith

end
end Yau.Geometry

end OAI
