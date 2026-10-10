import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateRootEnergy

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Ostmann.Construction
attribute [local instance] Classical.propDecidable

theorem positive_product_count_le (R : Finset ℕ+) (U : ℝ)
    (hR : ∀P∈R,(P:ℝ)≤Real.exp U) : (R.card:ℝ)≤Real.exp U := by
  have hs : R.image (fun P : ℕ+ => (P:ℕ)) ⊆ Finset.Icc 1 ⌊Real.exp U⌋₊ := by
    intro n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨P.pos,Nat.le_floor (hR P hP)⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective R (show Function.Injective (fun P : ℕ+ => (P:ℕ)) from fun _ _ h => Subtype.ext h)] at hc
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at hc
  exact (by exact_mod_cast hc : (R.card:ℝ)≤(⌊Real.exp U⌋₊:ℝ)).trans
    (Nat.floor_le (Real.exp_pos _).le)

theorem normalized_external_sum_le {α : Type*} [Fintype α]
    (ν : FinitePrior α) (R : Finset ℕ+) (F : ℕ+→α→ℝ)
    (C T Δ W V M : ℝ) (hC : 0≤C) (hM : 0≤M)
    (hR : ∀P∈R,(P:ℝ)≤Real.exp (T+V))
    (hbound : ∀P∈R,ν.mean (F P)≤C*Real.exp (-T-Δ+W)*M) :
    ν.mean (fun y => ∑P∈R,F P y)≤C*Real.exp (-Δ+W+V)*M := by
  have he : ν.mean (fun y => ∑P∈R,F P y)=∑P∈R,ν.mean (F P) := by
    unfold FinitePrior.mean
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  rw [he]
  calc
    _ ≤ ∑_P∈R,C*Real.exp (-T-Δ+W)*M := Finset.sum_le_sum hbound
    _ = (R.card:ℝ)*(C*Real.exp (-T-Δ+W)*M) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ Real.exp (T+V)*(C*Real.exp (-T-Δ+W)*M) :=
      mul_le_mul_of_nonneg_right (positive_product_count_le R (T+V) hR)
        (mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) hM)
    _ = C*Real.exp (-Δ+W+V)*M := by
      have he : Real.exp (T+V)*Real.exp (-T-Δ+W)=Real.exp (-Δ+W+V) := by
        rw [←Real.exp_add]
        congr 1
        ring
      calc
        _ = C*(Real.exp (T+V)*Real.exp (-T-Δ+W))*M := by ring
        _ = _ := by rw [he]

end Ostmann.Characters.DiagonalEstimate

end

end OAI
