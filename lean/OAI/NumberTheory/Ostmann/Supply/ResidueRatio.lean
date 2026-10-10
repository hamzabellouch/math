import OAI.NumberTheory.Ostmann.Preliminaries.LocalUniformity
import OAI.NumberTheory.Ostmann.Preliminaries.Sizes
import OAI.NumberTheory.Ostmann.Supply.LogRatioCauchy

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators
open Ostmann.Preliminaries

def actualSupport (d : Decomposition) (p : ℕ) : Finset (ZMod p) :=
  if hp : p=0 then ∅ else letI : NeZero p := ⟨hp⟩; d.residueSupport p

theorem actualSupport_eq (d : Decomposition) (p : ℕ) [NeZero p] :
    actualSupport d p = d.residueSupport p := by
  simp [actualSupport,NeZero.ne p]

def actualRatio (d : Decomposition) (p : ℕ) : ℝ :=
  (p:ℝ)/((actualSupport d p).card:ℝ)-1

theorem actualRatio_eq_density (d : Decomposition) (p : ℕ) [NeZero p] :
    actualRatio d p = (1-d.residueDensity p)/d.residueDensity p := by
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hs : ((d.residueSupport p).card:ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (d.residueSupport_nonempty p)
  simp only [actualRatio,actualSupport_eq,Decomposition.residueDensity]
  field_simp

theorem actualRatio_pos (d : Decomposition) {p : ℕ} (hp : p.Prime) : 0<actualRatio d p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [actualRatio_eq_density]
  exact div_pos (sub_pos.mpr (d.residueDensity_lt_one p hp)) (d.residueDensity_pos p hp)

theorem actualRatio_penalty (d : Decomposition) (p : ℕ) [NeZero p] (hp : p.Prime) :
    actualRatio d p+(actualRatio d p)⁻¹-2 =
      (d.residueDensity p)⁻¹+(1-d.residueDensity p)⁻¹-4 := by
  have h0 := (d.residueDensity_pos p hp).ne'
  have h1 := (sub_pos.mpr (d.residueDensity_lt_one p hp)).ne'
  rw [actualRatio_eq_density]
  field_simp
  ring

def ratioWeightedSum (d : Decomposition) (Q : ℕ) : ℝ :=
  ∑ p∈Q.primesLE,(actualRatio d p+(actualRatio d p)⁻¹-2)*Real.log p/(p:ℝ)

theorem ratioWeightedSum_nonneg (d : Decomposition) (Q : ℕ) : 0 ≤ ratioWeightedSum d Q := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  exact div_nonneg (mul_nonneg (ratio_penalty_nonneg (actualRatio_pos d hprime))
    (Real.log_nonneg (by exact_mod_cast hprime.one_le))) (Nat.cast_nonneg _)

theorem ratioWeightedSum_mono (d : Decomposition) {Q R : ℕ} (hQR : Q≤R) :
    ratioWeightedSum d Q ≤ ratioWeightedSum d R := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hQ,hp'⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hQ.trans hQR,hp'⟩
  · intro p hp _
    have hprime := (Nat.mem_primesLE.mp hp).2
    exact div_nonneg (mul_nonneg (ratio_penalty_nonneg (actualRatio_pos d hprime))
      (Real.log_nonneg (by exact_mod_cast hprime.one_le))) (Nat.cast_nonneg _)

theorem ratioWeightedSum_le_collision (d : Decomposition) (X : ℕ) :
    ratioWeightedSum d (collisionScale 4 X) ≤ upperWindowCollision d X := by
  have h := weighted_density_penalty_le d (collisionScale 4 X)
    (fun i : upperWindow d.A X => i.val) (uniformWindowMass d.A X)
    (fun i : upperWindow d.B X => i.val) (uniformWindowMass d.B X)
  apply le_trans (le_of_eq _) h
  unfold ratioWeightedSum
  rw [← sum_primeUpTo]
  apply Finset.sum_congr rfl
  intro p hp
  rw [actualRatio_penalty d p.val (primeUpTo_prime p)]
  ring

end Ostmann.Supply

end

end OAI
