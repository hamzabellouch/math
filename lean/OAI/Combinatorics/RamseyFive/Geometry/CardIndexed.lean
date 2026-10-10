import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.CardMul
import OAI.Combinatorics.RamseyFive.Decoding.ScalarConditions

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SharpRamseyFive.ProjectiveRichLines
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K I : Type*} [Field K] [Fintype I]

omit [Fintype I] in
lemma card_indexed (X : Finset (ℙ K (I → K))) (U : Submodule K (I → K)) :
    (Finset.univ.filter (fun y : X => y.val.rep ∈ U)).card =
      (X.filter (fun y => y.submodule ≤ U)).card := by
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    refine Finset.mem_filter.mpr ⟨y.property,?_⟩
    rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
    exact (Finset.mem_filter.mp hy).2
  · intro y _ z _ h
    exact Subtype.ext h
  · intro y hy
    obtain ⟨hy,hU⟩ := Finset.mem_filter.mp hy
    refine ⟨⟨y,hy⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    rwa [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem] at hU

theorem source_rich_lines {q : ℕ} [CharP K q] (hq : 2 < q)
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (σ g n' a : ℝ) (hσq : Real.exp σ = q)
    (hσ : 1000 ≤ σ) (hg : 100000000 ≤ g) (hghi : g ≤ 2*σ)
    (hn' : Real.exp (3*σ/2+g)/4 ≤ n') (ha : Real.exp (-g/20) ≤ a)
    (X : Finset (ℙ K (I → K))) (hX : (X.card:ℝ) ≤ Real.exp (3*σ/2+g))
    (F : Finset (Submodule K (I → K))) (hF : ∀ U ∈ F, finrank K U = 2)
    (hrich : ∀ U ∈ F, n'*a/Real.exp σ ≤ (X.filter fun y => y.submodule ≤ U).card)
    (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
      ((X.filter fun y => y.submodule ≤ U).card:ℝ) ≤
        (Real.exp (3*σ/2+g)) ^ (4/3:ℝ) / Real.exp σ * Real.exp (-g/5)) :
    (F.card:ℝ)*(n'*a/Real.exp σ) ≤ 20814*Real.exp (3*σ/2+g) := by
  classical
  obtain ⟨hMlo,hCeq⟩ := RichRegime.source_substitution σ g n' a hn' ha
  let M : ℕ := ⌈n'*a/Real.exp σ⌉₊
  let C : ℕ := ⌊Real.exp (σ+17*g/15)⌋₊
  have hMM : n'*a/Real.exp σ ≤ (M:ℝ) := Nat.le_ceil _
  have hC : (C:ℝ) ≤ Real.exp (σ+17*g/15) := Nat.floor_le (by positivity)
  obtain ⟨hM2,hlarge,hCM,hchar⟩ := RichRegime.sufficiently_large_conditions σ g
    (X.card:ℝ) M C hσ hg hghi hX (hMlo.trans hMM) (hC.trans (by nlinarith [Real.exp_pos (σ+17*g/15)]))
  by_cases hFn : F.Nonempty
  · obtain ⟨U,hU⟩ := hFn
    have hMU : M ≤ (X.filter fun y => y.submodule ≤ U).card := Nat.ceil_le.mpr (hrich U hU)
    have hMN : M ≤ X.card := hMU.trans (Finset.card_filter_le _ _)
    have hXp : (0:ℝ) < X.card := lt_of_lt_of_le (by linarith : (0:ℝ)<M) (by exact_mod_cast hMN)
    have hXn : X.Nonempty := Finset.card_pos.mp (by exact_mod_cast hXp)
    let : Nonempty X := hXn.coe_sort
    have h2 : (2 : AlgebraicClosure K) ≠ 0 := by
      intro he
      have hd := (CharP.cast_eq_zero_iff (AlgebraicClosure K) q 2).mp he
      have hh := Nat.le_of_dvd (by decide : 0<2) hd
      omega
    have hh := quantitative_card_mul_le (L := AlgebraicClosure K) h2 hI
      (fun y : X => y.val) Subtype.val_injective (fun U : F => U.val)
      (fun U => hF U.val U.property) Subtype.val_injective M C
      (by exact_mod_cast hM2) (by simpa only [Fintype.card_coe] using hMN)
      (by
        intro U
        rw [card_indexed]
        exact Nat.ceil_le.mpr (hrich U.val U.property))
      (by
        intro U hU
        rw [card_indexed]
        apply Nat.le_floor
        rw [← hCeq]
        exact hcap U hU)
      (by simpa only [Fintype.card_coe] using hlarge)
      (by simpa only [Fintype.card_coe,hσq] using hchar)
      (by exact_mod_cast hCM)
    have hh' : (F.card:ℝ)*(M:ℝ) ≤ 20814*(X.card:ℝ) := by
      exact_mod_cast (by simpa only [Fintype.card_coe] using hh : F.card * M ≤ 20814 * X.card)
    exact (mul_le_mul_of_nonneg_left hMM (by positivity)).trans
      (hh'.trans (mul_le_mul_of_nonneg_left hX (by norm_num)))
  · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hFn
    rw [hF0,Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity

end SharpRamseyFive.ProjectiveRichLines

end

end OAI
