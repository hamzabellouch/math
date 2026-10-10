import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicCoverEnergy
import Mathlib.LinearAlgebra.Dimension.Finite

namespace OAI

/-! # Injectivity and dimension bound from harmonic averaging

On a subspace where the large-ball quadratic form has controlled growth,
the zero-average energy estimate gives injectivity of the actual averaging
map. No dimension bound or harmonic-function finiteness is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

def wordBallAverageMap (S C : Finset G) (t : ℕ) (V : Submodule ℝ (G → ℝ)) :
    V →ₗ[ℝ] (C → ℝ) where
  toFun f y := ∑ x ∈ translatedWordBall S t y.val, f.val x
  map_add' f g := by ext y; exact sum_add_distrib
  map_smul' c f := by ext y; exact (mul_sum ..).symm

theorem wordBallAverageMap_injective (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (C : Finset G) (r R t : ℕ) (hRt : 0 < R + 3 * t)
    (hdis : (C : Set G).Pairwise (fun x y =>
      Disjoint (translatedWordBall S r x) (translatedWordBall S r y)))
    (hC : C ⊆ wordBall S R)
    (hcover : ∀ x ∈ wordBall S R, ∃ y ∈ C, x ∈ translatedWordBall S t y)
    (V : Submodule ℝ (G → ℝ)) (hharm : ∀ f : V, CayleyHarmonic S f.val)
    (hpos : (wordBallQuadraticForm S R V).PosDef)
    (K : ℝ) (hgrowth : ∀ f : V, wordBallQuadraticValue S (2 * (R + 3 * t)) f.val ≤
      K * wordBallQuadraticValue S R f.val)
    (hsmall : harmonicCoverFactor S r R t * K < 1) :
    Function.Injective (wordBallAverageMap S C t V) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  by_contra hn
  have hp : 0 < wordBallQuadraticValue S R f.val := by
    simpa only [wordBallQuadraticForm_apply] using hpos f hn
  have hz : ∀ y ∈ C, ∑ x ∈ translatedWordBall S t y, f.val x = 0 := by
    intro y hy
    exact congr_fun hf ⟨y, hy⟩
  have he := harmonic_wordBall_zero_averages S hS hgen C r R t hRt hdis hC hcover
    f.val (hharm f) hz
  have hb := he.trans (mul_le_mul_of_nonneg_left (hgrowth f)
    (harmonicCoverFactor_nonneg S r R t))
  have hc := mul_lt_mul_of_pos_right hsmall hp
  rw [mul_assoc, one_mul] at hc
  exact (not_lt_of_ge hb) hc

theorem harmonic_subspace_dimension_le_cover (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (C : Finset G) (r R t : ℕ) (hRt : 0 < R + 3 * t)
    (hdis : (C : Set G).Pairwise (fun x y =>
      Disjoint (translatedWordBall S r x) (translatedWordBall S r y)))
    (hC : C ⊆ wordBall S R)
    (hcover : ∀ x ∈ wordBall S R, ∃ y ∈ C, x ∈ translatedWordBall S t y)
    (V : Submodule ℝ (G → ℝ)) (hharm : ∀ f : V, CayleyHarmonic S f.val)
    (hpos : (wordBallQuadraticForm S R V).PosDef)
    (K : ℝ) (hgrowth : ∀ f : V, wordBallQuadraticValue S (2 * (R + 3 * t)) f.val ≤
      K * wordBallQuadraticValue S R f.val)
    (hsmall : harmonicCoverFactor S r R t * K < 1) :
    Module.Finite ℝ V ∧ Module.finrank ℝ V ≤ C.card := by
  have hi := wordBallAverageMap_injective S hS hgen C r R t hRt hdis hC hcover
    V hharm hpos K hgrowth hsmall
  refine ⟨Module.Finite.of_injective (wordBallAverageMap S C t V) hi, ?_⟩
  simpa using LinearMap.finrank_le_finrank_of_injective hi

end PolycyclicRecognition

end

end OAI
