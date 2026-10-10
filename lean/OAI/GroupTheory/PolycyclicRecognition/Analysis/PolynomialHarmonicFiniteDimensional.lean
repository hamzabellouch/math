import OAI.GroupTheory.PolycyclicRecognition.Analysis.UniformHarmonicDimensionBound
import Mathlib.LinearAlgebra.Dimension.Free

namespace OAI

/-! # Finite-dimensionality of polynomial-growth harmonic functions

This proves the discrete Cayley-graph form of Kleiner, Theorem 1.4,
using the Poincare, good-scale, spectral and averaging arguments.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

theorem polynomialHarmonicFunctions_finite (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (d b : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hvol : ∀ R, ((wordBall S R).card : ℝ) ≤ D * (1 + (R : ℝ)) ^ b) :
    Module.Finite ℝ (polynomialHarmonicFunctions S d) := by
  classical
  let H := polynomialHarmonicFunctions S d
  let K := harmonicScaleConstant b d
  obtain ⟨w, hw, hwidth⟩ := exists_harmonic_separation_width (32 * (S.card : ℝ) * K ^ 4)
  have hwidth' : 128 * (S.card : ℝ) * harmonicScaleConstant b d ^ 4 < (16 : ℝ) ^ (2 * w) := by
    convert hwidth using 1
    dsimp [K]
    ring
  let N := 2 * Nat.ceil (K ^ w)
  have hfinite (V : Submodule ℝ (G → ℝ)) [Module.Finite ℝ V] (hV : V ≤ H) :
      Module.finrank ℝ V ≤ N := by
    by_cases hz : Module.finrank ℝ V = 0
    · rw [hz]
      exact Nat.zero_le _
    let basis := Module.finBasis ℝ V
    apply uniform_harmonic_subspace_dimension_bound S hS hgen V basis d b
      (by simpa using Nat.pos_of_ne_zero hz)
      (fun i => (hV (basis i).property).1)
      (fun f => (hV f.property).2) D hD hvol w hw hwidth'
  have hind (s : Finset H) (hs : LinearIndependent ℝ (fun i : s => (i : H))) :
      s.card ≤ N := by
    let f : s → G → ℝ := fun i => (i.val : H).val
    have hli : LinearIndependent ℝ f :=
      hs.map' H.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    let V := Submodule.span ℝ (Set.range f)
    let basis : Module.Basis s ℝ V := Module.Basis.span hli
    let : Module.Finite ℝ V := Module.Finite.of_basis basis
    have hV : V ≤ H := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (i.val : H).property
    have hd := hfinite V hV
    simpa only [Module.finrank_eq_card_basis basis, Fintype.card_coe] using hd
  apply Module.rank_lt_aleph0_iff.mp
  exact (rank_le hind).trans_lt Cardinal.natCast_lt_aleph0

theorem polynomialHarmonicFunctions_finite_of_word_growth (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (d C b : ℕ) (hvol : ∀ R, (wordBall S R).card ≤ C * (1 + R) ^ b) :
    Module.Finite ℝ (polynomialHarmonicFunctions S d) := by
  apply polynomialHarmonicFunctions_finite S hS hgen d b (C : ℝ) (Nat.cast_nonneg C)
  intro R
  exact_mod_cast hvol R

end PolycyclicRecognition

end

end OAI
