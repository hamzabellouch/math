import Mathlib
import OAI.Analysis.Commutator.MatrixGNS

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

omit [Nonempty I] in
lemma centeredStageVector_sub_trace (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (a : Matrix I I ℂ) :
    centeredStageVector τ φ (a - ((Fintype.card I : ℂ)⁻¹ * a.trace) • 1) =
      centeredStageVector τ φ a := by
  rw [map_sub, map_smul]
  have hz : centeredStageVector τ φ 1 = 0 := by
    change center (vacuum τ) (stageVector τ φ 1) = 0
    rw [stage_vacuum, center_vacuum]
  rw [hz, smul_zero, sub_zero]

lemma trace_sub_normalized_trace (a : Matrix I I ℂ) :
    (a - ((Fintype.card I : ℂ)⁻¹ * a.trace) • 1).trace = 0 := by
  have hn : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  field_simp
  simp

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
  [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

def stageSet (n : ℕ) : Set τ.GNS := Set.range (stageVector τ (φ n))

def centeredStageSet (n : ℕ) : Set (centeredSpace (vacuum τ)) :=
  {x | ∃ a : Matrix (I n) (I n) ℂ, a.trace = 0 ∧ centeredStageVector τ (φ n) a = x}

lemma centeredStageSet_eq (n : ℕ) :
    centeredStageSet τ I φ n = (center (vacuum τ)) '' stageSet τ I φ n := by
  ext x
  constructor
  · rintro ⟨a, _, rfl⟩
    exact ⟨stageVector τ (φ n) a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a - ((Fintype.card (I n) : ℂ)⁻¹ * a.trace) • 1,
      trace_sub_normalized_trace a, centeredStageVector_sub_trace τ (φ n) a⟩

lemma dense_centeredStageSet (hd : Dense (⋃ n, stageSet τ I φ n)) :
    Dense (⋃ n, centeredStageSet τ I φ n) := by
  have hs : Function.Surjective (center (vacuum τ)) :=
    fun x => ⟨x, center_centered (vacuum τ) x⟩
  have hi : (⋃ n, centeredStageSet τ I φ n) =
      (center (vacuum τ)) '' (⋃ n, stageSet τ I φ n) := by
    simp only [centeredStageSet_eq, Set.image_iUnion]
  rw [hi]
  exact hs.denseRange.dense_image (center (vacuum τ)).continuous hd

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)

omit [∀ n, Nonempty (I n)] in
include e he in
lemma stageSet_mono : Monotone (stageSet τ I φ) := by
  intro n m hnm x hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨e hnm a, ?_⟩
  change algebraVector τ (φ m (e hnm a)) = algebraVector τ (φ n a)
  rw [he]

include e he in
lemma centeredStageSet_mono : Monotone (centeredStageSet τ I φ) := by
  intro n m hnm
  rw [centeredStageSet_eq, centeredStageSet_eq]
  exact Set.image_mono (stageSet_mono τ I φ e he hnm)

end Kadison.TracialGNS
end

end OAI
