import OAI.Analysis.TraceCone.StrongDensity
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Completely positive approximation in a weak closure

The norm finite-test completely positive approximation property yields
simultaneous strong-star approximation on finitely many vectors. The factor maps
pass through a finite-dimensional matrix algebra.
-/

noncomputable section

open Filter Topology
open scoped NNReal ENNReal

namespace TraceConeClassification
open scoped CStarAlgebra ComplexOrder
universe u
variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The completely positive approximation property, in norm finite-test form. -/
def NuclearCPAP : Prop :=
  ∀ (s : Finset A) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (α : A →CP CStarMatrix (Fin n) (Fin n) ℂ)
      (β : CStarMatrix (Fin n) (Fin n) ℂ →CP A),
      (∀ a, ‖α a‖ ≤ ‖a‖) ∧ (∀ b, ‖β b‖ ≤ ‖b‖) ∧
      ∀ a ∈ s, ‖β (α a) - a‖ < ε

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Hyperfiniteness witnessed by an increasing sequence of finite-dimensional
star subalgebras with weak-operator dense union. -/
def IsHyperfiniteWOT (N : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ F : ℕ → StarSubalgebra ℂ (H →L[ℂ] H),
    Monotone F ∧ (∀ n, FiniteDimensional ℂ (F n)) ∧
    (∀ n, (F n).toNonUnitalStarSubalgebra ≤ N) ∧
    closure (ContinuousLinearMapWOT.ofCLM '' (⋃ n, (F n : Set (H →L[ℂ] H)))) =
      ContinuousLinearMapWOT.ofCLM '' (N : Set (H →L[ℂ] H))

end TraceConeClassification

namespace TraceConeClassification
open scoped CStarAlgebra ComplexOrder
universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Nuclear CPAP gives simultaneous strong-star approximation on finite sets of operators
and vectors in the weak closure of a representation. -/
theorem NuclearCPAP.weakClosure_cp_approx (hNuc : NuclearCPAP A)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (m k : ℕ)
    (T : Fin m → H →L[ℂ] H)
    (hT : ∀ j, T j ∈ weakClosure (NonUnitalStarAlgHom.range π))
    (ξ : Fin k → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (α : A →CP CStarMatrix (Fin n) (Fin n) ℂ)
      (β : CStarMatrix (Fin n) (Fin n) ℂ →CP A) (a : Fin m → A),
      (∀ x, ‖α x‖ ≤ ‖x‖) ∧ (∀ y, ‖β y‖ ≤ ‖y‖) ∧
      ∀ j i, ‖π (β (α (a j))) (ξ i) - T j (ξ i)‖ < ε ∧
        ‖star (π (β (α (a j)))) (ξ i) - star (T j) (ξ i)‖ < ε := by
  classical
  have happ (j : Fin m) : ∃ a : A, ∀ i,
      ‖π a (ξ i) - T j (ξ i)‖ < ε/2 ∧
      ‖star (π a) (ξ i) - star (T j) (ξ i)‖ < ε/2 := by
    obtain ⟨R,hR,he⟩ := weakClosure_strong_star_density
      (NonUnitalStarAlgHom.range π) (T j) (hT j) k ξ (ε/2) (by positivity)
    obtain ⟨a,rfl⟩ := hR
    exact ⟨a,he⟩
  choose a ha using happ
  let L : ℝ := (∑ i, ‖ξ i‖) + 1
  have hsum : 0 ≤ ∑ i, ‖ξ i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hL : 0 < L := by dsimp [L]; linarith
  have hi (i : Fin k) : ‖ξ i‖ ≤ L := by
    have hh : ‖ξ i‖ ≤ ∑ j, ‖ξ j‖ := Finset.single_le_sum
      (fun j _ => norm_nonneg (ξ j)) (Finset.mem_univ i)
    dsimp [L]
    linarith
  obtain ⟨n,α,β,hα,hβ,he⟩ := hNuc (Finset.univ.image a) (ε/(2*L)) (by positivity)
  have hnorm (j : Fin m) : ‖π (β (α (a j))) - π (a j)‖ < ε/(2*L) := by
    rw [← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le π _).trans_lt
      (he (a j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩))
  have hsmall (R : H →L[ℂ] H) (hR : ‖R‖ < ε/(2*L)) (i : Fin k) :
      ‖R (ξ i)‖ < ε/2 := by
    calc
      ‖R (ξ i)‖ ≤ ‖R‖ * ‖ξ i‖ := R.le_opNorm (ξ i)
      _ ≤ ‖R‖ * L := mul_le_mul_of_nonneg_left (hi i) (norm_nonneg _)
      _ < (ε/(2*L))*L := mul_lt_mul_of_pos_right hR hL
      _ = ε/2 := by field_simp
  refine ⟨n,α,β,a,hα,hβ,fun j i => ?_⟩
  have he₁ := hsmall (π (β (α (a j))) - π (a j)) (hnorm j) i
  have hs : ‖star (π (β (α (a j)))) - star (π (a j))‖ < ε/(2*L) := by
    simpa only [← star_sub,norm_star] using hnorm j
  have he₂ := hsmall (star (π (β (α (a j)))) - star (π (a j))) hs i
  constructor
  · have ht := norm_sub_le_norm_sub_add_norm_sub (π (β (α (a j))) (ξ i)) (π (a j) (ξ i)) (T j (ξ i))
    exact ht.trans_lt (by simpa only [sub_apply, add_halves] using add_lt_add he₁ (ha j i).1)
  · have ht := norm_sub_le_norm_sub_add_norm_sub (star (π (β (α (a j)))) (ξ i)) (star (π (a j)) (ξ i))
      (star (T j) (ξ i))
    exact ht.trans_lt (by simpa only [sub_apply, add_halves] using add_lt_add he₂ (ha j i).2)

end TraceConeClassification

end

end OAI
