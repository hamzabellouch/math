import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEmbeddings

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
section OrderedBirthCounts
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {N : ℕ} (J : SimpleGraph (Fin N)) (G : SimpleGraph V)
variable [DecidableRel J.Adj] [DecidableRel G.Adj]

theorem prefixEmbeddings_after_roots (R k : ℕ) (hR : R ≤ k) (hk : k ≤ N)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ x y : V, x ≠ y →
      ((Finset.univ.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) ≤ D)
    (hborn : ∀ i, R ≤ i → (hi : i+1 ≤ N) → ∃ u v : Fin i,
      u ≠ v ∧ J.Adj (Fin.castLE (by omega) u) ⟨i,by omega⟩ ∧
        J.Adj (Fin.castLE (by omega) v) ⟨i,by omega⟩) :
    ((prefixEmbeddings J G k hk).card : ℝ) ≤
      ((prefixEmbeddings J G R (hR.trans hk)).card : ℝ) * D ^ (k-R) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hR
  induction d with
  | zero => simp
  | succ d ih =>
    have hrec := prefixEmbeddings_succ_bound (J := J) (G := G) hk D (by
      intro ψ _
      obtain ⟨u,v,huv,hu,hv⟩ := hborn (R+d) (by omega) hk
      exact compatibleNext_le_codegree hk ψ u v huv hu hv D hD)
    have hm := mul_le_mul_of_nonneg_left (ih (by omega) (by omega) hborn) hD0
    calc
      _ ≤ D * (prefixEmbeddings J G (R+d) (by omega)).card := hrec
      _ ≤ D * ((prefixEmbeddings J G R (by omega)).card * D ^ (R+d-R)) := hm
      _ = _ := by simp only [Nat.add_sub_cancel_left]; ring

theorem prefixEmbeddings_matching_roots (r : ℕ) (hr : 2*r ≤ N)
    (Δ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ Δ)
    (hroot : ∀ i (hi : i < r), J.Adj ⟨2*i,by omega⟩ ⟨2*i+1,by omega⟩) :
    ((prefixEmbeddings J G (2*r) hr).card : ℝ) ≤ ((Fintype.card V : ℝ) * Δ) ^ r := by
  induction r with
  | zero => simp only [Nat.mul_zero,prefixEmbeddings_zero,Nat.cast_one,pow_zero,le_refl]
  | succ r ih =>
    have hr0 : 2*r ≤ N := by omega
    have hr1 : 2*r+1 ≤ N := by omega
    have hr2 : 2*r+1+1 ≤ N := by omega
    have hone := prefixEmbeddings_succ_bound (J := J) (G := G) hr1
      (Fintype.card V : ℝ) (by
        intro ψ _
        exact_mod_cast compatibleNext_le_order (J := J) hr1 ψ)
    have htwo := prefixEmbeddings_succ_bound (J := J) (G := G) hr2 Δ (by
      intro ψ _
      exact compatibleNext_le_degree hr2 ψ ⟨2*r,by omega⟩ (hroot r (by omega)) Δ hΔ)
    have hi := ih hr0 (fun i hi => hroot i (by omega))
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (Fintype.card V))) hΔ0
    calc
      _ = ((prefixEmbeddings J G (2*r+1+1) hr2).card : ℝ) := by congr 3
      _ ≤ Δ * (prefixEmbeddings J G (2*r+1) hr1).card := htwo
      _ ≤ Δ * ((Fintype.card V : ℝ) * (prefixEmbeddings J G (2*r) hr0).card) :=
        mul_le_mul_of_nonneg_left hone hΔ0
      _ ≤ Δ * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * Δ)^r) := hmul
      _ = _ := by rw [pow_succ]; ring

end OrderedBirthCounts
end SharpTerminalLeave

end

end OAI
