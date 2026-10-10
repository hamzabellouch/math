import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Crossing

namespace OAI

/-! Neutral local terms, ground energy and the full-system gap. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.OptimizerNeutral
open scoped BigOperators
open PolynomialPEPS.Subvolume.TraceStripping PolynomialPEPS.Subvolume.CrossingIdentity
variable {L q : ℕ}

lemma inserted_eq_right (A : ℕ → Operator L q) (H : Operator L q)
    (r n : ℕ) (hr : r≤n) (hc : ∀ j, j<r → Commute H (A j)) :
    insertedProduct A H r n = orderedPrefix A n * H := by
  have hcomm := commute_prefix A H r hc
  unfold insertedProduct
  rw [mul_assoc,hcomm.eq,← mul_assoc,← orderedPrefix_split]
  rw [Nat.add_sub_of_le hr]

theorem neutral_identity (hq : 0<q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X) (a : ℕ → ℝ)
    (ψ : State L q) (n : ℕ) (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (r : ℕ) (hr : r≤n) (H : Operator L q)
    (hH : ∀ j, r≤j → j<n → SupportedOn H (X j))
    (hc : ∀ j, j<r → Commute H (liftLocal (X j) (F j).matrix)) :
    let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
    let v := asMap (L := L) (q := q) P ψ
    inner ℂ v (asMap H v) = inner ℂ v (asMap (P*H) ψ) := by
  have ht := optimizer_strip_outer hq X hX a ψ n F hF r hr H hH
  dsimp only at ht ⊢
  rw [inserted_eq_right _ H r n hr hc] at ht
  exact ht

theorem excitation_of_transition_errors {ι : Type*} [Fintype ι]
    (h : ι → Operator L q) (Ω : State L q) (E₀ : ℝ)
    (hg : asMap (∑ i, h i) Ω = (E₀:ℂ) • Ω)
    (P : Operator L q) (ε : ι → ℝ)
    (he : ∀ i, |(inner ℂ (asMap P Ω) (asMap (h i) (asMap P Ω))).re -
      (inner ℂ (asMap P Ω) (asMap (P*h i) Ω)).re| ≤ ε i) :
    (inner ℂ (asMap P Ω) (asMap (∑ i, h i) (asMap P Ω))).re -
      E₀*‖asMap P Ω‖^2 ≤ ∑ i, ε i := by
  let v := asMap (L := L) (q := q) P Ω
  have hg' : asMap (P*(∑ i, h i)) Ω = (E₀:ℂ) • v := by
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (P*(∑ i, h i)) Ω = _
    rw [map_mul]
    change asMap P (asMap (∑ i, h i) Ω) = _
    rw [hg,map_smul]
  have htrans : (inner ℂ v (asMap (P*(∑ i, h i)) Ω)).re = E₀*‖v‖^2 := by
    rw [hg',inner_smul_right,inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  change (inner ℂ v (asMap (∑ i, h i) v)).re-E₀*‖v‖^2 ≤ _
  rw [← htrans,Matrix.mul_sum]
  simp only [asMap,map_sum,_root_.sum_apply,inner_sum,Complex.re_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  exact (le_abs_self _).trans (he i)

theorem gap_fidelity (H : Operator L q) (Ω v : State L q) (E₀ Δ ε : ℝ)
    (hg : FullSystemGap H Ω E₀ Δ) (hΔ : 0<Δ)
    (he : (inner ℂ v (asMap H v)).re-E₀*‖v‖^2 ≤ ε*‖v‖^2) :
    (1-ε/Δ)*‖v‖^2 ≤ ‖inner ℂ Ω v‖^2 := by
  have h := (hg v).trans he
  apply (le_of_mul_le_mul_left (a := Δ))
  · calc
      Δ*((1-ε/Δ)*‖v‖^2) = (Δ-ε)*‖v‖^2 := by field_simp
      _ ≤ Δ*‖inner ℂ Ω v‖^2 := by nlinarith
  · exact hΔ

end PolynomialPEPS.Subvolume.OptimizerNeutral

end

end OAI
