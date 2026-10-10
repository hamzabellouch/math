import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.GridCollar
import OAI.MathematicalPhysics.PEPSFilters.CollarWeights

namespace OAI

/-! Uniform geometric filter optimizers with energy, fidelity and entropy bounds. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Topology

open scoped BigOperators Matrix.Norms.L2Operator
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

theorem geometric_optimizer_producer (q : ℕ) (hq : 2 ≤ q)
    (J Δ ε : ℝ) (hJ : 0 < J) (hΔ : 0 < Δ) (hε : 0 < ε) :
    ∃ (M : ℕ) (η : ℝ), 0 < M ∧ 0 < η ∧ η ≤ 1 ∧
      ∀ (L : ℕ), 2 ≤ L → ∀ (r x y w h : ℕ), 0 < r → w+1 ≤ r → h+1 ≤ r →
      ∀ (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
        (Ω : State L q) (E : ℝ),
        IsGridHamiltonian J hv he → UniqueGround (Hamiltonian hv he) Ω E →
        FullSystemGap (Hamiltonian hv he) Ω E Δ →
      ∃ m : ℕ, m+1 ≤ M*r ∧
        let S := enlargedRectangle L x y w h 0
        let X : Fin (m+1) → Finset (Vertex L) := fun j => enlargedRectangle L x y w h (j.val+1)
        let a : Fin (m+1) → ℝ := fun j => collarWeight η (r+1) j.val
        (4:ℝ) ≤ ∑ j, a j ∧ (∑ j, a j) ≤ 5 ∧
        (∀ j, 0 < a j ∧ a j ≤ 1) ∧
        (∀ j, S ⊆ X j ∧ X j ⊆ enlargedRectangle L x y w h (M*r)) ∧
        ∃ F : FilterFamily q (m+1) X,
          IsMaximizer Ω a F ∧ 0 < ‖output F Ω‖ ∧ ‖normalizedOutput F Ω‖ = 1 ∧
          |expectation (normalizedOutput F Ω) (Hamiltonian hv he) - E| ≤ ε*Δ ∧
          1 - ‖inner ℂ Ω (normalizedOutput F Ω)‖^2 ≤ ε ∧
          UpperComparison S Ω a F 0 r := by
  classical
  have hq0 : 0 < q := by omega
  let : NeZero q := ⟨by omega⟩
  have hq' : (0:ℝ) < q := by exact_mod_cast hq0
  let η : ℝ := min 1 (ε*Δ/(40*(q:ℝ)^2*J))
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hbudget : 40*(q:ℝ)^2*J*η ≤ ε*Δ := by
    have hp : (0:ℝ) < 40*(q:ℝ)^2*J := by positivity
    have hh := (le_div_iff₀ hp).mp (min_le_right (1:ℝ) (ε*Δ/(40*(q:ℝ)^2*J)))
    dsimp only [η]
    nlinarith
  obtain ⟨M,hM,hweights⟩ := exists_uniform_collar_weights hη hη1
  refine ⟨2*M,η,by omega,hη,hη1,?_⟩
  intro L hL r x y w h hr hw hh hv he Ω E hH hg hgap
  obtain ⟨n,hn,hnb,hnl,hnu,hna,hncost⟩ := hweights (r+1) (by omega)
  cases n with
  | zero => omega
  | succ m =>
    have hmr : m+1 ≤ (2*M)*r := by nlinarith
    let S := enlargedRectangle L x y w h 0
    let X : Fin (m+1) → Finset (Vertex L) := fun j => enlargedRectangle L x y w h (j.val+1)
    let a : Fin (m+1) → ℝ := fun j => collarWeight η (r+1) j.val
    have hX : Monotone X := by
      intro j k hjk
      apply enlargedRectangle_monotone
      exact Nat.add_le_add_right hjk 1
    have hsep : ∀ e : Edge L, ∀ j k, Crosses (X j) e → Crosses (X k) e → j = k := by
      intro e j k hj hk
      apply Fin.ext
      have hz := crossing_enlargedRectangle_unique e hj hk
      omega
    have hST (j) : S ⊆ X j := enlargedRectangle_monotone L x y w h (Nat.zero_le _)
    have hbound (j : Fin (m+1)) : X j ⊆ enlargedRectangle L x y w h ((2*M)*r) := by
      apply enlargedRectangle_monotone
      have hj := j.isLt
      omega
    have ha : ∀ j, 0 < a j := fun j => (hna j).1
    have ha1 : ∀ j, a j ≤ 1 := fun j => (hna j).2
    have hsum : (∑ j, a j) = collarWeightSum η (r+1) (m+1) :=
      Fin.sum_univ_eq_sum_range (collarWeight η (r+1)) (m+1)
    have hcost : (q:ℝ)^2 * J * ∑ j, (crossingCount (X j):ℝ) * (a j)^2 ≤ ε*Δ := by
      have hc : (∑ j, (crossingCount (X j):ℝ) * (a j)^2) ≤ 40*η := by
        calc
          _ ≤ ∑ j : Fin (m+1), 8 * (((r+1+j.val:ℕ):ℝ)) * (a j)^2 := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            have hb := crossingCount_enlargedRectangle_scale L x y w h (j.val+1) r hw hh
            exact_mod_cast (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)
          _ = 8 * ∑ j : Fin (m+1), (((r+1+j.val:ℕ):ℝ)) * (a j)^2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _; ring
          _ ≤ 8*(5*η) := mul_le_mul_of_nonneg_left hncost (by norm_num)
          _ = 40*η := by ring
      have hp := mul_le_mul_of_nonneg_left hc (show 0 ≤ (q:ℝ)^2*J by positivity)
      have heq : (q:ℝ)^2*J*(40*η) = 40*(q:ℝ)^2*J*η := by ring
      rw [heq] at hp
      exact hp.trans hbudget
    obtain ⟨F,hF,hFpos,hE,hfid⟩ := exists_maximizer_energy X hX hsep a ha ha1 hv he J hH Ω E Δ hg hgap
    refine ⟨m,hmr,?_,?_,hna,fun j => ⟨hST j,hbound j⟩,F,hF,hFpos,?_,hE.trans hcost,?_,?_⟩
    · rw [hsum]; exact hnl
    · rw [hsum]; exact hnu
    · exact norm_normalized _ (norm_pos_iff.mp hFpos)
    · have hz := hfid.trans hcost
      nlinarith
    · exact upperComparison_zero hST hX hg.1 ha hF r

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
