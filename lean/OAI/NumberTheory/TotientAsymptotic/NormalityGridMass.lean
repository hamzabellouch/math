import OAI.NumberTheory.TotientAsymptotic.NormalityGridCell

namespace OAI

/-! Finite union of the normality grid cells. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace TotientAsymptotic

def normalityGridIndices (M : ℕ) : Finset (ℕ×ℕ) :=
  (Finset.range (M+1)).product (Finset.range (M+1))

lemma normality_grid_constant_sum (M : ℕ) (W : ℝ) :
    (∑ _ij ∈ normalityGridIndices M,W) = (((M+1:ℕ):ℝ))^2*W := by
  have hc : (normalityGridIndices M).card = (M+1)*(M+1) := by
    exact (Finset.card_product (Finset.range (M+1)) (Finset.range (M+1))).trans
      (by rw [Finset.card_range])
  rw [Finset.sum_const,hc]
  simp only [nsmul_eq_mul,Nat.cast_mul,pow_two]

lemma normality_grid_cover (A : ℝ) (M : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,∃ i j : ℕ,1 ≤ i ∧ i < j ∧ j ≤ M ∧ A ≤ (j:ℝ)-1 ∧
      Real.sqrt (A*((j:ℝ)-1))-4 ≤
      |(omegaIn n (normalityGridPoint i) (normalityGridPoint j):ℝ)-((j:ℝ)-i)|) :
    Q ⊆ (normalityGridIndices M).biUnion (normalityGridCell A M Q) := by
  classical
  intro n hn
  obtain ⟨i,j,hi,hij,hj,hD,hh⟩ := hQ n hn
  apply Finset.mem_biUnion.mpr
  refine ⟨(i,j),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
    Finset.mem_range.mpr (by omega)⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨hn,hi,hij,hj,hD,hh⟩

lemma reciprocal_sum_biUnion_le {α : Type*} (I : Finset α) (S : α → Finset ℕ) :
    (∑ n ∈ I.biUnion S,(n:ℝ)⁻¹) ≤ ∑ i ∈ I,∑ n ∈ S i,(n:ℝ)⁻¹ := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ha]
    have he := Finset.sum_union_inter (s₁:=S a) (s₂:=I.biUnion S) (f:=fun n : ℕ => (n:ℝ)⁻¹)
    have hn : 0 ≤ ∑ n ∈ S a ∩ I.biUnion S,(n:ℝ)⁻¹ :=
      Finset.sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
    linarith

lemma normality_grid_sum_bound (A : ℝ) (M : ℕ) (Q : Finset ℕ) (W : ℝ)
    (hcover : Q ⊆ (normalityGridIndices M).biUnion (normalityGridCell A M Q))
    (hF : ∀ ij, (∑ n ∈ normalityGridCell A M Q ij,(n:ℝ)⁻¹) ≤ W) :
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ (((M+1:ℕ):ℝ))^2*W := by
  classical
  calc
    _ ≤ ∑ n ∈ (normalityGridIndices M).biUnion (normalityGridCell A M Q),(n:ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => by positivity)
    _ ≤ ∑ ij ∈ normalityGridIndices M,∑ n ∈ normalityGridCell A M Q ij,(n:ℝ)⁻¹ :=
      reciprocal_sum_biUnion_le (normalityGridIndices M) (normalityGridCell A M Q)
    _ ≤ ∑ _ij ∈ normalityGridIndices M,W := Finset.sum_le_sum (fun ij _ => hF ij)
    _ = _ := normality_grid_constant_sum M W

theorem normality_grid_mass : ∃ C : ℝ, 0<C ∧ ∀ N M : ℕ,
    2 ≤ N → normalityGridPoint M ≤ N → ∀ A : ℝ, 0<A → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0<n ∧ n ≤ N ∧ ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ M ∧ A ≤ (j:ℝ)-1 ∧
      Real.sqrt (A*((j:ℝ)-1))-4 ≤
        |(omegaIn n (normalityGridPoint i) (normalityGridPoint j):ℝ)-((j:ℝ)-i)|) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*(((M+1:ℕ):ℝ))^2*Real.log N*Real.exp (-A/6) := by
  classical
  obtain ⟨C,hC,hbound⟩ := normality_grid_cell_mass
  refine ⟨C,hC,?_⟩
  intro N M hN hMN A hA Q hQ
  have hcover := normality_grid_cover A M Q (fun n hn => (hQ n hn).2.2)
  have hF := hbound N M hN hMN A hA Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hh := normality_grid_sum_bound A M Q (C*Real.log N*Real.exp (-A/6)) hcover hF
  calc
    _ ≤ (((M+1:ℕ):ℝ))^2*(C*Real.log N*Real.exp (-A/6)) := hh
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
