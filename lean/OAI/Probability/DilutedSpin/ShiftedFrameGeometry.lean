import OAI.Probability.DilutedSpin.DoubledStemProjection
import OAI.Probability.DilutedSpin.RootMatrixTriple

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance shiftedFrameGeometryPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {n : ℕ}

lemma branchingCount_stem (S : PrescribedTree n) (r : ℕ) (P : ℕ → Prop) :
    branchingCount (stem S r) P=branchingCount S (fun u => P (u+r)) := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
    change branchingCount (unary (stem S r)) P=_
    rw [branchingCount_unary,ih]
    simp only [Nat.add_assoc]

/-- Charged depths after retaining the genuine shared prefix above d. -/
noncomputable def shiftedPrefixDepths (S : PrescribedTree n) (d : ℕ) : Finset ℕ :=
  (shiftedTwinDepths S).image (fun u => u+d)

lemma mem_shiftedPrefixDepths (S : PrescribedTree n) (d u : ℕ) :
    u+d ∈ shiftedPrefixDepths S d ↔ u ∈ shiftedTwinDepths S := by
  classical
  simp [shiftedPrefixDepths]

/-- No old branch can pay a charged target factor, even below a retained
shared prefix. Equal-depth occurrences in the twins remain separate. -/
theorem shifted_prefix_old_count (S : PrescribedTree n) (d : ℕ)
    (hS : NoAdjacentBranchDepths S) :
    branchingCount (stem (doubled (bottomUnary S)) d) (· ∈ shiftedPrefixDepths S d)=0 := by
  rw [branchingCount_stem]
  simpa only [mem_shiftedPrefixDepths] using shifted_twin_old_count S hS

theorem shifted_prefix_target_count (S : PrescribedTree n) (d : ℕ) :
    branchingCount (stem (doubled (unary S)) d) (· ∈ shiftedPrefixDepths S d)=
      2*branchingCount S (fun _ => True) := by
  rw [branchingCount_stem]
  simpa only [mem_shiftedPrefixDepths] using shifted_twin_target_count S

theorem shifted_prefix_total_count (S : PrescribedTree n) (d : ℕ) :
    branchingCount (stem (doubled (unary S)) d) (fun _ => True)=
      branchingCount (stem (doubled (unary S)) d) (· ∈ shiftedPrefixDepths S d)+1 := by
  rw [branchingCount_stem,branchingCount_stem]
  simpa only [mem_shiftedPrefixDepths] using shifted_twin_total_count S

lemma branchRegular_unary {n : ℕ} (S : PrescribedTree n) (m : Fin (n+2) → ℝ) (η : ℝ) :
    BranchRegular (unary S) m η ↔ BranchRegular S (fun j => m j.succ) η := by
  simp only [unary,BranchRegular]
  simp

lemma branchRegular_grid_stem (S : PrescribedTree n) (r d L : ℕ) (η : ℝ) :
    BranchRegular (stem S r) (grid (n+r) d L) η ↔
      BranchRegular S (grid n (d+r) L) η := by
  induction r generalizing d with
  | zero => simp only [Nat.add_zero]; rfl
  | succ r ih =>
    change BranchRegular (unary (stem S r)) (grid (n+r+1) d L) η ↔ _
    rw [branchRegular_unary]
    have he : (fun j : Fin (n+r+1) => grid (n+r+1) d L j.succ)=grid (n+r) (d+1) L := by
      funext j
      simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
    rw [he,ih]
    rw [show d+1+r=d+(r+1) by omega]

/-- All higher-degree factors below a regularly interior evaluation depth
are uniformly positive; no regularity of a union of shapes is needed. -/
lemma branchRegular_grid_of_lower (S : PrescribedTree n) (d L : ℕ) (η : ℝ)
    (h : η≤(d:ℝ)/(L:ℝ)) : BranchRegular S (grid n d L) η := by
  induction S generalizing d with
  | leaf => trivial
  | @node n k C ih =>
    have h' : η≤((d+1:ℕ):ℝ)/(L:ℝ) := h.trans (by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
      exact_mod_cast Nat.le_succ d)
    constructor
    · intro _
      simpa [grid] using h'
    · intro i
      have he : (fun j : Fin (n+1) => grid (n+1) d L j.succ)=grid n (d+1) L := by
        funext j
        simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
      rw [he]
      exact ih i (d+1) h'

lemma branchRegular_shifted_frame (S : PrescribedTree n) (r d L : ℕ) (η : ℝ)
    (he : η≤((d+r+2:ℕ):ℝ)/(L:ℝ)) :
    BranchRegular (stem (doubled (unary (stem S r))) d)
      (grid (n+r+1+1+d) 0 L) η := by
  rw [branchRegular_grid_stem]
  simp only [Nat.zero_add,doubled,BranchRegular]
  refine ⟨by norm_num,?_⟩
  intro i
  have hgrid : (fun j : Fin (n+r+1+1) => grid (n+r+1+1) d L j.succ)=grid (n+r+1) (d+1) L := by
    funext j
    simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
  rw [hgrid,branchRegular_unary]
  have hgrid' : (fun j : Fin (n+r+1) => grid (n+r+1) (d+1) L j.succ)=grid (n+r) (d+2) L := by
    funext j
    simp [grid,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
  rw [hgrid',branchRegular_grid_stem]
  apply branchRegular_grid_of_lower
  simpa only [show d+2+r=d+r+2 by omega] using he

/-- Exact cancellation of all powers of the grid mesh in the absolute
extension cost, with arbitrary shared prefixes and aligned twin depths. -/
theorem shifted_prefix_relative_charge (S : PrescribedTree n) (d k : ℕ)
    (a b : (stem (doubled (unary S)) d).Leaf) (hab : a≠b)
    (η : ℝ) (hη : 0<η)
    (hr : BranchRegular (stem (doubled (unary S)) d) (grid (n+1+1+d) 0 (n+1+1+d)) η) :
    shiftedCharge (shiftedPrefixDepths S d) (stem (doubled (unary S)) d)
        (stem (doubled (bottomUnary S)) d) k /
      |partialKappa (stem (doubled (unary S)) d) (grid (n+1+1+d) 0 (n+1+1+d)) Finset.univ /
        partialKappa (stem (doubled (unary S)) d) (grid (n+1+1+d) 0 (n+1+1+d)) {b,a}| ≤
      chargeBound (2*(leaves (stem (doubled (bottomUnary S)) d)+k:ℕ))
        (((shiftedPrefixDepths S d).card:ℝ)*(leaves (stem (doubled (bottomUnary S)) d)+k:ℕ)) k
        (2*branchingCount S (fun _ => True)) /
          η^(branchExcess (stem (doubled (unary S)) d)) := by
  have hh := shiftedCharge_relative_bound (by omega : 0<n+1+1+d) (shiftedPrefixDepths S d)
    (stem (doubled (unary S)) d) (stem (doubled (bottomUnary S)) d) k a b hab η hη hr
    (shifted_prefix_total_count S d)
  simpa only [shifted_prefix_target_count] using hh

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
