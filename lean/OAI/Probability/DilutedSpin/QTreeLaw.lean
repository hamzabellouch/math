import OAI.Probability.DilutedSpin.PhysicalOverlapLimit

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance qTreeLawDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
 
noncomputable def qExpect {n : ℕ} (m : Fin (n+1) → ℝ)
    (F : PrescribedTree n → ℝ) : ℕ → PrescribedTree n → ℝ
  | 0, S => F S
  | k+1, S => ∑ v : Internal S, (-gamma S m v / leaves S) * qExpect m F k (grow S v)

theorem qExpect_const {n : ℕ} (m : Fin (n+1) → ℝ)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1) (c : ℝ)
    (k : ℕ) (S : PrescribedTree n) : qExpect m (fun _ => c) k S = c := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [qExpect, ih]
    rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_neg_distrib, sum_gamma, hroot, hend]
    have hn : (leaves S:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (leaves_pos S))
    simp [hn]

theorem qExpect_mono {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) {F G : PrescribedTree n → ℝ}
    (hFG : ∀ S, F S ≤ G S) (k : ℕ) (S : PrescribedTree n) :
    qExpect m F k S ≤ qExpect m G k S := by
  induction k generalizing S with
  | zero => exact hFG S
  | succ k ih =>
    exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (ih (grow S v))
      (div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg _)))

theorem abs_qExpect_le {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    {F : PrescribedTree n → ℝ} {C : ℝ} (hF : ∀ S, |F S| ≤ C)
    (k : ℕ) (S : PrescribedTree n) : |qExpect m F k S| ≤ C := by
  apply abs_le.mpr
  constructor
  · simpa only [qExpect_const m hroot hend] using
      qExpect_mono m hm hpos (fun S => (abs_le.mp (hF S)).1) k S
  · simpa only [qExpect_const m hroot hend] using
      qExpect_mono m hm hpos (fun S => (abs_le.mp (hF S)).2) k S

lemma qExpect_nonneg {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (F : PrescribedTree n → ℝ)
    (hF : ∀ S, 0≤F S) (k : ℕ) (S : PrescribedTree n) : 0≤qExpect m F k S := by
  induction k generalizing S with
  | zero => exact hF S
  | succ k ih => exact Finset.sum_nonneg (fun v _ => mul_nonneg
      (div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg _)) (ih _))

lemma qExpect_sum {n : ℕ} (m : Fin (n+1) → ℝ) {ι : Type} (s : Finset ι)
    (F : ι → PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => ∑ i∈s, F i T) k S=∑ i∈s, qExpect m (F i) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,Finset.mul_sum]; exact Finset.sum_comm

lemma qExpect_mul_const {n : ℕ} (m : Fin (n+1) → ℝ)
    (F : PrescribedTree n → ℝ) (c : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T*c) k S=qExpect m F k S*c := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,Finset.sum_mul,mul_assoc]

/-- Only the genuine reachable terminal leaf number is required. -/
lemma qExpect_mono_leaves {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (F G : PrescribedTree n → ℝ)
    (k : ℕ) (S : PrescribedTree n)
    (hFG : ∀ T, T.leaves=S.leaves+k → F T≤G T) :
    qExpect m F k S≤qExpect m G k S := by
  induction k generalizing S with
  | zero => exact hFG S (by omega)
  | succ k ih =>
    apply Finset.sum_le_sum
    intro v _
    apply mul_le_mul_of_nonneg_left
    · apply ih
      intro T hT
      apply hFG
      rw [leaves_grow] at hT
      omega
    · exact div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg _)

lemma qExpect_grid_le_historyMass {L : ℕ} (hL : 0<L) (F : PrescribedTree L → ℝ)
    (hF : ∀ T, 0≤F T) (k : ℕ) (S : PrescribedTree L) :
    qExpect (grid L 0 L) F k S≤historyMass F k S 0 := by
  have hm : Monotone (grid L 0 L) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast (show 0+i.val≤0+j.val from Nat.add_le_add_left hij 0))
      (le_of_lt (Nat.cast_pos.mpr hL))
  have hp : ∀ j, 0≤grid L 0 L j := fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [qExpect,historyMass,CharP.cast_eq_zero,zero_mul,zero_add]
    apply Finset.sum_le_sum
    intro v _
    have hg : |gamma S (grid L 0 L) v| = -gamma S (grid L 0 L) v :=
      abs_of_nonpos (gamma_nonpos S _ hm hp v)
    rw [hg]
    have hcoef : -gamma S (grid L 0 L) v / S.leaves≤ -gamma S (grid L 0 L) v := by
      apply div_le_self (neg_nonneg.mpr (gamma_nonpos S _ hm hp v))
      exact_mod_cast leaves_pos S
    apply mul_le_mul hcoef (ih _) (qExpect_nonneg _ hm hp F hF k _) (neg_nonneg.mpr (gamma_nonpos S _ hm hp v))

lemma qExpect_grid_branching {L : ℕ} (hL : 0<L) (Q : Finset ℕ) (k b : ℕ)
    (S : PrescribedTree L) :
    qExpect (grid L 0 L) (fun T => if branchingCount S (·∈Q)+b≤branchingCount T (·∈Q)
      then 1 else 0) k S≤
    chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k b * (L:ℝ)⁻¹^b := by
  exact (qExpect_grid_le_historyMass hL _ (fun _ => by split_ifs <;> norm_num) k S).trans
    (charging_final_shape hL Q k b 0 S (Nat.zero_le _))

end DilutedSpinGlass.PrescribedTree

end

end OAI
