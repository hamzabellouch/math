import OAI.Analysis.Cotype.UniformL1
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def BConvex (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin n → X,
    (∀ i, ‖x i‖ ≤ 1) → ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ) - δ

theorem exists_common_sign_norming {n : ℕ} (x : Fin n → X)
    (hx : ∀ i, ‖x i‖ ≤ 1) (ε : Cube n) {δ : ℝ}
    (hε : (n : ℝ)-δ ≤ ‖rademacherSum X x ε‖) :
    ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ ∀ i, 1-δ ≤ φ (sign (ε i) • x i) := by
  obtain ⟨φ,hφ,he⟩ := exists_dual_vector'' ℝ (rademacherSum X x ε)
  have hb i : φ (sign (ε i) • x i) ≤ 1 := by
    apply (le_abs_self _).trans
    have hn : ‖sign (ε i) • x i‖ ≤ 1 := by
      cases ε i <;> simpa using hx i
    exact (φ.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hφ).trans hn)
  refine ⟨φ,hφ,fun i => ?_⟩
  have hs : (∑ j, (1-φ (sign (ε j) • x j))) ≤ δ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hv : (∑ j, φ (sign (ε j) • x j)) = ‖rademacherSum X x ε‖ := by
      rw [← map_sum]; exact he
    rw [hv]; linarith
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sub_nonneg.mpr (hb j))
    (Finset.mem_univ i)
  linarith

theorem l1Family_of_all_signs_large {n : ℕ} (x : Fin n → X)
    (hx : ∀ i, ‖x i‖ ≤ 1) {δ : ℝ}
    (h : ∀ ε : Cube n, (n : ℝ)-δ ≤ ‖rademacherSum X x ε‖) :
    L1Family x (1-δ) := by
  classical
  refine ⟨hx,fun a => ?_⟩
  let ε : Cube n := fun i => decide (a i < 0)
  have ha i : |a i| * sign (ε i) = a i := by
    dsimp [ε, sign]
    split_ifs with hi
    · have hi' : a i < 0 := by simpa using hi
      rw [abs_of_neg hi']; ring
    · have hi' : ¬ a i < 0 := by simpa using hi
      rw [abs_of_nonneg (le_of_not_gt hi')]; ring
  obtain ⟨φ,hφ,hv⟩ := exists_common_sign_norming x hx ε (h ε)
  have hb : (1-δ)*∑ i, |a i| ≤ φ (∑ i, a i • x i) := by
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |a i| * φ (sign (ε i) • x i) := by nlinarith [hv i, abs_nonneg (a i)]
      _ = φ (a i • x i) := by rw [← smul_eq_mul, ← map_smul, smul_smul, ha]
  exact hb.trans ((le_abs_self _).trans ((φ.le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hφ)))

theorem l1Family_of_not_bConvex (h : ¬ BConvex X) {c : ℝ} (hc : c < 1) (n : ℕ) :
    ∃ x : Fin n → X, L1Family x c := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨fun i => Fin.elim0 i, by simp [L1Family]⟩
  have hh : ¬ ∀ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ)-(1-c) := by
    intro hh
    exact h ⟨n,Nat.pos_of_ne_zero hn,1-c,sub_pos.mpr hc,hh⟩
  push Not at hh
  obtain ⟨x,hx,hs⟩ := hh
  exact ⟨x, by simpa using l1Family_of_all_signs_large x hx (fun ε => (hs ε).le)⟩

theorem uniformL1_of_not_bConvex (h : ¬ BConvex X) : UniformL1 X :=
  ⟨1/2,by norm_num,fun n => l1Family_of_not_bConvex h (by norm_num) n⟩

theorem bConvex_of_not_uniformL1 (h : ¬ UniformL1 X) : BConvex X := by
  by_contra hb
  exact h (uniformL1_of_not_bConvex hb)

end Cotype

end

end OAI
