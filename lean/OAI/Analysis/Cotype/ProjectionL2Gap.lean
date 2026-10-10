import OAI.Analysis.Cotype.ProjectionSemigroup
import OAI.Analysis.Cotype.TypeL2Amplification

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem sign_deficit_of_quadraticTypeBound {n : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (h : QuadraticTypeBound X n A) (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ Real.sqrt (A*n) := by
  classical
  have hsum : (∑ i, ‖x i‖^2) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by nlinarith [hx i, norm_nonneg (x i)])
      _ = _ := by simp
  have hb : average (fun ε => ‖rademacherSum X x ε‖^2) ≤ A*n := by
    rw [← cubeL2_sq]
    exact (h x).trans (mul_le_mul_of_nonneg_left hsum hA)
  by_contra hh
  push Not at hh
  have hp ε : A*n < ‖rademacherSum X x ε‖^2 := by
    have hs := Real.sq_sqrt (mul_nonneg hA (Nat.cast_nonneg n))
    nlinarith [hh ε, Real.sqrt_nonneg (A*n), norm_nonneg (rademacherSum X x ε)]
  have hstrict := Finset.sum_lt_sum (fun ε (_ : ε ∈ Finset.univ) => (hp ε).le)
    ⟨fun _ => false, Finset.mem_univ _, hp _⟩
  have hc : (0 : ℝ) < Fintype.card (Cube n) := by exact_mod_cast Fintype.card_pos
  have hmul := mul_lt_mul_of_pos_left hstrict (inv_pos.mpr hc)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] at hmul
  exact (not_lt_of_ge hb) hmul

theorem uniform_sign_deficit_l2Amplification (h : BConvex X) :
    ∃ n : ℕ, 0 < n ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω],
      ∀ x : Fin n → PiLp 2 (fun _ : Ω => X), (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum (PiLp 2 (fun _ : Ω => X)) x ε‖ ≤ (n : ℝ)-δ := by
  obtain ⟨n,hn,A,hA,hAn,hgap⟩ := fixed_quadratic_improvement_of_bConvex h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (A*n) < (n : ℝ) := by
    apply (Real.sqrt_lt' hnR).mpr
    nlinarith
  refine ⟨n,hn,(n : ℝ)-Real.sqrt (A*n),sub_pos.mpr hs,?_⟩
  intro Ω _ _ x hx
  simpa only [sub_sub_cancel] using
    sign_deficit_of_quadraticTypeBound hA (quadraticTypeBound_l2Amplification hgap) x hx

theorem uniform_projectionSemigroup_power_gap_l2Amplification (h : NontrivialType X) :
    ∃ n : ℕ, 0 < n ∧ ∃ C : ℝ, 0 ≤ C ∧ C < (2 : ℝ)^n ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (m : ℕ)
        (P : Fin m → PiLp 2 (fun _ : Ω => X) →L[ℝ] PiLp 2 (fun _ : Ω => X)),
        (∀ i, P i * P i = P i) → (∀ i j, Commute (P i) (P j)) →
        (∀ i x, ‖P i x‖ ≤ ‖x‖) → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        ∀ y, ‖((1-projectionSemigroup P r)^n) y‖ ≤ C*‖y‖ := by
  obtain ⟨n,hn,δ,hδ,hgap⟩ := uniform_sign_deficit_l2Amplification (nontrivialType_iff_bConvex.mp h)
  let C : ℝ := max 0 ((2 : ℝ)^n-δ/n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨n,hn,C,le_max_left _ _,?_,?_⟩
  · exact max_lt (by positivity) (sub_lt_self _ (div_pos hδ hnR))
  · intro Ω _ _ m P hp hc hP r hr hr1 y
    exact (projectionSemigroup_power_bound_of_sign_deficit hn (hgap Ω) P hp hc hP hr hr1 y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg y))

end Cotype

end

end OAI
