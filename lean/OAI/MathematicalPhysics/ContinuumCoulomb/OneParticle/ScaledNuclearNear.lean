import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SeparatedNuclearNear

namespace OAI

/-! Equal-mass near-node errors have the required square-mesh scaling.
The constant depends on the separation and near-ball ratios, not on the
number of nuclei or the size of the box. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem scaled_nuclear_near_bound {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m n : ℕ) (u : Coulomb.H1Vector n)
      (s : SpinConfiguration n) (i : Fin n) (R : Fin m → Position) (h ρ : ℝ),
      0 < h → h ≤ 1 → 0 ≤ ρ →
      (∀ a b, a ≠ b → σ*h ≤ ‖R a-R b‖) →
      (ρ*h^3/8)*(∑ a, ∫ x in electronBall i (R a) (κ*h),
        Coulomb.coulombKernel (Coulomb.position x i-R a)*‖u.value s x‖^2) ≤
      ρ*A*h^2*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
  obtain ⟨C,hC,hbound⟩ := separated_nuclear_near_bound
  let M : ℝ := (4*κ+σ)^3/σ^3
  let B : ℝ := max (24*C^2/κ) (8*κ)
  let A : ℝ := max 1 (M/8*B)
  refine ⟨A,le_max_left _ _,fun m n u s i R h ρ hh hh1 hρ hsep => ?_⟩
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 ≤ B := (by positivity : 0 ≤ 24*C^2/κ).trans (le_max_left _ _)
  have hmass : 0 ≤ ∫ x, ‖u.value s x‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hgrad : 0 ≤ ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hh2 : h^2 ≤ 1 := by nlinarith
  have he := hbound m n u s i R (κ*h) (σ*h) (mul_pos hκ hh) (mul_pos hσ hh) hsep
  have hr : (4*(κ*h)+σ*h)^3/(σ*h)^3 = M := by
    dsimp [M]
    field_simp [hσ.ne',hh.ne']
  rw [hr] at he
  have hb : (24*C^2/κ)*(∫ x, ‖u.value s x‖^2)+
      8*κ*h^2*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) ≤
      B*((∫ x, ‖u.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
    rw [mul_add]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hmass
    · apply mul_le_mul_of_nonneg_right _ hgrad
      exact (mul_le_mul_of_nonneg_left hh2 (by positivity : 0 ≤ 8*κ)).trans
        (by simpa only [mul_one] using (le_max_right (24*C^2/κ) (8*κ)))
  calc
    _ ≤ (ρ*h^3/8)*(M*((24*C^2/(κ*h))*(∫ x, ‖u.value s x‖^2)+
        8*(κ*h)*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (ρ*h^2)*(M/8)*((24*C^2/κ)*(∫ x, ‖u.value s x‖^2)+
        8*κ*h^2*(∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) := by
      field_simp [hκ.ne',hh.ne']
    _ ≤ (ρ*h^2)*(M/8)*(B*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ ρ*A*h^2*((∫ x, ‖u.value s x‖^2)+
        ∑ k : Fin 3, ∫ x, ‖u.gradient s (i,k) x‖^2) := by
      have ha : M/8*B ≤ A := le_max_right _ _
      nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ha (add_nonneg hmass hgrad))
        (show 0 ≤ ρ*h^2 by positivity)]

end ContinuumCoulomb

end

end OAI
