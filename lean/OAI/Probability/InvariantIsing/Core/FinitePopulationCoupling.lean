import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalTransport

namespace OAI

/-! A coupling retains a common fraction of every population and sends
the remaining mass independently to the required residual population. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

def retainedPopulationCoupling {A : Type*} [DecidableEq A]
    (γ δ : A → ℝ) (ε : ℝ) (a j : A) : ℝ :=
  (if a=j then (1-ε)*γ a else 0)+γ a*(δ j-(1-ε)*γ j)

lemma retainedPopulationCoupling_nonneg {A : Type*} [DecidableEq A]
    (γ δ : A → ℝ) {ε : ℝ} (hε : ε ≤ 1) (hγ : ∀ a, 0 ≤ γ a)
    (hδ : ∀ a, (1-ε)*γ a ≤ δ a) (a j : A) :
    0 ≤ retainedPopulationCoupling γ δ ε a j := by
  apply add_nonneg
  · split_ifs
    · exact mul_nonneg (sub_nonneg.mpr hε) (hγ a)
    · rfl
  · exact mul_nonneg (hγ a) (sub_nonneg.mpr (hδ j))

lemma retainedPopulationCoupling_row {A : Type*} [Fintype A] [DecidableEq A]
    (γ δ : A → ℝ) (hγ : ∑ a, γ a=1) (hδ : ∑ a, δ a=1) (ε : ℝ) (a : A) :
    ∑ j, retainedPopulationCoupling γ δ ε a j=γ a := by
  simp only [retainedPopulationCoupling,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum,hγ,hδ]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  ring

lemma retainedPopulationCoupling_col {A : Type*} [Fintype A] [DecidableEq A]
    (γ δ : A → ℝ) (hγ : ∑ a, γ a=1) (ε : ℝ) (j : A) :
    ∑ a, retainedPopulationCoupling γ δ ε a j=δ j := by
  simp only [retainedPopulationCoupling,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,hγ]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

lemma retainedPopulationCoupling_cost {A : Type*} [Fintype A] [DecidableEq A]
    (γ δ b : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hδsum : ∑ a, δ a=1) {ε D : ℝ}
    (hδ : ∀ a, (1-ε)*γ a ≤ δ a) (hb : ∀ a, |b a| ≤ D) :
    (∑ a, ∑ j, retainedPopulationCoupling γ δ ε a j* |b a-b j|) ≤ 2*D*ε := by
  have he a j : retainedPopulationCoupling γ δ ε a j* |b a-b j|=
      (γ a*(δ j-(1-ε)*γ j))* |b a-b j| := by
    unfold retainedPopulationCoupling
    split_ifs with h
    · subst j; simp
    · simp
  simp_rw [he]
  calc
    _ ≤ ∑ a, ∑ j, (γ a*(δ j-(1-ε)*γ j))*(2*D) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [hb a,hb j]))
        (mul_nonneg (hγ a) (sub_nonneg.mpr (hδ j)))
    _ = 2*D*ε := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_sub_distrib,
        ← Finset.mul_sum,hγsum,hδsum]
      rw [← Finset.sum_mul,hγsum]
      ring

end InvariantIsing

end

end OAI
