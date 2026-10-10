import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetAbsorption
import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetEnvelope

namespace OAI

noncomputable section
open Filter
namespace Ostmann.Characters.HistoryFrequencyBudget

theorem normalized_budget_eventually (j : ℕ) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 ≤ C → ∀ D : ℝ, 0 < D → ∀ K : ℝ, 0 ≤ K →
      ∀ᶠ m : ℝ in atTop,
        K*Real.exp (-(2:ℝ)^j*a*m)*
          FrequencyTreeSum.budget (ranges a m j)
            (fun p => C*(bound a m (j-p.length):ℝ)^ε *
              (2*D*(bound a m (j-(false::p).length):ℝ)^ε *
                (1+Real.log (bound a m (j-p.length))))) j [] ≤ Real.exp (δ*m) := by
  let r : ℝ := (2:ℝ)^j
  let A := linearEnvelope a j
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : 1 ≤ r := one_le_pow₀ (by norm_num)
  have hA : 0 < A := linearEnvelope_pos ha.le j
  let ε := δ/(4*r*A)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,?_⟩
  intro C hC D hD K hK
  let c := Real.log (max K 1) + r*Real.log 2 +
    (r-1)*Real.log (max (2*C*D) 1*(1+A))
  have heq : 2*r*ε*A = δ/2 := by
    dsimp [ε]
    field_simp
    ring
  have hlead : 2*(r-1)*ε*A ≤ δ/2 := by
    rw [← heq]
    have := mul_nonneg hε.le hA.le
    nlinarith
  have herr := eventually_const_sqrt_le (4*r-2) c (δ/2) (by positivity)
  filter_upwards [herr,eventually_ge_atTop (1:ℝ)] with m hmerr hm
  have hb := budget_bound hC hD hε.le ha.le hm j
  have hm0 : 0 ≤ m := by linarith
  have hKpos : 0 < max K 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  calc
    _ ≤ K*Real.exp (-r*a*m)*
        Real.exp (r*(Real.log 2+a*m+2*Real.sqrt m)+(r-1)*nodeExponent C D ε a m j) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg hK (Real.exp_pos _).le)
    _ ≤ max K 1*Real.exp (-r*a*m)*
        Real.exp (r*(Real.log 2+a*m+2*Real.sqrt m)+(r-1)*nodeExponent C D ε a m j) := by
      gcongr
      exact le_max_left _ _
    _ = Real.exp (2*(r-1)*ε*A*m+(4*r-2)*Real.sqrt m+c) := by
      rw [← Real.exp_log hKpos,← Real.exp_add,← Real.exp_add]
      congr 1
      dsimp [nodeExponent,c,A]
      ring
    _ ≤ Real.exp (δ*m) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hlead hm0
      linarith

theorem normalized_historyTotal_eventually (j : ℕ) {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 ≤ C → ∀ K : ℝ, 0 ≤ K →
      ∀ᶠ m : ℝ in atTop,
        K*Real.exp (-(2:ℝ)^j*a*m)*
          HistoryFrequencyLabels.historyTotal (ranges a m j)
            (ReducedFrequencyTree.factor ε C) j [] ≤ Real.exp (δ*m) := by
  obtain ⟨ε,hε,hscalar⟩ := normalized_budget_eventually j ha hδ
  obtain ⟨D,hD,hsum⟩ := HistoryFrequencyLabels.historyTotal_reduced_le ε hε
  refine ⟨ε,hε,?_⟩
  intro C hC K hK
  filter_upwards [hscalar C hC D hD K hK,eventually_ge_atTop (1:ℝ)] with m hm hm1
  have hm0 : 0 ≤ m := by linarith
  have hb := hsum C hC (ranges a m j) (fun p => bound a m (j-p.length))
    (fun p => bound_pos ha.le hm0 _) (fun p s hs => (mem_signedRange _ _).mp hs) j []
  exact (mul_le_mul_of_nonneg_left hb (mul_nonneg hK (Real.exp_pos _).le)).trans hm

end Ostmann.Characters.HistoryFrequencyBudget

end

end OAI
