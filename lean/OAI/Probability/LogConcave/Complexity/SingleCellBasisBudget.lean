import Mathlib
import OAI.Probability.LogConcave.Sampling.ProbabilityNodes

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

def singleCellBasisBudget (n : ℕ) : ℝ :=
  Classical.choose (exists_basis_budget (probabilityNodes n))

lemma singleCellBasisBudget_spec (n : ℕ) :
    1 ≤ singleCellBasisBudget n ∧
      ∀v∈Icc (0:ℝ) 1,∑i,|basis (probabilityNodes n) i v| ≤ singleCellBasisBudget n :=
  Classical.choose_spec (exists_basis_budget (probabilityNodes n))

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ : Measure Ω}

omit [CompleteSpace E] in
theorem singleCell_interpolation_rms (n : ℕ) (hn : 0<n) (C : ℝ) (hC : 1 ≤ C)
    (hC' : ∀v∈Icc (0:ℝ) 1,∑i,|basis (probabilityNodes n) i v| ≤ C) :
    ∀J : ℕ → ℝ → Ω → E, (∀k t,Measurable (J k t)) →
      ∀B : ℝ,0 ≤ B →
      (∀t∈Icc (0:ℝ) 1,
        Integrable (fun y => ‖J 0 t y-chainTaylor (fun k v => J k v y) n 0 t‖^2) μ ∧
        (∫y,‖J 0 t y-chainTaylor (fun k v => J k v y) n 0 t‖^2 ∂μ) ≤
          (t^(n+1)/(n.factorial:ℝ))^2*B) →
      ∀v∈Icc (0:ℝ) 1,
        Integrable (fun y => ‖J 0 v y-interpolation (probabilityNodes n)
          (fun i => J 0 (probabilityNodes n i) y) v‖^2) μ ∧
        (∫y,‖J 0 v y-interpolation (probabilityNodes n)
          (fun i => J 0 (probabilityNodes n i) y) v‖^2 ∂μ) ≤ 4*C^2*B := by
  intro J hJ B hB htay v hv
  have hs (t : ℝ) (ht : t∈insert v (range (probabilityNodes n))) : t∈Icc (0:ℝ) 1 := by
    rcases ht with rfl|⟨i,rfl⟩
    · exact hv
    · exact probabilityNodes_mem hn i
  have h := cell_chain_error_rms (probabilityNodes n) (probabilityNodes_injective hn) n
    (by simp) J 0 1 v hB hC (hC' v hv)
    (fun t _ => by
      simp only [zero_add,one_mul]
      apply Measurable.aestronglyMeasurable
      exact (hJ 0 t).sub (chainTaylor_measurable J hJ n 0 t))
    (fun t ht => by simpa only [zero_add,one_mul] using (htay t (hs t ht)).1)
    (fun t ht => by
      simp only [zero_add,one_mul]
      apply (htay t (hs t ht)).2.trans
      apply mul_le_of_le_one_left hB
      apply pow_le_one₀ (by positivity [(hs t ht).1])
      apply (div_le_iff₀ (by positivity : 0<(n.factorial:ℝ))).mpr
      simp only [one_mul]
      exact (pow_le_one₀ (hs t ht).1 (hs t ht).2).trans (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)))
  simpa only [zero_add,one_mul] using h

theorem singleCell_quadrature_rms [SFinite μ] (n : ℕ) (f : ℝ → Ω → E)
    (hm : Measurable (fun p : ℝ × Ω => f p.1 p.2))
    (hc : ∀y,ContinuousOn (fun t => f t y) (Icc (0:ℝ) 1))
    {B : ℝ} (hB : 0 ≤ B)
    (hi : ∀t∈Icc (0:ℝ) 1,Integrable (fun y => ‖f t y-interpolation (probabilityNodes n)
      (fun i => f (probabilityNodes n i) y) t‖^2) μ)
    (hb : ∀t∈Icc (0:ℝ) 1,(∫y,‖f t y-interpolation (probabilityNodes n)
      (fun i => f (probabilityNodes n i) y) t‖^2 ∂μ) ≤ B)
    {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1) :
    Integrable (fun y => ‖(∫t in 0..θ,f t y)-∑i,weight (probabilityNodes n) i 0 θ •
      f (probabilityNodes n i) y‖^2) μ ∧
    (∫y,‖(∫t in 0..θ,f t y)-∑i,weight (probabilityNodes n) i 0 θ •
      f (probabilityNodes n i) y‖^2 ∂μ) ≤ B := by
  have hh := cellQuadrature_error_rms (probabilityNodes n) f 1 hθ.1
    (fun y => ((hc y).mono (by
      intro t ht; exact ⟨ht.1,ht.2.trans hθ.2⟩)).intervalIntegrable_of_Icc hθ.1)
    (by
      apply Measurable.aestronglyMeasurable
      apply hm.sub
      unfold interpolation
      exact Finset.measurable_sum _ (fun i _ =>
        ((basis_continuous (probabilityNodes n) i).measurable.comp measurable_fst).smul
          (hm.comp (measurable_const.prodMk measurable_snd))))
    (fun t ht => hi t ⟨ht.1.le,ht.2.trans hθ.2⟩)
    (fun t ht => hb t ⟨ht.1.le,ht.2.trans hθ.2⟩)
  simp only [one_smul,cellQuadrature,one_mul,one_pow] at hh
  exact ⟨hh.1,hh.2.trans (mul_le_of_le_one_left hB (pow_le_one₀ hθ.1 hθ.2))⟩
end LogConcaveSampling

end

end

end OAI
