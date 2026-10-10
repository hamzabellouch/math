import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace OAI

/-! The weak subsequence criterion for convergence in operator norm. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralOperatorNorm_criterion {E Z : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : ℕ → E →L[ℝ] Z) (T₀ : E →L[ℝ] Z)
    (hsub : ∀ u : ℕ → E, (∀ n, ‖u n‖ ≤ 1) →
      ∃ v : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ L : E →L[ℝ] ℝ, Tendsto (fun n => L (u (φ n))) atTop (𝓝 (L v)))
    (hseq : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u : ℕ → E, ∀ v : E,
      (∀ n, ‖u n‖ ≤ 1) →
      (∀ L : E →L[ℝ] ℝ, Tendsto (fun n => L (u n)) atTop (𝓝 (L v))) →
      Tendsto (fun n => T (ns n) (u n)) atTop (𝓝 (T₀ v)))
    (hconst : ∀ u : ℕ → E, ∀ v : E, (∀ n, ‖u n‖ ≤ 1) →
      (∀ L : E →L[ℝ] ℝ, Tendsto (fun n => L (u n)) atTop (𝓝 (L v))) →
      Tendsto (fun n => T₀ (u n)) atTop (𝓝 (T₀ v))) :
    Tendsto T atTop (𝓝 T₀) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hn
  have hf : ∃ᶠ n in atTop, ε ≤ dist (T n) T₀ := by
    simpa only [Filter.Frequently,not_le,not_lt] using hn
  obtain ⟨ns,hns,hbad⟩ := exists_seq_forall_of_frequently hf
  have hx (n : ℕ) : ∃ u : E, ‖u‖ ≤ 1 ∧ ε/2 < ‖(T (ns n)-T₀) u‖ := by
    let A := T (ns n)-T₀
    have ha : ε/2 < ‖A‖ := (half_lt_self hε).trans_le
      (by simpa only [dist_eq_norm] using hbad n)
    obtain ⟨u,hu⟩ := A.exists_mul_lt_of_lt_opNorm (half_pos hε).le ha
    have hu0 : ‖u‖ ≠ 0 := by
      intro hz
      have hz' := norm_image_of_norm_eq_zero A A.continuous hz
      rw [hz,hz',mul_zero] at hu
      exact lt_irrefl _ hu
    have hup : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu0)
    refine ⟨‖u‖⁻¹ • u,?_,?_⟩
    · simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),
        inv_mul_cancel₀ hu0,le_refl]
    · simpa only [map_smul,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),div_eq_inv_mul] using
        (lt_div_iff₀ hup).2 hu
  choose u hu hTu using hx
  obtain ⟨v,φ,hφ,hw⟩ := hsub u (fun n => hu n)
  have h₁ := hseq (ns ∘ φ) (hns.comp hφ.tendsto_atTop) (u ∘ φ) v
    (fun n => hu (φ n)) hw
  have h₂ := hconst (u ∘ φ) v (fun n => hu (φ n)) hw
  have hd : Tendsto (fun n => ‖(T (ns (φ n))-T₀) (u (φ n))‖) atTop (𝓝 0) := by
    simpa only [sub_apply,Function.comp_def,sub_self,norm_zero] using
      (h₁.sub h₂).norm
  obtain ⟨n,hn⟩ := (hd.eventually (gt_mem_nhds (half_pos hε))).exists
  exact (not_lt_of_ge (hTu (φ n)).le) hn

end DefocusingNLS

end OAI
