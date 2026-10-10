import Mathlib
import OAI.Probability.SKGap.Localization.GramRobust

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

theorem gram_path_robust {κ : Type*} [Fintype κ] [DecidableEq κ]
    {a : ℝ} (ha : 0 < a) (H : Matrix κ κ ℝ) (C₀ : ℝ → Matrix κ κ ℝ)
    (hc₀ : Continuous C₀) (hherm : ∀ r ∈ Icc 0 a, (C₀ r).IsHermitian)
    (hzero : C₀ 0=0) (hdet : ∀ r ∈ Icc 0 a, (1-H*C₀ r).det ≠ 0) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ρ ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι κ ℝ)
        (C : Matrix κ κ ℝ), C.IsHermitian → dist (Qᵀ*Q) H < ρ →
        dist C (C₀ a) < ρ → ((1-δ) • (1 : Matrix ι ι ℝ)-Q*C*Qᵀ).PosDef := by
  let F := fun (p : ℝ × (Matrix κ κ ℝ × Matrix κ κ ℝ)) (r : ℝ) =>
    (1-((1-p.1)⁻¹ • p.2.1) * (C₀ r+(r/a) • (p.2.2-C₀ a))).det
  have hnear : ∀ᶠ p in 𝓝 (0,(H,C₀ a)), ∀ r ∈ Icc 0 a, F p r ≠ 0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have hbase : F (0,(H,C₀ a)) r ≠ 0 := by
      simpa only [F,sub_zero,inv_one,one_smul,sub_self,smul_zero,add_zero] using hdet r hr
    have hc : ContinuousAt (fun z => F z.1 z.2) ((0,(H,C₀ a)),r) := by
      unfold F
      fun_prop (disch := norm_num)
    exact hc.eventually (eventually_ne_nhds hbase)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ := min (ε/2) (1/2)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  refine ⟨δ,ε,hδ,hδ1,hε,?_⟩
  intro ι _ _ Q C hC hQ hCC
  have hin : dist (δ,(Qᵀ*Q,C)) (0,(H,C₀ a)) < ε := by
    simp only [Prod.dist_eq,dist_zero_right,Real.norm_eq_abs,abs_of_pos hδ,max_lt_iff]
    exact ⟨hδε,hQ,hCC⟩
  have hh := hball hin
  let D := fun r => C₀ r+(r/a) • (C-C₀ a)
  have hc : Continuous D := by unfold D; fun_prop
  have hhD : ∀ r ∈ Icc 0 a, (D r).IsHermitian := by
    intro r hr
    exact (hherm r hr).add
      ((hC.sub (hherm a ⟨ha.le,le_rfl⟩)).smul (R := ℝ) (isSelfAdjoint_iff.mpr (star_trivial (r/a))))
  have hz : D 0=0 := by simp [D,hzero]
  have heq : D a=C := by simp [D,div_self ha.ne']
  rw [← heq]
  apply positive_from_gram_path ha.le (sub_pos.mpr hδ1) Q D hc hhD hz
  intro r hr
  exact hh r hr

end SKGap
end
end

end OAI
