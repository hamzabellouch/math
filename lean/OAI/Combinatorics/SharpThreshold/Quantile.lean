import Mathlib

namespace OAI

noncomputable section
namespace Problem313

def unitQuantile (μ : ℝ → ℝ) (a : ℝ) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}

theorem unitQuantile_set_bddBelow (μ : ℝ → ℝ) (a : ℝ) :
    BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} :=
  ⟨0, fun _ hp => hp.1.1⟩

theorem unitQuantile_set_nonempty {μ : ℝ → ℝ} {a : ℝ}
    (h1 : μ 1 = 1) (ha : a ≤ 1) :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}.Nonempty := by
  refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
  simpa only [h1] using ha

theorem unitQuantile_mem {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h1 : μ 1 = 1) (ha : a ≤ 1) :
    unitQuantile μ a ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ (unitQuantile μ a) := by
  have hc : IsClosed {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} :=
    isClosed_Icc.inter (isClosed_le continuous_const hμ)
  exact hc.csInf_mem (unitQuantile_set_nonempty h1 ha) (unitQuantile_set_bddBelow μ a)

theorem unitQuantile_eq_level {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    μ (unitQuantile μ a) = a := by
  have hq := unitQuantile_mem hμ h1 ha1
  have ha : a ∈ Set.Icc (μ 0) (μ (unitQuantile μ a)) := by
    exact ⟨by simpa only [h0] using ha0, hq.2⟩
  obtain ⟨x, hx, heq⟩ := intermediate_value_Icc hq.1.1 hμ.continuousOn ha
  have hqx : unitQuantile μ a ≤ x := by
    apply csInf_le (unitQuantile_set_bddBelow μ a)
    exact ⟨⟨hx.1, hx.2.trans hq.1.2⟩, heq.ge⟩
  have hxq : x = unitQuantile μ a := le_antisymm hx.2 hqx
  simpa only [hxq] using heq

theorem unitQuantile_mem_Ioo {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    unitQuantile μ a ∈ Set.Ioo (0 : ℝ) 1 := by
  have hq := (unitQuantile_mem hμ h1 ha1.le).1
  have heq := unitQuantile_eq_level hμ h0 h1 ha0.le ha1.le
  constructor
  · refine lt_of_le_of_ne hq.1 ?_
    intro he
    rw [← he, h0] at heq
    exact ha0.ne heq
  · refine lt_of_le_of_ne hq.2 ?_
    intro he
    rw [he, h1] at heq
    exact ha1.ne heq.symm

theorem unitQuantile_mono {μ : ℝ → ℝ} {a b : ℝ}
    (h1 : μ 1 = 1) (hab : a ≤ b) (hb : b ≤ 1) :
    unitQuantile μ a ≤ unitQuantile μ b := by
  apply csInf_le_csInf (unitQuantile_set_bddBelow μ a)
    (unitQuantile_set_nonempty h1 hb)
  intro p hp
  exact ⟨hp.1, hab.trans hp.2⟩

theorem unitQuantile_strictMonoOn {μ : ℝ → ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1) :
    StrictMonoOn (unitQuantile μ) (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hle := unitQuantile_mono h1 hab.le hb.2
  refine lt_of_le_of_ne hle ?_
  intro heq
  have haeq := unitQuantile_eq_level hμ h0 h1 ha.1 ha.2
  have hbeq := unitQuantile_eq_level hμ h0 h1 hb.1 hb.2
  rw [heq, hbeq] at haeq
  exact hab.ne haeq.symm

end Problem313

end

end OAI
