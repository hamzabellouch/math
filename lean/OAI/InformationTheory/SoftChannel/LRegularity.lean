import OAI.InformationTheory.BooleanNoise.LRegularity
import OAI.InformationTheory.SoftChannel.JensenGaps

namespace OAI

section

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem LRegularity_L_eq_rGap_on_left {x : ℝ} (hx : x ∈ Ioc 0 ell) :
    L x = rGap (ell - x) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact L_eq_rGap ⟨hx.1, hlt⟩
  · simp [L]

theorem LRegularity_LDeriv_eq_formula_on_left {x : ℝ} (hx : x ∈ Ioc 0 ell) :
    LDeriv x = 2 - rDeriv (ell - x) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact ite_eq_left ⟨hx.1, hlt⟩
  · simp [LDeriv]

theorem LRegularity_L_join_neighborhood : Ioc (0 : ℝ) ell ∪ Ici ell ∈ 𝓝 ell := by
  apply mem_of_superset (Ioi_mem_nhds ell_pos)
  intro x hx
  rcases le_total x ell with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr h

end LeanBlast.CourtadeKumar
end
end

end OAI
