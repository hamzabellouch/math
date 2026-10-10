import OAI.Analysis.CircleDomains.Uniformization.NondegeneratePhaseSubsequence
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Uniform nondegeneration of the actual selected round holes. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

lemma PhaseCollar.selectedRadius_lower_bound (P:PhaseCollar C i) :
    ∃δ:ℝ,0<δ ∧ ∀n,δ ≤ selectedRadius C (cyclicSchedule m) (visitTime n i) := by
  classical
  by_contra hn
  push Not at hn
  have hex (k:ℕ) : ∃n,selectedRadius C (cyclicSchedule m) (visitTime n i)<1/((k:ℝ)+1) :=
    hn _ (by positivity)
  choose t ht using hex
  have hzero : Tendsto (fun k => selectedRadius C (cyclicSchedule m) (visitTime (t k) i))
      atTop (𝓝 (0:ℝ)) :=
    squeeze_zero (fun k => (selectedRadius_pos C (cyclicSchedule m) (visitTime (t k) i)).le)
      (fun k => (ht k).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨s,ρ,hs,hρ,hlim⟩ := P.exists_positive_radius_limit_along t
  have he : ρ=0 := tendsto_nhds_unique hlim (hzero.comp hs.tendsto_atTop)
  exact hρ.ne' he

lemma selectedRadii_common_lower_bound {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1)))
    (ha:∀i,IsAnalyticJordanCap (C.hole i)) :
    ∃δ:ℝ,0<δ ∧ ∀n (i:Fin (m+1)),δ ≤ selectedRadius C (cyclicSchedule m) (visitTime n i) := by
  classical
  have hex (i:Fin (m+1)) : ∃δ:ℝ,0<δ ∧ ∀n,δ ≤ selectedRadius C (cyclicSchedule m) (visitTime n i) := by
    obtain ⟨P⟩ := phaseCollar_nonempty C ha i
    exact P.selectedRadius_lower_bound
  choose δ hδ hbound using hex
  let S : Finset ℝ := Finset.univ.image δ
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨S.min' hS,?_,?_⟩
  · exact (Finset.lt_min'_iff _ _).mpr (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hδ i)
  · intro n i
    exact (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)).trans (hbound i n)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
