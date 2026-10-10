import Mathlib
import OAI.Analysis.HardSphere.Operators.Stationary
import OAI.Analysis.HardSphere.Thermodynamics.LowCountAbove

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.CellOrbital
open Wiener

theorem grid_stationary_low_above (Amin : ℝ) : ∃ α₀ ell D₀ Q : ℝ,
    Amin≤α₀ ∧ 0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (K n : ℕ) [Nontrivial (Fin n)] (L : Length) (D α : ℝ),
      1≤K → L.val=(K:ℝ) → D=(n:ℝ)/L.val^3 → D₀≤D → α₀/2≤α → α≤2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (T : ℝ), 0≤T → ∀ (q : Time) (A : Finset (Fin 3→Fin K)),
      groundPathLaw n L (α/D) T g {ω | ∀v∈A,(centeredCount L (gridCenter L v) (ω q):ℝ)<ell*D}≤
        ENNReal.ofReal ((Q/D^2)^A.card) := by
  obtain ⟨α₀,ell,D₀,Q,hA,hα,hell,hD₀,hQ,hs⟩ := scaled_joint_low_counts_above Amin
  refine ⟨α₀,ell,D₀,Q,hA,hα,hell,hD₀,hQ,?_⟩
  intro K n inst L D α hK hLK hDN hDD hαl hαu g hg T hT q A
  have hL : 1≤L.val := by rw [hLK]; exact_mod_cast hK
  have hn : 2≤n := Nat.succ_le_of_lt (by simpa only [Fintype.card_fin] using (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (Fin n))))
  have hset : MeasurableSet {X : Configuration n L | ∀v∈A,(centeredCount L (gridCenter L v) X:ℝ)<ell*D} := by
    simpa only [Set.ofPred_forall, Function.comp_def] using MeasurableSet.iInter (fun site ↦
      MeasurableSet.iInter (fun _ : site∈A ↦ measurableSet_lt
        ((measurable_of_countable (fun count : ℕ ↦ (count:ℝ))).comp
          (centeredCount_measurable L (gridCenter L site))) measurable_const))
  have hm := (hg.groundPathLaw_marginal T hT q).measure_preimage hset.nullMeasurableSet
  change groundPathLaw n L (α/D) T g ((fun ω ↦ ω q) ⁻¹' {X | ∀v∈A,(centeredCount L (gridCenter L v) X:ℝ)<ell*D})≤_
  rw [hm]
  apply (groundPositionLaw_le_joint (mul_pos hell (hD₀.trans_le hDD)) (gridCenter L) A g _ hset ?_).trans
  · exact ENNReal.ofReal_le_ofReal (hs (Fin 3→Fin K) n L D α hn hL hDN hDD hαl hαu g hg
      (gridCenter L) (gridCenter_separated hLK) A)
  · intro X hX v hv
    exact (count_le_centeredCount L (gridCenter L v) X).trans (hX v hv).le

end HardSphere.CellOrbital

end
end

end

end OAI
