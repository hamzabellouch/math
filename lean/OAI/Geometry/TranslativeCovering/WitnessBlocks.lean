import OAI.Geometry.TranslativeCovering.DiagramActivity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4

namespace WitnessBlocks
open MeasureTheory PoissonDiagrams
open scoped BigOperators Classical

lemma certificates {Ω : Type u_1} {J : Type u_2} [MeasurableSpace Ω] [DecidableEq J]
    (S : Finset J) (μ : Measure Ω) (E : J → Set Ω) {B T : ℝ}
    (hpos : ∀ i ∈ S,0 < μ.real (E i)) (hle : ∀ i ∈ S,μ.real (E i) ≤ 1)
    (hfirst : ∑ i ∈ S,Real.log (1+(μ.real (E i))⁻¹) ≤ B)
    (hrow : ∑ i ∈ S,Real.log (1+∑ j ∈ S.erase i,Blocks.weight μ (E i) (E j)) ≤ T) :
    Real.exp (-B) ≤ (∏ i : S,μ.real (E i)) ∧ (∏ i : S,μ.real (E i)) ≤ 1 ∧
      diagram μ (fun i : S => E i) (fun i : S => E i) ≤
        (∏ i : S,μ.real (E i))^2*Real.exp (B+T) := by
  have hfirst' : ∑ i : S,Real.log (1+(μ.real (E i))⁻¹) ≤ B := by
    simpa using (Finset.sum_coe_sort S (fun i => Real.log (1+(μ.real (E i))⁻¹))).trans_le hfirst
  have he (i : S) :
      ∑ j ∈ (Finset.univ : Finset S).erase i,Blocks.weight μ (E i) (E j) =
      ∑ j ∈ S.erase i.val,Blocks.weight μ (E i) (E j) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i),Finset.sum_erase_eq_sub i.property]
    congr 1
    simpa using Finset.sum_coe_sort S (fun j => Blocks.weight μ (E i) (E j))
  have hrow' : ∑ i : S,Real.log (1+∑ j ∈ (Finset.univ : Finset S).erase i,
      Blocks.weight μ (E i) (E j)) ≤ T := by
    simp_rw [he]
    simpa using (Finset.sum_coe_sort S (fun i => Real.log (1+∑ j ∈ S.erase i,Blocks.weight μ (E i) (E j)))).trans_le hrow
  refine ⟨DiagramActivity.activity_lower μ (fun i : S => E i) (fun i => hpos i i.property) hfirst',
    DiagramActivity.activity_upper μ (fun i : S => E i) (fun i => hle i i.property),?_⟩
  exact DiagramActivity.self_activity_normalized μ (fun i : S => E i) (fun i => hpos i i.property) hfirst' (by simpa only [Finset.sum_erase_eq_sub (Finset.mem_univ _),Blocks.weight] using hrow')

lemma nonempty_slots {I : Type u_3} [Fintype I] [Nonempty I]
    (P : Finpartition (Finset.univ : Finset I)) : Nonempty P.parts := by
  obtain ⟨s,hs⟩ := P.parts_nonempty (by simpa using Finset.univ_nonempty.ne_empty)
  exact ⟨⟨s,hs⟩⟩

lemma card_slots {I : Type u_4} [Fintype I] [DecidableEq I]
    (P : Finpartition (Finset.univ : Finset I)) : Fintype.card P.parts ≤ Fintype.card I := by
  simpa using P.card_parts_le_card

end WitnessBlocks

end OAI
