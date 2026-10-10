import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Estimates.FullParallelCountFilter

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal
variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

def descriptorValid (N : ℕ) : PolicyDescriptor → Prop
  | .parallel g p => g ≤ p ∧ p ≤ N
  | .projection p t => p ≤ t ∧ t ≤ N

lemma endpointGood_at_cell (ρ : Measure V) (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ)
    (J i : ℕ) (b : PolicyDescriptor) {P : CellPath d}
    (hP : P ∈ dyadicPaths (descriptorAnchor b)) {x : V} (hx : x∈treeCell P) (w : V) :
    (x,w)∈endpointGood ρ m N sig C J i b ↔ w∈descriptorGood ρ m N sig C J i P b := by
  refine ⟨fun h => h P hP hx,?_⟩
  intro hw Q hQ hxQ
  have he : Q=P := by
    by_contra hn
    exact Set.disjoint_left.mp (treeCell_disjoint
      (((mem_dyadicPaths _ _).mp hQ).trans ((mem_dyadicPaths _ _).mp hP).symm) hn) hxQ hx
  simpa only [he] using hw

lemma ae_occupied_anchor (ρ : Measure V) [IsFiniteMeasure ρ] (p : ℕ)
    (hroot : ρ (treeCell [])ᶜ=0) :
    ∀ᵐ x ∂ρ, ∃ P∈dyadicPaths p, x∈treeCell P ∧ 0<ρ (treeCell P) := by
  have ha : ∀ P : CellPath d, ∀ᵐ x ∂ρ, x∈treeCell P → 0<ρ (treeCell P) := by
    intro P
    by_cases hp : 0<ρ (treeCell P)
    · exact Filter.Eventually.of_forall (fun _ _ => hp)
    · have hz : ρ (treeCell P)=0 := nonpos_iff_eq_zero.mp (le_of_not_gt hp)
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
      exact fun h => (hx h).elim
  have hall := ae_all_iff.mpr ha
  have hr : ∀ᵐ x ∂ρ, x∈treeCell [] := by
    simpa only [mem_compl_iff,not_not] using measure_eq_zero_iff_ae_notMem.mp hroot
  filter_upwards [hall,hr] with x hx hxroot
  rw [←treeCell_cover_root p] at hxroot
  obtain ⟨P,hP,hxp⟩ := mem_iUnion₂.mp hxroot
  exact ⟨P,hP,hxp,hx P hxp⟩

theorem uniform_original_fiber_test_bound (sig : ℝ) (hsig : 0<sig) :
    ∃ N₀ : ℕ, ∀ N≥N₀, ∀ (ρ : Measure V) (m : ℝ → ℝ) (B : ℕ) (s : ℝ),
      RegularizedProfileData ρ N B s sig m →
      ∀ (ν : Measure V) [IsProbabilityMeasure ν] (S : Set V), MeasurableSet S →
      ∀ dir : V → V, Measurable dir → (∀ y∈S, ‖dir y‖=1) →
      (∀ w : V, ‖w‖=1 → ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ν {y | y∈S ∧ dir y∈ball w r} ≤ ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      ∀ (J : ℕ) (b : PolicyDescriptor), descriptorValid N b →
      ∀ x : V, (∃ P∈dyadicPaths (descriptorAnchor b), x∈treeCell P ∧ 0<ρ (treeCell P)) →
        ν {y | y∈S ∧ (x,dir y)∉endpointGood ρ m N sig (1000*(d+1:ℝ)) J 0 b} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
  obtain ⟨N₁,hparallel⟩ := uniform_actual_parallel_exceptional d sig hsig
  obtain ⟨N₂,hprojection⟩ := uniform_actual_projection_exceptional d sig hsig
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ρ m B s hr ν _ S hS dir hdir hunit hcap J b hb x hx
  obtain ⟨P,hP,hx,hpos⟩ := hx
  let ξ : Measure V := (ν.restrict S).map dir
  have hfinite : IsFiniteMeasure ξ := by dsimp [ξ]; infer_instance
  have hmass : ξ univ ≤ 1 := by
    dsimp only [ξ]
    rw [Measure.map_apply hdir MeasurableSet.univ]
    simpa only [preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter] using (prob_le_one (μ:=ν) (s:=S))
  have hsphere : ∀ᵐ w ∂ξ, ‖w‖=1 := by
    dsimp only [ξ]
    rw [ae_map_iff hdir.aemeasurable (measurableSet_eq_fun measurable_norm measurable_const)]
    filter_upwards [ae_restrict_mem hS] with y hy
    exact hunit y hy
  have hc : ∀ w : V, ‖w‖=1 → ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      ξ (ball w r) ≤ ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2)) := by
    intro w hw r hr0 hr1
    dsimp only [ξ]
    rw [Measure.map_apply hdir measurableSet_ball,Measure.restrict_apply (hdir measurableSet_ball)]
    convert hcap w hw r hr0 hr1 using 1
    congr 1
    ext y
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,and_comm]
  have ht : ξ (descriptorGood ρ m N sig (1000*(d+1:ℝ)) J 0 P b)ᶜ ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
    cases b with
    | parallel g p =>
        exact hparallel N (by omega) ρ m B s hr ξ hfinite hmass hsphere hc J g p hb.1 hb.2
          P ((mem_dyadicPaths _ _).mp hP) hpos
    | projection p t =>
        exact hprojection N (by omega) ρ m B s hr ξ hfinite hmass hsphere hc J p t hb.1 hb.2
          P ((mem_dyadicPaths _ _).mp hP) hpos
  let := hr.probability
  dsimp only [ξ] at ht
  rw [Measure.map_apply hdir (measurable_descriptorGood _ _ _ _ _ _ _ _ _).compl,
    Measure.restrict_apply (hdir (measurable_descriptorGood _ _ _ _ _ _ _ _ _).compl)] at ht
  convert ht using 1
  congr 1
  ext y
  simp only [mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_compl_iff,endpointGood_at_cell ρ m N sig
    (1000*(d+1:ℝ)) J 0 b hP hx,and_comm]
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
