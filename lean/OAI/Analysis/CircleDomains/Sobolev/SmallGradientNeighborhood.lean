import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneSobolev
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! An integrable gradient that vanishes on a closed set has arbitrarily
small energy on open neighborhoods of that set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_open_integral_small_of_zero_on_closed
    {f : EuclideanPlane → ℝ} (hf : Integrable f volume)
    {F : Set EuclideanPlane} (hF : IsClosed F)
    (hz : ∀ᵐ x ∂volume, x ∈ F → f x=0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set EuclideanPlane, IsOpen U ∧ F ⊆ U ∧ (∫ x in U, f x) < ε := by
  let U (n : ℕ) := thickening (1/((n : ℝ)+1)) F
  have ho (n : ℕ) : IsOpen (U n) := isOpen_thickening
  have hsub (n : ℕ) : F ⊆ U n := by
    intro x hx
    exact mem_thickening_iff.mpr ⟨x, hx, by simp; positivity⟩
  have ha : Antitone U := by
    intro m n hmn
    apply thickening_mono
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hcap : (⋂ n, U n) = F := by
    apply Subset.antisymm
    · intro x hx
      rw [← hF.closure_eq, closure_eq_iInter_thickening]
      refine mem_iInter.mpr fun r => mem_iInter.mpr fun hr => ?_
      have ht := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hr)
      obtain ⟨n, hn⟩ := ht.exists
      exact thickening_mono hn.le F (mem_iInter.mp hx n)
    · exact subset_iInter hsub
  have ht := tendsto_setIntegral_of_antitone (fun n => (ho n).measurableSet) ha
    ⟨0, hf.integrableOn⟩
  have hzero : (∫ x in F, f x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem hF.measurableSet] with x hx hxF
    exact hx hxF
  rw [hcap, hzero] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨U n, ho n, hsub n, hn⟩

end CircleDomainRigidity

end

end OAI
