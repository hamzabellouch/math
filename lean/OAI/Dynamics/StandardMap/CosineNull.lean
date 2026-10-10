import OAI.Dynamics.StandardMap.MeanGrowth

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma countable_cosine_zero : Set.Countable {x : Circle | cosine x=0} := by
  apply (Set.countable_range (fun m : ℤ => (((2*(m:ℝ)+1)/4:ℝ) : Circle))).mono
  intro x hx
  obtain ⟨r,rfl⟩ := (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1:ℝ))) x
  change Real.cos (2*Real.pi*r)=0 at hx
  obtain ⟨m,hm⟩ := Real.cos_eq_zero_iff.mp hx
  refine ⟨m,?_⟩
  have he : r=(2*(m:ℝ)+1)/4 := by
    have hp := Real.pi_pos
    nlinarith
  rw [he]
instance circleVolumeNullSingleton : NullSingletonClass (volume : Measure Circle) := by
  constructor
  intro x
  rw [← Metric.closedBall_zero (x := x),AddCircle.volume_closedBall]
  norm_num
lemma volume_cosine_zero : volume {x : Circle | cosine x=0}=0 := countable_cosine_zero.measure_zero volume
lemma cosine_small_measure (η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ volume {x : Circle | |cosine x|≤δ}<ENNReal.ofReal η := by
  let E : ℕ → Set Circle := fun n => {x | |cosine x|≤1/((n:ℝ)+1)}
  have hm : Antitone E := by
    intro i j hij x hx
    change |cosine x|≤1/((i:ℝ)+1)
    change |cosine x|≤1/((j:ℝ)+1) at hx
    exact hx.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1))
  have he : (⋂ n,E n)={x : Circle | cosine x=0} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,E]
    constructor
    · intro hx
      apply abs_eq_zero.mp
      by_contra hn
      have hp : 0 < |cosine x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hn)
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt hp
      exact (not_lt_of_ge (hx n)) hn
    · intro hx n; simp [hx]; positivity
  have ht := tendsto_measure_iInter_atTop
    (μ := (volume : Measure Circle)) (s := E)
    (fun n => ((isClosed_le continuous_cosine.abs continuous_const).measurableSet.nullMeasurableSet)) hm
    ⟨0,measure_ne_top _ _⟩
  rw [he,volume_cosine_zero] at ht
  have hh : ∀ᶠ n : ℕ in atTop, volume (E n)<ENNReal.ofReal η :=
    ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨n,hn⟩ := hh.exists
  refine ⟨1/((n:ℝ)+1),by positivity,?_,hn⟩
  exact (div_le_one (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
end StandardMapEntropy

end OAI
