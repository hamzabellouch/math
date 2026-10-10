import OAI.Geometry.Perimeter.Regularity.FlatnessImprovement

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem connected_crosses_frontier {X : Type*} [TopologicalSpace X]
    {S K : Set X} (hS : IsPreconnected S) (hK : IsClosed K)
    {x y : X} (hx : x∈S) (hxK : x∈K) (hy : y∈S) (hyK : y∉K) :
    (S ∩ frontier K).Nonempty := by
  by_contra hn
  have hsub : S ⊆ interior K ∪ Kᶜ := by
    intro z hz
    by_cases hzK : z∈K
    · left
      apply (mem_interior_iff_notMem_frontier hzK).mpr
      intro hzf
      exact hn ⟨z,hz,hzf⟩
    · exact Or.inr hzK
  have hd : Disjoint (interior K) Kᶜ :=
    Set.disjoint_left.mpr fun z hz hzc ↦ hzc (interior_subset hz)
  rcases hS.subset_or_subset isOpen_interior hK.isOpen_compl hd hsub with h | h
  · exact hyK (interior_subset (h hy))
  · exact h hx hxK

theorem FullSlab.lower_phaseSupport {E : Set (Euc n)} {v : Euc n} {R a : ℝ}
    (hs : FullSlab E v R a) (ha : 0≤a) {x : Euc n}
    (hx : x∈Metric.ball 0 R) (hxi : inner ℝ v x < -a) :
    x∈(volume.restrict E).support := by
  let U : Set (Euc n) := Metric.ball 0 R ∩ {z | inner ℝ v z < -a}
  have hU : IsOpen U := Metric.isOpen_ball.inter (isOpen_lt (continuous_const.inner continuous_id) continuous_const)
  have hUE : U ≤ᵐ[volume] E := by
    filter_upwards [hs.2] with z hz
    intro hzU
    have hi : inner ℝ v z < 0 := lt_of_lt_of_le hzU.2 (neg_nonpos.mpr ha)
    apply (hz hzU.1 ?_).mpr hi
    rw [abs_of_neg hi]
    have hzi : inner ℝ v z < -a := hzU.2
    linarith
  apply Measure.support_mono (Measure.restrict_mono_ae hUE)
  apply Measure.interior_inter_support
  exact ⟨hU.interior_eq.symm ▸ ⟨hx,hxi⟩,by rw [Measure.support_eq_univ]; trivial⟩

theorem FullSlab.upper_not_phaseSupport {E : Set (Euc n)} {v : Euc n} {R a : ℝ}
    (hs : FullSlab E v R a) (ha : 0≤a) {x : Euc n}
    (hx : x∈Metric.ball 0 R) (hxi : a < inner ℝ v x) :
    x∉(volume.restrict E).support := by
  let U : Set (Euc n) := Metric.ball 0 R ∩ {z | a < inner ℝ v z}
  have hU : IsOpen U := Metric.isOpen_ball.inter (isOpen_lt continuous_const (continuous_const.inner continuous_id))
  have hUE : ∀ᵐ z ∂volume, z∉U∩E := by
    filter_upwards [hs.2] with z hz
    rintro ⟨hzU,hzE⟩
    have hi : 0 < inner ℝ v z := lt_of_le_of_lt ha hzU.2
    have he := hz hzU.1 (by rw [abs_of_pos hi]; exact hzU.2)
    exact (not_lt_of_ge hi.le) (he.mp hzE)
  have hzero : (volume.restrict E) U=0 := by
    rw [Measure.restrict_apply hU.measurableSet]
    simpa only [not_not, ofPred_mem_eq] using ae_iff.mp hUE
  exact Measure.subset_compl_support_of_isOpen hU hzero ⟨hx,hxi⟩

theorem FullSlab.central_fiber_meets_support (hn : 1<n) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) {v : Euc n} (hv : ‖v‖=1)
    {a : ℝ} (ha : 0≤a) (ha4 : a<1/4) (hs : FullSlab E v 8 a)
    (y : normalPlane v) (hy : ‖y‖<1/4) :
    ∃ t : ℝ, |t|≤a ∧ (y:Euc n)+t•v ∈ perimeterSupport E ∩ Metric.ball 0 1 := by
  let f : ℝ → Euc n := fun t ↦ (y:Euc n)+t•v
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hnorm (t : ℝ) (ht : t∈Icc (-(1/4)) (1/4)) : ‖f t‖<1 := by
    have htn : |t|≤1/4 := abs_le.mpr ht
    have hh := norm_add_le (y:Euc n) (t•v)
    rw [norm_smul,hv,mul_one,Real.norm_eq_abs] at hh
    change ‖(y:Euc n)+t•v‖<1
    change ‖(y:Euc n)‖<1/4 at hy
    linarith
  have hball (t : ℝ) (ht : t∈Icc (-(1/4)) (1/4)) : f t∈Metric.ball 0 8 := by
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hnorm t ht]
  have hleft : f (-(1/4))∈(volume.restrict E).support :=
    hs.lower_phaseSupport ha (hball _ (by norm_num)) (by
      change inner ℝ v ((y:Euc n)+ (-(1/4):ℝ)•v) < -a
      rw [normal_fiber_inner hv]; linarith)
  have hright : f (1/4)∉(volume.restrict E).support :=
    hs.upper_not_phaseSupport ha (hball _ (by norm_num)) (by
      change a < inner ℝ v ((y:Euc n)+(1/4:ℝ)•v)
      rw [normal_fiber_inner hv]; exact ha4)
  obtain ⟨z,⟨t,ht,rfl⟩,hz⟩ := connected_crosses_frontier
    (isPreconnected_Icc.image f hf.continuousOn) Measure.isClosed_support
    (mem_image_of_mem f (by norm_num : (-(1/4):ℝ)∈Icc (-(1/4)) (1/4))) hleft
    (mem_image_of_mem f (by norm_num : (1/4:ℝ)∈Icc (-(1/4)) (1/4))) hright
  rw [minimizing_frontier_phaseSupport
    (Real.HolderConjugate.conjExponent (by exact_mod_cast hn : 1<(n:ℝ))) hmin] at hz
  have hsmall : f t∈Metric.ball 0 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hnorm t ht
  refine ⟨t,?_,hz,hsmall⟩
  have hh := hs.1 (f t) ⟨hz,hball t ht⟩
  simpa only [f,normal_fiber_inner hv] using hh

end RPISingularHarnack

end

end OAI
