import OAI.Analysis.CircleDomains.Selection.RegularLevelLeastPeriod
import OAI.Analysis.CircleDomains.Topology.PeriodicCircleDescent

namespace OAI

/-! Actual smooth embedded circles parametrizing the components of a
compact regular planar level. The parametrization comes from its tangent flow. -/
open Set Function
open scoped Topology Manifold ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma CompactRegularLevelFlow.exists_regular_period_one {f : ℂ → ℝ} {a : ℝ}
    (F : CompactRegularLevelFlow f a) (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact {z | f z = a}) (x : {z // f z = a}) :
    ∃ σ : ℝ → ℂ, ContDiff ℝ ∞ σ ∧ Periodic σ 1 ∧ InjOn σ (Ico 0 1) ∧
      (∀ t, deriv σ t ≠ 0) ∧ range σ = Subtype.val '' connectedComponent x := by
  obtain ⟨p,hp⟩ := F.exists_least_positive_period hf ha hc x
  have hp0 : 0 < p := hp.1.2
  have hper := F.periodic_of_return x hp.1.1
  let σ : ℝ → ℂ := fun t => F.trajectory x (p*t)
  have hσ : ContDiff ℝ ∞ σ := (F.trajectory_smooth x).comp (contDiff_const.mul contDiff_id)
  refine ⟨σ,hσ,?_,?_,?_,?_⟩
  · intro t
    dsimp [σ]
    convert hper (p*t) using 1
    congr 1
    ring
  · intro s hs t ht hst
    have he := F.injOn_fundamental_interval x hp
      (show p*s ∈ Ico 0 p from ⟨mul_nonneg hp0.le hs.1, mul_lt_of_lt_one_right hp0 hs.2⟩)
      (show p*t ∈ Ico 0 p from ⟨mul_nonneg hp0.le ht.1, mul_lt_of_lt_one_right hp0 ht.2⟩) hst
    exact (mul_left_cancel₀ hp0.ne' he)
  · intro t
    have hm : HasDerivAt (fun u : ℝ => p*u) p t := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul p
    have hd : HasDerivAt σ (p • F.field (F.trajectory x (p*t))) t :=
      (F.equation x (p*t)).scomp t hm
    rw [hd.deriv]
    apply smul_ne_zero hp0.ne'
    simpa only [(F.equation x (p*t)).deriv] using F.regular x (p*t)
  · have hr : range σ = range (F.trajectory x) := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨p*t,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨t/p,?_⟩
        dsimp [σ]
        rw [mul_div_cancel₀ _ hp0.ne']
    rw [hr, ← F.range_levelTrajectory_eq_component hf ha x]
    exact (range_comp Subtype.val (F.levelTrajectory x))

lemma exists_smooth_circle_of_compact_regular_level {f : ℂ → ℝ} {a : ℝ}
    (hf : ContDiff ℝ ∞ f) (ha : IsPlanarRegularValue f a)
    (hc : IsCompact {z | f z = a}) (x : {z // f z = a}) :
    ∃ g : Circle → ℂ, ContMDiff (𝓡 1) (𝓘(ℝ,ℂ)) ∞ g ∧ Topology.IsEmbedding g ∧
      range g = Subtype.val '' connectedComponent x := by
  obtain ⟨F⟩ := exists_compact_regular_level_flow hf ha hc
  obtain ⟨σ,hs,hp,hi,_,hr⟩ := F.exists_regular_period_one hf ha hc x
  refine ⟨periodicCircleDescent hp,periodicCircleDescent_smooth hp hs,?_,?_⟩
  · exact ((periodicCircleDescent_smooth hp hs).continuous.isClosedEmbedding
      (periodicCircleDescent_injective hp hi)).isEmbedding
  · exact (periodicCircleDescent_range hp).trans hr

end CircleDomainRigidity

end

end OAI
