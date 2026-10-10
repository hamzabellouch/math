import OAI.Geometry.RCD.Sobolev.HarmonicEnergyTailBound
import OAI.Geometry.RCD.Metric.RescaledBallVolume
import OAI.Geometry.RCD.Sobolev.SobolevLevelChain

namespace OAI

/-! # Uniform local energy estimates throughout an inner ball -/

open Set Metric Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_energy_tail_inner_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (β : ℝ) (hβ : 0<β) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (p : X) (r : ℝ), 0 < r → -1≤K*(5*r)^2 →
      ∀ (f : SobolevSpace (hausdorff n X) hX.quadratic) (L : ℝ≥0),
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (5*r)) f →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (4*r)),
        localGamma (hausdorff n X) hX.quadratic f f x≤(L:ℝ)^2) →
      (∫ x in ball p (4*r), (max (r^2*localGamma (hausdorff n X) hX.quadratic f f x-1) 0)^2
        ∂hausdorff n X)≤δ*(hausdorff n X).real (ball p (5*r)) →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p (3*r)),
        r^2*localGamma (hausdorff n X) hX.quadratic f f x≤1+β := by
  obtain ⟨δ,hδ,hbound⟩ := hX.harmonic_energy_small_tail_bound hn β hβ
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (a:=1) (δ:=1/40)
    zero_le_one (by norm_num) (by norm_num)
  have hD0 : 0<D := zero_lt_one.trans_le hD
  refine ⟨δ/D,div_pos hδ hD0,?_⟩
  intro p r hr hcurv f L hf hgrad hsmall
  let μ := hausdorff n X
  let F := fun x => (max (r^2*localGamma μ hX.quadratic f f x-1) 0)^2
  have : IsFiniteMeasure (μ.restrict (ball p (4*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded _ isBounded_ball⟩
  have henergy : MemLp (fun x => r^2*localGamma μ hX.quadratic f f x) 2
      (μ.restrict (ball p (4*r))) := by
    apply MemLp.of_bound (((localGamma_memL1 μ hX.quadratic f f).aestronglyMeasurable.const_mul (r^2)).restrict)
      (r^2*(L:ℝ)^2)
    filter_upwards [hgrad,ae_restrict_of_ae (localGamma_self μ hX.quadratic f)] with x hx he
    rw [Real.norm_eq_abs,abs_of_nonneg (by rw [he]; positivity)]
    exact mul_le_mul_of_nonneg_left hx (sq_nonneg r)
  have hi : IntegrableOn F (ball p (4*r)) μ :=
    ((upperLevelPart_lipschitz 1).comp_memLp (upperLevelPart_zero zero_le_one) henergy).integrable_sq
  let T := ball p (3*r)
  let V : T → Set X := fun q => ball q.val (r/16)
  have hlocal (q : T) : ∀ᵐ x ∂μ.restrict (V q), r^2*localGamma μ hX.quadratic f f x≤1+β := by
    have hq : dist q.val p<3*r := q.property
    have hsub : ball q.val (8*(r/16))⊆ball p (4*r) :=
      Metric.ball_subset_ball' (by linarith)
    have hsub5 : ball q.val (8*(r/16))⊆ball p (5*r) :=
      Metric.ball_subset_ball' (by linarith)
    have hsub2 : ball q.val (2*(r/16))⊆ball p (4*r) :=
      Metric.ball_subset_ball' (by linarith)
    have hcurv' : -1≤K*(2*(r/16))^2 := by
      by_cases hK : 0≤K
      · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg _))
      · have hs : (2*(r/16))^2≤(5*r)^2 := by nlinarith [sq_nonneg r]
        have hm := mul_le_mul_of_nonpos_left hs (le_of_not_ge hK)
        linarith
    have hmass := hvol p (5*r) (by positivity) hcurv q.val (by linarith)
    have hrad : (1/40:ℝ)*(5*r)=2*(r/16) := by ring
    rw [hrad] at hmass
    have hsmall' : (∫ x in ball q.val (2*(r/16)), F x ∂μ)≤
        δ*μ.real (ball q.val (2*(r/16))) := by
      calc
        _ ≤ ∫ x in ball p (4*r), F x ∂μ :=
          setIntegral_mono_set hi (Filter.Eventually.of_forall (fun x => sq_nonneg _)) (Filter.Eventually.of_forall hsub2)
        _ ≤ (δ/D)*μ.real (ball p (5*r)) := hsmall
        _ ≤ (δ/D)*(D*μ.real (ball q.val (2*(r/16)))) :=
          mul_le_mul_of_nonneg_left hmass (div_nonneg hδ.le hD0.le)
        _ = _ := by field_simp
    exact hbound q.val (r/16) (r^2) (by positivity) (sq_nonneg _) hcurv' f L
      (hf.mono μ hX.quadratic hsub5)
      (ae_restrict_of_ae_restrict_of_subset hsub hgrad) hsmall'
  let := hX.separable
  obtain ⟨s,hs,hcover⟩ := (HereditarilyLindelofSpace.isLindelof T).elim_countable_subcover
    V (fun _ => isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (by positivity)⟩)
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_restrict_biUnion_iff V hs _).mpr (fun q _ => hlocal q))

end RegularPointCoordinates

end

end OAI
