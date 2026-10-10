import OAI.Geometry.RCD.Sobolev.HarmonicEnergyTailBound
import OAI.Geometry.RCD.Sobolev.BoundedPositiveTail
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Sharp inner gradients from the actual outer L1 energy error -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_unit_tail_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (β : ℝ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (r : ℝ), 0 < r → -1 ≤ K*(2*r)^2 →
      ∀ (f : SobolevSpace (hausdorff n X) hX.quadratic) (L : ℝ≥0),
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (2*r)) f →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (2*r)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ (L : ℝ)^2) →
      (∫ x in ball p (2*r), (max (localGamma (hausdorff n X) hX.quadratic f f x-1) 0)^2
        ∂hausdorff n X) ≤ δ*(hausdorff n X).real (ball p (2*r)) →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p r),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ 1+β := by
  obtain ⟨δ,hδ,hbound⟩ := hX.harmonic_energy_small_tail_bound hn β hβ
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (a:=1) (δ:=1/16)
    zero_le_one (by norm_num) (by norm_num)
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  refine ⟨δ/D,div_pos hδ hD0,?_⟩
  intro p r hr hcurv f L hf hgrad hsmall
  let μ := hausdorff n X
  let F := fun x => (max (localGamma μ hX.quadratic f f x-1) 0)^2
  have hfin : μ (ball p (2*r)) ≠ ⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hi := ((localGamma_memL1 μ hX.quadratic f f).integrableOn.sub
    (integrableOn_const hfin : IntegrableOn (fun _ : X => (1 : ℝ)) (ball p (2*r)) μ)).abs
  have hF : IntegrableOn F (ball p (2*r)) μ := by
    apply ((hi.const_mul ((L : ℝ)^2)).mono'
      (((localGamma_memL1 μ hX.quadratic f f).aestronglyMeasurable.restrict.sub
        aestronglyMeasurable_const).sup aestronglyMeasurable_const |>.pow 2))
    filter_upwards [hgrad] with x hx
    change |(max (localGamma μ hX.quadratic f f x-1) 0)^2| ≤
      (L : ℝ)^2*|localGamma μ hX.quadratic f f x-1|
    simpa only [Real.norm_eq_abs,abs_sq] using
      bounded_positive_tail_pointwise (sq_nonneg (L : ℝ)) hx
  let T := ball p r
  let V : T → Set X := fun q => ball q.val (r/16)
  have hlocal (q : T) : ∀ᵐ x ∂μ.restrict (V q), localGamma μ hX.quadratic f f x ≤ 1+β := by
    have hq : dist q.val p < r := q.property
    have hsub : ball q.val (8*(r/16)) ⊆ ball p (2*r) :=
      Metric.ball_subset_ball' (by linarith)
    have hsub2 : ball q.val (2*(r/16)) ⊆ ball p (2*r) :=
      Metric.ball_subset_ball' (by linarith)
    have hcurv' : -1 ≤ K*(2*(r/16))^2 := by
      by_cases hK : 0 ≤ K
      · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (mul_nonneg hK (sq_nonneg _))
      · have hs : (2*(r/16))^2 ≤ (2*r)^2 := by nlinarith [sq_nonneg r]
        have hm := mul_le_mul_of_nonpos_left hs (le_of_not_ge hK)
        linarith
    have hmass := hvol p (2*r) (by positivity) hcurv q.val (by linarith)
    have hrad : (1/16 : ℝ)*(2*r) = 2*(r/16) := by ring
    rw [hrad] at hmass
    have hsmall' : (∫ x in ball q.val (2*(r/16)), F x ∂μ) ≤
        δ*μ.real (ball q.val (2*(r/16))) := by
      calc
        _ ≤ ∫ x in ball p (2*r), F x ∂μ :=
          setIntegral_mono_set hF (Filter.Eventually.of_forall (fun x => sq_nonneg _))
            (Filter.Eventually.of_forall hsub2)
        _ ≤ (δ/D)*μ.real (ball p (2*r)) := hsmall
        _ ≤ (δ/D)*(D*μ.real (ball q.val (2*(r/16)))) :=
          mul_le_mul_of_nonneg_left hmass (div_nonneg hδ.le hD0.le)
        _ = _ := by field_simp
    simpa only [one_mul] using hbound q.val (r/16) 1 (by positivity) zero_le_one hcurv' f L
      (hf.mono μ hX.quadratic hsub)
      (ae_restrict_of_ae_restrict_of_subset hsub hgrad)
      (by simpa only [one_mul,F] using hsmall')
  let := hX.separable
  obtain ⟨s,hs,hcover⟩ := (HereditarilyLindelofSpace.isLindelof T).elim_countable_subcover
    V (fun _ => isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (by positivity)⟩)
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_restrict_biUnion_iff V hs _).mpr (fun q _ => hlocal q))

theorem NoncollapsedRCD.harmonic_l1_gradient_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (β B : ℝ) (hβ : 0 < β) (hB : 0 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (p : X) (r : ℝ), 0 < r → -1 ≤ K*(2*r)^2 →
      ∀ f : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (2*r)) f →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (2*r)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ B) →
      ((hausdorff n X).real (ball p (2*r)))⁻¹*(∫ x in ball p (2*r),
        |localGamma (hausdorff n X) hX.quadratic f f x-1| ∂hausdorff n X) ≤ ε →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p r),
        localGamma (hausdorff n X) hX.quadratic f f x ≤ 1+β := by
  obtain ⟨δ,hδ,hbound⟩ := hX.harmonic_unit_tail_bound hn β hβ
  refine ⟨δ/(B+1),div_pos hδ (by positivity),?_⟩
  intro p r hr hcurv f hh hg he
  let μ := hausdorff n X
  have hf : μ (ball p (2*r)) ≠ ⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hm : 0 < μ.real (ball p (2*r)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (by positivity)).ne' hf
  have hi := ((localGamma_memL1 μ hX.quadratic f f).integrableOn.sub
    (integrableOn_const hf : IntegrableOn (fun _ : X => (1 : ℝ)) (ball p (2*r)) μ)).abs
  have hb := bounded_positive_tail_integral μ (ball p (2*r)) hB
    (localGamma_memL1 μ hX.quadratic f f).aestronglyMeasurable.restrict hi hg
  have hraw : (∫ x in ball p (2*r), |localGamma μ hX.quadratic f f x-1| ∂μ) ≤
      (δ/(B+1))*μ.real (ball p (2*r)) := by
    apply (div_le_iff₀ hm).mp
    simpa only [div_eq_inv_mul] using he
  have hcoef : B*(δ/(B+1)) ≤ δ := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (show 0 < B+1 by positivity)).mpr (by nlinarith)
  apply hbound p r hr hcurv f ⟨Real.sqrt B,Real.sqrt_nonneg B⟩ hh
    (by
      change ∀ᵐ x ∂μ.restrict (ball p (2*r)),
        localGamma μ hX.quadratic f f x ≤ (Real.sqrt B)^2
      simpa only [Real.sq_sqrt hB] using hg)
  calc
    _ ≤ B*(∫ x in ball p (2*r), |localGamma μ hX.quadratic f f x-1| ∂μ) := hb
    _ ≤ B*((δ/(B+1))*μ.real (ball p (2*r))) := mul_le_mul_of_nonneg_left hraw hB
    _ ≤ δ*μ.real (ball p (2*r)) := by
      nlinarith [mul_le_mul_of_nonneg_right hcoef hm.le]

end RegularPointCoordinates

end

end OAI
