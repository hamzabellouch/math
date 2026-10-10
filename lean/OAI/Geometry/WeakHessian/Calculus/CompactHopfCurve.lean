import Mathlib
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMapLipschitz
import OAI.Geometry.WeakHessian.Calculus.CompactHopf

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma compactHopf_uniform_data (_hfin : FiniteOnBoundedSets m) (f : X →ᵇ ℝ)
    (o : X) (hf : HasCompactSupport (f : X → ℝ)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ (R : ℝ) (L : ℝ≥0), 0 < R ∧ ∀ t ∈ Icc a b,
      tsupport (boundedHopfMap f t : X → ℝ) ⊆ Metric.closedBall o R ∧
      LipschitzWith L (boundedHopfMap f t : X → ℝ) := by
  obtain ⟨R,hR,hsub⟩ := hf.isCompact.isBounded.subset_closedBall_lt 0 o
  have hb : 0 < b := ha.trans_le hab
  let D := Real.sqrt (4*b*‖f‖)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hDs : D^2 = 4*b*‖f‖ := Real.sq_sqrt (by positivity)
  let L : ℝ≥0 := ⟨D/a+1/(2*a)+2*‖f‖,by positivity⟩
  refine ⟨R+b+‖f‖+1,L,by positivity,?_⟩
  intro t ht
  have ht0 := ha.trans_le ht.1
  constructor
  · apply closure_minimal _ Metric.isClosed_closedBall
    exact (boundedHopfMap_support_bound f o hR.le ((subset_tsupport f).trans hsub) ht0).trans
      (Metric.closedBall_subset_closedBall (by linarith [ht.2]))
  · have H := hopfLax_lipschitz_radius f.continuous
      (fun x => (boundedContinuous_bounds f x).1) (fun x => (boundedContinuous_bounds f x).2)
      (by linarith [norm_nonneg f]) ht0 hD (by rw [hDs]; nlinarith [norm_nonneg f,ht.2])
    have hL : (⟨D/t+1/(2*t)+(‖f‖-(-‖f‖)),by simp only [sub_neg_eq_add]; positivity⟩ : ℝ≥0) ≤ L := by
      change D/t+1/(2*t)+(‖f‖-(-‖f‖)) ≤ D/a+1/(2*a)+2*‖f‖
      have h1 := div_le_div_of_nonneg_left hD ha ht.1
      have h2 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
        (by positivity : 0 < 2*a) (by linarith [ht.1] : 2*a ≤ 2*t)
      linarith
    convert! H.weaken hL using 1
    funext x
    exact boundedHopfMap_apply_pos f ht0 x

omit [SigmaFinite m] in
lemma compactHopf_exists_L2_curve (hfin : FiniteOnBoundedSets m) (f : X →ᵇ ℝ)
    (o : X) (hf : HasCompactSupport (f : X → ℝ)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ (W : ℝ → Lp ℝ 2 m) (D : ℝ),
      (∀ t, 0 < t → W t =ᵐ[m] boundedHopfMap f t) ∧
      ContinuousOn W (Icc a b) ∧
      (∀ t, 0 < t → Sobolev m (W t : X → ℝ)) ∧
      (∀ t, 0 < t → MemLp (fun x => (weakGradient m (W t) x)^2) 2 m) ∧
      (∀ t ∈ Icc a b, (∫ x, (weakGradient m (W t) x)^2 ∂m) ≤ D) ∧
      (∀ r s, 0 < r → r ≤ s → ∀ᵐ x ∂m,
        W s x-W r x ≤ (-(s-r)*r/(2*s))*(weakGradient m (W r) x)^2) := by
  let W : ℝ → Lp ℝ 2 m := fun t => if ht : 0 < t then
    (boundedHopfMap_memLp_compact hfin f o hf ht).toLp (boundedHopfMap f t) else 0
  have he (t : ℝ) (ht : 0 < t) : W t =ᵐ[m] boundedHopfMap f t := by
    dsimp only [W]; rw [dite_eq_left ht]; exact MemLp.coeFn_toLp _
  have hSob (t : ℝ) (ht : 0 < t) : Sobolev m (W t : X → ℝ) :=
    (sobolev_congr_ae (he t ht)).mpr (sobolev_of_lipschitz_compactSupport hfin
      (boundedHopfMap_lipschitz f ht).choose_spec (boundedHopfMap_compactSupport f o hf ht))
  have hg2 (t : ℝ) (ht : 0 < t) : MemLp (fun x => (weakGradient m (W t) x)^2) 2 m := by
    obtain ⟨L,hL⟩ := boundedHopfMap_lipschitz f ht
    have hbb : ∀ᵐ x ∂m, |weakGradient m (W t) x| ≤ (L:ℝ) := by
      filter_upwards [weakGradient_congr_ae (he t ht),weakGradient_le_lipschitz hfin hL,
        weakGradient_nonneg (m := m) (W t)] with x hx hb hn
      rw [abs_of_nonneg hn,hx]; exact hb
    simpa only [sq] using
      memLp_mul_bounded (hSob t ht).2.2 (hSob t ht).2.2.aestronglyMeasurable hbb
  obtain ⟨R,L,_,hRL⟩ := compactHopf_uniform_data hfin f o hf ha hab
  let Q := Metric.closedBall o R
  have hQ : MeasurableSet Q := measurableSet_closedBall
  have hQfin : m Q < ∞ := hfin _ Metric.isBounded_closedBall
  let hi := memLp_indicator_const (μ := m) 2 hQ (1:ℝ) (Or.inr hQfin.ne)
  let χ : Lp ℝ 2 m := hi.toLp (Q.indicator (fun _ => (1:ℝ)))
  have hχe : χ =ᵐ[m] Q.indicator (fun _ => (1:ℝ)) := hi.coeFn_toLp
  have hLip : LipschitzOnWith ⟨(2*‖f‖/a)*‖χ‖,by positivity⟩ W (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs
    rw [dist_eq_norm]
    calc
      ‖W t-W s‖ ≤ ‖((2*‖f‖/a)*dist t s) • χ‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [Lp.coeFn_sub (W t) (W s),Lp.coeFn_smul ((2*‖f‖/a)*dist t s) χ,
          he t (ha.trans_le ht.1),he s (ha.trans_le hs.1),hχe] with x hd hm het hes hc
        simp only [hd,hm,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,het,hes,hc]
        by_cases hx : x ∈ Q
        · rw [indicator_of_mem hx,mul_one]
          rw [Real.norm_eq_abs (r := (2*‖f‖/a)*dist t s),abs_of_nonneg (by positivity)]
          exact ((BoundedContinuousFunction.dist_coe_le_dist (f := boundedHopfMap f t)
            (g := boundedHopfMap f s) x).trans
            ((boundedHopfMap_time_lipschitz f ha).dist_le_mul _ ht.1 _ hs.1))
        · rw [indicator_of_notMem hx,mul_zero,norm_zero,
            image_eq_zero_of_notMem_tsupport (fun hh => hx ((hRL t ht).1 hh)),
            image_eq_zero_of_notMem_tsupport (fun hh => hx ((hRL s hs).1 hh)),sub_self,norm_zero]
      _ = ((2*‖f‖/a)*‖χ‖)*dist t s := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        ring
  let D := ∫ x, Q.indicator (fun _ => (L:ℝ)^2) x ∂m
  refine ⟨W,D,he,hLip.continuousOn,hSob,hg2,?_,?_⟩
  · intro t ht
    apply integral_mono_ae (hSob t (ha.trans_le ht.1)).2.2.integrable_sq
      ((integrableOn_const (C := (L:ℝ)^2) hQfin.ne).integrable_indicator hQ)
    have hQS := sobolev_of_lipschitz_compactSupport hfin (hRL t ht).2
      (boundedHopfMap_compactSupport f o hf (ha.trans_le ht.1))
    filter_upwards [weakGradient_congr_ae (he t (ha.trans_le ht.1)),
      weakGradient_le_lipschitz hfin (hRL t ht).2,
      weakGradient_nonneg (m := m) (boundedHopfMap f t),weakGradient_zero_off_support hQS.2.1]
      with x hx hB hn hz
    rw [hx]
    by_cases hmem : x ∈ Q
    · rw [indicator_of_mem hmem]
      exact (sq_le_sq₀ hn L.coe_nonneg).mpr hB
    · rw [indicator_of_notMem hmem,hz (fun hh => hmem ((hRL t ht).1 hh)),sq]
      norm_num
  · intro r s hr hrs
    obtain ⟨L,hL⟩ := boundedHopfMap_lipschitz f hr
    have hsl := weakGradient_le_localSlope hfin hL
    have hfunc : (boundedHopfMap f r : X → ℝ) = hopfLax f r := funext (boundedHopfMap_apply_pos f hr)
    filter_upwards [he s (hr.trans_le hrs),he r hr,weakGradient_congr_ae (he r hr),
      hsl,weakGradient_nonneg (m := m) (boundedHopfMap f r)] with x hes her hge hg hn
    rw [hes,her,hge,boundedHopfMap_apply_pos f (hr.trans_le hrs),boundedHopfMap_apply_pos f hr]
    have H := hopf_forward_increment f.continuous (fun x => (boundedContinuous_bounds f x).1)
      (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) hr hrs x
    apply H.trans
    have hcoeff : -(s-r)*r/(2*s) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith
    rw [hfunc] at hg hn ⊢
    exact mul_le_mul_of_nonpos_left ((sq_le_sq₀ hn ENNReal.toReal_nonneg).mpr hg) hcoeff

end WeakHessianTransport

end
end

end OAI
