import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyMinimal
import OAI.Geometry.WeakHessian.Sobolev.UpperGradientNormTendsto
import OAI.Geometry.WeakHessian.Sobolev.AddConst
import OAI.Geometry.WeakHessian.Sobolev.LocalSobolevLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile6
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

def rootClip (B : ℝ) (r : ℝ) : ℝ := max 0 (min B r)
lemma rootClip_lipschitz (B : ℝ) : LipschitzWith 1 (rootClip B) :=
  (LipschitzWith.const_min LipschitzWith.id B).const_max 0
lemma rootClip_zero {B : ℝ} (hB : 0 ≤ B) : rootClip B 0 = 0 := by simp [rootClip,hB]
lemma rootClip_nonneg (B r : ℝ) : 0 ≤ rootClip B r := le_max_left _ _
lemma rootClip_le {B : ℝ} (hB : 0 ≤ B) (r : ℝ) : rootClip B r ≤ B :=
  max_le hB (min_le_left _ _)
lemma rootClip_eq {B r : ℝ} (hr : 0 ≤ r) (hB : r ≤ B) : rootClip B r = r := by
  simp only [rootClip,min_eq_right hB,max_eq_right hr]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma exists_clipped_cutoff_approx (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) {B : ℝ} (hB : 0 ≤ B)
    (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (henergy : cheegerEnergy m w = ENNReal.ofReal (‖hw.2.2.toLp (weakGradient m w)‖^2/2))
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχn : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (_hχc : HasCompactSupport χ)
    (hwχ : ∀ᵐ x ∂m, w x*χ x = w x)
    (hDχ : ∀ᵐ x ∂m, weakGradient m w x*χ x = weakGradient m w x)
    (hwD : ∀ᵐ x ∂m, w x*weakGradient m χ x = 0) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      (∀ n x, 0 ≤ fs n x ∧ fs n x ≤ B) ∧
      (∀ n, tsupport (fs n) ⊆ tsupport χ) ∧
      ∃ hfs : ∀ n, MemLp (fs n) 2 m,
      ∃ Ds : ℕ → X → ℝ, ∃ hDs : ∀ n, MemLp (Ds n) 2 m,
        (∀ n, IsLocalWeakUpperGradient m (fs n) (Ds n)) ∧
        Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.1.toLp w)) ∧
        Tendsto (fun n => (hDs n).toLp (Ds n)) atTop
          (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  let W := hw.1.toLp w
  let D := hw.2.2.toLp (weakGradient m w)
  have hD : IsMinimalLocalWeakUpperGradient m (W: X → ℝ) D :=
    (weakGradient_isMinimal hw.2.1.2).congr_ae hw.1.coeFn_toLp.symm hw.2.2.coeFn_toLp.symm
  have he : cheegerEnergy m (W: X → ℝ) = ENNReal.ofReal (‖D‖^2/2) := by
    rw [cheegerEnergy_congr_ae hw.1.coeFn_toLp]
    exact henergy
  obtain ⟨gs,hgLip,hgs,hsl,hg,hs⟩ := exists_lipschitz_strong_slopes hfin hD he
  let cs (n : ℕ) := rootClip B ∘ gs n
  let hc (n : ℕ) : MemLp (cs n) 2 m := (rootClip_lipschitz B).comp_memLp (rootClip_zero hB) (hgs n)
  have hcLip (n : ℕ) : GloballyLipschitz (cs n) := ⟨_,(rootClip_lipschitz B).comp (hgLip n).choose_spec⟩
  have hcn (n : ℕ) (x : X) : 0 ≤ cs n x := rootClip_nonneg _ _
  have hcB (n : ℕ) (x : X) : |cs n x| ≤ B := by
    rw [abs_of_nonneg (hcn n x)]; exact rootClip_le hB _
  have hcW : (rootClip_lipschitz B).compLp (rootClip_zero hB) W = W := by
    apply Lp.ext
    filter_upwards [(rootClip_lipschitz B).coeFn_compLp (rootClip_zero hB) W,
      hw.1.coeFn_toLp,hwn,hwB] with x hx hwx hn hb
    rw [hx]
    change rootClip B (W x) = W x
    change W x = w x at hwx
    rw [hwx,rootClip_eq hn hb]
  have hcs : Tendsto (fun n => (hc n).toLp (cs n)) atTop (𝓝 W) := by
    have H := ((rootClip_lipschitz B).continuous_compLp (rootClip_zero hB)).tendsto W |>.comp hg
    rw [hcW] at H
    convert H using 1
    funext n
    apply Lp.ext
    filter_upwards [(hc n).coeFn_toLp,
      (rootClip_lipschitz B).coeFn_compLp (rootClip_zero hB) ((hgs n).toLp (gs n)),
      (hgs n).coeFn_toLp] with x h1 h2 h3
    simp only [h1,h2,Function.comp_apply,h3,cs]
  let hχS := localSobolev_of_lipschitz hfin hχ
  have hχB : ∀ᵐ x ∂m, |χ x| ≤ 1 := ae_of_all _ fun x => by rw [abs_of_nonneg (hχn x)]; exact hχ1 x
  have hχDB : ∀ᵐ x ∂m, |weakGradient m χ x| ≤ (L:ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) χ,weakGradient_le_lipschitz hfin hχ] with x hx hy
    rwa [abs_of_nonneg hx]
  let A := boundedMulLp hχ.continuous.aestronglyMeasurable hχB
  let T := boundedMulLp (weakGradient_isMinimal hχS.2).1.1.aestronglyMeasurable hχDB
  have hAW : A W = W := by
    apply Lp.ext
    filter_upwards [boundedMulLp_ae hχ.continuous.aestronglyMeasurable hχB W,hw.1.coeFn_toLp,hwχ] with x hx hy hz
    change A W x = W x
    change A W x = W x*χ x at hx
    change W x = w x at hy
    rw [hx,hy,hz]
  have hAD : A D = D := by
    apply Lp.ext
    filter_upwards [boundedMulLp_ae hχ.continuous.aestronglyMeasurable hχB D,hw.2.2.coeFn_toLp,hDχ] with x hx hy hz
    change A D x = D x
    change A D x = D x*χ x at hx
    change D x = weakGradient m w x at hy
    rw [hx,hy,hz]
  have hTW : T W = 0 := by
    apply Lp.ext
    filter_upwards [boundedMulLp_ae (weakGradient_isMinimal hχS.2).1.1.aestronglyMeasurable hχDB W,
      hw.1.coeFn_toLp,hwD,Lp.coeFn_zero (α := X) (E := ℝ) (p := 2) (μ := m)] with x hx hy hz hzero
    change T W x = (0 : Lp ℝ 2 m) x
    change T W x = W x*weakGradient m χ x at hx
    change W x = w x at hy
    rw [hx,hy,hz,hzero]
    rfl
  let fs (n : ℕ) (x : X) := cs n x*χ x
  let hfs (n : ℕ) : MemLp (fs n) 2 m := memLp_mul_bounded (hc n) hχ.continuous.aestronglyMeasurable hχB
  let Ds (n : ℕ) (x : X) := χ x*(localSlope (gs n) x).toReal+cs n x*weakGradient m χ x
  let hDs (n : ℕ) : MemLp (Ds n) 2 m := by
    apply (show MemLp (fun x => χ x*(localSlope (gs n) x).toReal) 2 m from by
      simpa only [mul_comm] using memLp_mul_bounded (hsl n) hχ.continuous.aestronglyMeasurable hχB).add
      (memLp_mul_bounded (hc n) (weakGradient_isMinimal hχS.2).1.1.aestronglyMeasurable hχDB)
  refine ⟨fs,fun n => ⟨_,lipschitz_mul_bounded (hcLip n).choose_spec hχ (hcB n)
    (fun x => by rw [abs_of_nonneg (hχn x)]; exact hχ1 x)⟩,
    fun n x => ⟨mul_nonneg (hcn n x) (hχn x),?_⟩,?_,hfs,Ds,hDs,?_,?_,?_⟩
  · exact (mul_le_of_le_one_right (hcn n x) (hχ1 x)).trans (rootClip_le hB _)
  · intro n
    exact tsupport_mul_subset_right
  · intro n
    have H := ((localSlope_isLocalWeakUpperGradient hfin (hgLip n).choose_spec).normalContraction
      (rootClip_lipschitz B)).mul_bounded (weakGradient_isMinimal hχS.2).1
      (fun o R _hR => (hc n).restrict _) hχ.continuous.measurable.aemeasurable hχB hχDB
    convert H using 1
    funext x
    simp only [Ds,abs_of_nonneg (hχn x),abs_of_nonneg (hcn n x),cs]
  · have H := A.continuous.tendsto W |>.comp hcs
    rw [hAW] at H
    convert H using 1
    funext n
    apply Lp.ext
    filter_upwards [(hfs n).coeFn_toLp,boundedMulLp_ae hχ.continuous.aestronglyMeasurable hχB ((hc n).toLp (cs n)),
      (hc n).coeFn_toLp] with x hx hy hz
    change (A ((hc n).toLp (cs n))) x = _ at hy
    simp only [Function.comp_apply,hx,hy,hz,fs]
  · have H := (A.continuous.tendsto D |>.comp hs).add (T.continuous.tendsto W |>.comp hcs)
    rw [hAD,hTW,add_zero] at H
    convert H using 1
    funext n
    apply Lp.ext
    filter_upwards [(hDs n).coeFn_toLp,Lp.coeFn_add (A ((hsl n).toLp _)) (T ((hc n).toLp _)),
      boundedMulLp_ae hχ.continuous.aestronglyMeasurable hχB ((hsl n).toLp _),
      boundedMulLp_ae (weakGradient_isMinimal hχS.2).1.1.aestronglyMeasurable hχDB ((hc n).toLp _),
      (hsl n).coeFn_toLp,(hc n).coeFn_toLp] with x hx hy h1 h2 h3 h4
    change (A ((hsl n).toLp _)) x = _ at h1
    change (T ((hc n).toLp _)) x = _ at h2
    simp only [Function.comp_apply,hx,hy,Pi.add_apply,h1,h2,h3,h4,Ds,mul_comm]

section

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

def rootCutoff (o : X) (R : ℝ) (x : X) : ℝ := rootClip 1 (R+2-dist x o)
lemma rootCutoff_lipschitz (o : X) (R : ℝ) : LipschitzWith 1 (rootCutoff o R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (rootCutoff o R x) (rootCutoff o R y) ≤
        dist (R+2-dist x o) (R+2-dist y o) := by
      simpa only [NNReal.coe_one,one_mul,rootCutoff] using
        (rootClip_lipschitz 1).dist_le_mul (R+2-dist x o) (R+2-dist y o)
    _ = dist (dist x o) (dist y o) := dist_sub_left _ _ _
    _ ≤ 1*dist x y := by simpa using dist_dist_dist_le_left x y o

lemma rootCutoff_nonneg (o : X) (R : ℝ) (x : X) : 0 ≤ rootCutoff o R x := rootClip_nonneg _ _
lemma rootCutoff_le_one (o : X) (R : ℝ) (x : X) : rootCutoff o R x ≤ 1 := rootClip_le zero_le_one _
lemma rootCutoff_one {o : X} {R : ℝ} {x : X} (hx : x ∈ Metric.closedBall o R) :
    rootCutoff o R x = 1 := by
  have H : dist x o ≤ R := hx
  simp only [rootCutoff,rootClip,min_eq_left (by linarith : 1 ≤ R+2-dist x o),max_eq_right zero_le_one]
lemma rootCutoff_support (o : X) (R : ℝ) : tsupport (rootCutoff o R) ⊆ Metric.closedBall o (R+2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  have H : R+2 < dist x o := lt_of_not_ge hh
  have he : rootCutoff o R x = 0 := by
    apply max_eq_left
    exact (min_le_right _ _).trans (by linarith)
  exact hx he

end

lemma cutoff_gradient_identities (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : LocalSobolev m w) {Q : Set X} (hQ : MeasurableSet Q)
    (hws : ∀ᵐ x ∂m, x ∉ Q → w x = 0)
    {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχeq : ∀ x ∈ Q, χ x = 1) :
    (∀ᵐ x ∂m, w x*χ x = w x) ∧
    (∀ᵐ x ∂m, weakGradient m w x*χ x = weakGradient m w x) ∧
    (∀ᵐ x ∂m, w x*weakGradient m χ x = 0) := by
  have hzero : LocalSobolev m (fun _ : X => (0:ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero,_,isMinimalLocalWeakUpperGradient_const 0⟩
  have hone : LocalSobolev m (fun _ : X => (1:ℝ)) := by simpa only [zero_add] using hzero.add_const hfin 1
  have hDz := weakGradient_locality hw hzero hQ.compl hws
  have hDc := weakGradient_locality (localSobolev_of_lipschitz hfin hχ) hone hQ (ae_of_all _ hχeq)
  refine ⟨?_,?_,?_⟩
  · filter_upwards [hws] with x hx
    by_cases h : x ∈ Q
    · rw [hχeq x h,mul_one]
    · rw [hx h,zero_mul]
  · filter_upwards [hDz,weakGradient_const (m := m) 0] with x hx hz
    by_cases h : x ∈ Q
    · rw [hχeq x h,mul_one]
    · rw [hx h,hz,zero_mul]
  · filter_upwards [hws,hDc,weakGradient_const (m := m) 1] with x hwx hx hz
    by_cases h : x ∈ Q
    · rw [hx h,hz,mul_zero]
    · rw [hwx h,zero_mul]

variable [ProperSpace X]

theorem CurvatureDimension.compact_root_approximation {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) {B : ℝ} (hB : 0 ≤ B)
    (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (o : X) (R : ℝ≥0) (hws : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → w x = 0) :
    ∃ fs : ℕ → X → ℝ, (∀ n, GloballyLipschitz (fs n)) ∧
      (∀ n x, 0 ≤ fs n x ∧ fs n x ≤ B) ∧
      (∀ n, tsupport (fs n) ⊆ Metric.closedBall o ((R:ℝ)+2)) ∧
      ∃ hfs : ∀ n, MemLp (fs n) 2 m,
      ∃ Ds : ℕ → X → ℝ, ∃ hDs : ∀ n, MemLp (Ds n) 2 m,
        (∀ n, IsLocalWeakUpperGradient m (fs n) (Ds n)) ∧
        Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.1.toLp w)) ∧
        Tendsto (fun n => (hDs n).toLp (Ds n)) atTop
          (𝓝 (hw.2.2.toLp (weakGradient m w))) := by
  obtain ⟨hwχ,hDχ,hwD⟩ := cutoff_gradient_identities hfin hw.2.1 measurableSet_closedBall hws
    (rootCutoff_lipschitz o R) (fun x hx => rootCutoff_one hx)
  obtain ⟨fs,hLip,hBnd,hs,hfs,Ds,hDs,hUG,hfsT,hDsT⟩ := exists_clipped_cutoff_approx hfin hw hB hwn hwB
    (hcd.global_cheegerEnergy_eq_weakGradient hfin o hw)
    (rootCutoff_lipschitz o R) (rootCutoff_nonneg o R) (rootCutoff_le_one o R)
    (isCompact_closedBall o ((R:ℝ)+2) |>.of_isClosed_subset (isClosed_tsupport _) (rootCutoff_support o R))
    hwχ hDχ hwD
  exact ⟨fs,hLip,hBnd,fun n => (hs n).trans (rootCutoff_support o R),hfs,Ds,hDs,hUG,hfsT,hDsT⟩
end WeakHessian

end
end InlinedFile6

end OAI
