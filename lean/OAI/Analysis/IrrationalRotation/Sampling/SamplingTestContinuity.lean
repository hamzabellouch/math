import OAI.Analysis.IrrationalRotation.Model.SamplingTests
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingContinuity
import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingLp
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Invariant233.SamplingTests

lemma measurable_kernel (endpoint : Bool) (m : ℕ) :
    Measurable (fun p : ℝ × ℝ => kernel endpoint m p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => CircleParameterData.delta p.1) :=
    (measurable_fract.comp measurable_fst).min
      (measurable_const.sub (measurable_fract.comp measurable_fst))
  have hk : Measurable (fun p : ℝ × ℝ => CircleParameterData.kernel m p.1 p.2) := by
    unfold CircleParameterData.kernel
    apply Measurable.ite
    · exact (measurableSet_le measurable_const hd).inter
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd (measurable_const.mul hd)))
    · exact measurable_const.div (measurable_const.mul hd)
    · exact measurable_const
  cases endpoint
  · exact hk.comp (measurable_fst.prodMk (measurable_fract.comp measurable_snd))
  · exact hk.comp ((measurable_fst.sub (measurable_fract.comp measurable_snd)).prodMk
      (measurable_fract.comp measurable_snd))

lemma measurable_circleKernel (endpoint : Bool) (m : ℕ) :
    Measurable (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2) :=
  (measurable_kernel endpoint m).comp
    ((CircleParameterData.measurable_rep.comp measurable_snd).prodMk measurable_fst)

lemma measurable_average (endpoint : Bool) (m d : ℕ) (s : Finset ℕ) :
    Measurable (average endpoint m d s) := by
  unfold average
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_prod
  intro i hi
  have hp : Measurable (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) =>
      (n : ℝ) * z.1 i) :=
    measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)
  have hx : Measurable (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact (measurable_circleKernel endpoint m).comp (hp.prodMk hx)

lemma measurable_errorSq (endpoint : Bool) (m d : ℕ) (s : Finset ℕ) :
    Measurable (errorSq endpoint m d s) :=
  ((measurable_average endpoint m d s).sub measurable_const).pow_const 2

lemma kernel_bounds (endpoint : Bool) {m : ℕ} (hm : 0 < m) (z v : ℝ) :
    0 ≤ kernel endpoint m z v ∧
      kernel endpoint m z v ≤ (m : ℝ)^2 / CircleParameterData.kernelWidth m :=
  CircleParameterData.orientedKernel_bounds endpoint hm z (Int.fract v)

lemma average_bounds (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (z : (Fin d → ℝ) × UnitAddTorus (Fin d)) :
    0 ≤ average endpoint m d s z ∧ average endpoint m d s z ≤
      ((m : ℝ)^2 / CircleParameterData.kernelWidth m) ^ d := by
  classical
  let B : ℝ := (m : ℝ)^2 / CircleParameterData.kernelWidth m
  have hB : 0 ≤ B := by dsimp [B, CircleParameterData.kernelWidth]; positivity
  have hnon (n : ℕ) : 0 ≤ ∏ i : Fin d,
      circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i) :=
    Finset.prod_nonneg fun i _ => (kernel_bounds endpoint hm _ _).1
  have hupper (n : ℕ) : (∏ i : Fin d,
      circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)) ≤ B ^ d := by
    calc
      _ ≤ ∏ _i : Fin d, B := Finset.prod_le_prod₀
        (fun i _ => (kernel_bounds endpoint hm _ _).1)
        (fun i _ => (kernel_bounds endpoint hm _ _).2)
      _ = _ := by simp
  unfold average
  refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => hnon n), ?_⟩
  by_cases hs : s.card = 0
  · simp only [hs, Nat.cast_zero, inv_zero, zero_mul]
    exact pow_nonneg hB d
  · have hsR : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
    calc
      _ ≤ (s.card : ℝ)⁻¹ * ∑ _n ∈ s, B ^ d :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hupper n) (by positivity)
      _ = B ^ d := by simp [hsR]

lemma errorSq_bounds (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (z : (Fin d → ℝ) × UnitAddTorus (Fin d)) :
    0 ≤ errorSq endpoint m d s z ∧ |errorSq endpoint m d s z| ≤
      (((m : ℝ)^2 / CircleParameterData.kernelWidth m) ^ d + 1) ^ 2 := by
  have ha := average_bounds endpoint hm d s z
  have hb : 0 ≤ ((m : ℝ)^2 / CircleParameterData.kernelWidth m) ^ d := by
    unfold CircleParameterData.kernelWidth
    positivity
  unfold errorSq
  refine ⟨sq_nonneg _, ?_⟩
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (average endpoint m d s z),
    mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]

lemma ae_joint_continuousAt_kernel (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (v : ℝ) (hv : Int.fract v ≠ 0) :
    ∀ᵐ z : ℝ ∂volume,
      ContinuousAt (fun p : ℝ × ℝ => kernel endpoint m p.1 p.2) (z,v) := by
  have hh := (ScalarSampling.manuscript_parameters hm).1
  have hvfloor : v ≠ (⌊v⌋ : ℤ) := by
    intro heq
    apply hv
    rw [heq]
    simp
  have hf : ContinuousAt Int.fract v := continuousAt_fract hvfloor
  have hcomp (z : ℝ) : ContinuousAt
      (fun p : ℝ × ℝ => (p.1, Int.fract p.2)) (z,v) :=
    continuous_fst.continuousAt.prodMk (hf.comp_of_eq continuous_snd.continuousAt rfl)
  cases endpoint
  · filter_upwards [ScalarSampling.ae_joint_continuousAt_circleKernel hh.ne'
      (Int.fract v) (by simpa using hv)] with z hz
    have h := hz.comp_of_eq (hcomp z) rfl
    convert h using 1
    funext p
    exact CircleParameterData.starting_kernel_fract m p.1 p.2
  · filter_upwards [ScalarSampling.ae_joint_continuousAt_circleEndpoint hh.ne'
      (Int.fract v) (by simpa using hv)] with z hz
    have h := hz.comp_of_eq (hcomp z) rfl
    convert h using 1
    funext p
    exact CircleParameterData.endpoint_kernel_fract m p.1 p.2

lemma ae_joint_continuousAt_circleKernel (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (v : ℝ) (hv : Int.fract v ≠ 0) :
    ∀ᵐ x : Circle ∂volume,
      ContinuousAt (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2) (v,x) := by
  let : NullSingletonClass (volume : Measure Circle) := by
    constructor
    intro x
    simpa using (AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) 0)
  have hc := CocycleSupport.measurePreserving_circleRepresentative.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (ae_joint_continuousAt_kernel endpoint hm v hv))
  filter_upwards [hc, (volume : Measure Circle).ae_ne 0] with x hx hxzero
  have hr : ContinuousAt CircleParameterData.rep x :=
    continuous_subtype_val.continuousAt.comp
      (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hxzero)
  have hp : ContinuousAt
      (fun p : ℝ × Circle => (CircleParameterData.rep p.2, p.1)) (v,x) :=
    (hr.comp_of_eq continuous_snd.continuousAt rfl).prodMk continuous_fst.continuousAt
  exact hx.comp_of_eq hp rfl

lemma continuousAt_average_of_kernel (endpoint : Bool) (m d : ℕ) (s : Finset ℕ)
    (τ : Fin d → ℝ) (y : UnitAddTorus (Fin d))
    (h : ∀ n ∈ s, ∀ i : Fin d,
      ContinuousAt (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2)
        ((n : ℝ) * τ i, y i)) :
    ContinuousAt (average endpoint m d s) (τ,y) := by
  have hterm (n : ℕ) (hn : n ∈ s) (i : Fin d) :
      ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) =>
        circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)) (τ,y) := by
    have ha : ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => z.1 i)
        (τ,y) := (continuousAt_apply i τ).comp_of_eq continuous_fst.continuousAt rfl
    have hy : ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => z.2 i)
        (τ,y) := (continuousAt_apply i y).comp_of_eq continuous_snd.continuousAt rfl
    have hnphase : ContinuousAt
        (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => (n : ℝ) * z.1 i) (τ,y) :=
      continuousAt_const.mul ha
    have hmap : ContinuousAt
        (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => ((n : ℝ) * z.1 i, z.2 i))
        (τ,y) := hnphase.prodMk hy
    exact ContinuousAt.comp
      (f := fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => ((n : ℝ) * z.1 i, z.2 i))
      (g := fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2)
      (h n hn i) hmap
  have hp (n : ℕ) (hn : n ∈ s) :
      ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) =>
        ∏ i : Fin d, circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)) (τ,y) :=
    tendsto_finsetProd Finset.univ (fun i _ => hterm n hn i)
  have hs : ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) =>
      ∑ n ∈ s, ∏ i : Fin d, circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)) (τ,y) :=
    tendsto_finsetSum s hp
  exact hs.const_mul _

lemma ae_joint_continuousAt_average (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : Finset ℕ) (τ : Fin d → ℝ)
    (hphase : ∀ n ∈ s, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0) :
    ∀ᵐ y : UnitAddTorus (Fin d) ∂volume,
      ContinuousAt (average endpoint m d s) (τ,y) := by
  let : IsProbabilityMeasure (volume : Measure Circle) :=
    CharacterLaws.circleHaar.property
  have hc (n : ℕ) (hn : n ∈ s) (i : Fin d) :
      ∀ᵐ y : UnitAddTorus (Fin d) ∂volume,
        ContinuousAt (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2)
          ((n : ℝ) * τ i, y i) :=
    (measurePreserving_eval (fun _ : Fin d => (volume : Measure Circle)) i).quasiMeasurePreserving.ae
      (ae_joint_continuousAt_circleKernel endpoint hm _ (hphase n hn i))
  have hall : ∀ᵐ y : UnitAddTorus (Fin d) ∂volume, ∀ n ∈ s, ∀ i : Fin d,
      ContinuousAt (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2)
        ((n : ℝ) * τ i, y i) := by
    rw [Finset.eventually_all]
    intro n hn
    exact ae_all_iff.mpr (hc n hn)
  filter_upwards [hall] with y hy
  exact continuousAt_average_of_kernel endpoint m d s τ y hy

lemma ae_joint_continuousAt_errorSq (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : Finset ℕ) (τ : Fin d → ℝ)
    (hphase : ∀ n ∈ s, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0) :
    ∀ᵐ y : UnitAddTorus (Fin d) ∂volume,
      ContinuousAt (errorSq endpoint m d s) (τ,y) := by
  filter_upwards [ae_joint_continuousAt_average endpoint hm d s τ hphase] with y hy
  exact (hy.sub continuousAt_const).pow 2

end Invariant233.SamplingTests

end

end OAI
