import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingShear
import Mathlib.Topology.Algebra.Order.Floor

namespace OAI

open Set Filter MeasureTheory
open scoped Topology

namespace Invariant233.ScalarSampling

lemma continuousAt_ite_lt_of_ne {X : Type*} [TopologicalSpace X]
    {f g a b : X → ℝ} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hne : f x ≠ g x) :
    ContinuousAt (fun y => if f y < g y then a y else b y) x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply ha.congr_of_eventuallyEq
    filter_upwards [hf.eventually_lt hg hlt] with y hy
    exact ite_eq_left hy
  · apply hb.congr_of_eventuallyEq
    filter_upwards [hg.eventually_lt hf hgt] with y hy
    exact ite_eq_right (not_lt.mpr hy.le)

lemma continuousAt_ite_le_of_ne {X : Type*} [TopologicalSpace X]
    {f g a b : X → ℝ} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hne : f x ≠ g x) :
    ContinuousAt (fun y => if f y ≤ g y then a y else b y) x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply ha.congr_of_eventuallyEq
    filter_upwards [hf.eventually_lt hg hlt] with y hy
    exact ite_eq_left hy.le
  · apply hb.congr_of_eventuallyEq
    filter_upwards [hg.eventually_lt hf hgt] with y hy
    exact ite_eq_right (not_le.mpr hy)

theorem continuousAt_rawKernel_pair {h α : ℝ} (hh : h ≠ 0) (p : ℝ × ℝ)
    (hdelta : delta p.1 ≠ 0) (hcut : α ≠ delta p.1)
    (hzero : p.2 ≠ 0) (hedge : p.2 ≠ h * delta p.1) :
    ContinuousAt (fun q : ℝ × ℝ => rawKernel h α q.1 q.2) p := by
  have hd : ContinuousAt (fun q : ℝ × ℝ => delta q.1) p :=
    continuous_fst.continuousAt.min (continuousAt_const.sub continuous_fst.continuousAt)
  have hheight : ContinuousAt (fun q : ℝ × ℝ => h * delta q.1) p := continuousAt_const.mul hd
  have hinv : ContinuousAt (fun q : ℝ × ℝ => (h * delta q.1)⁻¹) p :=
    hheight.inv₀ (mul_ne_zero hh hdelta)
  have he := continuousAt_ite_lt_of_ne continuous_snd.continuousAt hheight
    hinv (continuousAt_const (y := (0 : ℝ))) hedge
  have hz := continuousAt_ite_lt_of_ne (continuousAt_const (y := (0 : ℝ)))
    continuous_snd.continuousAt he (continuousAt_const (y := (0 : ℝ))) hzero.symm
  have hc := continuousAt_ite_le_of_ne (continuousAt_const (y := α)) hd hz
    (continuousAt_const (y := (0 : ℝ))) hcut
  convert hc using 1
  funext q
  simp only [rawKernel, Set.indicator_apply, mem_Ioo, ite_and]

theorem continuousAt_circleKernel_pair {h α : ℝ} (hh : h ≠ 0) (p : ℝ × ℝ)
    (hz : Int.fract p.1 ≠ 0) (hv : Int.fract p.2 ≠ 0)
    (hcut : α ≠ delta (Int.fract p.1))
    (hedge : Int.fract p.2 ≠ h * delta (Int.fract p.1)) :
    ContinuousAt (fun q : ℝ × ℝ => circleKernel h α q.1 q.2) p := by
  have hdz : 0 < delta (Int.fract p.1) := by
    apply lt_min
    · exact lt_of_le_of_ne (Int.fract_nonneg _) hz.symm
    · exact sub_pos.mpr (Int.fract_lt_one _)
  have hzfloor : p.1 ≠ (⌊p.1⌋ : ℤ) := by
    intro heq
    apply hz
    rw [heq]; simp
  have hvfloor : p.2 ≠ (⌊p.2⌋ : ℤ) := by
    intro heq
    apply hv
    rw [heq]; simp
  have hrep : ContinuousAt (fun q : ℝ × ℝ => (Int.fract q.1, Int.fract q.2)) p :=
    ((continuousAt_fract hzfloor).comp continuous_fst.continuousAt).prodMk
      ((continuousAt_fract hvfloor).comp continuous_snd.continuousAt)
  exact (continuousAt_rawKernel_pair hh (Int.fract p.1, Int.fract p.2)
    hdz.ne' hcut hv hedge).comp_of_eq hrep rfl

theorem continuousAt_circleEndpoint_pair {h α : ℝ} (hh : h ≠ 0) (p : ℝ × ℝ)
    (hz : Int.fract (p.1 - p.2) ≠ 0) (hv : Int.fract p.2 ≠ 0)
    (hcut : α ≠ delta (Int.fract (p.1 - p.2)))
    (hedge : Int.fract p.2 ≠ h * delta (Int.fract (p.1 - p.2))) :
    ContinuousAt (fun q : ℝ × ℝ => circleKernel h α (q.1 - q.2) q.2) p := by
  have hshear : ContinuousAt (fun q : ℝ × ℝ => (q.1-q.2, q.2)) p :=
    (continuous_fst.continuousAt.sub continuous_snd.continuousAt).prodMk continuous_snd.continuousAt
  exact (continuousAt_circleKernel_pair hh (p.1-p.2, p.2) hz hv hcut hedge).comp_of_eq hshear rfl

lemma ae_fract_sub_ne (c a : ℝ) : ∀ᵐ x : ℝ ∂volume, Int.fract (x-c) ≠ a := by
  rw [ae_iff]
  apply Set.Countable.measure_zero
  apply (Set.countable_range (fun n : ℤ => a + c + n)).mono
  intro x hx
  change ¬Int.fract (x-c) ≠ a at hx
  have heq := not_not.mp hx
  refine ⟨⌊x-c⌋, ?_⟩
  have hsum := Int.fract_add_floor (x-c)
  rw [heq] at hsum
  linarith

lemma ae_delta_fract_sub_ne (c a : ℝ) :
    ∀ᵐ x : ℝ ∂volume, delta (Int.fract (x-c)) ≠ a := by
  filter_upwards [ae_fract_sub_ne c a, ae_fract_sub_ne c (1-a)] with x hx hy
  intro heq
  unfold delta at heq
  rcases le_total (Int.fract (x-c)) (1-Int.fract (x-c)) with h | h
  · rw [min_eq_left h] at heq
    exact hx heq
  · rw [min_eq_right h] at heq
    apply hy
    linarith

theorem ae_joint_continuousAt_circleKernel {h α : ℝ} (hh : h ≠ 0)
    (v : ℝ) (hv : Int.fract v ≠ 0) :
    ∀ᵐ z : ℝ ∂volume,
      ContinuousAt (fun p : ℝ × ℝ => circleKernel h α p.1 p.2) (z,v) := by
  filter_upwards [ae_fract_sub_ne 0 0, ae_delta_fract_sub_ne 0 α,
    ae_delta_fract_sub_ne 0 (Int.fract v / h)] with z hz hc he
  simp only [sub_zero] at hz hc he
  apply continuousAt_circleKernel_pair hh (z,v) hz hv hc.symm
  intro heq
  apply he
  rw [heq]
  field_simp

theorem ae_joint_continuousAt_circleEndpoint {h α : ℝ} (hh : h ≠ 0)
    (v : ℝ) (hv : Int.fract v ≠ 0) :
    ∀ᵐ z : ℝ ∂volume,
      ContinuousAt (fun p : ℝ × ℝ => circleKernel h α (p.1-p.2) p.2) (z,v) := by
  filter_upwards [ae_fract_sub_ne v 0, ae_delta_fract_sub_ne v α,
    ae_delta_fract_sub_ne v (Int.fract v / h)] with z hz hc he
  apply continuousAt_circleEndpoint_pair hh (z,v) hz hv hc.symm
  intro heq
  apply he
  rw [heq]
  field_simp

theorem ae_joint_continuousAt_manuscriptPower {m : ℕ} (hm : 200 ≤ m)
    (n τ : ℝ) (hphase : Int.fract (n*τ) ≠ 0) :
    ∀ᵐ z : ℝ ∂volume,
      ContinuousAt (fun p : ℝ × ℝ => manuscriptKernel m p.1 (n*p.2)) (z,τ) := by
  have hh := (manuscript_parameters hm).1
  filter_upwards [ae_joint_continuousAt_circleKernel hh.ne' (n*τ) hphase] with z hz
  have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1,n*p.2)) (z,τ) :=
    continuous_fst.continuousAt.prodMk (continuousAt_const.mul continuous_snd.continuousAt)
  exact hz.comp_of_eq hc rfl

theorem ae_joint_continuousAt_manuscriptEndpointPower {m : ℕ} (hm : 200 ≤ m)
    (n τ : ℝ) (hphase : Int.fract (n*τ) ≠ 0) :
    ∀ᵐ z : ℝ ∂volume,
      ContinuousAt (fun p : ℝ × ℝ => manuscriptEndpointKernel m p.1 (n*p.2)) (z,τ) := by
  have hh := (manuscript_parameters hm).1
  filter_upwards [ae_joint_continuousAt_circleEndpoint hh.ne' (n*τ) hphase] with z hz
  have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1,n*p.2)) (z,τ) :=
    continuous_fst.continuousAt.prodMk (continuousAt_const.mul continuous_snd.continuousAt)
  exact hz.comp_of_eq hc rfl

end Invariant233.ScalarSampling

end OAI
