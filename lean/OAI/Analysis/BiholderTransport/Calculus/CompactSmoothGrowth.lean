import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.UniformFiniteGrowth
import OAI.Analysis.BiholderTransport.Calculus.PartialDerivatives
import OAI.Analysis.BiholderTransport.Calculus.TaylorBound

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {P E : Type*} [TopologicalSpace P] [CompactSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [Nonempty ι]

lemma compact_finite_smooth_transverse_growth
    (f : P → ι → E → ℝ) (w : P → ι → ℝ)
    (hw : ∀ a i, 0 ≤ w a i) (hsum : ∀ a, ∑ i, w a i = 1)
    (hwc : ∀ i, Continuous (fun a => w a i))
    (hf : ∀ a i, ∀ᶠ q : E × P in 𝓝 (0,a), ContDiffAt ℝ 2 (f q.2 i) q.1)
    (hf0 : ∀ a i, f a i 0 = 0)
    (hLc : ∀ i, Continuous (fun a => fderiv ℝ (f a i) 0))
    (hBc : ∀ i, Continuous (fun a => fderiv ℝ (fderiv ℝ (f a i)) 0))
    (hD : ∀ a i, ContinuousAt (fun q : E × P =>
      fderiv ℝ (fderiv ℝ (f q.2 i)) q.1) (0,a))
    (hmean : ∀ a v, ∑ i, w a i * fderiv ℝ (f a i) 0 v = 0)
    (hpos : ∀ a v, ‖v‖ = 1 → (∀ i, fderiv ℝ (f a i) 0 v ≤ 0) →
      0 < ∑ i, w a i * fderiv ℝ (fderiv ℝ (f a i)) 0 v v) :
    ∃ b > 0, ∀ᶠ h : E in 𝓝 0, ∀ a : P, ∃ i, b * ‖h‖^2 ≤ f a i h := by
  let L := fun a i => fderiv ℝ (f a i) 0
  let B := fun a i => (1/2 : ℝ) • fderiv ℝ (fderiv ℝ (f a i)) 0
  have hB : ∀ i, Continuous (fun a => B a i) :=
    fun i => (continuous_const : Continuous (fun _ : P => (1/2 : ℝ))).smul (hBc i)
  have hpos' : ∀ a v, ‖v‖ = 1 → (∀ i, L a i v ≤ 0) →
      0 < ∑ i, w a i * B a i v v := by
    intro a v hv hl
    have he : (∑ i, w a i * B a i v v) = (1/2:ℝ) *
        ∑ i, w a i * fderiv ℝ (fderiv ℝ (f a i)) 0 v v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [B,_root_.smul_apply,smul_eq_mul]
      ring
    rw [he]
    exact mul_pos (by norm_num) (hpos a v hv hl)
  obtain ⟨b,hb,H⟩ := uniform_finite_transverse_quadratic_growth w L B hw hsum hmean
    hwc hLc hB hpos'
  have HT : ∀ᶠ h : E in 𝓝 0, ∀ i, ∀ a : P,
      |f a i h - L a i h - B a i h h| ≤ (b/2) * ‖h‖^2 := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := compact_parametric_second_order_remainder (fun a => f a i)
      (fun a => hf a i) (fun a => hD a i) (half_pos hb)
    filter_upwards [hi] with h hh
    intro a
    simpa only [hf0,sub_zero,L,B,_root_.smul_apply,smul_eq_mul,one_div,div_eq_mul_inv,
      one_mul,mul_comm] using hh a
  refine ⟨b/2,half_pos hb,?_⟩
  filter_upwards [H,HT] with h hh ht
  intro a
  obtain ⟨i,hi⟩ := hh a
  have he := (abs_le.mp (ht i a)).1
  exact ⟨i,by nlinarith⟩

end

open Set Filter
open scoped Topology ContDiff

lemma compact_smooth_data_transverse_growth
    {P Q E : Type*} [TopologicalSpace P] [CompactSpace P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : Q → ι → E → ℝ) (d : P → Q) (hd : Continuous d) (w : P → ι → ℝ)
    (hw : ∀ a i, 0 ≤ w a i) (hsum : ∀ a, ∑ i, w a i = 1)
    (hwc : ∀ i, Continuous (fun a => w a i))
    (hf : ∀ a i, ContDiffAt ℝ ∞ (fun q : Q × E => F q.1 i q.2) (d a,0))
    (hf0 : ∀ a i, F (d a) i 0 = 0)
    (hmean : ∀ a v, ∑ i, w a i * fderiv ℝ (F (d a) i) 0 v = 0)
    (hpos : ∀ a v, ‖v‖ = 1 → (∀ i, fderiv ℝ (F (d a) i) 0 v ≤ 0) →
      0 < ∑ i, w a i * fderiv ℝ (fderiv ℝ (F (d a) i)) 0 v v) :
    ∃ b > 0, ∀ᶠ h : E in 𝓝 0, ∀ a : P, ∃ i, b * ‖h‖^2 ≤ F (d a) i h := by
  have hc : Continuous (fun q : E × P => (d q.2,q.1)) :=
    (hd.comp continuous_snd).prodMk continuous_fst
  have hF : ∀ a i, ∀ᶠ q : E × P in 𝓝 (0,a), ContDiffAt ℝ 2 (F (d q.2) i) q.1 := by
    intro a i
    have H := ((hf a i).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp)
    filter_upwards [hc.continuousAt.tendsto.eventually H] with q hq
    exact hq.comp q.1 (contDiffAt_const.prodMk contDiffAt_id)
  have hD : ∀ a i, ContinuousAt (fun q : E × P =>
      fderiv ℝ (fderiv ℝ (F (d q.2) i)) q.1) (0,a) := by
    intro a i
    exact (ContDiffAt.partial_snd_fderiv_two (f := fun q => F q i) (hf a i)).continuousAt.comp
      (x := (0,a)) (f := fun q : E × P => (d q.2,q.1)) hc.continuousAt
  apply compact_finite_smooth_transverse_growth (fun a => F (d a)) w hw hsum hwc hF hf0
  · intro i
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (ContDiffAt.partial_snd_fderiv (f := fun q => F q i) (hf a i)).continuousAt.comp
      (x := a) (f := fun a => (d a,(0:E))) (hd.continuousAt.prodMk continuousAt_const)
  · intro i
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (hD a i).comp (x := a) (f := fun a => ((0:E),a))
      (continuousAt_const.prodMk continuousAt_id)
  · exact hD
  · exact hmean
  · exact hpos

end WeakMTWTransport

end

end OAI
