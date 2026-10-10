import Mathlib
import OAI.Analysis.MumfordShah.Variations

namespace OAI

/-! MumfordShah sobolev algebra. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology Filter
open scoped ContDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Filter

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff

lemma test_deriv_integral_eq_zero {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (a : ℂ) :
    (∫ x : ℂ, fderiv ℝ ψ x a) = 0 := by
  have hd : Continuous (fun x => fderiv ℝ ψ x a) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : ℂ => (1 : ℝ)) (g := ψ) (v := a)
    (by simp)
    (by simpa using hd.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ a))
    (by simpa using hψ.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const _) (fun x _ => hψ.differentiable (by norm_num) x)
  simpa using hi

lemma SobolevOn.sub_const {u : ℂ → ℝ} {m : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) (hU : Bornology.IsBounded U) (c : ℝ) :
    SobolevOn (fun x => u x - c) m U := by
  have : IsFiniteMeasure (volume.restrict U) :=
    ⟨by simpa using hU.measure_lt_top (μ := (volume : Measure ℂ))⟩
  refine ⟨hu.1.sub (memLp_const c), hu.2.1, ?_⟩
  intro ψ hψ hc ht a
  have hd : MemLp (fun x => fderiv ℝ ψ x a) 2 (volume.restrict U) :=
    ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ a)
  have hi : Integrable (fun x => u x * fderiv ℝ ψ x a) (volume.restrict U) := hu.1.integrable_mul hd
  have hid : Integrable (fun x => c * fderiv ℝ ψ x a) (volume.restrict U) :=
    (hd.integrable (by norm_num)).const_mul c
  have hz : (∫ x in U, fderiv ℝ ψ x a) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [fderiv_of_notMem_tsupport ℝ (fun hn => hx (ht hn))]; simp)]
    exact test_deriv_integral_eq_zero hψ hc a
  simp_rw [sub_mul]
  rw [integral_sub hi hid, integral_const_mul, hz, mul_zero, sub_zero]
  exact hu.2.2 ψ hψ hc ht a

lemma SobolevOn.sub {u v : ℂ → ℝ} {m n : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) (hv : SobolevOn v n U) :
    SobolevOn (u-v) (m-n) U := by
  refine ⟨hu.1.sub hv.1, hu.2.1.sub hv.2.1, ?_⟩
  intro ψ hψ hc ht a
  have hd : MemLp (fun x => fderiv ℝ ψ x a) 2 (volume.restrict U) :=
    ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ a)
  have htL : MemLp ψ 2 (volume.restrict U) := hψ.continuous.memLp_of_hasCompactSupport hc
  have him : Integrable (fun x => inner ℝ (m x) a * ψ x) (volume.restrict U) :=
    (hu.2.1.inner_const (𝕜 := ℝ) a).integrable_mul htL
  have hin : Integrable (fun x => inner ℝ (n x) a * ψ x) (volume.restrict U) :=
    (hv.2.1.inner_const (𝕜 := ℝ) a).integrable_mul htL
  have hiu : Integrable (fun x => u x * fderiv ℝ ψ x a) (volume.restrict U) := hu.1.integrable_mul hd
  have hiv : Integrable (fun x => v x * fderiv ℝ ψ x a) (volume.restrict U) := hv.1.integrable_mul hd
  simp only [Pi.sub_apply, inner_sub_left, sub_mul]
  rw [integral_sub hiu hiv,
    integral_sub him hin, hu.2.2 ψ hψ hc ht a, hv.2.2 ψ hψ hc ht a]
  ring

lemma SobolevOn.mono {u : ℂ → ℝ} {m : ℂ → ℂ} {U V : Set ℂ}
    (hu : SobolevOn u m V) (hUV : U ⊆ V) : SobolevOn u m U := by
  refine ⟨hu.1.mono_measure (Measure.restrict_mono hUV le_rfl),
    hu.2.1.mono_measure (Measure.restrict_mono hUV le_rfl), ?_⟩
  intro ψ hψ hc ht a
  have hleft (S : Set ℂ) (hS : tsupport ψ ⊆ S) :
      (∫ x in S, u x * fderiv ℝ ψ x a) = ∫ x, u x * fderiv ℝ ψ x a := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [fderiv_of_notMem_tsupport ℝ (fun hn => hx (hS hn))]; simp)
  have hright (S : Set ℂ) (hS : tsupport ψ ⊆ S) :
      (∫ x in S, inner ℝ (m x) a * ψ x) = ∫ x, inner ℝ (m x) a * ψ x := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hn => hx (hS hn))]; simp)
  have h := hu.2.2 ψ hψ hc (ht.trans hUV) a
  rwa [hleft V (ht.trans hUV), hright V (ht.trans hUV), ← hleft U ht, ← hright U ht] at h

lemma SobolevOn.congr_gradient {u : ℂ → ℝ} {m n : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) (he : m =ᵐ[volume.restrict U] n) :
    SobolevOn u n U := by
  refine ⟨hu.1, MemLp.ae_eq he hu.2.1, ?_⟩
  intro ψ hψ hc ht a
  rw [hu.2.2 ψ hψ hc ht a]
  congr 1
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

lemma weak_gradient_zero_on {u : ℂ → ℝ} {m : ℂ → ℂ} {O : Set ℂ}
    (hu : SobolevOn u m O) (hO : IsOpen O)
    (hz : u =ᵐ[volume.restrict O] 0) :
    m =ᵐ[volume.restrict O] 0 := by
  have hm (a : ℂ) : (fun x => inner ℝ (m x) a) =ᵐ[volume.restrict O] 0 := by
    have hL : LocallyIntegrableOn (fun x => inner ℝ (m x) a) O volume :=
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hu.2.1.inner_const (𝕜 := ℝ) a).locallyIntegrable (by norm_num))
    have hf := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero hL ?_
    · exact (ae_restrict_iff' hO.measurableSet).mpr hf
    intro ψ hψ hc ht
    have h := hu.2.2 ψ hψ hc ht a
    have hzero : (∫ x in O, u x * fderiv ℝ ψ x a) = 0 := by
      have hez : (fun x => u x * fderiv ℝ ψ x a) =ᵐ[volume.restrict O] 0 := by
        filter_upwards [hz] with x hx
        simp [hx]
      rw [integral_congr_ae hez]
      simp
    rw [hzero] at h
    have hint : (∫ x in O, inner ℝ (m x) a * ψ x) = 0 := by linarith
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := O) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hn => hx (ht hn))]; simp)]
    simpa [smul_eq_mul, mul_comm] using hint
  filter_upwards [hm 1, hm Complex.I] with x hx hy
  have hi (a : ℂ) : inner ℝ (m x) a = (m x).re * a.re + (m x).im * a.im := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
    change (a * star (m x)).re = _
    simp [Complex.mul_re]
    ring
  simp only [Pi.zero_apply, hi, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add] at hx hy
  apply Complex.ext <;> assumption

open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff

lemma SobolevOn.mul_smooth {u : ℂ → ℝ} {m : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) :
    SobolevOn (fun x => χ x * u x)
      (fun x => χ x • m x + u x • gradient χ x) U := by
  have hχL : MemLp χ ∞ (volume.restrict U) := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχgL : MemLp (gradient χ) ∞ (volume.restrict U) :=
    (continuous_gradient_of_smooth hχ).memLp_of_hasCompactSupport (compactSupport_gradient hc)
  refine ⟨hχL.fun_mul (r := 2) hu.1, (hχL.smul hu.2.1).add (hu.1.smul hχgL), ?_⟩
  intro ψ hψ hψc ht a
  have hprod := hu.2.2 (χ * ψ) (hχ.mul hψ) (hc.mul_right)
    (tsupport_mul_subset_right.trans ht) a
  have hχdL : MemLp (fun x => fderiv ℝ χ x a) ∞ (volume.restrict U) :=
    ((hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ a)
  have hψL : MemLp ψ 2 (volume.restrict U) := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hψdL : MemLp (fun x => fderiv ℝ ψ x a) 2 (volume.restrict U) :=
    ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hψc.fderiv_apply ℝ a)
  have hi : Integrable (fun x => χ x * u x * fderiv ℝ ψ x a) (volume.restrict U) :=
    (hχL.fun_mul (r := 2) hu.1).integrable_mul hψdL
  have hj : Integrable (fun x => u x * fderiv ℝ χ x a * ψ x) (volume.restrict U) := by
    have hL : MemLp (fun x => u x * fderiv ℝ χ x a) 2 (volume.restrict U) := by
      exact hu.1.fun_mul hχdL
    exact hL.integrable_mul hψL
  have hk : Integrable (fun x => χ x * inner ℝ (m x) a * ψ x) (volume.restrict U) :=
    (hχL.fun_mul (r := 2) (hu.2.1.inner_const (𝕜 := ℝ) a)).integrable_mul hψL
  have hd (x : ℂ) : u x * fderiv ℝ (χ * ψ) x a =
      χ x * u x * fderiv ℝ ψ x a + u x * fderiv ℝ χ x a * ψ x := by
    rw [fderiv_mul (hχ.differentiable (by norm_num) x) (hψ.differentiable (by norm_num) x)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  simp_rw [hd] at hprod
  rw [integral_add hi hj] at hprod
  have hright (x : ℂ) : inner ℝ (χ x • m x + u x • gradient χ x) a * ψ x =
      χ x * inner ℝ (m x) a * ψ x + u x * fderiv ℝ χ x a * ψ x := by
    simp only [inner_add_left, real_inner_smul_left, inner_gradient_left, add_mul]
  simp_rw [hright]
  rw [integral_add hk hj]
  have hh : (∫ x in U, inner ℝ (m x) a * (χ * ψ) x) =
      ∫ x in U, χ x * inner ℝ (m x) a * ψ x := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [Pi.mul_apply]
    ring
  rw [hh] at hprod
  linarith

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff

lemma SobolevOn.translate {u : ℂ → ℝ} {m : ℂ → ℂ} {U : Set ℂ}
    (hu : SobolevOn u m U) (hU : MeasurableSet U) (t : ℂ) :
    SobolevOn (fun x => u (x-t)) (fun x => m (x-t)) ((fun x => x-t) ⁻¹' U) := by
  have hp := (measurePreserving_sub_right volume t).restrict_preimage hU
  refine ⟨hu.1.comp_measurePreserving hp, hu.2.1.comp_measurePreserving hp, ?_⟩
  intro ψ hψ hc ht a
  let Ψ := fun x : ℂ => ψ (x+t)
  have hΨ : ContDiff ℝ ∞ Ψ := hψ.comp (contDiff_id.add contDiff_const)
  have hcΨ : HasCompactSupport Ψ := hc.comp_homeomorph (Homeomorph.addRight t)
  have hsΨ : tsupport Ψ ⊆ U := by
    intro x hx
    have hh : x+t ∈ tsupport ψ := tsupport_comp_subset_preimage ψ
      (continuous_id.add continuous_const) hx
    have hh := ht hh
    simpa only [mem_preimage, add_sub_cancel_right] using hh
  have hh := hu.2.2 Ψ hΨ hcΨ hsΨ a
  have hl := hp.integral_comp (Homeomorph.addRight (-t)).measurableEmbedding
    (fun x => u x * fderiv ℝ Ψ x a)
  have hr := hp.integral_comp (Homeomorph.addRight (-t)).measurableEmbedding
    (fun x => inner ℝ (m x) a * Ψ x)
  have hd (x : ℂ) : fderiv ℝ Ψ (x-t) = fderiv ℝ ψ x := by
    simp only [Ψ, fderiv_comp_add_right, sub_add_cancel]
  simp only [hd] at hl
  simp only [Ψ, sub_add_cancel] at hr
  rw [hl, hr]
  exact hh

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff

lemma Rectifiable.mono {H A : Set Plane} (hH : Rectifiable H) (hA : A ⊆ H) :
    Rectifiable A := by
  obtain ⟨γ,hγ,h0⟩ := hH
  exact ⟨γ,hγ,measure_mono_null (sdiff_subset_sdiff_left hA) h0⟩

lemma Rectifiable.union {A B : Set Plane} (hA : Rectifiable A) (hB : Rectifiable B) :
    Rectifiable (A ∪ B) := by
  obtain ⟨γ,hγ,hA⟩ := hA
  obtain ⟨η,hη,hB⟩ := hB
  let e := Denumerable.eqv (ℕ ⊕ ℕ)
  let ζ (n : ℕ) : ℝ → Plane := Sum.elim γ η (e.symm n)
  have hγsub : (⋃ n, range (γ n)) ⊆ ⋃ n, range (ζ n) := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨e (Sum.inl n), ?_⟩
    simpa only [ζ, Equiv.symm_apply_apply, Sum.elim_inl] using hn
  have hηsub : (⋃ n, range (η n)) ⊆ ⋃ n, range (ζ n) := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨e (Sum.inr n), ?_⟩
    simpa only [ζ, Equiv.symm_apply_apply, Sum.elim_inr] using hn
  refine ⟨ζ,?_,?_⟩
  · intro n
    dsimp [ζ]
    cases he : e.symm n with
    | inl k => exact hγ k
    | inr k => exact hη k
  · apply measure_mono_null (t := (A \ ⋃ n, range (γ n)) ∪ (B \ ⋃ n, range (η n)))
    · intro x hx
      rcases hx.1 with ha|hb
      · exact Or.inl ⟨ha,fun h => hx.2 (hγsub h)⟩
      · exact Or.inr ⟨hb,fun h => hx.2 (hηsub h)⟩
    · exact measure_union_null hA hB

lemma Rectifiable.translate {A : Set Plane} (hA : Rectifiable A) (t : Plane) :
    Rectifiable ((fun x => x+t) '' A) := by
  obtain ⟨γ,hγ,hA⟩ := hA
  refine ⟨fun n s => γ n s+t, ?_, ?_⟩
  · intro n
    obtain ⟨C,hC⟩ := hγ n
    exact ⟨1*C,(isometry_add_right t).lipschitzWith.comp hC⟩
  · have heq : ((fun x => x+t) '' A) \ ⋃ n, range (fun s => γ n s+t) =
        (fun x => x+t) '' (A \ ⋃ n, range (γ n)) := by
      ext x
      constructor
      · rintro ⟨⟨y,hy,rfl⟩,hx⟩
        refine ⟨y,⟨hy,?_⟩,rfl⟩
        intro hz
        obtain ⟨n,s,hs⟩ := mem_iUnion.mp hz
        subst y
        exact hx (mem_iUnion.mpr ⟨n,mem_range_self s⟩)
      · rintro ⟨y,⟨hy,hn⟩,rfl⟩
        refine ⟨mem_image_of_mem _ hy,?_⟩
        intro hx
        obtain ⟨n,s,hs⟩ := mem_iUnion.mp hx
        exact hn (mem_iUnion.mpr ⟨n,⟨s,add_right_cancel hs⟩⟩)
    rw [heq]
    rw [(isometry_add_right t).hausdorffMeasure_image (Or.inl (by norm_num : (0:ℝ) ≤ 1))]
    exact hA

lemma translate_set_eq_preimage (A : Set Plane) (t : Plane) :
    (fun x => x+t) '' A = (fun x => x-t) ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x-t,hx,sub_add_cancel _ _⟩

lemma translated_length (A : Set Plane) (t : Plane) :
    lengthMeasure ((fun x => x+t) '' A) = lengthMeasure A := by
  exact (isometry_add_right t).hausdorffMeasure_image (Or.inl (by norm_num)) A

end MumfordShah
end

end OAI
