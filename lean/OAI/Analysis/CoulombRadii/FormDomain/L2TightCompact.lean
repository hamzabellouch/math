import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.WeakHilbertCompact
import OAI.Analysis.CoulombRadii.FormDomain.L1L2Fourier

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma cutL2_sub_self (s:Set E) (hs:MeasurableSet s) (u:Lp ℂ 2 (volume:Measure E)) :
    u-cutL2 s hs u=cutL2 sᶜ hs.compl u := by
  have h := cutL2_add_compl s hs u
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)
lemma double_cut_approximation (s t:Set E) (hs:MeasurableSet s) (ht:MeasurableSet t)
    (u:Lp ℂ 2 (volume:Measure E)) :
    ‖(𝓕 u : Lp ℂ 2 (volume:Measure E))-cutL2 t ht (𝓕 (cutL2 s hs u))‖ ≤
      ‖cutL2 tᶜ ht.compl (𝓕 u)‖+‖cutL2 sᶜ hs.compl u‖ := by
  calc
    _≤‖(𝓕 u : Lp ℂ 2 (volume:Measure E))-cutL2 t ht (𝓕 u)‖+
        ‖cutL2 t ht (𝓕 u)-cutL2 t ht (𝓕 (cutL2 s hs u))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤‖cutL2 tᶜ ht.compl (𝓕 u)‖+‖(𝓕 u : Lp ℂ 2 (volume:Measure E))-𝓕 (cutL2 s hs u)‖ := by
      rw [cutL2_sub_self,←cutL2_sub]
      exact add_le_add (le_refl _) (cutL2_norm_le t ht _)
    _= _ := by
      have h : ‖(𝓕 u : Lp ℂ 2 (volume:Measure E))-𝓕 (cutL2 s hs u)‖=‖u-cutL2 s hs u‖ := by
        change ‖(Lp.fourierTransformₗᵢ E ℂ) u-(Lp.fourierTransformₗᵢ E ℂ) (cutL2 s hs u)‖=_
        rw [←map_sub,(Lp.fourierTransformₗᵢ E ℂ).norm_map]
      rw [h,cutL2_sub_self]

lemma l2_tight_frequency_subsequence
    (u:ℕ → Lp ℂ 2 (volume:Measure E)) (C:ℝ) (hb:∀ n,‖u n‖≤C)
    (hspace:∀ ε:ℝ,0<ε → ∃ s:Set E,∃ hs:MeasurableSet s,volume s≠∞ ∧
      ∀ᶠ n in atTop,‖cutL2 sᶜ hs.compl (u n)‖≤ε)
    (hfreq:∀ ε:ℝ,0<ε → ∃ t:Set E,∃ ht:MeasurableSet t,volume t≠∞ ∧
      ∀ᶠ n in atTop,‖cutL2 tᶜ ht.compl (𝓕 (u n))‖≤ε) :
    ∃ v:Lp ℂ 2 (volume:Measure E),∃ φ:ℕ → ℕ,StrictMono φ ∧
      Tendsto (u ∘ φ) atTop (𝓝 v) := by
  let : Fact ((2:ℝ≥0∞)≠∞) := ⟨by norm_num⟩
  obtain ⟨v,hv,φ,hφ,hw⟩ := bounded_hilbert_weak_subsequence u C hb
  have hd : CauchySeq (fun n => (𝓕 (u (φ n)) : Lp ℂ 2 (volume:Measure E))) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hδ : 0<ε/8 := by positivity
    obtain ⟨s,hs,hμ,hsp⟩ := hspace (ε/8) hδ
    obtain ⟨t,ht,hν,hfr⟩ := hfreq (ε/8) hδ
    have hconv := fourier_double_cut_tendsto s t hs ht hμ hν (u ∘ φ) v C
      (fun n => hb (φ n)) hw
    have hloc := hconv.eventually (Metric.ball_mem_nhds _ hδ)
    have hsp' := hφ.tendsto_atTop.eventually hsp
    have hfr' := hφ.tendsto_atTop.eventually hfr
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((hloc.and hsp').and hfr')
    refine ⟨N,?_⟩
    intro j hj k hk
    obtain ⟨⟨hlj,hsj⟩,hfj⟩ := hN j hj
    obtain ⟨⟨hlk,hsk⟩,hfk⟩ := hN k hk
    have hjj := double_cut_approximation s t hs ht (u (φ j))
    have hkk := double_cut_approximation s t hs ht (u (φ k))
    change dist (cutL2 t ht (𝓕 (cutL2 s hs (u (φ j)))))
      (cutL2 t ht (𝓕 (cutL2 s hs v))) < ε/8 at hlj
    change dist (cutL2 t ht (𝓕 (cutL2 s hs (u (φ k)))))
      (cutL2 t ht (𝓕 (cutL2 s hs v))) < ε/8 at hlk
    have hh := dist_triangle4 (𝓕 (u (φ j)))
      (cutL2 t ht (𝓕 (cutL2 s hs (u (φ j)))) )
      (cutL2 t ht (𝓕 (cutL2 s hs (u (φ k)))) ) (𝓕 (u (φ k)))
    have hmid := dist_triangle (cutL2 t ht (𝓕 (cutL2 s hs (u (φ j)))))
      (cutL2 t ht (𝓕 (cutL2 s hs v)))
      (cutL2 t ht (𝓕 (cutL2 s hs (u (φ k)))))
    rw [dist_comm (cutL2 t ht (𝓕 (cutL2 s hs v)))] at hmid
    rw [dist_comm (cutL2 t ht (𝓕 (cutL2 s hs (u (φ k)))))] at hh
    simp only [dist_eq_norm] at hh hmid hlj hlk ⊢
    linarith
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete hd
  refine ⟨(Lp.fourierTransformₗᵢ E ℂ).symm w,φ,hφ,?_⟩
  have h := ((Lp.fourierTransformₗᵢ E ℂ).symm.continuous.tendsto w).comp hw
  change Tendsto (fun n => (Lp.fourierTransformₗᵢ E ℂ).symm
    ((Lp.fourierTransformₗᵢ E ℂ) (u (φ n)))) atTop (𝓝 ((Lp.fourierTransformₗᵢ E ℂ).symm w)) at h
  simpa only [LinearIsometryEquiv.symm_apply_apply,Function.comp_def] using h
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate ContDiff BigOperators
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma l2_real_test_inner (f:E → ℝ) (hf:MemLp (fun x => (f x:ℂ)) 2 volume)
    (u:Lp ℂ 2 (volume:Measure E)) :
    inner ℂ (hf.toLp (fun x => (f x:ℂ))) u = ∫ x,(f x:ℂ)*u x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx,RCLike.inner_apply,mul_comm]
lemma weak_l2_pairing_tendsto {u:ℕ → Lp ℂ 2 (volume:Measure E)}
    {v:Lp ℂ 2 (volume:Measure E)}
    (hw:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v)))
    (f:E → ℝ) (hf:MemLp (fun x => (f x:ℂ)) 2 volume) :
    Tendsto (fun n => ∫ x,(f x:ℂ)*u n x) atTop (𝓝 (∫ x,(f x:ℂ)*v x)) := by
  simpa only [l2_real_test_inner] using hw (hf.toLp (fun x => (f x:ℂ)))
lemma weak_l2_derivative_limit {u d:ℕ → Lp ℂ 2 (volume:Measure E)}
    {v g:Lp ℂ 2 (volume:Measure E)} (a:E)
    (hu:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v)))
    (hd:∀ w,Tendsto (fun n => inner ℂ w (d n)) atTop (𝓝 (inner ℂ w g)))
    (hw:∀ n (φ:E → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u n x)=-(∫ x,(φ x:ℂ)*d n x)) :
    ∀ (φ:E → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*v x)=-(∫ x,(φ x:ℂ)*g x) := by
  intro φ hφ hc
  have hfc : Continuous (fun x => (φ x:ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hfs : HasCompactSupport (fun x => (φ x:ℂ)) := hc.comp_left (g:=fun t:ℝ=>(t:ℂ)) (by simp)
  have hdc : Continuous (fun x => (fderiv ℝ φ x a:ℂ)) :=
    Complex.continuous_ofReal.comp ((hφ.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const))
  have hds : HasCompactSupport (fun x => (fderiv ℝ φ x a:ℂ)) :=
    ((hc.fderiv ℝ).comp_left (g:=fun T:E →L[ℝ] ℝ => T a) (by simp)).comp_left
      (g:=fun t:ℝ=>(t:ℂ)) (by simp)
  have H1 := weak_l2_pairing_tendsto hu _ (hdc.memLp_of_hasCompactSupport hds)
  have H2 := (weak_l2_pairing_tendsto hd _ (hfc.memLp_of_hasCompactSupport hfs)).neg
  exact tendsto_nhds_unique H1 (by simpa only [hw _ φ hφ hc] using H2)

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma h1_spatial_tight_subsequence
    (u:ℕ → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (d:ℕ → ι → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (hw:∀ n i (φ:EuclideanSpace ℝ ι → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single i 1):ℂ)*u n x)=-(∫ x,(φ x:ℂ)*d n i x))
    (C K:ℝ) (hb:∀ n,‖u n‖≤C) (hK:∀ n,∑ i,‖d n i‖^2≤K)
    (hsp:∀ ε:ℝ,0<ε → ∃ s:Set (EuclideanSpace ℝ ι),∃ hs:MeasurableSet s,volume s≠(⊤:ℝ≥0∞) ∧
      ∀ᶠ n in atTop,‖cutL2 sᶜ hs.compl (u n)‖≤ε) :
    ∃ v:Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)),∃ φ:ℕ → ℕ,StrictMono φ ∧
      Tendsto (u ∘ φ) atTop (𝓝 v) := by
  apply l2_tight_frequency_subsequence u C hb hsp
  intro ε hε
  obtain ⟨R,hR,H⟩ := bounded_gradient_frequency_tight u d hw K hK ε hε
  exact ⟨Metric.ball 0 R,measurableSet_ball,measure_ball_lt_top.ne,Filter.Eventually.of_forall H⟩
end Coulomb
end

end

end OAI
