import Mathlib
import OAI.Analysis.MumfordShah.TranslatedCompetitor

namespace OAI

/-! MumfordShah decay comparison. -/

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
open Set MeasureTheory Metric Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

lemma eventually_cocompact_to_norm_radius {P : ℂ → Prop}
    (hP : ∀ᶠ x : ℂ in cocompact ℂ, P x) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x : ℂ, R ≤ ‖x‖ → P x := by
  obtain ⟨K,hK,hKP⟩ := mem_cocompact.mp hP
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.exists_pos_norm_lt
  refine ⟨max 1 R,le_max_left _ _,?_⟩
  intro x hx
  exact hKP (fun hn => not_lt_of_ge ((le_max_right 1 R).trans hx) (hKR x hn))

lemma decay_to_radius {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {k : ℕ}
    (h : ∃ C : ℝ, ∀ᶠ x : ℂ in cocompact ℂ, ‖f x‖ ≤ C*‖x‖⁻¹^k) :
    ∃ D R : ℝ, 0 ≤ D ∧ 1 ≤ R ∧ ∀ x : ℂ, R ≤ ‖x‖ → ‖f x‖ ≤ D/‖x‖^k := by
  obtain ⟨C,hC⟩ := h
  obtain ⟨R,hR,hRx⟩ := eventually_cocompact_to_norm_radius hC
  refine ⟨max C 0,R,le_max_right _ _,hR,?_⟩
  intro x hx
  calc
    ‖f x‖ ≤ C*‖x‖⁻¹^k := hRx x hx
    _ ≤ max C 0*‖x‖⁻¹^k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = max C 0/‖x‖^k := by rw [inv_pow,div_eq_mul_inv]

lemma norm_sub_lower_half {x t : ℂ} (ht : 2*‖t‖ ≤ ‖x‖) : ‖x‖/2 ≤ ‖x-t‖ := by
  have h := norm_sub_le x t
  have h' := norm_le_norm_sub_add x t
  linarith

lemma translate_inverse_decay {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    {D R : ℝ} (hD : 0 ≤ D) (hR : 1 ≤ R) {k : ℕ}
    (hf : ∀ᵐ x ∂volume, R ≤ ‖x‖ → ‖f x‖ ≤ D/‖x‖^k) (t : ℂ) :
    ∀ᵐ x ∂volume, max (2*R) (2*‖t‖) ≤ ‖x‖ → ‖f (x-t)‖ ≤ (2:ℝ)^k*D/‖x‖^k := by
  have ht := (measurePreserving_sub_right (volume : Measure ℂ) t).quasiMeasurePreserving.ae hf
  filter_upwards [ht] with x hx hxx
  have hRx : 2*R ≤ ‖x‖ := (le_max_left _ _).trans hxx
  have htx : 2*‖t‖ ≤ ‖x‖ := (le_max_right _ _).trans hxx
  have hxn : 0 < ‖x‖ := by linarith
  have hl := norm_sub_lower_half htx
  have hRp : R ≤ ‖x-t‖ := by linarith
  calc
    ‖f (x-t)‖ ≤ D/‖x-t‖^k := hx hRp
    _ ≤ D/(‖x‖/2)^k := div_le_div_of_nonneg_left hD (pow_pos (half_pos hxn) _)
      (pow_le_pow_left₀ (le_of_lt (half_pos hxn)) hl _)
    _ = (2:ℝ)^k*D/‖x‖^k := by rw [div_pow]; field_simp

lemma inverse_decay_add {E : Type*} [NormedAddCommGroup E] {f g : ℂ → E}
    {D D' R R' : ℝ} {k : ℕ}
    (hf : ∀ᵐ x ∂volume, R ≤ ‖x‖ → ‖f x‖ ≤ D/‖x‖^k)
    (hg : ∀ᵐ x ∂volume, R' ≤ ‖x‖ → ‖g x‖ ≤ D'/‖x‖^k) :
    ∀ᵐ x ∂volume, max R R' ≤ ‖x‖ → ‖f x+g x‖ ≤ (D+D')/‖x‖^k := by
  filter_upwards [hf,hg] with x hx hy hxx
  calc
    ‖f x+g x‖ ≤ ‖f x‖+‖g x‖ := norm_add_le _ _
    _ ≤ D/‖x‖^k+D'/‖x‖^k := add_le_add (hx ((le_max_left _ _).trans hxx))
      (hy ((le_max_right _ _).trans hxx))
    _ = (D+D')/‖x‖^k := by ring

lemma inverse_decay_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {D R : ℝ} {k : ℕ}
    (hf : ∀ᵐ x ∂volume, R ≤ ‖x‖ → ‖f x‖ ≤ D/‖x‖^k) (σ : ℝ) :
    ∀ᵐ x ∂volume, R ≤ ‖x‖ → ‖σ • f x‖ ≤ (|σ| * D)/‖x‖^k := by
  filter_upwards [hf] with x hx hxx
  rw [norm_smul,Real.norm_eq_abs]
  calc
    |σ| * ‖f x‖ ≤ |σ| * (D/‖x‖^k) := mul_le_mul_of_nonneg_left (hx hxx) (abs_nonneg _)
    _ = (|σ| * D)/‖x‖^k := by ring

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

def HasInversePowerDecay {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) (k : ℕ) : Prop :=
  ∃ D R : ℝ, 0 ≤ D ∧ 1 ≤ R ∧ ∀ᵐ x ∂volume, R ≤ ‖x‖ → ‖f x‖ ≤ D/‖x‖^k

lemma HasInversePowerDecay.congr_ae {E : Type*} [NormedAddCommGroup E]
    {f g : ℂ → E} {k : ℕ} (hf : HasInversePowerDecay f k) (he : f =ᵐ[volume] g) :
    HasInversePowerDecay g k := by
  obtain ⟨D,R,hD,hR,hf⟩ := hf
  refine ⟨D,R,hD,hR,?_⟩
  filter_upwards [hf,he] with x hx hg
  simpa only [← hg] using hx

lemma HasInversePowerDecay.add {E : Type*} [NormedAddCommGroup E]
    {f g : ℂ → E} {k : ℕ} (hf : HasInversePowerDecay f k) (hg : HasInversePowerDecay g k) :
    HasInversePowerDecay (fun x => f x+g x) k := by
  obtain ⟨D,R,hD,hR,hf⟩ := hf
  obtain ⟨D',R',hD',hR',hg⟩ := hg
  exact ⟨D+D',max R R',add_nonneg hD hD',hR.trans (le_max_left _ _),inverse_decay_add hf hg⟩

lemma HasInversePowerDecay.neg {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {k : ℕ} (hf : HasInversePowerDecay f k) :
    HasInversePowerDecay (fun x => -f x) k := by
  obtain ⟨D,R,hD,hR,hf⟩ := hf
  exact ⟨D,R,hD,hR,hf.mono (by intro x hx; simpa only [norm_neg] using hx)⟩

lemma HasInversePowerDecay.sub {E : Type*} [NormedAddCommGroup E]
    {f g : ℂ → E} {k : ℕ} (hf : HasInversePowerDecay f k) (hg : HasInversePowerDecay g k) :
    HasInversePowerDecay (fun x => f x-g x) k := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma HasInversePowerDecay.smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} {k : ℕ} (hf : HasInversePowerDecay f k) (σ : ℝ) :
    HasInversePowerDecay (fun x => σ • f x) k := by
  obtain ⟨D,R,hD,hR,hf⟩ := hf
  exact ⟨|σ| * D,R,mul_nonneg (abs_nonneg _) hD,hR,inverse_decay_smul hf σ⟩

lemma HasInversePowerDecay.translate {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {k : ℕ} (hf : HasInversePowerDecay f k) (t : ℂ) :
    HasInversePowerDecay (fun x => f (x-t)) k := by
  obtain ⟨D,R,hD,hR,hf⟩ := hf
  refine ⟨2^k*D,max (2*R) (2*‖t‖),by positivity,?_,translate_inverse_decay hD hR hf t⟩
  exact (by linarith : 1 ≤ 2*R).trans (le_max_left _ _)

lemma hasInversePowerDecay_of_compact_support_ae {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {R : ℝ} (hf : ∀ᵐ x ∂volume, R < ‖x‖ → f x = 0) (k : ℕ) :
    HasInversePowerDecay f k := by
  refine ⟨0,max 1 (R+1),le_rfl,le_max_left _ _,?_⟩
  filter_upwards [hf] with x hx hxx
  have hR : R+1 ≤ ‖x‖ := (le_max_right _ _).trans hxx
  rw [hx (by linarith),norm_zero,zero_div]

lemma hasInversePowerDecay_of_eventual {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {k : ℕ}
    (hf : ∃ C : ℝ, ∀ᶠ x : ℂ in cocompact ℂ, ‖f x‖ ≤ C*‖x‖⁻¹^k) :
    HasInversePowerDecay f k := by
  obtain ⟨D,R,hD,hR,hf⟩ := decay_to_radius hf
  exact ⟨D,R,hD,hR,ae_of_all _ hf⟩

lemma normalized_potential_decay {φ : ℂ → ℝ}
    (hd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ k φ z‖ ≤ C*‖z‖⁻¹^(k+1)) : HasInversePowerDecay φ 1 := by
  apply hasInversePowerDecay_of_eventual
  simpa only [Nat.zero_add,norm_iteratedFDeriv_zero] using hd 0

lemma normalized_potential_gradient_decay {φ : ℂ → ℝ} {w : ℂ → ℂ} {R : ℝ}
    (hd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ z in cocompact ℂ,
      ‖iteratedFDeriv ℝ k φ z‖ ≤ C*‖z‖⁻¹^(k+1))
    (hg : ∀ᵐ x ∂volume, R < ‖x‖ → gradient φ x = w x) : HasInversePowerDecay w 2 := by
  have hgd : HasInversePowerDecay (gradient φ) 2 := by
    apply hasInversePowerDecay_of_eventual
    obtain ⟨C,hC⟩ := hd 1
    refine ⟨C,?_⟩
    filter_upwards [hC] with x hx
    simpa only [norm_iteratedFDeriv_one,gradient,LinearIsometryEquiv.norm_map] using hx
  obtain ⟨D,S,hD,hS,hgd⟩ := hgd
  refine ⟨D,max S (R+1),hD,hS.trans (le_max_left _ _),?_⟩
  filter_upwards [hgd,hg] with x hx hy hxx
  have hR : R+1 ≤ ‖x‖ := (le_max_right _ _).trans hxx
  rw [← hy (by linarith)]
  exact hx ((le_max_left _ _).trans hxx)

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff

lemma memLp_plane_translate {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {f : ℂ → E}
    (hf : MemLp f p volume) (t : ℂ) : MemLp (fun x => f (x-t)) p volume := by
  simpa only [Function.comp_def] using hf.comp_measurePreserving
    (measurePreserving_sub_right (volume : Measure ℂ) t)

lemma HasInversePowerDecay.integrable_inner {G q : ℂ → ℂ}
    (hqD : HasInversePowerDecay q 2) (hq : MemLp q 2 volume)
    (hG : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp G 2 (volume.restrict U))
    {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0:ℂ) R, ‖G x‖^2) ≤ C*(1+R)) :
    Integrable (fun x => inner ℝ (G x) (q x)) volume := by
  obtain ⟨D,R,hD,hR,hqD⟩ := hqD
  exact integrable_interaction_of_growth_decay (fun R _ => hG _ isOpen_ball isBounded_ball)
    hq hC hD hR hg hqD

lemma integrate_translated_quadratic {p q : ℂ → ℂ}
    (hp : MemLp p 2 volume) (hq : MemLp q 2 volume) (t : ℂ) (σ : ℝ) :
    (∫ x : ℂ, ‖p (x-t)+σ • q (x-t)‖^2) = (∫ x : ℂ, ‖p x‖^2)+
      2*σ*(∫ x : ℂ, inner ℝ (p x) (q x))+σ^2*(∫ x : ℂ, ‖q x‖^2) := by
  rw [(measurePreserving_sub_right (volume : Measure ℂ) t).integral_comp
    (Homeomorph.subRight t).measurableEmbedding (fun x => ‖p x+σ • q x‖^2)]
  have hpI := hp.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hqI := hq.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hpqI := integrable_inner_memLp_measure hp hq
  have heq (x : ℂ) : ‖p x+σ • q x‖^2 = ‖p x‖^2+2*σ*inner ℝ (p x) (q x)+σ^2*‖q x‖^2 := by
    rw [norm_add_sq_real,norm_smul,Real.norm_eq_abs,inner_smul_right]
    nlinarith [sq_abs σ]
  simp_rw [heq]
  rw [integral_add (hpI.fun_add (hpqI.const_mul (2*σ))) (hqI.const_mul (σ^2)),
    integral_add hpI (hpqI.const_mul (2*σ)),integral_const_mul,integral_const_mul]

theorem translated_quadratic_comparison {v : Pair} (hv : GlobalAbsoluteMinimizer v)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsClosed B) (hH : v.K = A ∪ B)
    (hAB : Disjoint A B) {t : ℂ} (hAtB : Disjoint ((fun x => x+t) '' A) B)
    {f h k φ ψ : ℂ → ℝ} {G e d w z : ℂ → ℂ} (σ : ℝ)
    (hf : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn f G (U \ B))
    (hh : SobolevOn h e Aᶜ) (hk : SobolevOn k d Aᶜ)
    (hhc : IsCompact (essentialSupport h)) (hkc : IsCompact (essentialSupport k))
    (hφ : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn φ w U)
    (hψ : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → SobolevOn ψ z U)
    (heq : v.u =ᵐ[volume] fun x => f x+h x-φ x)
    (hgeq : v.grad =ᵐ[volume] fun x => G x+(e x-w x))
    (hp : MemLp (fun x => e x-w x) 2 volume) (hq : MemLp (fun x => d x-z x) 2 volume)
    (hpD : HasInversePowerDecay (fun x => e x-w x) 2)
    (hqD : HasInversePowerDecay (fun x => d x-z x) 2)
    (hφD : HasInversePowerDecay φ 1) (hψD : HasInversePowerDecay ψ 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ T : ℝ, 1 ≤ T → (∫ x in ball (0:ℂ) T, ‖G x‖^2) ≤ C*(1+T)) :
    0 ≤ 2*((∫ x : ℂ, inner ℝ (G x) (e (x-t)-w (x-t)))-
      (∫ x : ℂ, inner ℝ (G x) (e x-w x)))+
      2*σ*((∫ x : ℂ, inner ℝ (G x) (d (x-t)-z (x-t)))+
        (∫ x : ℂ, inner ℝ (e x-w x) (d x-z x)))+
      σ^2*(∫ x : ℂ, ‖d x-z x‖^2) := by
  have hH0 := volume_eq_zero_of_locally_finite_length hv.1.2.2.1
  have hB0 : volume B = 0 := measure_mono_null (by rw [hH]; exact subset_union_right) hH0
  have hG : ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → MemLp G 2 (volume.restrict U) := by
    intro U hU hb
    have h := (hf U hU hb).2.1
    rwa [restrict_diff_null_set hB0] at h
  have hpt := memLp_plane_translate hp t
  have hqt := memLp_plane_translate hq t
  have hpI := hpD.integrable_inner hp hG hC hgrowth
  have hptI := (hpD.translate t).integrable_inner hpt hG hC hgrowth
  have hqtI := (hqD.translate t).integrable_inner hqt hG hC hgrowth
  have hsumI : Integrable (fun x => inner ℝ (G x)
      ((e (x-t)-w (x-t))+σ • (d (x-t)-z (x-t)))) volume := by
    simpa only [inner_add_right,inner_smul_right] using hptI.fun_add (hqtI.const_mul σ)
  obtain ⟨D,R,hD,hR,haD⟩ := (hφD.sub (hφD.translate t)).sub ((hψD.translate t).smul σ)
  have hi := translated_comparison_limit hv hA hB hH hAB hAtB σ hf hh hk hhc hkc hφ hψ
    heq hgeq hp (hpt.add (hqt.const_smul σ)) hpI hsumI hC hD hR hgrowth
    (by simpa only [Real.norm_eq_abs,smul_eq_mul,pow_one] using haD)
  have hlin : (∫ x : ℂ, inner ℝ (G x) ((e (x-t)-w (x-t))+σ • (d (x-t)-z (x-t)))) =
      (∫ x : ℂ, inner ℝ (G x) (e (x-t)-w (x-t)))+
      σ*(∫ x : ℂ, inner ℝ (G x) (d (x-t)-z (x-t))) := by
    simp_rw [inner_add_right,inner_smul_right]
    rw [integral_add hptI (hqtI.const_mul σ),integral_const_mul]
  rw [hlin,integrate_translated_quadratic hp hq t σ] at hi
  linarith

end MumfordShah
end

end OAI
