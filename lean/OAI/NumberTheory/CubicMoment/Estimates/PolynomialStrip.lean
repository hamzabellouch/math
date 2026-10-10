import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Polynomial strip growth from finite order and polynomial boundary
bounds. The finite-order hypothesis is much weaker than the conclusion;
the proof uses the Phragmén–Lindelöf theorem in mathlib. -/

noncomputable section
open Set Filter Asymptotics
namespace CubicFirstMoment

/-- A finite-order bound restricted to a closed vertical strip. -/
def FiniteVerticalOrder (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
    ‖f z‖ ≤ Real.exp (C*(1+|z.im|)^k)

lemma finiteVerticalOrder_double_exp {f : ℂ → ℂ} {a b c : ℝ}
    (hf : FiniteVerticalOrder f a b) (hc : 0 < c) :
    f =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)]
      (fun z : ℂ => Real.exp (Real.exp (c*|z.im|))) := by
  obtain ⟨C,k,hC,hf⟩ := hf
  have he := ((isLittleO_pow_exp_pos_mul_atTop k hc).const_mul_left (C*2^k)).bound
    (by norm_num : (0:ℝ) < 1)
  have hlarge : ∀ᶠ u : ℝ in atTop,
      C*(1+u)^k ≤ Real.exp (c*u) := by
    filter_upwards [he,eventually_ge_atTop (1:ℝ)] with u hu hu1
    have hu0 : 0 ≤ u := le_trans zero_le_one hu1
    have hpow : (1+u)^k ≤ (2*u)^k := pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      C*(1+u)^k ≤ C*(2*u)^k := mul_le_mul_of_nonneg_left hpow hC
      _ = (C*2^k)*u^k := by rw [mul_pow]; ring
      _ ≤ Real.exp (c*u) := by
        exact (le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul] using hu)
  apply IsBigO.of_bound' 
  have hlarge' := ((tendsto_comap : Tendsto (abs ∘ Complex.im) (comap (abs ∘ Complex.im) atTop) atTop).eventually hlarge).filter_mono (inf_le_left :
    comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b) ≤
      comap (abs ∘ Complex.im) atTop)
  have hs : ∀ᶠ z : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Ioo a b), z.re ∈ Ioo a b :=
    Filter.Eventually.filter_mono inf_le_right (by simp)
  filter_upwards [hlarge',hs] with z hz hzstrip
  exact (hf z ⟨hzstrip.1.le,hzstrip.2.le⟩).trans <| by
    simpa using Real.exp_le_exp.mpr hz

private lemma strip_shift_norm_lower {a : ℝ} {z : ℂ} (hz : a ≤ z.re) :
    1 ≤ ‖z+((1-a:ℝ):ℂ)‖ := by
  have hr := Complex.re_le_norm (z+((1-a:ℝ):ℂ))
  simp only [Complex.add_re,Complex.ofReal_re] at hr
  linarith

private lemma strip_shift_norm_upper {a b : ℝ} {z : ℂ}
    (hz : z.re ∈ Icc a b) :
    ‖z+((1-a:ℝ):ℂ)‖ ≤ (b-a+1)*(1+|z.im|) := by
  have hn := Complex.norm_le_abs_re_add_abs_im (z+((1-a:ℝ):ℂ))
  simp only [Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,add_zero] at hn
  rw [abs_of_nonneg (by linarith [hz.1] : 0 ≤ z.re+(1-a))] at hn
  nlinarith [abs_nonneg z.im,hz.1,hz.2]

/-- A finite-order holomorphic function with polynomial bounds on both
vertical edges has polynomial growth throughout the strip. -/
theorem polynomial_strip_of_finite_order {f : ℂ → ℂ} {a b C : ℝ}
    (hab : a < b) (hfd : Differentiable ℂ f) (hf : FiniteVerticalOrder f a b)
    (hC : 0 ≤ C) (n : ℕ)
    (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C*(1+|z.im|)^n)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C*(1+|z.im|)^n) :
    ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ (C*2^n*(b-a+1)^n)*(1+|z.im|)^n := by
  let g (z : ℂ) := f z/(z+((1-a:ℝ):ℂ))^n
  have hcl : closure (Complex.re ⁻¹' Ioo a b) ⊆ Complex.re ⁻¹' Icc a b := by
    apply closure_minimal
    · intro z hz
      exact ⟨hz.1.le,hz.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hne {z : ℂ} (hz : a ≤ z.re) : z+((1-a:ℝ):ℂ) ≠ 0 := by
    have hn := strip_shift_norm_lower hz
    intro he
    rw [he,norm_zero] at hn
    norm_num at hn
  have hgd : DiffContOnCl ℂ g (Complex.re ⁻¹' Ioo a b) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    exact (hfd z).differentiableWithinAt.div
      (((differentiable_id.add_const ((1-a:ℝ):ℂ)).pow n) z).differentiableWithinAt
      (pow_ne_zero _ (hne (hcl hz).1))
  have hgnorm {z : ℂ} (hz : a ≤ z.re) : ‖g z‖ ≤ ‖f z‖ := by
    dsimp [g]
    rw [norm_div,norm_pow]
    exact div_le_self (_root_.norm_nonneg _) (one_le_pow₀ (strip_shift_norm_lower hz))
  have hgf : FiniteVerticalOrder g a b := by
    obtain ⟨D,k,hD,hf⟩ := hf
    exact ⟨D,k,hD,fun z hz => (hgnorm hz.1).trans (hf z hz)⟩
  have hboundary {z : ℂ} (hz : z.re ∈ Icc a b)
      (hfz : ‖f z‖ ≤ C*(1+|z.im|)^n) : ‖g z‖ ≤ C*2^n := by
    have hn := strip_shift_norm_lower hz.1
    have hi : |z.im| ≤ ‖z+((1-a:ℝ):ℂ)‖ := by
      simpa using Complex.abs_im_le_norm (z+((1-a:ℝ):ℂ))
    have hpow : (1+|z.im|)^n ≤ (2*‖z+((1-a:ℝ):ℂ)‖)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    dsimp [g]
    rw [norm_div,norm_pow]
    apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hn) _)).mpr
    calc
      ‖f z‖ ≤ C*(1+|z.im|)^n := hfz
      _ ≤ C*(2*‖z+((1-a:ℝ):ℂ)‖)^n := mul_le_mul_of_nonneg_left hpow hC
      _ = _ := by rw [mul_pow]; ring
  have hc : 0 < Real.pi/(2*(b-a)) := div_pos Real.pi_pos (by linarith)
  have hcb : Real.pi/(2*(b-a)) < Real.pi/(b-a) := by
    apply div_lt_div_of_pos_left Real.pi_pos (by linarith) (by linarith)
  intro z hz
  have hg : ‖g z‖ ≤ C*2^n := PhragmenLindelof.vertical_strip hgd
    ⟨Real.pi/(2*(b-a)),hcb,1,by
      simpa only [one_mul] using finiteVerticalOrder_double_exp hgf hc⟩
    (fun w hw => hboundary ⟨hw.ge,hw ▸ hab.le⟩ (ha w hw))
    (fun w hw => hboundary ⟨hw ▸ hab.le,hw.le⟩ (hb w hw)) hz.1 hz.2
  have hfeq : ‖f z‖ = ‖g z‖*‖z+((1-a:ℝ):ℂ)‖^n := by
    dsimp [g]
    rw [norm_div,norm_pow,div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr (hne hz.1)))]
  rw [hfeq]
  calc
    _ ≤ (C*2^n)*((b-a+1)*(1+|z.im|))^n :=
      mul_le_mul hg (pow_le_pow_left₀ (_root_.norm_nonneg _) (strip_shift_norm_upper hz) n)
        (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI
