import OAI.Analysis.LipschitzHilbert.Fourier.LineProductSpectrum

namespace OAI

/-! An elementary fourth-power bound for the difference of positive and
negative frequency Schwartz functions. The proof uses only Plancherel,
frequency support of products, and a scalar quadratic inequality. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_positive (a b : SchwartzMap ℝ ℂ)
    (ha : ∀ eta, eta≤0 → (𝓕 a : SchwartzMap ℝ ℂ) eta=0)
    (hb : ∀ eta, eta≤0 → (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    ∀ eta, eta≤0 → (𝓕 (lineSchwartzProduct a b) : SchwartzMap ℝ ℂ) eta=0 := by
  intro eta he
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : t≤0
  · exact Or.inl (ha t ht)
  · exact Or.inr (hb (eta-t) (by linarith))

theorem lineSchwartzProduct_negative (a b : SchwartzMap ℝ ℂ)
    (ha : ∀ eta, 0≤eta → (𝓕 a : SchwartzMap ℝ ℂ) eta=0)
    (hb : ∀ eta, 0≤eta → (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    ∀ eta, 0≤eta → (𝓕 (lineSchwartzProduct a b) : SchwartzMap ℝ ℂ) eta=0 := by
  intro eta he
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : 0≤t
  · exact Or.inl (ha t ht)
  · exact Or.inr (hb (eta-t) (by linarith))

theorem schwartz_disjoint_energy_add_sub (a b : SchwartzMap ℝ ℂ)
    (h : ∀ eta, (𝓕 a : SchwartzMap ℝ ℂ) eta=0 ∨ (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    (∫ x, ‖(a+b) x‖^2)=(∫ x, ‖(a-b) x‖^2) := by
  rw [←SchwartzMap.integral_norm_sq_fourier (a+b),
    ←SchwartzMap.integral_norm_sq_fourier (a-b)]
  apply integral_congr_ae
  filter_upwards [] with eta
  simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,
    add_apply,neg_apply]
  rcases h eta with ha | hb
  · rw [ha,zero_add,zero_add,norm_neg]
  · rw [hb,add_zero,neg_zero,add_zero]

theorem hardyPair_fourth_power (a b : SchwartzMap ℝ ℂ)
    (ha : ∀ eta, eta≤0 → (𝓕 a : SchwartzMap ℝ ℂ) eta=0)
    (hb : ∀ eta, 0≤eta → (𝓕 b : SchwartzMap ℝ ℂ) eta=0) :
    (∫ x, ‖(a-b) x‖^4)≤68*(∫ x, ‖(a+b) x‖^4) := by
  let f := a+b
  let g := a-b
  let H := lineSchwartzProduct a a+lineSchwartzProduct b b
  let Q := lineSchwartzProduct a a-lineSchwartzProduct b b
  have horth : (∫ x, ‖H x‖^2)=(∫ x, ‖Q x‖^2) := by
    apply schwartz_disjoint_energy_add_sub
    intro eta
    by_cases he : eta≤0
    · exact Or.inl (lineSchwartzProduct_positive a a ha ha eta he)
    · exact Or.inr (lineSchwartzProduct_negative b b hb hb eta (by linarith))
  have hidentity (x : ℝ) : g x*g x=2*H x-f x*f x := by
    simp only [f,g,H,add_apply,sub_apply,lineSchwartzProduct_apply]
    ring
  have hQ (x : ℝ) : Q x=f x*g x := by
    simp only [Q,f,g,add_apply,sub_apply,lineSchwartzProduct_apply]
    ring
  have hpoint (x : ℝ) : ‖g x‖^4≤8*‖H x‖^2+2*‖f x‖^4 := by
    have hn := norm_sub_le (2*H x) (f x*f x)
    rw [←hidentity,norm_mul,norm_mul,norm_mul] at hn
    norm_num at hn
    have hs := sq_nonneg (2*‖H x‖-‖f x‖^2)
    nlinarith [sq_nonneg (‖g x‖^2-(2*‖H x‖+‖f x‖^2))]
  have hQpoint (x : ℝ) : ‖Q x‖^2≤(1/16:ℝ)*‖g x‖^4+4*‖f x‖^4 := by
    rw [hQ,norm_mul,mul_pow]
    nlinarith [sq_nonneg (‖g x‖^2/4-2*‖f x‖^2)]
  have hf : Integrable (fun x => ‖f x‖^4) :=
    (f.memLp 4 volume).integrable_norm_pow (by decide)
  have hg : Integrable (fun x => ‖g x‖^4) :=
    (g.memLp 4 volume).integrable_norm_pow (by decide)
  have hH : Integrable (fun x => ‖H x‖^2) :=
    (H.memLp 2 volume).integrable_norm_pow (by decide)
  have hQi : Integrable (fun x => ‖Q x‖^2) :=
    (Q.memLp 2 volume).integrable_norm_pow (by decide)
  have hi := integral_mono hg ((hH.const_mul 8).add (hf.const_mul 2)) hpoint
  have hqi := integral_mono hQi ((hg.const_mul (1/16)).add (hf.const_mul 4)) hQpoint
  simp only [Pi.add_apply] at hi hqi
  rw [integral_add (hH.const_mul 8) (hf.const_mul 2),integral_const_mul,integral_const_mul,
    horth] at hi
  rw [integral_add (hg.const_mul (1/16)) (hf.const_mul 4),integral_const_mul,
    integral_const_mul] at hqi
  change (∫ x, ‖g x‖^4)≤68*(∫ x, ‖f x‖^4)
  linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
