import OAI.MeasureTheory.Falconer.Angular.SelectedAngularBins
import OAI.MeasureTheory.Falconer.Estimates.ScaleUniformNonstationary
import OAI.MeasureTheory.Falconer.Geometry.CompactMultiplierScale

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem complex_mul_derivative_scale {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C B D E : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (j : ℕ) (x : ℝ)
    (hbf : ∀ k ≤ j, ‖iteratedDeriv k f x‖ ≤ C*D^k)
    (hbg : ∀ k ≤ j, ‖iteratedDeriv k g x‖ ≤ B*E^k) :
    ‖iteratedDeriv j (fun y => f y*g y) x‖ ≤ C*B*(D+E)^j := by
  have hf' : ContDiffAt ℝ j f x :=
    (hf.of_le (WithTop.coe_le_coe.mpr (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
  have hg' : ContDiffAt ℝ j g x :=
    (hg.of_le (WithTop.coe_le_coe.mpr (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
  rw [iteratedDeriv_fun_mul hf' hg', add_pow, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (j.choose k : ℝ) * (C*D^k) * (B*E^(j-k)) := by
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hbf k hk') (Nat.cast_nonneg _)
          (mul_nonneg hC (pow_nonneg hD _)))
        (hbg (j-k) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hB (pow_nonneg hE _))
    _ = _ := by ring

noncomputable def selectedBinAmplitude (δ : ℝ) (S : Finset ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun θ => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ : ℝ) : ℂ)*f θ

theorem selectedBinAmplitude_contDiff (δ : ℝ) (S : Finset ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (selectedBinAmplitude δ S f) :=
  (Complex.ofRealCLM.contDiff.comp
    (ContDiff.sum (fun k _ => periodicAngularBin_contDiff _ k))).mul hf

theorem selectedBinAmplitude_derivatives (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ, 0 < δ → δ ≤ 2*Real.pi → ∀ S : Finset ℕ,
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ {C D : ℝ}, 0 ≤ C → 0 ≤ D →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ∀ j ≤ n, ∀ x, ‖iteratedDeriv j (selectedBinAmplitude δ S f) x‖ ≤
      A*C*(max D δ⁻¹)^j := by
  choose Q hQ hbQ using selectedAngularBins_scale_derivatives
  let B := ∑ j ∈ Finset.range (n+1), Q j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hQ j)
  refine ⟨B*2^n, by positivity, ?_⟩
  intro δ hδ hcap S f hf C D hC hD hb j hj x
  let g : ℝ → ℝ := fun θ => ∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ
  have hg : ContDiff ℝ ∞ g := ContDiff.sum (fun k _ => periodicAngularBin_contDiff _ k)
  have hbg : ∀ k ≤ j, ‖iteratedDeriv k (fun y => (g y : ℂ)) x‖ ≤ B*δ⁻¹^k := by
    intro k hk
    rw [iteratedDeriv_ofReal hg, Complex.norm_real]
    have hQB : Q k ≤ B := Finset.single_le_sum (fun l _ => hQ l)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hk.trans hj)))
    exact (hbQ k δ hδ hcap S x).trans
      (mul_le_mul_of_nonneg_right hQB (by positivity))
  have hm := complex_mul_derivative_scale (Complex.ofRealCLM.contDiff.comp hg) hf
    hB hC (inv_nonneg.mpr hδ.le) hD j x hbg (fun k hk => hb k (hk.trans hj) x)
  apply hm.trans
  have hscale : δ⁻¹+D ≤ 2*max D δ⁻¹ := by
    have h1 := le_max_left D δ⁻¹
    have h2 := le_max_right D δ⁻¹
    linarith
  calc
    _ ≤ B*C*(2*max D δ⁻¹)^j := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hscale j) (mul_nonneg hB hC)
    _ = (B*2^j)*C*(max D δ⁻¹)^j := by rw [mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (hD.trans (le_max_left _ _)) _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) hB) hC

theorem selectedBinAmplitude_nonstationary {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {a b : ℝ} (hab : a ≤ b) (hsw : tsupport w ⊆ Icc a b)
    (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ, 0 < δ → δ ≤ 1 → ∀ S : Finset ℕ,
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    (∀ x ∈ tsupport (fun y => w y * selectedBinAmplitude δ S f y), δ ≤ |Real.sin x|) →
    ∀ {C D Λ : ℝ}, 0 ≤ C → 0 ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ x * (w x * selectedBinAmplitude δ S f x)‖ ≤
      A*C*(max D δ⁻¹/(Λ*δ))^n := by
  obtain ⟨B,hB,hbin⟩ := selectedBinAmplitude_derivatives n
  obtain ⟨W,hW,hweight⟩ := compact_multiplier_uniform_derivatives hw isCompact_Icc hsw n
  obtain ⟨A,hA,hnon⟩ := angular_nonstationary_max_scale hab n
  refine ⟨A*(W*B), by positivity, ?_⟩
  intro δ hδ hcap S f hf haway C D Λ hC hD hΛ hb
  have hg := selectedBinAmplitude_contDiff δ S hf
  have hδπ : δ ≤ 2*Real.pi := hcap.trans (by have := Real.one_le_pi_div_two; linarith)
  have hbin' := hbin δ hδ hδπ S hf hC hD hb
  have hd : 1 ≤ max D δ⁻¹ := ((one_le_inv₀ hδ).mpr hcap).trans (le_max_right _ _)
  have hh := hweight hg (mul_nonneg hB hC) hd hbin'
  have hs : tsupport (fun y => w y * selectedBinAmplitude δ S f y) ⊆ Icc a b :=
    tsupport_mul_subset_left.trans hsw
  have hi := hnon δ hδ hcap (hw.mul hg) hs haway
    (mul_nonneg hW (mul_nonneg hB hC)) hΛ (fun k hk x _ => hh k hk x)
  apply hi.trans_eq
  ring

end PlanarFalconer

end OAI
