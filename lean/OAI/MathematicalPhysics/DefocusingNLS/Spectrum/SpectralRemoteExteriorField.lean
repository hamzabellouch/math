import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteJetOperations
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationSubunit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialODEGrowthRegularity

namespace OAI

/-! Uniform fixed-order derivatives of the true exterior ODE field on a
subunit position ball with bounded velocity. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

noncomputable def spectralRemoteExteriorSkew : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  (0 : (ℂ × ℂ) →L[ℝ] ℂ).prod
    ((-Complex.I/2) • ContinuousLinearMap.snd ℝ ℂ ℂ)

private theorem field_split (nu : ℂ) (n : ℕ) :
    Function.uncurry (radialExteriorODEField nu n) = fun x : ℝ × (ℂ × ℂ) =>
      Real.exp (2*x.1) • spectralRemoteExteriorSkew x.2 +
        radialExteriorErrorMatrix nu x.2 +
        (ContinuousLinearMap.inr ℝ ℂ ℂ) (oddPowerNonlinearity n x.2.1) := by
  funext x
  rw [Function.uncurry_apply_pair,radialExteriorODEField_split]
  congr 2
  apply Prod.ext
  · simp [spectralRemoteExteriorSkew]
  · change -Complex.I*(Real.exp (2*x.1)/2 : ℝ)*x.2.2 =
      (Real.exp (2*x.1) : ℂ)*((-Complex.I/2)*x.2.2)
    push_cast
    ring

private theorem odd_jet (n k : ℕ) (x : ℝ × (ℂ × ℂ))
    (h : ‖iteratedFDeriv ℝ k (oddPowerNonlinearity n) x.2.1‖ ≤ 1) :
    ‖iteratedFDeriv ℝ k (fun y : ℝ × (ℂ × ℂ) =>
      (ContinuousLinearMap.inr ℝ ℂ ℂ) (oddPowerNonlinearity n y.2.1)) x‖ ≤ 1 := by
  let R : (ℝ × (ℂ × ℂ)) →L[ℝ] ℂ :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℂ))
  have hR : ‖R‖ ≤ 1 :=
    ((ContinuousLinearMap.fst ℝ ℂ ℂ).opNorm_comp_le _).trans
      ((mul_le_mul (ContinuousLinearMap.norm_fst_le ..)
        (ContinuousLinearMap.norm_snd_le ..) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hN : ContDiff ℝ ∞ (oddPowerNonlinearity n) :=
    (contDiff_oddPowerNonlinearity n).of_le le_top
  have hh := (ContinuousLinearMap.inr ℝ ℂ ℂ).norm_iteratedFDeriv_comp_left (x := x)
    (hN.comp R.contDiff).contDiffAt (by simp : (k : ℕ∞ω) ≤ ∞)
  have hJ : ‖ContinuousLinearMap.inr ℝ ℂ ℂ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp
  have hr := (spectralRemote_right_jet R hR _ hN x k).trans h
  apply hh.trans
  exact (mul_le_mul hJ hr (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

private theorem field_jet_bound (nu : ℂ) (n k : ℕ) (x : ℝ × (ℂ × ℂ))
    (M U : ℝ) (hM : 1 ≤ M) (hU : 0 ≤ U) (hx : ‖x.2‖ ≤ M) (ht : 0 ≤ x.1)
    (hA : ‖radialExteriorErrorMatrix nu‖ ≤ U)
    (hN : ‖iteratedFDeriv ℝ k (oddPowerNonlinearity n) x.2.1‖ ≤ 1) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (radialExteriorODEField nu n)) x‖ ≤
      (((∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*2^i)*
        ‖spectralRemoteExteriorSkew‖*M)+U*M+1)*Real.exp (2*x.1) := by
  have he : ContDiff ℝ ∞ (fun y : ℝ × (ℂ × ℂ) =>
      Real.exp (2*y.1) • spectralRemoteExteriorSkew y.2) := by fun_prop
  have ha : ContDiff ℝ ∞ (fun y : ℝ × (ℂ × ℂ) => radialExteriorErrorMatrix nu y.2) := by
    fun_prop
  have hn : ContDiff ℝ ∞ (fun y : ℝ × (ℂ × ℂ) =>
      (ContinuousLinearMap.inr ℝ ℂ ℂ) (oddPowerNonlinearity n y.2.1)) := by
    exact (ContinuousLinearMap.inr ℝ ℂ ℂ).contDiff.comp
      (((contDiff_oddPowerNonlinearity n).of_le (show (∞ : ℕ∞ω) ≤ ⊤ from le_top)).comp
        (contDiff_snd.fst))
  rw [field_split,fun_iteratedFDeriv_add_apply ((he.add ha).contDiffAt.of_le (by simp))
    (hn.contDiffAt.of_le (by simp)),
    fun_iteratedFDeriv_add_apply (he.contDiffAt.of_le (by simp)) (ha.contDiffAt.of_le (by simp))]
  have hl := (spectralRemote_state_linear_jet (radialExteriorErrorMatrix nu) x M hM hx k).trans
    (mul_le_mul_of_nonneg_right hA (by linarith))
  have hnl := odd_jet n k x hN
  have hexp : 1 ≤ Real.exp (2*x.1) := Real.one_le_exp_iff.mpr (by positivity)
  calc
    _ ≤ (‖iteratedFDeriv ℝ k (fun y : ℝ × (ℂ × ℂ) =>
          Real.exp (2*y.1) • spectralRemoteExteriorSkew y.2) x‖ +
        ‖iteratedFDeriv ℝ k (fun y : ℝ × (ℂ × ℂ) => radialExteriorErrorMatrix nu y.2) x‖) +
        ‖iteratedFDeriv ℝ k (fun y : ℝ × (ℂ × ℂ) =>
          (ContinuousLinearMap.inr ℝ ℂ ℂ) (oddPowerNonlinearity n y.2.1)) x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (((∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*2^i)*
        ‖spectralRemoteExteriorSkew‖*M)*Real.exp (2*x.1)+U*M)+1 :=
      add_le_add (add_le_add (spectralRemote_time_linear_jet _ x M hM hx k) hl) hnl
    _ ≤ _ := by nlinarith [mul_nonneg hU (show 0 ≤ M by linarith)]

theorem spectralRemote_exterior_field_jets (nu : ℕ → ℂ) (nu0 : ℂ)
    (hnu : Tendsto nu atTop (𝓝 nu0)) (Z : ℕ → ℝ → ℂ × ℂ)
    (L rho M : ℝ) (hL : 0 ≤ L) (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hM : 1 ≤ M)
    (hZ : ∀ᶠ n in atTop, ∀ t ∈ Ioi L, ‖Z n t‖ ≤ M ∧ ‖(Z n t).1‖ ≤ rho) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioi L, ∀ i ≤ k,
      ‖iteratedFDeriv ℝ i (Function.uncurry (radialExteriorODEField (nu n) n)) (t,Z n t)‖ ≤
        C*Real.exp (2*t) := by
  have hm : Tendsto (fun n => radialExteriorMatrixBound (nu n)) atTop
      (𝓝 (radialExteriorMatrixBound nu0)) := by
    have hc : Continuous radialExteriorMatrixBound := by unfold radialExteriorMatrixBound; fun_prop
    exact hc.continuousAt.tendsto.comp hnu
  let U := radialExteriorMatrixBound nu0+1
  have hU : 0 ≤ U := by dsimp only [U]; linarith [radialExteriorMatrixBound_pos nu0]
  have hAb : ∀ᶠ n in atTop, ‖radialExteriorErrorMatrix (nu n)‖ ≤ U := by
    filter_upwards [hm.eventually (gt_mem_nhds (show radialExteriorMatrixBound nu0 < U from by dsimp only [U]; linarith))] with n hn
    exact (ContinuousLinearMap.opNorm_le_bound _ (radialExteriorMatrixBound_pos _).le
      (radialExteriorErrorMatrix_norm _)).trans hn.le
  intro k
  let B := fun i : ℕ => ((∑ j ∈ Finset.range (i+1), (i.choose j : ℝ)*2^j)*
      ‖spectralRemoteExteriorSkew‖*M)+U*M+1
  have hB : ∀ i, 0 ≤ B i := by intro i; dsimp only [B]; positivity
  refine ⟨∑ i ∈ Finset.range (k+1), B i,Finset.sum_nonneg (fun i _ => hB i),?_⟩
  have hNs : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k+1), ∀ z : ℂ, ‖z‖ ≤ rho →
      ‖iteratedFDeriv ℝ i (oddPowerNonlinearity n) z‖ ≤ 1 := by
    apply (eventually_all_finset _).mpr
    intro i hi
    exact (homogeneous_oddPower_derivatives_subunit i rho hrho hrho1 1 (by norm_num)).mono
      (fun n hn z hz => (hn z hz).le)
  filter_upwards [hZ,hAb,hNs] with n hn hAn hNn
  intro t ht i hi
  have him : i ∈ Finset.range (k+1) := Finset.mem_range.mpr (by omega)
  have hb := field_jet_bound (nu n) n i (t,Z n t) M U hM hU (hn t ht).1
    (hL.trans ht.le) hAn (hNn i him _ (hn t ht).2)
  exact hb.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hB j) him) (Real.exp_nonneg _))

end DefocusingNLS

end OAI
