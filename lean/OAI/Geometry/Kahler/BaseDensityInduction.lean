import OAI.Geometry.Kahler.BaseDensityScales

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

structure DensityStage (W : ℕ → Base → ℝ) (Q : ℕ) (c K : ℝ) (j : ℕ) : Prop where
  positive : ∀ ξ : Sphere, 0 < W j ξ
  horizontal : HorizontalBound (W j) (K*Real.sqrt ((Q:ℝ)^j))
  phase : ∀ ξ : Sphere, |phaseDerivative (W j) ξ| ≤ K*(Q:ℝ)^j*W j ξ
  step : ∀ i, j=i+1 → ∀ ξ : Sphere, c*W i ξ ≤ W j ξ ∧ W j ξ ≤ 2*W i ξ

lemma density_induction {Q N : ℕ} (hQ : 2 ≤ Q) {R E F B F₁ B₁ D c K : ℝ}
    (hR : 0 < R) (hER : E < R) (hQR : 2*R ≤ Q)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁)
    (hD1 : 1 ≤ D) (hDR : 2*Real.sqrt (2*R) ≤ D)
    (hc : 0 < c) (hc1 : 2*c ≤ 1) (hK : 0 ≤ K) (hN : 2/c ≤ (2:ℝ)^N)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0)
    (hfv : ∀ y, 0 ≤ y → |f y| ≤ F) (hbv : ∀ y, 0 ≤ y → |b y| ≤ B)
    (hfd : ∀ y, 0 ≤ y → |deriv f y| ≤ F₁) (hbd : ∀ y, 0 ≤ y → |deriv b y| ≤ B₁)
    (P : ℕ → Finset Sphere)
    (hdis : ∀ j, (P (Q^(j+1)):Set Sphere).PairwiseDisjoint (peakPatch (Q^(j+1)) R))
    (hH : Real.exp (K*D/Real.sqrt (Q:ℝ)+2*R/Q) ≤ 2)
    (hsmall : Real.exp (K*D/Real.sqrt (Q:ℝ)+2*R/Q)*(F+B*(K/Q)) ≤ 1-2*c)
    (hphase : K/Q ≤ 1)
    (hsecond : (2*(Real.exp K*(2/c))*4^N*Real.exp 2)/(Q:ℝ)^2 ≤ 1)
    (hderH : 2*D*(4*(F+B)+F₁+B₁)+K/Real.sqrt (Q:ℝ) ≤ K*c)
    (hderT : 2*D*(4*(F+B)+F₁+B₁)+K/Q ≤ K*c) :
    ∀ j, DensityStage (density Q R f b P) Q c K j := by
  have hQ0 : 0 < Q := by omega
  have hq : (0:ℝ) < Q := by exact_mod_cast hQ0
  have hD : 0 ≤ D := by linarith
  have hC : 0 ≤ 4*(F+B)+F₁+B₁ := by positivity
  let W := density Q R f b P
  have hsm : ∀ j, ContDiff ℝ ∞ (W j) := density_smooth hQ0 hER hf hb htail P
  have hfder : ∀ ξ : Base, fderiv ℝ (fun _ : Base => (1:ℝ)) ξ=0 := fun ξ => (hasFDerivAt_const (1:ℝ) ξ).fderiv
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      constructor
      · intro ξ; norm_num [W,density]
      · intro ξ v hv
        simp only [density,hfder,zero_apply,abs_zero,pow_zero,Real.sqrt_one,mul_one]
        positivity
      · intro ξ
        simp only [density,phaseDerivative,hfder,zero_apply,abs_zero,pow_zero,mul_one]
        exact hK
      · intro i hi; omega
    | succ j =>
      have old := ih j (Nat.lt_succ_self j)
      have hk : 0 < Q^(j+1) := pow_pos hQ0 _
      have hk0 : (0:ℝ) < (Q:ℝ)^(j+1) := pow_pos hq _
      have hsk : 0 < Real.sqrt ((Q:ℝ)^(j+1)) := Real.sqrt_pos.mpr hk0
      have hsQ : 0 < Real.sqrt (Q:ℝ) := Real.sqrt_pos.mpr hq
      have hkR : 2*R ≤ (Q^(j+1):ℕ) := by
        exact_mod_cast hQR.trans (density_degree_ge (by omega : 1 ≤ Q) j)
      have henv : ∀ p ∈ P (Q^(j+1)), ∀ ξ ∈ peakPatch (Q^(j+1)) R p,
          Real.exp (2*densityHeight (Q^(j+1)) p ξ/(Q^(j+1):ℕ))*W j (centralPoint p ξ) ≤
          Real.exp (K*D/Real.sqrt (Q:ℝ)+2*R/Q)*W j ξ := by
        intro p hp ξ ht
        have hh := density_central_envelope ((hsm j).differentiable (by simp)) old.positive
          (by positivity : 0 ≤ K*Real.sqrt ((Q:ℝ)^j)) old.horizontal hk hR hkR p ξ ht
        apply hh.trans
        apply mul_le_mul_of_nonneg_right _ (old.positive ξ).le
        apply Real.exp_le_exp.mpr
        simpa only [Nat.cast_pow] using density_envelope_bound (by omega : 1 ≤ Q) hK hR.le hDR j
      have henv2 : ∀ p ∈ P (Q^(j+1)), ∀ ξ ∈ peakPatch (Q^(j+1)) R p,
          Real.exp (2*densityHeight (Q^(j+1)) p ξ/(Q^(j+1):ℕ))*W j (centralPoint p ξ) ≤ 2*W j ξ := by
        intro p hp ξ ht
        exact (henv p hp ξ ht).trans (mul_le_mul_of_nonneg_right hH (old.positive ξ).le)
      have hTscaled : ∀ ξ : Sphere, |phaseDerivative (W j) ξ| ≤ (Q^(j+1):ℕ)*(K/Q)*W j ξ := by
        intro ξ
        simpa only [Nat.cast_pow,density_phase_scale hQ0 K j] using old.phase ξ
      have hT : ∀ ξ : Sphere, |phaseDerivative (W j) ξ| ≤ (Q^(j+1):ℕ)*W j ξ := by
        intro ξ
        apply (hTscaled ξ).trans
        simp only [Nat.cast_pow]
        exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hphase hk0.le).trans_eq (mul_one _)) (old.positive ξ).le
      have hTT : ∀ ξ : Sphere, |phaseDerivative (phaseDerivative (W j)) ξ| ≤ ((Q^(j+1):ℕ):ℝ)^2*W j ξ := by
        intro ξ
        have hh := phase_second_from_steps hQ hc (by linarith) hK hN W rfl
          (fun i hi => hsm i) (fun i hi => (ih i (by omega)).positive)
          (fun i hi => (ih i (by omega)).phase)
          (fun i hi => (ih (i+1) (by omega)).step i rfl)
          (density_bandwidth hQ0 hER hf hb htail P j) ξ
        have he := density_second_scale hQ0 (2*(Real.exp K*(2/c))*4^N*Real.exp 2) j
        rw [← he] at hh
        apply hh.trans
        simp only [Nat.cast_pow]
        have hp := (old.positive ξ).le
        exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)).trans_eq (mul_one _)) hp
      have hval : ∀ ξ : Sphere, 0 < W (j+1) ξ ∧ c*W j ξ ≤ W (j+1) ξ ∧ W (j+1) ξ ≤ 2*W j ξ := by
        intro ξ
        exact density_update_value hk f b (W j) hF hB (by positivity : 0 ≤ K/Q) hc hc1 old.positive hTscaled hfv hbv
          (P (Q^(j+1))) (hdis j) henv hsmall ξ
      constructor
      · intro ξ; exact (hval ξ).1
      · intro ξ v hv
        have hdir : ∀ p ∈ P (Q^(j+1)), ξ ∈ peakPatch (Q^(j+1)) R p →
            ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ (D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖)/(Q^(j+1):ℕ) := by
          intro p hp ht
          simpa only [Nat.cast_pow] using horizontal_direction_ratio hk hR hkR hDR p ξ ht v hv
        have hh := density_update_direction hk hER hf hb (hsm j) htail hF hB hF₁ hB₁
          (by positivity : 0 ≤ D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖) (by norm_num : (0:ℝ) ≤ 2)
          old.positive hT hTT hfv hbv hfd hbd (P (Q^(j+1))) (hdis j) ξ v hdir (fun p hp ht => henv2 p hp ξ ht)
        have hx := old.horizontal ξ v hv
        have he : K*Real.sqrt ((Q:ℝ)^j)*‖v‖*W j ξ+
            (D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖)*2*(4*(F+B)+F₁+B₁)*W j ξ =
            (2*D*(4*(F+B)+F₁+B₁)+K/Real.sqrt (Q:ℝ))*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖*W j ξ := by
          rw [density_sqrt_scale hQ0 j]
          field_simp
          ring
        calc
          _ ≤ |fderiv ℝ (W j) ξ v|+(D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖)*2*(4*(F+B)+F₁+B₁)*W j ξ := hh
          _ ≤ K*Real.sqrt ((Q:ℝ)^j)*‖v‖*W j ξ+(D*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖)*2*(4*(F+B)+F₁+B₁)*W j ξ := add_le_add hx le_rfl
          _ = _ := he
          _ ≤ (K*c)*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖*W j ξ := by gcongr; exact (old.positive ξ).le
          _ = K*Real.sqrt ((Q:ℝ)^(j+1))*‖v‖*(c*W j ξ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hval ξ).2.1 (by positivity)
      · intro ξ
        have hdir : ∀ p ∈ P (Q^(j+1)), ξ ∈ peakPatch (Q^(j+1)) R p →
            ‖bracket (Complex.I • (ξ:Base)) (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ (D*(Q:ℝ)^(j+1))/(Q^(j+1):ℕ) := by
          intro p hp ht
          rw [phase_direction_ratio p ξ (norm_pos_iff.mp (peakPatch_norm_pos ht))]
          simp only [Nat.cast_pow]
          rw [mul_div_cancel_right₀ D hk0.ne']
          exact hD1
        have hh := density_update_direction hk hER hf hb (hsm j) htail hF hB hF₁ hB₁
          (by positivity : 0 ≤ D*(Q:ℝ)^(j+1)) (by norm_num : (0:ℝ) ≤ 2)
          old.positive hT hTT hfv hbv hfd hbd (P (Q^(j+1))) (hdis j) ξ (Complex.I • (ξ:Base)) hdir (fun p hp ht => henv2 p hp ξ ht)
        have hx := old.phase ξ
        have he : K*(Q:ℝ)^j*W j ξ+(D*(Q:ℝ)^(j+1))*2*(4*(F+B)+F₁+B₁)*W j ξ =
            (2*D*(4*(F+B)+F₁+B₁)+K/Q)*(Q:ℝ)^(j+1)*W j ξ := by
          rw [pow_succ]
          field_simp
          ring
        calc
          _ ≤ |phaseDerivative (W j) ξ|+(D*(Q:ℝ)^(j+1))*2*(4*(F+B)+F₁+B₁)*W j ξ := hh
          _ ≤ K*(Q:ℝ)^j*W j ξ+(D*(Q:ℝ)^(j+1))*2*(4*(F+B)+F₁+B₁)*W j ξ := add_le_add hx le_rfl
          _ = _ := he
          _ ≤ (K*c)*(Q:ℝ)^(j+1)*W j ξ := by gcongr; exact (old.positive ξ).le
          _ = K*(Q:ℝ)^(j+1)*(c*W j ξ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hval ξ).2.1 (by positivity)
      · intro i hi ξ
        have he : i=j := by omega
        subst i
        exact (hval ξ).2

end PinchedHartogs.BaseConstruction

end

end OAI
