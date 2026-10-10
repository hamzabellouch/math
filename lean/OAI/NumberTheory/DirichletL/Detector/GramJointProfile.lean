import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Detector.GramLatticeDecay
import OAI.NumberTheory.DirichletL.Detector.GramAnnularLattice
import OAI.NumberTheory.DirichletL.Detector.GramJointConstruction

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set FourierBridge
namespace ProbeGramJointProfile
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

def rayControl (B n : ℕ) (g : 𝓢(ℝ, ℂ)) : ℝ :=
  (Finset.Iic (2*B+n,n)).sup (schwartzSeminormFamily ℝ ℝ ℂ) g

lemma rayControl_nonneg (B n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    0 ≤ rayControl B n g := apply_nonneg _ _

lemma mul_derivative_bound {f g : Joint → ℂ} (n : ℕ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Joint)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hfb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2^n*C*D := by
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x (by simp)
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hfb i (Finset.mem_range_succ_iff.mp hi)) (by positivity))
        (hgb (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

lemma compact_derivatives {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set Joint} (hK : IsCompact K) {f : Joint → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
    obtain ⟨D, hD⟩ := hK.bddAbove_image
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.continuousOn
    exact ⟨D, fun x hx => hD (Set.mem_image_of_mem _ hx)⟩
  choose D hD using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n+1), |D i|, by
    have hn : 0 ≤ ∑ i ∈ Finset.range (n+1), |D i| := by positivity
    linarith, ?_⟩
  intro i hi x hx
  have hs : |D i| ≤ ∑ j ∈ Finset.range (n+1), |D j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_range.mpr (by omega))
  exact (hD i x hx).trans ((le_abs_self _).trans (by linarith))

lemma compact_positive_margin {K : Set Joint} (hK : IsCompact K)
    {h : Joint → ℝ} (hc : Continuous h) (hp : ∀ x ∈ K, 0 < h x) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, m ≤ h x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hm⟩ := hK.exists_isMinOn hne hc.continuousOn
    exact ⟨min 1 (h x), lt_min zero_lt_one (hp x hx), min_le_left _ _,
      fun y hy => (min_le_right _ _).trans (hm hy)⟩
  · exact ⟨1, zero_lt_one, le_rfl, fun x hx => False.elim (hne ⟨x,hx⟩)⟩

lemma scaled_argument_derivative {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D R : ℝ} (hD : 1 ≤ D) (hR : 0 ≤ R) (i : ℕ) (hi : 1 ≤ i)
    (x : Joint) (hb : ‖iteratedFDeriv ℝ i h x‖ ≤ D) :
    ‖iteratedFDeriv ℝ i (fun y => R*h y) x‖ ≤ (D^2*(1+R))^i := by
  have he : iteratedFDeriv ℝ i (fun y => R*h y) x = R • iteratedFDeriv ℝ i h x :=
    by simpa only [smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := R) (i := i) (x := x)
        ((hh.of_le (by exact_mod_cast le_top)).contDiffAt))
  rw [he, norm_smul, Real.norm_of_nonneg hR]
  have hDi : D ≤ D^i := by
    calc D = D^1 := by simp
         _ ≤ D^i := pow_le_pow_right₀ hD hi
  have hRi : R ≤ (1+R)^i := by
    calc R ≤ 1+R := by linarith
         _ = (1+R)^1 := by simp
         _ ≤ (1+R)^i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * ‖iteratedFDeriv ℝ i h x‖ ≤ R*D := mul_le_mul_of_nonneg_left hb hR
    _ ≤ (1+R)^i * D^i := mul_le_mul hRi hDi (by linarith) (by positivity)
    _ ≤ (D^2*(1+R))^i := by
      rw [mul_pow, pow_two, mul_pow]
      have hhD : 1 ≤ D^i := one_le_pow₀ hD
      nlinarith [mul_nonneg (show 0 ≤ (1+R)^i by positivity)
        (show 0 ≤ (D^i)^2-D^i by nlinarith)]

lemma normalized_phase_derivative (v x : ℝ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (logPhase (v/(2*Real.pi))) x‖ = |v|^i := by
  rw [JointLogSeparation.logPhase_iteratedFDeriv_norm, norm_div,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi), Real.norm_eq_abs]
  congr 1
  field_simp

lemma phase_derivative_bound {φ : Joint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {D : ℝ} (hD : 1 ≤ D) (n j : ℕ) (hj : j ≤ n)
    (x : Joint) (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i φ x‖ ≤ D) (v : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y => logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
      (n.factorial : ℝ)*D^n*(1+|v|)^n := by
  have hcomp := norm_iteratedFDeriv_comp_le (JointLogSeparation.logPhase_temperate (v/(2*Real.pi))).1
    hφ (n := j) (by simp) x (C := (1+|v|)^n) (D := D)
  have hc : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (logPhase (v/(2*Real.pi))) (φ x)‖ ≤
      (1+|v|)^n := by
    intro i hi
    rw [normalized_phase_derivative]
    exact (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |v| ≤ 1+|v|) i).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg v]) (hi.trans hj))
  have hd : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i φ x‖ ≤ D^i := by
    intro i hi hij
    exact (hb i (hij.trans hj)).trans (by
      calc D = D^1 := by simp
           _ ≤ D^i := pow_le_pow_right₀ hD hi)
  calc
    _ ≤ (j.factorial : ℝ)*(1+|v|)^n*D^j := hcomp hc hd
    _ ≤ (n.factorial : ℝ)*(1+|v|)^n*D^n := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity))
        (pow_le_pow_right₀ hD hj) (by positivity) (by positivity)
    _ = _ := by ring

lemma kernel_derivative_bound {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D m R : ℝ} (hD : 1 ≤ D) (hm : 0 < m) (hm1 : m ≤ 1) (hR : 0 ≤ R)
    (B n j : ℕ) (hj : j ≤ n) (x : Joint)
    (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i h x‖ ≤ D) (hl : m ≤ h x)
    (g : 𝓢(ℝ, ℂ)) :
    ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (((n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n))*rayControl B n g) /
        (1+R)^(2*B) := by
  have hu : 0 ≤ R*h x := mul_nonneg hR (hm.le.trans hl)
  have hden : 0 < (1+R*h x)^(2*B+n) := by positivity
  have harg : ContDiff ℝ ∞ (fun y => R*h y) := contDiff_const.mul hh
  have hcomp : ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
        (D^2*(1+R))^j := by
    apply norm_iteratedFDeriv_comp_le (g.smooth ⊤) harg (by simp) x
    · intro i hi
      apply (le_div_iff₀ hden).mpr
      have hd := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (2*B+n,n)) (k := 2*B+n) (n := i) le_rfl (hi.trans hj) g (R*h x)
      change (1+‖R*h x‖)^(2*B+n) * ‖iteratedFDeriv ℝ i g (R*h x)‖ ≤
        2^(2*B+n)*rayControl B n g at hd
      rw [Real.norm_of_nonneg hu] at hd
      simpa only [mul_comm] using hd
    · intro i hi hij
      exact scaled_argument_derivative hh hD hR i hi x (hb i (hij.trans hj))
  have hscale : m*(1+R) ≤ 1+R*h x := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hl)]
  have habs := FourierBridge.derivative_scale_absorption R (R*h x) m D
    (2^(2*B+n)*rayControl B n g) (2*B) n j hR hm (by linarith)
    (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)) hu hscale hj
  have hbound : m^(2*B+n)*(1+R)^(2*B)*
      ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (n.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^n := by
    calc
      _ ≤ m^(2*B+n)*(1+R)^(2*B)*
          ((j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
            (D^2*(1+R))^j) := mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ ≤ (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^j := habs
      _ ≤ _ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj)
            (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
          (pow_le_pow_right₀ (one_le_pow₀ hD) hj) (by positivity)
          (mul_nonneg (by positivity) (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
  apply (le_div_iff₀ (by positivity : 0 < (1+R)^(2*B))).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < m^(2*B+n))).mpr
  convert hbound using 1 <;> ring

def amplitudeControl (n : ℕ) (A : 𝓢(Joint, ℂ)) : ℝ :=
  (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) A

lemma amplitudeControl_nonneg (n : ℕ) (A : 𝓢(Joint, ℂ)) :
    0 ≤ amplitudeControl n A := apply_nonneg _ _

lemma amplitude_derivative_bound (n i : ℕ) (hi : i ≤ n)
    (A : 𝓢(Joint, ℂ)) (x : Joint) :
    ‖iteratedFDeriv ℝ i A x‖ ≤ amplitudeControl n A := by
  have hp : schwartzSeminormFamily ℝ Joint ℂ (0, i) ≤
      (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) :=
    Finset.le_sup (Finset.mem_Iic.mpr ⟨le_rfl, hi⟩)
  have hz : ‖iteratedFDeriv ℝ i A x‖ ≤ SchwartzMap.seminorm ℝ 0 i A := by
    simpa using SchwartzMap.le_seminorm ℝ 0 i A x
  exact hz.trans (Seminorm.le_def.mp hp A)

theorem compact_profile_seminorm
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      SchwartzMap.seminorm ℝ k n F ≤
        C*amplitudeControl n A*rayControl B n g*(1+|v|)^n/(1+R)^(2*B) := by
  obtain ⟨Dφ, hDφ, hbφ⟩ := compact_derivatives hK hφ n
  obtain ⟨Dh, hDh, hbh⟩ := compact_derivatives hK hh n
  obtain ⟨m, hm, hm1, hml⟩ := compact_positive_margin hK hh.continuous hhpos
  obtain ⟨L0, hL0⟩ := hK.bddAbove_image (continuous_norm.continuousOn : ContinuousOn (fun x : Joint => ‖x‖) K)
  let D := max Dφ Dh
  let L := max 1 L0
  have hD : 1 ≤ D := hDφ.trans (le_max_left _ _)
  have hL : 1 ≤ L := le_max_left _ _
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let Cg : ℝ := (n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n)
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  let Cp : ℝ := (n.factorial : ℝ)*D^n
  have hCp : 0 < Cp := by dsimp [Cp]; positivity
  refine ⟨L^k*2^n*2^n*Cp*Cg, by positivity, ?_⟩
  intro A hA g v R hR F hF
  have hp : ContDiff ℝ ∞ (fun y => logPhase (v/(2*Real.pi)) (φ y)) :=
    (JointLogSeparation.logPhase_temperate _).1.comp hφ
  have hg : ContDiff ℝ ∞ (fun y => g (R*h y)) :=
    (g.smooth ⊤).comp (contDiff_const.mul hh)
  have hFfun : (F : Joint → ℂ) =
      fun x => A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x) := funext hF
  have hFs : tsupport (F : Joint → ℂ) ⊆ K := by
    rw [hFfun]
    exact (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hA
  have hAn := amplitudeControl_nonneg n A
  have hgn := rayControl_nonneg B n g
  have hden : 0 < (1+R)^(2*B) := by positivity
  apply SchwartzMap.seminorm_le_bound ℝ k n F (by positivity)
  intro x
  by_cases hx : x ∈ K
  · have hxb : ‖x‖ ≤ L := (hL0 (mem_image_of_mem _ hx)).trans (le_max_right _ _)
    have hpbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          Cp*(1+|v|)^n :=
      phase_derivative_bound hφ hD n j hj x
        (fun i hi => (hbφ i hi x hx).trans (le_max_left _ _)) v
    have hgbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
          Cg*rayControl B n g/(1+R)^(2*B) :=
      kernel_derivative_bound hh hD hm hm1 hR B n j hj x
        (fun i hi => (hbh i hi x hx).trans (le_max_right _ _)) (hml x hx) g
    have hap (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => A y * logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          2^n*amplitudeControl n A*(Cp*(1+|v|)^n) := by
      calc
        _ ≤ 2^j*amplitudeControl n A*(Cp*(1+|v|)^n) :=
          mul_derivative_bound j (A.smooth ⊤) hp x hAn (by positivity)
            (fun i hi => amplitude_derivative_bound n i (hi.trans hj) A x)
            (fun i hi => hpbd i (hi.trans hj))
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hAn) (by positivity)
    have hb := mul_derivative_bound n ((A.smooth ⊤).mul hp) hg x
      (C := 2^n*amplitudeControl n A*(Cp*(1+|v|)^n))
      (D := Cg*rayControl B n g/(1+R)^(2*B)) (by positivity) (by positivity) hap hgbd
    rw [hFfun]
    calc
      _ ≤ L^k * (2^n*(2^n*amplitudeControl n A*(Cp*(1+|v|)^n))*
          (Cg*rayControl B n g/(1+R)^(2*B))) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxb _) hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ n (F : Joint → ℂ) x = 0 := by
      apply Function.notMem_support.mp
      intro hx'
      exact hx (hFs ((support_iteratedFDeriv_subset n) hx'))
    rw [hz, norm_zero, mul_zero]
    positivity

lemma amplitudeControl_mono {n N : ℕ} (hn : n ≤ N) (A : 𝓢(Joint, ℂ)) :
    amplitudeControl n A ≤ amplitudeControl N A := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨le_rfl, hn⟩))) A

lemma rayControl_mono (B : ℕ) {n N : ℕ} (hn : n ≤ N) (g : 𝓢(ℝ, ℂ)) :
    rayControl B n g ≤ rayControl B N g := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨by omega, hn⟩))) g

def heightOrder (H : Finset (ℕ × ℕ)) : ℕ := H.sup Prod.snd

theorem compact_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      sourceControl H F ≤
        C*amplitudeControl (heightOrder H) A*rayControl B (heightOrder H) g*
          (1+|v|)^(heightOrder H)/(1+R)^(2*B) := by
  have hc (p : ℕ × ℕ) := compact_profile_seminorm hK hφ hh hhpos B p.1 p.2
  choose C hC hbound using hc
  let D : ℝ := 1+∑ p ∈ H, C p
  have hD : 0 < D := by
    have hs : 0 ≤ ∑ p ∈ H, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro A hA g v R hR F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hgn := rayControl_nonneg B (heightOrder H) g
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro p hp
  have hn : p.2 ≤ heightOrder H := Finset.le_sup hp
  have hCD : C p ≤ D := by
    have hs := Finset.single_le_sum (fun p _ => (hC p).le) hp
    dsimp [D]
    linarith
  exact (hbound p A hA g v R hR F hF).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · exact mul_le_mul
        (mul_le_mul hCD (amplitudeControl_mono hn A)
          (amplitudeControl_nonneg _ _) hD.le)
        (rayControl_mono B hn g) (rayControl_nonneg _ _ _) (by positivity)
    · exact pow_le_pow_right₀ (by linarith [abs_nonneg v]) hn
    · positivity
    · positivity)

lemma sqrt_decay_absorption (T : ℝ) (hT : 0 ≤ T) (B : ℕ) :
    (1+T)^B ≤ (1+Real.sqrt T)^(2*B) := by
  have hbase : 1+T ≤ (1+Real.sqrt T)^2 := by
    nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T]
  calc
    _ ≤ ((1+Real.sqrt T)^2)^B := pow_le_pow_left₀ (by positivity) hbase B
    _ = _ := by rw [pow_mul]

theorem compact_fourier_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ), 0 ≤ T →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) *
        paperFourierRayCLM U (Real.sqrt T*h x)) →
      sourceControl H F ≤ C*amplitudeControl (heightOrder H) A*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨D, hD, hbound⟩ := compact_profile_finite hK hφ hh hhpos B H
  obtain ⟨S, E, hE, hEbound⟩ := schwartzCLM_finite_seminorm_control
    paperFourierRayCLM (Finset.Iic (2*B+heightOrder H,heightOrder H))
  refine ⟨S, D*E, by positivity, ?_⟩
  intro A hA U v T hT F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hUn : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  have hg := hEbound U
  change rayControl B (heightOrder H) (paperFourierRayCLM U) ≤
    E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U at hg
  calc
    _ ≤ D*amplitudeControl (heightOrder H) A*
        rayControl B (heightOrder H) (paperFourierRayCLM U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) :=
      hbound A hA (paperFourierRayCLM U) v (Real.sqrt T) (Real.sqrt_nonneg _) F hF
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) := by
      gcongr
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+T)^B :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (sqrt_decay_absorption T hT B)
    _ = _ := by ring

open ProbeGramJointConstruction

theorem jointProfile_homogeneous (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
        (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
      sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
        C*amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)*
          S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*
          (1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := compact_fourier_profile_finite
    (sourceCompact_isCompact b) (phase_smooth a b ha) (rootScale_smooth a b ha)
    (fun z _ => rootScale_pos a b ha z) B H
  refine ⟨S, C, hC, ?_⟩
  intro W hs hW U v T hT
  exact hb (amplitudeSchwartz W a b ha hab hs hW)
    (tsupport_amplitude_subset W a b ha hab hs) U v T hT
    (jointProfile W U a b ha hab hs hW v T hT)
    (jointProfile_factorization W U a b ha hab hs hW v T hT)

theorem jointProfile_uniform_degree (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (J : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W),
      ∃ C : ℝ, 0 < C ∧ ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
        sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
          C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := jointProfile_homogeneous a b ha hab B H
  refine ⟨heightOrder H, S, ?_⟩
  intro W hs hW
  let A := amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)
  have hA : 0 ≤ A := amplitudeControl_nonneg _ _
  refine ⟨C*(1+A), by positivity, ?_⟩
  intro U v T hT
  have hU : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  exact (hb W hs hW U v T hT).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by dsimp [A]; linarith :
        amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW) ≤ 1+A) hC.le) hU)

end ProbeGramJointProfile

end

end OAI
