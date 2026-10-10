import Mathlib
import OAI.Geometry.SmoothYau.Limits.CompactExteriorBackgroundDomination
import OAI.Geometry.SmoothYau.Limits.CompactStrictProfileRatio
import OAI.Geometry.SmoothYau.Limits.ScalarCauchyCross

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma geometric_complex_product_jet_bound
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*(F*R^i)*(G*S^(h-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i hi') (Nat.cast_nonneg _)
          (mul_nonneg hF (pow_nonneg hR _)))
        (hgj (h-i) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hG (pow_nonneg hS _))
    _ = F*G*(R+S)^h := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma compact_raw_jet_bound {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ h, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact (((hf.contDiffAt (hO.mem_nhds (hKO hx))).continuousAt_iteratedFDeriv
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))))).continuousWithinAt
  choose B hB using hb
  let C := 1+∑ j ∈ Finset.range (h+1), max 0 (B j)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro j hj x hx
  calc
    _ ≤ B j := hB j x hx
    _ ≤ max 0 (B j) := le_max_right _ _
    _ ≤ ∑ j ∈ Finset.range (h+1), max 0 (B j) :=
      Finset.single_le_sum (fun k _ => le_max_left _ _) (Finset.mem_range.mpr (by omega))
    _ ≤ C := by dsimp [C]; linarith
lemma complex_power_envelope_jet_bound {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : E) (h n : ℕ) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ A*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ ≤ A^n*((n:ℝ)*C)^j := by
  induction n with
  | zero =>
    intro j hj
    cases j with
    | zero => simp only [pow_zero,norm_iteratedFDeriv_zero,norm_one,one_mul,le_refl]
    | succ j => simp only [pow_zero,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,
        Nat.cast_zero,zero_mul,zero_pow (by omega : j+1 ≠ 0),mul_zero,le_refl]
  | succ n ih =>
    intro j hj
    have hb := geometric_complex_product_jet_bound (hf.pow n) hf x j
      (pow_nonneg hA _) hA (mul_nonneg (Nat.cast_nonneg _) hC) hC
      (fun k hk => ih k (hk.trans hj)) (fun k hk => hfj k (hk.trans hj))
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hb


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_power_weighted_jets {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    {K : Set E} (hK : IsCompact K) (φ : E → ℝ) (hφ : ContinuousOn φ K) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
        C*(n:ℝ)^j*(Real.exp ((n:ℝ)*φ x)+‖f x‖^n) := by
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound isOpen_univ hK (subset_univ K) hf.contDiffOn h
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hφ
  let r := Real.exp (-B)
  have hr : 0 < r := Real.exp_pos _
  let T := max 1 (D/r)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  refine ⟨T^h,pow_pos (zero_lt_one.trans_le hT1) _,?_⟩
  intro n x hx j hj
  let A := max ‖f x‖ (Real.exp (φ x))
  have hA : 0 ≤ A := (norm_nonneg _).trans (le_max_left _ _)
  have hrA : r ≤ A := by
    have hlow : -B ≤ φ x := by
      have hh := (neg_abs_le (φ x)).trans' (neg_le_neg (hB x hx))
      simpa only [Real.norm_eq_abs] using hh
    exact (Real.exp_le_exp.mpr hlow).trans (le_max_right _ _)
  have hraw : ∀ k ≤ h, ‖iteratedFDeriv ℝ k f x‖ ≤ A*T^k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using
        (le_max_left ‖f x‖ (Real.exp (φ x)))
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hTk : T ≤ T^k := by simpa only [pow_one] using pow_le_pow_right₀ hT1 hk1
      calc
        _ ≤ D := hDj k hk x hx
        _ = r*(D/r) := by field_simp
        _ ≤ A*T^k := mul_le_mul hrA ((le_max_right _ _).trans hTk)
          (div_nonneg (zero_le_one.trans hD) hr.le) hA
  have hp := complex_power_envelope_jet_bound hf x h n hA hT0 hraw j hj
  have hreal : ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
      A^n*((n:ℝ)*T)^j := by
    calc
      _ ≤ ‖Complex.reCLM‖*‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ :=
        ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.reCLM (x:=x)
          (hf.pow n).contDiffAt (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
      _ ≤ 1*(A^n*((n:ℝ)*T)^j) := mul_le_mul (le_of_eq Complex.reCLM_norm)
        hp (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hAn : A^n ≤ Real.exp ((n:ℝ)*φ x)+‖f x‖^n := by
    by_cases he : ‖f x‖ ≤ Real.exp (φ x)
    · dsimp [A]
      rw [max_eq_right he,←Real.exp_nat_mul]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
    · dsimp [A]
      rw [max_eq_left (le_of_not_ge he)]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have he : A^n*((n:ℝ)*T)^j = T^j*(n:ℝ)^j*A^n := by rw [mul_pow]; ring
  rw [he] at hreal
  exact hreal.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
    hAn (pow_nonneg hA _) (by positivity))

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold BoxIntegral Metric
open scoped Topology ContDiff

lemma sphericalRadius_eq_planar_norm (a b : Euclidean 4) (q : Sphere 3) :
    sphericalRadius a b q = ‖planarLinear a b q‖ := by
  have hh := Complex.sq_norm (planarLinear a b q)
  simp only [planarLinear_apply,Complex.normSq_apply,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,
    zero_mul,sub_zero,add_zero,Complex.add_im,Complex.mul_im,zero_add] at hh
  have hs := sphericalRadius_sq a b q
  apply (sq_eq_sq₀ (sphericalRadius_nonneg a b q) (norm_nonneg _)).mp
  rw [hs]
  change _ = ‖(⟪a,(q : Euclidean 4)⟫_ℝ : ℂ)+Complex.I*⟪b,(q : Euclidean 4)⟫_ℝ‖^2
  nlinarith only [hh]

lemma spherical_chart_pullback_smooth {φ : Sphere 3 → ℝ}
    (hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ) (p : Sphere 3) :
    ContDiff ℝ ∞ (φ ∘ (chartAt (Euclidean 3) p).symm) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact contDiffAt_inChart hφ p (by rw [sphere_chart_target]; trivial)

lemma roundPlanarChart_contDiff (a b : Euclidean 4) (p : Sphere 3) :
    ContDiff ℝ ∞ (roundPlanarChart a b p) :=
  contDiffOn_univ.mp (by simpa only [sphere_chart_target] using roundPlanarChart_smooth a b p)

def sphericalChartWeight (φ : Sphere 3 → ℝ) (n : ℕ) (y : Fin 3 → ℝ) : ℝ :=
  Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y)))+
    ‖roundPlanarChart sourceAxisOne sourceAxisTwo sourcePole (normalWaveEquiv y)‖^n

def sphericalExceptionalInChart (φ : Sphere 3 → ℝ) (n : ℕ) : Set (Fin 3 → ℝ) :=
  {y | ‖roundPlanarChart sourceAxisOne sourceAxisTwo sourcePole (normalWaveEquiv y)‖^n ≤
    (n:ℝ)^6*Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y)))}

lemma sphericalChartWeight_lower (φ : Sphere 3 → ℝ) (n : ℕ) (y : Fin 3 → ℝ) :
    Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y))) ≤
      sphericalChartWeight φ n y := le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)

lemma sphericalChartWeight_upper (φ : Sphere 3 → ℝ) (n : ℕ) (y : Fin 3 → ℝ)
    (hy : y ∈ sphericalExceptionalInChart φ n) :
    sphericalChartWeight φ n y ≤ (1+(n:ℝ)^6)*
      Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y))) := by
  dsimp [sphericalExceptionalInChart] at hy
  dsimp [sphericalChartWeight]
  nlinarith

theorem spherical_background_input_bounds {φ : Sphere 3 → ℝ}
    (hφ : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ φ)
    {S : Set (Fin 3 → ℝ)} (hS : IsCompact S) :
    ∃ T₀ > 0, ∃ H > 0, ∀ n : ℕ, 2 ≤ n →
      Differentiable ℝ (sphericalChartWeight φ n) ∧
      (∀ y, 0 < sphericalChartWeight φ n y) ∧
      (∀ y ∈ S, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n ∘
          (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) y‖ ≤
          T₀*(n:ℝ)^j*sphericalChartWeight φ n y) ∧
      (∀ y ∈ S, ‖fderiv ℝ (sphericalChartWeight φ n) y‖ ≤ H*(n:ℝ)*sphericalChartWeight φ n y) := by
  let f := roundPlanarChart sourceAxisOne sourceAxisTwo sourcePole ∘ normalWaveEquiv
  let ψ := (φ ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv
  have hf : ContDiff ℝ ∞ f :=
    (roundPlanarChart_contDiff sourceAxisOne sourceAxisTwo sourcePole).comp normalWaveEquiv.contDiff
  have hψ : ContDiff ℝ ∞ ψ := (spherical_chart_pullback_smooth hφ sourcePole).comp normalWaveEquiv.contDiff
  obtain ⟨T,hT,hTbound⟩ := real_power_weighted_jets hf hS ψ hψ.continuous.continuousOn 2
  obtain ⟨H,hH,hHb⟩ := positive_wave_weight_control f ψ (hf.of_le (by simp)) (hψ.of_le (by simp)) hS
  refine ⟨T,hT,H,hH,?_⟩
  intro n hn
  obtain ⟨hW,hW0,hWD⟩ := hHb n hn
  exact ⟨hW.differentiable one_ne_zero,hW0,fun y hy j hj => hTbound n y hy j hj,hWD⟩

theorem spherical_exceptional_eventually_coverage {φ : Sphere 3 → ℝ}
    (hφ : Continuous φ) {t s : ℝ} (ht : 0 < t) (hts : t < s) (hs : s < 1)
    (hgap : ∀ q, t < sphericalRadius sourceAxisOne sourceAxisTwo q →
      φ q < Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q)) :
    ∀ᶠ n : ℕ in atTop, sphericalExceptionalInChart φ n ⊆ normalWaveEquiv.symm ''
      sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo s := by
  let K : Set (Sphere 3) := {q | s ≤ sphericalRadius sourceAxisOne sourceAxisTwo q}
  have hK : IsCompact K := (isClosed_le continuous_const (sphericalRadius_continuous _ _)).isCompact
  have hd := compact_exterior_background_domination hK
    (sphericalRadius_continuous sourceAxisOne sourceAxisTwo).continuousOn hφ.continuousOn
    (fun q hq => ht.trans_le (hts.le.trans hq))
    (fun q hq => hgap q (hts.trans_le hq)) 6
  filter_upwards [hd] with n hn
  intro y hy
  refine ⟨normalWaveEquiv y,?_,normalWaveEquiv.symm_apply_apply y⟩
  apply (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole hs _).mpr
  by_contra hm
  have hrad : s ≤ sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm (normalWaveEquiv y)) := (lt_of_not_ge hm).le
  have hh := hn _ hrad
  rw [sphericalRadius_eq_planar_norm] at hh
  exact (not_lt_of_ge hy) hh

lemma roundPower_abs_le_radius_pow (a b : Euclidean 4) (n : ℕ) (q : Sphere 3) :
    |roundPower a b n q| ≤ (sphericalRadius a b q)^n := by
  rw [sphericalRadius_eq_planar_norm,←norm_pow]
  exact Complex.abs_re_le_norm _

theorem spherical_background_sign_small {φ : Sphere 3 → ℝ} (hφ : Continuous φ)
    (I : Box (Fin 3)) {t : ℝ}
    (hI : ∀ y ∈ normalWaveEquiv '' Box.Icc I,
      sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) sourcePole).symm y) < t)
    (hgap : ∀ q, 0 < sphericalRadius sourceAxisOne sourceAxisTwo q →
      sphericalRadius sourceAxisOne sourceAxisTwo q < t →
      Real.log (sphericalRadius sourceAxisOne sourceAxisTwo q) < φ q)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ y ∈ normalWaveEquiv '' Box.Icc I,
      |roundPower sourceAxisOne sourceAxisTwo n ((chartAt (Euclidean 3) sourcePole).symm y)| ≤
        c*Real.exp ((n:ℝ)*φ ((chartAt (Euclidean 3) sourcePole).symm y)) := by
  let K := normalWaveEquiv '' Box.Icc I
  have hK : IsCompact K := I.isCompact_Icc.image normalWaveEquiv.continuous
  let r := sphericalRadius sourceAxisOne sourceAxisTwo ∘ (chartAt (Euclidean 3) sourcePole).symm
  let ψ := φ ∘ (chartAt (Euclidean 3) sourcePole).symm
  have hr : Continuous r := (sphericalRadius_continuous _ _).comp (sphere_chart_symm_continuous _)
  have hψ : Continuous ψ := hφ.comp (sphere_chart_symm_continuous _)
  obtain ⟨ρ,hρ,hρ1,hdom⟩ := compact_strict_profile_ratio hK hr.continuousOn hψ.continuousOn
    (fun y _ => sphericalRadius_nonneg _ _ _) (fun y hy hn => hgap _
      (lt_of_le_of_ne (sphericalRadius_nonneg _ _ _) (Ne.symm hn)) (hI y hy))
  have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1
  filter_upwards [htend.eventually (Iio_mem_nhds hc)] with n hn
  intro y hy
  calc
    _ ≤ r y^n := roundPower_abs_le_radius_pow _ _ _ _
    _ ≤ (ρ*Real.exp (ψ y))^n := pow_le_pow_left₀ (sphericalRadius_nonneg _ _ _) (hdom y hy) n
    _ = ρ^n*Real.exp ((n:ℝ)*ψ y) := by rw [mul_pow,←Real.exp_nat_mul]
    _ ≤ c*Real.exp ((n:ℝ)*ψ y) := mul_le_mul_of_nonneg_right hn.le (Real.exp_pos _).le


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
section PowerJets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma complex_power_jet_bound {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (x : E) (h n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ ‖f x‖*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ ≤
      ‖f x‖^n*((n:ℝ)*C)^j := by
  induction n with
  | zero =>
    intro j hj
    cases j with
    | zero => simp only [pow_zero,norm_iteratedFDeriv_zero,norm_one,one_mul,le_refl]
    | succ j => simp only [pow_zero,iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,
        Nat.cast_zero,zero_mul,zero_pow (by omega : j+1 ≠ 0),mul_zero,le_refl]
  | succ n ih =>
    intro j hj
    have hb := geometric_complex_product_jet_bound (hf.pow n) hf x j
      (pow_nonneg (norm_nonneg _) _) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC) hC
      (fun k hk => ih k (hk.trans hj)) (fun k hk => hfj k (hk.trans hj))
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hb
end PowerJets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma complex_power_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f O) (h n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ ‖f x‖*(C)^j) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y^n) x‖ ≤
      ‖f x‖^n*((n:ℝ)*C)^j := by
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hxO hf
  have hh := complex_power_jet_bound hF x h n hC (fun j hj => by
    rw [←he.self_of_nhds,←(he.iteratedFDeriv ℝ j).self_of_nhds]
    exact hfj j hj)
  intro j hj
  have hepow : (fun y => f y^n) =ᶠ[𝓝 x] (fun y => F y^n) :=
    he.mono (fun y hy => congrArg (fun z : ℂ => z^n) hy)
  rw [(hepow.iteratedFDeriv ℝ j).self_of_nhds,he.self_of_nhds]
  exact hh j hj

theorem annular_real_power_jets {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f O) (h n : ℕ) {r C : ℝ}
    (hr : 0 < r) (hrx : r ≤ ‖f x‖) (hC : 0 ≤ C)
    (hfj : ∀ j, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (f y^n).re) x‖ ≤
      (max 1 (C/r))^j*(n:ℝ)^j*‖f x‖^n := by
  let B := max 1 (C/r)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hbound : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ ‖f x‖*B^j := by
    intro j hj
    by_cases hj0 : j=0
    · subst j
      rw [norm_iteratedFDeriv_zero,pow_zero,mul_one]
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hbj : B ≤ B^j := by simpa only [pow_one] using pow_le_pow_right₀ hB1 hj1
      calc
        _ ≤ C := hfj j hj1 hj
        _ = r*(C/r) := by field_simp
        _ ≤ ‖f x‖*B^j := mul_le_mul hrx ((le_max_right _ _).trans hbj)
          (div_nonneg hC hr.le) (norm_nonneg _)
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hxO hf
  have hpow := complex_power_jet_bound hF x h n hB0 (fun j hj => by
    rw [←he.self_of_nhds,←(he.iteratedFDeriv ℝ j).self_of_nhds]
    exact hbound j hj)
  intro j hj
  have hp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left Complex.reCLM (x:=x)
    (hF.pow n).contDiffAt (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
  have heRe : (fun y => (f y^n).re) =ᶠ[𝓝 x] (fun y => (F y^n).re) :=
    he.mono (fun y hy => congrArg (fun z : ℂ => (z^n).re) hy)
  rw [(heRe.iteratedFDeriv ℝ j).self_of_nhds]
  calc
    _ ≤ ‖Complex.reCLM‖*‖iteratedFDeriv ℝ j (fun y => F y^n) x‖ := hp
    _ ≤ 1*(‖F x‖^n*((n:ℝ)*B)^j) := mul_le_mul (le_of_eq Complex.reCLM_norm)
      (hpow j hj) (norm_nonneg _) zero_le_one
    _ = _ := by rw [←he.self_of_nhds,mul_pow]; dsimp [B]; ring

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace

variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

theorem roundPower_annular_chart_jets (a b : Euclidean (d+1)) (p : Sphere d)
    {K : Set (Euclidean d)} (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (h : ℕ) {r : ℝ} (hr : 0 < r) (hKr : ∀ y ∈ K, r ≤ ‖roundPlanarChart a b p y‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ y ∈ K, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
        C*(n:ℝ)^j*‖roundPlanarChart a b p y‖^n := by
  have hf := roundPlanarChart_smooth a b p
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound (chartAt (Euclidean d) p).open_target hK hKO hf h
  let B := max 1 (D/r)
  have hB1 : 1 ≤ B := le_max_left _ _
  refine ⟨B^h,pow_pos (zero_lt_one.trans_le hB1) _,?_⟩
  intro n y hy j hj
  have hh := annular_real_power_jets (chartAt (Euclidean d) p).open_target (hKO hy) hf h n
    hr (hKr y hy) (zero_le_one.trans hD) (fun k _ hk => hDj k hk y hy) j hj
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hj) (pow_nonneg (Nat.cast_nonneg _) _))
    (pow_nonneg (norm_nonneg _) _))

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
section CompactInverseJets
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma compact_metric_inverse_jets (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i j : CoordIndex E, ∀ k ≤ h, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A := by
  classical
  choose B hB hBj using fun i j : CoordIndex E =>
    compact_raw_jet_bound (chartAt E p).open_target hK hKO (contDiffOn_metricInverse g p i j) h
  let A := 1+∑ i, ∑ j, B i j
  have hB0 (i j : CoordIndex E) : 0 ≤ B i j := zero_le_one.trans (hB i j)
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hB0 i j)))
  refine ⟨A,hA,?_⟩
  intro i j k hk y hy
  calc
    _ ≤ B i j := hBj i j k hk y hy
    _ ≤ ∑ j, B i j := Finset.single_le_sum (fun j _ => hB0 i j) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, B i j := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => hB0 i j)) (Finset.mem_univ i)
    _ ≤ A := by dsimp [A]; linarith
end CompactInverseJets

variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

theorem roundPower_conjugate_projection_control
    (g : SmoothMetric (Euclidean d) (Sphere d)) (a b : Euclidean (d+1)) (p : Sphere d)
    (ha : inner ℝ a a=1) (hb : inner ℝ b b=1) (hab : inner ℝ a b=0)
    {K : Set (Euclidean d)} (hK : IsCompact K) (hKO : K ⊆ (chartAt (Euclidean d) p).target)
    (hg : ∀ y ∈ K, ∀ v z : TangentSpace 𝓘(ℝ,Euclidean d) ((chartAt (Euclidean d) p).symm y),
      g.inner _ v z = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) _ v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) _ z))
    (h : ℕ) {r t D : ℝ} (hr : 0 < r) (ht : t < 1) (hD : 0 ≤ D)
    (hKr : ∀ y ∈ K, r ≤ ‖roundPlanarChart a b p y‖)
    (hKt : ∀ y ∈ K, Complex.normSq (roundPlanarChart a b p y) ≤ t)
    (w : ℕ → Sphere d → ℝ)
    (hw : ∀ n, ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ (w n))
    (hw0 : ∀ n x, w n x ≠ 0)
    (hwl : ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, 1/2 ≤ w n ((chartAt (Euclidean d) p).symm y))
    (hwu : ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, w n ((chartAt (Euclidean d) p).symm y) ≤ 2)
    (hwj : ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, 1 ≤ j → j ≤ h+1 → ∀ y ∈ K,
      ‖iteratedFDeriv ℝ j (w n ∘ (chartAt (Euclidean d) p).symm) y‖ ≤ D)
    (hwG : ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K,
      coordinateGradientPair g (w n) (w n) ((chartAt (Euclidean d) p).symm y) ≤ (1-t)/16) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ y ∈ K, ∀ i j : CoordIndex (Euclidean d),
      ‖iteratedFDeriv ℝ h (chartGradientProjection g
        (fun x => roundPower a b n x/w n x) p i j) y‖ ≤ C*(n:ℝ)^h := by
  obtain ⟨C0,hC0,hCj⟩ := roundPower_annular_chart_jets a b p hK hKO (h+1) hr hKr
  obtain ⟨A,hA,hAj⟩ := compact_metric_inverse_jets g p hK hKO h
  let C1 := C0*((h+1).factorial:ℝ)^2/(1/2)*(1+max 1 (D/(1/2)))^(h+1)
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  let L := ∑ j, ‖Module.finBasis ℝ (Euclidean d) j‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have he (i : CoordIndex (Euclidean d)) : ‖Module.finBasis ℝ (Euclidean d) i‖ ≤ L :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  let δ := (1-t)/16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let J := 2^h*A*C1*L
  let C := J*(C1*L)*(h.factorial:ℝ)^2/δ*
    (2+2*max 1 ((Fintype.card (CoordIndex (Euclidean d)):ℝ)*J*(C1*L)/δ))^h
  refine ⟨max C 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  intro n hn y hy i j
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  let W := ‖roundPlanarChart a b p y‖^n
  have hrY : 0 < ‖roundPlanarChart a b p y‖ := hr.trans_le (hKr y hy)
  have hW : 0 < W := pow_pos hrY _
  let u := fun x => roundPower a b n x/w n x
  have hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u :=
    (roundPower_smooth a b n).div₀ (hw n) (hw0 n)
  have huw : ContDiffOn ℝ ∞ (w n ∘ (chartAt (Euclidean d) p).symm)
      (chartAt (Euclidean d) p).target := fun z hz => (contDiffAt_inChart (hw n) p hz).contDiffWithinAt
  have hu0 : ContDiffOn ℝ ∞ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm)
      (chartAt (Euclidean d) p).target :=
    fun z hz => (contDiffAt_inChart (roundPower_smooth a b n) p hz).contDiffWithinAt
  have huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt (Euclidean d) p).symm) y‖ ≤
      C1*(n:ℝ)^k*W := by
    exact sharp_conjugate_jet_bound_on (chartAt (Euclidean d) p).open_target (hKO hy)
      hu0 huw (h+1) (by norm_num : (0:ℝ)<1/2) hW hnR hC0.le hD (hwl n hn y hy)
      (fun k hk => hCj n y hy k hk) (fun k hk hkh => hwj n hn k hk hkh y hy)
  have hR : 0 < Complex.normSq (roundPlanarChart a b p y) := by
    rw [Complex.normSq_eq_norm_sq]; positivity
  have hgL := roundPower_conjugate_gradient_lower g ((chartAt (Euclidean d) p).symm y)
    (hg y hy) a b n hn ha hb hab hR (hKt y hy) ht (w n) (hw n) (hw0 n)
    (hwl n hn y hy) (hwu n hn y hy) (hwG n hn y hy)
  have heW : Complex.normSq (roundPlanarChart a b p y)^n=W^2 := by
    dsimp [W]
    rw [Complex.normSq_eq_norm_sq,←pow_mul,←pow_mul,Nat.mul_comm 2 n]
  have hgrad : δ*((n:ℝ)*W)^2 ≤ coordinateGradientPair g u u ((chartAt (Euclidean d) p).symm y) := by
    change δ*(n:ℝ)^2*Complex.normSq (roundPlanarChart a b p y)^n ≤ _ at hgL
    rw [heW] at hgL
    simpa only [mul_pow,mul_assoc] using hgL
  have hp := chartGradientProjection_jet_bound hu g p (hKO hy) h hδ hnR hW hC1
    (zero_le_one.trans hA) hL he (fun i j k hk => hAj i j k hk y hy) huj hgrad i j
  exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg (Nat.cast_nonneg _) _))


end YauCounterexamples
end

end OAI
