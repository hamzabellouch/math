import Mathlib

namespace OAI

noncomputable section
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
namespace YauCounterexamples

lemma scalar_pred_power_weight_bound {r m a : ℝ} (hr : 0 ≤ r) (hm : 0 < m)
    (hma : m ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    m*r^(n-1) ≤ a^n+r^n := by
  have ha : 0 ≤ a := hm.le.trans hma
  have hn' : n-1+1=n := Nat.sub_add_cancel hn
  by_cases hmr : m ≤ r
  · calc
      _ ≤ r*r^(n-1) := mul_le_mul_of_nonneg_right hmr (pow_nonneg hr _)
      _ = r^n := by rw [←pow_succ',hn']
      _ ≤ _ := le_add_of_nonneg_left (pow_nonneg ha _)
  · calc
      _ ≤ a*a^(n-1) := mul_le_mul hma (pow_le_pow_left₀ hr ((le_of_not_ge hmr).trans hma) (n-1))
        (pow_nonneg hr _) ha
      _ = a^n := by rw [←pow_succ',hn']
      _ ≤ _ := le_add_of_nonneg_right (pow_nonneg hr _)

theorem positive_wave_weight_control
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F) (φ : E → ℝ) (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ)
    {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ContDiff ℝ 1 (fun x => Real.exp ((n:ℝ)*φ x)+‖f x‖^n) ∧
      (∀ x : E, 0 < Real.exp ((n:ℝ)*φ x)+‖f x‖^n) ∧
      ∀ x ∈ K, ‖fderiv ℝ (fun y => Real.exp ((n:ℝ)*φ y)+‖f y‖^n) x‖ ≤
        C*(n:ℝ)*(Real.exp ((n:ℝ)*φ x)+‖f x‖^n) := by
  obtain ⟨A,hAf⟩ := hK.exists_bound_of_continuousOn (hf.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨B,hBp⟩ := hK.exists_bound_of_continuousOn (hφ.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨R,hRp⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  let D := max 1 (max A B)
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  have hAD : A ≤ D := (le_max_left A B).trans (le_max_right _ _)
  have hBD : B ≤ D := (le_max_right A B).trans (le_max_right _ _)
  let m := Real.exp (-R)
  have hm : 0 < m := Real.exp_pos _
  refine ⟨D+D/m,by positivity,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (1:ℝ) < (n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have hfn : ContDiff ℝ 1 (fun x => ‖f x‖^n) := by
    simpa only [Real.rpow_natCast] using hf.norm_rpow hnR
  have hex : ContDiff ℝ 1 (fun x => Real.exp ((n:ℝ)*φ x)) := (contDiff_const.mul hφ).exp
  refine ⟨hex.add hfn,fun x => add_pos_of_pos_of_nonneg (Real.exp_pos _) (pow_nonneg (norm_nonneg _) _),?_⟩
  intro x hx
  let W := Real.exp ((n:ℝ)*φ x)+‖f x‖^n
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hem : m ≤ Real.exp (φ x) := by
    apply Real.exp_le_exp.mpr
    have hh := (neg_abs_le (φ x)).trans' (neg_le_neg (hRp x hx))
    simpa only [Real.norm_eq_abs] using hh
  have hpred : ‖f x‖^(n-1) ≤ W/m := by
    apply (le_div_iff₀ hm).mpr
    have hh := scalar_pred_power_weight_bound (norm_nonneg (f x)) hm hem hn1
    rw [←Real.exp_nat_mul] at hh
    simpa only [W, mul_comm] using hh
  have hnorm : ‖fderiv ℝ (fun y => ‖f y‖^n) x‖ ≤ (n:ℝ)*‖f x‖^(n-1)*D := by
    have hh := norm_fderiv_norm_rpow_le (x:=x) (hf.differentiable one_ne_zero) hnR
    have hcast : (n:ℝ)-1 = ((n-1:ℕ):ℝ) := by rw [Nat.cast_sub hn1]; norm_num
    rw [hcast,Real.rpow_natCast] at hh
    simp only [Real.rpow_natCast] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ((hAf x hx).trans hAD) (by positivity))
  have he : HasFDerivAt (fun y => Real.exp ((n:ℝ)*φ y))
      (Real.exp ((n:ℝ)*φ x) • ((n:ℝ) • fderiv ℝ φ x)) x :=
    (((hφ.differentiable one_ne_zero x).hasFDerivAt).const_mul (n:ℝ)).exp
  have heNorm : ‖fderiv ℝ (fun y => Real.exp ((n:ℝ)*φ y)) x‖ ≤
      (n:ℝ)*D*Real.exp ((n:ℝ)*φ x) := by
    rw [he.fderiv]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)]
    calc
      _ ≤ Real.exp ((n:ℝ)*φ x)*((n:ℝ)*D) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((hBp x hx).trans hBD) (Nat.cast_nonneg _)) (Real.exp_pos _).le
      _ = _ := by ring
  change ‖fderiv ℝ ((fun y => Real.exp ((n:ℝ)*φ y)) + (fun y => ‖f y‖^n)) x‖ ≤ _
  rw [fderiv_add (hex.differentiable one_ne_zero x) (hfn.differentiable one_ne_zero x)]
  calc
    _ ≤ ‖fderiv ℝ (fun y => Real.exp ((n:ℝ)*φ y)) x‖ +
      ‖fderiv ℝ (fun y => ‖f y‖^n) x‖ := norm_add_le _ _
    _ ≤ (n:ℝ)*D*Real.exp ((n:ℝ)*φ x)+(n:ℝ)*‖f x‖^(n-1)*D := add_le_add heNorm hnorm
    _ ≤ (n:ℝ)*D*W+(n:ℝ)*(W/m)*D := add_le_add
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)) (by positivity))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpred (Nat.cast_nonneg _)) hD.le)
    _ = _ := by dsimp [W]; field_simp

theorem positive_wave_weight_on_control
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → F) (φ : E → ℝ) {O : Set E} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 1 f O) (hφ : ContDiffOn ℝ 1 φ O)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ContDiffOn ℝ 1 (fun x => Real.exp ((n:ℝ)*φ x)+‖f x‖^n) O ∧
      (∀ x : E, 0 < Real.exp ((n:ℝ)*φ x)+‖f x‖^n) ∧
      ∀ x ∈ K, ‖fderiv ℝ (fun y => Real.exp ((n:ℝ)*φ y)+‖f y‖^n) x‖ ≤
        C*(n:ℝ)*(Real.exp ((n:ℝ)*φ x)+‖f x‖^n) := by
  obtain ⟨A,hAf⟩ := hK.exists_bound_of_continuousOn ((hf.continuousOn_fderiv_of_isOpen hO le_rfl).mono hKO)
  obtain ⟨B,hBp⟩ := hK.exists_bound_of_continuousOn ((hφ.continuousOn_fderiv_of_isOpen hO le_rfl).mono hKO)
  obtain ⟨R,hRp⟩ := hK.exists_bound_of_continuousOn (hφ.continuousOn.mono hKO)
  let D := max 1 (max A B)
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  have hAD : A ≤ D := (le_max_left A B).trans (le_max_right _ _)
  have hBD : B ≤ D := (le_max_right A B).trans (le_max_right _ _)
  let m := Real.exp (-R)
  have hm : 0 < m := Real.exp_pos _
  refine ⟨D+D/m,by positivity,?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (1:ℝ) < (n:ℝ) := by exact_mod_cast (show 1<n by omega)
  have hfn : ContDiffOn ℝ 1 (fun x => ‖f x‖^n) O := by
    simpa only [Function.comp_def,Real.rpow_natCast] using (contDiff_norm_rpow hnR).comp_contDiffOn hf
  have hex : ContDiffOn ℝ 1 (fun x => Real.exp ((n:ℝ)*φ x)) O := (contDiffOn_const.mul hφ).exp
  refine ⟨hex.add hfn,fun x => add_pos_of_pos_of_nonneg (Real.exp_pos _) (pow_nonneg (norm_nonneg _) _),?_⟩
  intro x hx
  have hxO : O ∈ 𝓝 x := hO.mem_nhds (hKO hx)
  have hfx := (hf.differentiableOn one_ne_zero x (hKO hx)).differentiableAt hxO
  have hφx := (hφ.differentiableOn one_ne_zero x (hKO hx)).differentiableAt hxO
  have hexx := (hex.differentiableOn one_ne_zero x (hKO hx)).differentiableAt hxO
  have hfnx := (hfn.differentiableOn one_ne_zero x (hKO hx)).differentiableAt hxO
  let W := Real.exp ((n:ℝ)*φ x)+‖f x‖^n
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hem : m ≤ Real.exp (φ x) := by
    apply Real.exp_le_exp.mpr
    have hh := (neg_abs_le (φ x)).trans' (neg_le_neg (hRp x hx))
    simpa only [Real.norm_eq_abs] using hh
  have hpred : ‖f x‖^(n-1) ≤ W/m := by
    apply (le_div_iff₀ hm).mpr
    have hh := scalar_pred_power_weight_bound (norm_nonneg (f x)) hm hem hn1
    rw [←Real.exp_nat_mul] at hh
    simpa only [W, mul_comm] using hh
  have hnorm : ‖fderiv ℝ (fun y => ‖f y‖^n) x‖ ≤ (n:ℝ)*‖f x‖^(n-1)*D := by
    have hh : ‖fderiv ℝ (fun y => ‖f y‖^(n:ℝ)) x‖ ≤
        (n:ℝ)*‖f x‖^((n:ℝ)-1)*‖fderiv ℝ f x‖ := by
      change ‖fderiv ℝ ((fun z : F => ‖z‖^(n:ℝ)) ∘ f) x‖ ≤ _
      rw [fderiv_comp x (differentiable_norm_rpow hnR (f x)) hfx]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq
        (by rw [norm_fderiv_norm_id_rpow (f x) hnR])
    have hcast : (n:ℝ)-1 = ((n-1:ℕ):ℝ) := by rw [Nat.cast_sub hn1]; norm_num
    rw [hcast,Real.rpow_natCast] at hh
    simp only [Real.rpow_natCast] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ((hAf x hx).trans hAD) (by positivity))
  have he : HasFDerivAt (fun y => Real.exp ((n:ℝ)*φ y))
      (Real.exp ((n:ℝ)*φ x) • ((n:ℝ) • fderiv ℝ φ x)) x :=
    ((hφx.hasFDerivAt).const_mul (n:ℝ)).exp
  have heNorm : ‖fderiv ℝ (fun y => Real.exp ((n:ℝ)*φ y)) x‖ ≤
      (n:ℝ)*D*Real.exp ((n:ℝ)*φ x) := by
    rw [he.fderiv]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)]
    calc
      _ ≤ Real.exp ((n:ℝ)*φ x)*((n:ℝ)*D) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((hBp x hx).trans hBD) (Nat.cast_nonneg _)) (Real.exp_pos _).le
      _ = _ := by ring
  change ‖fderiv ℝ ((fun y => Real.exp ((n:ℝ)*φ y)) + (fun y => ‖f y‖^n)) x‖ ≤ _
  rw [fderiv_add hexx hfnx]
  calc
    _ ≤ ‖fderiv ℝ (fun y => Real.exp ((n:ℝ)*φ y)) x‖ +
      ‖fderiv ℝ (fun y => ‖f y‖^n) x‖ := norm_add_le _ _
    _ ≤ (n:ℝ)*D*Real.exp ((n:ℝ)*φ x)+(n:ℝ)*‖f x‖^(n-1)*D := add_le_add heNorm hnorm
    _ ≤ (n:ℝ)*D*W+(n:ℝ)*(W/m)*D := add_le_add
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)) (by positivity))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpred (Nat.cast_nonneg _)) hD.le)
    _ = _ := by dsimp [W]; field_simp
end YauCounterexamples

end

end OAI
