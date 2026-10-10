import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialVariableProfiles
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialDilations

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E]

def logSingularSource (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  a z * logGradientProfile s z (V (b+z))
def sqrtSingularSource (a : E → ℝ) (V : E → E) (s : ℝ) (b z : E) : ℝ :=
  a z * sqrtGradientProfile s z (V (b+z))

omit [ProperSpace E] in
lemma logShell_eq_normalized (a : E → ℝ) (V : E → E)
    {r s : ℝ} (hr : 0 < r) (b x : E) :
    shellCutoff r x * logSingularSource a V s b x =
      r⁻¹ • variableLogProfile (shellCutoff 1) a V (s/r,r,b) (r⁻¹ • (x-0)) := by
  have h := variableLogProfile_shell_scale a V (s := s) hr b (r⁻¹ • x)
  simp only [smul_smul,mul_inv_cancel₀ hr.ne',one_smul] at h
  rw [sub_zero,← h]
  simp [logSingularSource,smul_eq_mul,← mul_assoc,hr.ne']

omit [ProperSpace E] in
lemma sqrtShell_eq_normalized (a : E → ℝ) (V : E → E)
    {r s : ℝ} (hr : 0 < r) (b x : E) :
    shellCutoff r x * sqrtSingularSource a V s b x =
      variableSqrtProfile (shellCutoff 1) a V (s/r,r,b) (r⁻¹ • (x-0)) := by
  have h := variableSqrtProfile_shell_scale a V (s := s) hr b (r⁻¹ • x)
  simpa only [sqrtSingularSource,sub_zero,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using h

omit [ProperSpace E] in
lemma logInner_eq_normalized (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b x : E) :
    scaledCutoff s x * logSingularSource a V s b x =
      s⁻¹ • variableLogProfile (scaledCutoff 1) a V (1,s,b) (s⁻¹ • (x-0)) := by
  have h := variableLogProfile_inner_scale a V hs b (s⁻¹ • x)
  simp only [smul_smul,mul_inv_cancel₀ hs.ne',one_smul] at h
  rw [sub_zero,← h]
  simp [logSingularSource,smul_eq_mul,← mul_assoc,hs.ne']

omit [ProperSpace E] in
lemma sqrtInner_eq_normalized (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b x : E) :
    scaledCutoff s x * sqrtSingularSource a V s b x =
      variableSqrtProfile (scaledCutoff 1) a V (1,s,b) (s⁻¹ • (x-0)) := by
  have h := variableSqrtProfile_inner_scale a V hs b (s⁻¹ • x)
  simpa only [sqrtSingularSource,sub_zero,smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using h

lemma logShell_derivatives_bounded (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (fun z => shellCutoff r z * logSingularSource a V s b z) x‖ ≤
        C / r^(n+1) := by
  obtain ⟨C,hC,hbound⟩ := variableLogProfile_derivatives_bounded (shellCutoff 1) a V
    (shellCutoff_smooth _) (shellCutoff_compact (by norm_num))
    (shellCutoff_origin_not_tsupport (by norm_num)) ha hV hK R n
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hb x
  have hsr : s/r ∈ Icc (0:ℝ) 1 := ⟨div_nonneg hs.1 hr.1.le,(div_le_one hr.1).mpr hs.2⟩
  have hf : ContDiff ℝ ∞ (variableLogProfile (shellCutoff 1) a V (s/r,r,b)) :=
    (variableLogProfile_smooth (shellCutoff 1) a V (shellCutoff_smooth _)
      (shellCutoff_origin_not_tsupport (by norm_num)) ha hV).comp (contDiff_const.prodMk contDiff_id)
  have he : (fun z => shellCutoff r z * logSingularSource a V s b z) =
      fun z => r⁻¹ • variableLogProfile (shellCutoff 1) a V (s/r,r,b) (r⁻¹ • (z-0)) :=
    funext (logShell_eq_normalized a V hr.1 b)
  rw [he]
  calc
    _ ≤ |r⁻¹| * ‖iteratedFDeriv ℝ n (variableLogProfile (shellCutoff 1) a V (s/r,r,b))
        (r⁻¹ • (x-0))‖ / r^n := norm_iteratedFDeriv_scaled_dilate_le _ hf hr.1 r⁻¹ 0 x n
    _ ≤ |r⁻¹| * C / r^n := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound _ hsr r ⟨hr.1.le,hr.2⟩ b hb _) (abs_nonneg _))
      (pow_nonneg hr.1.le n)
    _ = _ := by rw [abs_of_pos (inv_pos.mpr hr.1),pow_succ]; field_simp

lemma sqrtShell_derivatives_bounded (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0:ℝ) R, ∀ s ∈ Icc (0:ℝ) r, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (fun z => shellCutoff r z * sqrtSingularSource a V s b z) x‖ ≤
        C / r^n := by
  obtain ⟨C,hC,hbound⟩ := variableSqrtProfile_derivatives_bounded (shellCutoff 1) a V
    (shellCutoff_smooth _) (shellCutoff_compact (by norm_num))
    (shellCutoff_origin_not_tsupport (by norm_num)) ha hV hK R n
  refine ⟨C,hC,?_⟩
  intro r hr s hs b hb x
  have hsr : s/r ∈ Icc (0:ℝ) 1 := ⟨div_nonneg hs.1 hr.1.le,(div_le_one hr.1).mpr hs.2⟩
  have hf : ContDiff ℝ ∞ (variableSqrtProfile (shellCutoff 1) a V (s/r,r,b)) :=
    (variableSqrtProfile_smooth (shellCutoff 1) a V (shellCutoff_smooth _)
      (shellCutoff_origin_not_tsupport (by norm_num)) ha hV).comp (contDiff_const.prodMk contDiff_id)
  have he : (fun z => shellCutoff r z * sqrtSingularSource a V s b z) =
      fun z => variableSqrtProfile (shellCutoff 1) a V (s/r,r,b) (r⁻¹ • (z-0)) :=
    funext (sqrtShell_eq_normalized a V hr.1 b)
  rw [he]
  exact (norm_iteratedFDeriv_dilate_le _ hf hr.1 0 x n).trans
    (div_le_div_of_nonneg_right (hbound _ hsr r ⟨hr.1.le,hr.2⟩ b hb _) (pow_nonneg hr.1.le n))
lemma logInner_derivatives_bounded (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (fun z => scaledCutoff s z * logSingularSource a V s b z) x‖ ≤
        C / s^(n+1) := by
  obtain ⟨C,hC,hbound⟩ := innerLogProfile_derivatives_bounded (scaledCutoff 1) a V
    (scaledCutoff_smooth _) (scaledCutoff_compact (by norm_num)) ha hV hK R n
  refine ⟨C,hC,?_⟩
  intro s hs b hb x
  have hf : ContDiff ℝ ∞ (variableLogProfile (scaledCutoff 1) a V (1,s,b)) :=
    (innerLogProfile_smooth (scaledCutoff 1) a V (scaledCutoff_smooth _) ha hV).comp
      ((show ContDiff ℝ ∞ (fun _ : E => (s,b)) from contDiff_const).prodMk contDiff_id)
  have he : (fun z => scaledCutoff s z * logSingularSource a V s b z) =
      fun z => s⁻¹ • variableLogProfile (scaledCutoff 1) a V (1,s,b) (s⁻¹ • (z-0)) :=
    funext (logInner_eq_normalized a V hs.1 b)
  rw [he]
  calc
    _ ≤ |s⁻¹| * ‖iteratedFDeriv ℝ n (variableLogProfile (scaledCutoff 1) a V (1,s,b))
        (s⁻¹ • (x-0))‖ / s^n := norm_iteratedFDeriv_scaled_dilate_le _ hf hs.1 s⁻¹ 0 x n
    _ ≤ |s⁻¹| * C / s^n := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound s ⟨hs.1.le,hs.2⟩ b hb _) (abs_nonneg _))
      (pow_nonneg hs.1.le n)
    _ = _ := by rw [abs_of_pos (inv_pos.mpr hs.1),pow_succ]; field_simp

lemma sqrtInner_derivatives_bounded (a : E → ℝ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Ioc (0:ℝ) R, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ n (fun z => scaledCutoff s z * sqrtSingularSource a V s b z) x‖ ≤
        C / s^n := by
  obtain ⟨C,hC,hbound⟩ := innerSqrtProfile_derivatives_bounded (scaledCutoff 1) a V
    (scaledCutoff_smooth _) (scaledCutoff_compact (by norm_num)) ha hV hK R n
  refine ⟨C,hC,?_⟩
  intro s hs b hb x
  have hf : ContDiff ℝ ∞ (variableSqrtProfile (scaledCutoff 1) a V (1,s,b)) :=
    (innerSqrtProfile_smooth (scaledCutoff 1) a V (scaledCutoff_smooth _) ha hV).comp
      ((show ContDiff ℝ ∞ (fun _ : E => (s,b)) from contDiff_const).prodMk contDiff_id)
  have he : (fun z => scaledCutoff s z * sqrtSingularSource a V s b z) =
      fun z => variableSqrtProfile (scaledCutoff 1) a V (1,s,b) (s⁻¹ • (z-0)) :=
    funext (sqrtInner_eq_normalized a V hs.1 b)
  rw [he]
  exact (norm_iteratedFDeriv_dilate_le _ hf hs.1 0 x n).trans
    (div_le_div_of_nonneg_right (hbound s ⟨hs.1.le,hs.2⟩ b hb _) (pow_nonneg hs.1.le n))
end TamingCompatibility.RadialPotential

end

end OAI
