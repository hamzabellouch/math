import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialGradientBridge
import OAI.Geometry.TamingCompatibility.Functional.RadialParameterJets

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def variableLogProfile (χ a : E → ℝ) (V : E → E) (p : ℝ × ℝ × E) (z : E) : ℝ :=
  χ z * (a (p.2.1 • z) * logGradientProfile p.1 z (V (p.2.2 + p.2.1 • z)))

def variableSqrtProfile (χ a : E → ℝ) (V : E → E) (p : ℝ × ℝ × E) (z : E) : ℝ :=
  χ z * (a (p.2.1 • z) * sqrtGradientProfile p.1 z (V (p.2.2 + p.2.1 • z)))

lemma variableLogProfile_smooth (χ a : E → ℝ) (V : E → E)
    (hχ : ContDiff ℝ ∞ χ) (h0 : (0:E) ∉ tsupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => variableLogProfile χ a V q.1 q.2) := by
  unfold variableLogProfile
  refine cutoff_parameter_smooth χ hχ h0
    (fun (p : ℝ × ℝ × E) z => a (p.2.1 • z) * logGradientProfile p.1 z
      (V (p.2.2 + p.2.1 • z))) ?_
  intro p hp
  have hpos : 0 < p.1.1^2 + ‖p.2‖^2 := by
    have hz := norm_pos_iff.mpr hp
    nlinarith [sq_nonneg p.1.1]
  have hscale : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => q.1.2.1 • q.2) :=
    (contDiff_fst.snd.fst).smul contDiff_snd
  have hpoint : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => q.1.2.2 + q.1.2.1 • q.2) :=
    (contDiff_fst.snd.snd).add hscale
  have hden : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => q.1.1^2 + ‖q.2‖^2) :=
    (contDiff_fst.fst.pow 2).add ((contDiff_norm_sq ℝ).comp contDiff_snd)
  exact (ha.comp hscale).contDiffAt.mul
    ((hden.contDiffAt.inv hpos.ne').mul
      (contDiff_snd.inner ℝ (hV.comp hpoint)).contDiffAt)

lemma variableSqrtProfile_smooth (χ a : E → ℝ) (V : E → E)
    (hχ : ContDiff ℝ ∞ χ) (h0 : (0:E) ∉ tsupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => variableSqrtProfile χ a V q.1 q.2) := by
  unfold variableSqrtProfile
  refine cutoff_parameter_smooth χ hχ h0
    (fun (p : ℝ × ℝ × E) z => a (p.2.1 • z) * sqrtGradientProfile p.1 z
      (V (p.2.2 + p.2.1 • z))) ?_
  intro p hp
  have hpos : 0 < p.1.1^2 + ‖p.2‖^2 := by
    have hz := norm_pos_iff.mpr hp
    nlinarith [sq_nonneg p.1.1]
  have hscale : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => q.1.2.1 • q.2) :=
    (contDiff_fst.snd.fst).smul contDiff_snd
  have hpoint : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => q.1.2.2 + q.1.2.1 • q.2) :=
    (contDiff_fst.snd.snd).add hscale
  have hden : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × E) × E => q.1.1^2 + ‖q.2‖^2) :=
    (contDiff_fst.fst.pow 2).add ((contDiff_norm_sq ℝ).comp contDiff_snd)
  exact (ha.comp hscale).contDiffAt.mul
    (((hden.contDiffAt.sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne').mul
      (contDiff_snd.inner ℝ (hV.comp hpoint)).contDiffAt)

lemma variableLogProfile_derivatives_bounded (χ a : E → ℝ) (V : E → E)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h0 : (0:E) ∉ tsupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) R, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (variableLogProfile χ a V (t,r,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_cutoff_derivatives_bounded χ hχc
    (fun (p : ℝ × ℝ × E) z => a (p.2.1 • z) * logGradientProfile p.1 z
      (V (p.2.2 + p.2.1 • z)))
    (variableLogProfile_smooth χ a V hχ h0 ha hV)
    (isCompact_Icc.prod (isCompact_Icc.prod hK)) n
  exact ⟨C,hC,fun t ht r hr b hb z => h (t,r,b) ⟨ht,hr,hb⟩ z⟩

lemma variableSqrtProfile_derivatives_bounded (χ a : E → ℝ) (V : E → E)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h0 : (0:E) ∉ tsupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) R, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (variableSqrtProfile χ a V (t,r,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_cutoff_derivatives_bounded χ hχc
    (fun (p : ℝ × ℝ × E) z => a (p.2.1 • z) * sqrtGradientProfile p.1 z
      (V (p.2.2 + p.2.1 • z)))
    (variableSqrtProfile_smooth χ a V hχ h0 ha hV)
    (isCompact_Icc.prod (isCompact_Icc.prod hK)) n
  exact ⟨C,hC,fun t ht r hr b hb z => h (t,r,b) ⟨ht,hr,hb⟩ z⟩

variable [HasContDiffBump E]
lemma shellCutoff_origin_not_tsupport {r : ℝ} (hr : 0 < r) :
    (0:E) ∉ tsupport (shellCutoff r : E → ℝ) := by
  intro h
  exact (shellCutoff_tsupport hr h).2 (by simpa using hr)

lemma variableLogProfile_shell_scale (a : E → ℝ) (V : E → E)
    {r s : ℝ} (hr : 0 < r) (b z : E) :
    r * (shellCutoff r (r • z) * (a (r • z) * logGradientProfile s (r • z) (V (b+r•z)))) =
      variableLogProfile (shellCutoff 1) a V (s/r,r,b) z := by
  rw [shellCutoff_scale hr.ne']
  have h := logGradientProfile_scale hr (s := s/r) z (V (b+r•z))
  rw [mul_div_cancel₀ s hr.ne'] at h
  dsimp only [variableLogProfile]
  calc
    _ = shellCutoff 1 z * (a (r • z) * (r * logGradientProfile s (r • z) (V (b+r•z)))) := by ring
    _ = _ := by rw [h]

lemma variableSqrtProfile_shell_scale (a : E → ℝ) (V : E → E)
    {r s : ℝ} (hr : 0 < r) (b z : E) :
    shellCutoff r (r • z) * (a (r • z) * sqrtGradientProfile s (r • z) (V (b+r•z))) =
      variableSqrtProfile (shellCutoff 1) a V (s/r,r,b) z := by
  rw [shellCutoff_scale hr.ne']
  have h := sqrtGradientProfile_scale hr (s := s/r) z (V (b+r•z))
  rw [mul_div_cancel₀ s hr.ne'] at h
  exact congrArg (fun x => shellCutoff 1 z * (a (r • z) * x)) h
end TamingCompatibility.RadialPotential

end
end

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma innerLogProfile_smooth (χ a : E → ℝ) (V : E → E)
    (hχ : ContDiff ℝ ∞ χ) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun q : (ℝ × E) × E => variableLogProfile χ a V (1,q.1.1,q.1.2) q.2) := by
  have hscale : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => q.1.1 • q.2) :=
    contDiff_fst.fst.smul contDiff_snd
  have hpoint : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => q.1.2 + q.1.1 • q.2) :=
    contDiff_fst.snd.add hscale
  have hden : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => (1:ℝ)^2 + ‖q.2‖^2) :=
    contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_snd)
  have hpos : ∀ q : (ℝ × E) × E, 0 < (1:ℝ)^2 + ‖q.2‖^2 := by
    intro q; nlinarith [sq_nonneg ‖q.2‖]
  exact (hχ.comp contDiff_snd).mul ((ha.comp hscale).mul
    ((hden.inv (fun q => (hpos q).ne')).mul (contDiff_snd.inner ℝ (hV.comp hpoint))))

lemma innerSqrtProfile_smooth (χ a : E → ℝ) (V : E → E)
    (hχ : ContDiff ℝ ∞ χ) (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun q : (ℝ × E) × E => variableSqrtProfile χ a V (1,q.1.1,q.1.2) q.2) := by
  have hscale : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => q.1.1 • q.2) :=
    contDiff_fst.fst.smul contDiff_snd
  have hpoint : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => q.1.2 + q.1.1 • q.2) :=
    contDiff_fst.snd.add hscale
  have hden : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => (1:ℝ)^2 + ‖q.2‖^2) :=
    contDiff_const.add ((contDiff_norm_sq ℝ).comp contDiff_snd)
  have hpos : ∀ q : (ℝ × E) × E, 0 < (1:ℝ)^2 + ‖q.2‖^2 := by
    intro q; nlinarith [sq_nonneg ‖q.2‖]
  exact (hχ.comp contDiff_snd).mul ((ha.comp hscale).mul
    (((hden.sqrt (fun q => (hpos q).ne')).inv
      (fun q => (Real.sqrt_pos.mpr (hpos q)).ne')).mul (contDiff_snd.inner ℝ (hV.comp hpoint))))

lemma innerLogProfile_derivatives_bounded (χ a : E → ℝ) (V : E → E)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) R, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (variableLogProfile χ a V (1,r,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_cutoff_derivatives_bounded χ hχc
    (fun (p : ℝ × E) z => a (p.1 • z) * logGradientProfile 1 z (V (p.2 + p.1 • z)))
    (innerLogProfile_smooth χ a V hχ ha hV) (isCompact_Icc.prod hK) n
  exact ⟨C,hC,fun r hr b hb z => h (r,b) ⟨hr,hb⟩ z⟩

lemma innerSqrtProfile_derivatives_bounded (χ a : E → ℝ) (V : E → E)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ V)
    {K : Set E} (hK : IsCompact K) (R : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) R, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (variableSqrtProfile χ a V (1,r,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_cutoff_derivatives_bounded χ hχc
    (fun (p : ℝ × E) z => a (p.1 • z) * sqrtGradientProfile 1 z (V (p.2 + p.1 • z)))
    (innerSqrtProfile_smooth χ a V hχ ha hV) (isCompact_Icc.prod hK) n
  exact ⟨C,hC,fun r hr b hb z => h (r,b) ⟨hr,hb⟩ z⟩

variable [HasContDiffBump E]
lemma variableLogProfile_inner_scale (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b z : E) :
    s * (scaledCutoff s (s • z) * (a (s • z) * logGradientProfile s (s • z) (V (b+s•z)))) =
      variableLogProfile (scaledCutoff 1) a V (1,s,b) z := by
  have hc : scaledCutoff s (s • z) = scaledCutoff 1 z := by
    simpa using scaledCutoff_scale hs.ne' 1 z
  rw [hc]
  have h := logGradientProfile_scale hs (s := 1) z (V (b+s•z))
  rw [mul_one] at h
  dsimp only [variableLogProfile]
  calc
    _ = scaledCutoff 1 z * (a (s • z) * (s * logGradientProfile s (s • z) (V (b+s•z)))) := by ring
    _ = _ := by rw [h]

lemma variableSqrtProfile_inner_scale (a : E → ℝ) (V : E → E)
    {s : ℝ} (hs : 0 < s) (b z : E) :
    scaledCutoff s (s • z) * (a (s • z) * sqrtGradientProfile s (s • z) (V (b+s•z))) =
      variableSqrtProfile (scaledCutoff 1) a V (1,s,b) z := by
  have hc : scaledCutoff s (s • z) = scaledCutoff 1 z := by
    simpa using scaledCutoff_scale hs.ne' 1 z
  rw [hc]
  have h := sqrtGradientProfile_scale hs (s := 1) z (V (b+s•z))
  rw [mul_one] at h
  exact congrArg (fun x => scaledCutoff 1 z * (a (s • z) * x)) h
end TamingCompatibility.RadialPotential

end
end

end
end

end OAI
