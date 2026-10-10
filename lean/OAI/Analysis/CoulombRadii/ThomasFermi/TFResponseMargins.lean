import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.PatchResponse

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma tfScalarDensity_continuous : Continuous tfScalarDensity := by
  unfold tfScalarDensity
  exact (Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/2)).comp
    ((continuous_id.max continuous_const).div_const _)

lemma tfScalarDensity_strict {v w : ℝ} (hv : 0≤v) (hvw : v<w) :
    tfScalarDensity v<tfScalarDensity w := by
  unfold tfScalarDensity
  rw [max_eq_left hv,max_eq_left (hv.trans hvw.le)]
  apply Real.rpow_lt_rpow (div_nonneg hv (mul_nonneg thomasFermiKineticConstant_pos.le (by norm_num))) _ (by norm_num)
  exact (div_lt_div_iff_of_pos_right (mul_pos thomasFermiKineticConstant_pos (by norm_num))).mpr hvw

lemma tfScalarDensity_scale (v : ℝ) {a : ℝ} (ha : 0<a) :
    tfScalarDensity (v/a^4)=tfScalarDensity v/a^6 := by
  unfold tfScalarDensity
  have hmax : max (v/a^4) 0=max v 0/a^4 := by
    simpa only [zero_div] using max_div_div_right (pow_nonneg ha.le 4) v 0
  rw [hmax]
  have heq : max v 0/a^4/(thomasFermiKineticConstant*(5/3:ℝ)) =
      (max v 0/(thomasFermiKineticConstant*(5/3:ℝ)))/a^4 := by ring
  rw [heq,Real.div_rpow (div_nonneg (le_max_right _ _) (mul_nonneg thomasFermiKineticConstant_pos.le (by norm_num))) (pow_nonneg ha.le 4)]
  have hp : (a^4)^(3/2:ℝ)=a^6 := by
    rw [←Real.rpow_natCast a 4,←Real.rpow_mul ha.le]
    norm_num
  rw [hp]

theorem exists_tf_response_margins {hl hh η : ℝ} (hη : 0<η) (hηl : η<hl)
    (hlh : hl≤hh) : ∃ ε : ℝ, 0<ε ∧ ε≤1 ∧
    ∀ {h θ δ e : ℝ}, h∈Icc hl hh → 0≤θ → θ≤ε → 0≤δ → δ≤ε → 0≤e → e≤ε →
      tfScalarDensity (h-η+θ)*(1+δ)+e<tfScalarDensity h ∧
      tfScalarDensity h<tfScalarDensity (h+η-θ)*(1-δ)-e := by
  have hlo : 0<hl := hη.trans hηl
  have hcontL : Continuous (fun h => tfScalarDensity h-tfScalarDensity (h-η/2)) :=
    tfScalarDensity_continuous.sub (tfScalarDensity_continuous.comp (continuous_id.sub continuous_const))
  have hcontU : Continuous (fun h => tfScalarDensity (h+η/2)-tfScalarDensity h) :=
    (tfScalarDensity_continuous.comp (continuous_id.add continuous_const)).sub tfScalarDensity_continuous
  obtain ⟨minPoint,hminPoint,Hd₁⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hlh) hcontL.continuousOn
  let d₁ := tfScalarDensity minPoint-tfScalarDensity (minPoint-η/2)
  have hd₁ : 0<d₁ :=
    sub_pos.mpr (tfScalarDensity_strict (by linarith [hminPoint.1]) (by linarith))
  obtain ⟨d₂,hd₂,Hd₂⟩ := isCompact_Icc.exists_forall_le' hcontU.continuousOn
    (a:=0) (s:=Icc hl hh) (fun h hh' => sub_pos.mpr (tfScalarDensity_strict (by linarith [hh'.1]) (by linarith)))
  let A := tfScalarDensity (hh+η)
  have hA : 0≤A := tfScalarDensity_nonneg _
  let ε := min 1 (min (η/2) (min (d₁/(2*(A+1))) (d₂/(2*(A+1)))))
  have hε : 0<ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,min_le_left _ _,?_⟩
  intro h θ δ e hh' hθ hθε hδ hδε he heε
  have hεη : ε≤η/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεd₁ : ε≤d₁/(2*(A+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεd₂ : ε≤d₂/(2*(A+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd₁' := (le_div_iff₀ (show 0<2*(A+1) by positivity)).mp hεd₁
  have hd₂' := (le_div_iff₀ (show 0<2*(A+1) by positivity)).mp hεd₂
  have hb₁ : tfScalarDensity (h-η+θ)≤tfScalarDensity (h-η/2) := tfScalarDensity_mono (by linarith)
  have hb₂ : tfScalarDensity (h+η/2)≤tfScalarDensity (h+η-θ) := tfScalarDensity_mono (by linarith)
  have hc₁ : tfScalarDensity (h-η+θ)≤A := tfScalarDensity_mono (by linarith [hh'.2])
  have hc₂ : tfScalarDensity (h+η-θ)≤A := tfScalarDensity_mono (by linarith [hh'.2])
  have herr₁ := mul_le_mul hc₁ hδε hδ hA
  have herr₂ := mul_le_mul hc₂ hδε hδ hA
  have hg₁ : d₁≤tfScalarDensity h-tfScalarDensity (h-η/2) := Hd₁ hh'
  have hg₂ := Hd₂ h hh'
  constructor <;> nlinarith
end Coulomb
end

end

end OAI
