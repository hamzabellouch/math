import OAI.Analysis.HenonEmden.CapWeights

namespace OAI

universe uE

section SphereCaps

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.CapWeights

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def lowerConstant : ℝ := (μ (ball (0:E) 1)).toReal /
  (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) / 2^(Module.finrank ℝ E)
def upperConstant : ℝ := 4^Module.finrank ℝ E*(μ (ball (0:E) 1)).toReal

omit [BorelSpace E] [Nontrivial E] in
lemma constants_positive : 0 < lowerConstant μ ∧ 0 < upperConstant μ := by
  obtain ⟨hc,hC⟩ := CapGeometry.cap_constants_pos μ
  exact ⟨div_pos hc (by positivity),hC⟩

lemma sphere_normalizer_bounds (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    lowerConstant μ*l^(Module.finrank ℝ E-1) ≤ normalizer μ.toSphere θ l ∧
    normalizer μ.toSphere θ l ≤ upperConstant μ*l^(Module.finrank ℝ E-1) := by
  have hb := normalizer_bounds μ.toSphere θ hl
  have hlo := (CapGeometry.cap_real_bounds μ θ (by linarith : 0 < l/2) (by linarith : l/2 ≤ 1)).1
  have hhi := (CapGeometry.cap_real_bounds μ θ hl hl1).2
  refine ⟨?_,hb.2.trans hhi⟩
  have hn : Module.finrank ℝ E-1+1 = Module.finrank ℝ E :=
    Nat.sub_add_cancel (Module.finrank_pos : 0 < Module.finrank ℝ E)
  apply le_trans _ hb.1
  convert div_le_div_of_nonneg_right hlo (by norm_num : (0:ℝ) ≤ 2) using 1
  unfold lowerConstant
  have h2 : (2:ℝ)^Module.finrank ℝ E = 2^(Module.finrank ℝ E-1)*2 := by
    nth_rw 1 [← hn]; rw [pow_succ]
  rw [div_pow,h2]
  ring

lemma sphere_normalizer_pos (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    0 < normalizer μ.toSphere θ l :=
  (mul_pos (constants_positive μ).1 (pow_pos hl _)).trans_le (sphere_normalizer_bounds μ θ hl hl1).1

/-- Oscillation of a normalized cap with comparable radii, uniformly in directions. -/
lemma sphere_normalized_oscillation
    {θ θ' : sphere (0:E) 1} {l l' ρ : ℝ} (hρ : 0 < ρ)
    (hl : ρ/2 ≤ l) (hl' : ρ/2 ≤ l') (hlU : l ≤ 2*ρ) (hlU' : l' ≤ 2*ρ)
    (hl1 : l ≤ 1) (hl1' : l' ≤ 1) (e : sphere (0:E) 1) :
    |normalized μ.toSphere θ l e-normalized μ.toSphere θ' l' e| ≤
      (2/(lowerConstant μ/2^(Module.finrank ℝ E-1))+
        2*(2^(Module.finrank ℝ E)*upperConstant μ)/(lowerConstant μ/2^(Module.finrank ℝ E-1))^2)*
      (dist θ θ'+2*|l-l'|)/ρ^(Module.finrank ℝ E) := by
  let d := Module.finrank ℝ E-1
  let c := lowerConstant μ/2^d
  let C := 2^(Module.finrank ℝ E)*upperConstant μ
  have hc : 0 < c := div_pos (constants_positive μ).1 (by positivity)
  have hC : 0 < C := mul_pos (by positivity) (constants_positive μ).2
  have hl0 : 0 < l := (half_pos hρ).trans_le hl
  have hl0' : 0 < l' := (half_pos hρ).trans_le hl'
  have hZ (θ : sphere (0:E) 1) {l : ℝ} (hl : ρ/2 ≤ l) (hl1 : l ≤ 1) :
      c*ρ^d ≤ normalizer μ.toSphere θ l := by
    apply le_trans _ (sphere_normalizer_bounds μ θ ((half_pos hρ).trans_le hl) hl1).1
    calc
      _ = lowerConstant μ*(ρ/2)^d := by rw [div_pow]; dsimp [c]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (half_pos hρ).le hl d) (constants_positive μ).1.le
  have hmu (θ : sphere (0:E) 1) {l : ℝ} (hl0 : 0 < l) (hlU : l ≤ 2*ρ) (hl1 : l ≤ 1) :
      (μ.toSphere (ball θ l)).toReal ≤ upperConstant μ*(2*ρ)^d := by
    exact (CapGeometry.cap_real_bounds μ θ hl0 hl1).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0.le hlU d) (constants_positive μ).2.le)
  have hμ : (μ.toSphere (ball θ l)).toReal+(μ.toSphere (ball θ' l')).toReal ≤ C*ρ^d := by
    apply le_trans (add_le_add (hmu θ hl0 hlU hl1) (hmu θ' hl0' hlU' hl1'))
    have hn : d+1 = Module.finrank ℝ E := Nat.sub_add_cancel (Module.finrank_pos : 0 < Module.finrank ℝ E)
    apply le_of_eq
    dsimp [C]
    rw [← hn,pow_succ,mul_pow]
    ring
  have hparam : (dist θ θ'+2*|l-l'|)/l ≤ 2*(dist θ θ'+2*|l-l'|)/ρ := by
    calc
      _ ≤ (dist θ θ'+2*|l-l'|)/(ρ/2) := div_le_div_of_nonneg_left (by positivity) (half_pos hρ) hl
      _ = _ := by ring
  have hh := normalized_oscillation μ.toSphere hl0 hl0' (mul_pos hc (pow_pos hρ d))
    (hZ θ hl hl1) (hZ θ' hl' hl1') hμ hparam e
  apply hh.trans
  have hn : d+1 = Module.finrank ℝ E := Nat.sub_add_cancel (Module.finrank_pos : 0 < Module.finrank ℝ E)
  apply le_of_eq
  change (1/(c*ρ^d)+C*ρ^d/(c*ρ^d)^2)*(2*(dist θ θ'+2*|l-l'|)/ρ) =
    (2/c+2*C/c^2)*(dist θ θ'+2*|l-l'|)/ρ^(Module.finrank ℝ E)
  rw [← hn,pow_succ]
  field_simp [ne_of_gt hc,ne_of_gt hρ]
  ring

end HenonLaneEmden.CapWeights
end
end SphereCaps

end OAI
