import Mathlib
import OAI.Probability.SphericalField.Heat.Derivatives

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma expBCF_norm_le (d : ℝ) (f : ℝ →ᵇ ℝ) :
    ‖expBCF d f‖ ≤ Real.exp (|d| * ‖f‖) := by
  rw [BoundedContinuousFunction.norm_le (Real.exp_pos _).le]
  exact exp_bcf_bound d f

lemma Jet3.exp_norms (g : Jet3) (d C₀ C₁ C₂ C₃ : ℝ≥0)
    (h₀ : ‖g.f‖ ≤ C₀) (h₁ : ‖g.d1‖ ≤ C₁) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃) :
    let E := Real.exp ((d : ℝ)*C₀)
    ‖(g.exp d).f‖ ≤ E ∧ ‖(g.exp d).d1‖ ≤ (d : ℝ)*E*C₁ ∧
    ‖(g.exp d).d2‖ ≤ E*((d : ℝ)^2*C₁^2 + d*C₂) ∧
    ‖(g.exp d).d3‖ ≤ E*((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*C₁*C₂ + d*C₃) := by
  dsimp only
  have hf : ‖expBCF d g.f‖ ≤ Real.exp ((d : ℝ)*C₀) := by
    refine (expBCF_norm_le d g.f).trans ?_
    rw [abs_of_nonneg d.coe_nonneg]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h₀ d.coe_nonneg)
  refine ⟨hf, ?_, ?_, ?_⟩
  · change ‖(d : ℝ) • (expBCF d g.f * g.d1)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ) * (‖expBCF d g.f‖ * ‖g.d1‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ (d : ℝ) * (Real.exp ((d : ℝ)*C₀) * C₁) := by gcongr
      _ = _ := by ring
  · change ‖expBCF d g.f * ((d : ℝ)^2 • (g.d1^2) + (d : ℝ) • g.d2)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * (‖(d : ℝ)^2 • (g.d1^2)‖ + ‖(d : ℝ) • g.d2‖) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^2 * ‖g.d1^2‖ + (d : ℝ) * ‖g.d2‖) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg, abs_pow]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^2 * C₁^2 + (d : ℝ) * C₂) := by
        gcongr
        exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖expBCF d g.f * ((d : ℝ)^3 • (g.d1^3) + (3*(d : ℝ)^2) • (g.d1*g.d2) + (d : ℝ) • g.d3)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * ((‖(d : ℝ)^3 • (g.d1^3)‖ + ‖(3*(d : ℝ)^2) • (g.d1*g.d2)‖) + ‖(d : ℝ) • g.d3‖) := by
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^3 * ‖g.d1^3‖ + 3*(d : ℝ)^2*‖g.d1*g.d2‖ + (d : ℝ)*‖g.d3‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ)^3),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3*(d : ℝ)^2), abs_of_nonneg d.coe_nonneg]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*(C₁*C₂) + (d : ℝ)*C₃) := by
        gcongr
        · exact (norm_pow_le _ _).trans (by gcongr)
        · exact (norm_mul_le _ _).trans (by gcongr)
      _ = _ := by ring

lemma Jet3.heatLog_uniform_bounds (d : ℝ≥0) (g : Jet3) :
    ∃ C₀ C₁ C₂ C₃ : ℝ≥0, ∀ s : ℝ≥0,
      ‖(g.heatLog s d).f‖ ≤ C₀ ∧ ‖(g.heatLog s d).d1‖ ≤ C₁ ∧
      ‖(g.heatLog s d).d2‖ ≤ C₂ ∧ ‖(g.heatLog s d).d3‖ ≤ C₃ := by
  by_cases hd : d = 0
  · subst d
    refine ⟨‖g.f‖₊, ‖g.d1‖₊, ‖g.d2‖₊, ‖g.d3‖₊, ?_⟩
    intro s; simpa only [Jet3.heatLog, ↓reduceDIte, coe_nnnorm] using g.gaussianAverage_norms s
  let e := g.exp d
  let B := (Real.exp (-(d : ℝ)*‖g.f‖))⁻¹
  let r := (d : ℝ)⁻¹
  have hB : 0 ≤ B := by positivity
  have hr : 0 ≤ r := by positivity
  refine ⟨‖g.f‖₊,
    ⟨r*(‖e.d1‖*B), by positivity⟩,
    ⟨r*(‖e.d2‖*B+‖e.d1‖^2*B^2), by positivity⟩,
    ⟨r*(‖e.d3‖*B+3*(‖e.d1‖*‖e.d2‖*B^2)+2*(‖e.d1‖^3*B^3)), by positivity⟩, ?_⟩
  intro s
  let A := e.gaussianAverage s
  let c := Real.exp (-(d : ℝ)*‖g.f‖)
  let hc := Real.exp_pos (-(d : ℝ)*‖g.f‖)
  let hA : ∀ x, c ≤ A.f x := fun x => (gaussianAverage_exp_bounds s d d.coe_nonneg g.f x).1
  let J := invBCF A.f c hc hA
  have hj : ‖J‖ ≤ B := invBCF_norm_le A.f c hc hA
  obtain ⟨_, h₁,h₂,h₃⟩ := e.gaussianAverage_norms s
  have hf : ‖(g.heatLog s d).f‖ ≤ ‖g.f‖ := by
    rw [g.heatLog_f, BoundedContinuousFunction.norm_le (norm_nonneg _)]
    exact heatLog_abs_le s d g.f
  rw [Jet3.heatLog, dite_eq_right hd]
  refine ⟨by simpa only [Jet3.heatLog, dite_eq_right hd, coe_nnnorm] using hf, ?_, ?_, ?_⟩
  · change ‖r • (A.d1*J)‖ ≤ r * (‖e.d1‖*B)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (by gcongr)) hr
  · change ‖r • (A.d2*J - A.d1^2*J^2)‖ ≤ r*(‖e.d2‖*B+‖e.d1‖^2*B^2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    gcongr
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖r • (A.d3*J - (3 : ℝ) • (A.d1*A.d2*J^2) + (2 : ℝ) • (A.d1^3*J^3))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_left _ hr
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_mul_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)

lemma heatLog_generator_uniform (d C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (g : Jet3), ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ →
      ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ → ∀ (s : ℝ≥0), s ≤ 1 → ∀ x : ℝ,
        |heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)| ≤
          (C : ℝ) * (s : ℝ) * Real.sqrt s := by
  let M := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  have hM : 0 ≤ M := integral_nonneg (fun z => by positivity)
  by_cases hd : d = 0
  · subst d
    refine ⟨⟨(C₃ : ℝ)/6*M, by positivity⟩, ?_⟩
    intro g _ _ _ h₃ s _ x
    simp only [heatLog, ↓reduceIte, NNReal.coe_zero, zero_mul, add_zero]
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * M := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * M := by gcongr
      _ = (C₃ : ℝ)/6*M * (s : ℝ) * Real.sqrt s := by
        have hh := Real.sq_sqrt s.coe_nonneg
        calc
          _ = (C₃ : ℝ)/6*M * (Real.sqrt s)^2 * Real.sqrt s := by ring
          _ = _ := by rw [hh]
  let c := Real.exp (-(d : ℝ)*C₀)
  let E := Real.exp ((d : ℝ)*C₀)
  let E₂ : ℝ≥0 := ⟨E*((d : ℝ)^2*C₁^2+(d : ℝ)*C₂), by positivity⟩
  let E₃ : ℝ≥0 := ⟨E*((d : ℝ)^3*C₁^3+3*(d : ℝ)^2*C₁*C₂+(d : ℝ)*C₃), by positivity⟩
  let K := ((E₂ : ℝ)/2+(E₃ : ℝ)/6*M)^2/c^2 + ((E₃ : ℝ)/6*M)/c
  have hc : 0 < c := Real.exp_pos _
  have hK : 0 ≤ K := by positivity
  have hdpos : (0 : ℝ) < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd)
  refine ⟨⟨(d : ℝ)⁻¹*K, by positivity⟩, ?_⟩
  intro g h₀ h₁ h₂ h₃ s hs x
  have hh := g.exp_norms d C₀ C₁ C₂ C₃ h₀ h₁ h₂ h₃
  have hlo (x : ℝ) : c ≤ (g.exp d).f x := by
    change Real.exp (-(d : ℝ)*C₀) ≤ Real.exp ((d : ℝ)*g.f x)
    apply Real.exp_le_exp.mpr
    have hb : |g.f x| ≤ C₀ := (g.f.norm_coe_le_norm x).trans h₀
    nlinarith [(abs_le.mp hb).1]
  have herr := log_gaussian_generator_error (g.exp d) c hc hlo E₂ E₃ hh.2.2.1 hh.2.2.2 s hs x
  have he : (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x =
      (d : ℝ) * ((s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)) := by
    change (s : ℝ)/2 * (Real.exp ((d : ℝ)*g.f x) * ((d : ℝ)^2*g.d1 x^2 + (d : ℝ)*g.d2 x)) /
      Real.exp ((d : ℝ)*g.f x) = _
    field_simp
    ring
  have hid : heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x+(d : ℝ)*g.d1 x^2) =
      (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (g.exp d).f x) - Real.log ((g.exp d).f x) -
        (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x) := by
    rw [he]
    change _ = (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (expBCF d g.f) x) -
      Real.log (Real.exp ((d : ℝ)*g.f x)) - _)
    rw [Real.log_exp]
    simp only [heatLog, hd, ↓reduceIte]
    field_simp
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hdpos)]
  calc
    _ ≤ (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hdpos.le)
    _ = _ := by change (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) = (d : ℝ)⁻¹*K*(s : ℝ)*Real.sqrt s; ring

end SphericalPerceptron
end
end

end OAI
