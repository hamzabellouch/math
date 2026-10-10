import Mathlib
import OAI.Geometry.CAT0Fillings.Powers.EulerMoments

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_all_powers (hz : IsCycle T) (P : q.Sobolev) {p A n S C : ℝ}
    (hp : 2 < p) (hA : 0 < A) (hn : 0 < n) (hS : 0 < S) (hC : 0 ≤ C)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hs : ∀ R : q.Sobolev,
      MemLp (q.inclusion R) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ∧
      S*(lpNorm (q.inclusion R) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT))^2 ≤
        A*‖q.closedGradient R‖^2+C*‖q.inclusion R‖^2)
    (heuler : ∀ R : q.Sobolev,
      A*inner ℝ (q.closedGradient P) (q.closedGradient R)+n*inner ℝ (q.inclusion P) (q.inclusion R) =
      n*(∫ x, (q.inclusion P x)^(p-1)*q.inclusion R x ∂MassMeasure.currentMassMeasure hT)) :
    (∀ b : ℝ, 0 < b → MemLp (q.inclusion P) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT)) ∧
    (∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => (q.inclusion P x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w)) := by
  have hgain (a : ℝ) (ha : 1 < a)
      (hv : MemLp (fun x => (q.inclusion P x)^a) 2 (MassMeasure.currentMassMeasure hT)) :
      MemLp (fun x => (q.inclusion P x)^a) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) := by
    obtain ⟨R,hRv,hRG⟩ := q.closed_euler_power hz P ha hp hA hn hS hC hP hv hs heuler
    exact MemLp.ae_eq hRv (hs R).1
  have hm := all_moments_of_power_gain hp hP (hs P).1 hgain
  refine ⟨hm,?_⟩
  intro γ hγ
  rcases hγ.eq_or_lt with hγ | hγ
  · subst γ
    refine ⟨P,?_,?_⟩
    · exact Eventually.of_forall fun _ => (Real.rpow_one _).symm
    · filter_upwards [] with w
      simp only [sub_self,Real.rpow_zero,mul_one,one_smul]
  · have hv := (memLp_power_iff (Lp.aestronglyMeasurable (q.inclusion P)) hP
      (by linarith : 0 < γ) (b := 2)).mpr (hm (γ*2) (by positivity))
    have hv' : MemLp (fun x => (q.inclusion P x)^γ) 2 (MassMeasure.currentMassMeasure hT) := by simpa using hv
    exact q.closed_euler_power hz P hγ hp hA hn hS hC hP hv' hs heuler

lemma weighted_gradient_memLp (P : q.Sobolev)
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w))
    {a : ℝ} (ha : 0 ≤ a) :
    MemLp (fun w => ((q.inclusion P (q.atlasParam w))^a) • q.closedGradient P w) 2 q.atlasMeasure := by
  obtain ⟨R,hR⟩ := hpow (a+1) (by linarith)
  have hr := (MemLp.ae_eq hR (Lp.memLp (q.closedGradient R))).const_smul ((a+1)⁻¹)
  apply (memLp_congr_ae ?_).mp hr
  filter_upwards [] with w
  simp only [Pi.smul_apply,add_sub_cancel_right,smul_smul]
  rw [←mul_assoc,inv_mul_cancel₀ (by linarith : a+1 ≠ 0),one_mul]

lemma polynomial_weighted_energy (P : q.Sobolev)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w))
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun w => (q.inclusion P (q.atlasParam w))^a * ‖q.closedGradient P w‖^2) q.atlasMeasure := by
  have hh := (q.weighted_gradient_memLp P hpow (show 0 ≤ a/2 by positivity)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  apply hh.congr
  filter_upwards [q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X => 0 ≤ q.inclusion P x) hP] with w hw
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hw _),mul_pow,←Real.rpow_mul_natCast hw]
  norm_num

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} [IsFiniteMeasure μ]
lemma power_memLp_two {f : α → ℝ} (hp : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hm : ∀ b : ℝ, 0 < b → MemLp f (ENNReal.ofReal b) μ) {a : ℝ} (ha : 0 ≤ a) :
    MemLp (fun x => (f x)^a) 2 μ := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    simpa only [Real.rpow_zero] using (memLp_const (1:ℝ) : MemLp (fun _ : α => (1:ℝ)) 2 μ)
  · have h := (memLp_power_iff (hm 2 (by norm_num)).aestronglyMeasurable hp ha (b := 2)).mpr
      (hm (a*2) (by positivity))
    simpa using h

lemma polynomial_domination_memLp {f : α → ℝ} {G : α → E} {a : ℝ}
    (hp : ∀ᵐ x ∂μ, 0 ≤ f x) (hf : MemLp (fun x => (f x)^a) 2 μ)
    (hG : MemLp G 2 μ) (hfg : MemLp (fun x => (f x)^a • G x) 2 μ) (C K : ℝ) :
    MemLp (fun x => C*(1+(f x)^a)*(K+‖G x‖)) 2 μ := by
  have hh := (((memLp_const (1:ℝ)).add hf).const_mul (C*K)).add
    ((hG.norm.add hfg.norm).const_mul C)
  apply (memLp_congr_ae ?_).mp hh
  filter_upwards [hp] with x hx
  simp only [Pi.add_apply,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx a)]
  ring
end CAT0Fillings.ClosedCalculus
end

section
open scoped NNReal

namespace CAT0Fillings.ClosedCalculus
lemma norm_binary_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b C K Z : ℝ} {u v : E} (hC : 0 ≤ C) (ha : |a| ≤ C) (hb : |b| ≤ C)
    (hu : ‖u‖ ≤ K) (hv : ‖v‖ ≤ Z) : ‖a • u+b • v‖ ≤ C*(K+Z) := by
  calc
    _ ≤ ‖a • u‖+‖b • v‖ := norm_add_le _ _
    _ = |a| *‖u‖+|b| *‖v‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ C*K+C*Z := add_le_add (mul_le_mul ha hu (norm_nonneg _) hC)
      (mul_le_mul hb hv (norm_nonneg _) hC)
    _ = _ := by ring
end CAT0Fillings.ClosedCalculus
end

end OAI
