import Mathlib
import OAI.Probability.SKRatio.Matrices.BrownianUnitLaw

namespace OAI

section
section
noncomputable section
namespace SKRatioGaussian.PathBridge
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0→Ω→ℝ}

def normalizedIncrement (B : ℝ≥0→Ω→ℝ) (s δ : ℝ≥0) : ℝ≥0→Ω→ℝ :=
  fun t ω=>(sqrt δ)⁻¹*(B (s+δ*t) ω-B s ω)

def incrementEnergy (B : ℝ≥0→Ω→ℝ) (s δ : ℝ≥0) (n : ℕ) (ω : Fin n→Ω) : ℝ :=
  pathEnergy n (fun i=>continuousPathVersion (unitBrownianProcess (normalizedIncrement B s δ)) (ω i))

lemma incrementEnergy_tail (hB : IsBrownianReal B P) :
    ∃ H : ℝ, 0<H ∧ ∀ s δ : ℝ≥0, δ≠0 → ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n=>P)).real
        {ω | H*(n:ℝ) ≤ incrementEnergy B s δ n ω} ≤ exp (-(n:ℝ)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨H,hH,ht⟩ := brownian_normalized_increment_tail hB
  refine ⟨H,hH,fun s δ hδ n=>?_⟩
  have hb : IsBrownianReal (normalizedIncrement B s δ) P := (hB.shift s).smul hδ
  have hm := aemeasurable_continuousPathVersion (brownian_unit_gaussian hb).aemeasurable
    (brownian_unit_continuous hb)
  let := brownianUnitLaw_probability hb
  have hp := Measure.pi_map_pi (ι:=Fin n) (fun _=>hm)
  have ha : AEMeasurable (fun ω : Fin n→Ω=>fun i=>
      continuousPathVersion (unitBrownianProcess (normalizedIncrement B s δ)) (ω i))
      (Measure.pi (fun _ : Fin n=>P)) :=
    AEMeasurable.of_eval (fun index=>hm.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval _ index))
  have hset : MeasurableSet {f : Fin n→UnitPath | H*(n:ℝ) ≤ pathEnergy n f} := by
    apply measurableSet_le measurable_const
    unfold pathEnergy
    fun_prop
  have hh := map_measureReal_apply_of_aemeasurable ha hset
  rw [hp] at hh
  rw [show {ω : Fin n→Ω | H*(n:ℝ) ≤ incrementEnergy B s δ n ω} =
    (fun ω : Fin n→Ω=>fun i=>continuousPathVersion
      (unitBrownianProcess (normalizedIncrement B s δ)) (ω i)) ⁻¹'
        {f | H*(n:ℝ) ≤ pathEnergy n f} from rfl,← hh]
  exact ht s δ hδ n

omit [MeasurableSpace Ω] in
lemma increment_square_sum_le {s δ : ℝ≥0} (hδ : δ≠0) (n : ℕ) (ω : Fin n→Ω)
    (hc : ∀ i,Continuous (fun t=>unitBrownianProcess (normalizedIncrement B s δ) t (ω i)))
    (t : UnitInterval) :
    ∑ i,(B (s+δ*⟨t.1,t.2.1⟩) (ω i)-B s (ω i))^2 ≤
      (δ:ℝ)*incrementEnergy B s δ n ω := by
  have hδp : 0<(δ:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hδ)
  have hs : 0<sqrt (δ:ℝ) := sqrt_pos.2 hδp
  unfold incrementEnergy pathEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hf : continuousPathVersion (unitBrownianProcess (normalizedIncrement B s δ)) (ω i) t =
      (sqrt δ)⁻¹*(B (s+δ*⟨t.1,t.2.1⟩) (ω i)-B s (ω i)) := by
    simp only [continuousPathVersion,dite_eq_left (hc i),ContinuousMap.coe_mk]
    rfl
  have hn := ContinuousMap.norm_coe_le_norm
    (continuousPathVersion (unitBrownianProcess (normalizedIncrement B s δ)) (ω i)) t
  rw [hf,Real.norm_eq_abs] at hn
  have hh := sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.2 hn
  rw [sq_abs,mul_pow,inv_pow,Real.sq_sqrt hδp.le] at hh
  have hv := mul_le_mul_of_nonneg_left hh hδp.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hδp.ne',one_mul] using hv

theorem brownian_coordinate_modulus (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0<κ) :
    ∃ δ : ℝ≥0, 0<δ ∧ ∀ s : ℝ≥0, ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n=>P)).real
        {ω | ∃ t : UnitInterval,
          κ^2*(n:ℝ) < ∑ i,(B (s+δ*⟨t.1,t.2.1⟩) (ω i)-B s (ω i))^2} ≤ exp (-(n:ℝ)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨H,hH,ht⟩ := incrementEnergy_tail hB
  let δ : ℝ≥0 := ⟨κ^2/H,le_of_lt (div_pos (sq_pos_of_pos hκ) hH)⟩
  have hδ : 0<δ := div_pos (sq_pos_of_pos hκ) hH
  refine ⟨δ,hδ,fun s n=>?_⟩
  have hb : IsBrownianReal (normalizedIncrement B s δ) P := (hB.shift s).smul hδ.ne'
  have hc : ∀ᵐ ω : Fin n→Ω ∂Measure.pi (fun _ : Fin n=>P),
      ∀ i,Continuous (fun t=>unitBrownianProcess (normalizedIncrement B s δ) t (ω i)) := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n=>P) (i:=i)) (brownian_unit_continuous hb)
  have hm : ∀ᵐ ω ∂Measure.pi (fun _ : Fin n=>P),
      (∃ t : UnitInterval,κ^2*(n:ℝ) < ∑ i,(B (s+δ*⟨t.1,t.2.1⟩) (ω i)-B s (ω i))^2) →
        H*(n:ℝ) ≤ incrementEnergy B s δ n ω := by
    filter_upwards [hc] with ω hω
    rintro ⟨t,ht⟩
    have hh := increment_square_sum_le hδ.ne' n ω hω t
    change _ ≤ (κ^2/H)*_ at hh
    rw [div_mul_eq_mul_div,le_div_iff₀ hH] at hh
    nlinarith [sq_pos_of_pos hκ]
  calc
    _ ≤ (Measure.pi (fun _ : Fin n=>P)).real {ω | H*(n:ℝ) ≤ incrementEnergy B s δ n ω} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hm)
    _ ≤ _ := ht s δ hδ.ne' n

theorem brownian_coordinate_modulus_small (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0<κ) :
    ∃ δ₀ : ℝ, 0<δ₀ ∧ ∀ s δ : ℝ≥0, 0<δ → (δ:ℝ)≤δ₀ → ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n=>P)).real
        {ω | ∃ t : UnitInterval,
          κ^2*(n:ℝ) < ∑ i,(B (s+δ*⟨t.1,t.2.1⟩) (ω i)-B s (ω i))^2} ≤ exp (-(n:ℝ)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨H,hH,ht⟩ := incrementEnergy_tail hB
  refine ⟨κ^2/H,div_pos (sq_pos_of_pos hκ) hH,fun s δ hδ hδ₀ n=>?_⟩
  have hb : IsBrownianReal (normalizedIncrement B s δ) P := (hB.shift s).smul hδ.ne'
  have hc : ∀ᵐ ω : Fin n→Ω ∂Measure.pi (fun _ : Fin n=>P),
      ∀ i,Continuous (fun t=>unitBrownianProcess (normalizedIncrement B s δ) t (ω i)) := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n=>P) (i:=i)) (brownian_unit_continuous hb)
  have hm : ∀ᵐ ω ∂Measure.pi (fun _ : Fin n=>P),
      (∃ t : UnitInterval,κ^2*(n:ℝ) < ∑ i,(B (s+δ*⟨t.1,t.2.1⟩) (ω i)-B s (ω i))^2) →
        H*(n:ℝ) ≤ incrementEnergy B s δ n ω := by
    filter_upwards [hc] with ω hω
    rintro ⟨t,ht⟩
    have hh := increment_square_sum_le hδ.ne' n ω hω t
    have he : 0 ≤ incrementEnergy B s δ n ω  := by
      unfold incrementEnergy pathEnergy
      exact Finset.sum_nonneg (fun i _=>sq_nonneg _)
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hδ₀ he)
    rw [div_mul_eq_mul_div,le_div_iff₀ hH] at hh'
    nlinarith [sq_pos_of_pos hκ]
  calc
    _ ≤ (Measure.pi (fun _ : Fin n=>P)).real {ω | H*(n:ℝ) ≤ incrementEnergy B s δ n ω} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hm)
    _ ≤ _ := ht s δ hδ.ne' n
end SKRatioGaussian.PathBridge

end
end

section
noncomputable section

end
end
end

end OAI
