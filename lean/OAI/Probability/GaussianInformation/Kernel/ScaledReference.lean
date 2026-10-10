import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ReferenceMoments

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.Scale
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Sphere Coercivity ReferenceGaussian GaussianTools

lemma normalized_restriction {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (E : Set α) (hE : MeasurableSet E) (hm : 0 < ν E) :
    ∃ τ : Measure α, IsProbabilityMeasure τ ∧
      ENNReal.ofReal (ν E).toReal • τ ≤ ν ∧ (∀ᵐ u ∂τ,u ∈ E) := by
  let τ := (ν E)⁻¹ • ν.restrict E
  have hmt : ν E ≠ ∞ := measure_ne_top _ _
  refine ⟨τ,?_,?_,?_⟩
  · constructor
    simp only [τ,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hm.ne' hmt
  · rw [ENNReal.ofReal_toReal hmt]
    dsimp [τ]
    rw [smul_smul,ENNReal.mul_inv_cancel hm.ne' hmt,one_smul]
    exact Measure.restrict_le_self
  · exact (Measure.smul_absolutelyContinuous (μ := ν.restrict E) (c := (ν E)⁻¹)).ae_le (ae_restrict_mem hE)

lemma dyadic_log_identity (p j : ℕ) :
    Real.log ((2:ℝ)^(j*p)) = (p:ℝ)*Real.log 2-(p:ℝ)*Real.log (radius j) := by
  unfold radius
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow,
    Real.log_div (by norm_num) (by norm_num),Real.log_one]
  push_cast
  ring

lemma chosen_scale_log {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    {L j : ℕ} (hm : 0 < ν (closedBall s (radius j)))
    (hJ : J ν s ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*((L:ℝ)+2))*
      (ENNReal.ofReal ((2:ℝ)^(j*(2*(d/16))))*ν (closedBall s (radius j)))) :
    Real.log ((J ν s).toReal) ≤
      2*(2*(d/16):ℕ)*Real.log 2+Real.log ((L:ℝ)+2)+
       Real.log (ν (closedBall s (radius j))).toReal-(2*(d/16):ℕ)*Real.log (radius j) := by
  have hjpos : 0 < (J ν s).toReal :=
    lt_of_lt_of_le (by positivity) (J_real_bounds hd ν hH hν s hs).1
  have hmt : ν (closedBall s (radius j)) ≠ ∞ := measure_ne_top _ _
  have hmr : 0 < (ν (closedBall s (radius j))).toReal := ENNReal.toReal_pos hm.ne' hmt
  have hto := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt)) hJ
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2^(2*(d/16))*((L:ℝ)+2)),
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2^(j*(2*(d/16))))] at hto
  have hlog := Real.log_le_log hjpos hto
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hmr.ne',Real.log_pow,dyadic_log_identity] at hlog
  push_cast at hlog ⊢
  linarith

lemma radius_mono {i j : ℕ} (hij : i ≤ j) : radius j ≤ radius i := by
  unfold radius
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) hij) (by norm_num)

lemma reference_J_lower {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) (hs : ‖s‖=1) (L : ℕ) (hL : 0 < L)
    (hcut : ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1)
    (e : Fin (2*(d/16)) → ℝ) (he : ∀ i,|e i| ≤ radius L) :
    Real.log (J ν s).toReal-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤
      (∫ X : Mat (2*(d/16)) d,
        Real.log (mixture ν (fun j : Fin L => radius j) X (applyRows X s+e))
        ∂Measure.pi (fun _ : Fin (2*(d/16)) => scalarRow d)) := by
  obtain ⟨j,hj,hm,hjb⟩ := exists_J_scale hd ν hH hν s hs L hL hcut
  obtain ⟨τ,hτ,hdom,hτs⟩ := normalized_restriction ν (closedBall s (radius j)) measurableSet_closedBall hm
  have := hτ
  have hmr : 0 < (ν (closedBall s (radius j))).toReal := ENNReal.toReal_pos hm.ne' (measure_ne_top _ _)
  have hsupport : ∀ᵐ u ∂ν,u ∈ closedBall s 2 := by
    filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega))] with u hu
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by rw [hu,hs]; norm_num)
  have hlow := local_mixture_rows_ge hL ν τ hmr hdom (fun j : Fin L => radius j)
    (fun j => radius_pos j) s (radius_pos j).le (by norm_num : (0:ℝ) ≤ 2)
    hτs hsupport e ⟨j,hj⟩
  have hJlog := chosen_scale_log hd ν hH hν s hs hm hjb
  have he2 : (∑ i : Fin (2*(d/16)),e i^2) ≤ (2*(d/16):ℕ)*(radius j)^2 := by
    calc
      _ ≤ ∑ _i : Fin (2*(d/16)),(radius j)^2 := by
        apply Finset.sum_le_sum; intro i _
        have hie : |e i| ≤ radius j := (he i).trans (radius_mono (by omega))
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hie 2
      _ = _ := by simp
  have henergy : ((2*(d/16):ℕ)*(radius j)^2+∑ i,e i^2)/(radius j)^2 ≤ 2*(2*(d/16):ℕ) := by
    apply (div_le_iff₀ (sq_pos_of_pos (radius_pos j))).mpr
    linarith
  have hlL : Real.log L ≤ Real.log ((L:ℝ)+2) := Real.log_le_log (by positivity) (by linarith)
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hlpi : Real.log (2*Real.pi) ≤ 7 := by
    have hh := Real.log_le_sub_one_of_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)
    linarith [Real.pi_lt_four]
  have hp : ((2*(d/16):ℕ):ℝ) ≤ (d:ℝ) := by
    have h := Nat.div_mul_le_self d 16
    exact_mod_cast (show 2*(d/16) ≤ d by omega)
  dsimp only at hlow
  push_cast at hlow hJlog he2 henergy hp ⊢
  have hk0 : (0:ℝ) ≤ (d/16:ℕ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl2 (show (0:ℝ) ≤ 4*(d/16:ℕ) by positivity),
    mul_le_mul_of_nonneg_left hlpi (show (0:ℝ) ≤ (d/16:ℕ) by positivity)]

end KernelPotential.Scale
open MeasureTheory ProbabilityTheory

end OAI
