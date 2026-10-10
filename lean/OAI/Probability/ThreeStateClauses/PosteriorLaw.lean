import Mathlib
import OAI.Probability.ThreeStateClauses.PositiveMoments

namespace OAI

/-! Posterior Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
open Radial ThreeState.TreeClauses.Positive

def messageSet : Set Vec := {m | (∀ i, 0 ≤ m i) ∧ avg m = 1}
abbrev Message := messageSet

lemma coordinate_nonneg (m : Message) (i : Fin 3) : 0 ≤ m.1 i := m.2.1 i
lemma coordinate_le_three (m : Message) (i : Fin 3) : m.1 i ≤ 3 := by
  have hs := m.2.2
  dsimp only [avg] at hs
  have h₀ := m.2.1 0
  have h₁ := m.2.1 1
  have h₂ := m.2.1 2
  fin_cases i <;> dsimp at * <;> linarith

lemma continuous_avg : Continuous (avg : Vec → ℝ) :=
  (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2)).div_const 3

lemma isClosed_messageSet : IsClosed messageSet := by
  have h : IsClosed {m : Vec | ∀ i, 0 ≤ m i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i ↦ isClosed_le continuous_const (continuous_apply i))
  exact h.inter (isClosed_eq continuous_avg continuous_const)

lemma isCompact_messageSet : IsCompact messageSet :=
  (isCompact_Icc (a := fun _ : Fin 3 ↦ (0:ℝ)) (b := fun _ : Fin 3 ↦ (3:ℝ))).of_isClosed_subset
    isClosed_messageSet (fun m hm ↦ ⟨hm.1, fun i ↦ coordinate_le_three ⟨m, hm⟩ i⟩)

instance : CompactSpace Message := isCompact_iff_compactSpace.mp isCompact_messageSet

lemma continuous_coordinate (i : Fin 3) : Continuous (fun m : Message ↦ m.1 i) :=
  (continuous_apply i).comp continuous_subtype_val

lemma integral_avg_measure {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → Vec}
    (hf : ∀ i, Integrable (fun x ↦ f x i) ν) :
    (∫ x, avg (f x) ∂ν) = avg (fun i ↦ ∫ x, f x i ∂ν) := by
  simp only [avg, integral_div]
  rw [integral_add (f := fun x ↦ f x 0+f x 1) (g := fun x ↦ f x 2) ((hf 0).add (hf 1)) (hf 2),
    integral_add (f := fun x ↦ f x 0) (g := fun x ↦ f x 1) (hf 0) (hf 1)]

lemma integrable_avg {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → Vec}
    (hf : ∀ i, Integrable (fun x ↦ f x i) ν) : Integrable (fun x ↦ avg (f x)) ν :=
  (((hf 0).add (hf 1)).add (hf 2)).div_const 3

def permute (σ : Equiv.Perm (Fin 3)) (m : Message) : Message :=
  ⟨fun i ↦ m.1 (σ i), fun i ↦ m.2.1 (σ i), by
    have h : avg (fun i ↦ m.1 (σ i)) = avg m.1 := by
      have he := Equiv.sum_comp σ m.1
      simpa only [Fin.sum_univ_three, avg, div_left_inj' (by norm_num : (3:ℝ) ≠ 0)] using he
    rw [h]; exact m.2.2⟩

lemma continuous_permute (σ : Equiv.Perm (Fin 3)) : Continuous (permute σ) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i ↦ continuous_coordinate (σ i))

structure Law where
  probability : ProbabilityMeasure Message
  balanced : ∀ i, ∫ m, m.1 i ∂probability.toMeasure = 1
  symmetric : ∀ σ, MeasurePreserving (permute σ) probability.toMeasure probability.toMeasure

def edgeMessage (lam : ℝ) (m : Message) : Vec := edge lam m.1

lemma edge_lower {lam : ℝ} (hl : 0 ≤ lam) (m : Message) (i : Fin 3) :
    1-lam ≤ edgeMessage lam m i := by
  dsimp [edgeMessage, edge]
  nlinarith [mul_nonneg hl (coordinate_nonneg m i)]

lemma edge_upper {lam : ℝ} (hl : 0 ≤ lam) (m : Message) (i : Fin 3) :
    edgeMessage lam m i ≤ 1+2*lam := by
  dsimp [edgeMessage, edge]
  nlinarith [mul_nonneg hl (sub_nonneg.mpr (coordinate_le_three m i))]

lemma edge_positive {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (m : Message) :
    PositiveMessage (edgeMessage lam m) := by
  refine ⟨fun i ↦ lt_of_lt_of_le (sub_pos.mpr hl₁) (edge_lower hl₀ m i), ?_⟩
  have hc : avg (centered m.1) = 0 := by
    change avg (fun i ↦ m.1 i-1) = 0
    rw [avg_sub, avg_const, m.2.2]; ring
  change avg (fun i ↦ 1+lam*centered m.1 i) = 1
  rw [avg_add, avg_const, avg_mul, hc]; ring

lemma continuous_edgeMessage (lam : ℝ) : Continuous (edgeMessage lam) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_const.mul ((continuous_coordinate i).sub continuous_const))

lemma continuous_edge_log {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (i : Fin 3) :
    Continuous (fun m : Message ↦ Real.log (edgeMessage lam m i)) :=
  ((continuous_apply i).comp (continuous_edgeMessage lam)).log
    (fun m ↦ ne_of_gt ((edge_positive hl₀ hl₁ m).1 i))

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma avg_permute_vec (σ : Equiv.Perm (Fin 3)) (v : Vec) :
    avg (fun i ↦ v (σ i)) = avg v := by
  have h := Equiv.sum_comp σ v
  simpa only [Fin.sum_univ_three, avg, div_left_inj' (by norm_num : (3:ℝ) ≠ 0)] using h

def permuteMeasurableEquiv (σ : Equiv.Perm (Fin 3)) : Message ≃ᵐ Message where
  toFun := permute σ
  invFun := permute σ.symm
  left_inv m := by apply Subtype.ext; funext i; simp [permute]
  right_inv m := by apply Subtype.ext; funext i; simp [permute]
  measurable_toFun := (continuous_permute σ).measurable
  measurable_invFun := (continuous_permute σ.symm).measurable

lemma compact_integrable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma Law.integral_equivariant (Q : Law) {f : Message → Vec}
    (hf : ∀ i, Integrable (fun m ↦ f m i) Q.probability.toMeasure)
    (hs : ∀ σ m i, f (permute σ m) i = f m (σ i)) (i : Fin 3) :
    (∫ m, f m i ∂Q.probability.toMeasure) = ∫ m, avg (f m) ∂Q.probability.toMeasure := by
  have he (j : Fin 3) : (∫ m, f m j ∂Q.probability.toMeasure) = ∫ m, f m i ∂Q.probability.toMeasure := by
    let σ := Equiv.swap i j
    have hp : MeasurePreserving (permuteMeasurableEquiv σ) Q.probability.toMeasure Q.probability.toMeasure := Q.symmetric σ
    have h := hp.integral_comp' (fun m ↦ f m i)
    change (∫ m, f (permute σ m) i ∂Q.probability.toMeasure) = _ at h
    simp_rw [hs] at h
    simpa only [σ, Equiv.swap_apply_left] using h
  rw [integral_avg_measure hf]
  dsimp only [avg]
  rw [he 0, he 1, he 2]
  ring

lemma continuous_edge_centeredLog {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (i : Fin 3) :
    Continuous (fun m : Message ↦ logCentered (edgeMessage lam m) i) := by
  apply (continuous_edge_log hl₀ hl₁ i).sub
  exact continuous_avg.comp (continuous_pi (fun j ↦ continuous_edge_log hl₀ hl₁ j))

lemma edge_permute (lam : ℝ) (σ : Equiv.Perm (Fin 3)) (m : Message) (i : Fin 3) :
    edgeMessage lam (permute σ m) i = edgeMessage lam m (σ i) := rfl

lemma edge_logCentered_permute (lam : ℝ) (σ : Equiv.Perm (Fin 3)) (m : Message) (i : Fin 3) :
    logCentered (edgeMessage lam (permute σ m)) i = logCentered (edgeMessage lam m) (σ i) := by
  unfold logCentered logAverage
  simp_rw [edge_permute]
  rw [avg_permute_vec σ (fun i ↦ Real.log (edgeMessage lam m i))]

lemma Law.edge_balanced (Q : Law) (lam : ℝ) (i : Fin 3) :
    (∫ m, edgeMessage lam m i ∂Q.probability.toMeasure) = 1 := by
  have hi : Integrable (fun m : Message ↦ m.1 i) Q.probability.toMeasure := compact_integrable (continuous_coordinate i)
  change (∫ m : Message, 1+lam*(m.1 i-1) ∂Q.probability.toMeasure) = 1
  rw [integral_add (f := fun _ : Message ↦ (1:ℝ)) (g := fun m ↦ lam*(m.1 i-1))
    (integrable_const _) ((hi.sub (integrable_const _)).const_mul _),
    integral_const_mul, integral_sub (f := fun m : Message ↦ m.1 i) (g := fun _ ↦ (1:ℝ)) hi (integrable_const _), Q.balanced]
  simp

lemma symEntropy_centeredLog' {m : Vec} (hm : avg m = 1) :
    avg (fun i ↦ m i*logCentered m i) = 2*symEntropy m := by
  have he : avg (fun i ↦ m i*logAverage m) = logAverage m := by
    calc
      _ = logAverage m*avg m := by dsimp only [avg]; ring
      _ = _ := by rw [hm]; ring
  simp only [logCentered, mul_sub, avg_sub, he]
  dsimp only [symEntropy, logAverage, avg]
  ring

lemma Law.edge_centeredLog_mean (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (i : Fin 3) :
    (∫ m, edgeMessage lam m i*logCentered (edgeMessage lam m) i ∂Q.probability.toMeasure) =
      2*(∫ m, symEntropy (edgeMessage lam m) ∂Q.probability.toMeasure) := by
  rw [Q.integral_equivariant (f := fun m i ↦ edgeMessage lam m i*logCentered (edgeMessage lam m) i)
    (fun i ↦ compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
    (continuous_edge_centeredLog hl₀ hl₁ i))) (fun σ m i ↦ by rw [edge_permute, edge_logCentered_permute]) i]
  simp_rw [symEntropy_centeredLog' (edge_positive hl₀ hl₁ _).2]
  rw [integral_const_mul]

lemma Law.edge_centeredLog_sq (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (i : Fin 3) :
    (∫ m, edgeMessage lam m i*logCentered (edgeMessage lam m) i^2 ∂Q.probability.toMeasure) =
      2*(∫ m, correction (edgeMessage lam m) ∂Q.probability.toMeasure) := by
  rw [Q.integral_equivariant (f := fun m i ↦ edgeMessage lam m i*logCentered (edgeMessage lam m) i^2)
    (fun i ↦ compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
    ((continuous_edge_centeredLog hl₀ hl₁ i).pow 2))) (fun σ m i ↦ by rw [edge_permute, edge_logCentered_permute]) i]
  rw [← integral_const_mul]
  congr 1; funext m; simp only [correction]; ring

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

def xMoment (m : Message) : ℝ := momentX (centered m.1)
def yMoment (m : Message) : ℝ := momentY (centered m.1)

lemma message_centered_avg (m : Message) : avg (centered m.1) = 0 := by
  change avg (fun i ↦ m.1 i-1) = 0
  rw [avg_sub, avg_const, m.2.2]; ring

lemma continuous_xMoment : Continuous xMoment := by
  unfold xMoment momentX centered
  exact (continuous_avg.comp (continuous_pi (fun i ↦ ((continuous_coordinate i).sub continuous_const).pow 2))).div_const 2

lemma continuous_yMoment : Continuous yMoment := by
  unfold yMoment momentY centered
  exact (continuous_avg.comp (continuous_pi (fun i ↦ ((continuous_coordinate i).sub continuous_const).pow 3))).div_const 2

lemma xMoment_nonneg (m : Message) : 0 ≤ xMoment m := momentX_nonneg _

lemma xMoment_le_one (m : Message) : xMoment m ≤ 1 := by
  have h (i : Fin 3) : (m.1 i)^2 ≤ 3*m.1 i := by
    nlinarith [mul_nonneg (coordinate_nonneg m i) (sub_nonneg.mpr (coordinate_le_three m i))]
  have hs := m.2.2
  dsimp only [avg] at hs
  dsimp only [xMoment, momentX, centered, avg]
  nlinarith [h 0, h 1, h 2]

lemma yMoment_discriminant (m : Message) : yMoment m^2 ≤ xMoment m^3 :=
  moment_discriminant (message_centered_avg m)

lemma moment_quadratic_nonneg {x y a : ℝ} (hx : 0 ≤ x) (hy : y^2 ≤ x^3) :
    0 ≤ x*a^2+2*y*a+x^2 := by
  rcases eq_or_lt_of_le hx with h | h
  · have hx0 : x = 0 := h.symm
    have hy0 : y = 0 := by rw [hx0] at hy; nlinarith [sq_nonneg y]
    simp [hx0,hy0]
  · have hh : 0 ≤ x*(x*a^2+2*y*a+x^2) := by nlinarith [sq_nonneg (x*a+y)]
    exact nonneg_of_mul_nonneg_right hh h

def Law.mu (Q : Law) := ∫ m, xMoment m ∂Q.probability.toMeasure
def Law.nu (Q : Law) := ∫ m, xMoment m^2 ∂Q.probability.toMeasure
def Law.eta (Q : Law) := ∫ m, yMoment m ∂Q.probability.toMeasure

lemma Law.mu_nonneg (Q : Law) : 0 ≤ Q.mu := integral_nonneg xMoment_nonneg
lemma Law.nu_nonneg (Q : Law) : 0 ≤ Q.nu := integral_nonneg (fun _ ↦ sq_nonneg _)

lemma Law.mu_le_one (Q : Law) : Q.mu ≤ 1 := by
  have h := integral_mono (μ := Q.probability.toMeasure)
    (compact_integrable continuous_xMoment) (integrable_const (1:ℝ)) xMoment_le_one
  simpa [Law.mu] using h

lemma Law.second_moment_lower (Q : Law) : Q.mu^2 ≤ Q.nu := by
  have hi := compact_integrable continuous_xMoment (μ := Q.probability.toMeasure)
  have hi₂ := compact_integrable (continuous_xMoment.pow 2) (μ := Q.probability.toMeasure)
  have h := integral_nonneg (μ := Q.probability.toMeasure) (f := fun m : Message ↦ (xMoment m-Q.mu)^2)
    (fun m ↦ sq_nonneg (xMoment m-Q.mu))
  have hfunc : (fun m : Message ↦ (xMoment m-Q.mu)^2) =
      (fun m ↦ xMoment m^2 - 2*Q.mu*xMoment m + Q.mu^2) := by funext m; ring
  rw [hfunc, integral_add (f := fun m ↦ xMoment m^2-2*Q.mu*xMoment m)
    (g := fun _ ↦ Q.mu^2) (hi₂.sub (hi.const_mul _)) (integrable_const _),
    integral_sub (f := fun m ↦ xMoment m^2) (g := fun m ↦ 2*Q.mu*xMoment m) hi₂ (hi.const_mul (2*Q.mu)), integral_const_mul] at h
  simp only [integral_const, measure_univ, Measure.real, ENNReal.toReal_one, smul_eq_mul, one_mul] at h
  change 0 ≤ Q.nu-2*Q.mu*Q.mu+Q.mu^2 at h
  linarith

lemma Law.moment_discriminant (Q : Law) : Q.eta^2 ≤ Q.mu*Q.nu := by
  have hi := compact_integrable continuous_xMoment (μ := Q.probability.toMeasure)
  have hi₂ := compact_integrable (continuous_xMoment.pow 2) (μ := Q.probability.toMeasure)
  have hy := compact_integrable continuous_yMoment (μ := Q.probability.toMeasure)
  have hquad (a : ℝ) : 0 ≤ Q.mu*(a*a)+(2*Q.eta)*a+Q.nu := by
    have h := integral_nonneg (μ := Q.probability.toMeasure)
      (f := fun m : Message ↦ xMoment m*a^2+2*yMoment m*a+xMoment m^2)
      (fun m : Message ↦ moment_quadratic_nonneg (a := a) (xMoment_nonneg m) (yMoment_discriminant m))
    rw [integral_add (f := fun m ↦ xMoment m*a^2+2*yMoment m*a) (g := fun m ↦ xMoment m^2)
      ((hi.mul_const _).add ((hy.const_mul _).mul_const _)) hi₂,
      integral_add (f := fun m ↦ xMoment m*a^2) (g := fun m ↦ 2*yMoment m*a)
        (hi.mul_const _) ((hy.const_mul _).mul_const _),
      integral_mul_const, integral_mul_const, integral_const_mul] at h
    change 0 ≤ Q.mu*a^2+2*Q.eta*a+Q.nu at h
    nlinarith
  have h := discrim_le_zero hquad
  dsimp only [discrim] at h
  nlinarith

end ThreeState.TreeClauses.Experiment

end

end OAI
