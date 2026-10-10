import Mathlib
import OAI.Probability.ThreeStateClauses.FiniteUpdate
import OAI.Probability.ThreeStateClauses.Correlation

namespace OAI

/-! Projection. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

def edgeCentered (lam : ℝ) (m : Message) (i : Fin 3) : ℝ := edgeMessage lam m i-1

lemma continuous_edgeCentered (lam : ℝ) (i : Fin 3) :
    Continuous (fun m : Message ↦ edgeCentered lam m i) :=
  ((continuous_apply i).comp (continuous_edgeMessage lam)).sub continuous_const

lemma Law.edgeCentered_mean (Q : Law) (lam : ℝ) (i : Fin 3) :
    (∫ m, edgeCentered lam m i ∂Q.probability.toMeasure) = 0 := by
  unfold edgeCentered
  rw [integral_sub (f := fun m ↦ edgeMessage lam m i) (g := fun _ ↦ (1:ℝ))
    (compact_integrable ((continuous_apply i).comp (continuous_edgeMessage lam))) (integrable_const _),
    Q.edge_balanced]
  simp

lemma Law.edgeCentered_second (Q : Law) (lam : ℝ) (i : Fin 3) :
    (∫ m, edgeCentered lam m i^2 ∂Q.probability.toMeasure) = 2*lam^2*Q.mu := by
  rw [Q.integral_equivariant (f := fun m i ↦ edgeCentered lam m i^2)
    (fun i ↦ compact_integrable ((continuous_edgeCentered lam i).pow 2))
    (fun _ _ _ ↦ rfl)]
  have he (m : Message) : avg (fun i ↦ edgeCentered lam m i^2) = 2*lam^2*xMoment m := by
    have hh := xMoment_edge lam m
    change (avg (fun i ↦ edgeCentered lam m i^2))/2 = _ at hh
    linarith
  simp_rw [he]
  rw [integral_const_mul]
  rfl

lemma Law.edgeCentered_tilt_diag (Q : Law) (lam : ℝ) (i : Fin 3) :
    (∫ m, edgeMessage lam m i*edgeCentered lam m i ∂Q.probability.toMeasure) = 2*lam^2*Q.mu := by
  have he (m : Message) : edgeMessage lam m i*edgeCentered lam m i =
      edgeCentered lam m i+edgeCentered lam m i^2 := by unfold edgeCentered; ring
  simp_rw [he]
  rw [integral_add (f := fun m ↦ edgeCentered lam m i) (g := fun m ↦ edgeCentered lam m i^2)
    (compact_integrable (continuous_edgeCentered lam i))
    (compact_integrable ((continuous_edgeCentered lam i).pow 2)),
    Q.edgeCentered_mean, Q.edgeCentered_second, zero_add]

lemma Law.edgeCentered_tilt_mean (Q : Law) (lam : ℝ) (i : Fin 3) :
    (∫ m, edgeMessage lam m i*edgeCentered lam m 0 ∂Q.probability.toMeasure) =
      if i=0 then 2*(lam^2*Q.mu) else -(lam^2*Q.mu) := by
  have hi (i : Fin 3) : Integrable (fun m ↦ edgeMessage lam m i*edgeCentered lam m 0) Q.probability.toMeasure :=
    compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul (continuous_edgeCentered lam 0))
  have he : (∫ m, edgeMessage lam m 1*edgeCentered lam m 0 ∂Q.probability.toMeasure) =
      ∫ m, edgeMessage lam m 2*edgeCentered lam m 0 ∂Q.probability.toMeasure := by
    have hh := (show MeasurePreserving (permuteMeasurableEquiv (Equiv.swap 1 2))
      Q.probability.toMeasure Q.probability.toMeasure from Q.symmetric _).integral_comp'
        (fun m ↦ edgeMessage lam m 1*edgeCentered lam m 0)
    simpa [permuteMeasurableEquiv, edgeCentered, edge_permute, Equiv.swap_apply_def] using hh.symm
  have hsum : avg (fun i ↦ ∫ m, edgeMessage lam m i*edgeCentered lam m 0 ∂Q.probability.toMeasure) = 0 := by
    rw [← integral_avg_measure hi]
    have hh (m : Message) : avg (fun i ↦ edgeMessage lam m i*edgeCentered lam m 0) = edgeCentered lam m 0 := by
      have hav : avg (edgeMessage lam m) = 1 := by
        dsimp only [edgeMessage, edge, avg]
        have hm := m.2.2
        dsimp only [avg] at hm
        linear_combination lam*hm
      calc
        _ = avg (edgeMessage lam m)*edgeCentered lam m 0 := by dsimp [avg]; ring
        _ = _ := by rw [hav, one_mul]
    simp_rw [hh]
    exact Q.edgeCentered_mean lam 0
  dsimp only [avg] at hsum
  rw [Q.edgeCentered_tilt_diag lam 0, he] at hsum
  fin_cases i
  · simp [Q.edgeCentered_tilt_diag]; ring
  · change (∫ m, edgeMessage lam m 1*edgeCentered lam m 0 ∂Q.probability.toMeasure) = -(lam^2*Q.mu)
    rw [he]; linarith
  · change (∫ m, edgeMessage lam m 2*edgeCentered lam m 0 ∂Q.probability.toMeasure) = -(lam^2*Q.mu)
    linarith

def branchSum (lam : ℝ) {n : ℕ} (m : Fin n → Message) : ℝ := ∑ j, edgeCentered lam (m j) 0

lemma continuous_branchSum (lam : ℝ) (n : ℕ) : Continuous (branchSum lam (n := n)) :=
  continuous_finsetSum _ (fun j _ ↦ (continuous_edgeCentered lam 0).comp (continuous_apply j))

lemma integral_branchProduct_sum (Q : Law) (lam : ℝ) (n : ℕ) (i : Fin 3) :
    (∫ m : Fin n → Message, branchProduct (branchEdges lam m) i*branchSum lam m
      ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) =
      n*(if i=0 then 2*(lam^2*Q.mu) else -(lam^2*Q.mu)) := by
  have hh := integral_weighted_sum (ι := Fin n)
    (compact_integrable ((continuous_apply i).comp (continuous_edgeMessage lam)))
    (compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
      (continuous_edgeCentered lam 0))) (Q.edge_balanced lam i)
  simp only [Function.comp_apply] at hh
  rw [Q.edgeCentered_tilt_mean] at hh
  simpa only [weightProduct, branchProduct, branchEdges, branchSum, Fintype.card_fin, Function.comp_apply] using hh

lemma integral_normalizer_sum (Q : Law) (lam : ℝ) (n : ℕ) :
    (∫ m : Fin n → Message, normalizer (branchEdges lam m)*branchSum lam m
      ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) = 0 := by
  have he (m : Fin n → Message) : normalizer (branchEdges lam m)*branchSum lam m =
      avg (fun i ↦ branchProduct (branchEdges lam m) i*branchSum lam m) := by dsimp [normalizer, avg]; ring
  simp_rw [he]
  rw [integral_avg_measure (f := fun m : Fin n → Message ↦ fun i ↦ branchProduct (branchEdges lam m) i*branchSum lam m)
    (fun i ↦ compact_integrable ((continuous_branchProduct lam i).mul (continuous_branchSum lam n)))]
  simp_rw [integral_branchProduct_sum]
  norm_num [avg, show (2 : Fin 3) ≠ 0 from by decide]
  ring

lemma integral_normalizer_sq_sum (Q : Law) (lam : ℝ) (n : ℕ) :
    (∫ m : Fin n → Message, normalizer (branchEdges lam m)*branchSum lam m^2
      ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) =
      2*n*(lam^2*Q.mu)+2*((n:ℝ)^2-n)*(lam^2*Q.mu)^2 := by
  have he (m : Fin n → Message) : normalizer (branchEdges lam m)*branchSum lam m^2 =
      avg (fun i ↦ branchProduct (branchEdges lam m) i*branchSum lam m^2) := by dsimp [normalizer, avg]; ring
  simp_rw [he]
  rw [integral_avg_measure (f := fun m : Fin n → Message ↦ fun i ↦ branchProduct (branchEdges lam m) i*branchSum lam m^2)
    (fun i ↦ compact_integrable ((continuous_branchProduct lam i).mul ((continuous_branchSum lam n).pow 2)))]
  have hh (i : Fin 3) : (∫ m : Fin n → Message, branchProduct (branchEdges lam m) i*branchSum lam m^2
      ∂(Measure.pi fun _ ↦ Q.probability.toMeasure)) =
      n*(∫ m, edgeMessage lam m i*edgeCentered lam m 0^2 ∂Q.probability.toMeasure)+
      ((n:ℝ)^2-n)*(if i=0 then 2*(lam^2*Q.mu) else -(lam^2*Q.mu))^2 := by
    have h := integral_weighted_sq_sum (ι := Fin n)
      (compact_integrable ((continuous_apply i).comp (continuous_edgeMessage lam)))
      (compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
        (continuous_edgeCentered lam 0)))
      (compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
        ((continuous_edgeCentered lam 0).pow 2))) (Q.edge_balanced lam i)
    simp only [Function.comp_apply] at h
    rw [Q.edgeCentered_tilt_mean] at h
    simpa only [weightProduct, branchProduct, branchEdges, branchSum, Fintype.card_fin, Function.comp_apply] using h
  simp_rw [hh]
  rw [avg_add, avg_mul]
  have hmean : avg (fun i ↦ ∫ m, edgeMessage lam m i*edgeCentered lam m 0^2 ∂Q.probability.toMeasure) =
      2*lam^2*Q.mu := by
    rw [← integral_avg_measure (f := fun m : Message ↦ fun i ↦ edgeMessage lam m i*edgeCentered lam m 0^2)
      (fun i ↦ compact_integrable (((continuous_apply i).comp (continuous_edgeMessage lam)).mul
      ((continuous_edgeCentered lam 0).pow 2)))]
    have hh (m : Message) : avg (fun i ↦ edgeMessage lam m i*edgeCentered lam m 0^2) = edgeCentered lam m 0^2 := by
      have hm := m.2.2
      dsimp only [edgeMessage, edge, edgeCentered, avg] at *
      linear_combination (1+lam*(m.1 0-1)-1)^2*lam*hm
    simp_rw [hh]
    exact Q.edgeCentered_second lam 0
  rw [hmean]
  norm_num [avg, show (2 : Fin 3) ≠ 0 from by decide]
  ring

lemma Law.centered_second (Q : Law) (i : Fin 3) :
    (∫ m, (m.1 i-1)^2 ∂Q.probability.toMeasure) = 2*Q.mu := by
  simpa [edgeCentered, edgeMessage, edge] using Q.edgeCentered_second 1 i

lemma integral_posterior_sum (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    (∫ m : Fin n → Message, ((branchOutput hl₀ hl₁ m).1 0-1)*branchSum lam m
      ∂tiltedProduct Q lam n) = 2*n*(lam^2*Q.mu) := by
  rw [integral_tiltedProduct Q hl₀ hl₁]
  have he (m : Fin n → Message) :
      normalizer (branchEdges lam m)*(((branchOutput hl₀ hl₁ m).1 0-1)*branchSum lam m) =
      branchProduct (branchEdges lam m) 0*branchSum lam m-normalizer (branchEdges lam m)*branchSum lam m := by
    change normalizer (branchEdges lam m)*((branchProduct (branchEdges lam m) 0/normalizer (branchEdges lam m)-1)*branchSum lam m) = _
    field_simp [ne_of_gt (normalizer_positive (branchEdges_positive hl₀ hl₁ m))]
  simp_rw [he]
  rw [integral_sub (f := fun m : Fin n → Message ↦ branchProduct (branchEdges lam m) 0*branchSum lam m)
    (g := fun m ↦ normalizer (branchEdges lam m)*branchSum lam m)
    (compact_integrable ((continuous_branchProduct lam 0).mul (continuous_branchSum lam n)))
    (compact_integrable ((continuous_normalizer n lam).mul (continuous_branchSum lam n))),
    integral_branchProduct_sum, integral_normalizer_sum]
  simp; ring

lemma finite_projection_quadratic (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (n : ℕ) (a : ℝ) :
    0 ≤ (2*n*(lam^2*Q.mu)+2*((n:ℝ)^2-n)*(lam^2*Q.mu)^2)*(a*a)+
      (-4*n*(lam^2*Q.mu))*a+2*(finiteLaw Q hl₀ hl₁ n).mu := by
  let beta := lam^2*Q.mu
  have : IsProbabilityMeasure (tiltedProduct Q lam n) := tiltedProduct_isProbability Q hl₀ hl₁ n
  let v : (Fin n → Message) → ℝ := fun m ↦ (branchOutput hl₀ hl₁ m).1 0-1
  have hv : Continuous v := ((continuous_coordinate 0).comp (continuous_branchOutput hl₀ hl₁ n)).sub continuous_const
  have hv₂ : (∫ m, v m^2 ∂tiltedProduct Q lam n) = 2*(finiteLaw Q hl₀ hl₁ n).mu := by
    have hh := (finiteLaw Q hl₀ hl₁ n).centered_second 0
    change (∫ m, (m.1 0-1)^2 ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) = _ at hh
    change (∫ m, (m.1 0-1)^2 ∂Measure.map (branchOutput hl₀ hl₁) (tiltedProduct Q lam n)) = _ at hh
    rw [integral_map (f := fun m : Message ↦ (m.1 0-1)^2) (continuous_branchOutput hl₀ hl₁ n).measurable.aemeasurable
      (((continuous_coordinate 0).sub continuous_const).pow 2).measurable.aestronglyMeasurable] at hh
    exact hh
  have hT₂ : (∫ m, branchSum lam m^2 ∂tiltedProduct Q lam n) =
      2*n*beta+2*((n:ℝ)^2-n)*beta^2 := by
    rw [integral_tiltedProduct Q hl₀ hl₁]
    exact integral_normalizer_sq_sum Q lam n
  have hvT : (∫ m, v m*branchSum lam m ∂tiltedProduct Q lam n) = 2*n*beta :=
    integral_posterior_sum Q hl₀ hl₁ n
  show 0 ≤ (2*n*beta+2*((n:ℝ)^2-n)*beta^2)*(a*a)+
      (-4*n*beta)*a+2*(finiteLaw Q hl₀ hl₁ n).mu
  have hh := integral_nonneg (μ := tiltedProduct Q lam n)
    (f := fun m : Fin n → Message ↦ (v m-a*branchSum lam m)^2) (fun m ↦ sq_nonneg (v m-a*branchSum lam m))
  have he (m : Fin n → Message) : (v m-a*branchSum lam m)^2 =
      v m^2-2*a*(v m*branchSum lam m)+a^2*branchSum lam m^2 := by ring
  simp_rw [he] at hh
  rw [integral_add (f := fun m ↦ v m^2-2*a*(v m*branchSum lam m))
    (g := fun m ↦ a^2*branchSum lam m^2)
    ((compact_integrable (hv.pow 2)).sub ((compact_integrable (hv.mul (continuous_branchSum lam n))).const_mul _))
    ((compact_integrable ((continuous_branchSum lam n).pow 2)).const_mul _),
    integral_sub (f := fun m ↦ v m^2) (g := fun m ↦ 2*a*(v m*branchSum lam m))
      (compact_integrable (hv.pow 2)) ((compact_integrable (hv.mul (continuous_branchSum lam n))).const_mul _),
    integral_const_mul, integral_const_mul, hv₂, hvT, hT₂] at hh
  nlinarith [hh]

theorem finite_projection (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ)*(lam^2*Q.mu)/(1+((n:ℝ)-1)*(lam^2*Q.mu)) ≤ (finiteLaw Q hl₀ hl₁ n).mu := by
  let beta := lam^2*Q.mu
  have hb : 0 ≤ beta := mul_nonneg (sq_nonneg _) Q.mu_nonneg
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < 1+((n:ℝ)-1)*beta := by nlinarith [mul_nonneg (sub_nonneg.mpr hn') hb]
  have : IsProbabilityMeasure (tiltedProduct Q lam n) := tiltedProduct_isProbability Q hl₀ hl₁ n
  let v : (Fin n → Message) → ℝ := fun m ↦ (branchOutput hl₀ hl₁ m).1 0-1
  have hv : Continuous v := ((continuous_coordinate 0).comp (continuous_branchOutput hl₀ hl₁ n)).sub continuous_const
  have hv₂ : (∫ m, v m^2 ∂tiltedProduct Q lam n) = 2*(finiteLaw Q hl₀ hl₁ n).mu := by
    have hh := (finiteLaw Q hl₀ hl₁ n).centered_second 0
    change (∫ m, (m.1 0-1)^2 ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) = _ at hh
    change (∫ m, (m.1 0-1)^2 ∂Measure.map (branchOutput hl₀ hl₁) (tiltedProduct Q lam n)) = _ at hh
    rw [integral_map (f := fun m : Message ↦ (m.1 0-1)^2) (continuous_branchOutput hl₀ hl₁ n).measurable.aemeasurable
      (((continuous_coordinate 0).sub continuous_const).pow 2).measurable.aestronglyMeasurable] at hh
    exact hh
  have hT₂ : (∫ m, branchSum lam m^2 ∂tiltedProduct Q lam n) =
      2*n*beta+2*((n:ℝ)^2-n)*beta^2 := by
    rw [integral_tiltedProduct Q hl₀ hl₁]
    exact integral_normalizer_sq_sum Q lam n
  have hvT : (∫ m, v m*branchSum lam m ∂tiltedProduct Q lam n) = 2*n*beta :=
    integral_posterior_sum Q hl₀ hl₁ n
  have hquad (a : ℝ) : 0 ≤ (2*n*beta+2*((n:ℝ)^2-n)*beta^2)*(a*a)+
      (-4*n*beta)*a+2*(finiteLaw Q hl₀ hl₁ n).mu := by
    have hh := integral_nonneg (μ := tiltedProduct Q lam n)
      (f := fun m : Fin n → Message ↦ (v m-a*branchSum lam m)^2) (fun m ↦ sq_nonneg (v m-a*branchSum lam m))
    have he (m : Fin n → Message) : (v m-a*branchSum lam m)^2 =
        v m^2-2*a*(v m*branchSum lam m)+a^2*branchSum lam m^2 := by ring
    simp_rw [he] at hh
    rw [integral_add (f := fun m ↦ v m^2-2*a*(v m*branchSum lam m))
      (g := fun m ↦ a^2*branchSum lam m^2)
      ((compact_integrable (hv.pow 2)).sub ((compact_integrable (hv.mul (continuous_branchSum lam n))).const_mul _))
      ((compact_integrable ((continuous_branchSum lam n).pow 2)).const_mul _),
      integral_sub (f := fun m ↦ v m^2) (g := fun m ↦ 2*a*(v m*branchSum lam m))
        (compact_integrable (hv.pow 2)) ((compact_integrable (hv.mul (continuous_branchSum lam n))).const_mul _),
      integral_const_mul, integral_const_mul, hv₂, hvT, hT₂] at hh
    nlinarith [hh]
  have hh := discrim_le_zero hquad
  dsimp only [discrim] at hh
  have hcs : ((n:ℝ)*beta)^2 ≤ (finiteLaw Q hl₀ hl₁ n).mu*((n:ℝ)*beta+((n:ℝ)^2-n)*beta^2) := by nlinarith [hh]
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · have hb0' : beta = 0 := hb0.symm
    change (n:ℝ)*beta/(1+((n:ℝ)-1)*beta) ≤ _
    simp only [hb0', mul_zero, add_zero, zero_div]
    exact (finiteLaw Q hl₀ hl₁ n).mu_nonneg
  · have hnb : 0 < (n:ℝ)*beta := mul_pos (lt_of_lt_of_le zero_lt_one hn') hbpos
    apply (div_le_iff₀ hd).2
    apply le_of_mul_le_mul_left (a := (n:ℝ)*beta) (b := (n:ℝ)*beta) (c := (finiteLaw Q hl₀ hl₁ n).mu*(1+((n:ℝ)-1)*beta)) _ hnb
    calc
      (n:ℝ)*beta*((n:ℝ)*beta) = ((n:ℝ)*beta)^2 := by ring
      _ ≤ _ := hcs
      _ = _ := by ring

end ThreeState.TreeClauses.Experiment

end

end OAI
