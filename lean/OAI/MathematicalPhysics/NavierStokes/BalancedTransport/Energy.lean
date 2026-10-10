import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Sobolev

namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma Smooth.slice {v : Field F} (hv : Smooth v) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ (⊤ : ℕ∞) (v t) := by
  apply contDiffOn_univ.mp
  exact hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩)

lemma Smooth.sub {v w : Field F} (hv : Smooth v) (hw : Smooth w) :
    Smooth (fun t x => v t x - w t x) := hv.sub hw

lemma CH.memLp {v : Field F} {k : ℕ} (hv : CH k v)
    (a : List (Fin 3)) (ha : a.length ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (spatialD a v t) 2 (volume : Measure Space) := by
  obtain ⟨V, _, he⟩ := hv a ha
  exact (Lp.memLp (V t)).ae_eq (he t ht)

lemma membrane_component {f : Space → Space} (hf : MemLp f 2 (volume : Measure Space))
    (hc : Continuous f) (i : Fin 3) : MemLp (fun x => f x i) 2 (volume : Measure Space) := by
  apply hf.of_le ((continuous_apply i).comp hc).aestronglyMeasurable
  exact Eventually.of_forall (fun x => norm_le_pi_norm (f x) i)

lemma integrable_bounded_mul_l2_mul_l2 {a f g : Space → ℝ} {C : ℝ}
    (ha : Continuous a) (hab : ∀ x, ‖a x‖ ≤ C)
    (hf : MemLp f 2 (volume : Measure Space)) (hg : MemLp g 2 (volume : Measure Space)) :
    Integrable (fun x => a x * f x * g x) (volume : Measure Space) := by
  convert (hf.integrable_mul hg).bdd_mul ha.aestronglyMeasurable
      (Eventually.of_forall hab) using 1
  ext x
  simp only [Pi.mul_apply, mul_assoc]

lemma integral_mul_pd_eq_neg_pd_mul {f g : Space → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3)
    (hdg : Integrable (fun x => pd j f x * g x) (volume : Measure Space))
    (hfd : Integrable (fun x => f x * pd j g x) (volume : Measure Space))
    (hfg : Integrable (fun x => f x * g x) (volume : Measure Space)) :
    (∫ x, f x * pd j g x) = - ∫ x, pd j f x * g x :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdg hfd hfg
    (fun x _ => hf x) (fun x _ => hg x)

lemma transport_component {a w : Space → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (j : Fin 3) {C : ℝ} (hc : ∀ x, ‖a x‖ ≤ C) (hd : ∀ x, ‖pd j a x‖ ≤ C)
    (hw₂ : MemLp w 2 (volume : Measure Space))
    (hdw₂ : MemLp (pd j w) 2 (volume : Measure Space)) :
    2 * (∫ x, a x * pd j w x * w x) = - ∫ x, pd j a x * w x * w x := by
  have Hi := integrable_bounded_mul_l2_mul_l2 ha.continuous hc hdw₂ hw₂
  have Hj := integrable_bounded_mul_l2_mul_l2 (pd_contDiff j ha).continuous hd hw₂ hw₂
  have Hk := integrable_bounded_mul_l2_mul_l2 ha.continuous hc hw₂ hw₂
  have he (x : Space) : pd j (fun x => w x * w x) x = 2 * (pd j w x * w x) := by
    rw [pd_mul j (hw.differentiable (by simp) x) (hw.differentiable (by simp) x)]
    ring
  have hdg : Integrable (fun x => pd j a x * (w x * w x)) (volume : Measure Space) := by
    simpa only [mul_assoc] using Hj
  have hfg : Integrable (fun x => a x * (w x * w x)) (volume : Measure Space) := by
    simpa only [mul_assoc] using Hk
  have hfd : Integrable (fun x => a x * pd j (fun x => w x * w x) x)
      (volume : Measure Space) := by
    convert Hi.const_mul 2 using 1
    ext x
    rw [he]
    ring
  have H := integral_mul_pd_eq_neg_pd_mul (ha.differentiable (by simp))
    ((hw.mul hw).differentiable (by simp)) j hdg hfd hfg
  have he' : (fun x => a x * pd j (fun x => w x * w x) x) =
      (fun x => 2 * (a x * pd j w x * w x)) := by
    ext x
    rw [he]
    ring
  rw [he', integral_const_mul] at H
  simpa only [mul_assoc] using H

theorem transport_cancellation {v : Space → Space} {w : Space → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {C : ℝ} (hb : ∀ x, ‖v x‖ ≤ C) (hdb : ∀ x j, ‖pd j v x‖ ≤ C)
    (hdiv : ∀ x, ∑ j, pd j v x j = 0)
    (hw₂ : MemLp w 2 (volume : Measure Space))
    (hdw₂ : ∀ j, MemLp (pd j w) 2 (volume : Measure Space)) :
    (∑ j, ∫ x, v x j * pd j w x * w x) = 0 := by
  have he (j : Fin 3) (x : Space) : pd j (fun x => v x j) x = pd j v x j :=
    pd_apply j j (hv.differentiable (by simp) x)
  have H (j : Fin 3) := transport_component (contDiff_pi.mp hv j) hw j
    (fun x => (norm_le_pi_norm (v x) j).trans (hb x))
    (fun x => by rw [he]; exact (norm_le_pi_norm (pd j v x) j).trans (hdb x j))
    hw₂ (hdw₂ j)
  have hdj (j : Fin 3) : Integrable (fun x => pd j v x j * w x * w x) (volume : Measure Space) := by
    apply integrable_bounded_mul_l2_mul_l2
      ((continuous_apply j).comp (pd_contDiff j hv).continuous)
      (fun x => (norm_le_pi_norm (pd j v x) j).trans (hdb x j)) hw₂ hw₂
  have hsum : (∑ j, ∫ x, pd j v x j * w x * w x) = 0 := by
    rw [← integral_finsetSum _ (fun j _ => hdj j)]
    have hz (x : Space) : (∑ j, pd j v x j * w x * w x) = 0 := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hdiv x, zero_mul, zero_mul]
    simp only [hz, integral_zero]
  have Hsum := congrArg (fun f : Fin 3 → ℝ => ∑ j, f j) (funext H)
  simp only [he, Finset.sum_neg_distrib, ← Finset.mul_sum, hsum, neg_zero] at Hsum
  linarith

lemma diffusion_component {w : Space → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (j : Fin 3) (hw₂ : MemLp w 2 (volume : Measure Space))
    (hd₂ : MemLp (pd j w) 2 (volume : Measure Space))
    (hdd₂ : MemLp (pd j (pd j w)) 2 (volume : Measure Space)) :
    (∫ x, w x * pd j (pd j w) x) = - ∫ x, (pd j w x) ^ 2 := by
  simpa only [pow_two] using integral_mul_pd_eq_neg_pd_mul
    (hw.differentiable (by simp)) ((pd_contDiff j hw).differentiable (by simp)) j
    (hd₂.integrable_mul hd₂) (hw₂.integrable_mul hdd₂) (hw₂.integrable_mul hd₂)

theorem pressure_cancellation {w : Space → Space} {p : Space → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hdiv : ∀ x, ∑ j, pd j w x j = 0)
    (hw₂ : ∀ j, MemLp (fun x => w x j) 2 (volume : Measure Space))
    (hdw₂ : ∀ j, MemLp (fun x => pd j w x j) 2 (volume : Measure Space))
    (hp₂ : MemLp p 2 (volume : Measure Space))
    (hdp₂ : ∀ j, MemLp (pd j p) 2 (volume : Measure Space)) :
    (∑ j, ∫ x, w x j * pd j p x) = 0 := by
  have he (j : Fin 3) (x : Space) : pd j (fun x => w x j) x = pd j w x j :=
    pd_apply j j (hw.differentiable (by simp) x)
  have hdj (j : Fin 3) : Integrable (fun x => pd j w x j * p x) (volume : Measure Space) :=
    (hdw₂ j).integrable_mul hp₂
  have H (j : Fin 3) : (∫ x, w x j * pd j p x) = -∫ x, pd j w x j * p x := by
    have hdj' : Integrable (fun x => pd j (fun x => w x j) x * p x) (volume : Measure Space) := by
      simpa only [he] using hdj j
    simpa only [he] using integral_mul_pd_eq_neg_pd_mul
      ((contDiff_pi.mp hw j).differentiable (by simp)) (hp.differentiable (by simp)) j
      hdj' ((hw₂ j).integrable_mul (hdp₂ j)) ((hw₂ j).integrable_mul hp₂)
  simp only [H, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun j _ => hdj j)]
  have hz (x : Space) : (∑ j, pd j w x j * p x) = 0 := by
    rw [← Finset.sum_mul, hdiv x, zero_mul]
  simp only [hz, integral_zero, neg_zero]

end BalancedTransport.Analysis
end

end OAI
