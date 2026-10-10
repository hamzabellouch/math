import OAI.MeasureTheory.Falconer.Fourier.JetChartControl
import OAI.MeasureTheory.Falconer.Angular.AngularEnvelope

namespace OAI

/-! # Actual differentiated descriptor products as angular symbols

Multiplication by the smooth coefficient of an inverse term preserves
every descriptor support. The derivative scales add under multiplication;
normalization records its exact amplitude cost.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

private theorem iteratedDeriv_product_bound (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {B C D E : ℝ} (hB : 0 ≤ B) (_hC : 0 ≤ C) (hD : 0 ≤ D) (_hE : 0 ≤ E)
    (t : ℕ) (x : ℝ)
    (hb : ∀ j ≤ t, ‖iteratedDeriv j f x‖ ≤ B*D^j)
    (hc : ∀ j ≤ t, ‖iteratedDeriv j g x‖ ≤ C*E^j) :
    ‖iteratedDeriv t (fun x => f x*g x) x‖ ≤ (B*C)*(D+E)^t := by
  have h := norm_iteratedFDeriv_mul_le hf hg x (by simp : (t : ℕ∞ω) ≤ ∞)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  apply h.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (t+1), (t.choose j:ℝ)*(B*D^j)*(C*E^(t-j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjt : j ≤ t := by have := Finset.mem_range.mp hj; omega
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hb j hjt) (Nat.cast_nonneg _))
        (hc (t-j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB (pow_nonneg hD _)))
    _ = (B*C)*(∑ j ∈ Finset.range (t+1), (t.choose j:ℝ)*D^j*E^(t-j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (B*C)*(D+E)^t := by
      congr 1
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring

 theorem ChartSymbolControl.mul {n L : ℕ}
    {b c : Space (n+2) → Sphere (n+2) → ℂ} {B C D E : ℝ}
    (hb : ChartSymbolControl L b B D) (hc : ChartSymbolControl L c C E)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ChartSymbolControl L (fun x w => b x w*c x w) (B*C) (D+E) := by
  refine ⟨hb.measurable.mul hc.measurable,?_,?_,?_⟩
  · intro x w
    rw [norm_mul]
    exact mul_le_mul (hb.bound x w) (hc.bound x w) (norm_nonneg _) hB
  · intro x e y
    exact (hb.smooth x e y).mul (hc.smooth x e y)
  · intro e t ht x y hy u hu
    exact iteratedDeriv_product_bound _ _ (hb.smooth x e y) (hc.smooth x e y)
      hB hC hD hE t u (fun j hj => hb.derivative e j (hj.trans ht) x y hy u hu)
      (fun j hj => hc.derivative e j (hj.trans ht) x y hy u hu)

 theorem descriptorJetProduct_mul_admissible {n L : ℕ} {ι : Type*}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
    (b : ι → PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+2)))
    (k : ι → ℕ) (v : (j : ι) → Sphere (n+2) → Fin (k j) → Space (n+2))
    (q : Sphere (n+2) → ℂ) {P C D E : ℝ}
    (hP : 0 < P) (hC : 0 < C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hp : ChartSymbolControl L (descriptorJetProduct Q ρ m N σ J i F b S k v) P D)
    (hq : ChartSymbolControl L (fun _ w => q w) C E) :
    AngularAdmissible L (E+D)
      {z | ∀ j ∈ F, z ∈ descriptorEndpointGood Q ρ m N σ J (i+1) (b j)}
      (normalizedEndpoint (C*P)
        (fun x w => q w*descriptorJetProduct Q ρ m N σ J i F b S k v x w)) := by
  refine ⟨(hq.mul hp hC.le hP.le hE hD).normalized
    (mul_pos hC hP) le_rfl (add_nonneg hE hD),?_⟩
  intro x w hw
  have h := normalizedEndpoint_ne_zero (C*P) _ x w hw
  exact descriptorJetProduct_support Q ρ m N σ J i F b S k v x w (mul_ne_zero_iff.mp h).2

end Falconer

end OAI
