import Mathlib
import OAI.Probability.Perceptron.Variational.TensorFeatures
import OAI.Probability.Perceptron.Variational.NonlinearDirectionIBP

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma spinOverlap_self {N : ℕ} (x : NormalizedSpin N) : spinOverlap x x = 1 := by
  have hx : ‖x.val‖ = 1 := by simp
  simp [spinOverlap,hx]

lemma spinOverlap_sum {N : ℕ} (x y : NormalizedSpin N) :
    spinOverlap x y = ∑ i, x.val i*y.val i := by
  simp [spinOverlap,PiLp.inner_apply,mul_comm]

lemma normalizedSpin_coord_bound {N : ℕ} (x : NormalizedSpin N) (i : Fin N) : |x.val i| ≤ 1 := by
  have hx : ‖x.val‖ = 1 := by simp
  simpa only [Real.norm_eq_abs,hx] using PiLp.norm_apply_le x.val i

lemma spherical_pattern_direction_ibp {n : ℕ}
    (μ : Measure (NormalizedSpin (n+1))) [IsProbabilityMeasure μ]
    (f : Jet3) (G : ℝ →ᵇ ℝ) {h : NormalizedSpin (n+1) → ℝ}
    (hh : Measurable h) {A : ℝ} (hA : 0≤A) (hhA : ∀ x, |h x|≤A) :
    let b := gaussianField (n+1) (fun i (x : NormalizedSpin (n+1)) => x.val i)
    let H := fun g x => h x+f.f (b g x)
    (∫ g, gibbsReplicaMean μ (H g) 2 (fun x =>
      G (spinOverlap (x 0) (x 1))*f.d1 (b g (x 0))*
        (b g (x 1)-spinOverlap (x 0) (x 1)*b g (x 0)))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫ g, gibbsReplicaMean μ (H g) 2 (fun x =>
      G (spinOverlap (x 0) (x 1))*f.d1 (b g (x 0))*f.d1 (b g (x 1))*
        (1-spinOverlap (x 0) (x 1)^2)) -
      2*gibbsReplicaMean μ (H g) 3 (fun x =>
        G (spinOverlap (x 1) (x 2))*f.d1 (b g (x 1))*f.d1 (b g (x 0))*
          (spinOverlap (x 2) (x 0)-spinOverlap (x 1) (x 2)*spinOverlap (x 1) (x 0)))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let v := fun i (x : NormalizedSpin (n+1)) => x.val i
  let w := fun i (x : Fin 2→NormalizedSpin (n+1)) =>
    G (spinOverlap (x 0) (x 1))*(v i (x 1)-spinOverlap (x 0) (x 1)*v i (x 0))
  have hv : ∀ i, Measurable (v i) := fun i => by dsimp [v]; fun_prop
  have hw : ∀ i, Measurable (w i) := fun i => by dsimp [w,v,spinOverlap]; fun_prop
  have hwB (i x) : |w i x| ≤ ‖G‖*2 := by
    dsimp [w]; rw [abs_mul]
    apply mul_le_mul (G.norm_coe_le_norm _) _ (abs_nonneg _) (norm_nonneg _)
    apply (abs_sub _ _).trans
    have h1 := normalizedSpin_coord_bound (x 1) i
    have h0 := normalizedSpin_coord_bound (x 0) i
    have hr := spinOverlap_abs_le (x 0) (x 1)
    dsimp [v]; rw [abs_mul]
    have := mul_le_mul hr h0 (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith
  have hK (x : Fin 2→NormalizedSpin (n+1)) (y : NormalizedSpin (n+1)) :
      (∑ i, w i x*v i y) = G (spinOverlap (x 0) (x 1))*
        (spinOverlap (x 1) y-spinOverlap (x 0) (x 1)*spinOverlap (x 0) y) := by
    simp only [w,v,spinOverlap_sum,Finset.mul_sum,Finset.sum_sub_distrib,sub_mul,mul_sub]
    congr 1 <;> (apply Finset.sum_congr rfl; intros; ring)
  have hb (g : Fin (n+1)→ℝ) (x : Fin 2→NormalizedSpin (n+1)) :
      (∑ i, g i*w i x) = G (spinOverlap (x 0) (x 1))*
        (gaussianField (n+1) v g (x 1)-spinOverlap (x 0) (x 1)*gaussianField (n+1) v g (x 0)) := by
    simp only [w,gaussianField,Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]
    congr 1 <;> (apply Finset.sum_congr rfl; intros; ring)
  have he := nonlinear_pattern_direction_ibp μ (0:Fin 2) f hv hh hw hA
    (by norm_num : (0:ℝ)≤1) (by positivity : 0≤‖G‖*2) hhA
    (fun i x => normalizedSpin_coord_bound x i) hwB
  dsimp only at he
  simp_rw [hK,hb] at he
  convert he using 1
  · congr 1; funext g; congr 1; funext x; ring
  · congr 1; funext g
    congr 1
    · congr 1; funext x
      simp only [Fin.sum_univ_two,spinOverlap_self]
      rw [show spinOverlap (x 1) (x 0) = spinOverlap (x 0) (x 1) from real_inner_comm _ _]
      ring
    · congr 1; congr 1; funext x
      simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
      ring

end SphericalPerceptronFreeEnergy
end

end OAI
