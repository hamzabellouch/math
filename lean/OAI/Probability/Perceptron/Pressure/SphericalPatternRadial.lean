import Mathlib
import OAI.Probability.Perceptron.Pressure.SphericalPatternDirection

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma spherical_pattern_radial_ibp {n : ℕ}
    (μ : Measure (NormalizedSpin (n+1))) [IsProbabilityMeasure μ]
    (f : Jet3) {h : NormalizedSpin (n+1)→ℝ}
    (hh : Measurable h) {A : ℝ} (hA : 0≤A) (hhA : ∀ x,|h x|≤A) :
    let b := gaussianField (n+1) (fun i (x : NormalizedSpin (n+1)) => x.val i)
    let H := fun g x => h x+f.f (b g x)
    (∫ g,gibbsReplicaMean μ (H g) 1 (fun x => b g (x 0)*f.d1 (b g (x 0)))
      ∂Measure.pi (fun _ => gaussianReal 0 1))=
    ∫ g,gibbsReplicaMean μ (H g) 1 (fun x => f.d2 (b g (x 0))+f.d1 (b g (x 0))^2)-
      gibbsReplicaMean μ (H g) 2 (fun x => spinOverlap (x 0) (x 1)*f.d1 (b g (x 0))*f.d1 (b g (x 1)))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  dsimp only
  let v := fun i (x : NormalizedSpin (n+1)) => x.val i
  let w := fun i (x : Fin 1→NormalizedSpin (n+1)) => v i (x 0)
  have hv : ∀ i,Measurable (v i) := fun i => by dsimp [v]; fun_prop
  have hw : ∀ i,Measurable (w i) := fun i => by dsimp [w,v]; fun_prop
  have hK (x : Fin 1→NormalizedSpin (n+1)) (y : NormalizedSpin (n+1)) :
      (∑ i,w i x*v i y)=spinOverlap (x 0) y := by simp only [w,v,spinOverlap_sum]
  have hb (g : Fin (n+1)→ℝ) (x : Fin 1→NormalizedSpin (n+1)) :
      (∑ i,g i*w i x)=gaussianField (n+1) v g (x 0) := rfl
  have he := nonlinear_pattern_direction_ibp μ (0:Fin 1) f hv hh hw hA
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1) hhA
    (fun i x => normalizedSpin_coord_bound x i) (fun i x => normalizedSpin_coord_bound (x 0) i)
  dsimp only at he
  simp_rw [hK,hb] at he
  convert he using 1
  · congr 1; funext g; congr 1; funext x; ring
  · congr 1; funext g
    simp only [Nat.cast_one,one_mul,Fin.sum_univ_one,spinOverlap_self,Fin.succ_zero_eq_one,mul_one]
    congr 1
    · congr 1; funext x; ring
    · congr 1; funext x
      rw [show spinOverlap (x 1) (x 0)=spinOverlap (x 0) (x 1) from real_inner_comm _ _]
      ring

end SphericalPerceptronFreeEnergy
end

end OAI
