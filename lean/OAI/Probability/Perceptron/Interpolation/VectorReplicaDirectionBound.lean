import Mathlib
import OAI.Probability.Perceptron.Variational.IntegratedConvex

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma euclideanGaussian_replica_direction_bound {I : Type} [Fintype I] {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (r : ℕ)
    {H : S→ℝ} {V : S→EuclideanSpace ℝ I} {W : (Fin r→S)→EuclideanSpace ℝ I}
    (hH : Measurable H) (hV : Measurable V) (hW : Measurable W)
    {A C D K : ℝ} (hC : 0≤C) (hD : 0≤D) (hK : 0≤K)
    (hA : ∀ x, |H x|≤A) (hVC : ∀ x, ‖V x‖≤C) (hWD : ∀ x, ‖W x‖≤D)
    (hWK : ∀ x y, |inner ℝ (W x) (V y)|≤K) :
    |∫ g, gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) r
      (fun x => inner ℝ (W x) g) ∂stdGaussian (EuclideanSpace ℝ I)|≤2*r*K := by
  let ν := Measure.pi (fun _ : Fin r => μ)
  let HH := replicaPotential H r
  let VV := fun x : Fin r→S => ∑ l, V (x l)
  have hHH : Measurable HH := replicaPotential_measurable hH r
  have hVV : Measurable VV := Finset.measurable_sum _ fun l _ => hV.comp (measurable_pi_apply l)
  have hHHA (x : Fin r→S) : |HH x|≤r*A := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin r, A := Finset.sum_le_sum fun l _ => hA (x l)
      _ = _ := by simp
  have hVVC (x : Fin r→S) : ‖VV x‖^2≤(r*C)^2 := by
    have hb : ‖VV x‖≤r*C := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _ : Fin r, C := Finset.sum_le_sum fun l _ => hVC (x l)
        _ = _ := by simp
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg r) hC)).2 hb
  have hWWD (x : Fin r→S) : ‖W x‖^2≤D^2 :=
    (sq_le_sq₀ (norm_nonneg _) hD).2 (hWD x)
  have hc (x y : Fin r→S) : |inner ℝ (W x) (VV y)|≤r*K := by
    dsimp only [VV]
    rw [inner_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin r, K := Finset.sum_le_sum fun l _ => hWK x (y l)
      _ = _ := by simp
  have he := euclideanGaussian_tiltMean_ibp ν hHH hVV hW hHHA hVVC hWWD
  have hham (g : EuclideanSpace ℝ I) : (fun x => HH x+inner ℝ (VV x) g)=
      replicaPotential (fun x => H x+inner ℝ (V x) g) r := by
    funext x
    simp only [HH,VV,replicaPotential,sum_inner,Finset.sum_add_distrib]
  have hl (g : EuclideanSpace ℝ I) :
      gibbsReplicaMean μ (fun x => H x+inner ℝ (V x) g) r (fun x => inner ℝ (W x) g)=
        tiltMean ν (fun x => HH x+inner ℝ (VV x) g) (fun x => inner ℝ (W x) g) 1 := by
    rw [hham]
    rfl
  simp_rw [hl]
  rw [he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ I, (2*r*K:ℝ) ∂stdGaussian (EuclideanSpace ℝ I) := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
      apply ae_of_all
      intro g
      have hm : Measurable (fun x => HH x+inner ℝ (VV x) g) := hHH.add (hVV.inner measurable_const)
      have hm1 : Measurable (fun x => inner ℝ (W x) (VV x)) := hW.inner hVV
      have hm2 : Measurable (fun x : Fin 2→(Fin r→S) => inner ℝ (W (x 1)) (VV (x 0))) :=
        (hW.comp (measurable_pi_apply 1)).inner (hVV.comp (measurable_pi_apply 0))
      have hb1 := tiltMean_bound_general ν hm hm1 (t:=1) (by positivity : 0≤(r:ℝ)*K) (fun x => hc x x)
      have hb2 : |gibbsReplicaMean ν (fun x => HH x+inner ℝ (VV x) g) 2
          (fun x => inner ℝ (W (x 1)) (VV (x 0)))|≤(r:ℝ)*K :=
        tiltMean_bound_general (Measure.pi (fun _ : Fin 2 => ν))
          (replicaPotential_measurable hm 2) hm2 (by positivity)
          (fun x => hc (x 1) (x 0))
      exact (abs_sub _ _).trans (by linarith)
    _ = _ := by simp

end SphericalPerceptronFreeEnergy
end

end OAI
