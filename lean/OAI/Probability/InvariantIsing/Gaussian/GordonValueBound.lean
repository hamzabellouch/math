import OAI.Probability.InvariantIsing.Gaussian.GordonBounds

namespace OAI

/-! Finite Lipschitz and integrability bounds for the Gaussian minimum--maximum value. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators
namespace InvariantIsing
variable {U V : Type*} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]

lemma gordonValue_sub_bound (H J : U × V → ℝ) (K : ℝ)
    (hD : ∀ x, |H x-J x| ≤ K) : |gordonValue H-gordonValue J| ≤ K := by
  let F := fun t : ℝ => fun x => J x+t*(H x-J x)
  have hd (t : ℝ) : HasDerivAt (fun t => gordonValue (F t))
      (gordonMean (F t) (fun x => H x-J x)) t := by
    apply gordonValue_hasDerivAt
    intro x
    simpa only [F, id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const (H x-J x)).const_add (J x))
  have hb (t : ℝ) : ‖gordonMean (F t) (fun x => H x-J x)‖ ≤ K := by
    simpa only [Real.norm_eq_abs] using gordonMean_bound (F t) _ K hD
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ)) (fun t _ => (hd t).hasDerivWithinAt)
    (fun t _ => hb t) convex_univ (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
  simpa only [F,zero_mul,add_zero,one_mul,add_sub_cancel,sub_zero,norm_one,mul_one,
    Real.norm_eq_abs] using h

lemma integrable_gordonValue {d : ℕ} (H : U × V → ℝ) (C : U × V → Fin d → ℝ) :
    Integrable (fun g => gordonValue (fun x => H x+linearGaussian C g x))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hc : Continuous (fun g : Fin d → ℝ => gordonValue (fun x => H x+linearGaussian C g x)) :=
    continuous_gordonValue _ (fun x => by unfold linearGaussian; fun_prop)
  apply ((integrable_const |gordonValue H|).add
    (integrable_finsetSum Finset.univ (fun x _ => (integrable_linearGaussian C x).abs))).mono'
    hc.aestronglyMeasurable
  apply ae_of_all
  intro g
  have hb := gordonValue_sub_bound (fun x => H x+linearGaussian C g x) H
    (∑ x, |linearGaussian C g x|) (fun x => by
      simpa only [add_sub_cancel_left] using
        Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian C g y)) (Finset.mem_univ x))
  rw [Real.norm_eq_abs]
  have ht := abs_add_le
    (gordonValue (fun x => H x+linearGaussian C g x)-gordonValue H) (gordonValue H)
  rw [sub_add_cancel] at ht
  change |gordonValue (fun x => H x+linearGaussian C g x)| ≤
    |gordonValue H| + ∑ x, |linearGaussian C g x|
  exact ht.trans (by linarith)

lemma integrable_gordon_linear {d : ℕ} (A C : U × V → Fin d → ℝ) (x : U × V) :
    Integrable (fun g => linearGaussian A g x*gordonWeight (fun y => linearGaussian C g y) x)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  apply (integrable_linearGaussian A x).mul_bdd
    (continuous_gordonWeight _ (fun y => by unfold linearGaussian; fun_prop) x).aestronglyMeasurable
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs,abs_of_nonneg (gordonWeight_nonneg _ x)]
  exact gordonWeight_le_one _ x

end InvariantIsing

end

end OAI
