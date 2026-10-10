import OAI.Probability.ClassicalON.WeightedLinear

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ)

def edgeHamiltonian (b : E → ℝ) (x : X) : ℝ := ∑ e,b e*T e x

def edgeMean (b : E → ℝ) (f : X → ℝ) : ℝ := exponentialMean μ (edgeHamiltonian T b) f

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem continuous_edgeHamiltonian (hT : ∀ e,Continuous (T e)) (b : E → ℝ) :
    Continuous (edgeHamiltonian T b) := by
  exact continuous_finsetSum _ (fun e _ => continuous_const.mul (hT e))

def EdgeCovarianceNonneg : Prop := ∀ b : E → ℝ,(∀ e,0≤b e) → ∀ e f : E,
  edgeMean μ T b (T e)*edgeMean μ T b (T f)≤edgeMean μ T b (fun x => T e x*T f x)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
theorem edgeMean_zero (f : X → ℝ) : edgeMean μ T (fun _ => 0) f=∫ x,f x ∂μ := by
  have hz : edgeHamiltonian T (fun _ => 0)=(fun _ => 0) := by funext x; simp [edgeHamiltonian]
  unfold edgeMean
  rw [hz,exponentialMean_zero]

theorem edgeMean_direction_derivative (hT : ∀ e,Continuous (T e)) (b d : E → ℝ)
    (e : E) (t : ℝ) :
    HasDerivAt (fun u => edgeMean μ T (fun g => b g+u*d g) (T e))
      (∑ g,d g*(edgeMean μ T (fun h => b h+t*d h) (fun x => T e x*T g x)-
        edgeMean μ T (fun h => b h+t*d h) (T e)*
        edgeMean μ T (fun h => b h+t*d h) (T g))) t := by
  have he (u : ℝ) (x : X) : edgeHamiltonian T (fun g => b g+u*d g) x=
      edgeHamiltonian T b x+u*edgeHamiltonian T d x := by
    simp only [edgeHamiltonian,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
  have hd := hasDerivAt_exponentialMean μ (continuous_edgeHamiltonian T hT b)
    (continuous_edgeHamiltonian T hT d) (hT e) t
  simp_rw [← he] at hd
  change HasDerivAt (fun u => exponentialMean μ (edgeHamiltonian T (fun g => b g+u*d g)) (T e)) _ _
  apply hd.congr_deriv
  rw [show (fun x => T e x*edgeHamiltonian T d x)=
    (fun x => ∑ g,d g*(T e x*T g x)) by funext; simp only [edgeHamiltonian,Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  rw [exponentialMean_sum μ (continuous_edgeHamiltonian T hT _) _ (fun g => by fun_prop)]
  change (∑ g,exponentialMean μ _ (fun x => d g*(T e x*T g x)))-
    exponentialMean μ _ (T e)*exponentialMean μ _ (fun x => ∑ g,d g*T g x)=_
  rw [exponentialMean_sum μ (continuous_edgeHamiltonian T hT _) _ (fun g => by fun_prop)]
  simp only [exponentialMean_const_mul,Finset.mul_sum,← Finset.sum_sub_distrib,edgeMean]
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem edgeMean_mono_couplings (hT : ∀ e,Continuous (T e))
    (hCov : EdgeCovarianceNonneg μ T) {a b : E → ℝ}
    (ha : ∀ e,0≤a e) (hab : ∀ e,a e≤b e) (e : E) :
    edgeMean μ T a (T e)≤edgeMean μ T b (T e) := by
  let d := fun g => b g-a g
  let F := fun t => edgeMean μ T (fun g => a g+t*d g) (T e)
  have hD := edgeMean_direction_derivative μ T hT a d e
  have hM : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t _ => (hD t).continuousAt.continuousWithinAt)
      (fun t _ => (hD t).hasDerivWithinAt)
    intro t ht
    apply Finset.sum_nonneg
    intro g _
    apply mul_nonneg (sub_nonneg.mpr (hab g))
    apply sub_nonneg.mpr
    apply hCov
    intro h
    have ht0 : 0≤t := (interior_subset ht).1
    exact add_nonneg (ha h) (mul_nonneg ht0 (sub_nonneg.mpr (hab h)))
  have hh := hM (by simp : (0 : ℝ)∈Icc 0 1) (by simp : (1 : ℝ)∈Icc 0 1) (by norm_num)
  simpa only [F,d,zero_mul,add_zero,one_mul,add_sub_cancel] using hh

theorem edgeMean_nonneg (hT : ∀ e,Continuous (T e)) (hCov : EdgeCovarianceNonneg μ T)
    (h0 : ∀ e,0≤∫ x,T e x ∂μ) (b : E → ℝ) (hb : ∀ e,0≤b e) (e : E) :
    0≤edgeMean μ T b (T e) := by
  have hh := edgeMean_mono_couplings μ T hT hCov (fun _ => le_rfl) hb e
  rw [edgeMean_zero] at hh
  exact (h0 e).trans hh

end
end ClassicalON

end

end OAI
