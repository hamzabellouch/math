import OAI.Probability.ClassicalON.ProductFKG

namespace OAI

universe uE uV uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {V : Type uV} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ) (left right : E → V) (b : E → ℝ)

def amplitudeCoupling (a : V → ℝ) (e : E) : ℝ := b e*a (left e)*a (right e)

def amplitudePartition (a : V → ℝ) : ℝ :=
  ∫ x,Real.exp (edgeHamiltonian T (amplitudeCoupling left right b a) x) ∂μ

def amplitudeSlope (a d : V → ℝ) (t : ℝ) (e : E) : ℝ :=
  b e*(d (left e)*(a (right e)+t*d (right e))+(a (left e)+t*d (left e))*d (right e))

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
 theorem continuous_amplitudeHamiltonian (hT : ∀ e,Continuous (T e)) :
    Continuous (fun p : (V → ℝ)×X => edgeHamiltonian T
      (amplitudeCoupling left right b p.1) p.2) := by
  unfold edgeHamiltonian amplitudeCoupling
  fun_prop

theorem amplitudePartition_pos (hT : ∀ e,Continuous (T e)) (a : V → ℝ) :
    0<amplitudePartition μ T left right b a := by
  exact compact_integral_pos (continuous_edgeHamiltonian T hT _).rexp (fun x => Real.exp_pos _)

theorem continuous_amplitudePartition [Fintype V] (hT : ∀ e,Continuous (T e)) :
    Continuous (amplitudePartition μ T left right b) := by
  exact compact_parametric_integral _ (continuous_amplitudeHamiltonian T left right b hT).rexp

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem amplitudeHamiltonian_direction_derivative (a d : V → ℝ) (t : ℝ) (x : X) :
    HasDerivAt (fun u => edgeHamiltonian T
      (amplitudeCoupling left right b (fun v => a v+u*d v)) x)
      (edgeHamiltonian T (amplitudeSlope left right b a d t) x) t := by
  unfold edgeHamiltonian
  apply HasDerivAt.fun_sum
  intro e _
  have hl := ((hasDerivAt_id t).mul_const (d (left e))).const_add (a (left e))
  have hr := ((hasDerivAt_id t).mul_const (d (right e))).const_add (a (right e))
  exact (((hl.const_mul (b e)).mul hr).mul_const (T e x)).congr_deriv (by
    simp only [id_eq,amplitudeSlope]; ring)

theorem log_amplitudePartition_direction_derivative (hT : ∀ e,Continuous (T e))
    (a d : V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => Real.log (amplitudePartition μ T left right b (fun v => a v+u*d v)))
      (∑ e,amplitudeSlope left right b a d t e*
        edgeMean μ T (amplitudeCoupling left right b (fun v => a v+t*d v)) (T e)) t := by
  let H := fun u x => edgeHamiltonian T
    (amplitudeCoupling left right b (fun v => a v+u*d v)) x
  let A := fun u x => edgeHamiltonian T (amplitudeSlope left right b a d u) x
  have hc : Continuous (fun p : ℝ×X => H p.1 p.2) := by
    unfold H edgeHamiltonian amplitudeCoupling; fun_prop
  have ha : Continuous (fun p : ℝ×X => A p.1 p.2) := by
    unfold A edgeHamiltonian amplitudeSlope; fun_prop
  have hI := hasDerivAt_integral_compact μ (fun u x => Real.exp (H u x))
    (fun u x => Real.exp (H u x)*A u x) hc.rexp (hc.rexp.mul ha) (fun u x =>
      (amplitudeHamiltonian_direction_derivative T left right b a d u x).exp) t
  have hz := amplitudePartition_pos μ T left right b hT (fun v => a v+t*d v)
  apply (hI.log hz.ne').congr_deriv
  change exponentialMean μ (H t) (A t)=_
  unfold A edgeHamiltonian
  rw [exponentialMean_sum μ (continuous_edgeHamiltonian T hT _) _ (fun e => by fun_prop)]
  simp only [exponentialMean_const_mul,edgeMean]

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype E] in
 theorem amplitudeCoupling_mono (hb : ∀ e,0≤b e) {a c : V → ℝ}
    (ha : ∀ v,0≤a v) (hac : ∀ v,a v≤c v) (e : E) :
    amplitudeCoupling left right b a e≤amplitudeCoupling left right b c e := by
  unfold amplitudeCoupling
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hac _) (hb e)) (hac _)
    (ha _) (mul_nonneg (hb e) ((ha _).trans (hac _)))

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype E] in
 theorem amplitudeSlope_nonneg (hb : ∀ e,0≤b e) {a d : V → ℝ}
    (ha : ∀ v,0≤a v) (hd : ∀ v,0≤d v) {t : ℝ} (ht : 0≤t) (e : E) :
    0≤amplitudeSlope left right b a d t e := by
  unfold amplitudeSlope
  exact mul_nonneg (hb e) (add_nonneg
    (mul_nonneg (hd _) (add_nonneg (ha _) (mul_nonneg ht (hd _))))
    (mul_nonneg (add_nonneg (ha _) (mul_nonneg ht (hd _))) (hd _)))

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype E] in
 theorem amplitudeSlope_mono (hb : ∀ e,0≤b e) {a c d : V → ℝ}
    (hd : ∀ v,0≤d v) (hac : ∀ v,a v≤c v) (t : ℝ) (e : E) :
    amplitudeSlope left right b a d t e≤amplitudeSlope left right b c d t e := by
  unfold amplitudeSlope
  apply mul_le_mul_of_nonneg_left _ (hb e)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add (hac _) le_rfl) (hd _))
    (mul_le_mul_of_nonneg_right (add_le_add (hac _) le_rfl) (hd _))

end
end ClassicalON

end

end OAI
