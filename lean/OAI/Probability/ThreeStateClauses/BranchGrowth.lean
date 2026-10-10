import Mathlib
import OAI.Probability.ThreeStateClauses.Projection

namespace OAI

/-! Branch Growth. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma continuous_compact_integral {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
    {f : X × Y → ℝ} (hf : Continuous f) : Continuous (fun x ↦ ∫ y, f (x,y) ∂μ) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := (univ : Set Y)) isCompact_univ
  · exact hf.continuousOn
  · simp

lemma continuous_cons (n : ℕ) : Continuous (fun p : Message × (Fin n → Message) ↦ (Fin.cons p.1 p.2 : Fin (n+1) → Message)) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa using (continuous_fst : Continuous (fun p : Message × (Fin n → Message) ↦ p.1))
  · change Continuous (fun p : Message × (Fin n → Message) ↦ p.2 k)
    fun_prop

lemma integral_pi_cons (Q : Law) (n : ℕ) {f : (Fin (n+1) → Message) → ℝ} (hf : Continuous f) :
    (∫ m, f m ∂(Measure.pi fun _ : Fin (n+1) ↦ Q.probability.toMeasure)) =
      ∫ m : Fin n → Message, (∫ e, f (Fin.cons e m) ∂Q.probability.toMeasure)
        ∂(Measure.pi fun _ ↦ Q.probability.toMeasure) := by
  have he : (∫ m, f m ∂(Measure.pi fun _ : Fin (n+1) ↦ Q.probability.toMeasure)) =
      ∫ p : Message × (Fin n → Message), f (Fin.cons p.1 p.2)
        ∂Q.probability.toMeasure.prod (Measure.pi fun _ ↦ Q.probability.toMeasure) := by
    rw [← (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Q.probability.toMeasure) 0).symm.integral_comp']
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq]
  rw [he]
  exact integral_prod_symm _ (compact_integrable (hf.comp (continuous_cons n)))

lemma branchProduct_cons (lam : ℝ) {n : ℕ} (e : Message) (m : Fin n → Message) (i : Fin 3) :
    branchProduct (branchEdges lam (Fin.cons e m)) i = edgeMessage lam e i*branchProduct (branchEdges lam m) i := by
  simp [branchProduct, branchEdges, Fin.prod_univ_succ]

lemma normalizer_cons {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) {n : ℕ} (e : Message) (m : Fin n → Message) :
    normalizer (branchEdges lam (Fin.cons e m)) =
      normalizer (branchEdges lam m)*pairZ lam (branchOutput hl₀ hl₁ m) e := by
  unfold normalizer pairZ
  change avg (fun i ↦ branchProduct (branchEdges lam (Fin.cons e m)) i) = _
  simp_rw [branchProduct_cons]
  change avg (fun i ↦ edgeMessage lam e i*branchProduct (branchEdges lam m) i) =
    avg (branchProduct (branchEdges lam m))*avg (fun i ↦
      (branchProduct (branchEdges lam m) i/normalizer (branchEdges lam m))*edgeMessage lam e i)
  have hz := ne_of_gt (normalizer_positive (branchEdges_positive hl₀ hl₁ m))
  change normalizer (branchEdges lam m) ≠ 0 at hz
  have hid : avg (branchProduct (branchEdges lam m)) = normalizer (branchEdges lam m) := rfl
  rw [hid]
  dsimp only [avg]
  field_simp [hz]

lemma branchOutput_cons {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) {n : ℕ} (e : Message) (m : Fin n → Message) :
    branchOutput hl₀ hl₁ (Fin.cons e m) = pairPosterior hl₀ hl₁ (branchOutput hl₀ hl₁ m) e := by
  apply Subtype.ext
  funext i
  change branchProduct (branchEdges lam (Fin.cons e m)) i/normalizer (branchEdges lam (Fin.cons e m)) =
    (branchProduct (branchEdges lam m) i/normalizer (branchEdges lam m))*edgeMessage lam e i/
      pairZ lam (branchOutput hl₀ hl₁ m) e
  rw [branchProduct_cons, normalizer_cons hl₀ hl₁]
  ring

lemma finite_succ_integral (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ)
    {f : Message → ℝ} (hf : Continuous f) :
    (∫ m, f m ∂(finiteProbability Q hl₀ hl₁ (n+1)).toMeasure) =
      ∫ r, (∫ m, pairZ lam r m*f (pairPosterior hl₀ hl₁ r m) ∂Q.probability.toMeasure)
        ∂(finiteProbability Q hl₀ hl₁ n).toMeasure := by
  have hk : Continuous (fun p : Message × Message ↦ pairZ lam p.1 p.2*f (pairPosterior hl₀ hl₁ p.1 p.2)) :=
    (continuous_pairZ lam).mul (hf.comp (continuous_pairPosterior hl₀ hl₁))
  rw [integral_finiteProbability Q hl₀ hl₁ (n+1) hf.measurable,
    integral_pi_cons Q n (f := fun m ↦ normalizer (branchEdges lam m)*f (branchOutput hl₀ hl₁ m)) ((continuous_normalizer (n+1) lam).mul (hf.comp (continuous_branchOutput hl₀ hl₁ (n+1)))),
    integral_finiteProbability Q hl₀ hl₁ n (continuous_compact_integral hk).measurable]
  congr 1
  funext m
  simp_rw [normalizer_cons hl₀ hl₁, branchOutput_cons hl₀ hl₁, mul_assoc, integral_const_mul]

theorem correlationEntropy_succ (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (n : ℕ) :
    correlationEntropy Q lam (n+1) = correlationEntropy Q lam n + pairCorrelation (finiteLaw Q hl₀ hl₁ n) Q lam := by
  let c : Message → ℝ := fun r ↦ ∫ e, pairZ lam r e*Real.log (pairZ lam r e) ∂Q.probability.toMeasure
  have hc : Continuous c := continuous_compact_integral (continuous_pairEntropy hl₀ hl₁)
  have he (m : Fin n → Message) :
      (∫ e, normalizer (branchEdges lam (Fin.cons e m))*Real.log (normalizer (branchEdges lam (Fin.cons e m)))
        ∂Q.probability.toMeasure) =
      normalizer (branchEdges lam m)*Real.log (normalizer (branchEdges lam m))+
      normalizer (branchEdges lam m)*c (branchOutput hl₀ hl₁ m) := by
    have hp := normalizer_positive (branchEdges_positive hl₀ hl₁ m)
    have hpp (e : Message) := pairZ_positive hl₀ hl₁ (branchOutput hl₀ hl₁ m) e
    have hid (e : Message) :
        normalizer (branchEdges lam (Fin.cons e m))*Real.log (normalizer (branchEdges lam (Fin.cons e m))) =
        (normalizer (branchEdges lam m)*Real.log (normalizer (branchEdges lam m)))*pairZ lam (branchOutput hl₀ hl₁ m) e+
        normalizer (branchEdges lam m)*(pairZ lam (branchOutput hl₀ hl₁ m) e*Real.log (pairZ lam (branchOutput hl₀ hl₁ m) e)) := by
      rw [normalizer_cons hl₀ hl₁, Real.log_mul (ne_of_gt hp) (ne_of_gt (hpp e))]
      ring
    simp_rw [hid]
    have hz : Continuous (fun e ↦ pairZ lam (branchOutput hl₀ hl₁ m) e) :=
      (continuous_pairZ lam).comp (continuous_const.prodMk continuous_id)
    have hj : Continuous (fun e ↦ pairZ lam (branchOutput hl₀ hl₁ m) e*Real.log (pairZ lam (branchOutput hl₀ hl₁ m) e)) :=
      (continuous_pairEntropy hl₀ hl₁).comp (continuous_const.prodMk continuous_id)
    rw [integral_add (f := fun e ↦
      (normalizer (branchEdges lam m)*Real.log (normalizer (branchEdges lam m)))*pairZ lam (branchOutput hl₀ hl₁ m) e)
      (g := fun e ↦ normalizer (branchEdges lam m)*(pairZ lam (branchOutput hl₀ hl₁ m) e*Real.log (pairZ lam (branchOutput hl₀ hl₁ m) e)))
      ((compact_integrable hz).const_mul _) ((compact_integrable hj).const_mul _),
      integral_const_mul, integral_const_mul, integral_pairZ, mul_one]
  unfold correlationEntropy
  rw [integral_pi_cons Q n (continuous_correlationIntegrand hl₀ hl₁ (n+1))]
  simp_rw [he]
  rw [integral_add (f := fun m : Fin n → Message ↦ normalizer (branchEdges lam m)*Real.log (normalizer (branchEdges lam m)))
    (g := fun m ↦ normalizer (branchEdges lam m)*c (branchOutput hl₀ hl₁ m))
    (compact_integrable (continuous_correlationIntegrand hl₀ hl₁ n))
    (compact_integrable ((continuous_normalizer n lam).mul (hc.comp (continuous_branchOutput hl₀ hl₁ n))))]
  congr 1
  exact (integral_finiteProbability Q hl₀ hl₁ n hc.measurable).symm

lemma xMoment_tangent (r s : Message) :
    xMoment r+avg (fun i ↦ (r.1 i-1)*(s.1 i-r.1 i)) ≤ xMoment s := by
  have hp : 0 ≤ avg (fun i ↦ (s.1 i-r.1 i)^2)/2 :=
    by
      dsimp [avg]
      positivity
  have he : xMoment s-xMoment r-avg (fun i ↦ (r.1 i-1)*(s.1 i-r.1 i)) =
      avg (fun i ↦ (s.1 i-r.1 i)^2)/2 := by
    dsimp [xMoment, momentX, centered, avg]; ring
  linarith

lemma xMoment_sq_tangent (r s : Message) :
    xMoment r^2+avg (fun i ↦ 2*xMoment r*(r.1 i-1)*(s.1 i-r.1 i)) ≤ xMoment s^2 := by
  have ht := xMoment_tangent r s
  have he : avg (fun i ↦ 2*xMoment r*(r.1 i-1)*(s.1 i-r.1 i)) =
      2*xMoment r*avg (fun i ↦ (r.1 i-1)*(s.1 i-r.1 i)) := by
    dsimp [avg]; ring
  rw [he]
  nlinarith [mul_nonneg (xMoment_nonneg r) (sub_nonneg.mpr ht), sq_nonneg (xMoment s-xMoment r)]

lemma integral_pair_linear (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (r : Message) (a : Vec) :
    (∫ m, pairZ lam r m*avg (fun i ↦ a i*((pairPosterior hl₀ hl₁ r m).1 i-r.1 i))
      ∂Q.probability.toMeasure) = 0 := by
  have hc (i : Fin 3) : Continuous (fun m : Message ↦ (pairPosterior hl₀ hl₁ r m).1 i) :=
    (continuous_coordinate i).comp ((continuous_pairPosterior hl₀ hl₁).comp (continuous_const.prodMk continuous_id))
  have hz : Continuous (fun m : Message ↦ pairZ lam r m) :=
    (continuous_pairZ lam).comp (continuous_const.prodMk continuous_id)
  have he (m : Message) : pairZ lam r m*avg (fun i ↦ a i*((pairPosterior hl₀ hl₁ r m).1 i-r.1 i)) =
      avg (fun i ↦ a i*(pairZ lam r m*(pairPosterior hl₀ hl₁ r m).1 i-r.1 i*pairZ lam r m)) := by
    dsimp [avg]; ring
  simp_rw [he]
  rw [integral_avg_measure (f := fun m : Message ↦ fun i ↦ a i*(pairZ lam r m*(pairPosterior hl₀ hl₁ r m).1 i-r.1 i*pairZ lam r m))
    (fun i ↦ compact_integrable (continuous_const.mul ((hz.mul (hc i)).sub (continuous_const.mul hz))))]
  have hzero (i : Fin 3) : (∫ m, a i*(pairZ lam r m*(pairPosterior hl₀ hl₁ r m).1 i-r.1 i*pairZ lam r m)
      ∂Q.probability.toMeasure) = 0 := by
    rw [integral_const_mul, integral_sub (f := fun m ↦ pairZ lam r m*(pairPosterior hl₀ hl₁ r m).1 i)
      (g := fun m ↦ r.1 i*pairZ lam r m)
      (compact_integrable (hz.mul (hc i))) ((compact_integrable hz).const_mul _),
      integral_pair_coordinate, integral_const_mul, integral_pairZ]
    ring
  simp_rw [hzero]
  exact avg_const 0

lemma integral_pair_tangent_lower (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    {f : Message → ℝ} (hf : Continuous f) (r : Message) (a : Vec)
    (ht : ∀ s, f r+avg (fun i ↦ a i*(s.1 i-r.1 i)) ≤ f s) :
    f r ≤ ∫ m, pairZ lam r m*f (pairPosterior hl₀ hl₁ r m) ∂Q.probability.toMeasure := by
  have hz : Continuous (fun m : Message ↦ pairZ lam r m) :=
    (continuous_pairZ lam).comp (continuous_const.prodMk continuous_id)
  have hp : Continuous (fun m : Message ↦ pairPosterior hl₀ hl₁ r m) :=
    (continuous_pairPosterior hl₀ hl₁).comp (continuous_const.prodMk continuous_id)
  have hc : Continuous (fun m : Message ↦ avg (fun i ↦ a i*((pairPosterior hl₀ hl₁ r m).1 i-r.1 i))) :=
    continuous_avg.comp (continuous_pi (fun i ↦ continuous_const.mul (((continuous_coordinate i).comp hp).sub continuous_const)))
  have hh := integral_mono (μ := Q.probability.toMeasure)
    (f := fun m ↦ pairZ lam r m*(f r+avg (fun i ↦ a i*((pairPosterior hl₀ hl₁ r m).1 i-r.1 i))))
    (g := fun m ↦ pairZ lam r m*f (pairPosterior hl₀ hl₁ r m))
    (compact_integrable (hz.mul (continuous_const.add hc)))
    (compact_integrable (hz.mul (hf.comp hp)))
    (fun m ↦ mul_le_mul_of_nonneg_left (ht _) (pairZ_positive hl₀ hl₁ r m).le)
  simp_rw [mul_add] at hh
  rw [integral_add (f := fun m ↦ pairZ lam r m*f r)
    (g := fun m ↦ pairZ lam r m*avg (fun i ↦ a i*((pairPosterior hl₀ hl₁ r m).1 i-r.1 i)))
    ((compact_integrable hz).mul_const _) (compact_integrable (hz.mul hc)),
    integral_mul_const, integral_pairZ, integral_pair_linear, one_mul, add_zero] at hh
  exact hh

theorem finite_nu_mono (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    Monotone (fun n ↦ (finiteLaw Q hl₀ hl₁ n).nu) := by
  apply monotone_nat_of_le_succ
  intro n
  change (∫ m, xMoment m^2 ∂(finiteProbability Q hl₀ hl₁ n).toMeasure) ≤
    ∫ m, xMoment m^2 ∂(finiteProbability Q hl₀ hl₁ (n+1)).toMeasure
  rw [finite_succ_integral Q hl₀ hl₁ n (f := fun m ↦ xMoment m^2) (continuous_xMoment.pow 2)]
  apply integral_mono (compact_integrable (continuous_xMoment.pow 2))
    (compact_integrable (continuous_compact_integral
      ((continuous_pairZ lam).mul ((continuous_xMoment.pow 2).comp (continuous_pairPosterior hl₀ hl₁)))))
  intro r
  exact integral_pair_tangent_lower Q hl₀ hl₁ (continuous_xMoment.pow 2) r
    (fun i ↦ 2*xMoment r*(r.1 i-1)) (xMoment_sq_tangent r)

end ThreeState.TreeClauses.Experiment

end

end OAI
