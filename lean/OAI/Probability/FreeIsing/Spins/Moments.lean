import OAI.Probability.FreeIsing.Estimates.CylinderBasics
import OAI.Probability.FreeIsing.Spins.Kernel
import OAI.Probability.FreeIsing.Trees.EdgeCylinders

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def IsingSpin.toReal : IsingSpin → ℝ
  | .neg => -1
  | .pos => 1

@[simp] lemma IsingSpin.toReal_neg : IsingSpin.toReal .neg = -1 := rfl
@[simp] lemma IsingSpin.toReal_pos : IsingSpin.toReal .pos = 1 := rfl

local instance spinMomentsMeasurableSingleton : MeasurableSingletonClass IsingSpin where
  measurableSet_singleton _ := trivial

lemma measurable_spinToReal : Measurable IsingSpin.toReal := measurable_of_finite _

lemma measurable_spinEvent {d : ℕ} (v : TreeVertex d) (s : IsingSpin) :
    MeasurableSet {x : TreeVertex d → IsingSpin | x v = s} :=
  measurableSet_eq_fun (measurable_pi_apply v) measurable_const

lemma HasFreeIsingLaw.isProbabilityMeasure {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu) :
    IsProbabilityMeasure mu := by
  let v : TreeVertex d := ⟨[], List.isChain_nil⟩
  have hu : (Set.univ : Set (TreeVertex d → IsingSpin)) =
      {x | x v = IsingSpin.neg} ∪ {x | x v = IsingSpin.pos} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_ofPred_eq, true_iff]
    cases x v <;> simp
  have hd : Disjoint {x : TreeVertex d → IsingSpin | x v = IsingSpin.neg}
      {x | x v = IsingSpin.pos} := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact IsingSpin.noConfusion (hx.symm.trans hy)
  constructor
  rw [hu, measure_union hd (measurable_spinEvent v .pos),
    h.marginal v .neg, h.marginal v .pos]
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.add_halves 1

lemma norm_spinToReal (s : IsingSpin) : ‖s.toReal‖ = 1 := by
  cases s <;> norm_num [IsingSpin.toReal]

lemma integrable_spin {d : ℕ} (mu : Measure (TreeVertex d → IsingSpin))
    [IsFiniteMeasure mu] (v : TreeVertex d) :
    Integrable (fun x => (x v).toReal) mu := by
  apply Integrable.of_bound (measurable_spinToReal.comp (measurable_pi_apply v)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => (norm_spinToReal (x v)).le)

lemma HasFreeIsingLaw.integral_spin {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) : ∫ x, (x v).toReal ∂mu = 0 := by
  let := h.isProbabilityMeasure
  have hf : (fun x : TreeVertex d → IsingSpin => (x v).toReal) =
      (fun x => ({x | x v = IsingSpin.pos} : Set (TreeVertex d → IsingSpin)).indicator (fun _ => (2 : ℝ)) x - 1) := by
    funext x
    cases hv : x v <;> simp [hv, Set.indicator, IsingSpin.toReal]
    norm_num
  rw [hf, integral_sub]
  · rw [integral_indicator_const _ (measurable_spinEvent v .pos), integral_const]
    simp [Measure.real, h.marginal v .pos]
  · exact (integrable_const (2 : ℝ)).indicator (measurable_spinEvent v .pos)
  · exact integrable_const 1

lemma HasFreeIsingLaw.integral_spin_sq {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) : ∫ x, (x v).toReal ^ 2 ∂mu = 1 := by
  let := h.isProbabilityMeasure
  have hf : (fun x : TreeVertex d → IsingSpin => (x v).toReal ^ 2) = fun _ => (1 : ℝ) := by
    funext x
    cases x v <;> norm_num [IsingSpin.toReal]
  rw [hf]
  simp

lemma memLp_spin {d : ℕ} (mu : Measure (TreeVertex d → IsingSpin))
    [IsFiniteMeasure mu] (v : TreeVertex d) (p : ENNReal) :
    MemLp (fun x => (x v).toReal) p mu := by
  apply MemLp.of_bound (measurable_spinToReal.comp (measurable_pi_apply v)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => (norm_spinToReal (x v)).le)

lemma HasFreeIsingLaw.variance_spin {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) : ProbabilityTheory.variance (fun x => (x v).toReal) mu = 1 := by
  have hm : Measurable (fun x : TreeVertex d → IsingSpin => (x v).toReal) :=
    measurable_spinToReal.comp (measurable_pi_apply v)
  rw [ProbabilityTheory.variance_eq_integral hm.aemeasurable, h.integral_spin v]
  simpa only [sub_zero] using h.integral_spin_sq v

lemma HasFreeIsingLaw.integral_factor_spin {d : ℕ} {theta : ℝ}
    {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}
    (hPhi : Measurable Phi)
    (h : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (v : TreeVertex d) : ∫ U, (Phi U v).toReal ∂labelMeasure d = 0 := by
  have hm : Measurable (fun x : TreeVertex d → IsingSpin => (x v).toReal) :=
    measurable_spinToReal.comp (measurable_pi_apply v)
  exact (integral_map (μ := labelMeasure d) hPhi.aemeasurable hm.aestronglyMeasurable).symm.trans
    (h.integral_spin v)

lemma HasFreeIsingLaw.integral_factor_spin_sq {d : ℕ} {theta : ℝ}
    {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}
    (hPhi : Measurable Phi)
    (h : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (v : TreeVertex d) : ∫ U, (Phi U v).toReal ^ 2 ∂labelMeasure d = 1 := by
  have hm : Measurable (fun x : TreeVertex d → IsingSpin => (x v).toReal ^ 2) :=
    (measurable_spinToReal.comp (measurable_pi_apply v)).pow_const 2
  exact (integral_map (μ := labelMeasure d) hPhi.aemeasurable hm.aestronglyMeasurable).symm.trans
    (h.integral_spin_sq v)

lemma integral_spin_mul_of_diagonal {d : ℕ}
    (mu : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure mu]
    (u v : TreeVertex d) (rho : ℝ) (hrho : -1 ≤ rho)
    (hneg : mu {x | x u = IsingSpin.neg ∧ x v = IsingSpin.neg} =
      ENNReal.ofReal ((1 + rho) / 4))
    (hpos : mu {x | x u = IsingSpin.pos ∧ x v = IsingSpin.pos} =
      ENNReal.ofReal ((1 + rho) / 4)) :
    ∫ x, (x u).toReal * (x v).toReal ∂mu = rho := by
  have hE : MeasurableSet {x : TreeVertex d → IsingSpin | x u = x v} :=
    measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply v)
  have hsplit : {x : TreeVertex d → IsingSpin | x u = x v} =
      {x | x u = IsingSpin.neg ∧ x v = IsingSpin.neg} ∪
      {x | x u = IsingSpin.pos ∧ x v = IsingSpin.pos} := by
    ext x
    cases hu : x u <;> cases hv : x v <;> simp [hu, hv]
  have hdisj : Disjoint
      {x : TreeVertex d → IsingSpin | x u = IsingSpin.neg ∧ x v = IsingSpin.neg}
      {x | x u = IsingSpin.pos ∧ x v = IsingSpin.pos} := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact IsingSpin.noConfusion (hx.1.symm.trans hy.1)
  have hmeasure : mu {x | x u = x v} = ENNReal.ofReal ((1 + rho) / 2) := by
    rw [hsplit, measure_union hdisj
      ((measurable_spinEvent u .pos).inter (measurable_spinEvent v .pos)), hneg, hpos]
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ (1 + rho) / 4)
      (by linarith : 0 ≤ (1 + rho) / 4)]
    congr 1
    ring
  have hf : (fun x : TreeVertex d → IsingSpin => (x u).toReal * (x v).toReal) =
      (fun x => ({x | x u = x v} : Set (TreeVertex d → IsingSpin)).indicator
        (fun _ => (2 : ℝ)) x - 1) := by
    funext x
    cases hu : x u <;> cases hv : x v <;>
      simp [hu, hv, IsingSpin.toReal, Set.indicator] <;> norm_num
  rw [hf, integral_sub]
  · rw [integral_indicator_const _ hE, integral_const]
    simp only [Measure.real, hmeasure, ENNReal.toReal_ofReal (by linarith : 0 ≤ (1 + rho) / 2),
      smul_eq_mul, measure_univ, ENNReal.toReal_one, one_mul]
    ring
  · exact (integrable_const (2 : ℝ)).indicator hE
  · exact integrable_const 1

theorem IsingSpin.toReal_eq_spinSign (s : IsingSpin) : s.toReal = spinSign s := by
  cases s <;> rfl

lemma HasFreeIsingLaw.integral_spinSign {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) : ∫ x, spinSign (x v) ∂mu = 0 := by
  simpa only [IsingSpin.toReal_eq_spinSign] using h.integral_spin v

lemma HasFreeIsingLaw.integral_spinSign_sq {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) : ∫ x, spinSign (x v) ^ 2 ∂mu = 1 := by
  simpa only [IsingSpin.toReal_eq_spinSign] using h.integral_spin_sq v

lemma HasFreeIsingLaw.variance_spinSign {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) : ProbabilityTheory.variance (fun x => spinSign (x v)) mu = 1 := by
  simpa only [IsingSpin.toReal_eq_spinSign] using h.variance_spin v

lemma HasFreeIsingLaw.integral_edge_spin {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu)
    (htheta : -1 ≤ theta) {u v : TreeVertex d} (huv : treeAdj u v) :
    ∫ x, (x u).toReal * (x v).toReal ∂mu = theta := by
  let := h.isProbabilityMeasure
  apply integral_spin_mul_of_diagonal mu u v theta htheta
  · simpa only [ite_true] using h.edge_cylinder huv .neg .neg
  · simpa only [ite_true] using h.edge_cylinder huv .pos .pos

lemma HasFreeIsingLaw.integral_edge_spinSign {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (h : HasFreeIsingLaw theta mu)
    (htheta : -1 ≤ theta) {u v : TreeVertex d} (huv : treeAdj u v) :
    ∫ x, spinSign (x u) * spinSign (x v) ∂mu = theta := by
  simpa only [IsingSpin.toReal_eq_spinSign] using h.integral_edge_spin htheta huv

end Problem367

end

end OAI
