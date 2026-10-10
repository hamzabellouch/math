import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcess
import OAI.Combinatorics.BalancedRyser.Selection.SelectionThinning

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in
theorem sum_flagsWeight (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V) :
    (∑ flags : V → Bool, flagsWeight p q G S flags) = 1 := by
  have h := Fintype.prod_sum
    (fun v : V => fun b : Bool =>
      if b then thinningRate p q G S v else 1 - thinningRate p q G S v)
  simpa [flagsWeight, Fintype.sum_bool] using h.symm

omit [Fintype I] in
theorem sum_drawWeight_vertex (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (i : I) :
    (∑ w : V, drawWeight G S i w) = if i ∈ S.remaining then (S.remaining.card : ℝ)⁻¹ else 0 := by
  by_cases hi : i ∈ S.remaining
  · have hcardS : (S.remaining.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hS
    have hcardD : ((domain G S i).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (hdom i hi)
    simp only [drawWeight, hi, true_and, ite_true]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    field_simp
  · simp [drawWeight, hi]

theorem sum_drawWeight (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty) :
    (∑ i : I, ∑ w : V, drawWeight G S i w) = 1 := by
  simp_rw [sum_drawWeight_vertex G S hS hdom]
  rw [← Finset.sum_filter]
  have hcardS : (S.remaining.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  simp [hcardS]

theorem sum_noiseWeight (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty) :
    (∑ r : Noise I V, noiseWeight p q G S r) = 1 := by
  simp only [Noise, Fintype.sum_prod_type, noiseWeight]
  simp_rw [← Finset.mul_sum, sum_flagsWeight, mul_one]
  exact sum_drawWeight G S hS hdom

theorem sum_stepWeight (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V) :
    (∑ out, stepWeight p q t G S out) = 1 := by
  by_cases hp : Precheck p q t G S
  · simp only [stepWeight, hp, ite_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact sum_noiseWeight p q G S hp.1 (fun i hi => (hp.2.2.2.1 i hi).1)
  · simp [stepWeight, hp]

theorem sum_transitionWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Option (State I V)) :
    (∑ out, transitionWeight p q t G before out) = 1 := by
  cases before with
  | none => simp [transitionWeight]
  | some S => exact sum_stepWeight p q t G S

theorem sum_historyWeight (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ) :
    (∑ out, historyWeight p q G t out) = 1 := by
  induction t with
  | zero => simp [historyWeight]
  | succ t ih =>
    simp only [historyWeight]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_transitionWeight, mul_one]
    exact ih

omit [Fintype I] in
theorem hazard_nonnegative (G : Input I V) (S : State I V) (v : V) :
    0 ≤ hazard G S v := by
  unfold hazard
  positivity

omit [Fintype I] in
theorem thinningRate_bounds_of_precheck (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hp : Precheck p q t G S) (v : V) :
    0 ≤ thinningRate p q G S v ∧ thinningRate p q G S v ≤ p.alpha q := by
  by_cases hv : v ∈ currentVertices G S
  · have h := SelectionThinning.thinningRate_bounds
      (hazard_nonnegative G S v) (hp.2.2.2.2 v hv) hp.2.2.1
    simpa only [thinningRate, hv, ite_true, SelectionThinning.thinningRate] using h
  · simp only [thinningRate, hv, ite_false]
    exact ⟨le_rfl, hp.2.1⟩

omit [Fintype I] in
theorem flagsWeight_nonnegative_of_precheck (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hp : Precheck p q t G S) (flags : V → Bool) :
    0 ≤ flagsWeight p q G S flags := by
  change 0 ≤ SelectionThinning.thinningMass (thinningRate p q G S) flags
  apply SelectionThinning.thinningMass_nonneg
  intro v
  have h := thinningRate_bounds_of_precheck p q t G S hp v
  exact ⟨h.1, h.2.trans hp.2.2.1.le⟩

omit [Fintype I] [Fintype V] in
theorem drawWeight_nonnegative (G : Input I V) (S : State I V) (i : I) (w : V) :
    0 ≤ drawWeight G S i w := by
  unfold drawWeight
  split
  · positivity
  · exact le_rfl

omit [Fintype I] in
theorem noiseWeight_nonnegative_of_precheck (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hp : Precheck p q t G S) (r : Noise I V) :
    0 ≤ noiseWeight p q G S r :=
  mul_nonneg (drawWeight_nonnegative G S r.1 r.2.1)
    (flagsWeight_nonnegative_of_precheck p q t G S hp r.2.2)

theorem stepWeight_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (out : Option (State I V)) : 0 ≤ stepWeight p q t G S out := by
  unfold stepWeight
  split
  · rename_i hp
    apply Finset.sum_nonneg
    intro r _
    split
    · exact noiseWeight_nonnegative_of_precheck p q t G S hp r
    · exact le_rfl
  · split <;> norm_num

theorem transitionWeight_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Option (State I V)) : 0 ≤ transitionWeight p q t G before out := by
  cases before with
  | none => simp only [transitionWeight]; split <;> norm_num
  | some S => exact stepWeight_nonnegative p q t G S out

theorem historyWeight_nonnegative (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (out : Option (State I V)) : 0 ≤ historyWeight p q G t out := by
  induction t generalizing out with
  | zero => simp only [historyWeight]; split <;> norm_num
  | succ t ih =>
    apply Finset.sum_nonneg
    intro before _
    exact mul_nonneg (ih before) (transitionWeight_nonnegative p q t G before out)

theorem sum_drawStepWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Option (State I V)) : (∑ draw, drawStepWeight p q t G before draw) = 1 := by
  cases before with
  | none => simp [drawStepWeight]
  | some S =>
    by_cases hp : Precheck p q t G S
    · simp only [drawStepWeight, hp, ite_true, Fintype.sum_option]
      simpa only [zero_add] using
        sum_noiseWeight p q G S hp.1 (fun i hi => (hp.2.2.2.1 i hi).1)
    · simp [drawStepWeight, hp]

omit [Fintype I] in
theorem drawStepWeight_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Option (State I V)) (draw : Option (Noise I V)) :
    0 ≤ drawStepWeight p q t G before draw := by
  cases before with
  | none => simp only [drawStepWeight]; split <;> norm_num
  | some S =>
    by_cases hp : Precheck p q t G S
    · cases draw with
      | none => simp [drawStepWeight, hp]
      | some r => simpa only [drawStepWeight, hp, ite_true] using
        noiseWeight_nonnegative_of_precheck p q t G S hp r
    · simp only [drawStepWeight, hp, ite_false]; split <;> norm_num

theorem transitionWeight_eq_draw_pushforward (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Option (State I V)) :
    transitionWeight p q t G before out =
      ∑ draw, if advance q G before draw = out then drawStepWeight p q t G before draw else 0 := by
  cases before with
  | none =>
    by_cases ho : out = none <;> simp [transitionWeight, advance, drawStepWeight, ho, eq_comm]
  | some S =>
    by_cases hp : Precheck p q t G S
    · simp [transitionWeight, stepWeight, drawStepWeight, advance, hp, Fintype.sum_option]
    · by_cases ho : out = none <;>
        simp [transitionWeight, stepWeight, drawStepWeight, advance, hp, ho, Fintype.sum_option, eq_comm]

omit [Fintype I] in
theorem snapshotWeight_nonnegative (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) : 0 ≤ snapshotWeight p q t G before out := by
  unfold snapshotWeight
  split
  · exact drawStepWeight_nonnegative p q t G before.1 out.2
  · exact le_rfl

theorem sum_snapshotWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) : (∑ out, snapshotWeight p q t G before out) = 1 := by
  simp only [Snapshot, Fintype.sum_prod_type, snapshotWeight]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact sum_drawStepWeight p q t G before.1

def snapshotPMF (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) : PMF (Snapshot I V) :=
  PMF.ofFintype (fun out => ENNReal.ofReal (snapshotWeight p q t G before out)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun out _ => snapshotWeight_nonnegative p q t G before out)]
    rw [sum_snapshotWeight]
    simp)

theorem snapshotPMF_apply_real (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) :
    (snapshotPMF p q t G before out).toReal = snapshotWeight p q t G before out :=
  ENNReal.toReal_ofReal (snapshotWeight_nonnegative p q t G before out)

def historyPMF (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ) :
    PMF (Option (State I V)) :=
  PMF.ofFintype (fun out => ENNReal.ofReal (historyWeight p q G t out)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun out _ => historyWeight_nonnegative p q G t out)]
    rw [sum_historyWeight]
    simp)

theorem historyPMF_apply_real (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (out : Option (State I V)) :
    (historyPMF p q G t out).toReal = historyWeight p q G t out :=
  ENNReal.toReal_ofReal (historyWeight_nonnegative p q G t out)

end
end Balanced.Selection.Process

end OAI
