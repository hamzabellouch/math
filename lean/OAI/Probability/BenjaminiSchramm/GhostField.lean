import OAI.Probability.BenjaminiSchramm.TwoGhost
import OAI.Probability.CriticalPercolation.ProductMeasure.TailProduct

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm

def ghostRate (h x : ℝ≥0) : unitInterval :=
  ⟨ghostKernel h x, ghostKernel_nonneg h.2 x.2, ghostKernel_le_one h x⟩

def ghostFieldLaw {V : Type*} (h : ℝ≥0) (w : V → ℝ≥0) : Measure (Set V) :=
  CriticalPercolation.BernoulliProduct.law (fun v => ghostRate h (w v))

instance ghostFieldLaw_probability {V : Type*} (h : ℝ≥0) (w : V → ℝ≥0) :
    IsProbabilityMeasure (ghostFieldLaw h w) := by
  unfold ghostFieldLaw
  infer_instance

lemma ghostRate_closed_probability (h x : ℝ≥0) :
    CriticalPercolation.BernoulliProduct.bitMeasure (ghostRate h x) {False} =
      ENNReal.ofReal (Real.exp (-(h : ℝ) * x)) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change ENNReal.ofReal
    ((CriticalPercolation.BernoulliProduct.bitMeasure (ghostRate h x)).real {False}) = _
  rw [CriticalPercolation.BernoulliProduct.bitMeasure_real_singleton]
  simp [CriticalPercolation.BernoulliProduct.bitWeight, ghostRate, ghostKernel]

theorem ghostFieldLaw_avoid_finset {V : Type*} (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V) :
    ghostFieldLaw h w {m | Disjoint (S : Set V) m} =
      ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) := by
  unfold ghostFieldLaw
  have hm : MeasurableSet {m : Set V | Disjoint (S : Set V) m} := by
    rw [show {m : Set V | Disjoint (S : Set V) m} = ⋂ v ∈ S, {m | v ∉ m} from by
      ext m
      simp [Set.disjoint_left]]
    exact S.measurableSet_biInter fun v _ => (measurable_set_mem v).setOf.compl
  rw [CriticalPercolation.BernoulliProduct.law,
    Measure.map_apply MeasurableEquiv.setOfPred.measurable hm]
  have he : MeasurableEquiv.setOfPred ⁻¹' {m : Set V | Disjoint (S : Set V) m} =
      ((S : Set V).pi (fun _ => {False}) : Set (V → Prop)) := by
    ext f
    change Disjoint (S : Set V) {v | f v} ↔ ∀ v ∈ (S : Set V), f v = False
    constructor
    · intro hd v hv
      exact propext (iff_false_intro fun hf => Set.disjoint_left.mp hd hv hf)
    · intro hd
      apply Set.disjoint_left.mpr
      intro v hv hf
      change f v at hf
      rw [hd v hv] at hf
      exact hf
  rw [he]
  erw [Measure.infinitePi_pi
    (μ := fun v : V => CriticalPercolation.BernoulliProduct.bitMeasure (ghostRate h (w v)))
    (s := S) (t := fun _ : V => ({False} : Set Prop)) (fun _ _ => MeasurableSet.of_discrete)]
  simp_rw [ghostRate_closed_probability]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  exact (Finset.mul_sum S _ _).symm

theorem ghostFieldLaw_avoid_finite {V : Type*} (h : ℝ≥0) (w : V → ℝ≥0)
    (S : Set V) (hS : S.Finite) :
    ghostFieldLaw h w {m | Disjoint S m} =
      ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ hS.toFinset, (w v : ℝ))) := by
  convert ghostFieldLaw_avoid_finset h w hS.toFinset using 1
  rw [hS.coe_toFinset]

def ghostHits {V : Type*} (S : Set V) : Set (Set V) := {m | ∃ v ∈ S, v ∈ m}

lemma measurableSet_ghostHits {V : Type*} [Countable V] (S : Set V) :
    MeasurableSet (ghostHits S) :=
  (Measurable.exists fun v => measurable_const.and (measurable_set_mem v)).setOf

lemma ghostHits_compl {V : Type*} (S : Set V) : (ghostHits S)ᶜ = {m | Disjoint S m} := by
  ext m
  simp [ghostHits, Set.disjoint_left]

theorem ghostFieldLaw_real_hit_finset {V : Type*} [Countable V]
    (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V) :
    (ghostFieldLaw h w).real (ghostHits (S : Set V)) =
      ghostKernel h (∑ v ∈ S, (w v : ℝ)) := by
  have he := probReal_compl_eq_one_sub (μ := ghostFieldLaw h w)
    (measurableSet_ghostHits (S : Set V))
  rw [ghostHits_compl, measureReal_def, ghostFieldLaw_avoid_finset,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
  dsimp [ghostKernel]
  linarith

theorem twoGhostFieldLaw_real_hit_finset {V : Type*} [Countable V]
    (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V) :
    ((ghostFieldLaw h w).prod (ghostFieldLaw h w)).real
      (ghostHits (S : Set V) ×ˢ ghostHits (S : Set V)) =
        ghostKernel h (∑ v ∈ S, (w v : ℝ)) ^ 2 := by
  rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
  change (ghostFieldLaw h w).real (ghostHits (S : Set V)) *
    (ghostFieldLaw h w).real (ghostHits (S : Set V)) = _
  rw [ghostFieldLaw_real_hit_finset, sq]

end Percolation.BenjaminiSchramm

end

end OAI
