import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Probability.ConditionalRestriction

namespace OAI

namespace Balanced.FreshWitnessProbability

open ConditionalRestriction TupleAlignment
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem offsetLaw_uniform : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
  ext M
  simp only [offsetLaw, PMF.uniformOfFintype_apply, Fintype.card_fun,
    Fintype.card_option, Fintype.card_bool]

def exposedLaw (D : Finset (Direction F)) (a : MergedPairs F) : PMF (MergedPairs F) :=
  (offsetLaw F).filter {M | ∀ d, d ∈ D → M d = a d}
    ⟨a, by intro d hd; rfl, by simp [offsetLaw]⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exposedLaw_map_fresh (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D) :
    (exposedLaw D a).map (fun M i => M (e i)) =
      PMF.uniformOfFintype (ι → Bool → F) := by
  have h := uniform_conditional_restrict (A := Bool → F) e (fun d => d ∈ D) a
  have hset : {o : ι → Bool → F | ∀ i, e i ∈ D → o i = a (e i)} = Set.univ := by
    ext o
    simp [hfresh]
  have htarget : ((PMF.uniformOfFintype (ι → Bool → F)).filter
      {o | ∀ i, e i ∈ D → o i = a (e i)}
      (fixed_supported (fun i => e i ∈ D) (fun i => a (e i)))) =
      PMF.uniformOfFintype (ι → Bool → F) := by
    ext o
    simp only [PMF.filter_apply, hset, Set.indicator_univ, PMF.tsum_coe,
      inv_one, mul_one]
  rw [htarget] at h
  simpa only [exposedLaw, offsetLaw_uniform] using h

theorem prescribed_offsets_probability (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D) (b : ι → Bool → F) :
    ((exposedLaw D a).toOuterMeasure {M | ∀ i, M (e i) = b i}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ (2 * Fintype.card ι) := by
  have h := congrArg (fun p => (p.toOuterMeasure {b}).toReal)
    (exposedLaw_map_fresh D a e hfresh)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton] at h
  have hevent : (fun M i => M (e i)) ⁻¹' {b} =
      {M : MergedPairs F | ∀ i, M (e i) = b i} := by
    ext M
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact funext_iff
  rw [hevent] at h
  simpa only [PMF.uniformOfFintype_apply, Fintype.card_fun,
    Fintype.card_bool, Nat.cast_pow, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, inv_pow, pow_mul] using h

theorem prescribed_point_incidence_probability
    (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D)
    (p : ι → Bool → Point F) :
    ((exposedLaw D a).toOuterMeasure
      {M | ∀ i s, OnLine (p i s) (constituent M (e i) s)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ (2 * Fintype.card ι) := by
  have hevent : {M : MergedPairs F |
      ∀ i s, OnLine (p i s) (constituent M (e i) s)} =
      {M | ∀ i, M (e i) = fun s => lineEval (e i) (p i s)} := by
    ext M
    simp only [Set.mem_ofPred_eq, OnLine, constituent]
    constructor
    · intro h i
      funext s
      exact (h i s).symm
    · intro h i s
      exact (congrFun (h i) s).symm
  rw [hevent]
  exact prescribed_offsets_probability D a e hfresh _

theorem probability_exists_le_sum {Ω κ : Type*} [Fintype κ]
    (law : PMF Ω) (E : κ → Set Ω) :
    (law.toOuterMeasure {ω | ∃ i, ω ∈ E i}).toReal ≤
      ∑ i, (law.toOuterMeasure (E i)).toReal := by
  have hfinite (i : κ) : law.toOuterMeasure (E i) ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact law.tsum_coe_indicator_ne_top _
  have h := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun i _ => hfinite i))
    (MeasureTheory.measure_iUnion_fintype_le law.toOuterMeasure E)
  rw [ENNReal.toReal_sum (fun i _ => hfinite i)] at h
  simpa only [Set.ofPred_exists, Set.ofPred_mem_eq] using h

theorem oriented_pairs_probability
    (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D)
    (x y : ι → Point F) (σ : ι → Bool) :
    ((exposedLaw D a).toOuterMeasure {M | ∀ i,
      OnLine (x i) (constituent M (e i) (σ i)) ∧
      OnLine (y i) (constituent M (e i) (!(σ i)))}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ (2 * Fintype.card ι) := by
  let b (i : ι) (s : Bool) : F :=
    if s = σ i then lineEval (e i) (x i) else lineEval (e i) (y i)
  have hevent : {M : MergedPairs F | ∀ i,
      OnLine (x i) (constituent M (e i) (σ i)) ∧
      OnLine (y i) (constituent M (e i) (!(σ i)))} =
      {M | ∀ i, M (e i) = b i} := by
    ext M
    simp only [Set.mem_ofPred_eq, OnLine, constituent]
    constructor
    · intro h i
      funext s
      cases hs : σ i <;> cases s
      · simpa [b, hs] using (h i).1.symm
      · simpa [b, hs] using (h i).2.symm
      · simpa [b, hs] using (h i).2.symm
      · simpa [b, hs] using (h i).1.symm
    · intro h i
      have hfalse := congrFun (h i) false
      have htrue := congrFun (h i) true
      cases hs : σ i <;> simp_all [b]
  rw [hevent]
  exact prescribed_offsets_probability D a e hfresh b

theorem paired_witnesses_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D)
    (x y : ι → Point F) :
    ((exposedLaw D a).toOuterMeasure {M | ∃ σ : ι → Bool, ∀ i,
      OnLine (x i) (constituent M (e i) (σ i)) ∧
      OnLine (y i) (constituent M (e i) (!(σ i)))}).toReal ≤
      (2 : ℝ) ^ Fintype.card ι *
        (Fintype.card F : ℝ)⁻¹ ^ (2 * Fintype.card ι) := by
  calc
    _ ≤ ∑ σ : ι → Bool, ((exposedLaw D a).toOuterMeasure {M | ∀ i,
        OnLine (x i) (constituent M (e i) (σ i)) ∧
        OnLine (y i) (constituent M (e i) (!(σ i)))}).toReal :=
      probability_exists_le_sum _ _
    _ = _ := by
      simp only [oriented_pairs_probability D a e hfresh, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]

end
end Balanced.FreshWitnessProbability

end OAI
