import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferFirstFailure
import OAI.Probability.Ballisticity.Estimates.BudgetClipping

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev SupportedTupleMeasures {d k : ℕ} (C : Set (Fin k → Lattice d)) :=
  {π : Measure (Fin k → Lattice d) // π Cᶜ = 0}

lemma supportedTupleMeasures_singleton {d k : ℕ} (C : Set (Fin k → Lattice d))
    (π : SupportedTupleMeasures C) {x : Fin k → Lattice d} (hx : x ∉ C) : π.val {x} = 0 := by
  apply le_antisymm _ bot_le
  calc
    π.val {x} ≤ π.val Cᶜ := measure_mono (Set.singleton_subset_iff.mpr hx)
    _ = 0 := π.property

lemma relativeBudgetWordLaw_rows {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (x : Fin k → Lattice d) (S : Set (Lattice d))
    (hx : ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => relativeBudgetWordLaw e f H r ω x) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply TupleKernel.measurable_countable_measure
  intro w
  simp only [relativeBudgetWordLaw,TupleKernel.restrict_singleton]
  by_cases hb : TupleRelativeBudget e f x H r w
  · simp only [hb,Set.mem_ofPred_eq,ite_eq_left,rawTupleWordLaw_singleton]
    apply Finset.measurable_prod
    intro j _
    exact (Measure.measurable_coe (measurableSet_singleton (w j))).comp
      ((measurable_rawWordLaw_rows (realPosition (step e)) H (x j)).mono
        (rowSigma_mono (hx j)) le_rfl)
  · simp only [Set.mem_ofPred_eq,hb,ite_false]
    exact measurable_const

noncomputable def relativeBudgetMassENN {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d) : ℝ≥0∞ :=
  ∫⁻ x, relativeBudgetWordLaw e f H r ω x Set.univ ∂π

lemma relativeBudgetMassENN_joint_rows {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (C : Set (Fin k → Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable (SupportedTupleMeasures C × Environment d) ℝ≥0∞
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => relativeBudgetMassENN e f H r p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  simp only [relativeBudgetMassENN,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · exact (((Measure.measurable_coe MeasurableSet.univ).comp
      (relativeBudgetWordLaw_rows e f H r x S (hC x hx))).comp measurable_snd).mul
      ((Measure.measurable_coe (measurableSet_singleton x)).comp
        (measurable_subtype_coe.comp measurable_fst))
  · have he : (fun p : SupportedTupleMeasures C × Environment d =>
        relativeBudgetWordLaw e f H r p.2 x Set.univ*p.1.val {x}) = fun _ => 0 := by
      funext p
      rw [supportedTupleMeasures_singleton C p.1 hx,mul_zero]
    rw [he]
    exact measurable_const

lemma relativeBudgetMassENN_le_one {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π]
    (ω : Environment d) : relativeBudgetMassENN e f H r π ω ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : Fin k → Lattice d, (1:ℝ≥0∞) ∂π :=
      lintegral_mono fun x => relativeBudgetWordLaw_le_one e f H r ω x
    _ = 1 := by simp

lemma relativeBudgetMassENN_toReal {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π]
    (ω : Environment d) : (relativeBudgetMassENN e f H r π ω).toReal =
      relativeBudgetMass e f H r π ω := by
  symm
  exact integral_toReal (measurable_of_countable _).aemeasurable
    (ae_of_all _ fun x => measure_lt_top (relativeBudgetWordLaw e f H r ω x) Set.univ)

def TupleAtHeight {d k : ℕ} (ℓ : Vector d) (a : ℝ) : Set (Fin k → Lattice d) :=
  {x | ∀ j, dot (realPosition (x j)) ℓ = a}

noncomputable def budgetTraversalMass {d k : ℕ} (e f : Direction d) (a r : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (h : ℕ) (ω : Environment d) : ℝ≥0∞ :=
  if h=0 then 1 else relativeBudgetMassENN e f h r (π ω).val ω

lemma budgetTraversalMass_adapted {d k : ℕ} (e f : Direction d) (a r : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    Adapted (rowHeightFiltration (realPosition (step e)) a) (budgetTraversalMass e f a r π) := by
  intro h
  by_cases hh : h=0
  · simp only [hh]
    exact measurable_const
  · have hle : rowSigma (BelowHeight (realPosition (step e)) a) ≤
        rowSigma (BelowHeight (realPosition (step e)) (a+h)) := by
      apply rowSigma_mono
      intro y hy
      dsimp [BelowHeight] at hy ⊢
      have : (0:ℝ) ≤ h := Nat.cast_nonneg h
      linarith
    have hC (x : Fin k → Lattice d) (hx : x ∈ TupleAtHeight (k := k) (realPosition (step e)) a) :
        ∀ j, Strip (realPosition (step e)) (x j) h ⊆ BelowHeight (realPosition (step e)) (a+h) := by
      intro j y hy
      change dot (realPosition y) (realPosition (step e)) < a+h
      simpa only [hx j] using hy.2
    have hp := hπ.mono hle le_rfl
    have hm := (relativeBudgetMassENN_joint_rows e f h r (TupleAtHeight (k := k) (realPosition (step e)) a)
      (BelowHeight (realPosition (step e)) (a+h)) hC).comp (hp.prodMk measurable_id)
    change @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+h))) _ _
    unfold budgetTraversalMass
    simp only [ite_eq_right hh]
    exact hm

noncomputable def budgetFirstThreat {d k : ℕ} (e f : Direction d) (a r g : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (H : ℕ) : Environment d → ℕ :=
  hittingBtwn (budgetTraversalMass e f a r π) (Set.Iio (ENNReal.ofReal g)) 1 H

lemma budgetFirstThreat_stopping {d k : ℕ} (e f : Direction d) (a r g : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) (H : ℕ) :
    IsStoppingTime (rowHeightFiltration (realPosition (step e)) a)
      (fun ω => (budgetFirstThreat e f a r g π H ω : WithTop ℕ)) :=
  (budgetTraversalMass_adapted e f a r π hπ).isStoppingTime_hittingBtwn measurableSet_Iio

lemma before_budgetFirstThreat_pass {d k : ℕ} (e f : Direction d) (a r g : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (H : ℕ) (ω : Environment d) {j : ℕ} (hj : 0 < j)
    (hjlt : j < budgetFirstThreat e f a r g π H ω) :
    ENNReal.ofReal g ≤ relativeBudgetMassENN e f j r (π ω).val ω := by
  have hn := notMem_of_lt_hittingBtwn hjlt hj
  simpa only [budgetTraversalMass,ite_eq_right (Nat.ne_of_gt hj),Set.mem_Iio,not_lt] using hn

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma upwardWord_successful {d : ℕ} (e : Direction d) (x : Lattice d) :
    wordPath x [e] ∈ HitAt (Strip (realPosition (step e)) x (1:ℕ))
      (Upper (realPosition (step e)) x (1:ℕ)) [e].length := by
  constructor
  · change dot (realPosition x) (realPosition (step e)) + (1:ℕ) ≤
      dot (realPosition (x+step e)) (realPosition (step e))
    simp only [dot_signed_direction,signedCoordinate_add,signedCoordinate_step_self,Nat.cast_one,le_refl]
  · intro n hn
    have : n=0 := by simpa using hn
    subst n
    change dot (realPosition x) (realPosition (step e)) ≤ dot (realPosition x) (realPosition (step e)) ∧
      dot (realPosition x) (realPosition (step e)) < dot (realPosition x) (realPosition (step e))+(1:ℕ)
    constructor <;> simp

def upwardHitWord {d : ℕ} (e : Direction d) (x : Lattice d) :
    HitWord x (Strip (realPosition (step e)) x (1:ℕ)) (Upper (realPosition (step e)) x (1:ℕ)) :=
  ⟨[e],upwardWord_successful e x⟩

lemma relativeWordDisplacement_zero {d : ℕ} (e f : Direction d) (x : Lattice d)
    (w : List (Direction d)) : relativeWordDisplacement e f x 0 w = 0 := by
  have ht : wordFirstHitTime e x 0 w = 0 := Nat.eq_zero_of_le_zero
    (wordFirstHitTime_le e x 0 w (by simp))
  simp [relativeWordDisplacement,wordFirstHitPosition,ht,signedCoordinate]

lemma upwardWord_budget {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (x : Fin k → Lattice d) : TupleRelativeBudget e f x 1 0 (fun _ => [e]) := by
  intro s hs i j
  interval_cases s
  · simp only [relativeWordDisplacement_zero,sub_self,abs_zero,le_refl]
  · have hd (y : Lattice d) : relativeWordDisplacement e f y 1 [e] = 0 := by
      rw [show [e] = (upwardHitWord e y).val from rfl,
        relativeWordDisplacement_endpoint e f y 1 (upwardHitWord e y)]
      simp only [upwardHitWord,List.length_singleton,wordPath,add_sub_cancel_left,
        signedCoordinate_step_other f e hef.symm]
    simp only [hd,sub_self,abs_zero,le_refl]

def tupleAppendUpward {d k : ℕ} (e : Direction d) (w : Fin k → List (Direction d)) :
    Fin k → List (Direction d) := fun j => w j ++ [e]

lemma tupleAppendUpward_injective {d k : ℕ} (e : Direction d) :
    Function.Injective (tupleAppendUpward (k := k) e) := by
  intro u v h
  funext j
  exact List.append_cancel_right (congrFun h j)

lemma tupleAppendUpward_budget {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (x : Fin k → Lattice d) (H : ℕ) (r : ℝ)
    (w : ∀ j, HitWord (x j) (Strip (realPosition (step e)) (x j) H) (Upper (realPosition (step e)) (x j) H))
    (hb : TupleRelativeBudget e f x H r (fun j => (w j).val)) :
    TupleRelativeBudget e f x (H+1) r (tupleAppendUpward e (fun j => (w j).val)) := by
  change TupleRelativeBudget e f x (H+1) r (fun j => (w j).val++[e])
  simpa only [add_zero,upwardHitWord] using
    tupleRelativeBudget_append e f x H 1 r 0 le_rfl w
      (fun j => upwardHitWord e (wordPath (x j) (w j).val (w j).val.length)) hb
      (upwardWord_budget e f hef _)

lemma rawWordLaw_upward_atom {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d)
    (x : Lattice d)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)) :
    rawWordLaw (realPosition (step e)) (H+1) ω x {w.val++[e]} =
      rawWordLaw (realPosition (step e)) H ω x {w.val} *
        ((ω (wordPath x w.val w.val.length)).1 e : ℝ≥0∞) := by
  have hc := wordPath_hit_append e x H 1 w (upwardHitWord e (wordPath x w.val w.val.length))
  change wordPath x (w.val++[e]) ∈ HitAt (Strip (realPosition (step e)) x (H+1:ℕ))
    (Upper (realPosition (step e)) x (H+1:ℕ)) (w.val++[e]).length at hc
  rw [rawWordLaw_singleton,ite_eq_left hc,rawWordLaw_singleton,ite_eq_left w.property,
    wordWeight_append,ENNReal.ofReal_mul (wordWeight_nonneg _ _ _)]
  simp only [wordWeight,mul_one,ENNReal.ofReal_coe_nnreal]

lemma relativeBudgetWordLaw_upward {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞)^k • (relativeBudgetWordLaw e f H r ω x).map (tupleAppendUpward e) ≤
      relativeBudgetWordLaw e f (H+1) r ω x := by
  rw [← Measure.map_smul _ (measurable_of_countable _).aemeasurable]
  let S : Set (Fin k → List (Direction d)) := {w | TupleRelativeBudget e f x H r w ∧
    ∀ j, wordPath (x j) (w j) ∈ HitAt (Strip (realPosition (step e)) (x j) H)
      (Upper (realPosition (step e)) (x j) H) (w j).length}
  apply TupleKernel.countable_restricted_map_le _ _ S _ (tupleAppendUpward_injective e).injOn
  · intro w hw
    rw [Measure.smul_apply,smul_eq_mul,relativeBudgetWordLaw_singleton]
    by_cases hb : TupleRelativeBudget e f x H r w
    · rw [ite_eq_left hb,rawTupleWordLaw_singleton]
      have hj : ∃ j, ¬ wordPath (x j) (w j) ∈ HitAt (Strip (realPosition (step e)) (x j) H)
          (Upper (realPosition (step e)) (x j) H) (w j).length := by
        by_contra hn
        push Not at hn
        exact hw ⟨hb,hn⟩
      obtain ⟨j,hj⟩ := hj
      have hz := Finset.prod_eq_zero (f := fun j => rawWordLaw (realPosition (step e)) H ω (x j) {w j}) (Finset.mem_univ j)
        (show rawWordLaw (realPosition (step e)) H ω (x j) {w j}=0 by rw [rawWordLaw_singleton,ite_eq_right hj])
      rw [hz,mul_zero]
    · rw [ite_eq_right hb,mul_zero]
  · intro w hw
    let u j : HitWord (x j) (Strip (realPosition (step e)) (x j) H) (Upper (realPosition (step e)) (x j) H) :=
      ⟨w j,hw.2 j⟩
    have hb := tupleAppendUpward_budget e f hef x H r u hw.1
    rw [Measure.smul_apply,smul_eq_mul,relativeBudgetWordLaw_singleton,ite_eq_left hw.1,
      relativeBudgetWordLaw_singleton,ite_eq_left hb,rawTupleWordLaw_singleton,rawTupleWordLaw_singleton]
    have he (j : Fin k) : rawWordLaw (realPosition (step e)) (H+1) ω (x j) {tupleAppendUpward e w j} =
        rawWordLaw (realPosition (step e)) H ω (x j) {w j} *
          ((ω (wordPath (x j) (w j) (w j).length)).1 e : ℝ≥0∞) := rawWordLaw_upward_atom e H ω (x j) (u j)
    simp_rw [he]
    rw [Finset.prod_mul_distrib,mul_comm]
    apply mul_le_mul_right
    calc
      (κ : ℝ≥0∞)^k = ∏ _j : Fin k, (κ : ℝ≥0∞) := by simp
      _ ≤ _ := Finset.prod_le_prod fun j _ => ENNReal.coe_le_coe.mpr (hκ _)

lemma relativeBudgetMassENN_upward {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (H : ℕ) (r : ℝ) (ω : Environment d) (π : Measure (Fin k → Lattice d))
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞)^k * relativeBudgetMassENN e f H r π ω ≤
      relativeBudgetMassENN e f (H+1) r π ω := by
  rw [relativeBudgetMassENN,← lintegral_const_mul _ (measurable_of_countable _)]
  apply lintegral_mono
  intro x
  have ht := relativeBudgetWordLaw_upward e f hef H r ω x κ hκ Set.univ
  simpa only [Measure.smul_apply,smul_eq_mul,Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
    Set.preimage_univ] using ht

end DirectionalTransience

end

end OAI
