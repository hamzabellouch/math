import Mathlib
import OAI.Probability.Ballisticity.Coupling.StageSeedProfile
import OAI.Probability.Ballisticity.Estimates.RetainedComposition

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def cellSeedMass {d k : ℕ} (e f : Direction d) (a G : ℝ) (Hs : ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (ω : Environment d) : ℝ≥0∞ :=
  seedSeparatedRaw e f Hs G (π ω).val ω Set.univ

noncomputable def cellEarlyMass {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (Hs He : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (ω : Environment d) : ℝ :=
  relativeBudgetMass e f He (G/4) (seedSeparatedProfile e f hef a G Hs (π ω) ω).val ω

noncomputable def cellEarlyProfile {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (hG : 0 ≤ G) (Hs He : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (ω : Environment d) : BudgetProfile (k:=k) e f (a+Hs+He) (3*G/4) := by
  let q := nextBudgetProfile e f He (a+Hs) G (G/4) (by positivity)
    (seedSeparatedProfile e f hef a G Hs (π ω) ω) ω
  refine ⟨q.val,q.property.1,?_⟩
  have hg : G-G/4=3*G/4 := by ring
  simpa only [hg] using q.property.2

lemma cellSeedMass_measurable {d k : ℕ} (e f : Direction d) (a G : ℝ) (Hs : ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+Hs))) _
      (cellSeedMass e f a G Hs π) := by
  have hle : rowSigma (BelowHeight (realPosition (step e)) a)  ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+Hs)) :=
    rowSigma_mono (fun x hx => by
      change dot (realPosition x) (realPosition (step e)) < _ at *
      exact lt_of_lt_of_le hx (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  let : MeasurableSpace (Environment d) :=
    rowSigma (BelowHeight (realPosition (step e)) (a+Hs))
  unfold cellSeedMass
  apply (Measure.measurable_coe MeasurableSet.univ).comp
  apply (seedSeparatedRaw_joint_rows e f Hs G a _ ?_).comp
    ((hπ.mono hle le_rfl).prodMk measurable_id)
  intro x hx j y hy
  change dot (realPosition y) (realPosition (step e))<a+Hs
  simpa only [hx j] using hy.2

lemma cellEarlyMass_measurable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (Hs He : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))) _
      (cellEarlyMass e f hef a G Hs He π) := by
  have hle : rowSigma (BelowHeight (realPosition (step e)) (a+Hs))  ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He)) :=
    rowSigma_mono (fun x hx => by
      change dot (realPosition x) (realPosition (step e)) < _ at *
      exact lt_of_lt_of_le hx (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  let : MeasurableSpace (Environment d) :=
    rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))
  have hm := seedSeparatedProfile_measurable e f hef a G Hs π hπ
  exact (budgetProfileMass_joint_rows e f (a+Hs) G He (G/4) _ (by
    intro x hx j y hy
    change dot (realPosition y) (realPosition (step e))<a+Hs+He
    simpa only [hx j] using hy.2)).comp ((hm.mono hle le_rfl).prodMk measurable_id)

lemma cellEarlyProfile_measurable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (hG : 0 ≤ G) (Hs He : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))) _
      (cellEarlyProfile e f hef a G hG Hs He π) := by
  let : MeasurableSpace (Environment d) :=
    rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))
  have hm := nextBudgetProfile_measurable_below e f (a+Hs) G (G/4) (by positivity) He
    (fun ω => seedSeparatedProfile e f hef a G Hs (π ω) ω)
    (seedSeparatedProfile_measurable e f hef a G Hs π hπ)
  exact (measurable_subtype_coe.comp hm).subtype_mk

lemma cellEarlyProfile_retained {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (hG : 0 ≤ G) (Hs He : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (ω : Environment d) :
    (cellSeedMass e f a G Hs π ω * ENNReal.ofReal (cellEarlyMass e f hef a G Hs He π ω)) •
      (cellEarlyProfile e f hef a G hG Hs He π ω).val  ≤
        rawTupleMixture (realPosition (step e)) (Hs+He) (π ω).val ω := by
  let p := seedSeparatedProfile e f hef a G Hs (π ω) ω
  have hp : cellSeedMass e f a G Hs π ω • p.val=seedSeparatedRaw e f Hs G (π ω).val ω :=
    seedSeparatedProfile_mass e f hef a G Hs (π ω) ω
  have hq : ENNReal.ofReal (cellEarlyMass e f hef a G Hs He π ω) •
      (cellEarlyProfile e f hef a G hG Hs He π ω).val =
      budgetEndpointMixture e f He (G/4) p.val ω := by
    change ENNReal.ofReal (relativeBudgetMass e f He (G/4) p.val ω) •
      (nextBudgetProfile e f He (a+Hs) G (G/4) (by positivity) p ω).val = _
    rw [←relativeBudgetMassENN_toReal, ENNReal.ofReal_toReal (lt_of_le_of_lt
      (relativeBudgetMassENN_le_one e f He (G/4) p.val ω) ENNReal.one_lt_top).ne]
    exact nextBudgetProfile_mass e f He (a+Hs) G (G/4) (by positivity) p ω
  rw [mul_smul,hq]
  calc
    _  ≤  cellSeedMass e f a G Hs π ω • rawTupleMixture (realPosition (step e)) He p.val ω := by
      exact smul_le_smul_left _ (budgetEndpointMixture_le_raw e f He (G/4) p.val ω)
    _ = rawTupleMixture (realPosition (step e)) He
        (cellSeedMass e f a G Hs π ω • p.val) ω := (rawTupleMixture_smul _ _ _ _ _).symm
    _  ≤  rawTupleMixture (realPosition (step e)) He
        (rawTupleMixture (realPosition (step e)) Hs (π ω).val ω) ω := by
      rw [hp]
      exact rawTupleMixture_mono _ _ _ Measure.restrict_le_self
    _  ≤  _ := rawTupleMixture_comp_le e Hs He (π ω).val ω

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def failedOpportunityBlocks {Ω : Type*} (F : ℕ → ℕ → Set Ω) (i : ℕ) : List ℕ → Set Ω
  | [] => Set.univ
  | n::ns => F i n ∩ failedOpportunityBlocks F (i+n) ns

lemma failedOpportunityBlocks_bound {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (F : ℕ → ℕ → Set Ω)
    (hFm : ∀ i n, 0<n → MeasurableSet[ℱ (i+n)] (F i n)) (c : ℝ≥0∞)
    (hfresh : ∀ i n, 0<n → ∀ A : Set Ω, MeasurableSet[ℱ i] A →
      μ (A∩F i n)≤c^n*μ A) (ns : List ℕ) (hpos : ∀ n∈ns, 0<n)
    (i : ℕ) (A : Set Ω) (hA : MeasurableSet[ℱ i] A) :
    μ (A∩failedOpportunityBlocks F i ns)≤c^ns.sum*μ A := by
  induction ns generalizing i A with
  | nil => simp [failedOpportunityBlocks]
  | cons n ns ih =>
    have hn : 0<n := hpos n (by simp)
    have hAn : MeasurableSet[ℱ (i+n)] (A∩F i n) :=
      (ℱ.mono (Nat.le_add_right i n) A hA).inter (hFm i n hn)
    have hi := ih (fun k hk => hpos k (by simp [hk])) (i+n) (A∩F i n) hAn
    rw [failedOpportunityBlocks,← Set.inter_assoc]
    apply hi.trans
    calc
      c^ns.sum*μ (A∩F i n) ≤ c^ns.sum*(c^n*μ A) := by gcongr; exact hfresh i n hn A hA
      _ = c^(n::ns).sum*μ A := by simp [pow_add]; ring

theorem opportunity_exhaustion_probability {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (F : ℕ → ℕ → Set Ω)
    (hFm : ∀ i n, 0<n → MeasurableSet[ℱ (i+n)] (F i n)) (c : ℝ≥0∞)
    (hfresh : ∀ i n, 0<n → ∀ A : Set Ω, MeasurableSet[ℱ i] A →
      μ (A∩F i n)≤c^n*μ A) (m : ℕ) :
    μ (⋃ p : Composition m, failedOpportunityBlocks F 0 p.blocks)≤
      (2:ℝ≥0∞)^(m-1)*c^m := by
  apply (measure_iUnion_le _).trans
  calc
    (∑' p : Composition m, μ (failedOpportunityBlocks F 0 p.blocks)) ≤
        ∑' _p : Composition m, c^m := by
      apply ENNReal.tsum_le_tsum
      intro p
      have hh := failedOpportunityBlocks_bound μ ℱ F hFm c hfresh p.blocks
        (fun n hn => p.blocks_pos hn) 0 Set.univ MeasurableSet.univ
      simpa using hh
    _ = (2:ℝ≥0∞)^(m-1)*c^m := by
      rw [tsum_fintype]
      simp [composition_card,nsmul_eq_mul]

end DirectionalTransience

end

end OAI
