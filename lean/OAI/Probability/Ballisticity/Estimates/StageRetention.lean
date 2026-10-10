import Mathlib
import OAI.Probability.Ballisticity.Estimates.StoppedSplice
import OAI.Probability.Ballisticity.Coupling.StageSeedProfile
import OAI.Probability.Ballisticity.Estimates.RetainedComposition

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma stageStop_pos {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ)
    (hH : 0<H) (hR : 0<R) (ω : Environment d) :
    0<stageStop e f a Gminus Gplus B π H R ω := by
  change 1 ≤ stageStop e f a Gminus Gplus B π H R ω
  exact le_hittingBtwn (n:=1) (le_min hH hR) ω

lemma stageStop_le {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (ω : Environment d) :
    stageStop e f a Gminus Gplus B π H R ω  ≤  min H R := hittingBtwn_le ω

lemma stageStop_traversal_lower {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ)
    (hH : 0<H) (hR : 0<R) (hB : 0 ≤ B) (ω : Environment d)
    (hπ : ∀ᵐ x ∂(π ω).val,TupleSeparated f Gminus x)
    (κ : ℝ≥0) (hκ : ∀ y,κ ≤ (ω y).val e) :
    (κ : ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-B))  ≤
      stageEndpointMass e f a Gminus π (stageStop e f a Gminus Gplus B π H R ω) ω := by
  let n := stageStop e f a Gminus Gplus B π H R ω
  have hn : 0<n := stageStop_pos e f a Gminus Gplus B π H R hH hR ω
  have hp : ENNReal.ofReal (Real.exp (-B))  ≤  stageEndpointMass e f a Gminus π (n-1) ω := by
    by_cases hz : n-1=0
    · rw [hz,stageEndpointMass,rawTupleMixture_zero]
      have hfull : (π ω).val {x | TupleSeparated f Gminus x}=1 := by
        calc
          _ = (π ω).val Set.univ := by
            apply measure_congr
            filter_upwards [hπ] with x hx
            apply propext
            exact iff_true_intro hx
          _ = 1 := measure_univ
      rw [hfull]
      exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hB))
    · exact before_stageStop_pass e f a Gminus Gplus B π H R ω (Nat.pos_of_ne_zero hz) (by dsimp [n]; omega)
  have hu := stage_separated_mass_upward e f (n-1) Gminus (π ω).val ω κ hκ
  have he : n-1+1=n := by omega
  rw [he] at hu
  exact (mul_le_mul_right hp _).trans hu

noncomputable def stageRetainedGap {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (ω : Environment d) : ℝ :=
  let h := stageStop e f a Gminus Gplus B π H R ω
  if h=H ∧ ENNReal.ofReal (Real.exp (-B))  ≤  stageTestMass e f a Gminus Gplus π H h ω
  then Gplus else Gminus

noncomputable def stageOutput {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a Gminus Gplus B : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (H R : ℕ) (ω : Environment d) :
    BudgetProfile (k:=k) e f (a+stageStop e f a Gminus Gplus B π H R ω)
      (stageRetainedGap e f a Gminus Gplus B π H R ω) :=
  seedSeparatedProfile e f hef a (stageRetainedGap e f a Gminus Gplus B π H R ω)
    (stageStop e f a Gminus Gplus B π H R ω) (π ω) ω

noncomputable def stageRetainedMass {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (ω : Environment d) : ℝ≥0∞ :=
  stageEndpointMass e f a (stageRetainedGap e f a Gminus Gplus B π H R ω) π
    (stageStop e f a Gminus Gplus B π H R ω) ω

lemma stageOutput_retained_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a Gminus Gplus B : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (H R : ℕ) (ω : Environment d) :
    stageRetainedMass e f a Gminus Gplus B π H R ω •
      (stageOutput e f hef a Gminus Gplus B π H R ω).val  ≤
      rawTupleMixture (realPosition (step e)) (stageStop e f a Gminus Gplus B π H R ω) (π ω).val ω := by
  unfold stageRetainedMass stageEndpointMass stageOutput
  rw [←seedSeparatedRaw_univ,seedSeparatedProfile_mass]
  exact Measure.restrict_le_self

lemma stageRetainedMass_lower {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ)
    (hH : 0<H) (hR : 0<R) (hB : 0 ≤ B) (ω : Environment d)
    (hπ : ∀ᵐ x ∂(π ω).val,TupleSeparated f Gminus x)
    (κ : ℝ≥0) (hκ : ∀ y,κ ≤ (ω y).val e) :
    (κ : ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-B))  ≤
      stageRetainedMass e f a Gminus Gplus B π H R ω := by
  unfold stageRetainedMass stageRetainedGap
  dsimp only
  split
  · rename_i hpass
    have hp := (stage_pass_retains e f a Gminus Gplus B π H _ ω
      (stageStop_pos e f a Gminus Gplus B π H R hH hR ω) hpass.2).2 hpass.1
    have hk1 : (κ : ℝ≥0∞) ≤ 1 := (ENNReal.coe_le_coe.mpr (hκ 0)).trans (by exact_mod_cast row_entry_le_one (ω 0) e)
    exact (mul_le_of_le_one_left' (pow_le_one' hk1 _)).trans hp
  · exact stageStop_traversal_lower e f a Gminus Gplus B π H R hH hR hB ω hπ κ hκ

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def stageOutputAt {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a Gminus Gplus B : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (H h : ℕ) (ω : Environment d) : Measure (Fin k → Lattice d) :=
  if h=H ∧ ENNReal.ofReal (Real.exp (-B)) ≤ stageTestMass e f a Gminus Gplus π H h ω
  then (seedSeparatedProfile e f hef a Gplus h (π ω) ω).val
  else (seedSeparatedProfile e f hef a Gminus h (π ω) ω).val

lemma stageOutputAt_adapted {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a Gminus Gplus B : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H h : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+h))) _
      (stageOutputAt e f hef a Gminus Gplus B π H h) := by
  have hs := (stageTestMass_adapted e f a Gminus Gplus π hπ H) h
  have hp := measurable_subtype_coe.comp (seedSeparatedProfile_measurable e f hef a Gplus h π hπ)
  have hm := measurable_subtype_coe.comp (seedSeparatedProfile_measurable e f hef a Gminus h π hπ)
  exact hp.ite ((MeasurableSet.const (h=H)).inter (measurableSet_le measurable_const hs)) hm

lemma stageOutput_eq_at {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a Gminus Gplus B : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (H R : ℕ) (ω : Environment d) :
    (stageOutput e f hef a Gminus Gplus B π H R ω).val=
      stageOutputAt e f hef a Gminus Gplus B π H (stageStop e f a Gminus Gplus B π H R ω) ω := by
  unfold stageOutput stageRetainedGap stageOutputAt
  dsimp only
  split
  · rename_i h
    exact congrArg (fun G => (seedSeparatedProfile e f hef a G
      (stageStop e f a Gminus Gplus B π H R ω) (π ω) ω).val) (ite_eq_left h)
  · rename_i h
    exact congrArg (fun G => (seedSeparatedProfile e f hef a G
      (stageStop e f a Gminus Gplus B π H R ω) (π ω) ω).val) (ite_eq_right h)

lemma stageStop_event {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H R h : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+h))]
      {ω | stageStop e f a Gminus Gplus B π H R ω=h} := by
  have ht := (stageStop_stopping e f a Gminus Gplus B π hπ H R).measurableSet_eq_of_countable h
  change MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+h))] _ at ht
  simpa only [WithTop.coe_inj, Nat.cast_withTop] using ht

lemma stageOutput_stopped_rows {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a Gminus Gplus B : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H R : ℕ) (U : Set (Measure (Fin k → Lattice d))) (hU : MeasurableSet U) :
    StoppedRowsEvent (fun h => BelowHeight (realPosition (step e)) (a+h))
      (stageStop e f a Gminus Gplus B π H R)
      {ω | (stageOutput e f hef a Gminus Gplus B π H R ω).val ∈ U} := by
  intro h
  have he : {ω | (stageOutput e f hef a Gminus Gplus B π H R ω).val ∈ U} ∩
      {ω | stageStop e f a Gminus Gplus B π H R ω=h} =
      (stageOutputAt e f hef a Gminus Gplus B π H h ⁻¹' U) ∩
      {ω | stageStop e f a Gminus Gplus B π H R ω=h} := by
    ext ω
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_preimage]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> refine ⟨?_,h₂⟩
    · rwa [stageOutput_eq_at,h₂] at h₁
    · rwa [stageOutput_eq_at,h₂]
  rw [he]
  exact ((stageOutputAt_adapted e f hef a Gminus Gplus B π hπ H h) hU).inter
    (stageStop_event e f a Gminus Gplus B π hπ H R h)

end DirectionalTransience

end

end OAI
