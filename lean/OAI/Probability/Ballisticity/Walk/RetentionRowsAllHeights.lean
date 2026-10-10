import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPair

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma retainedPairLaw_zero {d : ℕ} (ℓ : Vector d) (f : Direction d) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    retainedPairLaw ℓ f 0 z π ω = π.restrict {y | z ≤ signedCoordinate f (y.2-y.1)} := by
  simp only [retainedPairLaw,rawPairMixture_zero]

lemma retainedPairLaw_joint_rows_all {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (C : Set (Lattice d × Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) (Measure (Lattice d × Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => retainedPairLaw ℓ f H z p.1.val p.2) := by
  by_cases hH : H=0
  · subst H
    simp only [retainedPairLaw_zero]
    let : MeasurableSpace (Environment d) := rowSigma S
    apply Measure.measurable_of_measurable_coe
    intro U hU
    simp only [Measure.restrict_apply hU]
    exact (Measure.measurable_coe (hU.inter (Set.to_countable _).measurableSet)).comp
      (measurable_subtype_coe.comp measurable_fst)
  · exact retainedPairLaw_joint_rows ℓ f (Nat.pos_of_ne_zero hH) z C S hC

lemma upwardRetainedLaw_joint_rows {d : ℕ} (e f : Direction d)
    (H : ℕ) (z : ℝ) (κ : ℝ≥0) (C : Set (Lattice d × Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip (realPosition (step e)) x.1 H ⊆ S ∧
      Strip (realPosition (step e)) x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) (Measure (Lattice d × Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => upwardRetainedLaw e f H z p.1.val p.2 κ) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have hm := (Measure.measurable_map (pairUp e) (measurable_of_countable _)).comp
    (retainedPairLaw_joint_rows_all (realPosition (step e)) f H z C S hC)
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [upwardRetainedLaw,Measure.smul_apply,smul_eq_mul]
  exact measurable_const.mul ((Measure.measurable_coe hU).comp hm)

lemma strip_subset_below_height {d : ℕ} (ℓ : Vector d) (a : ℝ)
    (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight ℓ a)
    {h k : ℕ} (hhk : h ≤ k) :
    Strip ℓ x.1 h ⊆ BelowHeight ℓ (a+k) ∧ Strip ℓ x.2 h ⊆ BelowHeight ℓ (a+k) := by
  have hhkR : (h:ℝ) ≤ k := by exact_mod_cast hhk
  constructor
  · intro y hy
    change dot (realPosition y) ℓ < a+k
    have ht := hy.2
    rw [hx.1] at ht
    linarith
  · intro y hy
    change dot (realPosition y) ℓ < a+k
    have ht := hy.2
    rw [hx.2] at ht
    linarith

lemma rowSigma_below_height_mono {d : ℕ} (ℓ : Vector d) (a : ℝ) (k : ℕ) :
    rowSigma (BelowHeight ℓ a) ≤ rowSigma (BelowHeight ℓ (a+k)) := by
  apply rowSigma_mono
  intro y hy
  dsimp [BelowHeight] at hy ⊢
  have : (0:ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma retainedPairLaw_at_height_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (a z : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight ℓ a)) _ π)
    {h k : ℕ} (hhk : h ≤ k) :
    @Measurable _ _ (rowSigma (BelowHeight ℓ (a+k))) _
      (fun ω => retainedPairLaw ℓ f h z (π ω).val ω) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight ℓ (a+k))
  have hp : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+k))) _ π :=
    hπ.mono (rowSigma_below_height_mono ℓ a k) le_rfl
  have hm := (retainedPairLaw_joint_rows_all ℓ f h z (PairAtHeight ℓ a) (BelowHeight ℓ (a+k))
    (fun x hx => strip_subset_below_height ℓ a x hx hhk)).comp (hp.prodMk measurable_id)
  exact hm

lemma upwardRetainedLaw_at_height_rows {d : ℕ} (e f : Direction d)
    (a z : ℝ) (κ : ℝ≥0) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {h k : ℕ} (hhk : h ≤ k) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _
      (fun ω => upwardRetainedLaw e f h z (π ω).val ω κ) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) (a+k))
  have hp : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _ π :=
    hπ.mono (rowSigma_below_height_mono (realPosition (step e)) a k) le_rfl
  have hm := (upwardRetainedLaw_joint_rows e f h z κ (PairAtHeight (realPosition (step e)) a)
    (BelowHeight (realPosition (step e)) (a+k))
    (fun x hx => strip_subset_below_height (realPosition (step e)) a x hx hhk)).comp
      (hp.prodMk measurable_id)
  exact hm
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferFirstFailure_eq_measurable {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (a z g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight ℓ a)) _ π) (H k : ℕ) :
    MeasurableSet[rowSigma (BelowHeight ℓ (a+k))] {ω | bufferFirstFailure ℓ f a z g π H ω = k} := by
  have hm := (bufferFirstFailure_stopping ℓ f a z g π hπ H).measurableSet_eq_of_countable k
  have heq : {ω | bufferFirstFailure ℓ f a z g π H ω = k} =
      {ω | (bufferFirstFailure ℓ f a z g π H ω : WithTop ℕ) = (k : WithTop ℕ)} := by
    ext ω
    change _ = _ ↔ _ = _
    norm_cast
  rw [heq]
  exact hm

lemma bufferStageRetainedLaw_at_stop_lt {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0) {k : ℕ} (hkH : k < H)
    (hk : bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k) :
    bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ =
      upwardRetainedLaw e f (k-1) (z₀+(1-ε)*r) (π ω).val ω κ := by
  have hf := bufferFirstFailure_fails_of_lt (realPosition (step e)) f a (z₀+(1-ε)*r) g π hH ω
    (by simpa only [hk] using hkH)
  rw [hk] at hf
  simp only [bufferStageRetainedLaw,hk,ite_eq_left hf]

lemma bufferStageRetainedLaw_stopped_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {H : ℕ} (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _
      (fun ω => if bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k
        then bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ else 0) := by
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  have heq := bufferFirstFailure_eq_measurable ℓ f a z g π hπ H k
  by_cases hk : k ≤ H
  · rcases lt_or_eq_of_le hk with hklt|he
    · have hf : (fun ω => if bufferFirstFailure ℓ f a z g π H ω = k
          then bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ else 0) =
        (fun ω => if bufferFirstFailure ℓ f a z g π H ω = k
          then upwardRetainedLaw e f (k-1) z (π ω).val ω κ else 0) := by
        funext ω
        by_cases hj : bufferFirstFailure ℓ f a z g π H ω = k
        · simp only [ite_eq_left hj]
          exact bufferStageRetainedLaw_at_stop_lt e f a z₀ r ε α g π hH ω κ hklt hj
        · simp only [ite_eq_right hj]
      change @Measurable _ _ (rowSigma (BelowHeight ℓ (a+k))) _ _
      rw [hf]
      exact (upwardRetainedLaw_at_height_rows e f a z κ π hπ (Nat.sub_le k 1)).ite heq measurable_const
    · subst k
      have hp : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+H))) _ π :=
        hπ.mono (rowSigma_below_height_mono ℓ a H) le_rfl
      have hmass (b : ℝ) : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+H))) _
          (fun ω => pairKernelMass ℓ f H b (π ω).val ω) := by
        have hm := (pairKernelMass_joint_rows ℓ f hH b (PairAtHeight ℓ a) (BelowHeight ℓ (a+H))
          (fun x hx => strip_subset_below_height ℓ a x hx le_rfl)).comp (hp.prodMk measurable_id)
        exact hm
      have hu := upwardRetainedLaw_at_height_rows e f a z κ π hπ (Nat.sub_le H 1)
      have hc := retainedPairLaw_at_height_rows ℓ f a z π hπ (le_refl H)
      have hg := retainedPairLaw_at_height_rows ℓ f a (z₀+(1+α)*r) π hπ (le_refl H)
      have hf : (fun ω => if bufferFirstFailure ℓ f a z g π H ω = H
          then bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ else 0) =
        (fun ω => if bufferFirstFailure ℓ f a z g π H ω = H then
          (if pairKernelMass ℓ f H z (π ω).val ω < ENNReal.ofReal g then
            upwardRetainedLaw e f (H-1) z (π ω).val ω κ
          else if ENNReal.ofReal g ≤ pairKernelMass ℓ f H (z₀+(1+α)*r) (π ω).val ω then
            retainedPairLaw ℓ f H (z₀+(1+α)*r) (π ω).val ω
          else retainedPairLaw ℓ f H z (π ω).val ω) else 0) := by
        funext ω
        by_cases hj : bufferFirstFailure ℓ f a z g π H ω = H
        · simp only [ite_eq_left hj,bufferStageRetainedLaw]
          change (if pairKernelMass ℓ f (bufferFirstFailure ℓ f a z g π H ω) z (π ω).val ω < _
            then upwardRetainedLaw e f (bufferFirstFailure ℓ f a z g π H ω-1) z (π ω).val ω κ else _) = _
          rw [hj]
        · simp only [ite_eq_right hj]
      change @Measurable _ _ (rowSigma (BelowHeight ℓ (a+H))) _ _
      rw [hf]
      exact (hu.ite (measurableSet_lt (hmass z) measurable_const)
        (hg.ite (measurableSet_le measurable_const (hmass (z₀+(1+α)*r))) hc)).ite heq measurable_const
  · have hn (ω : Environment d) : bufferFirstFailure ℓ f a z g π H ω ≠ k := by
      have := (bufferFirstFailure_bounds ℓ f a z g π hH ω).2
      omega
    convert (measurable_const : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+k))) _
      (fun _ : Environment d => (0 : Measure (Lattice d × Lattice d)))) using 1
    funext ω
    exact ite_eq_right (hn ω)
end DirectionalTransience

end

end

end OAI
