import OAI.Combinatorics.PlanarL1.Persistence

namespace OAI


section

namespace PlanarL1.Parameters
noncomputable def successGain : ℝ := min Columns.Model.VertexTests.cutoffGain
  (min (kappaA*j/4) (min (kappaA*EA) (min (kappaB*R/50) (kappaB*lambda*R/50))))
lemma successGain_pos : 0 < successGain := by
  unfold successGain
  refine lt_min Columns.Model.VertexTests.cutoffGain_pos ?_
  norm_num [kappaA,a₁,j,EA,epsilon,kappaB,a₂,R,lambda]
lemma successGain_cutoff : successGain≤Columns.Model.VertexTests.cutoffGain := min_le_left _ _
lemma successGain_certificate : successGain≤kappaA*j/4 :=
  (min_le_right _ _).trans (min_le_left _ _)
lemma successGain_main : successGain≤kappaA*EA :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
lemma successGain_secondary : successGain≤kappaB*R/50 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
lemma successGain_increment : successGain≤kappaB*lambda*R/50 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
noncomputable def successChance : ℝ := secondaryChance/16
lemma successChance_pos : 0 < successChance := div_pos secondaryChance_pos (by norm_num)
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.CoupledState
open MeasureTheory Parameters SecondaryGeometry VertexBands VertexTests
open scoped NNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable [SFinite μ] [SFinite ν] [Fintype V]
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
variable (ht : 1≤t) (hgap : 10≤(R/200)*t)
variable (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {x y : V} {b : ℝ}

omit [SFinite μ] [SFinite ν] [Fintype V] in
lemma unchanged_success (h : S.Successful v b x y) :
    (S.unchanged ht).Successful v b x y :=
  Successful.lift (S.weaken ht) v h

lemma modes_unchanged (h : S.Successful v b x y) :
    1/4≤(S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v b x y) := by
  have hh := Execution.choose4_lower (S.branches ht hgap v hv phaseD hm p phaseG)
    (fun z => z.Successful v b x y) 0
  change (Execution.pure (S.unchanged ht)).prob (fun z => z.Successful v b x y)/4≤_ at hh
  rw [Execution.prob_pure_of (S.unchanged ht) (fun z => z.Successful v b x y) (S.unchanged_success ht v h)] at hh
  exact hh

lemma modes_main :
    FiniteRandom.prob (fun omega : MainFamily.Sample phaseD m =>
      b≤(MainFamily.batch A S.left phaseD hm omega).sets.separation
        (v x).column (v x).height (v y).column (v y).height)/4≤
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v b x y) := by
  have hh := Execution.choose4_lower (S.branches ht hgap v hv phaseD hm p phaseG)
    (fun z => z.Successful v b x y) 1
  change (Execution.uniform.bind (fun omega => .pure (S.main ht phaseD hm omega))).prob
    (fun z => z.Successful v b x y)/4≤_ at hh
  rw [Execution.prob_bind_pure,Execution.prob_uniform] at hh
  exact (div_le_div_of_nonneg_right (FiniteRandom.prob_mono (fun _ h => Or.inl h)) (by norm_num)).trans hh

lemma modes_secondary :
    FiniteRandom.prob (fun omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m =>
      b≤(SecondaryGeometry.layer (S.groups v hv phaseD p phaseG) hm omega).sets.separation
        (v x).column (v x).height (v y).column (v y).height)/4≤
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v b x y) := by
  have hh := Execution.choose4_lower (S.branches ht hgap v hv phaseD hm p phaseG)
    (fun z => z.Successful v b x y) 2
  change (Execution.uniform.bind (fun omega => .pure (S.secondary ht v hv phaseD hm p phaseG omega))).prob
    (fun z => z.Successful v b x y)/4≤_ at hh
  rw [Execution.prob_bind_pure,Execution.prob_uniform] at hh
  exact (div_le_div_of_nonneg_right (FiniteRandom.prob_mono (fun _ h => Or.inr (Or.inl h))) (by norm_num)).trans hh

lemma modes_increment :
    FiniteRandom.prob (fun sign : Fin (S.right.count+1) → Bool =>
      b≤(IncrementStep.update A S.right S.histories.history (S.cross hgap) S.histories.recorded sign).sets.separation
        (v x).column (v x).height (v y).column (v y).height)/4≤
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v b x y) := by
  have hh := Execution.choose4_lower (S.branches ht hgap v hv phaseD hm p phaseG)
    (fun z => z.Successful v b x y) 3
  change (Execution.uniform.bind (fun sign => .pure (S.increment ht hgap sign))).prob
    (fun z => z.Successful v b x y)/4≤_ at hh
  rw [Execution.prob_bind_pure,Execution.prob_uniform] at hh
  apply (div_le_div_of_nonneg_right (FiniteRandom.prob_mono ?_) (by norm_num)).trans hh
  intro sign hs
  apply Or.inr ∘ Or.inl
  change b≤(IncrementStep.update A S.right S.histories.history (S.cross hgap) S.histories.recorded sign).sets.lift.separation _ _ _ _
  simpa only [SetSystem.lift_separation] using hs

end PlanarL1.Columns.Model.CoupledState

end



section

namespace PlanarL1.Columns.Model.CoupledState
open MeasureTheory Parameters SecondaryGeometry VertexBands VertexTests PairGeometry
open scoped NNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable [SFinite μ] [SFinite ν] [Fintype V]
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
variable (ht : 1≤t) (hgap : 10≤(R/200)*t)
variable (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {x y : V}
variable (he : Eligible A S.left S.right v x y)
variable (hi : Interior A v (hv := hv) q p phaseD phaseG x)
variable (hj : Interior A v (hv := hv) q p phaseD phaseG y)
variable (hc : Cutoffs A S.left S.right v x y)
variable (ha : 1≤dist (v x) (v y)) (hd : dist (v x) (v y)<2)

include he hi hj hc ha hd in
lemma interior_success : secondaryChance/4≤
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v successGain x y) := by
  have hmain (h : 1/4≤FiniteRandom.prob (fun omega : MainFamily.Sample phaseD m =>
      kappaA*EA < (MainFamily.batch A S.left phaseD hm omega).sets.separation
        (v x).column (v x).height (v y).column (v y).height)) : secondaryChance/4≤
        (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => z.Successful v successGain x y) := by
    have hp := (secondaryChance_le_quarter.trans h).trans
      (FiniteRandom.prob_mono (fun _ h => successGain_main.trans h.le))
    exact (div_le_div_of_nonneg_right hp (by norm_num)).trans
      (S.modes_main ht hgap v hv phaseD hm p phaseG)
  by_cases hx : Nonempty ((S.left.chart (indexA A S.left v x)).comparison.BandDescent
      (BandTrees.band broad (lower A v L U hv q x))
      ((position A S.left S.right v hv he hi).point.widen (position A S.left S.right v hv he hi).subA) epsilon)
  swap
  · exact hmain (PairGeometry.no_descent_probability A S.left S.right v hv he hi hj hc ha hm hx)
  let he' := he.symm A S.left S.right v
  have hd' : dist (v y) (v x)<2 := by simpa only [dist_comm] using hd
  by_cases hy : Nonempty ((S.left.chart (indexA A S.left v y)).comparison.BandDescent
      (BandTrees.band broad (lower A v L U hv q y))
      ((position A S.left S.right v hv he' hj).point.widen (position A S.left S.right v hv he' hj).subA) epsilon)
  swap
  · have hh := PairGeometry.no_descent_probability A S.left S.right v hv he' hj hi
      (hc.symm A S.left S.right v) (by simpa only [dist_comm] using ha) hm hy
    exact hmain (hh.trans (FiniteRandom.prob_mono (fun _ h => by
      simpa only [SetSystem.separation_comm] using h)))
  have hyp : Nonempty ((S.left.chart (indexA A S.left v x)).comparison.BandDescent
      (BandTrees.band broad (lower A v L U hv q x)) (partner A S.left S.right v hv he hi hd) epsilon) := by
    apply OrdinaryData.descent_coordinates (congrArg S.left.chart (he.namesA A S.left S.right v))
      (congrArg (BandTrees.band broad) (broad_lower_eq A S.left S.right v hv hi hc)) _ _ hy
    · exact (partner_column A S.left S.right v hv he hi hd).symm
    · exact (partner_height A S.left S.right v hv he hi hd).symm
  by_cases hl : (S.left.chart (indexA A S.left v x)).comparison.NoLowCircular
      ((position A S.left S.right v hv he hi).point.widen (position A S.left S.right v hv he hi).subA)
      (partner A S.left S.right v hv he hi hd) (BandTrees.band narrow (narrowLower A v p x)) j
  swap
  · have hh := certificate_of_excluded A S.left S.right v hv he hi hc hd hl
    have hp := S.modes_unchanged ht hgap v hv phaseD hm p phaseG
      (Or.inr (Or.inr (hh.mono successGain_certificate)))
    exact (by linarith [secondaryChance_le_quarter] : secondaryChance/4≤1/4).trans hp
  have hr : Retained A S.left S.right v hv he hi hd := ⟨hx,hyp,hl⟩
  rcases retained_alternative A S.left S.right v hv he hi hj hc ha hd
      S.histories.history (S.cross hgap) S.histories.recorded hm hr with hsec|hinc
  · have hp := hsec.trans (FiniteRandom.prob_mono (fun _ h => successGain_secondary.trans h.le))
    exact (div_le_div_of_nonneg_right hp (by norm_num)).trans
      (S.modes_secondary ht hgap v hv phaseD hm p phaseG)
  · have hp := ((by linarith [secondaryChance_le_quarter] : secondaryChance≤1/2).trans hinc).trans
      (FiniteRandom.prob_mono (fun _ h => successGain_increment.trans h))
    exact (div_le_div_of_nonneg_right hp (by norm_num)).trans
      (S.modes_increment ht hgap v hv phaseD hm p phaseG)

include he ha hd in
/-- Quantitative success of the actual coupled four-mode step. All randomness
and surviving groups are sampled by the construction itself. -/
lemma step_success (hmany : 10000 ≤ m) : successChance≤
    (S.step ht hgap v hv hm).prob (fun z => z.Successful v successGain x y) := by
  rw [step,Execution.prob_bind]
  by_cases hc : Cutoffs A S.left S.right v x y
  · let E := geometricExecution m L U M
    let P := fun c : Choices m L U M => InteriorAt A v hv c x ∧ InteriorAt A v hv c y
    let f := fun c : Choices m L U M =>
      (S.modes ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2)).prob
        (fun z => z.Successful v successGain x y)
    have hp : 1/4≤E.prob P := interior_pair_probability A v hv m hmany x y
      (by simpa only [abs_sub_comm] using hc.1.le)
    have hg : secondaryChance/4*E.prob P≤E.mean f := E.mean_lower_of_event
      (fun c => Execution.prob_nonneg _ _) (fun c h =>
        S.interior_success ht hgap v hv _ hm _ _ he h.1 h.2 hc ha hd)
    change successChance≤E.mean f
    apply le_trans _ hg
    dsimp only [successChance]
    have hs := mul_le_mul_of_nonneg_left hp (div_nonneg secondaryChance_pos.le (by norm_num : (0:ℝ)≤4))
    linarith
  · have hs : S.Successful v successGain x y := by
      rcases separation_of_cutoff_failure A S.left S.right v he hc with h|h
      · exact Or.inl (successGain_cutoff.trans h)
      · exact Or.inr (Or.inl (successGain_cutoff.trans h))
    have hl : successChance≤1/4 := by
      unfold successChance
      linarith [secondaryChance_le_quarter]
    have hh := (geometricExecution m L U M).mean_mono (f := fun _ => (1:ℝ)/4)
      (fun c => S.modes_unchanged ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2) hs)
    rw [Execution.mean_const] at hh
    exact hl.trans hh
end PlanarL1.Columns.Model.CoupledState

end

end OAI
