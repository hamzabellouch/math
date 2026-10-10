import OAI.Probability.DirectionalWalk.ShiftedBlocks

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def commonBandContact {d : ℕ} (e : Step d) (n : ℕ) : Set (TwoTape (Word d)) :=
  {Z | ∃ h : ℕ, commonDepth (placedWidth e) Z (4*n) < h ∧
    h ≤ commonDepth (placedWidth e) Z (8*n) ∧ contactDepth e Z h}

lemma measurableSet_commonBandContact {d : ℕ} (e : Step d) (n : ℕ) :
    MeasurableSet (commonBandContact e n) := by
  simp only [commonBandContact,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun h =>
    (measurableSet_lt (measurable_commonDepth (placedWidth e) (4*n)) measurable_const).inter
      ((measurableSet_le measurable_const (measurable_commonDepth (placedWidth e) (8*n))).inter
        (measurableSet_contactDepth e h)))

lemma commonBand_probability_le_experiment {d : ℕ} (e : Step d)
    (ν : Bool → Measure (Word d)) [∀ b, IsProbabilityMeasure (ν b)]
    (hreg : ∀ b, ∀ᵐ a ∂ν b, RegenerationWord (axisDirection (placedAxis e b)) a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H)
    (n : ℕ) [NeZero n] :
    twoTapeLaw ν (commonBandContact e n) ≤
      experimentLaw ν (placedWidth e) (fun _ => wordEnd) n (experimentContact e) := by
  have : Countable (Word d) := inferInstance
  have : Countable (TapeList (Word d)) := inferInstance
  have : Countable (ThreeLists (Word d)) := inferInstance
  have : Countable (TwoTapeList (Word d)) := inferInstance
  let L := placedWidth e
  have hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a := by
    intro b
    filter_upwards [hreg b] with a ha
    exact slabRecords_pos _ _ ha
  rw [experimentLaw_fourWindows ν L hL he,Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  apply fourWindow_ge
  intro u r s t
  rw [← consecutiveFour_law ν L hL he,Measure.map_apply
    (measurable_consecutiveFour L _ _ _ _) (Set.to_countable _).measurableSet]
  apply measure_mono_ae
  filter_upwards [ae_twoTape_prop ν _ (fun b => (Set.to_countable _).measurableSet) hreg,
    ae_common_iterates ν L hL he] with Z hZ hi
  intro hc
  obtain ⟨h,ha,hb,hc⟩ := hc
  have hm := (commonDepth_strictMono L Z hi).monotone
  apply commonBand_experiment_contact e Z hZ hi (n+u) (n+r) (7*n+s) (n+t) h
  · exact (hm (by have := u.isLt; have := r.isLt; omega)).trans_lt ha
  · exact hb.trans (hm (by omega))
  · exact hc

lemma reversed_cut_endpoint_height {d : ℕ} (e : Step d) (Z : ℕ → Word d)
    (hZ : ∀ i, RegenerationWord (axisDirection e) (Z i)) (N : ℕ)
    (hC : Z ∈ tapeCut (axisDirection e) N) :
    axisHeight e (wordEnd (concatenateList (reverseTapeList
      (cutList (slabRecords (axisDirection e)) N Z)))-stepVector e) = (N : ℤ)-1 := by
  rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,axisHeight_step_self,
    concatenateList_end,listTotal_reverse,axisHeight_listTotal e false (cutList (slabRecords (axisDirection e)) N Z) (fun i => hZ i)]
  change (listHeight (slabRecords (axisDirection e)) (cutList (slabRecords (axisDirection e)) N Z) : ℤ)+ -1 = _
  have hh : listHeight (slabRecords (axisDirection e)) (cutList (slabRecords (axisDirection e)) N Z) = N := by
    rw [cutList,listHeight_prefix]
    exact cutListIndex_spec _ _ Z (fun i => slabRecords_pos _ _ (hZ i)) hC
  rw [hh]
  rfl

lemma reversed_cut_endpoint_cube {d : ℕ} (e : Step d) (Z : ℕ → Word d)
    (hZ : ∀ i, RegenerationWord (axisDirection e) (Z i)) (N : ℕ)
    (hC : Z ∈ tapeCut (axisDirection e) N)
    (hR : ∑ j ∈ Finset.range N, slabRadius (Z j) < (N : ℝ)^2) :
    ∃ q, wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) -
      stepVector e = axisCubeEnumeration e N (N^2+1) q := by
  have hbd (i : Fin d) : |(wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z)))-stepVector e) i| ≤ ((N^2+1 : ℕ) : ℤ) := by
    have hh := (reversed_cut_endpoint_radius e Z hZ N hC i).trans hR.le
    have hv : |((stepVector e i : ℤ) : ℝ)| ≤ 1 := by
      dsimp [stepVector]
      split_ifs <;> norm_num
    have habs : |((wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) i : ℝ)) - (stepVector e i : ℝ)| ≤ |((wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) i : ℝ))| + |(stepVector e i : ℝ)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le ((wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) i : ℝ)) (-(stepVector e i : ℝ))
    have ht := habs.trans (add_le_add hh hv)
    exact_mod_cast ht
  obtain ⟨q,hq⟩ := axisCubeEnumeration_surjective e N (N^2+1)
    (wordEnd (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z)))-stepVector e)
    (reversed_cut_endpoint_height e Z hZ N hC) hbd
  exact ⟨q,hq.symm⟩

lemma coveredDepthBand_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (s N low high m : ℕ) (hs : 0 < s) (hsN : s ≤ N) (hls : low ≤ s) (hsh : s < high)
    (hΔ : axisReachProb μ e (s-low)-axisReachProb μ e s ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    (annealed μ 0 (nonBacktracking (axisDirection e)))^2 ≤
      twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) (coveredDepthBand e low high) +
      (∫⁻ a, ENNReal.ofReal (slabRadius a) ∂slabLaw μ (axisDirection e)) / (N : ℝ≥0∞) +
      (annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (Fintype.card (AxisCubeSite e N (N^2+1))+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  let := slabLaw_probability μ (axisDirection e) (hp false)
  let := conditioned_probability μ (axisDirection (oppositeStep e)) (hp true)
  have hN : 0 < N := lt_of_lt_of_le hs hsN
  have : Nonempty (AxisCubeSite e N (N^2+1)) := axisCubeSite_nonempty e N (N^2+1) hN (by nlinarith)
  have : NeZero (Fintype.card (AxisCubeSite e N (N^2+1))) := ⟨Fintype.card_ne_zero⟩
  let A := Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
  let B := conditioned μ (axisDirection (oppositeStep e))
  let M := A.prod B
  let R : Set ((ℕ → Word d) × Path d) := {p | (N : ℝ)^2 ≤ ∑ j ∈ Finset.range N, slabRadius (p.1 j)}
  let C := mixedTapes e ⁻¹' coveredDepthBand e low high
  let F : Set ((ℕ → Word d) × Path d) := {p | p.1 ∈ tapeCut (axisDirection e) N ∧
    (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N p.1)),p.2) ∈
      finiteLateEndpointEvent e (N-s) (N-low) N (axisCubeEnumeration e N (N^2+1))}
  have hM : M (Prod.fst ⁻¹' (tapeCut (axisDirection e) s ∩ tapeCut (axisDirection e) N)) ≤ M C+M R+M F := by
    refine (measure_mono_ae (t := C ∪ R ∪ F) ?_).trans ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_tape_prop (slabLaw μ (axisDirection e)) (RegenerationWord (axisDirection e))
        (Set.to_countable _).measurableSet (ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero e) (hp false))),
      Measure.quasiMeasurePreserving_snd.ae
        (ae_goodSlabPath μ hell _ (axisDirection_ne_zero _) (hp true))] with p hpos hneg
    intro hcuts
    by_cases hc : p ∈ C
    · exact Or.inl (Or.inl hc)
    by_cases hr : p ∈ R
    · exact Or.inl (Or.inr hr)
    apply Or.inr
    refine ⟨hcuts.2,?_,two_cuts_uncovered_mixed e p hpos hneg s N low high hs hsN hls hsh hcuts.1 hcuts.2 hc⟩
    exact reversed_cut_endpoint_cube e p.1 hpos N hcuts.2 (lt_of_not_ge hr)
  have hC : M C = twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) (coveredDepthBand e low high) := by
    rw [← mixedTapes_law μ hell e hp,Measure.map_apply (measurable_mixedTapes e) (measurableSet_coveredDepthBand e low high)]
  have hR : M R ≤ (∫⁻ a, ENNReal.ofReal (slabRadius a) ∂slabLaw μ (axisDirection e)) / (N : ℝ≥0∞) := by
    change (A.prod B) (Prod.fst ⁻¹' {Z : ℕ → Word d | (N : ℝ)^2 ≤ ∑ j ∈ Finset.range N, slabRadius (Z j)}) ≤ _
    have hm : MeasurableSet {Z : ℕ → Word d | (N : ℝ)^2 ≤ ∑ j ∈ Finset.range N, slabRadius (Z j)} :=
      measurableSet_le measurable_const (Finset.measurable_sum _ (fun j _ =>
        (measurable_of_countable slabRadius).comp (measurable_pi_apply j)))
    rw [(measurePreserving_fst (μ := A) (ν := B)).measure_preimage hm.nullMeasurableSet]
    exact iid_radius_large _ N (lt_of_lt_of_le hs hsN)
  have hF := mixed_bridge_late_bound μ hell e (hp false) (N-s) (N-low) N m
    (by omega) (by omega) (axisCubeEnumeration e N (N^2+1))
    (axisCubeEnumeration_height e N (N^2+1)) (axisCubeEnumeration_injective e N (N^2+1))
    (by simpa only [show N-low-(N-s) = s-low by omega,show N-(N-s) = s by omega] using hΔ)
  have hcuts := axis_two_cuts_lower μ hell e (hp false) s N hsN
  have hfrom : M (Prod.fst ⁻¹' (tapeCut (axisDirection e) s ∩ tapeCut (axisDirection e) N)) =
      A (tapeCut (axisDirection e) s ∩ tapeCut (axisDirection e) N) := by
    exact measurePreserving_fst.measure_preimage ((measurableSet_tapeCut _ _).inter (measurableSet_tapeCut _ _)).nullMeasurableSet
  rw [hfrom,hC] at hM
  exact hcuts.trans (hM.trans (add_le_add (add_le_add le_rfl hR) hF))

lemma commonDepth_markov {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (r low : ℕ) (hlow : 0 < low) :
    twoTapeLaw ν {Z | low ≤ commonDepth L Z r} ≤
      (r : ℝ≥0∞) * ENNReal.ofReal (∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν) / (low : ℝ≥0∞) := by
  have hh := meas_ge_le_lintegral_div (μ := twoTapeLaw ν)
    (((measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (measurable_commonDepth L r)).aemeasurable)
    (ε := (low : ℝ≥0∞)) (by exact_mod_cast Nat.ne_zero_of_lt hlow) (by finiteness)
  have hs : {Z : TwoTape α | (low : ℝ≥0∞) ≤ (commonDepth L Z r : ℝ≥0∞)} =
      {Z | low ≤ commonDepth L Z r} := by ext Z;simp
  simp only [Function.comp_def] at hh
  rw [hs] at hh
  have heq : (∫⁻ Z, (commonDepth L Z r : ℝ≥0∞) ∂twoTapeLaw ν) =
      (r : ℝ≥0∞)*ENNReal.ofReal (∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν) := by
    have hv := ofReal_integral_eq_lintegral_ofReal (commonDepth_integrable ν L hL he hi r)
      (Filter.Eventually.of_forall (fun Z => Nat.cast_nonneg (commonDepth L Z r)))
    simp only [ENNReal.ofReal_natCast] at hv
    rw [← hv,commonDepth_integral ν L hL he hi,ENNReal.ofReal_mul (Nat.cast_nonneg r),ENNReal.ofReal_natCast]
  exact hh.trans_eq (congrArg (fun x => x/(low : ℝ≥0∞)) heq)

end DirectionalZeroOne

end OAI
