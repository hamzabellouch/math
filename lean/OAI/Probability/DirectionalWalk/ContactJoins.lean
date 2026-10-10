import OAI.Probability.DirectionalWalk.JoinedBridges

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def positiveJoin {d : ℕ} (a : ThreeLists (Word d)) : Word d :=
  concatenateList (appendTapeList (reverseTapeList a.2.2) (reverseTapeList a.2.1))
noncomputable def negativeJoin {d : ℕ} (a : ThreeLists (Word d)) : Word d :=
  concatenateList (appendTapeList a.1 a.2.1)

def middleContact {d : ℕ} (z : Site d) : Set (ThreeLists (Word d) × ThreeLists (Word d)) :=
  (Prod.map positiveJoin negativeJoin) ⁻¹' bridgeWordContact z

lemma signedThreeKernel_join_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ × (ℕ × ℕ)) :
    letI := slabLaw_probability μ v hp
    let U := fun h => Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) h)
    ((signedThreeKernel (slabLaw μ v) (slabRecords v) H).map positiveJoin ≤
      ((U H.2.2)⁻¹*(U H.2.1)⁻¹) • rawBridgeMeasure μ v (H.2.2+H.2.1)) ∧
    ((signedThreeKernel (slabLaw μ v) (slabRecords v) H).map negativeJoin ≤
      ((U H.1)⁻¹*(U H.2.1)⁻¹) • rawBridgeMeasure μ v (H.1+H.2.1)) := by
  let := slabLaw_probability μ v hp
  have hu (h : ℕ) : Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) h) ≠ 0 := by
    change Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (tapeCut v h) ≠ 0
    rw [tapeCut_mass μ hell v hv hp]
    exact ne_of_gt (hp.trans_le (reachRecord_mass_ge μ hell v hv h))
  dsimp only
  constructor
  · have hh := congrArg (fun M : Measure (TapeList (Word d) × TapeList (Word d)) =>
      M.map (fun p => concatenateList (appendTapeList (reverseTapeList p.1) (reverseTapeList p.2))))
      (signedThreeKernel_proj32 (slabLaw μ v) (slabRecords v) hu H)
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hh
    exact hh.le.trans (bridgeListLaw_join_reversed_raw_le μ hell v hv hp H.2.2 H.2.1)
  · have hh := congrArg (fun M : Measure (TapeList (Word d) × TapeList (Word d)) =>
      M.map (fun p => concatenateList (appendTapeList p.1 p.2)))
      (signedThreeKernel_proj12 (slabLaw μ v) (slabRecords v) hu H)
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hh
    exact hh.le.trans (bridgeListLaw_join_raw_le μ hell v hv hp H.1 H.2.1)

lemma four_bridge_contact_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e)))
    (hm : 0 < annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))
    (H : ℕ × (ℕ × ℕ)) (z : Site d) (n : ℕ)
    (h1 : n ≤ H.1) (h3 : n ≤ H.2.2)
    (hz : axisHeight e z = ((H.1+H.2.1+H.2.2 : ℕ) : ℤ)-1) :
    letI := slabLaw_probability μ (axisDirection e) hp
    letI := slabLaw_probability μ (axisDirection (oppositeStep e)) hm
    ((signedThreeKernel (slabLaw μ (axisDirection e)) (slabRecords (axisDirection e)) H).prod
      (signedThreeKernel (slabLaw μ (axisDirection (oppositeStep e)))
        (slabRecords (axisDirection (oppositeStep e))) H)) (middleContact z) ≤
      ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)^2 *
      ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)^2 *
      (2*((axisReachProb μ e n-axisReachProb μ e (H.1+H.2.1+H.2.2)) +
        (axisReachProb μ (oppositeStep e) n-axisReachProb μ (oppositeStep e) (H.1+H.2.1+H.2.2)))) := by
  let := slabLaw_probability μ (axisDirection e) hp
  let := slabLaw_probability μ (axisDirection (oppositeStep e)) hm
  have hU (f : Step d) (hf : 0 < annealed μ 0 (nonBacktracking (axisDirection f))) (h : ℕ) :
      letI := slabLaw_probability μ (axisDirection f) hf
      Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection f))
        (renewalCut (slabRecords (axisDirection f)) h) = axisReachProb μ f h :=
    axis_tapeCut_mass μ hell f hf h
  have hA := (signedThreeKernel_join_le μ hell (axisDirection e) (axisDirection_ne_zero e) hp H).1
  have hB := (signedThreeKernel_join_le μ hell (axisDirection (oppositeStep e))
    (axisDirection_ne_zero (oppositeStep e)) hm H).2
  simp only [hU e hp] at hA
  simp only [hU (oppositeStep e) hm] at hB
  have hpos (f : Step d) (hf : 0 < annealed μ 0 (nonBacktracking (axisDirection f))) (h : ℕ) :
      axisReachProb μ f h ≠ 0 := ne_of_gt (hf.trans_le (axisReachProb_lower μ hell f h))
  have hb : (axisReachProb μ (oppositeStep e) H.1)⁻¹ * (axisReachProb μ (oppositeStep e) H.2.1)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (hpos _ hm _)) (ENNReal.inv_ne_top.mpr (hpos _ hm _))
  have hh := product_contact_domination μ hell e z n (H.1+H.2.1+H.2.2) (H.2.2+H.2.1) (H.1+H.2.1)
    (by omega) (by omega) (by omega) (by omega) hz _ _ _ _ hb hA hB
  rw [Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_apply ((measurable_of_countable positiveJoin).prodMap (measurable_of_countable negativeJoin))
      (Set.to_countable _).measurableSet] at hh
  refine hh.trans ?_
  calc
    _ ≤ (((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)*
        ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)) *
      (((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)*
        ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)) * _ := by
          gcongr <;> exact axisReachProb_lower μ hell _ _
    _ = _ := by simp only [pow_two]

lemma shiftPath_preimage_wordCylinder {d : ℕ} (z : Site d) (a : Word d) :
    shiftPath (-z) ⁻¹' wordCylinder a = wordCylinder (translateWord z a) := by
  ext X
  constructor
  · intro h i hi
    rw [wordPath_translate z a i hi]
    have hh := h i hi
    dsimp only [shiftPath] at hh
    rw [← hh]
    abel
  · intro h i hi
    have hh := h i hi
    rw [wordPath_translate z a i hi] at hh
    change X i + -z = wordPath a i
    rw [hh]
    abel

end DirectionalZeroOne

end OAI
