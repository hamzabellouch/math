import OAI.Probability.SLE.Loewner.RightFieldDriverStability

namespace OAI

/-! A regular real Loewner trajectory has a whole surviving half-disk
which persists under small perturbations of the driving function. -/
noncomputable section
open Set Filter Complex Metric MeasureTheory
open scoped Topology NNReal

namespace SLEExactGauge

theorem real_boundary_driver_neighborhood_control
    (V : ℝ≥0 → ℝ) (T : ℝ≥0) (q : ℝ → ℝ)
    {m : ℝ} (hm : 0 < m)
    (hgap : ∀ t ∈ Icc 0 (T : ℝ), m ≤ q t-V t.toNNReal)
    (hqd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt q
      (2/(q t-V t.toNNReal)) (Icc 0 (T : ℝ)) t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : ℝ≥0 → ℝ), Continuous U →
      ∀ (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) →
      ∀ z ∈ ball ((q 0 : ℝ) : ℂ) δ ∩ upperHalfPlane,
        z ∈ survivingDomain γ T ∧ ∀ t : ℝ≥0, t ≤ T →
          dist (G t z) (q t : ℂ) < m/4 := by
  let a : ℝ := m/4
  have ha : 0 < a := by dsimp [a]; positivity
  let K : ℝ := 4*a⁻¹^2
  let C : ℝ := 2*a⁻¹^2
  have hcont : ContinuousAt (fun δ : ℝ => gronwallBound δ K (C*δ) T) 0 := by
    unfold gronwallBound
    split_ifs <;> fun_prop
  obtain ⟨η,hη,hsmall⟩ := Metric.continuousAt_iff.mp hcont (m/4) (by positivity)
  let δ := min (η/2) (m/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδη : δ < η := (min_le_left _ _).trans_lt (half_lt_self hη)
  have hδm : δ ≤ m/4 := min_le_right _ _
  have hb : gronwallBound δ K (C*δ) T < m/4 := by
    have hh := hsmall (show dist δ 0 < η by
      simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using hδη)
    simp only [mul_zero,gronwallBound_ε0_δ0,Real.dist_eq,sub_zero] at hh
    exact (le_abs_self _).trans_lt hh
  refine ⟨δ,hδ,?_⟩
  intro U hU γ G F hw hUV z hz
  have hu : Continuous (fun t : ℝ => U t.toNNReal) := hU.comp continuous_real_toNNReal
  obtain ⟨Y,_,hY0,hYd⟩ := exists_measurable_right_flow
    (fun t (_ : Unit) => U t.toNNReal) (hu.measurable.comp measurable_fst)
    (fun _ => hu) (fun _ => z) measurable_const ha
  let Z : ℝ → ℂ := fun t => Y t ()
  have hZ0 : Z 0=z := hY0 ()
  have hZ (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt Z
      (rightField a (U t.toNNReal) (Z t)) (Icc 0 (T : ℝ)) t :=
    (hYd () t ht.1).mono Icc_subset_Ici_self
  have hQ (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt
      (fun s => (q s : ℂ)) (rightField a (V t.toNNReal) (q t)) (Icc 0 (T : ℝ)) t := by
    rw [rightField_eq (show a ≤ (q t : ℂ).re-V t.toNNReal by
      simp only [Complex.ofReal_re]; dsimp [a]; linarith [hgap t ht])]
    have hh := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t (hqd t ht)
    simpa only [Function.comp_def,Complex.ofRealCLM_apply,Complex.ofReal_div,
      Complex.ofReal_ofNat,Complex.ofReal_sub] using hh
  have hclose (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : dist (Z t) (q t : ℂ) < m/4 := by
    have he := right_flow_driver_distance ha (fun s => U s.toNNReal)
      (fun s => V s.toNNReal) Z (fun s => (q s : ℂ)) T T.coe_nonneg hZ hQ δ
      (by rw [hZ0]; exact (mem_ball.mp hz.1).le)
      (fun s hs => hUV s.toNNReal ⟨zero_le,(Real.toNNReal_le_iff_le_coe).mpr hs.2⟩) t ht
    have hmono := gronwallBound_mono hδ.le
      (show 0 ≤ C*δ by dsimp [C]; positivity) (show 0 ≤ K by dsimp [K]; positivity) ht.2
    exact (he.trans hmono).trans_lt hb
  have hclip (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : a ≤ (Z t).re-U t.toNNReal := by
    have hr := Complex.abs_re_le_norm (Z t-(q t : ℂ))
    have he := hclose t ht
    rw [dist_eq_norm] at he
    have hreal : |(Z t).re-q t| < m/4 := by
      simpa only [Complex.sub_re,Complex.ofReal_re] using hr.trans_lt he
    have hd := hUV t.toNNReal ⟨zero_le,(Real.toNNReal_le_iff_le_coe).mpr ht.2⟩
    dsimp [a]
    linarith [(abs_lt.mp hreal).1,(abs_le.mp hd).2,hgap t ht]
  have hpos (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : 0 < (Z t).im := by
    apply right_flow_im_pos hu ha ht.1
    · intro s hs
      exact (hZ s ⟨hs.1,hs.2.trans ht.2⟩).mono
        (Icc_subset_Icc le_rfl ht.2)
    · simpa only [hZ0,upperHalfPlane,mem_ofPred_eq] using hz.2
  have hode (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt Z
      (2/(Z t-(U t.toNNReal : ℂ))) (Icc 0 (T : ℝ)) t := by
    rw [← rightField_eq (hclip t ht)]
    exact hZ t ht
  have hs := (hw.forward_flow_survives T Z hpos hode).1
  refine ⟨by simpa only [hZ0] using hs,?_⟩
  intro t ht
  have hsub : Icc 0 (t : ℝ) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc le_rfl (by exact_mod_cast ht)
  have he := (hw.forward_flow_survives t Z
    (fun s hs => hpos s (hsub hs))
    (fun s hs => (hode s (hsub hs)).mono hsub)).2
  rw [hZ0] at he
  rw [he]
  exact hclose t ⟨t.coe_nonneg,by exact_mod_cast ht⟩

theorem real_boundary_driver_neighborhood
    (V : ℝ≥0 → ℝ) (T : ℝ≥0) (q : ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hgap : ∀ t ∈ Icc 0 (T : ℝ), m ≤ q t-V t.toNNReal)
    (hqd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt q
      (2/(q t-V t.toNNReal)) (Icc 0 (T : ℝ)) t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : ℝ≥0 → ℝ), Continuous U →
      ∀ (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) →
      ball ((q 0 : ℝ) : ℂ) δ ∩ upperHalfPlane ⊆ survivingDomain γ T := by
  obtain ⟨δ,hδ,hh⟩ := real_boundary_driver_neighborhood_control V T q hm hgap hqd
  exact ⟨δ,hδ,fun U hU γ G F hw hUV z hz => (hh U hU γ G F hw hUV z hz).1⟩

end SLEExactGauge

end

end OAI
