import OAI.Combinatorics.Progressions.Lattices.AveragedAffineGrid
import OAI.Combinatorics.Progressions.Sampling.MixedGridBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def idealOutputLog (q degree : ℕ) (P : ℝ) : ℝ := 2*P+q+(degree : ℝ)*q+1

theorem idealOutputLog_nonneg (q degree : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ idealOutputLog q degree P := by unfold idealOutputLog; positivity

theorem idealOutputBound_le_exp {α : Type*} [Fintype α] (a : Finset α)
    {h degree : ℕ} (hh : h ≤ degree) {C W P : ℝ}
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hCP : C ≤ Real.exp P) (hWP : W ≤ Real.exp P) :
    W+(2 : ℝ)^a.card*(C*((Fintype.card α : ℝ)+1)^h) ≤
      Real.exp (idealOutputLog (Fintype.card α) degree P) := by
  have hc : a.card ≤ Fintype.card α := Finset.card_le_univ a
  have hb : (2 : ℝ)^a.card*(C*((Fintype.card α : ℝ)+1)^h) ≤
      booleanJetMassBudget (Fintype.card α) degree C := by
    unfold booleanJetMassBudget
    gcongr
    · norm_num
    · linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)]
  have hm := booleanJetMassBudget_le_exp (Fintype.card α) degree hC hCP
  have hs := add_le_exp_add_one hP
    (show 0 ≤ booleanJetMassLog (Fintype.card α) degree P by unfold booleanJetMassLog; positivity)
    hWP (hb.trans hm)
  apply hs.trans_eq
  congr 1
  unfold idealOutputLog booleanJetMassLog
  ring

noncomputable def commonAffineOutputLog {D α : Type*} [Fintype D] [Fintype α]
    (N : D → Type*) [∀ d, Fintype (N d)] (degree : ℕ) (P : ℝ) : ℝ :=
  (∑ d, jetOutputRadiusLog (Fintype.card α) (Fintype.card (N d)) degree P)+
    idealOutputLog (Fintype.card α) degree P+1

theorem commonAffineOutputLog_nonneg {D α : Type*} [Fintype D] [Fintype α]
    (N : D → Type*) [∀ d, Fintype (N d)] (degree : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ commonAffineOutputLog (α := α) N degree P := by
  have hs : 0 ≤ ∑ d, jetOutputRadiusLog (Fintype.card α) (Fintype.card (N d)) degree P :=
    Finset.sum_nonneg (fun d _ => jetOutputRadiusLog_nonneg _ _ _ hP)
  have hi := idealOutputLog_nonneg (Fintype.card α) degree hP
  unfold commonAffineOutputLog
  linarith

theorem commonAffineOutputLog_radius {D α : Type*} [Fintype D] [Fintype α]
    (N : D → Type*) [∀ d, Fintype (N d)] {I J : Type*} [Fintype I] [Fintype J]
    (d : D) (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (degree : ℕ) (R S : ℝ≥0) {P : ℝ} (hP : 0 ≤ P)
    (hA : ‖A.toContinuousLinearMap‖ ≤ Real.exp P) (hF : ‖F‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hS : (S : ℝ) ≤ Real.exp P) :
    (normalizedJetOutputRadius α (N d) A F degree R S : ℝ) ≤
      Real.exp (commonAffineOutputLog (α := α) N degree P) := by
  apply (normalizedJetOutputRadius_le_exp α (N d) A F degree R S hP hA hF hR hS).trans
  apply Real.exp_le_exp.mpr
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun d => jetOutputRadiusLog (Fintype.card α) (Fintype.card (N d)) degree P)
    (fun d _ => jetOutputRadiusLog_nonneg _ _ _ hP) (Finset.mem_univ d)
  have hi := idealOutputLog_nonneg (Fintype.card α) degree hP
  unfold commonAffineOutputLog
  linarith

theorem commonAffineOutputLog_ideal {D α : Type*} [Fintype D] [Fintype α]
    (N : D → Type*) [∀ d, Fintype (N d)] (degree : ℕ) {P η : ℝ}
    (hP : 0 ≤ P) (hη : η ≤ 1) :
    Real.exp (idealOutputLog (Fintype.card α) degree P)+η ≤
      Real.exp (commonAffineOutputLog (α := α) N degree P) := by
  have hs : 0 ≤ ∑ d, jetOutputRadiusLog (Fintype.card α) (Fintype.card (N d)) degree P :=
    Finset.sum_nonneg (fun d _ => jetOutputRadiusLog_nonneg _ _ _ hP)
  calc
    _ ≤ 1+Real.exp (idealOutputLog (Fintype.card α) degree P) := by linarith
    _ ≤ Real.exp (idealOutputLog (Fintype.card α) degree P+1) :=
      one_add_le_exp_succ (idealOutputLog_nonneg _ _ hP) le_rfl
    _ ≤ _ := by apply Real.exp_le_exp.mpr; unfold commonAffineOutputLog; linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem averagedAffine_log_density_data
    {W D G Z α : Type*} [MeasurableSpace W] [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d)
    (s : ∀ d, O d ↪ J d) (A : ∀ d, (O d → ℝ) ≃L[ℝ] (O d → ℝ))
    (F : ∀ d, (UnselectedColumn (s d) → ℝ) →L[ℝ] (O d → ℝ))
    (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (c w : ∀ d, J d ⊕ N d → ℝ) (z : W → Z → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (hw : ∀ d j, 0 < w d j) (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1)
    (δ : D → ℝ≥0) (hδ : ∀ d, 0 < δ d) (hwidth : ∀ d j, (δ d : ℝ) ≤ w d j)
    (degree : ℕ) (hdegree : ∀ d, h d ≤ degree)
    (hd : ∀ d n, (eN d n).sum (fun _ k => k) ≤ degree)
    (η : ℝ≥0) (hη : 0 < η) (hη1 : η ≤ 1) {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, (|c d j|+|w d j|)) ≤ Wsum)
    {P T E : ℝ} (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hA : ∀ d, ‖(A d).toContinuousLinearMap‖ ≤ Real.exp P)
    (hF : ∀ d, ‖F d‖ ≤ Real.exp P)
    (hInv : ∀ d, ‖(A d).symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : ∀ d, (R d : ℝ) ≤ Real.exp P)
    (htT : (t : ℝ)⁻¹ ≤ Real.exp T) (hδP : ∀ d, (δ d : ℝ)⁻¹ ≤ Real.exp P)
    (hηE : (η : ℝ)⁻¹ ≤ Real.exp E)
    (hCsumP : Csum ≤ Real.exp P) (hWsumP : Wsum ≤ Real.exp P)
    (μ : Measure W) [IsProbabilityMeasure μ] (hzbox : ∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) :
    let Ro := Real.exp (commonAffineOutputLog (α := α) N degree P)
    let b := jointPivotProfileLog s P T
    let f := averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η
    let g := smallAffineMixtureDensity h eK eN s A F sets extra c w t z
    Integrable (fun p : W × ((Σ d, O d) → ℝ) => f p.2-g p.1 p.2) (μ.prod volume) ∧
      (∀ᵐ a ∂μ, LipschitzWith ⟨Real.exp (affineProfileLogBound (Fintype.card (Σ d, O d)) E), Real.exp_nonneg _⟩ f ∧
        LipschitzWith ⟨Real.exp (Fintype.card D+(Fintype.card D+1)*b), Real.exp_nonneg _⟩ (g a) ∧
        (∀ v, (Ro : ℝ) < ‖v‖ → f v = 0) ∧ (∀ v, (Ro : ℝ) < ‖v‖ → g a v = 0)) := by
  let b := jointPivotProfileLog s P T
  let C : ℝ≥0 := ⟨Real.exp b, Real.exp_nonneg _⟩
  let Ro : ℝ≥0 := ⟨Real.exp (commonAffineOutputLog (α := α) N degree P), Real.exp_nonneg _⟩
  let Ri := Real.exp (idealOutputLog (Fintype.card α) degree P)
  obtain ⟨hC, hbounds⟩ := jointPivotProfile_regularity s A R δ t ht hδ hP hT hInv hR htT hδP
  have hRo : ∀ d, normalizedJetOutputRadius α (N d) (A d) (F d) degree (R d) (R d) ≤ Ro := by
    intro d
    exact_mod_cast commonAffineOutputLog_radius N d (A d) (F d) degree (R d) (R d) hP
      (hA d) (hF d) (hR d) (hR d)
  have hideal : ∀ d o, Wsum+(2 : ℝ)^(sets d o).card*(Csum*((Fintype.card α : ℝ)+1)^h d) ≤ Ri :=
    fun d o => idealOutputBound_le_exp (sets d o) (hdegree d) hCsum hP hCsumP hWsumP
  have hRiRo : Ri+(η : ℝ) ≤ Ro :=
    commonAffineOutputLog_ideal N degree hP (by exact_mod_cast hη1)
  have hs := averagedAffine_density_data h eK eN index s A F sets extra c w z hz hw R hsupport
    t ht ht1 δ hδ hwidth C C hC (fun d => (hbounds d).1) (fun d => (hbounds d).2)
    (fun _ => degree) hd Ro hRo η hη (Real.exp_nonneg _) hRiRo hcsum hwsum hideal μ hzbox
  dsimp only
  refine ⟨hs.1, ?_⟩
  filter_upwards [hs.2] with a ha
  refine ⟨ha.1.weaken ?_, ha.2.1.weaken ?_, ha.2.2.1, ha.2.2.2⟩
  · exact_mod_cast affineProductProfileLip_le_exp (Σ d, O d) hηE
  · change (Fintype.card D : ℝ)*Real.exp b*(Real.exp b)^Fintype.card D ≤ _
    exact jointDensityLip_le_exp _ b

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {O J : D → Type*} [∀ d, Fintype (O d)] [∀ d, Fintype (J d)]

noncomputable def affineGridCommonLog (N : D → Type*) [∀ d, Fintype (N d)]
    (s : ∀ d, O d ↪ J d) (degree : ℕ) (P T E : ℝ) : ℝ :=
  commonAffineOutputLog (α := α) N degree P+
    affineProfileLogBound (Fintype.card (Σ d, O d)) E+
    (Fintype.card D+(Fintype.card D+1)*jointPivotProfileLog s P T)+1

noncomputable def affineMixedGridLog (N : D → Type*) [∀ d, Fintype (N d)]
    (s : ∀ d, O d ↪ J d) (degree : ℕ) (P T E : ℝ) : ℝ :=
  Fintype.card (Σ d, O d)*(affineGridCommonLog (α := α) N s degree P T E+4)+
    affineGridCommonLog (α := α) N s degree P T E

theorem affineGridCommonLog_nonneg (N : D → Type*) [∀ d, Fintype (N d)]
    (s : ∀ d, O d ↪ J d) (degree : ℕ) {P T E : ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    0 ≤ affineGridCommonLog (α := α) N s degree P T E := by
  have := commonAffineOutputLog_nonneg (α := α) N degree hP
  have := affineProfileLogBound_nonneg (Fintype.card (Σ d, O d)) hE
  have := jointPivotProfileLog_nonneg s hP hT
  unfold affineGridCommonLog
  positivity

theorem affineMixedGridLog_nonneg (N : D → Type*) [∀ d, Fintype (N d)]
    (s : ∀ d, O d ↪ J d) (degree : ℕ) {P T E : ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    0 ≤ affineMixedGridLog (α := α) N s degree P T E := by
  have := affineGridCommonLog_nonneg (α := α) N s degree hP hT hE
  unfold affineMixedGridLog
  positivity

theorem affineMixedGridAllowance_le_exp (N : D → Type*) [∀ d, Fintype (N d)]
    (s : ∀ d, O d ↪ J d) (degree : ℕ) {P T E : ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T) (hE : 0 ≤ E)
    {V : Type*} [Fintype V] (select : V ↪ (Σ d, O d)) :
    mixedOutputGridAllowance select
      (Real.exp (commonAffineOutputLog (α := α) N degree P))
      (Real.exp (affineProfileLogBound (Fintype.card (Σ d, O d)) E)+
        Real.exp (Fintype.card D+(Fintype.card D+1)*jointPivotProfileLog s P T)) ≤
      Real.exp (affineMixedGridLog (α := α) N s degree P T E) := by
  have hr := commonAffineOutputLog_nonneg (α := α) N degree hP
  have ha := affineProfileLogBound_nonneg (Fintype.card (Σ d, O d)) hE
  have hb : 0 ≤ (Fintype.card D : ℝ)+(Fintype.card D+1)*jointPivotProfileLog s P T := by
    have := jointPivotProfileLog_nonneg s hP hT
    positivity
  apply mixedOutputGridAllowance_le_exp select (Real.exp_nonneg _)
    (add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    (affineGridCommonLog_nonneg (α := α) N s degree hP hT hE)
  · apply Real.exp_le_exp.mpr
    unfold affineGridCommonLog
    linarith
  · apply (add_le_exp_add_one ha hb le_rfl le_rfl).trans
    apply Real.exp_le_exp.mpr
    unfold affineGridCommonLog
    linarith

noncomputable def affineMixedGridAccuracy (N : D → Type*) [∀ d, Fintype (N d)]
    (s : ∀ d, O d ↪ J d) (degree : ℕ) (P T E M τ : ℝ) : ℝ :=
  min 1 (outputGridAccuracy M (Real.exp (affineMixedGridLog (α := α) N s degree P T E)) τ)

theorem affineMixedGridAccuracy_spec (N : D → Type*) [∀ d, Fintype (N d)]
    (s : ∀ d, O d ↪ J d) (degree : ℕ) (P T E : ℝ) {M τ ε : ℝ}
    (hM : 0 ≤ M) (hτ : 0 < τ) (hε : ε ≤ mixedCoefficientAccuracy M τ) :
    0 < affineMixedGridAccuracy (α := α) N s degree P T E M τ ∧
    affineMixedGridAccuracy (α := α) N s degree P T E M τ ≤ 1 ∧
    M*(ε+Real.exp (affineMixedGridLog (α := α) N s degree P T E)*
      affineMixedGridAccuracy (α := α) N s degree P T E M τ) ≤ τ := by
  refine ⟨lt_min zero_lt_one (outputGridAccuracy_pos hM (Real.exp_nonneg _) hτ), min_le_left _ _, ?_⟩
  exact outputGridError_le hM (Real.exp_nonneg _) hτ.le hε (min_le_right _ _)

theorem affineMixedGridAccuracy_inverse_le_exp (N : D → Type*) [∀ d, Fintype (N d)]
    (s : ∀ d, O d ↪ J d) (degree : ℕ) {P T E M τ W : ℝ}
    (hP : 0 ≤ P) (hT : 0 ≤ T) (hE : 0 ≤ E) (hM : 0 ≤ M) (hτ : 0 < τ) (hW : 0 ≤ W)
    (hMW : M ≤ Real.exp W) (hτW : τ⁻¹ ≤ Real.exp W) :
    (affineMixedGridAccuracy (α := α) N s degree P T E M τ)⁻¹ ≤
      Real.exp (3*(affineMixedGridLog (α := α) N s degree P T E+W)+8) := by
  have hQ := affineMixedGridLog_nonneg (α := α) N s degree hP hT hE
  have hWQ : W ≤ affineMixedGridLog (α := α) N s degree P T E+W := le_add_of_nonneg_left hQ
  have hQW : affineMixedGridLog (α := α) N s degree P T E ≤
      affineMixedGridLog (α := α) N s degree P T E+W := le_add_of_nonneg_right hW
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using (Real.one_le_exp_iff.mpr (by positivity :
      0 ≤ 3*(affineMixedGridLog (α := α) N s degree P T E+W)+8))
  · exact outputGridAccuracy_inverse_le_exp hM (Real.exp_nonneg _) hτ (add_nonneg hQ hW)
      (hMW.trans (Real.exp_le_exp.mpr hWQ)) (Real.exp_le_exp.mpr hQW)
      (hτW.trans (Real.exp_le_exp.mpr hWQ))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem averagedAffine_log_mixed_grid_error
    {V : Type*} [Fintype V]
    {W D G Z α : Type*} [MeasurableSpace W] [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d)
    (s : ∀ d, O d ↪ J d) (A : ∀ d, (O d → ℝ) ≃L[ℝ] (O d → ℝ))
    (F : ∀ d, (UnselectedColumn (s d) → ℝ) →L[ℝ] (O d → ℝ))
    (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (c w : ∀ d, J d ⊕ N d → ℝ) (z : W → Z → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (hw : ∀ d j, 0 < w d j) (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1)
    (δ : D → ℝ≥0) (hδ : ∀ d, 0 < δ d) (hwidth : ∀ d j, (δ d : ℝ) ≤ w d j)
    (degree : ℕ) (hdegree : ∀ d, h d ≤ degree)
    (hd : ∀ d n, (eN d n).sum (fun _ k => k) ≤ degree)
    (η : ℝ≥0) (hη : 0 < η) (hη1 : η ≤ 1) {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, (|c d j|+|w d j|)) ≤ Wsum)
    {P T E : ℝ} (hP : 0 ≤ P) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hA : ∀ d, ‖(A d).toContinuousLinearMap‖ ≤ Real.exp P)
    (hF : ∀ d, ‖F d‖ ≤ Real.exp P)
    (hInv : ∀ d, ‖(A d).symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : ∀ d, (R d : ℝ) ≤ Real.exp P)
    (htT : (t : ℝ)⁻¹ ≤ Real.exp T) (hδP : ∀ d, (δ d : ℝ)⁻¹ ≤ Real.exp P)
    (hηE : (η : ℝ)⁻¹ ≤ Real.exp E)
    (hCsumP : Csum ≤ Real.exp P) (hWsumP : Wsum ≤ Real.exp P)
    (μ : Measure W) [IsProbabilityMeasure μ] (hzbox : ∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) {ε : ℝ}
    (he : (∫ p : W × ((Σ d, O d) → ℝ),
      |averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η p.2 -
        smallAffineMixtureDensity h eK eN s A F sets extra c w t z p.1 p.2| ∂μ.prod volume) ≤ ε)
    (select : V ↪ (Σ d, O d))
    (a S : W × (UnselectedColumn select → ℝ) → V → ℝ)
    (hS : ∀ p j, 0 < S p j) {mesh M : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ p j, 1/S p j ≤ mesh)
    (grid : W × (UnselectedColumn select → ℝ) → Finset (V → ℤ)) (mask : W × (UnselectedColumn select → ℝ) → (V → ℤ) → ℝ)
    (φ : W × (UnselectedColumn select → ℝ) → (V → ℤ) → ℂ)
    (hM : 0 ≤ M) (hmask : ∀ p k, k ∈ grid p → |mask p k| ≤ M)
    (hφ : ∀ p k, k ∈ grid p → ‖φ p k‖ ≤ 1) :
    let f := averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η
    let g := smallAffineMixtureDensity h eK eN s A F sets extra c w t z
    ‖∫ p : W × (UnselectedColumn select → ℝ),
      gridDensityTest (selectedOutputSlice select f p.2) (a p) (S p) (grid p) (mask p) (φ p)-
      gridDensityTest (selectedOutputSlice select (g p.1) p.2) (a p) (S p) (grid p) (mask p) (φ p) ∂μ.prod volume‖ ≤
      M*(ε+Real.exp (affineMixedGridLog (α := α) N s degree P T E)*mesh) := by
  dsimp only
  obtain ⟨hi, hgood⟩ := averagedAffine_log_density_data h eK eN index s A F sets extra c w z hz
    hw R hsupport t ht ht1 δ hδ hwidth degree hdegree hd η hη hη1 hCsum hcsum hwsum
    hP hT hA hF hInv hR htT hδP hηE hCsumP hWsumP μ hzbox
  let Ro : ℝ≥0 := ⟨Real.exp (commonAffineOutputLog (α := α) N degree P), Real.exp_nonneg _⟩
  have herr := mixed_output_grid_error select μ
    (fun _ => averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η)
    (smallAffineMixtureDensity h eK eN s A F sets extra c w t z)
    Ro hgood hi he a S hS hmesh0 hmesh1 hmesh grid mask φ hM hmask hφ
  have hcost := affineMixedGridAllowance_le_exp (α := α) N s degree hP hT hE select
  apply herr.trans
  calc
    _ = M*(ε+mixedOutputGridAllowance select
        (Real.exp (commonAffineOutputLog (α := α) N degree P))
        (Real.exp (affineProfileLogBound (Fintype.card (Σ d, O d)) E)+
          Real.exp (Fintype.card D+(Fintype.card D+1)*jointPivotProfileLog s P T))*mesh) := by
      change M*(ε+(2*Real.exp (commonAffineOutputLog (α := α) N degree P))^
        Fintype.card (UnselectedColumn select)*
        ((2*Real.exp (commonAffineOutputLog (α := α) N degree P)+2)^Fintype.card V*
          (Real.exp (affineProfileLogBound (Fintype.card (Σ d, O d)) E)+
            Real.exp (Fintype.card D+(Fintype.card D+1)*jointPivotProfileLog s P T))*mesh)) = _
      unfold mixedOutputGridAllowance
      ring
    _ ≤ _ := by gcongr

end Erdos3

end

end OAI
