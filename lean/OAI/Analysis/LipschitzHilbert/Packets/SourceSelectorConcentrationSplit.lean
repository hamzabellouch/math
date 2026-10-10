import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledCrossResidual
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualVariation
import OAI.Analysis.LipschitzHilbert.Estimates.VariationDifference

namespace OAI

/-! Exact original-selector interval splitting for top concentration.
All three raw covariant jets use the original analyzing coefficients.
Only the frozen-centered synthesis needs a variation estimate; the
remaining interval is controlled by the positive angular error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

private theorem norm_increment_le_cubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    ‖F b-F a‖ ≤ cubicVariation F N := by
  have hcube : ‖F b-F a‖^3 ≤ finiteCubicVariation F N := by
    simpa using disjoint_increment_cube_sum F N (fun _ : Unit => a) (fun _ => b)
      (fun _ => hab) (fun _ => hb) (fun i j hij _ _ => (hij (Subsingleton.elim i j)).elim)
  have h := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) hcube
    (by norm_num : (0:ℝ) ≤ 1/3)
  have hpow : (‖F b-F a‖^3)^(1/3:ℝ) = ‖F b-F a‖ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
    norm_num
  simpa only [hpow,cubicVariation] using h

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)

private theorem rawBand_eq_packet_sum
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (j : Fin N) (x y : ℝ) :
    P.rawBand coeff i j x y =
      ∑ l : P.labels j, ∑ u : Item j l, P.rawPacketValue i j l u (coeff j l u) y x := by
  rw [rawBand,vectorPacketSynthesis_eq_sum,Fintype.sum_sigma]
  rfl

/-- The fixed main coefficient is the only part requiring cancellation. -/
def selectorCenteredRawVariation (i : Fin 3) (x y : ℝ) : ℝ :=
  cubicVariation (packetPartialSum (fun j => (P.withProfile alt hAlt).rawBand
    (P.physicalFrozenCenteredCoefficient t a b v g) i j x y)) N

theorem selector_rawBand_split
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (j : Fin N) (x y : ℝ) :
    (P.withProfile alt hAlt).rawBand (P.physicalMultiplierCoefficient t b v g) i j x y =
      (P.withProfile alt hAlt).rawBand (P.physicalFrozenCenteredCoefficient t a b v g) i j x y+
      (P.withProfile alt hAlt).rawBand (P.physicalAngularErrorCoefficient t a b v g) i j x y := by
  ext k
  simp only [rawBand,vectorPacketSynthesis,packetSynthesis_apply,WithLp.ofLp_toLp,PiLp.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [P.physicalMultiplierCoefficient_split t a b hb hb1 v hv g hg hg1]
  simp only [PiLp.add_apply]
  ring

theorem selector_rawInterval_split
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    (P.withProfile alt hAlt).rawInterval (P.physicalMultiplierCoefficient t b v g)
        i lower upper x y =
      (P.withProfile alt hAlt).rawInterval (P.physicalFrozenCenteredCoefficient t a b v g)
        i lower upper x y+
      (P.withProfile alt hAlt).rawInterval (P.physicalAngularErrorCoefficient t a b v g)
        i lower upper x y := by
  rw [(P.withProfile alt hAlt).rawInterval_eq_band_sum _ _ _ _ hlu,
    (P.withProfile alt hAlt).rawInterval_eq_band_sum _ _ _ _ hlu,
    (P.withProfile alt hAlt).rawInterval_eq_band_sum _ _ _ _ hlu,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ =>
    P.selector_rawBand_split alt hAlt t a b v g hb hb1 hv hg hg1 i j x y

/-- Positive angular error controls an arbitrary original interval,
without a factor for its number of scales or labels. -/
theorem selector_error_rawInterval_norm (horder : 6 ≤ P.order)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    ‖(P.withProfile alt hAlt).rawInterval (P.physicalAngularErrorCoefficient t a b v g)
        i lower upper x y‖ ≤
      P.absoluteConstant*P.physicalAngularError t a b v g (x,y+t*x) := by
  have hband (j : Fin N) :
      ‖(P.withProfile alt hAlt).rawBand (P.physicalAngularErrorCoefficient t a b v g)
        i j x y‖ ≤ P.absoluteConstant*P.physicalErrorScale t a b v g j y x := by
    rw [(P.withProfile alt hAlt).rawBand_eq_packet_sum]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ l : P.labels j, ∑ u : Item j l,
          ‖(P.withProfile alt hAlt).rawPacketValue i j l u
            (P.physicalAngularErrorCoefficient t a b v g j l u) y x‖ :=
        Finset.sum_le_sum fun _ _ => norm_sum_le _ _
      _ ≤ ∑ l : P.labels j, ∑ u : Item j l,
          P.absoluteConstant*(‖P.physicalAngularErrorCoefficient t a b v g j l u‖*
            tileEnvelope (P.length j*(P.snappedSite j l u).1)
              (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun u _ =>
          (P.withProfile alt hAlt).raw_packet_value_norm horder i j l u _ y x
      _ = _ := by simp only [physicalErrorScale,Finset.mul_sum]
  rw [(P.withProfile alt hAlt).rawInterval_eq_band_sum _ _ _ _ hlu]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        ‖(P.withProfile alt hAlt).rawBand (P.physicalAngularErrorCoefficient t a b v g)
          i j x y‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        P.absoluteConstant*P.physicalErrorScale t a b v g j y x :=
      Finset.sum_le_sum fun j _ => hband j
    _ ≤ ∑ j, P.absoluteConstant*P.physicalErrorScale t a b v g j y x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => mul_nonneg P.absoluteConstant_pos.le
          (P.physicalErrorScale_nonneg t a b v g j y x))
    _ = _ := by rw [← Finset.mul_sum,P.sum_physicalErrorScale]

theorem selector_rawInterval_norm_le_variation_add_error (horder : 6 ≤ P.order)
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (hu : upper ≤ N) (x y : ℝ) :
    ‖(P.withProfile alt hAlt).rawInterval (P.physicalMultiplierCoefficient t b v g)
        i lower upper x y‖ ≤
      P.selectorCenteredRawVariation alt hAlt t a b v g i x y+
        P.absoluteConstant*P.physicalAngularError t a b v g (x,y+t*x) := by
  rw [P.selector_rawInterval_split alt hAlt t a b v g hb hb1 hv hg hg1 i lower upper hlu x y]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (P.selector_error_rawInterval_norm alt hAlt t a b v g horder
    i lower upper hlu x y)
  rw [(P.withProfile alt hAlt).rawInterval_eq_band_sum _ _ _ _ hlu,
    ← packetPartialSum_sub_eq_band _ hlu]
  exact norm_increment_le_cubicVariation _ N lower upper hlu hu

/-- The raw first jet is exactly the scaled vertical covariant
 derivative, so the same split supplies both terms of top concentration. -/
theorem selector_rawInterval_joint_norm (horder : 6 ≤ P.order)
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (lower upper : ℕ) (hlu : lower ≤ upper) (hu : upper ≤ N)
    (W : ℝ) (hW : W ≤ |P.scale|) (x y : ℝ) :
    let F := fun x y => (P.withProfile alt hAlt).rawInterval
      (P.physicalMultiplierCoefficient t b v g) 0 lower upper x y
    ‖F x y‖+W*‖covariantSignal P.frequency (fun k yy => F x yy k) y‖ ≤
      P.selectorCenteredRawVariation alt hAlt t a b v g 0 x y+
      P.selectorCenteredRawVariation alt hAlt t a b v g 1 x y+
      2*P.absoluteConstant*P.physicalAngularError t a b v g (x,y+t*x) := by
  dsimp only
  have hcov := (P.withProfile alt hAlt).rawInterval_scaled_covariant
    (P.physicalMultiplierCoefficient t b v g) lower upper x y
  have hn := congrArg norm hcov
  rw [norm_smul,Real.norm_eq_abs] at hn
  have hc : W*‖covariantSignal P.frequency
      (fun k yy => (P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient t b v g) 0 lower upper x yy k) y‖ ≤
      ‖(P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient t b v g) 1 lower upper x y‖ := by
    calc
      _ ≤ |P.scale| * ‖covariantSignal P.frequency
          (fun k yy => (P.withProfile alt hAlt).rawInterval
            (P.physicalMultiplierCoefficient t b v g) 0 lower upper x yy k) y‖ :=
        mul_le_mul_of_nonneg_right hW (norm_nonneg _)
      _ = _ := hn
  have h0 := P.selector_rawInterval_norm_le_variation_add_error alt hAlt t a b v g
    horder hb hb1 hv hg hg1 0 lower upper hlu hu x y
  have h1 := P.selector_rawInterval_norm_le_variation_add_error alt hAlt t a b v g
    horder hb hb1 hv hg hg1 1 lower upper hlu hu x y
  linarith

/-- The positive error majorant controls a full packet-width vertical
 neighborhood at a fixed cost, without a supremum over coefficients. -/
theorem selector_error_vertical_neighborhood (x y shift : ℝ) (hshift : |shift| ≤ P.width) :
    P.physicalAngularError t a b v g (x,y+shift+t*x) ≤
      (3:ℝ)^6*P.physicalAngularError t a b v g (x,y+t*x) := by
  have henv (j : Fin N) (l : P.labels j) (u : Item j l) :
      tileEnvelope (P.length j*(P.snappedSite j l u).1)
        (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y+shift) ≤
      (3:ℝ)^6*tileEnvelope (P.length j*(P.snappedSite j l u).1)
        (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y) := by
    let center := P.width*(P.snappedSite j l u).2
    have heq : lineEnvelope center P.width 6 (y+shift) =
        lineEnvelope (center-shift) P.width 6 y := by
      unfold lineEnvelope
      congr 4
      ring
    have hnear := lineEnvelope_near_center (center-shift) center P.width y 6 P.width_pos
      (by simpa only [sub_sub_cancel_left,abs_neg] using hshift)
    change lineEnvelope _ _ _ x*lineEnvelope center P.width 6 (y+shift) ≤
      (3:ℝ)^6*(lineEnvelope _ _ _ x*lineEnvelope center P.width 6 y)
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hnear (lineEnvelope_nonneg _ _ _ _)).trans_eq (by ring)
  rw [← P.sum_physicalErrorScale t a b v g (y+shift) x,
    ← P.sum_physicalErrorScale t a b v g y x,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simp only [physicalErrorScale,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  apply Finset.sum_le_sum
  intro u _
  exact (mul_le_mul_of_nonneg_left (henv j l u) (norm_nonneg _)).trans_eq (by ring)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
