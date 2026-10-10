import OAI.Geometry.PinnedDistances.Main

namespace OAI

section
noncomputable section
open Filter
open scoped Topology BigOperators
namespace WeakPinned

def lightTargets (P : Finset Plane) (s : ℝ) (x : Plane) : Finset Plane :=
  (P.erase x).filter (fun y => (k P x y : ℝ) < (P.card : ℝ)^s)

def richTargets (P : Finset Plane) (s : ℝ) (x : Plane) : Finset Plane :=
  (P.erase x).filter (fun y => (P.card : ℝ)^s ≤ (k P x y : ℝ))

lemma light_card_le (P : Finset Plane) (s : ℝ) (x : Plane) :
    ((lightTargets P s x).card : ℝ) ≤ (distances P x).card * (P.card : ℝ)^s := by
  classical
  have hmap : (↑(lightTargets P s x) : Set Plane).MapsTo (fun y => dist y x) (distances P x) := by
    intro y hy
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hy).1
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ r ∈ distances P x, (P.card : ℝ)^s := by
      apply Finset.sum_le_sum
      intro r _
      let D := (lightTargets P s x).filter (fun y => dist y x = r)
      by_cases hD : D.Nonempty
      · obtain ⟨y,hy⟩ := hD
        have hsub : D ⊆ distanceFiber P x y := by
          intro z hz
          obtain ⟨hzL,hzr⟩ := Finset.mem_filter.mp hz
          obtain ⟨hyL,hyr⟩ := Finset.mem_filter.mp hy
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzL).1, hzr.trans hyr.symm⟩
        have hylt : (k P x y : ℝ) < (P.card : ℝ)^s :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
        exact (show (D.card : ℝ) ≤ (k P x y : ℝ) by exact_mod_cast Finset.card_le_card hsub).trans hylt.le
      · change (D.card : ℝ) ≤ (P.card : ℝ)^s
        rw [Finset.not_nonempty_iff_eq_empty.mp hD]
        simp only [Finset.card_empty, Nat.cast_zero]
        positivity
    _ = _ := by simp

lemma row_card_split (P : Finset Plane) (s : ℝ) (x : Plane) :
    (lightTargets P s x).card + (richTargets P s x).card = (P.erase x).card := by
  classical
  convert Finset.card_filter_add_card_filter_not (s := P.erase x)
    (fun y => (k P x y : ℝ) < (P.card : ℝ)^s) using 1
  simp [lightTargets,richTargets]

lemma rich_card_sum (P : Finset Plane) (s : ℝ) :
    ∑ x ∈ P, (richTargets P s x).card = (richPairs P s).card := by
  classical
  have hr (x : Plane) : richTargets P s x = P.filter (fun y => x ≠ y ∧ (P.card : ℝ)^s ≤ (k P x y : ℝ)) := by
    ext y
    simp only [richTargets, Finset.mem_filter, Finset.mem_erase]
    tauto
  simp only [hr, richPairs, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

lemma bad_fraction_bound (P : Finset Plane) (ε : ℝ) (hn : 2 ≤ P.card) :
    badPinFraction P ε ≤ 2*pairFraction P (ε/2) +
      2*((P.card : ℝ)^(1-ε/2)/(P.card : ℝ)) := by
  classical
  have hn2 : (2 : ℝ) ≤ P.card := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < P.card := by linarith
  have hm0 : (0 : ℝ) < (P.card : ℝ)-1 := by linarith
  have h1 : 1 ≤ P.card := by omega
  have hlight (x) (hx : x ∈ badPins P ε) :
      ((lightTargets P (ε/2) x).card : ℝ) ≤ (P.card : ℝ)^(1-ε/2) := by
    have hd := (Finset.mem_filter.mp hx).2
    calc
      _ ≤ (distances P x).card * (P.card : ℝ)^(ε/2) := light_card_le _ _ _
      _ ≤ (P.card : ℝ)^(1-ε)*(P.card : ℝ)^(ε/2) :=
        mul_le_mul_of_nonneg_right hd.le (Real.rpow_nonneg (by positivity) _)
      _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring
  have hrow (x) (hx : x ∈ badPins P ε) :
      (P.card : ℝ)-1 ≤ (richTargets P (ε/2) x).card+(P.card : ℝ)^(1-ε/2) := by
    have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
    have he : ((lightTargets P (ε/2) x).card : ℝ)+(richTargets P (ε/2) x).card=(P.card : ℝ)-1 := by
      rw [← Nat.cast_add, row_card_split, Finset.card_erase_of_mem hxP, Nat.cast_sub h1]
      norm_num
    linarith [hlight x hx]
  have hsum : ((badPins P ε).card : ℝ)*((P.card : ℝ)-1) ≤
      (∑ x ∈ badPins P ε, ((richTargets P (ε/2) x).card : ℝ)) +
      (badPins P ε).card*(P.card : ℝ)^(1-ε/2) := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum hrow
  have hRsum : (∑ x ∈ badPins P ε, ((richTargets P (ε/2) x).card : ℝ)) ≤
      ((richPairs P (ε/2)).card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ P, ((richTargets P (ε/2) x).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
      _ = _ := by rw [← Nat.cast_sum, rich_card_sum]
  have hb : ((badPins P ε).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun x => ((distances P x).card : ℝ)<(P.card : ℝ)^(1-ε)) P)
  have hl0 : (0 : ℝ) ≤ (P.card : ℝ)^(1-ε/2) := Real.rpow_nonneg (by positivity) _
  have htotal : ((badPins P ε).card : ℝ)*((P.card : ℝ)-1) ≤
      (richPairs P (ε/2)).card+(P.card : ℝ)*(P.card : ℝ)^(1-ε/2) := by
    linarith [mul_le_mul_of_nonneg_right hb hl0]
  have hlratio : (P.card : ℝ)^(1-ε/2)/((P.card : ℝ)-1) ≤
      2*((P.card : ℝ)^(1-ε/2)/(P.card : ℝ)) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hm0 hn0]
    nlinarith
  calc
    badPinFraction P ε = ((badPins P ε).card : ℝ)*((P.card : ℝ)-1)/
      ((P.card : ℝ)*((P.card : ℝ)-1)) := by unfold badPinFraction; field_simp
    _ ≤ ((richPairs P (ε/2)).card+(P.card : ℝ)*(P.card : ℝ)^(1-ε/2))/
      ((P.card : ℝ)*((P.card : ℝ)-1)) :=
      div_le_div_of_nonneg_right htotal (mul_pos hn0 hm0).le
    _ = pairFraction P (ε/2)+(P.card : ℝ)^(1-ε/2)/((P.card : ℝ)-1) := by
      unfold pairFraction
      field_simp
    _ ≤ 2*pairFraction P (ε/2)+2*((P.card : ℝ)^(1-ε/2)/(P.card : ℝ)) := by
      linarith [pairFraction_nonneg P (ε/2)]

lemma badPinFraction_nonneg (P : Finset Plane) (ε : ℝ) : 0 ≤ badPinFraction P ε := by
  unfold badPinFraction
  positivity

lemma badPinFraction_le_one (P : Finset Plane) (ε : ℝ) : badPinFraction P ε ≤ 1 := by
  have hb : ((badPins P ε).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun x => ((distances P x).card : ℝ)<(P.card : ℝ)^(1-ε)) P)
  by_cases hn : P.card=0
  · simp [badPinFraction,hn]
  · rw [badPinFraction,div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    exact hb

lemma bad_values_nonempty (n : ℕ) (ε : ℝ) :
    ({a : ℝ | ∃ P : Finset Plane, P.card=n ∧ a=badPinFraction P ε}).Nonempty := by
  obtain ⟨P,hP⟩ := Finset.exists_card_eq (α:=Plane) n
  exact ⟨_,P,hP,rfl⟩

lemma bad_values_bddAbove (n : ℕ) (ε : ℝ) :
    BddAbove {a : ℝ | ∃ P : Finset Plane, P.card=n ∧ a=badPinFraction P ε} := by
  refine ⟨1,?_⟩
  rintro a ⟨P,_,rfl⟩
  exact badPinFraction_le_one P ε

lemma badPinFraction_le_B (P : Finset Plane) (ε : ℝ) (hn : 0<P.card) :
    badPinFraction P ε ≤ B P.card ε := by
  rw [B,ite_eq_left hn]
  exact le_csSup (bad_values_bddAbove _ _) ⟨P,rfl,rfl⟩

lemma B_nonneg (n : ℕ) (ε : ℝ) : 0 ≤ B n ε := by
  by_cases hn : 0<n
  · obtain ⟨P,hP⟩ := Finset.exists_card_eq (α:=Plane) n
    rw [← hP] at hn ⊢
    exact (badPinFraction_nonneg P ε).trans (badPinFraction_le_B P ε hn)
  · simp [B,hn]

lemma B_bound (n : ℕ) (hn : 2≤n) (ε : ℝ) :
    B n ε ≤ 2*F n (ε/2)+2*((n : ℝ)^(1-ε/2)/(n : ℝ)) := by
  rw [B,ite_eq_left (by omega : 0<n)]
  apply csSup_le (bad_values_nonempty _ _)
  rintro a ⟨P,hP,rfl⟩
  have hPn : 2≤P.card := by omega
  have hf := fraction_le_F P (ε/2) hPn
  have hb := bad_fraction_bound P ε hPn
  rw [hP] at hf hb
  linarith

/-- All but a uniformly vanishing fraction of pins determine at least
`n^(1-ε)` distinct nonzero distances. -/
theorem pins (ε : ℝ) (hε : 0<ε) : Tendsto (fun n : ℕ => B n ε) atTop (𝓝 0) := by
  have hpower : Tendsto (fun n : ℕ => (n : ℝ)^(1-ε/2)/(n : ℝ)) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (half_pos hε)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
    simp only [Function.comp_apply]
    rw [show 1-ε/2=1+(-(ε/2)) by ring, Real.rpow_add hn0, Real.rpow_one]
    exact (mul_div_cancel_left₀ _ hn0.ne').symm
  apply squeeze_zero' (Eventually.of_forall (fun n => B_nonneg n ε))
    (eventually_atTop.2 ⟨2,fun n hn => B_bound n hn ε⟩)
  simpa only [mul_zero,add_zero] using ((main (ε/2) (half_pos hε)).const_mul 2).add (hpower.const_mul 2)

theorem pinsStatement : PinsStatement := pins

end WeakPinned

end
end
section
noncomputable section
open Filter
open scoped Topology
namespace WeakPinned

lemma distances_pos {P : Finset Plane} {x : Plane} {r : ℝ} (hr : r ∈ distances P x) :
    0 < r := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hr
  exact dist_pos.mpr (Finset.mem_erase.mp hy).1

/-- Every sufficiently large configuration has a pin with at least
    the prescribed power of its cardinality many distinct nonzero distances. -/
theorem exists_pin_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Finset Plane, P.card = n →
      ∃ x ∈ P, (P.card : ℝ) ^ (1-ε) ≤ ((distances P x).card : ℝ) := by
  have hb : ∀ᶠ n : ℕ in atTop, B n ε < 1 :=
    (pins ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1 P hP
  have hP0 : 0 < P.card := by omega
  by_contra hf
  have hbad : badPins P ε = P := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact lt_of_not_ge (fun h => hf ⟨x,hx,h⟩)
  have hfrac : badPinFraction P ε = 1 := by
    rw [badPinFraction, hbad, div_self (by exact_mod_cast Nat.ne_of_gt hP0)]
  have he := badPinFraction_le_B P ε hP0
  rw [hfrac,hP] at he
  exact (not_lt_of_ge he) hn

end WeakPinned

end
end

end OAI
