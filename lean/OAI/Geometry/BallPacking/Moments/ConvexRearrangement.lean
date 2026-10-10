import Mathlib
import OAI.Geometry.BallPacking.Models.BallVolume

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical
namespace PackingSufficiencySupport
open MeasureTheory
namespace Comparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem exists_gap_parameter {a b : ℝ} (ha : 0 < a) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ (1 - lam) * b < lam * a := by
  let B := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  have hb : b ≤ B := le_max_left _ _
  have hden : 0 < B + 2 * a := by positivity
  refine ⟨(B + a) / (B + 2 * a), div_pos (by positivity) hden, ?_, ?_⟩
  · rw [div_lt_one hden]
    linarith
  · apply (mul_lt_mul_iff_left₀ hden).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hb ha.le]

def translate {S : Set E} {hS : Convex ℝ S} (F : ConvexMaps S hS)
    (c : ℝ) : ConvexMaps S hS :=
  ⟨F.val + ContinuousMap.const S c, by
    intro x y a b ha hb hab
    have hf := F.property x y a b ha hb hab
    change F.val _ + c ≤ a * (F.val x + c) + b * (F.val y + c)
    nlinarith [congrArg (fun t : ℝ => t * c) hab]⟩

theorem exists_rearranged_gap {S : Set E} {hS : Convex ℝ S} [CompactSpace S]
    (h0 : (0 : E) ∈ S) (Q : ConvexMaps S hS)
    (R : ConvexMaps S hS → ConvexMaps S hS) (μ : C(S, ℝ) →ₗ[ℝ] ℝ)
    (hRlip : ∀ F G, dist (R F) (R G) ≤ dist F G)
    (hμlower : ∀ (F : C(S, ℝ)) (c : ℝ), (∀ x, c ≤ F x) → c ≤ μ F)
    (hRmean : ∀ F, μ (R F).val = μ F.val)
    (hRmin : ∀ F x, (R F).val ⟨0, h0⟩ ≤ (R F).val x)
    (hRorder : ∀ F G, (∀ x, F.val x ≤ G.val x) → ∀ x, (R F).val x ≤ (R G).val x)
    (hRtrans : ∀ F c, R (translate F c) = translate (R F) c)
    (hRbound : ∀ F (c : ℝ), (∀ x, F.val x ≤ c) → ∀ x, (R F).val x ≤ c)
    {τ m c : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hm : 0 < m) (hc : 0 < c)
    (hμQ : μ Q.val = -m)
    (houter : ∀ x : S, (x : E) ∉ τ • S → Q.val x ≤ -c) :
    ∃ (K : ConvexMaps S hS) (d : ℝ), 0 < d ∧
      ∀ x, (R (affineStep 1 (by norm_num) Q K)).val x ≤ K.val x - d := by
  let : Nonempty S := ⟨⟨0, h0⟩⟩
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set S).Nonempty) Q.val.continuous.continuousOn
  let d := min m c / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdm : d < m := by
    have := min_le_left m c
    have := lt_min hm hc
    dsimp [d]; linarith
  have hdc : d < c := by
    have := min_le_right m c
    have := lt_min hm hc
    dsimp [d]; linarith
  obtain ⟨lam, hlam, hlam1, hgap⟩ := exists_gap_parameter
    (b := d + Q.val z) (mul_pos (sub_pos.mpr hτ1) (sub_pos.mpr hdm))
  obtain ⟨K, hfix⟩ := exists_convex_fixedPoint Q R hRlip hlam.le hlam1
  have hn := fixedPoint_negative_maximum h0 Q K R μ hμlower hRmean hRmin hRbound
    hlam hlam1 hτ hτ1 hdc hμQ (fun x => hz (Set.mem_univ x)) houter
    (by simpa only [mul_assoc] using hgap) hfix
  have hstep : ∀ x, (affineStep 1 (by norm_num) Q K).val x ≤
      (translate (affineStep lam hlam.le Q K) (-d)).val x := by
    intro x
    have hx := (lt_div_iff₀ (sub_pos.mpr hlam1)).mp (hn x)
    change 1 * K.val x + Q.val x ≤ lam * K.val x + Q.val x + -d
    nlinarith
  refine ⟨K, d, hd, fun x => ?_⟩
  have hr := hRorder _ _ hstep x
  rw [hRtrans, hfix] at hr
  exact hr

section Minimum
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

def minimum (F : C(X, ℝ)) : ℝ := sInf (Set.range F)

theorem minimum_attained (F : C(X, ℝ)) : ∃ x, F x = minimum F :=
  (isCompact_range F.continuous).sInf_mem (Set.range_nonempty F)

omit [Nonempty X] in
theorem minimum_le (F : C(X, ℝ)) (x : X) : minimum F ≤ F x :=
  csInf_le (isCompact_range F.continuous).bddBelow ⟨x, rfl⟩

omit [CompactSpace X] in
theorem le_minimum (F : C(X, ℝ)) {c : ℝ} (h : ∀ x, c ≤ F x) : c ≤ minimum F :=
  le_csInf (Set.range_nonempty F) (by rintro y ⟨x, rfl⟩; exact h x)

theorem minimum_mono (F G : C(X, ℝ)) (h : ∀ x, F x ≤ G x) :
    minimum F ≤ minimum G :=
  le_minimum G (fun x => (minimum_le F x).trans (h x))

theorem minimum_add_const (F : C(X, ℝ)) (c : ℝ) :
    minimum (F + ContinuousMap.const X c) = minimum F + c := by
  obtain ⟨x, hx⟩ := minimum_attained F
  apply le_antisymm
  · calc
      _ ≤ (F + ContinuousMap.const X c) x := minimum_le _ x
      _ = _ := by simp [hx]
  · apply le_minimum
    intro y
    simpa [add_comm] using add_le_add_right (minimum_le F y) c

theorem minimum_lipschitz : LipschitzWith 1 (minimum : C(X, ℝ) → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro F G
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  apply abs_sub_le_iff.mpr
  constructor
  · obtain ⟨x, hx⟩ := minimum_attained G
    have h := (abs_sub_le_iff.mp (ContinuousMap.dist_apply_le_dist (f := F) (g := G) x)).1
    have hf := minimum_le F x
    rw [hx] at h
    linarith
  · obtain ⟨x, hx⟩ := minimum_attained F
    have h := (abs_sub_le_iff.mp (ContinuousMap.dist_apply_le_dist (f := F) (g := G) x)).2
    have hg := minimum_le G x
    rw [hx] at h
    linarith

end Minimum

section SlicedDomain
variable (Y : Set E) (L : E → ℝ)

def sliceDomain : Set (E × ℝ) := {x | x.1 ∈ Y ∧ x.2 ∈ Set.Icc 0 (L x.1)}

abbrev Slice := ↥(sliceDomain Y L)
abbrev UnitInterval := ↥(Set.Icc (0 : ℝ) 1)

def sliceBase : C(Slice Y L, Y) :=
  ⟨fun x => ⟨x.val.1, x.property.1⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩

def sliceHeight : C(Slice Y L, ℝ) :=
  ⟨fun x => x.val.2, continuous_snd.comp continuous_subtype_val⟩

def sliceLength (hL : ContinuousOn L Y) : C(Slice Y L, ℝ) :=
  (⟨fun y : Y => L y, hL.domRestrict⟩ : C(Y, ℝ)).comp (sliceBase Y L)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem intervalEndpoint_mem (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (xt : Slice Y L × UnitInterval) :
    (xt.1.val.1, xt.2.val * (L xt.1.val.1 - xt.1.val.2) + δ * xt.1.val.2)
      ∈ sliceDomain Y L := by
  refine ⟨xt.1.property.1, ?_, ?_⟩
  · have ht := xt.2.property.1
    have hx := xt.1.property.2
    change 0 ≤ xt.2.val * (L xt.1.val.1 - xt.1.val.2) + δ * xt.1.val.2
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hx.2), mul_nonneg hδ.1 hx.1]
  · have ht := xt.2.property.2
    have hx := xt.1.property.2
    change xt.2.val * (L xt.1.val.1 - xt.1.val.2) + δ * xt.1.val.2 ≤ L xt.1.val.1
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hx.2),
      mul_nonneg (sub_nonneg.mpr hδ.2) hx.1]

def intervalEndpoint (hL : ContinuousOn L Y) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    C(Slice Y L × UnitInterval, Slice Y L) := by
  refine ⟨fun xt => ⟨(xt.1.val.1, xt.2.val * (L xt.1.val.1 - xt.1.val.2) +
    δ * xt.1.val.2), intervalEndpoint_mem Y L δ hδ xt⟩, ?_⟩
  apply Continuous.subtype_mk
  apply Continuous.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  exact ((continuous_subtype_val.comp continuous_snd).mul
    (((sliceLength Y L hL).continuous.comp continuous_fst).sub
      ((sliceHeight Y L).continuous.comp continuous_fst))).add
      (((sliceHeight Y L).continuous.comp continuous_fst).const_mul δ)

def intervalValue (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ)) :
    C(Slice Y L × UnitInterval, ℝ) :=
  F.comp (intervalEndpoint Y L hL 0 (by norm_num)) ⊔
    F.comp (intervalEndpoint Y L hL 1 (by norm_num))

def rearrange (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ)) : C(Slice Y L, ℝ) :=
  ⟨fun x => minimum ((intervalValue Y L hL F).curry x),
    minimum_lipschitz.continuous.comp (intervalValue Y L hL F).curry.continuous⟩

def pointAtHeight (x : Slice Y L) (a : ℝ) (ha : a ∈ Set.Icc 0 (L x.val.1)) :
    Slice Y L := ⟨(x.val.1, a), x.property.1, ha⟩

def intervalCandidate (F : C(Slice Y L, ℝ)) (x : Slice Y L) (a : ℝ)
    (ha : 0 ≤ a) (hax : a + x.val.2 ≤ L x.val.1) : ℝ :=
  max (F (pointAtHeight Y L x a ⟨ha, by linarith [x.property.2.1]⟩))
    (F (pointAtHeight Y L x (a + x.val.2) ⟨by linarith [x.property.2.1], hax⟩))

omit [NormedSpace ℝ E] in
theorem intervalValue_eq_candidate (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x : Slice Y L) (t : UnitInterval) :
    intervalValue Y L hL F (x, t) =
      intervalCandidate Y L F x (t.val * (L x.val.1 - x.val.2))
        (mul_nonneg t.property.1 (sub_nonneg.mpr x.property.2.2))
        (by
          nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2)
            (sub_nonneg.mpr x.property.2.2)]) := by
  simp [intervalValue, intervalEndpoint, intervalCandidate, pointAtHeight]

theorem exists_unitInterval_mul {D a : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a) (haD : a ≤ D) :
    ∃ t : UnitInterval, t.val * D = a := by
  by_cases h : D = 0
  · have ha0 : a = 0 := le_antisymm (haD.trans_eq h) ha
    exact ⟨⟨0, by norm_num⟩, by simp [ha0]⟩
  · have hpos : 0 < D := lt_of_le_of_ne hD (Ne.symm h)
    exact ⟨⟨a / D, div_nonneg ha hD, (div_le_one hpos).mpr haD⟩,
      div_mul_cancel₀ a h⟩

omit [NormedSpace ℝ E] in
theorem rearrange_le_candidate (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x : Slice Y L) (a : ℝ) (ha : 0 ≤ a) (hax : a + x.val.2 ≤ L x.val.1) :
    rearrange Y L hL F x ≤ intervalCandidate Y L F x a ha hax := by
  obtain ⟨t, ht⟩ := exists_unitInterval_mul (sub_nonneg.mpr x.property.2.2) ha
    (show a ≤ L x.val.1 - x.val.2 by linarith)
  change minimum ((intervalValue Y L hL F).curry x) ≤ _
  calc
    _ ≤ (intervalValue Y L hL F).curry x t := minimum_le _ t
    _ = _ := by
      change intervalValue Y L hL F (x, t) = _
      rw [intervalValue_eq_candidate]
      simp only [ht]

omit [NormedSpace ℝ E] in
theorem rearrange_attained (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x : Slice Y L) :
    ∃ (a : ℝ) (ha : 0 ≤ a) (hax : a + x.val.2 ≤ L x.val.1),
      rearrange Y L hL F x = intervalCandidate Y L F x a ha hax := by
  obtain ⟨t, ht⟩ := minimum_attained ((intervalValue Y L hL F).curry x)
  have ha := mul_nonneg t.property.1 (sub_nonneg.mpr x.property.2.2)
  have hax : t.val * (L x.val.1 - x.val.2) + x.val.2 ≤ L x.val.1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr x.property.2.2)]
  refine ⟨_, ha, hax, ?_⟩
  change minimum ((intervalValue Y L hL F).curry x) = _
  rw [← ht]
  exact intervalValue_eq_candidate Y L hL F x t

theorem convex_sliceDomain (hc : ConcaveOn ℝ Y L) : Convex ℝ (sliceDomain Y L) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hc.1 hx.1 hy.1 ha hb hab, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
  · exact (add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha)
      (mul_le_mul_of_nonneg_left hy.2.2 hb)).trans (hc.2 hx.1 hy.1 ha hb hab)

theorem rearrange_convex (hL : ContinuousOn L Y) (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc)) :
    rearrange Y L hL F.val ∈ convexFunctionSet (sliceDomain Y L)
      (convex_sliceDomain Y L hc) := by
  intro x y a b ha hb hab
  let z : Slice Y L := ⟨a • x.val + b • y.val, (convex_sliceDomain Y L hc) x.property y.property ha hb hab⟩
  obtain ⟨A, hA, hAx, hFx⟩ := rearrange_attained Y L hL F.val x
  obtain ⟨B, hB, hBy, hFy⟩ := rearrange_attained Y L hL F.val y
  have hC : 0 ≤ a * A + b * B := add_nonneg (mul_nonneg ha hA) (mul_nonneg hb hB)
  have hCz : a * A + b * B + z.val.2 ≤ L z.val.1 := by
    change a * A + b * B + (a * x.val.2 + b * y.val.2) ≤ L (a • x.val.1 + b • y.val.1)
    calc
      _ = a * (A + x.val.2) + b * (B + y.val.2) := by ring
      _ ≤ a * L x.val.1 + b * L y.val.1 :=
        add_le_add (mul_le_mul_of_nonneg_left hAx ha) (mul_le_mul_of_nonneg_left hBy hb)
      _ ≤ _ := hc.2 x.property.1 y.property.1 ha hb hab
  have hz := rearrange_le_candidate Y L hL F.val z (a * A + b * B) hC hCz
  apply hz.trans
  apply max_le
  · have hf := F.property
      (pointAtHeight Y L x A ⟨hA, by linarith [x.property.2.1]⟩)
      (pointAtHeight Y L y B ⟨hB, by linarith [y.property.2.1]⟩) a b ha hb hab
    have hx : F.val (pointAtHeight Y L x A ⟨hA, by linarith [x.property.2.1]⟩) ≤
        rearrange Y L hL F.val x := by
      rw [hFx]; exact le_max_left _ _
    have hy : F.val (pointAtHeight Y L y B ⟨hB, by linarith [y.property.2.1]⟩) ≤
        rearrange Y L hL F.val y := by
      rw [hFy]; exact le_max_left _ _
    have hf' := hf.trans (add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb))
    simpa [pointAtHeight, z, smul_eq_mul] using hf'
  · have hf := F.property
      (pointAtHeight Y L x (A + x.val.2) ⟨by linarith [x.property.2.1], hAx⟩)
      (pointAtHeight Y L y (B + y.val.2) ⟨by linarith [y.property.2.1], hBy⟩) a b ha hb hab
    have hx : F.val (pointAtHeight Y L x (A + x.val.2) ⟨by linarith [x.property.2.1], hAx⟩) ≤
        rearrange Y L hL F.val x := by
      rw [hFx]; exact le_max_right _ _
    have hy : F.val (pointAtHeight Y L y (B + y.val.2) ⟨by linarith [y.property.2.1], hBy⟩) ≤
        rearrange Y L hL F.val y := by
      rw [hFy]; exact le_max_right _ _
    have hf' := hf.trans (add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb))
    convert hf' using 1
    congr 2
    ext <;> simp [pointAtHeight, z, smul_eq_mul]
    ring

omit [NormedSpace ℝ E] in
theorem rearrange_mono (hL : ContinuousOn L Y) (F G : C(Slice Y L, ℝ))
    (hFG : ∀ x, F x ≤ G x) : ∀ x, rearrange Y L hL F x ≤ rearrange Y L hL G x := by
  intro x
  apply minimum_mono
  intro t
  exact max_le_max (hFG _) (hFG _)

omit [NormedSpace ℝ E] in
theorem rearrange_add_const (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ)) (c : ℝ) :
    rearrange Y L hL (F + ContinuousMap.const _ c) =
      rearrange Y L hL F + ContinuousMap.const _ c := by
  ext x
  have hv : (intervalValue Y L hL (F + ContinuousMap.const _ c)).curry x =
      (intervalValue Y L hL F).curry x + ContinuousMap.const _ c := by
    ext t
    exact max_add_add_right _ _ c
  change minimum _ = minimum _ + c
  rw [hv, minimum_add_const]

omit [NormedSpace ℝ E] in
theorem rearrange_nonexpansive [CompactSpace (Slice Y L)] (hL : ContinuousOn L Y)
    (F G : C(Slice Y L, ℝ)) : dist (rearrange Y L hL F) (rearrange Y L hL G) ≤ dist F G := by
  apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist F G)).mpr
  intro x
  apply (minimum_lipschitz.dist_le_mul _ _).trans
  simp only [NNReal.coe_one, one_mul]
  apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist F G)).mpr
  intro t
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  exact max_le (ContinuousMap.dist_apply_le_dist (f := F) (g := G) _)
    (ContinuousMap.dist_apply_le_dist (f := F) (g := G) _)

theorem convex_le_max_on_slice (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc))
    (x : Slice Y L) {a b c : ℝ} (ha : 0 ≤ a) (hb : b ≤ L x.val.1)
    (hac : a ≤ c) (hcb : c ≤ b) :
    F.val (pointAtHeight Y L x c ⟨ha.trans hac, hcb.trans hb⟩) ≤
      max (F.val (pointAtHeight Y L x a ⟨ha, (hac.trans hcb).trans hb⟩))
        (F.val (pointAtHeight Y L x b ⟨ha.trans (hac.trans hcb), hb⟩)) := by
  by_cases hab : a = b
  · have hc : c = a := by linarith
    subst b; subst c
    exact le_max_left _ _
  have habpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (hac.trans hcb) hab)
  let q := (c - a) / (b - a)
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hac) habpos.le
  have hq1 : q ≤ 1 := (div_le_one habpos).mpr (by linarith)
  have hsum : (1-q) + q = 1 := by ring
  have hgeom : (1-q)*a + q*b = c := by
    dsimp [q]
    field_simp
    ring
  have hf := F.property
    (pointAtHeight Y L x a ⟨ha, (hac.trans hcb).trans hb⟩)
    (pointAtHeight Y L x b ⟨ha.trans (hac.trans hcb), hb⟩)
    (1-q) q (sub_nonneg.mpr hq1) hq0 hsum
  have heq : (⟨(1-q) • (pointAtHeight Y L x a
        ⟨ha, (hac.trans hcb).trans hb⟩).val + q •
      (pointAtHeight Y L x b ⟨ha.trans (hac.trans hcb), hb⟩).val,
      (convex_sliceDomain Y L hc) (pointAtHeight Y L x a
        ⟨ha, (hac.trans hcb).trans hb⟩).property
        (pointAtHeight Y L x b ⟨ha.trans (hac.trans hcb), hb⟩).property
        (sub_nonneg.mpr hq1) hq0 hsum⟩ : Slice Y L) =
      pointAtHeight Y L x c ⟨ha.trans hac, hcb.trans hb⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · change (1-q) • x.val.1 + q • x.val.1 = x.val.1
      rw [← add_smul, hsum, one_smul]
    · exact hgeom
  rw [heq] at hf
  apply hf.trans
  calc
    _ ≤ (1-q) * max _ _ + q * max _ _ := add_le_add
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hq1))
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hq0)
    _ = _ := by ring

theorem rearrange_monotone_height (hL : ContinuousOn L Y) (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc))
    (x : Slice Y L) {h : ℝ} (hh0 : 0 ≤ h) (hhx : h ≤ x.val.2) :
    rearrange Y L hL F.val
      (pointAtHeight Y L x h ⟨hh0, hhx.trans x.property.2.2⟩) ≤
      rearrange Y L hL F.val x := by
  obtain ⟨a, ha, hax, hmin⟩ := rearrange_attained Y L hL F.val x
  let z := pointAtHeight Y L x h ⟨hh0, hhx.trans x.property.2.2⟩
  have haz : a + z.val.2 ≤ L z.val.1 := by
    change a + h ≤ L x.val.1
    linarith
  apply (rearrange_le_candidate Y L hL F.val z a ha haz).trans
  rw [hmin]
  apply max_le
  · exact le_max_left _ _
  · exact convex_le_max_on_slice Y L hc F x ha hax
      (by change a ≤ a + h; linarith) (by change a + h ≤ a + x.val.2; linarith)

omit [NormedSpace ℝ E] in

theorem rearrange_compare_slices (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x y : Slice Y L) (hxy : x.val.2 = y.val.2) (hLen : L y.val.1 ≤ L x.val.1)
    (hF : ∀ (a : ℝ) (ha : a ∈ Set.Icc 0 (L y.val.1)),
      F (pointAtHeight Y L x a ⟨ha.1, ha.2.trans hLen⟩) ≤
        F (pointAtHeight Y L y a ha)) :
    rearrange Y L hL F x ≤ rearrange Y L hL F y := by
  obtain ⟨a, ha, hay, hmin⟩ := rearrange_attained Y L hL F y
  have hax : a + x.val.2 ≤ L x.val.1 := by rw [hxy]; exact hay.trans hLen
  apply (rearrange_le_candidate Y L hL F x a ha hax).trans
  rw [hmin]
  apply max_le_max
  · exact hF a ⟨ha, by linarith [y.property.2.1]⟩
  · simpa only [intervalCandidate, hxy] using
      hF (a + y.val.2) ⟨by linarith [y.property.2.1], hay⟩

end SlicedDomain

namespace IntervalMinimum

theorem sublevel_volume_eq {D : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hconv : ConvexOn ℝ (Set.Icc 0 D) f)
    (hchar : ∀ h ∈ Set.Icc 0 D, ∀ c, g h ≤ c ↔
      ∃ a, 0 ≤ a ∧ a + h ≤ D ∧ f a ≤ c ∧ f (a+h) ≤ c) (c : ℝ) :
    volume {h | h ∈ Set.Icc 0 D ∧ g h ≤ c} =
      volume {h | h ∈ Set.Icc 0 D ∧ f h ≤ c} := by
  let S : Set ℝ := {h | h ∈ Set.Icc 0 D ∧ f h ≤ c}
  have hcomp : IsCompact S := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hc : Convex ℝ S := hconv.convex_le c
  by_cases hne : S.Nonempty
  · let a := sInf S
    let b := sSup S
    have hab : a ≤ b := by
      obtain ⟨u, hu⟩ := hne
      exact (csInf_le hcomp.bddBelow hu).trans (le_csSup hcomp.bddAbove hu)
    have hrepr : S = Set.Icc a b := eq_Icc_of_connected_compact (hc.isConnected hne) hcomp
    have haS : a ∈ S := by rw [hrepr]; exact ⟨le_rfl, hab⟩
    have hbS : b ∈ S := by rw [hrepr]; exact ⟨hab, le_rfl⟩
    have heq : {h | h ∈ Set.Icc 0 D ∧ g h ≤ c} = Set.Icc 0 (b-a) := by
      ext h
      constructor
      · rintro ⟨hh, hgc⟩
        obtain ⟨u, hu, huh, hfu, hfuh⟩ := (hchar h hh c).mp hgc
        have huS : u ∈ S := ⟨⟨hu, by linarith [hh.1]⟩, hfu⟩
        have huhS : u+h ∈ S := ⟨⟨by linarith [hh.1], huh⟩, hfuh⟩
        rw [hrepr] at huS huhS
        exact ⟨hh.1, by linarith [huS.1, huhS.2]⟩
      · intro hh
        have hhD : h ∈ Set.Icc 0 D := ⟨hh.1, by linarith [haS.1.1, hbS.1.2, hh.2]⟩
        refine ⟨hhD, (hchar h hhD c).mpr ⟨a, haS.1.1, ?_, haS.2, ?_⟩⟩
        · linarith [hbS.1.2, hh.2]
        · have hah : a+h ∈ S := by rw [hrepr]; constructor <;> linarith [hh.1, hh.2]
          exact hah.2
    rw [heq]
    change volume (Set.Icc 0 (b-a)) = volume S
    rw [hrepr, Real.volume_Icc, Real.volume_Icc, sub_zero]
  · have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have heq : {h | h ∈ Set.Icc 0 D ∧ g h ≤ c} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro h ⟨hh, hgc⟩
      obtain ⟨a, ha, hah, hfa, _⟩ := (hchar h hh c).mp hgc
      exact hne ⟨a, ⟨ha, by linarith [hh.1]⟩, hfa⟩
    change volume _ = volume S
    rw [heq, hS]

theorem integral_eq {D : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hconv : ConvexOn ℝ (Set.Icc 0 D) f)
    (hchar : ∀ h ∈ Set.Icc 0 D, ∀ c, g h ≤ c ↔
      ∃ a, 0 ≤ a ∧ a + h ≤ D ∧ f a ≤ c ∧ f (a+h) ≤ c) :
    ∫ h in Set.Icc 0 D, g h = ∫ h in Set.Icc 0 D, f h := by
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 D)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hm : μ.map g = μ.map f := by
    apply Measure.ext_of_Iic
    intro c
    rw [Measure.map_apply hg.measurable measurableSet_Iic,
      Measure.map_apply hf.measurable measurableSet_Iic]
    dsimp [μ]
    rw [Measure.restrict_apply (hg.measurable measurableSet_Iic),
      Measure.restrict_apply (hf.measurable measurableSet_Iic)]
    simpa only [Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, and_comm] using
      sublevel_volume_eq hf hconv hchar c
  have h := congrArg (fun ν : Measure ℝ => ∫ t, t ∂ν) hm
  rw [integral_map (f := fun t : ℝ => t) hg.measurable.aemeasurable (by fun_prop),
    integral_map (f := fun t : ℝ => t) hf.measurable.aemeasurable (by fun_prop)] at h
  exact h

end IntervalMinimum

variable (Y : Set E) (L : E → ℝ)

def clampPoint (x : Slice Y L) : C(ℝ, Slice Y L) := by
  refine ⟨fun h => pointAtHeight Y L x (max 0 (min (L x.val.1) h))
    ⟨le_max_left _ _, max_le (x.property.2.1.trans x.property.2.2) (min_le_left _ _)⟩, ?_⟩
  apply Continuous.subtype_mk
  exact continuous_const.prodMk (continuous_const.max (continuous_const.min continuous_id))

def sliceFunction (F : C(Slice Y L, ℝ)) (x : Slice Y L) : C(ℝ, ℝ) :=
  F.comp (clampPoint Y L x)

omit [NormedSpace ℝ E] in
theorem sliceFunction_eq (F : C(Slice Y L, ℝ)) (x : Slice Y L)
    {h : ℝ} (hh : h ∈ Set.Icc 0 (L x.val.1)) :
    sliceFunction Y L F x h = F (pointAtHeight Y L x h hh) := by
  change F (pointAtHeight Y L x (max 0 (min (L x.val.1) h))
    ⟨le_max_left _ _, max_le (x.property.2.1.trans x.property.2.2) (min_le_left _ _)⟩) = _
  simp only [min_eq_right hh.2, max_eq_right hh.1]

theorem sliceFunction_convex (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc)) (x : Slice Y L) :
    ConvexOn ℝ (Set.Icc 0 (L x.val.1)) (sliceFunction Y L F.val x) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro a ha b hb p q hp hq hpq
  have hmid := (convex_Icc (0 : ℝ) (L x.val.1) : Convex ℝ _) ha hb hp hq hpq
  rw [sliceFunction_eq Y L F.val x hmid, sliceFunction_eq Y L F.val x ha,
    sliceFunction_eq Y L F.val x hb]
  have hf := F.property (pointAtHeight Y L x a ha) (pointAtHeight Y L x b hb)
    p q hp hq hpq
  have heq : (⟨p • (pointAtHeight Y L x a ha).val + q • (pointAtHeight Y L x b hb).val,
      (convex_sliceDomain Y L hc) (pointAtHeight Y L x a ha).property
        (pointAtHeight Y L x b hb).property hp hq hpq⟩ : Slice Y L) =
      pointAtHeight Y L x (p • a + q • b) hmid := by
    apply Subtype.ext
    apply Prod.ext
    · change p • x.val.1 + q • x.val.1 = x.val.1
      rw [← add_smul, hpq, one_smul]
    · rfl
  rw [heq] at hf
  exact hf

omit [NormedSpace ℝ E] in
theorem rearrange_slice_characterization (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x : Slice Y L) {h : ℝ} (hh : h ∈ Set.Icc 0 (L x.val.1)) (c : ℝ) :
    sliceFunction Y L (rearrange Y L hL F) x h ≤ c ↔
      ∃ a, 0 ≤ a ∧ a+h ≤ L x.val.1 ∧
        sliceFunction Y L F x a ≤ c ∧ sliceFunction Y L F x (a+h) ≤ c := by
  rw [sliceFunction_eq Y L (rearrange Y L hL F) x hh]
  let z := pointAtHeight Y L x h hh
  constructor
  · intro hgc
    obtain ⟨a, ha, haz, hmin⟩ := rearrange_attained Y L hL F z
    have haI : a ∈ Set.Icc 0 (L x.val.1) := ⟨ha, by change a+h ≤ L x.val.1 at haz; linarith [hh.1]⟩
    have hahI : a+h ∈ Set.Icc 0 (L x.val.1) := ⟨by linarith [hh.1], haz⟩
    refine ⟨a, ha, haz, ?_, ?_⟩
    · rw [sliceFunction_eq Y L F x haI]
      exact (le_max_left _ _).trans (hmin.symm.le.trans hgc)
    · rw [sliceFunction_eq Y L F x hahI]
      exact (le_max_right _ _).trans (hmin.symm.le.trans hgc)
  · rintro ⟨a, ha, hah, hfa, hfah⟩
    have haI : a ∈ Set.Icc 0 (L x.val.1) := ⟨ha, by linarith [hh.1]⟩
    have hahI : a+h ∈ Set.Icc 0 (L x.val.1) := ⟨by linarith [hh.1], hah⟩
    rw [sliceFunction_eq Y L F x haI] at hfa
    rw [sliceFunction_eq Y L F x hahI] at hfah
    exact (rearrange_le_candidate Y L hL F z a ha hah).trans (max_le hfa hfah)

theorem rearrange_slice_integral (hL : ContinuousOn L Y) (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc)) (x : Slice Y L) :
    ∫ h in Set.Icc 0 (L x.val.1), sliceFunction Y L (rearrange Y L hL F.val) x h =
      ∫ h in Set.Icc 0 (L x.val.1), sliceFunction Y L F.val x h := by
  apply IntervalMinimum.integral_eq (sliceFunction Y L F.val x).continuous
    (sliceFunction Y L (rearrange Y L hL F.val) x).continuous (sliceFunction_convex Y L hc F x)
  intro h hh c
  exact rearrange_slice_characterization Y L hL F.val x hh c

end Comparison
end PackingSufficiencySupport

namespace PackingSufficiencySupport.MomentPolytope
variable {m N : ℕ}
abbrev Moments (m : ℕ) := Fin m → ℝ
abbrev Base (j : Fin m) := {i : Fin m // i ≠ j} → ℝ

def region (b : Fin N → Moments m) (c : Fin N → ℝ) : Set (Moments m) :=
  {p | (∀ j, 0 ≤ p j) ∧ ∀ ν, ∑ j, b ν j * p j ≤ c ν}

def assemble (j : Fin m) (y : Base j) (h : ℝ) : Moments m :=
  fun i => if hi : i = j then h else y ⟨i, hi⟩

@[simp] theorem assemble_at (j : Fin m) (y : Base j) (h : ℝ) : assemble j y h j = h := by
  simp [assemble]
@[simp] theorem assemble_off (j : Fin m) (y : Base j) (h : ℝ) (i : {i : Fin m // i ≠ j}) :
    assemble j y h i = y i := by simp [assemble, i.property]

def split (j : Fin m) : Moments m ≃ₜ Base j × ℝ where
  toFun p := (fun i => p i, p j)
  invFun x := assemble j x.1 x.2
  left_inv p := by
    funext i
    by_cases hi : i = j <;> simp [assemble, hi]
  right_inv x := by
    apply Prod.ext
    · funext i; simp
    · simp
  continuous_toFun := (continuous_pi fun i => continuous_apply i.val).prodMk (continuous_apply j)
  continuous_invFun := by
    apply continuous_pi
    intro i
    by_cases hi : i = j
    · simpa [assemble, hi] using (continuous_snd : Continuous (Prod.snd : Base j × ℝ → ℝ))
    · simp only [assemble, dite_eq_right hi]
      exact (continuous_apply (⟨i, hi⟩ : {i : Fin m // i ≠ j})).comp continuous_fst

end PackingSufficiencySupport.MomentPolytope
end

end OAI
