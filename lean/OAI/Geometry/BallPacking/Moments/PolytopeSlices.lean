import Mathlib
import OAI.Geometry.BallPacking.Moments.ConvexRearrangement

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical
namespace PackingSufficiencySupport.MomentPolytope
variable {m N : ℕ}
theorem weighted_assemble (j : Fin m) (B : Moments m) (y : Base j) (h : ℝ) :
    ∑ i, B i * assemble j y h i = B j * h + ∑ i : {i : Fin m // i ≠ j}, B i.val * y i := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  simp only [assemble_at, assemble_off]

theorem weighted_affine {ι : Type*} [Fintype ι] (B y z : ι → ℝ) (a d : ℝ) :
    ∑ i, B i * (a * y i + d * z i) = a * ∑ i, B i * y i + d * ∑ i, B i * z i := by
  calc
    _ = ∑ i, (a * (B i * y i) + d * (B i * z i)) := by congr 1; funext i; ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem convex_region (b : Fin N → Moments m) (c : Fin N → ℝ) : Convex ℝ (region b c) := by
  intro y hy z hz a d ha hd had
  constructor
  · intro j; exact add_nonneg (mul_nonneg ha (hy.1 j)) (mul_nonneg hd (hz.1 j))
  · intro ν
    change ∑ i, b ν i * (a * y i + d * z i) ≤ c ν
    rw [weighted_affine]
    have h := add_le_add (mul_le_mul_of_nonneg_left (hy.2 ν) ha)
      (mul_le_mul_of_nonneg_left (hz.2 ν) hd)
    exact h.trans_eq (by rw [← add_mul, had, one_mul])

theorem lower_closed (b : Fin N → Moments m) (c : Fin N → ℝ) (hb : ∀ ν j, 0 ≤ b ν j)
    {p q : Moments m} (hp : p ∈ region b c) (hq : ∀ j, 0 ≤ q j) (hqp : ∀ j, q j ≤ p j) :
    q ∈ region b c := by
  refine ⟨hq, fun ν => (Finset.sum_le_sum fun i _ => ?_).trans (hp.2 ν)⟩
  exact mul_le_mul_of_nonneg_left (hqp i) (hb ν i)

def baseRegion (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) : Set (Base j) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∀ ν, ∑ i : {i : Fin m // i ≠ j}, b ν i.val * y i ≤ c ν}

theorem assemble_zero_mem_iff (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) (y : Base j) :
    assemble j y 0 ∈ region b c ↔ y ∈ baseRegion b c j := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h.1 i, fun ν => by simpa [weighted_assemble] using h.2 ν⟩
  · intro h
    constructor
    · intro i
      by_cases hi : i = j
      · simp [assemble, hi]
      · simpa [assemble, hi] using h.1 ⟨i, hi⟩
    · intro ν; simpa [weighted_assemble] using h.2 ν

theorem convex_baseRegion (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m) :
    Convex ℝ (baseRegion b c j) := by
  intro y hy z hz a d ha hd had
  constructor
  · intro i; exact add_nonneg (mul_nonneg ha (hy.1 i)) (mul_nonneg hd (hz.1 i))
  · intro ν
    change ∑ i : {i : Fin m // i ≠ j}, b ν i.val * (a * y i + d * z i) ≤ c ν
    rw [weighted_affine]
    have h := add_le_add (mul_le_mul_of_nonneg_left (hy.2 ν) ha)
      (mul_le_mul_of_nonneg_left (hz.2 ν) hd)
    exact h.trans_eq (by rw [← add_mul, had, one_mul])

theorem baseRegion_eq_image (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j, 0 ≤ b ν j) (j : Fin m) :
    baseRegion b c j = (fun p : Moments m => fun i : {i : Fin m // i ≠ j} => p i) '' region b c := by
  ext y
  constructor
  · intro hy
    refine ⟨assemble j y 0, (assemble_zero_mem_iff b c j y).mpr hy, ?_⟩
    funext i; simp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun i => hp.1 i, fun ν => ?_⟩
    have h := hp.2 ν
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j] at h
    linarith [mul_nonneg (hb ν j) (hp.1 j)]

theorem isCompact_baseRegion (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j, 0 ≤ b ν j) (hcomp : IsCompact (region b c)) (j : Fin m) :
    IsCompact (baseRegion b c j) := by
  rw [baseRegion_eq_image b c hb j]
  exact hcomp.image (continuous_pi fun i => continuous_apply i.val)

abbrev Active (b : Fin N → Moments m) (j : Fin m) := {ν : Fin N // 0 < b ν j}

theorem active_nonempty (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j, 0 ≤ b ν j) (hc : ∀ ν, 0 < c ν) (hcomp : IsCompact (region b c))
    (j : Fin m) : Nonempty (Active b j) := by
  by_contra hn
  have hzero : ∀ ν, b ν j = 0 := by
    intro ν
    apply le_antisymm _ (hb ν j)
    by_contra h
    exact hn ⟨⟨ν, lt_of_not_ge h⟩⟩
  obtain ⟨M, hM⟩ := (hcomp.image (continuous_apply j)).bddAbove
  let t := max 0 M + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hp : assemble j 0 t ∈ region b c := by
    constructor
    · intro i; by_cases hi : i = j <;> simp [assemble, hi, ht]
    · intro ν; simpa [weighted_assemble, hzero ν] using (hc ν).le
  have h := hM ⟨assemble j 0 t, hp, assemble_at j 0 t⟩
  dsimp [t] at h
  linarith [le_max_right (0 : ℝ) M]

variable (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)

def endpoint (ν : Active b j) (y : Base j) : ℝ :=
  (c ν - ∑ i : {i : Fin m // i ≠ j}, b ν i.val * y i) / b ν j

def length [Nonempty (Active b j)] (y : Base j) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun ν => endpoint b c j ν y)

theorem length_le [Nonempty (Active b j)] (ν : Active b j) (y : Base j) :
    length b c j y ≤ endpoint b c j ν y := Finset.inf'_le _ (Finset.mem_univ ν)

theorem le_length_iff [Nonempty (Active b j)] {y : Base j} {h : ℝ} :
    h ≤ length b c j y ↔ ∀ ν : Active b j, h ≤ endpoint b c j ν y := by
  simp [length, Finset.le_inf'_iff]

theorem continuous_endpoint (ν : Active b j) : Continuous (endpoint b c j ν) := by
  unfold endpoint
  fun_prop

theorem continuous_length [Nonempty (Active b j)] : Continuous (length b c j) := by
  apply Continuous.finset_inf'_apply
  intro ν _
  exact continuous_endpoint b c j ν

theorem endpoint_affine (ν : Active b j) (y z : Base j) (a d : ℝ) (had : a+d=1) :
    endpoint b c j ν (a • y + d • z) = a * endpoint b c j ν y + d * endpoint b c j ν z := by
  unfold endpoint
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [weighted_affine]
  calc
    _ = ((a+d) * c ν - (a * ∑ i : {i : Fin m // i ≠ j}, b ν i.val * y i +
        d * ∑ i : {i : Fin m // i ≠ j}, b ν i.val * z i)) / b ν j := by rw [had, one_mul]
    _ = _ := by ring

theorem concave_length [Nonempty (Active b j)] : ConcaveOn ℝ (baseRegion b c j) (length b c j) := by
  refine ⟨convex_baseRegion b c j, ?_⟩
  intro y _ z _ a d ha hd had
  apply (le_length_iff b c j).mpr
  intro ν
  rw [endpoint_affine b c j ν y z a d had]
  exact add_le_add (mul_le_mul_of_nonneg_left (length_le b c j ν y) ha)
    (mul_le_mul_of_nonneg_left (length_le b c j ν z) hd)

theorem assemble_mem_iff [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
    (y : Base j) (h : ℝ) :
    assemble j y h ∈ region b c ↔ y ∈ baseRegion b c j ∧ 0 ≤ h ∧ h ≤ length b c j y := by
  constructor
  · intro hp
    have hh : 0 ≤ h := by simpa using hp.1 j
    refine ⟨⟨fun i => by simpa using hp.1 i, fun ν => ?_⟩, hh, ?_⟩
    · have h := hp.2 ν
      rw [weighted_assemble] at h
      linarith [mul_nonneg (hb ν j) hh]
    · apply (le_length_iff b c j).mpr
      intro ν
      apply (le_div_iff₀ ν.property).mpr
      have h := hp.2 ν
      rw [weighted_assemble] at h
      dsimp [endpoint]
      nlinarith
  · rintro ⟨hy, hh, hL⟩
    constructor
    · intro i
      by_cases hi : i = j
      · simpa [assemble, hi] using hh
      · simpa [assemble, hi] using hy.1 ⟨i, hi⟩
    · intro ν
      rw [weighted_assemble]
      by_cases hpos : 0 < b ν j
      · have h := (le_length_iff b c j).mp hL ⟨ν, hpos⟩
        have h := (le_div_iff₀ hpos).mp h
        dsimp [endpoint] at h
        nlinarith
      · have hz : b ν j = 0 := le_antisymm (not_lt.mp hpos) (hb ν j)
        simpa [hz] using hy.2 ν

theorem length_nonneg [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
    {y : Base j} (hy : y ∈ baseRegion b c j) : 0 ≤ length b c j y :=
  ((assemble_mem_iff b c j hb y 0).mp ((assemble_zero_mem_iff b c j y).mpr hy)).2.2

theorem length_antitone [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i) :
    Antitone (length b c j) := by
  intro y z hyz
  apply (le_length_iff b c j).mpr
  intro ν
  apply (length_le b c j ν z).trans
  apply div_le_div_of_nonneg_right _ ν.property.le
  apply sub_le_sub_left
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyz i) (hb ν i)

theorem zero_mem (hc : ∀ ν, 0 ≤ c ν) : (0 : Moments m) ∈ region b c := by
  constructor
  · intro i; rfl
  · intro ν; simpa using hc ν

theorem assemble_affine (y z : Base j) (s t a d : ℝ) :
    assemble j (a • y + d • z) (a * s + d * t) =
      a • assemble j y s + d • assemble j z t := by
  funext i
  by_cases hi : i = j <;> simp [assemble, hi]

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
variable [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

def sliceEquiv : (region b c) ≃ₜ Slice (baseRegion b c j) (length b c j) :=
  (split j).subtype fun p => by
    have h := assemble_mem_iff b c j hb (fun i => p i) (p j)
    have heq : assemble j (fun i => p i) (p j) = p := (split j).left_inv p
    change p ∈ region b c ↔ (fun i : {i : Fin m // i ≠ j} => p i) ∈ baseRegion b c j ∧
      0 ≤ p j ∧ p j ≤ length b c j (fun i => p i)
    simpa only [heq] using h

def onSlice (F : C(region b c, ℝ)) : C(Slice (baseRegion b c j) (length b c j), ℝ) :=
  F.comp ⟨(sliceEquiv b c j hb).symm, (sliceEquiv b c j hb).symm.continuous⟩

def coordRearrange (F : C(region b c, ℝ)) : C(region b c, ℝ) :=
  (rearrange (baseRegion b c j) (length b c j) (continuous_length b c j).continuousOn
    (onSlice b c j hb F)).comp ⟨sliceEquiv b c j hb, (sliceEquiv b c j hb).continuous⟩

theorem onSlice_convex (F : ConvexMaps (region b c) (convex_region b c)) :
    onSlice b c j hb F.val ∈ convexFunctionSet _
      (convex_sliceDomain _ _ (concave_length b c j)) := by
  intro x y a d ha hd had
  have h := F.property ((sliceEquiv b c j hb).symm x) ((sliceEquiv b c j hb).symm y)
    a d ha hd had
  change F.val ((sliceEquiv b c j hb).symm _) ≤
    a * F.val ((sliceEquiv b c j hb).symm x) + d * F.val ((sliceEquiv b c j hb).symm y)
  have heq : (sliceEquiv b c j hb).symm
      ⟨a • x.val + d • y.val, (convex_sliceDomain _ _ (concave_length b c j))
        x.property y.property ha hd had⟩ =
      (⟨a • ((sliceEquiv b c j hb).symm x).val + d • ((sliceEquiv b c j hb).symm y).val,
        (convex_region b c) ((sliceEquiv b c j hb).symm x).property
          ((sliceEquiv b c j hb).symm y).property ha hd had⟩ : region b c) := by
    apply Subtype.ext
    exact assemble_affine j x.val.1 y.val.1 x.val.2 y.val.2 a d
  rw [heq]
  exact h

theorem coordRearrange_convex (F : ConvexMaps (region b c) (convex_region b c)) :
    coordRearrange b c j hb F.val ∈ convexFunctionSet _ (convex_region b c) := by
  let Fs : ConvexMaps (sliceDomain (baseRegion b c j) (length b c j))
      (convex_sliceDomain _ _ (concave_length b c j)) :=
    ⟨onSlice b c j hb F.val, onSlice_convex b c j hb F⟩
  have h := rearrange_convex (baseRegion b c j) (length b c j)
    (continuous_length b c j).continuousOn (concave_length b c j) Fs
  intro x y a d ha hd had
  exact h ((sliceEquiv b c j hb) x) ((sliceEquiv b c j hb) y) a d ha hd had

def coordOperator (F : ConvexMaps (region b c) (convex_region b c)) :
    ConvexMaps (region b c) (convex_region b c) :=
  ⟨coordRearrange b c j hb F.val, coordRearrange_convex b c j hb F⟩

theorem coordRearrange_mono (F G : C(region b c, ℝ)) (hFG : F ≤ G) :
    coordRearrange b c j hb F ≤ coordRearrange b c j hb G := by
  intro p
  apply rearrange_mono
  intro x
  exact hFG _

theorem coordRearrange_add_const (F : C(region b c, ℝ)) (a : ℝ) :
    coordRearrange b c j hb (F + ContinuousMap.const _ a) =
      coordRearrange b c j hb F + ContinuousMap.const _ a := by
  have heq : onSlice b c j hb (F + ContinuousMap.const _ a) =
      onSlice b c j hb F + ContinuousMap.const _ a := by
    ext x
    rfl
  unfold coordRearrange
  rw [heq, rearrange_add_const]
  rfl

theorem coordRearrange_nonexpansive [CompactSpace (region b c)]
    (F G : C(region b c, ℝ)) :
    dist (coordRearrange b c j hb F) (coordRearrange b c j hb G) ≤ dist F G := by
  apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist F G)).mpr
  intro p
  have hFG : F ≤ G + ContinuousMap.const _ (dist F G) := by
    intro x
    have h := ContinuousMap.dist_apply_le_dist (f := F) (g := G) x
    rw [Real.dist_eq] at h
    have h' := (abs_le.mp h).2
    change F x ≤ G x + dist F G
    linarith
  have hGF : G ≤ F + ContinuousMap.const _ (dist F G) := by
    intro x
    have h := ContinuousMap.dist_apply_le_dist (f := F) (g := G) x
    rw [Real.dist_eq] at h
    have h' := (abs_le.mp h).1
    change G x ≤ F x + dist F G
    linarith
  have h1 := coordRearrange_mono b c j hb _ _ hFG p
  have h2 := coordRearrange_mono b c j hb _ _ hGF p
  rw [coordRearrange_add_const] at h1 h2
  change coordRearrange b c j hb F p ≤ coordRearrange b c j hb G p + dist F G at h1
  change coordRearrange b c j hb G p ≤ coordRearrange b c j hb F p + dist F G at h2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)

def IncreasingIn (i : Fin m) (F : C(region b c, ℝ)) : Prop :=
  ∀ p q : region b c, p.val i ≤ q.val i → (∀ l, l ≠ i → p.val l = q.val l) → F p ≤ F q

variable (j : Fin m) [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

theorem coordRearrange_increasing (F : ConvexMaps (region b c) (convex_region b c)) :
    IncreasingIn b c j (coordRearrange b c j hb F.val) := by
  intro p q hpq heq
  let e := sliceEquiv b c j hb
  let Fs : ConvexMaps (sliceDomain (baseRegion b c j) (length b c j))
      (convex_sliceDomain _ _ (concave_length b c j)) :=
    ⟨onSlice b c j hb F.val, onSlice_convex b c j hb F⟩
  have hh : p.val j ∈ Set.Icc 0 (length b c j (e q).val.1) :=
    ⟨p.property.1 j, hpq.trans (e q).property.2.2⟩
  have he : pointAtHeight (baseRegion b c j) (length b c j) (e q) (p.val j) hh = e p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact (heq i i.property).symm
    · rfl
  change rearrange _ _ _ Fs.val (e p) ≤ rearrange _ _ _ Fs.val (e q)
  rw [← he]
  exact rearrange_monotone_height _ _ (continuous_length b c j).continuousOn
    (concave_length b c j) Fs (e q) (p.property.1 j) hpq

theorem coordRearrange_preserves_increasing (i : Fin m) (hij : i ≠ j)
    (F : C(region b c, ℝ)) (hF : IncreasingIn b c i F) :
    IncreasingIn b c i (coordRearrange b c j hb F) := by
  intro p q hpq heq
  let e := sliceEquiv b c j hb
  have hbase : (e p).val.1 ≤ (e q).val.1 := by
    intro l
    change p.val l ≤ q.val l
    by_cases hl : l.val = i
    · simpa [hl] using hpq
    · exact (heq l hl).le
  change rearrange _ _ _ (onSlice b c j hb F) (e p) ≤
    rearrange _ _ _ (onSlice b c j hb F) (e q)
  apply rearrange_compare_slices _ _ (continuous_length b c j).continuousOn _ (e p) (e q)
    (heq j hij.symm) (length_antitone b c j hb hbase)
  intro a ha
  apply hF
  · change assemble j (fun l => p.val l) a i ≤ assemble j (fun l => q.val l) a i
    simpa [assemble, hij] using hpq
  · intro l hli
    change assemble j (fun l => p.val l) a l = assemble j (fun l => q.val l) a l
    by_cases hlj : l = j
    · simp [assemble, hlj]
    · simpa [assemble, hlj] using heq l hli

theorem coordRearrange_bound (F : C(region b c, ℝ)) (a : ℝ) (hF : ∀ p, F p ≤ a) :
    ∀ p, coordRearrange b c j hb F p ≤ a := by
  intro p
  let e := sliceEquiv b c j hb
  change rearrange _ _ _ (onSlice b c j hb F) (e p) ≤ a
  have h := rearrange_le_candidate (baseRegion b c j) (length b c j)
    (continuous_length b c j).continuousOn (onSlice b c j hb F) (e p) 0 (by norm_num)
    (by simpa only [zero_add] using (e p).property.2.2)
  exact h.trans (max_le (hF _) (hF _))

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
variable {m N : ℕ} (j : Fin m)
open MeasureTheory

theorem measurePreserving_split : MeasurePreserving (split j) := by
  let : Unique {i : Fin m // ¬ i ≠ j} :=
    { default := ⟨j, by simp⟩
      uniq := fun i => Subtype.ext (by simpa using i.property) }
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin m => ℝ) (fun i => i ≠ j)
  have h₂ := (MeasurePreserving.id (volume : Measure (Base j))).prod
    (volume_preserving_piUnique (fun _ : {i : Fin m // ¬ i ≠ j} => ℝ))
  exact h₂.comp h₁

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Comparison
open MeasureTheory
variable {E : Type*} [TopologicalSpace E] [T2Space E]
variable [MeasurableSpace E] [BorelSpace E]

def zeroExtend (S : Set E) (F : C(S, ℝ)) (x : E) : ℝ :=
  if hx : x ∈ S then F ⟨x, hx⟩ else 0

omit [T2Space E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem zeroExtend_coe (S : Set E) (F : C(S, ℝ)) (x : S) :
    zeroExtend S F x = F x := by simp [zeroExtend, x.property]

omit [T2Space E] in
theorem zeroExtend_measurable (S : Set E) (hS : MeasurableSet S) (F : C(S, ℝ)) :
    Measurable (zeroExtend S F) :=
  F.continuous.measurable.dite measurable_const hS

omit [T2Space E] [MeasurableSpace E] [BorelSpace E] in
theorem zeroExtend_continuousOn (S : Set E) (F : C(S, ℝ)) :
    ContinuousOn (zeroExtend S F) S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : S.domRestrict (zeroExtend S F) = F := by ext x; exact zeroExtend_coe S F x
  rw [h]
  exact F.continuous

omit [T2Space E] [MeasurableSpace E] [BorelSpace E] in
theorem indicator_zeroExtend (S : Set E) (F : C(S, ℝ)) :
    S.indicator (zeroExtend S F) = zeroExtend S F := by
  ext x
  by_cases hx : x ∈ S <;> simp [Set.indicator, zeroExtend, hx]

theorem zeroExtend_integrable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) (F : C(S, ℝ)) : Integrable (zeroExtend S F) μ := by
  have h := (zeroExtend_continuousOn S F).integrableOn_compact hS (μ := μ)
  have h' := (integrable_indicator_iff hS.measurableSet).mpr h
  rwa [indicator_zeroExtend] at h'

def integralMap (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) : C(S, ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∫ x, zeroExtend S F x ∂μ
  map_add' F G := by
    have heq : zeroExtend S (F+G) = fun x => zeroExtend S F x + zeroExtend S G x := by
      ext x; by_cases hx : x ∈ S <;> simp [zeroExtend, hx]
    rw [heq, integral_add (zeroExtend_integrable μ S hS F) (zeroExtend_integrable μ S hS G)]
  map_smul' a F := by
    have heq : zeroExtend S (a • F) = fun x => a • zeroExtend S F x := by
      ext x; by_cases hx : x ∈ S <;> simp [zeroExtend, hx]
    simp only [heq, integral_smul, RingHom.id_apply]

theorem integralMap_mono (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) (F G : C(S, ℝ)) (hFG : F ≤ G) :
    integralMap μ S hS F ≤ integralMap μ S hS G := by
  apply integral_mono (zeroExtend_integrable μ S hS F) (zeroExtend_integrable μ S hS G)
  intro x
  by_cases hx : x ∈ S
  · simpa [zeroExtend, hx] using hFG ⟨x, hx⟩
  · simp [zeroExtend, hx]

theorem integralMap_const (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (S : Set E) (hS : IsCompact S) (a : ℝ) :
    integralMap μ S hS (ContinuousMap.const _ a) = (μ S).toReal * a := by
  change (∫ x, zeroExtend S (ContinuousMap.const _ a) x ∂μ) = _
  have heq : zeroExtend S (ContinuousMap.const _ a) = S.indicator (fun _ => a) := by
    ext x; by_cases hx : x ∈ S <;> simp [zeroExtend, hx]
  rw [heq, integral_indicator hS.measurableSet, integral_const]
  simp [measureReal_def]

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.Comparison
open MeasureTheory
variable {ι : Type*} [Fintype ι]
variable (Y : Set (ι → ℝ)) (L : (ι → ℝ) → ℝ)

theorem zeroExtend_slice (F : C(Slice Y L, ℝ)) (x : Slice Y L) :
    (fun h => zeroExtend (sliceDomain Y L) F (x.val.1, h)) =
      (Set.Icc 0 (L x.val.1)).indicator (sliceFunction Y L F x) := by
  funext h
  by_cases hh : h ∈ Set.Icc 0 (L x.val.1)
  · rw [Set.indicator_of_mem hh, sliceFunction_eq Y L F x hh]
    exact zeroExtend_coe _ _ (pointAtHeight Y L x h hh)
  · have hz : (x.val.1, h) ∉ sliceDomain Y L := fun hz => hh hz.2
    simp [zeroExtend, hz, Set.indicator_of_notMem hh]

theorem rearrange_integral (hL : ContinuousOn L Y) (hc : ConcaveOn ℝ Y L)
    (hS : IsCompact (sliceDomain Y L))
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc)) :
    integralMap volume (sliceDomain Y L) hS (rearrange Y L hL F.val) =
      integralMap volume (sliceDomain Y L) hS F.val := by
  change (∫ x, zeroExtend (sliceDomain Y L) (rearrange Y L hL F.val) x) =
    ∫ x, zeroExtend (sliceDomain Y L) F.val x
  rw [Measure.volume_eq_prod]
  rw [integral_prod _ (zeroExtend_integrable volume _ hS (rearrange Y L hL F.val)),
    integral_prod _ (zeroExtend_integrable volume _ hS F.val)]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hx : ∃ h, (y,h) ∈ sliceDomain Y L
  · obtain ⟨h, hh⟩ := hx
    let x : Slice Y L := ⟨(y,h), hh⟩
    change (∫ s, zeroExtend (sliceDomain Y L) (rearrange Y L hL F.val) (x.val.1,s)) =
      ∫ s, zeroExtend (sliceDomain Y L) F.val (x.val.1,s)
    rw [zeroExtend_slice, zeroExtend_slice, integral_indicator measurableSet_Icc,
      integral_indicator measurableSet_Icc]
    exact rearrange_slice_integral Y L hL hc F x
  · have hnone (h : ℝ) : (y,h) ∉ sliceDomain Y L := fun hh => hx ⟨h, hh⟩
    simp [zeroExtend, hnone]

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.MomentPolytope
open Comparison MeasureTheory
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
variable [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

include hb in
theorem image_split : split j '' region b c = sliceDomain (baseRegion b c j) (length b c j) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (sliceEquiv b c j hb ⟨p,hp⟩).property
  · intro hx
    refine ⟨assemble j x.1 x.2, (assemble_mem_iff b c j hb x.1 x.2).mpr hx, ?_⟩
    exact (split j).apply_symm_apply x

include hb in
theorem isCompact_sliceDomain (hcomp : IsCompact (region b c)) :
    IsCompact (sliceDomain (baseRegion b c j) (length b c j)) := by
  rw [← image_split b c j hb]
  exact hcomp.image (split j).continuous

theorem zeroExtend_onSlice (F : C(region b c, ℝ)) (p : Moments m) :
    zeroExtend (region b c) F p =
      zeroExtend (sliceDomain (baseRegion b c j) (length b c j)) (onSlice b c j hb F) (split j p) := by
  by_cases hp : p ∈ region b c
  · let x : region b c := ⟨p,hp⟩
    change zeroExtend _ F x = zeroExtend _ (onSlice b c j hb F) (sliceEquiv b c j hb x)
    rw [zeroExtend_coe, zeroExtend_coe]
    exact congrArg F ((sliceEquiv b c j hb).symm_apply_apply x).symm
  · have hs : split j p ∉ sliceDomain (baseRegion b c j) (length b c j) := by
      intro hs
      rw [← image_split b c j hb] at hs
      obtain ⟨q,hq,heq⟩ := hs
      exact hp ((split j).injective heq ▸ hq)
    simp [zeroExtend, hp, hs]

theorem integralMap_onSlice (hcomp : IsCompact (region b c)) (F : C(region b c, ℝ)) :
    integralMap volume (region b c) hcomp F =
      integralMap volume (sliceDomain (baseRegion b c j) (length b c j))
        (isCompact_sliceDomain b c j hb hcomp) (onSlice b c j hb F) := by
  change (∫ p, zeroExtend (region b c) F p) = ∫ x, zeroExtend _ _ x
  simp_rw [zeroExtend_onSlice b c j hb]
  exact (measurePreserving_split j).integral_comp (split j).measurableEmbedding _

theorem coordRearrange_integral (hcomp : IsCompact (region b c))
    (F : ConvexMaps (region b c) (convex_region b c)) :
    integralMap volume (region b c) hcomp (coordRearrange b c j hb F.val) =
      integralMap volume (region b c) hcomp F.val := by
  rw [integralMap_onSlice b c j hb, integralMap_onSlice b c j hb]
  have heq : onSlice b c j hb (coordRearrange b c j hb F.val) =
      rearrange (baseRegion b c j) (length b c j) (continuous_length b c j).continuousOn
        (onSlice b c j hb F.val) := by
    ext x
    exact congrArg (rearrange (baseRegion b c j) (length b c j)
      (continuous_length b c j).continuousOn (onSlice b c j hb F.val))
      ((sliceEquiv b c j hb).apply_symm_apply x)
  rw [heq]
  exact rearrange_integral _ _ _ (concave_length b c j)
    (isCompact_sliceDomain b c j hb hcomp) ⟨_, onSlice_convex b c j hb F⟩

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.MomentPolytope
open Comparison MeasureTheory
variable {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
variable [∀ j, Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)

def successive : List (Fin m) → ConvexMaps (region b c) (convex_region b c) →
    ConvexMaps (region b c) (convex_region b c)
  | [], F => F
  | j::js, F => successive js (coordOperator b c j hb F)

theorem successive_nonexpansive [CompactSpace (region b c)] (js : List (Fin m))
    (F G : ConvexMaps (region b c) (convex_region b c)) :
    dist (successive b c hb js F) (successive b c hb js G) ≤ dist F G := by
  induction js generalizing F G with
  | nil => exact le_rfl
  | cons j js ih =>
    exact (ih _ _).trans (coordRearrange_nonexpansive b c j hb F.val G.val)

theorem successive_mono (js : List (Fin m))
    (F G : ConvexMaps (region b c) (convex_region b c)) (hFG : F.val ≤ G.val) :
    (successive b c hb js F).val ≤ (successive b c hb js G).val := by
  induction js generalizing F G with
  | nil => exact hFG
  | cons j js ih => exact ih _ _ (coordRearrange_mono b c j hb _ _ hFG)

theorem successive_translate (js : List (Fin m))
    (F : ConvexMaps (region b c) (convex_region b c)) (a : ℝ) :
    successive b c hb js (translate F a) = translate (successive b c hb js F) a := by
  induction js generalizing F with
  | nil => rfl
  | cons j js ih =>
    have hd : coordOperator b c j hb (translate F a) = translate (coordOperator b c j hb F) a :=
      Subtype.ext (coordRearrange_add_const b c j hb F.val a)
    simp only [successive, hd, ih]

theorem successive_integral (hcomp : IsCompact (region b c)) (js : List (Fin m))
    (F : ConvexMaps (region b c) (convex_region b c)) :
    integralMap volume (region b c) hcomp (successive b c hb js F).val =
      integralMap volume (region b c) hcomp F.val := by
  induction js generalizing F with
  | nil => rfl
  | cons j js ih =>
    exact (ih _).trans (coordRearrange_integral b c j hb hcomp F)

end PackingSufficiencySupport.MomentPolytope
end

end OAI
