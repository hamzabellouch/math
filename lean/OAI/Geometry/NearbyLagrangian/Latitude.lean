import Mathlib
import OAI.Geometry.NearbyLagrangian.SphereSuspension

namespace OAI

/-! Controlled latitude deformations on split unit spheres. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.RadialTopology
open Set
open scoped Topology

def latitudeCap (c z : ℝ) : ℝ := max (-1) (min 1 (z/c))
def latitude (c : ℝ) (t : unitInterval) (z : ℝ) : ℝ :=
  (1-(t:ℝ))*z + (t:ℝ)*latitudeCap c z

def latitudeRadius (c : ℝ) (t : unitInterval) (z : ℝ) : ℝ :=
  Real.sqrt (1-latitude c t z ^ 2)

lemma latitudeCap_mem (c z : ℝ) : latitudeCap c z ∈ Icc (-1) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma latitudeCap_of_abs_le {c z : ℝ} (hc : 0 < c) (hz : |z| ≤ c) :
    latitudeCap c z = z/c := by
  have hp : z/c ≤ 1 := (div_le_one hc).mpr (le_trans (le_abs_self _) hz)
  have hm : -1 ≤ z/c := (le_div_iff₀ hc).mpr (by
    have h := neg_abs_le z
    linarith)
  simp only [latitudeCap,min_eq_right hp,max_eq_right hm]

lemma latitudeCap_of_le {c z : ℝ} (hc : 0 < c) (hz : c ≤ z) :
    latitudeCap c z = 1 := by
  have h : 1 ≤ z/c := (one_le_div hc).mpr hz
  simp only [latitudeCap,min_eq_left h]
  norm_num

lemma latitudeCap_of_neg_le {c z : ℝ} (hc : 0 < c) (hz : z ≤ -c) :
    latitudeCap c z = -1 := by
  have h : z/c ≤ -1 := (div_le_iff₀ hc).mpr (by linarith)
  have h' : z/c ≤ 1 := h.trans (by norm_num)
  simp only [latitudeCap,min_eq_right h',max_eq_left h]

lemma latitudeCap_sq_of_abs_ge {c z : ℝ} (hc : 0 < c) (hz : c ≤ |z|) :
    latitudeCap c z ^ 2 = 1 := by
  rcases le_or_gt 0 z with hp | hm
  · rw [abs_of_nonneg hp] at hz
    rw [latitudeCap_of_le hc hz]
    norm_num
  · rw [abs_of_neg hm] at hz
    rw [latitudeCap_of_neg_le hc (by linarith)]
    norm_num

lemma latitudeCap_ge_of_nonneg {c z : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : z ≤ latitudeCap c z := by
  apply le_max_of_le_right
  apply le_min hz1
  apply (le_div_iff₀ hc).mpr
  nlinarith [mul_nonneg hz (sub_nonneg.mpr hc1)]

lemma latitudeCap_le_of_nonpos {c z : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hz : z ≤ 0) (hz1 : -1 ≤ z) : latitudeCap c z ≤ z := by
  apply max_le hz1
  apply min_le_of_right_le
  apply (div_le_iff₀ hc).mpr
  nlinarith [mul_nonneg (neg_nonneg.mpr hz) (sub_nonneg.mpr hc1)]

lemma latitude_mem {c z : ℝ} (t : unitInterval) (hz : z ∈ Icc (-1) 1) :
    latitude c t z ∈ Icc (-1) 1 := by
  have hp := latitudeCap_mem c z
  have ht := t.property
  constructor <;> dsimp [latitude]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hz.1),
      mul_nonneg ht.1 (sub_nonneg.mpr hp.1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hz.2),
      mul_nonneg ht.1 (sub_nonneg.mpr hp.2)]

lemma abs_le_latitude {c z : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (t : unitInterval) (hz : |z| ≤ 1) : |z| ≤ |latitude c t z| := by
  rcases le_or_gt 0 z with hp | hm
  · have hcap := latitudeCap_ge_of_nonneg hc hc1 hp (le_abs_self z |>.trans hz)
    have hlat : z ≤ latitude c t z := by
      dsimp [latitude]
      nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr hcap)]
    rw [abs_of_nonneg hp,abs_of_nonneg (hp.trans hlat)]
    exact hlat
  · have hcap := latitudeCap_le_of_nonpos hc hc1 hm.le (by
      have h := neg_abs_le z; linarith)
    have hlat : latitude c t z ≤ z := by
      dsimp [latitude]
      nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr hcap)]
    rw [abs_of_neg hm,abs_of_nonpos (hlat.trans hm.le)]
    linarith

lemma sq_le_latitude_sq {c z : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (t : unitInterval) (hz : |z| ≤ 1) : z^2 ≤ latitude c t z ^2 := by
  have h := abs_le_latitude hc hc1 t hz
  nlinarith [sq_abs z,sq_abs (latitude c t z),abs_nonneg z,
    abs_nonneg (latitude c t z)]

@[simp] lemma latitude_zero (c z : ℝ) : latitude c 0 z = z := by simp [latitude]
@[simp] lemma latitude_one (c z : ℝ) : latitude c 1 z = latitudeCap c z := by simp [latitude]
lemma latitudeRadius_nonneg (c : ℝ) (t : unitInterval) (z : ℝ) :
    0 ≤ latitudeRadius c t z := Real.sqrt_nonneg _

lemma latitudeRadius_sq {c z : ℝ} (t : unitInterval) (hz : |z| ≤ 1) :
    latitudeRadius c t z ^2 + latitude c t z ^2 = 1 := by
  have hl := latitude_mem (c:=c) t (abs_le.mp hz)
  have hn : 0 ≤ 1-latitude c t z ^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl.2) (sub_nonneg.mpr hl.1)]
  rw [latitudeRadius,Real.sq_sqrt hn]
  ring

lemma latitudeRadius_le {c z r : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (t : unitInterval) (hr : 0 ≤ r) (hs : r^2+z^2=1) :
    latitudeRadius c t z ≤ r := by
  have hz : |z| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg r]
  have hsq := latitudeRadius_sq (c:=c) t hz
  have hlat := sq_le_latitude_sq hc hc1 t hz
  have hp := latitudeRadius_nonneg c t z
  nlinarith

lemma latitudeRadius_zero_time {c z r : ℝ} (hr : 0 ≤ r) (hs : r^2+z^2=1) :
    latitudeRadius c 0 z = r := by
  have hz : |z| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg r]
  have hsq := latitudeRadius_sq (c:=c) (0:unitInterval) hz
  rw [latitude_zero] at hsq
  have hp := latitudeRadius_nonneg c (0:unitInterval) z
  nlinarith

lemma latitudeRadius_one_eq_zero {c z : ℝ} (hc : 0 < c) (hz : c ≤ |z|) :
    latitudeRadius c 1 z = 0 := by
  rw [latitudeRadius,latitude_one,latitudeCap_sq_of_abs_ge hc hz]
  norm_num

lemma continuous_latitudeCap (c : ℝ) : Continuous (latitudeCap c) := by
  unfold latitudeCap
  fun_prop

lemma continuous_latitude (c : ℝ) :
    Continuous (fun p : unitInterval × ℝ => latitude c p.1 p.2) := by
  unfold latitude latitudeCap
  fun_prop

lemma continuous_latitudeRadius (c : ℝ) :
    Continuous (fun p : unitInterval × ℝ => latitudeRadius c p.1 p.2) := by
  unfold latitudeRadius
  exact (continuous_const.sub ((continuous_latitude c).pow 2)).sqrt

end NearbyLagrangian.RadialTopology

namespace NearbyLagrangian.RadialTopology
open Set
open scoped Topology
variable {B W : Type*} [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace ℝ W]

abbrev NormSphere (W : Type*) [NormedAddCommGroup W] := {w : W // ‖w‖ = 1}
abbrev SplitSphere (B W : Type*) [NormedAddCommGroup W] :=
  {p : B × (W × ℝ) // ‖p.2.1‖ ^ 2 + p.2.2 ^ 2 = 1}

def splitSphereProjection : C(SplitSphere B W,B) :=
  ⟨fun p => p.val.1,continuous_fst.comp continuous_subtype_val⟩

omit [TopologicalSpace B] [NormedSpace ℝ W] in
lemma splitSphere_abs_latitude (p : SplitSphere B W) : |p.val.2.2| ≤ 1 := by
  have h := p.property
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ‖p.val.2.1‖]

def splitNormalize (p : SplitSphere B W) (h : p.val.2.1 ≠ 0) : NormSphere W :=
  ⟨NormedSpace.normalize p.val.2.1,NormedSpace.norm_normalize_eq_one_iff.mpr h⟩

omit [TopologicalSpace B] [NormedSpace ℝ W] in
lemma splitOrigin_ne_of_radius_ne {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (q : unitInterval × SplitSphere B W) (hq : latitudeRadius c q.1 q.2.val.2.2 ≠ 0) :
    q.2.val.2.1 ≠ 0 := by
  intro h
  apply hq
  have hle := latitudeRadius_le hc hc1 q.1 (norm_nonneg q.2.val.2.1) q.2.property
  rw [h,norm_zero] at hle
  exact le_antisymm hle (latitudeRadius_nonneg _ _ _)

abbrev SplitNonzeroRadius (c : ℝ) :=
  {q : unitInterval × SplitSphere B W // latitudeRadius c q.1 q.2.val.2.2 ≠ 0}

def latitudeAngle {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W)) :
    C(SplitNonzeroRadius (B:=B) (W:=W) c,NormSphere W) where
  toFun q := H (q.val.1,(q.val.2.val.1,
    splitNormalize q.val.2 (splitOrigin_ne_of_radius_ne hc hc1 q.val q.property)))
  continuous_toFun := by
    have hv : Continuous (fun q : SplitNonzeroRadius (B:=B) (W:=W) c => q.val.2.val) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
    have hnorm : ∀ q : SplitNonzeroRadius (B:=B) (W:=W) c, ‖q.val.2.val.2.1‖ ≠ 0 :=
      fun q => norm_ne_zero_iff.mpr (splitOrigin_ne_of_radius_ne hc hc1 q.val q.property)
    have hu : Continuous (fun q : SplitNonzeroRadius (B:=B) (W:=W) c =>
        splitNormalize q.val.2 (splitOrigin_ne_of_radius_ne hc hc1 q.val q.property)) :=
      ((hv.snd.fst.norm.inv₀ hnorm).smul hv.snd.fst).subtype_mk _
    exact H.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      (hv.fst.prodMk hu))

def flowRadiusVector {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (q : unitInterval × SplitSphere B W) : W :=
  radialLift (fun q : unitInterval × SplitSphere B W => latitudeRadius c q.1 q.2.val.2.2)
    (fun q => (latitudeAngle hc hc1 H q).val) q

lemma norm_flowRadiusVector {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (q : unitInterval × SplitSphere B W) :
    ‖flowRadiusVector hc hc1 H q‖ = latitudeRadius c q.1 q.2.val.2.2 := by
  unfold flowRadiusVector
  rw [norm_radialLift _ _ (fun q => (latitudeAngle hc hc1 H q).property),
    abs_of_nonneg (latitudeRadius_nonneg _ _ _)]

lemma continuous_flowRadiusVector {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W)) :
    Continuous (flowRadiusVector hc hc1 H) := by
  unfold flowRadiusVector
  apply continuous_radialLift
  · exact (continuous_latitudeRadius c).comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).snd.snd))
  · exact continuous_subtype_val.comp (latitudeAngle hc hc1 H).continuous
  · intro q
    exact (latitudeAngle hc hc1 H q).property.le

lemma flowRadiusVector_of_nonzero {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (q : unitInterval × SplitSphere B W) (hq : q.2.val.2.1 ≠ 0) :
    flowRadiusVector hc hc1 H q = latitudeRadius c q.1 q.2.val.2.2 •
      (H (q.1,(q.2.val.1,splitNormalize q.2 hq))).val := by
  by_cases hr : latitudeRadius c q.1 q.2.val.2.2 = 0
  · have hv : flowRadiusVector hc hc1 H q = 0 := by
      apply norm_eq_zero.mp
      rw [norm_flowRadiusVector,hr]
    rw [hv,hr,zero_smul]
  · unfold flowRadiusVector
    rw [radialLift_of_ne_zero (fun p : unitInterval × SplitSphere B W =>
      latitudeRadius c p.1 p.2.val.2.2) _ (x:=q) hr]
    rfl

lemma flowRadiusVector_of_zero {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (q : unitInterval × SplitSphere B W) (hq : q.2.val.2.1 = 0) :
    flowRadiusVector hc hc1 H q = 0 := by
  apply norm_eq_zero.mp
  rw [norm_flowRadiusVector]
  have hle := latitudeRadius_le hc hc1 q.1 (norm_nonneg q.2.val.2.1) q.2.property
  rw [hq,norm_zero] at hle
  exact le_antisymm hle (latitudeRadius_nonneg _ _ _)

def latitudeDeform {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W)) :
    C(unitInterval × SplitSphere B W,SplitSphere B W) where
  toFun q := ⟨(q.2.val.1,flowRadiusVector hc hc1 H q,latitude c q.1 q.2.val.2.2),by
    rw [norm_flowRadiusVector]
    exact latitudeRadius_sq q.1 (splitSphere_abs_latitude _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hv : Continuous (fun q : unitInterval × SplitSphere B W => q.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact hv.fst.prodMk ((continuous_flowRadiusVector hc hc1 H).prodMk
      ((continuous_latitude c).comp (continuous_fst.prodMk hv.snd.snd)))

@[simp] lemma latitudeDeform_base {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (q : unitInterval × SplitSphere B W) :
    (latitudeDeform hc hc1 H q).val.1 = q.2.val.1 := rfl

lemma latitudeDeform_zero {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (hH : ∀ b u, H (0,(b,u)) = u) (q : SplitSphere B W) :
    latitudeDeform hc hc1 H (0,q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change flowRadiusVector hc hc1 H (0,q) = q.val.2.1
    by_cases hq : q.val.2.1 = 0
    · exact (flowRadiusVector_of_zero hc hc1 H _ hq).trans hq.symm
    · rw [flowRadiusVector_of_nonzero hc hc1 H _ hq,
        latitudeRadius_zero_time (norm_nonneg _) q.property,hH]
      exact NormedSpace.norm_smul_normalize _
  · exact latitude_zero c q.val.2.2

end NearbyLagrangian.RadialTopology

end

end OAI
