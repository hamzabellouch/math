import Mathlib
import OAI.Geometry.NearbyLagrangian.NegativeSuspension

namespace OAI

/-! Retraction and homotopy equivalence after adding a positive square. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.RadialTopology
open Set
open scoped Topology
variable {B W : Type*} [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace ℝ W]

abbrev PositiveSplit (f : B → W → ℝ) :=
  {p : SplitSphere B W // f p.val.1 p.val.2.1+p.val.2.2^2 ≤ 0}

def positiveSplitProjection (f : B → W → ℝ) : C(PositiveSplit f,B) :=
  ⟨fun p => p.val.val.1,continuous_fst.comp
    (continuous_subtype_val.comp continuous_subtype_val)⟩

omit [TopologicalSpace B] in
lemma positiveOrigin_ne {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    (p : PositiveSplit f) : p.val.val.2.1 ≠ 0 := by
  intro hz
  have hs := p.val.property
  have hn := p.property
  rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add] at hs
  rw [hz,degreeTwo_zero hhom,zero_add,hs] at hn
  norm_num at hn

def positiveInclusion (f : B → W → ℝ) : C((negativeSphere f).Total,PositiveSplit f) where
  toFun p := ⟨⟨(p.val.1,p.val.2,0),by simp [p.property.1]⟩,by
    simpa only [zero_pow (by decide : 2 ≠ 0),add_zero] using p.property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).prodMk continuous_const)

def positiveRetraction {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w) :
    C(PositiveSplit f,(negativeSphere f).Total) where
  toFun p := ⟨(p.val.val.1,NormedSpace.normalize p.val.val.2.1),by
    refine ⟨NormedSpace.norm_normalize_eq_one_iff.mpr (positiveOrigin_ne hhom p),?_⟩
    have hn : f p.val.val.1 p.val.val.2.1 ≤ 0 := by
      have h := p.property
      nlinarith [sq_nonneg p.val.val.2.2]
    rw [degreeTwo_normalized hhom p.val (positiveOrigin_ne hhom p)] at hn
    exact nonpos_of_mul_nonpos_right hn
      (sq_pos_of_pos (norm_pos_iff.mpr (positiveOrigin_ne hhom p)))⟩
  continuous_toFun := by
    have hv : Continuous (fun p : PositiveSplit f => p.val.val) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (hv.fst.prodMk ((hv.snd.fst.norm.inv₀
      (fun p => norm_ne_zero_iff.mpr (positiveOrigin_ne hhom p))).smul hv.snd.fst)).subtype_mk _

lemma positiveRetraction_inclusion {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    (p : (negativeSphere f).Total) : positiveRetraction hhom (positiveInclusion f p) = p := by
  apply Subtype.ext
  change (p.val.1,NormedSpace.normalize p.val.2) = p.val
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one p.property.1]

omit [TopologicalSpace B] [NormedSpace ℝ W] in
def positiveDenom {f : B → W → ℝ} (t : unitInterval) (p : PositiveSplit f) : ℝ :=
  Real.sqrt (‖p.val.val.2.1‖^2+((1-(t:ℝ))*p.val.val.2.2)^2)

omit [TopologicalSpace B] in
lemma positiveDenom_pos {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    (t : unitInterval) (p : PositiveSplit f) : 0 < positiveDenom t p := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_pos_of_nonneg
    (sq_pos_of_pos (norm_pos_iff.mpr (positiveOrigin_ne hhom p))) (sq_nonneg _)

omit [TopologicalSpace B] [NormedSpace ℝ W] in
lemma positiveDenom_sq {f : B → W → ℝ} (t : unitInterval) (p : PositiveSplit f) :
    positiveDenom t p ^2 = ‖p.val.val.2.1‖^2+((1-(t:ℝ))*p.val.val.2.2)^2 := by
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

omit [NormedSpace ℝ W] in
lemma continuous_positiveDenom {f : B → W → ℝ} :
    Continuous (fun q : unitInterval × PositiveSplit f => positiveDenom q.1 q.2) := by
  have hv : Continuous (fun q : unitInterval × PositiveSplit f => q.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact Real.continuous_sqrt.comp ((hv.snd.fst.norm.pow 2).add
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hv.snd.snd).pow 2))

omit [TopologicalSpace B] [NormedSpace ℝ W] in
lemma positiveDenom_zero {f : B → W → ℝ} (p : PositiveSplit f) : positiveDenom 0 p = 1 := by
  simp [positiveDenom,p.val.property]

omit [TopologicalSpace B] [NormedSpace ℝ W] in
lemma positiveDenom_one {f : B → W → ℝ} (p : PositiveSplit f) : positiveDenom 1 p = ‖p.val.val.2.1‖ := by
  simp [positiveDenom]

omit [TopologicalSpace B] in
lemma positiveDeform_sphere {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    (t : unitInterval) (p : PositiveSplit f) :
    ‖(positiveDenom t p)⁻¹ • p.val.val.2.1‖^2+
      ((positiveDenom t p)⁻¹*((1-(t:ℝ))*p.val.val.2.2))^2 = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (positiveDenom_pos hhom t p))]
  calc
    _ = (positiveDenom t p)⁻¹^2 * (‖p.val.val.2.1‖^2+
      ((1-(t:ℝ))*p.val.val.2.2)^2) := by ring
    _ = 1 := by rw [← positiveDenom_sq]; field_simp [(positiveDenom_pos hhom t p).ne']

omit [TopologicalSpace B] in
lemma positiveDeform_nonpositive {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    (t : unitInterval) (p : PositiveSplit f) :
    f p.val.val.1 ((positiveDenom t p)⁻¹ • p.val.val.2.1)+
      ((positiveDenom t p)⁻¹*((1-(t:ℝ))*p.val.val.2.2))^2 ≤ 0 := by
  rw [hhom _ _ (inv_nonneg.mpr (positiveDenom_pos hhom t p).le)]
  have ha : 0 ≤ 1-(t:ℝ) := sub_nonneg.mpr t.property.2
  have ha1 : 1-(t:ℝ) ≤ 1 := by linarith [t.property.1]
  have hs : ((1-(t:ℝ))*p.val.val.2.2)^2 ≤ p.val.val.2.2^2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
  calc
    _ = (positiveDenom t p)⁻¹^2 * (f p.val.val.1 p.val.val.2.1+
      ((1-(t:ℝ))*p.val.val.2.2)^2) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith [p.property])

def positiveDeform {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w) :
    C(unitInterval × PositiveSplit f,PositiveSplit f) where
  toFun q := ⟨⟨(q.2.val.val.1,(positiveDenom q.1 q.2)⁻¹ • q.2.val.val.2.1,
    (positiveDenom q.1 q.2)⁻¹*((1-(q.1:ℝ))*q.2.val.val.2.2)),
    positiveDeform_sphere hhom q.1 q.2⟩,positiveDeform_nonpositive hhom q.1 q.2⟩
  continuous_toFun := by
    have hv : Continuous (fun q : unitInterval × PositiveSplit f => q.2.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have hi := continuous_positiveDenom.inv₀ (fun q => (positiveDenom_pos hhom q.1 q.2).ne')
    exact (hv.fst.prodMk ((hi.smul hv.snd.fst).prodMk
      (hi.mul ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hv.snd.snd)))).subtype_mk _ |>.subtype_mk _

lemma positiveDeform_zero {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w) (p : PositiveSplit f) :
    positiveDeform hhom (0,p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  change (p.val.val.1,(positiveDenom 0 p)⁻¹ • p.val.val.2.1,
    (positiveDenom 0 p)⁻¹*((1-(0:ℝ))*p.val.val.2.2)) = p.val.val
  rw [positiveDenom_zero]
  simp

lemma positiveDeform_one {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w) (p : PositiveSplit f) :
    positiveDeform hhom (1,p) = positiveInclusion f (positiveRetraction hhom p) := by
  apply Subtype.ext
  apply Subtype.ext
  change (p.val.val.1,(positiveDenom 1 p)⁻¹ • p.val.val.2.1,
    (positiveDenom 1 p)⁻¹*((1-(1:ℝ))*p.val.val.2.2)) =
    (p.val.val.1,NormedSpace.normalize p.val.val.2.1,0)
  rw [positiveDenom_one]
  simp [NormedSpace.normalize]

def positiveSquareEquiv {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w) :
    Tubes.FiberwiseHomotopyEquiv (negativeSphere f).projection (positiveSplitProjection f) where
  toFun := positiveInclusion f
  invFun := positiveRetraction hhom
  toFun_over _ := rfl
  invFun_over _ := rfl
  left := (ContinuousMap.Homotopy.refl (ContinuousMap.id (negativeSphere f).Total)).cast
    (by apply ContinuousMap.ext; intro p; exact (positiveRetraction_inclusion hhom p).symm) rfl
  right := (show (ContinuousMap.id (PositiveSplit f)).Homotopy
      ((positiveInclusion f).comp (positiveRetraction hhom)) from {
    toContinuousMap := positiveDeform hhom
    map_zero_left := positiveDeform_zero hhom
    map_one_left := positiveDeform_one hhom }).symm
  left_over _ _ := rfl
  right_over _ _ := rfl

end NearbyLagrangian.RadialTopology

end

end OAI
