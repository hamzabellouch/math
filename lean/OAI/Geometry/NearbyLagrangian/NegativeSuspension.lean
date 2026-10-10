import Mathlib
import OAI.Geometry.NearbyLagrangian.NegativeEquivalence
import OAI.Geometry.NearbyLagrangian.Latitude

namespace OAI

/-! Suspension equivalences for negative domains of homogeneous functions. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.RadialTopology
open Set
open scoped Topology
variable {B W : Type*} [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace ℝ W]

def negativeSphere (f : B → W → ℝ) : SphereFamily B W where
  carrier := {p | ‖p.2‖ = 1 ∧ f p.1 p.2 ≤ 0}
  unit _ h := h.1

abbrev NegativeSplit (f : B → W → ℝ) :=
  {p : SplitSphere B W // f p.val.1 p.val.2.1 ≤ p.val.2.2 ^2}

def negativeSplitProjection (f : B → W → ℝ) : C(NegativeSplit f,B) :=
  ⟨fun p => p.val.val.1,continuous_fst.comp
    (continuous_subtype_val.comp continuous_subtype_val)⟩

omit [TopologicalSpace B] in
lemma degreeTwo_zero {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2 * f b w) (b : B) :
    f b 0 = 0 := by
  have h := hhom b 0 le_rfl 0
  simpa only [zero_smul,zero_pow (by decide : 2 ≠ 0),zero_mul] using h

omit [TopologicalSpace B] in
lemma degreeTwo_normalized {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2 * f b w)
    (p : SplitSphere B W) (hp : p.val.2.1 ≠ 0) :
    f p.val.1 p.val.2.1 = ‖p.val.2.1‖^2 * f p.val.1 (splitNormalize p hp) := by
  have h := hhom p.val.1 ‖p.val.2.1‖ (norm_nonneg _) (splitNormalize p hp)
  rw [show ‖p.val.2.1‖ • (splitNormalize p hp : W) = p.val.2.1 from
    NormedSpace.norm_smul_normalize _] at h
  exact h

omit [TopologicalSpace B] in

lemma negativeSplit_angular_band {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2 * f b w)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) (hce : c^2*(1+ε) ≤ ε)
    (p : NegativeSplit f) (hp : p.val.val.2.1 ≠ 0) (hz : |p.val.val.2.2| ≤ c) :
    f p.val.val.1 (splitNormalize p.val hp) ≤ ε := by
  have hn : 0 < ‖p.val.val.2.1‖ ^2 := sq_pos_of_pos (norm_pos_iff.mpr hp)
  have hzsq : p.val.val.2.2 ^2 ≤ c^2 := by
    nlinarith [sq_abs p.val.val.2.2,abs_nonneg p.val.val.2.2]
  apply le_of_mul_le_mul_left _ hn
  calc
    ‖p.val.val.2.1‖^2 * f p.val.val.1 (splitNormalize p.val hp) =
        f p.val.val.1 p.val.val.2.1 := (degreeTwo_normalized hhom p.val hp).symm
    _ ≤ p.val.val.2.2 ^2 := p.property
    _ ≤ ‖p.val.val.2.1‖^2 * ε := by
      have hs := p.val.property
      nlinarith [mul_nonneg (sub_nonneg.mpr hzsq) (show 0 ≤ 1+ε by linarith)]

lemma latitudeDeform_negative {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2 * f b w)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (hdec : ∀ t b u, f b (H (t,(b,u))) ≤ f b u)
    (t : unitInterval) (p : NegativeSplit f) :
    f (latitudeDeform hc hc1 H (t,p.val)).val.1
      (latitudeDeform hc hc1 H (t,p.val)).val.2.1 ≤
      (latitudeDeform hc hc1 H (t,p.val)).val.2.2 ^2 := by
  change f p.val.val.1 (flowRadiusVector hc hc1 H (t,p.val)) ≤
    latitude c t p.val.val.2.2 ^2
  by_cases hp : p.val.val.2.1 = 0
  · rw [flowRadiusVector_of_zero hc hc1 H _ hp,degreeTwo_zero hhom]
    positivity
  · rw [flowRadiusVector_of_nonzero hc hc1 H _ hp,
      hhom _ _ (latitudeRadius_nonneg _ _ _)]
    have hd := hdec t p.val.val.1 (splitNormalize p.val hp)
    have hr := latitudeRadius_le hc hc1 t (norm_nonneg p.val.val.2.1) p.val.property
    have hr0 := latitudeRadius_nonneg c t p.val.val.2.2
    have hz := sq_le_latitude_sq hc hc1 t (splitSphere_abs_latitude p.val)
    rcases le_or_gt (f p.val.val.1 (splitNormalize p.val hp)) 0 with hneg | hpos
    · exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hd.trans hneg)).trans
        (sq_nonneg _)
    · calc
        latitudeRadius c t p.val.val.2.2 ^2 * f p.val.val.1 (H _) ≤
            latitudeRadius c t p.val.val.2.2 ^2 * f p.val.val.1 (splitNormalize p.val hp) :=
          mul_le_mul_of_nonneg_left hd (sq_nonneg _)
        _ ≤ ‖p.val.val.2.1‖^2 * f p.val.val.1 (splitNormalize p.val hp) := by
          apply mul_le_mul_of_nonneg_right _ hpos.le
          nlinarith [norm_nonneg p.val.val.2.1]
        _ = f p.val.val.1 p.val.val.2.1 := (degreeTwo_normalized hhom p.val hp).symm
        _ ≤ p.val.val.2.2 ^2 := p.property
        _ ≤ latitude c t p.val.val.2.2 ^2 := hz

lemma latitudeDeform_nonpositive {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2 * f b w)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (hdec : ∀ t b u, f b (H (t,(b,u))) ≤ f b u)
    (t : unitInterval) (p : SplitSphere B W) (hneg : f p.val.1 p.val.2.1 ≤ 0) :
    f (latitudeDeform hc hc1 H (t,p)).val.1
      (latitudeDeform hc hc1 H (t,p)).val.2.1 ≤ 0 := by
  change f p.val.1 (flowRadiusVector hc hc1 H (t,p)) ≤ 0
  by_cases hp : p.val.2.1 = 0
  · rw [flowRadiusVector_of_zero hc hc1 H _ hp,degreeTwo_zero hhom]
  · rw [flowRadiusVector_of_nonzero hc hc1 H _ hp,
      hhom _ _ (latitudeRadius_nonneg _ _ _)]
    have ha : f p.val.1 (splitNormalize p hp) ≤ 0 := by
      rw [degreeTwo_normalized hhom p hp] at hneg
      exact nonpos_of_mul_nonpos_right hneg (sq_pos_of_pos (norm_pos_iff.mpr hp))
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) ((hdec _ _ _).trans ha)

lemma latitudeDeform_endpoint_nonpositive {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2 * f b w)
    {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 ≤ ε) (hce : c^2*(1+ε) ≤ ε)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (hpush : ∀ b (u : NormSphere W), f b u ≤ ε → f b (H (1,(b,u))) ≤ 0)
    (p : NegativeSplit f) :
    f (latitudeDeform hc hc1 H (1,p.val)).val.1
      (latitudeDeform hc hc1 H (1,p.val)).val.2.1 ≤ 0 := by
  change f p.val.val.1 (flowRadiusVector hc hc1 H (1,p.val)) ≤ 0
  by_cases hp : p.val.val.2.1 = 0
  · rw [flowRadiusVector_of_zero hc hc1 H _ hp,degreeTwo_zero hhom]
  · rw [flowRadiusVector_of_nonzero hc hc1 H _ hp,
      hhom _ _ (latitudeRadius_nonneg _ _ _)]
    by_cases hz : c ≤ |p.val.val.2.2|
    · rw [latitudeRadius_one_eq_zero hc hz]
      simp only [zero_pow (by decide : 2 ≠ 0),zero_mul,le_refl]
    · exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
        (hpush _ _ (negativeSplit_angular_band hhom hc hε hce p hp (le_of_lt (lt_of_not_ge hz))))

omit [TopologicalSpace B] in
lemma suspension_split_equation (f : B → W → ℝ) (p : (negativeSphere f).Suspension ℝ) :
    ‖p.val.2.1‖^2+p.val.2.2^2=1 := by
  simpa only [Real.norm_eq_abs,sq_abs] using p.property.2

def suspensionSplit (f : B → W → ℝ) :
    C((negativeSphere f).Suspension ℝ,SplitSphere B W) where
  toFun p := ⟨p.val,suspension_split_equation f p⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

lemma suspensionSplit_nonpositive {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    (p : (negativeSphere f).Suspension ℝ) :
    f p.val.1 p.val.2.1 ≤ 0 := by
  rcases p.property.1 with hz | hn
  · rw [hz,degreeTwo_zero hhom]
  · by_cases hz : p.val.2.1 = 0
    · rw [hz,degreeTwo_zero hhom]
    · change f (suspensionSplit f p).val.1 (suspensionSplit f p).val.2.1 ≤ 0
      rw [degreeTwo_normalized hhom (suspensionSplit f p) hz]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hn.2

omit [TopologicalSpace B] in
lemma split_mem_suspension {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    (p : SplitSphere B W) (hp : f p.val.1 p.val.2.1 ≤ 0) :
    (p.val.2.1 = 0 ∨ (p.val.1,NormedSpace.normalize p.val.2.1) ∈
      (negativeSphere f).carrier) ∧ ‖p.val.2.1‖^2+‖p.val.2.2‖^2 = 1 := by
  constructor
  · by_cases hz : p.val.2.1 = 0
    · exact Or.inl hz
    · right
      refine ⟨NormedSpace.norm_normalize_eq_one_iff.mpr hz,?_⟩
      rw [degreeTwo_normalized hhom p hz] at hp
      exact nonpos_of_mul_nonpos_right hp (sq_pos_of_pos (norm_pos_iff.mpr hz))
  · simpa only [Real.norm_eq_abs,sq_abs] using p.property

def suspensionNegativeInclusion {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w) :
    C((negativeSphere f).Suspension ℝ,NegativeSplit f) where
  toFun p := ⟨suspensionSplit f p,(suspensionSplit_nonpositive hhom p).trans (sq_nonneg _)⟩
  continuous_toFun := (suspensionSplit f).continuous.subtype_mk _

def negativeLatitudeDeform {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (hdec : ∀ t b u, f b (H (t,(b,u))) ≤ f b u) :
    C(unitInterval × NegativeSplit f,NegativeSplit f) where
  toFun q := ⟨latitudeDeform hc hc1 H (q.1,q.2.val),
    latitudeDeform_negative hhom hc hc1 H hdec q.1 q.2⟩
  continuous_toFun := ((latitudeDeform hc hc1 H).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

def suspensionLatitudeDeform {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (hdec : ∀ t b u, f b (H (t,(b,u))) ≤ f b u) :
    C(unitInterval × (negativeSphere f).Suspension ℝ,(negativeSphere f).Suspension ℝ) where
  toFun q := ⟨(latitudeDeform hc hc1 H (q.1,suspensionSplit f q.2)).val,
    split_mem_suspension hhom _ (latitudeDeform_nonpositive hhom hc hc1 H hdec q.1
      (suspensionSplit f q.2) (suspensionSplit_nonpositive hhom q.2))⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((latitudeDeform hc hc1 H).continuous.comp
      (continuous_fst.prodMk ((suspensionSplit f).continuous.comp continuous_snd)))).subtype_mk _

def negativeSuspensionRetraction {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 ≤ ε) (hce : c^2*(1+ε) ≤ ε)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (hpush : ∀ b (u : NormSphere W), f b u ≤ ε → f b (H (1,(b,u))) ≤ 0) :
    C(NegativeSplit f,(negativeSphere f).Suspension ℝ) where
  toFun p := ⟨(latitudeDeform hc hc1 H (1,p.val)).val,
    split_mem_suspension hhom _
      (latitudeDeform_endpoint_nonpositive hhom hc hc1 hε hce H hpush p)⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((latitudeDeform hc hc1 H).continuous.comp
      (continuous_const.prodMk continuous_subtype_val))).subtype_mk _

def negativeSuspensionEquiv {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 ≤ ε) (hce : c^2*(1+ε) ≤ ε)
    (H : C(unitInterval × (B × NormSphere W),NormSphere W))
    (hzero : ∀ b u, H (0,(b,u)) = u)
    (hdec : ∀ t b u, f b (H (t,(b,u))) ≤ f b u)
    (hpush : ∀ b (u : NormSphere W), f b u ≤ ε → f b (H (1,(b,u))) ≤ 0) :
    Tubes.FiberwiseHomotopyEquiv ((negativeSphere f).suspensionProjection (Z:=ℝ))
      (negativeSplitProjection f) where
  toFun := suspensionNegativeInclusion hhom
  invFun := negativeSuspensionRetraction hhom hc hc1 hε hce H hpush
  toFun_over _ := rfl
  invFun_over _ := rfl
  left := (show (ContinuousMap.id ((negativeSphere f).Suspension ℝ)).Homotopy
      ((negativeSuspensionRetraction hhom hc hc1 hε hce H hpush).comp
        (suspensionNegativeInclusion hhom)) from {
    toContinuousMap := suspensionLatitudeDeform hhom hc hc1 H hdec
    map_zero_left := by
      intro p
      apply Subtype.ext
      change (latitudeDeform hc hc1 H (0,suspensionSplit f p)).val = p.val
      exact congrArg (fun x : SplitSphere B W => x.val)
        (latitudeDeform_zero hc hc1 H hzero (suspensionSplit f p))
    map_one_left := by intro p; rfl
    }).symm
  right := (show (ContinuousMap.id (NegativeSplit f)).Homotopy
      ((suspensionNegativeInclusion hhom).comp
        (negativeSuspensionRetraction hhom hc hc1 hε hce H hpush)) from {
    toContinuousMap := negativeLatitudeDeform hhom hc hc1 H hdec
    map_zero_left := by
      intro p
      apply Subtype.ext
      exact latitudeDeform_zero hc hc1 H hzero p.val
    map_one_left := by intro p; rfl
    }).symm
  left_over _ _ := rfl
  right_over _ _ := rfl

end NearbyLagrangian.RadialTopology

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter Metric
open scoped Topology InnerProductSpace ContDiff NNReal Manifold
open RadialTopology
variable {E W B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace B] [CompactSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℝ,E) ∞ B]

theorem exists_angularDescent {g : B → RegularHomogeneous W}
    (hg : SmoothFamily (E:=E) g) {c : ℝ} (hc : 0 < c)
    (hgrad : ∀ b w, ‖w‖ = 1 → c ≤ ‖gradient (g b) w‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : C(unitInterval × (B × NormSphere W),NormSphere W),
      (∀ b u, H (0,(b,u)) = u) ∧
      (∀ t b u, g b (H (t,(b,u))) ≤ g b u) ∧
      (∀ b (u : NormSphere W), g b u ≤ ε → g b (H (1,(b,u))) ≤ 0) := by
  let F : B × W → W := fun p => (g p.1).tangentBandField c hc p.2
  have hF : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,W)) 𝓘(ℝ,W) ∞ F :=
    contMDiff_tangentBandField hg hc
  have hFs (b : B) : Differentiable ℝ (fun w => F (b,w)) := by
    have h := hF.comp ((contMDiff_const (c:=b)).prodMk (contMDiff_id (I:=𝓘(ℝ,W))))
    exact (contMDiff_iff_contDiff.mp h).differentiable (by simp)
  have hD : Continuous (fun p : B × W => fderiv ℝ (fun w => F (p.1,w)) p.2) :=
    (contMDiff_family_spatial_fderiv hF).continuous
  obtain ⟨L,K,hL,hK⟩ := ODE.param_compact_field_bounds hF.continuous hFs hD
    (R:=3) (fun b w hw => (g b).tangentBandField_zero hc hw)
  obtain ⟨φ⟩ := ODE.exists_paramCompleteFlow F hF.continuous hL hK
  have hS (b : B) (w : W) (hw : ‖w‖ = 1) (t : ℝ) :
      ‖φ.toFun ((b,w),t)‖ = 1 := by
    change ‖(φ.specialize b).toFun (w,t)‖ = 1
    rw [(φ.specialize b).norm_eq (fun w => (g b).tangentBandField_radial hc w),hw]
  let ε := c/32
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hgT (b : B) (w : W) (hw : ‖w‖ = 1) :
      0 ≤ fderiv ℝ (g b) w (F (b,w)) ∧
      (|g b w| ≤ ε → c^2/4 ≤ fderiv ℝ (g b) w (F (b,w))) :=
    tangentBandField_transverse hc le_rfl hw (hgrad b w hw)
      (by simpa only [sub_self,abs_zero] using hε.le)
      (by simpa only [sub_self,norm_zero] using hε.le)
  let δ := 8*ε/c^2
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have htime : 2*ε ≤ (c^2/4)*δ := by
    have he : (c^2/4)*δ = 2*ε := by dsimp [δ]; field_simp [hc.ne']; ring
    rw [he]
  let H : C(unitInterval × (B × NormSphere W),NormSphere W) := {
    toFun q := ⟨φ.toFun ((q.2.1,q.2.2.val),-(q.1:ℝ)*δ),hS _ _ q.2.2.property _⟩
    continuous_toFun := (φ.continuous_toFun.comp
      (((continuous_fst.comp continuous_snd).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).prodMk
          ((continuous_subtype_val.comp continuous_fst).neg.mul continuous_const))).subtype_mk _ }
  refine ⟨ε,hε,H,?_,?_,?_⟩
  · intro b u
    apply Subtype.ext
    change φ.toFun ((b,u.val),-(0:ℝ)*δ) = u.val
    rw [neg_zero,zero_mul,φ.initial]
  · intro t b u
    have hmono := (φ.specialize b).observable_monotone (g b).differentiable
      (S:={w : W | ‖w‖=1}) (hS b) (fun w hw => (hgT b w hw).1) u.property
    change g b (φ.toFun ((b,u.val),-(t:ℝ)*δ)) ≤ g b u.val
    have hneg : -(t:ℝ)*δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.property.1) hδ
    simpa only [ODE.ParamCompleteFlow.specialize,φ.initial] using hmono hneg
  · intro b u hu
    have hp := (φ.specialize b).push_sublevel (g b).differentiable
      (S:={w : W | ‖w‖=1}) (hS b) (fun w hw => (hgT b w hw).1) hδ htime
      (fun w hw => (hgT b w hw).2) u.property hu
    change g b (φ.toFun ((b,u.val),-(1:ℝ)*δ)) ≤ 0
    change g b (φ.toFun ((b,u.val),-δ)) ≤ -ε at hp
    rw [neg_mul,one_mul]
    exact hp.trans (neg_nonpos.mpr hε.le)

omit [FiniteDimensional ℝ W] [TopologicalSpace B] [CompactSpace B] [ChartedSpace E B]
  [IsManifold 𝓘(ℝ,E) ∞ B] in
lemma homogeneity_nonneg (g : RegularHomogeneous W) {r : ℝ} (hr : 0 ≤ r) (w : W) :
    g (r • w) = r^2*g w := by
  rcases hr.eq_or_lt with h | h
  · subst r; simp
  · exact g.homogeneity r h w

theorem smooth_negativeSuspension_equiv {g : B → RegularHomogeneous W}
    (hg : SmoothFamily (E:=E) g) {d : ℝ} (hd : 0 < d)
    (hgrad : ∀ b w, ‖w‖ = 1 → d ≤ ‖gradient (g b) w‖) :
    Nonempty (FiberwiseHomotopyEquiv
      ((negativeSphere (fun b w => g b w)).suspensionProjection (Z:=ℝ))
      (negativeSplitProjection (fun b w => g b w))) := by
  obtain ⟨ε,hε,H,hzero,hdec,hpush⟩ := exists_angularDescent hg hd hgrad
  have hden : 0 < 1+ε := by linarith
  have hc : 0 < ε/(1+ε) := div_pos hε hden
  have hc1 : ε/(1+ε) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hce : (ε/(1+ε))^2*(1+ε) ≤ ε := by
    calc
      (ε/(1+ε))^2*(1+ε) = ε*(ε/(1+ε)) := by field_simp
      _ ≤ ε*1 := mul_le_mul_of_nonneg_left hc1 hε.le
      _ = ε := mul_one _
  exact ⟨negativeSuspensionEquiv (fun b _ hr w => (g b).homogeneity_nonneg hr w)
    hc hc1 hε.le hce H hzero hdec hpush⟩

end NearbyLagrangian.Tubes.RegularHomogeneous

end

end OAI
