import Mathlib
import OAI.Geometry.NearbyLagrangian.CotangentModel
import OAI.Geometry.NearbyLagrangian.RelativeApproximation

namespace OAI

/-! Sphere cap collapses, smooth plateaus and localization of tube families. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian
namespace SphereCollapse

open Set Filter ContinuousMap
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev Sphere := Metric.sphere (0 : V) 1

def antipode (q : Sphere (V := V)) : Sphere (V := V) :=
  ⟨-(q : V), by simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using q.property⟩

omit [NormedSpace ℝ V] in
lemma norm_coe (x : Sphere (V := V)) : ‖(x : V)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

lemma blend_ne_zero (q : Sphere (V := V)) (χ : Sphere (V := V) → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0:ℝ) 1) (ha : χ (antipode q) = 0)
    (t : unitInterval) (x : Sphere (V := V)) :
    (1-(t:ℝ)*χ x) • (x:V) + ((t:ℝ)*χ x) • (q:V) ≠ 0 := by
  let r : ℝ := (t:ℝ)*χ x
  have hr : 0 ≤ r := mul_nonneg t.property.1 (hχ x).1
  have hr1 : r ≤ 1 := (mul_le_of_le_one_left (hχ x).1 t.property.2).trans (hχ x).2
  intro hz
  have he : (1-r) • (x:V) = -(r • (q:V)) := eq_neg_of_add_eq_zero_left hz
  have hn := congrArg norm he
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
    abs_of_nonneg (sub_nonneg.mpr hr1), norm_coe, mul_one, norm_neg] at hn
  have hrh : r = 1/2 := by linarith
  have hsum : (1/2:ℝ) • ((x:V)+(q:V)) = 0 := by
    simp only [smul_add]
    have hz' : (1-r) • (x:V) + r • (q:V) = 0 := hz
    rw [hrh] at hz'
    convert hz' using 1
    norm_num
  have hx : (x:V) = -(q:V) := by
    have he := (smul_eq_zero.mp hsum).resolve_left (by norm_num)
    exact eq_neg_of_add_eq_zero_left he
  have hxa : x = antipode q := Subtype.ext hx
  have hrz : r = 0 := by simp only [r, hxa, ha, mul_zero]
  linarith

def homotopy (q : Sphere (V := V)) (χ : C(Sphere (V := V),ℝ))
    (hχ : ∀ x, χ x ∈ Icc (0:ℝ) 1) (ha : χ (antipode q) = 0) :
    C(unitInterval × Sphere (V := V), Sphere (V := V)) := by
  let raw : unitInterval × Sphere (V := V) → V := fun p =>
    (1-(p.1:ℝ)*χ p.2) • (p.2:V) + ((p.1:ℝ)*χ p.2) • (q:V)
  have hr : Continuous raw :=
    ((continuous_const.sub ((continuous_subtype_val.comp continuous_fst).mul
      (χ.continuous.comp continuous_snd))).smul
      (continuous_subtype_val.comp continuous_snd)).add
      (((continuous_subtype_val.comp continuous_fst).mul
        (χ.continuous.comp continuous_snd)).smul continuous_const)
  have hn : ∀ p, raw p ≠ 0 := fun p => blend_ne_zero q χ hχ ha p.1 p.2
  refine ⟨fun p => ⟨‖raw p‖⁻¹ • raw p, ?_⟩, ?_⟩
  · simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hn p))]
  · exact ((hr.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (hn p))).smul hr).subtype_mk _

@[simp] lemma homotopy_zero (q : Sphere (V := V)) (χ : C(Sphere (V := V),ℝ))
    (hχ : ∀ x, χ x ∈ Icc (0:ℝ) 1) (ha : χ (antipode q) = 0)
    (x : Sphere (V := V)) : homotopy q χ hχ ha (0,x) = x := by
  apply Subtype.ext
  simp [homotopy]

lemma homotopy_one_eq (q : Sphere (V := V)) (χ : C(Sphere (V := V),ℝ))
    (hχ : ∀ x, χ x ∈ Icc (0:ℝ) 1) (ha : χ (antipode q) = 0)
    {x : Sphere (V := V)} (hx : χ x = 1) : homotopy q χ hχ ha (1,x) = q := by
  apply Subtype.ext
  simp [homotopy, hx]

def collapse (q : Sphere (V := V)) (χ : C(Sphere (V := V),ℝ))
    (hχ : ∀ x, χ x ∈ Icc (0:ℝ) 1) (ha : χ (antipode q) = 0) :
    C(Sphere (V := V),Sphere (V := V)) :=
  (homotopy q χ hχ ha).comp ⟨fun x => (1,x), continuous_const.prodMk continuous_id⟩

def idHomotopyCollapse (q : Sphere (V := V)) (χ : C(Sphere (V := V),ℝ))
    (hχ : ∀ x, χ x ∈ Icc (0:ℝ) 1) (ha : χ (antipode q) = 0) :
    (ContinuousMap.id (Sphere (V := V))).Homotopy (collapse q χ hχ ha) where
  toContinuousMap := homotopy q χ hχ ha
  map_zero_left := homotopy_zero q χ hχ ha
  map_one_left _ := rfl

end SphereCollapse
end NearbyLagrangian

namespace NearbyLagrangian.SphereCollapse

open Set ContinuousMap
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def cutoff (q : Sphere (V := V)) : C(Sphere (V := V),ℝ) :=
  ⟨fun x => min 1 (2 * ‖(x:V)+(q:V)‖),
    continuous_const.min (continuous_const.mul ((continuous_subtype_val.add continuous_const).norm))⟩

omit [NormedSpace ℝ V] in
lemma cutoff_mem (q x : Sphere (V := V)) : cutoff q x ∈ Icc (0:ℝ) 1 :=
  ⟨le_min zero_le_one (mul_nonneg (by norm_num) (norm_nonneg _)), min_le_left _ _⟩

omit [NormedSpace ℝ V] in
@[simp] lemma cutoff_antipode (q : Sphere (V := V)) : cutoff q (antipode q) = 0 := by
  simp [cutoff, antipode]

def capCollapse (q : Sphere (V := V)) : C(Sphere (V := V), Sphere (V := V)) :=
  collapse q (cutoff q) (cutoff_mem q) (cutoff_antipode q)

def capHomotopy (q : Sphere (V := V)) :
    (ContinuousMap.id (Sphere (V := V))).Homotopy (capCollapse q) :=
  idHomotopyCollapse q (cutoff q) (cutoff_mem q) (cutoff_antipode q)

lemma capCollapse_eq (q x : Sphere (V := V)) (hx : 1/2 ≤ ‖(x:V)+(q:V)‖) :
    capCollapse q x = q := by
  apply homotopy_one_eq q (cutoff q) (cutoff_mem q) (cutoff_antipode q) (x := x)
  change min (1:ℝ) (2 * ‖(x:V)+(q:V)‖) = 1
  exact min_eq_left (by linarith)

theorem localize_family {Y : Type*} [TopologicalSpace Y]
    (a : C(Sphere (V := V),Y)) (q : Sphere (V := V)) :
    a.Homotopic (a.comp (capCollapse q)) ∧
      ∀ x : Sphere (V := V), 1/2 ≤ ‖(x:V)+(q:V)‖ → (a.comp (capCollapse q)) x = a q := by
  constructor
  · simpa only [ContinuousMap.comp_id] using
      (ContinuousMap.Homotopic.refl a).comp (show (ContinuousMap.id _).Homotopic (capCollapse q)
        from ⟨capHomotopy q⟩)
  · intro x hx
    simp only [ContinuousMap.comp_apply, capCollapse_eq q x hx]

end NearbyLagrangian.SphereCollapse

namespace NearbyLagrangian.SphereCollapse
open Set ContinuousMap
open scoped Topology
variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace Y]

def plateauParameter (q : Sphere (V:=V)) : C(Sphere (V:=V),unitInterval) :=
  ⟨fun x => ⟨max 0 (min 1 (2*‖(x:V)+(q:V)‖-1)),
    le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩,
    (continuous_const.max (continuous_const.min
      ((continuous_const.mul (continuous_subtype_val.add continuous_const).norm).sub
        continuous_const))).subtype_mk _⟩

omit [NormedSpace ℝ V] in
lemma plateauParameter_zero (q x : Sphere (V:=V)) (hx : ‖(x:V)+(q:V)‖ ≤ 1/2) :
    plateauParameter q x = 0 := by
  apply Subtype.ext
  change max (0:ℝ) (min 1 (2*‖(x:V)+(q:V)‖-1)) = 0
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [NormedSpace ℝ V] in
lemma plateauParameter_one (q x : Sphere (V:=V)) (hx : 1 ≤ ‖(x:V)+(q:V)‖) :
    plateauParameter q x = 1 := by
  apply Subtype.ext
  change max (0:ℝ) (min 1 (2*‖(x:V)+(q:V)‖-1)) = 1
  rw [min_eq_left (by linarith),max_eq_right zero_le_one]

omit [NormedSpace ℝ V] in

theorem move_plateau (f : C(Sphere (V:=V),Y)) (q : Sphere (V:=V)) (y₀ y₁ : Y)
    (P : Path y₀ y₁)
    (hf : ∀ x : Sphere (V:=V), 1/2 ≤ ‖(x:V)+(q:V)‖ → f x = y₀) :
    ∃ g : C(Sphere (V:=V),Y), f.Homotopic g ∧
      (∀ x : Sphere (V:=V), 1 ≤ ‖(x:V)+(q:V)‖ → g x = y₁) := by
  let K : C(unitInterval × Sphere (V:=V),Y) :=
    { toFun := fun p => if ‖(p.2:V)+(q:V)‖ ≤ 1/2 then f p.2
        else P (p.1*plateauParameter q p.2)
      continuous_toFun := by
        apply (f.continuous.comp continuous_snd).if_le
          (P.continuous.comp (continuous_fst.mul ((plateauParameter q).continuous.comp continuous_snd)))
          ((continuous_subtype_val.comp continuous_snd).add continuous_const).norm continuous_const
        intro p hp
        change f p.2 = P (p.1*plateauParameter q p.2)
        change ‖(p.2:V)+(q:V)‖ = 1/2 at hp
        rw [plateauParameter_zero q p.2 hp.le,mul_zero,P.source,hf p.2 hp.ge] }
  let g : C(Sphere (V:=V),Y) :=
    K.comp ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩
  refine ⟨g,⟨{ toContinuousMap := K, map_zero_left := ?_,map_one_left := fun _ => rfl }⟩,?_⟩
  · intro x
    change (if ‖(x:V)+(q:V)‖ ≤ 1/2 then f x else P (0*plateauParameter q x)) = f x
    split_ifs with hx
    · rfl
    · rw [zero_mul,P.source,hf x (le_of_not_ge hx)]
  · intro x hx
    change (if ‖(x:V)+(q:V)‖ ≤ 1/2 then f x else P (1*plateauParameter q x)) = y₁
    rw [ite_eq_right (by linarith),one_mul,plateauParameter_one q x hx,P.target]

theorem localize_to_value (a : C(Sphere (V:=V),Y)) (q : Sphere (V:=V))
    (y : Y) (P : Path (a q) y) :
    ∃ b : C(Sphere (V:=V),Y), a.Homotopic b ∧
      ∀ x : Sphere (V:=V), 1 ≤ ‖(x:V)+(q:V)‖ → b x = y := by
  obtain ⟨b,hb,hplateau⟩ := move_plateau (a.comp (capCollapse q)) q (a q) y P
    (localize_family a q).2
  exact ⟨b,(localize_family a q).1.trans hb,hplateau⟩

end NearbyLagrangian.SphereCollapse

namespace NearbyLagrangian.Tubes
open ContinuousMap
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

instance tubePathConnected (k l : ℕ) : PathConnectedSpace (Tube k l) := by
  exact isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent

theorem standard_plateau {k l : ℕ}
    (a : C(SphereCollapse.Sphere (V:=V),Tube k l))
    (q : SphereCollapse.Sphere (V:=V)) :
    ∃ b : C(SphereCollapse.Sphere (V:=V),Tube k l), a.Homotopic b ∧
      ∀ x : SphereCollapse.Sphere (V:=V),
        1 ≤ ‖(x:V)+(q:V)‖ → b x = standardTube k l := by
  exact SphereCollapse.localize_to_value a q (standardTube k l)
    (PathConnectedSpace.somePath (a q) (standardTube k l))

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.SphereCollapse
open Set
open scoped Topology ContDiff Manifold InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def plateauBump : ContDiffBump (0:ℝ) := ⟨1,3/2,by norm_num,by norm_num⟩

def smoothPlateau (q : Sphere (V:=V)) (x : Sphere (V:=V)) : ℝ :=
  plateauBump (‖(x:V)+(q:V)‖^2)

omit [InnerProductSpace ℝ V] in
lemma smoothPlateau_mem (q x : Sphere (V:=V)) : smoothPlateau q x ∈ Icc (0:ℝ) 1 :=
  ⟨plateauBump.nonneg,plateauBump.le_one⟩

omit [InnerProductSpace ℝ V] in
lemma smoothPlateau_one (q x : Sphere (V:=V)) (hx : ‖(x:V)+(q:V)‖ ≤ 1) :
    smoothPlateau q x = 1 := by
  apply plateauBump.one_of_mem_closedBall
  change dist (‖(x:V)+(q:V)‖^2) 0 ≤ 1
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg ((x:V)+(q:V))]

omit [InnerProductSpace ℝ V] in
lemma smoothPlateau_zero (q x : Sphere (V:=V)) (hx : 3/2 ≤ ‖(x:V)+(q:V)‖^2) :
    smoothPlateau q x = 0 := by
  apply plateauBump.zero_of_le_dist
  change 3/2 ≤ dist (‖(x:V)+(q:V)‖^2) 0
  rwa [Real.dist_eq,sub_zero,abs_of_nonneg (sq_nonneg _)]

lemma contMDiff_smoothPlateau {n : ℕ} [Fact (Module.finrank ℝ V = n+1)]
    (q : Sphere (V:=V)) : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (smoothPlateau q) := by
  have h : ContDiff ℝ ∞ (fun x : V => ‖x+(q:V)‖^2) :=
    (contDiff_id.add contDiff_const).norm_sq ℝ
  exact plateauBump.contDiff.contMDiff.comp (h.contMDiff.comp contMDiff_coe_sphere)

lemma polar_cap_in_plateau (q x : Sphere (V:=V)) {e : V} (he : ‖e‖ = 1)
    (heq : ⟪e,(q:V)⟫_ℝ = 0) (hx : (31:ℝ)/32 < |⟪e,(x:V)⟫_ℝ|) :
    3/2 ≤ ‖(x:V)+(q:V)‖^2 := by
  have hxp := norm_coe x
  have hqp := norm_coe q
  let s := ⟪e,(x:V)⟫_ℝ
  let t := ⟪(q:V),(x:V)⟫_ℝ
  have hqe : ⟪(q:V),e⟫_ℝ = 0 := by rw [real_inner_comm,heq]
  have hnon : 0 ≤ ⟪(x:V)-s•e-t•(q:V),(x:V)-s•e-t•(q:V)⟫_ℝ :=
    real_inner_self_nonneg
  have hsum := norm_add_sq_real (x:V) (q:V)
  have hxe : ⟪(x:V),e⟫_ℝ = s := real_inner_comm _ _
  have hxq : ⟪(x:V),(q:V)⟫_ℝ = t := real_inner_comm _ _
  have hex : ⟪e,(x:V)⟫_ℝ = s := rfl
  have hqx : ⟪(q:V),(x:V)⟫_ℝ = t := rfl
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,inner_smul_right,
    real_inner_self_eq_norm_sq,he,hxp,hqp,heq,hqe,hxe,hxq,hex,hqx,
    one_pow,mul_zero,mul_one,sub_zero,sub_self] at hnon
  rw [hxp,hqp,hxq] at hsum
  dsimp only [s,t] at hnon hsum
  have habssq : ((31:ℝ)/32)^2 < ⟪e,(x:V)⟫_ℝ^2 := by
    nlinarith [sq_abs ⟪e,(x:V)⟫_ℝ,abs_nonneg ⟪e,(x:V)⟫_ℝ]
  nlinarith [sq_nonneg (⟪(q:V),(x:V)⟫_ℝ + 1/4)]

end NearbyLagrangian.SphereCollapse

namespace NearbyLagrangian.Tubes
open Set ContinuousMap
open scoped Topology ContDiff Manifold

theorem smooth_localized_tube {k l : ℕ} (hkl : 0 < k+l)
    (a : C(UnitSphere 10,Tube k l)) (q : UnitSphere 10) :
    ∃ b : C(UnitSphere 10,Tube k l), a.Homotopic b ∧
      RegularHomogeneous.SmoothFamily (E:=Euclidean 9) (fun x => (b x).val) ∧
      Nonempty (FiberwiseHomotopyEquiv (negativeProjection a) (negativeProjection b)) ∧
      ∀ x : UnitSphere 10, 3/2 ≤ ‖(x:Euclidean 10)+(q:Euclidean 10)‖^2 →
        b x = standardTube k l := by
  let : Fact (Module.finrank ℝ (Euclidean 10) = 9+1) := ⟨by simp [Euclidean]⟩
  obtain ⟨b,hab,hfixed⟩ := standard_plateau a q
  have hpres (x : UnitSphere 10) (hx : SphereCollapse.smoothPlateau q x ≠ 1) :
      b x = standardTube k l := by
    apply hfixed
    by_contra! h
    exact hx (SphereCollapse.smoothPlateau_one q x h.le)
  obtain ⟨g,hbg,hgs,hneg,hfix⟩ := exists_smooth_tube_relative (V:=Euclidean 9)
    hkl b (standardTube k l) (contDiff_standardForm k l).contDiffOn
      (SphereCollapse.contMDiff_smoothPlateau (n:=9) q)
      (SphereCollapse.smoothPlateau_mem q) hpres
  have hag := hab.trans hbg
  exact ⟨g,hag,hgs,negative_equiv_tube_of_homotopic (V:=Euclidean 9) hkl hag,
    fun x hx => hfix x (SphereCollapse.smoothPlateau_zero q x hx)⟩

theorem smooth_localized_kernel {m : ℕ} (hm : 0 < m)
    (a : C(UnitSphere 10,Tube m m)) (ha : StablyNonNull a)
    (hn : StableNegativeTrivial a) (q : UnitSphere 10) :
    ∃ b : C(UnitSphere 10,Tube m m), a.Homotopic b ∧ StablyNonNull b ∧
      StableNegativeTrivial b ∧
      RegularHomogeneous.SmoothFamily (E:=Euclidean 9) (fun x => (b x).val) ∧
      ∀ x : UnitSphere 10, 3/2 ≤ ‖(x:Euclidean 10)+(q:Euclidean 10)‖^2 →
        b x = standardTube m m := by
  obtain ⟨b,hab,hbs,_,hfix⟩ := smooth_localized_tube (by omega) a q
  exact ⟨b,hab,ha.of_homotopic hab,hn.of_homotopic (V:=Euclidean 9) hm hab,hbs,hfix⟩

end NearbyLagrangian.Tubes

end

end OAI
