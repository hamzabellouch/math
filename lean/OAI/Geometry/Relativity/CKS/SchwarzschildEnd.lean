import OAI.Geometry.Relativity.CKS.SourceExteriorDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSSourceExterior
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
attribute [local instance] CKSMixedGeometry.pointDimension_neZero CKSBoundarySurface.two_atLeastTwo
local instance : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩

def sphereDefault : Sphere := ⟨EuclideanSpace.single 0 1,by simp⟩
def sphereDirection (x : E3) : Sphere :=
  if h : x ≠ 0 then ⟨‖x‖⁻¹ • x, CKSSphericalHarmonics.normalize_mem_sphere x h⟩ else sphereDefault
lemma sphereDirection_val {x : E3} (hx : x ≠ 0) :
    (sphereDirection x).val = ‖x‖⁻¹ • x := by simp [sphereDirection,hx]
lemma sphereDirection_smoothAt {x : E3} (hx : x ≠ 0) :
    ContMDiffAt 𝓘(ℝ,E3) I2 ∞ sphereDirection x := by
  have he : (fun y : CKSSphericalHarmonics.puncturedSpace => sphereDirection y) =
      CKSSphericalHarmonics.normalizeSphere := by
    funext y; apply Subtype.ext; exact sphereDirection_val y.property
  have h := CKSSphericalHarmonics.normalizeSphere_smooth
  rw [← he] at h
  exact contMDiffAt_subtype_iff.mp (h ⟨x,hx⟩)

def positionInverse (m : ℝ) (x : E3) : Exterior :=
  (⟨max 0 (‖x‖-2*m),le_max_left _ _⟩,sphereDirection x)
lemma positionInverse_radius {m : ℝ} {x : E3} (hx : 2*m ≤ ‖x‖) :
    radius m (positionInverse m x) = ‖x‖ := by
  simp only [radius,height,positionInverse,max_eq_right (sub_nonneg.mpr hx)]
  ring
lemma position_left_inverse {m : ℝ} (hm : 0 < m) (p : Exterior) :
    positionInverse m (position m p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [positionInverse,norm_position hm,radius,height,add_sub_cancel_left,
      max_eq_right p.1.property]
  · apply Subtype.ext
    rw [show (positionInverse m (position m p)).2 = sphereDirection (position m p) from rfl,
      sphereDirection_val (norm_ne_zero_iff.mp (ne_of_gt (by rw [norm_position hm]; exact radius_pos hm p))),
      norm_position hm,position,smul_smul,inv_mul_cancel₀ (ne_of_gt (radius_pos hm p)),one_smul]
    rfl
lemma position_right_inverse {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖) :
    position m (positionInverse m x) = x := by
  have hp : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) hx
  unfold position directionAmbient
  rw [positionInverse_radius hx]
  change ‖x‖ • (sphereDirection x).val = x
  rw [sphereDirection_val (norm_ne_zero_iff.mp hp.ne'),smul_smul,
    mul_inv_cancel₀ hp.ne',one_smul]

lemma pair_smoothAt {f : E3 → Exterior} {x : E3}
    (ht : ContDiffAt ℝ ∞ (fun y => height (f y)) x)
    (hs : ContMDiffAt 𝓘(ℝ,E3) I2 ∞ (fun y => angular (f y)) x) :
    ContMDiffAt 𝓘(ℝ,E3) I3 ∞ f x := by
  rw [contMDiffAt_iff] at hs ⊢
  constructor
  · exact (ht.continuousAt.codRestrict (fun y => (f y).1.property)).prodMk hs.1
  · have hs' : ContDiffAt ℝ ∞ (fun y => chartAt E2 (f x).2 (f y).2) x := by
      simpa only [mfld_simps,chartAt_self_eq,OpenPartialHomeomorph.refl_apply,
        Function.comp_def,contDiffWithinAt_univ,angular] using hs.2
    have h := join.contDiff.contDiffAt.comp x (ht.prodMk hs')
    simp only [mfld_simps,chartAt_self_eq,
      Function.comp_def,contDiffWithinAt_univ]
    change ContDiffAt ℝ ∞ (fun y => join (height (f y),chartAt E2 (f x).2 (f y).2)) x
    exact h

lemma positionInverse_smoothAt {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m < ‖x‖) :
    ContMDiffAt 𝓘(ℝ,E3) I3 ∞ (positionInverse m) x := by
  have hp : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by positivity) hx))
  apply pair_smoothAt
  · have he : (fun y => height (positionInverse m y)) =ᶠ[𝓝 x] (fun y => ‖y‖-2*m) := by
      filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx] with y hy
      exact max_eq_right (sub_nonneg.mpr hy.le)
    exact ((contDiffAt_norm ℝ hp).sub contDiffAt_const).congr_of_eventuallyEq he
  · exact sphereDirection_smoothAt hp

lemma radius_sublevel_compact (m r : ℝ) : IsCompact {p : Exterior | radius m p ≤ r} := by
  have ht : IsCompact {t : Radial | t.val ≤ r-2*m} := by
    rw [Subtype.isCompact_iff]
    convert (isCompact_Icc : IsCompact (Icc 0 (r-2*m))) using 1
    ext t
    simp only [mem_image,mem_ofPred_eq,mem_Icc]
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ⟨a.property,ha⟩
    · rintro ⟨h0,h1⟩; exact ⟨⟨t,h0⟩,h1,rfl⟩
  convert ht.prod (isCompact_univ : IsCompact (univ : Set Sphere)) using 1
  ext p
  simp only [mem_ofPred_eq,mem_prod,mem_univ,and_true,radius,height]
  constructor <;> intro h <;> linarith

def coordinateEnd {m : ℝ} (hm : 0 < m) : CoordinateEnd (N := Exterior) where
  radius := 2*m+1
  radius_pos := by positivity
  domain := {p | 2*m+1 < radius m p}
  isOpen := isOpen_lt continuous_const (radius_smooth m).continuous
  coordinate := position m
  inverse := positionInverse m
  smooth := (position_smooth m).contMDiffOn
  inverse_smooth := fun x hx => (positionInverse_smoothAt hm (by change 2*m+1 < ‖x‖ at hx; linarith)).contMDiffWithinAt
  mapsTo := fun p hp => by rwa [norm_position hm]
  left_inverse := fun p _ => position_left_inverse hm p
  right_inverse := fun x hx => by
    have h := position_right_inverse hm (le_of_lt (by linarith : 2*m < ‖x‖))
    exact ⟨by dsimp; rw [positionInverse_radius (by linarith)]; exact hx,h⟩
  closed_far_side := fun r hr => by
    have he : {p : Exterior | p ∈ {p | 2*m+1 < radius m p} ∧ r ≤ ‖position m p‖} =
        {p | r ≤ radius m p} := by
      ext p; simp only [mem_ofPred_eq,norm_position hm]; constructor
      · exact And.right
      · intro hp; exact ⟨lt_of_lt_of_le hr hp,hp⟩
    rw [he]
    exact isClosed_le continuous_const (radius_smooth m).continuous
  compact_inner_side := fun r hr => by
    have he : {p : Exterior | p ∉ {p | 2*m+1 < radius m p} ∨ ‖position m p‖ ≤ r} =
        {p | radius m p ≤ r} := by
      ext p; simp only [mem_ofPred_eq,norm_position hm,not_lt]
      constructor
      · rintro (h|h); exact h.trans hr.le; exact h
      · exact Or.inr
    rw [he]
    exact radius_sublevel_compact m r
end CKSSchwarzschild

end

end OAI
