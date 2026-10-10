import OAI.Probability.FirstPassage.CrossingTrialGeometry
import OAI.Probability.FirstPassage.TiltedRegions
import OAI.Probability.FirstPassage.ConnectorEvents
import OAI.Probability.FirstPassage.SupportContactEstimate

namespace OAI

namespace PlanarFPP
open Set

def connectorWindow (b : ℝ) (X : ℤ) (Y S : ℝ) : Set Vertex :=
  {p | p.1=X ∧ |transverse b p-Y| ≤ S/4}

def connectorRegion (b : ℝ) (X d : ℤ) (Y S s : ℝ) : Set Vertex :=
  {p | (X : ℝ)-s ≤ p.1 ∧ (p.1 : ℝ) ≤ (X : ℝ)+d+s ∧
    |transverse b p-Y| ≤ 4*S}

theorem connectorRegion_finite (b : ℝ) (X d : ℤ) (Y S s : ℝ) :
    (connectorRegion b X d Y S s).Finite := by
  apply (finite_tilted_rectangle b X Y (|(d : ℝ)|+|s|) (4*S)).subset
  intro p hp
  refine ⟨abs_le.mpr ⟨?_,?_⟩,hp.2.2⟩ <;>
    linarith [hp.1,hp.2.1,le_abs_self s,le_abs_self (d : ℝ),abs_nonneg (d : ℝ)]

noncomputable def connectorVertices (b : ℝ) (X d : ℤ) (Y S s : ℝ) : Finset Vertex :=
  (connectorRegion_finite b X d Y S s).toFinset

@[simp] theorem mem_connectorVertices (b : ℝ) (X d : ℤ) (Y S s : ℝ) (p : Vertex) :
    p ∈ connectorVertices b X d Y S s ↔ p ∈ connectorRegion b X d Y S s :=
  (connectorRegion_finite b X d Y S s).mem_toFinset

theorem connector_transverse_displacement (b : ℝ) (X d : ℤ) (Y S σ a : ℝ)
    (hS : 0 ≤ S) (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p q : Vertex) (hp : p ∈ connectorWindow b X Y S)
    (hq : q ∈ connectorWindow b (X+d) (Y+σ*a*S) S) :
    S/2 ≤ σ*(transverse b q-transverse b p) ∧
      σ*(transverse b q-transverse b p) ≤ 5*S/2 := by
  have hsq : σ*σ=1 := by nlinarith [sq_abs σ]
  have hep := hp.2
  have heq := hq.2
  have hp' : |σ*(transverse b p-Y)| ≤ S/4 := by simpa [abs_mul,hσ] using hep
  have hq' : |σ*(transverse b q-(Y+σ*a*S))| ≤ S/4 := by simpa [abs_mul,hσ] using heq
  have he : σ*(transverse b q-transverse b p) =
      σ*(transverse b q-(Y+σ*a*S))-σ*(transverse b p-Y)+a*S := by
    calc
      _ = σ*(transverse b q-(Y+σ*a*S))-σ*(transverse b p-Y)+(σ*σ)*(a*S) := by ring
      _ = _ := by rw [hsq]; ring
  rw [he]
  obtain ⟨hp₀,hp₁⟩ := abs_le.mp hp'
  obtain ⟨hq₀,hq₁⟩ := abs_le.mp hq'
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right ha.1 hS,
    mul_le_mul_of_nonneg_right ha.2 hS]

theorem connector_window_bounds (b : ℝ) (X d : ℤ) (Y S σ a : ℝ)
    (hd : 0 ≤ d) (hS : 0 ≤ S) (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p : Vertex) (hp : p ∈ connectorWindow b X Y S ∪
      connectorWindow b (X+d) (Y+σ*a*S) S) :
    (X : ℝ) ≤ p.1 ∧ (p.1 : ℝ) ≤ (X : ℝ)+d ∧
      |transverse b p-Y| ≤ 9*S/4 := by
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  rcases hp with hp | hp
  · refine ⟨by simp [hp.1],?_,?_⟩
    · simp only [hp.1]; linarith
    · linarith [hp.2]
  · refine ⟨?_,by simp [hp.1],?_⟩
    · simp only [hp.1,Int.cast_add]; linarith
    · have hh := abs_add_le (transverse b p-(Y+σ*a*S)) (σ*a*S)
      have he : transverse b p-(Y+σ*a*S)+σ*a*S=transverse b p-Y := by ring
      rw [he,abs_mul,abs_mul,hσ,one_mul,abs_of_nonneg (by linarith : 0 ≤ a),abs_of_nonneg hS] at hh
      nlinarith [hp.2,mul_le_mul_of_nonneg_right ha.2 hS]

theorem transverse_plane_lipschitz (b : ℝ) (hb : |b| ≤ 1) (z : Plane) :
    |rCoord b z| ≤ 2*‖z‖ := by
  have hh := abs_sub_le (z 1) 0 (b*z 0)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at hh
  have hc₀ := plane_coordinate_le_norm z 0
  have hc₁ := plane_coordinate_le_norm z 1
  have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (z 0))
  change |z 1-b*z 0| ≤ _
  nlinarith

theorem plane_norm_le_shear (b : ℝ) (hb : |b| ≤ 1) (z : Plane) :
    ‖z‖ ≤ 2*|xCoord z|+|rCoord b z| := by
  have hh := abs_add_le (rCoord b z) (b*z 0)
  have he : rCoord b z+b*z 0=z 1 := by simp [rCoord_apply]
  rw [he,abs_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (z 0))
  have hn := plane_norm_le_coordinates z
  change ‖z‖ ≤ 2*|z 0|+|rCoord b z|
  linarith

theorem connector_union_diameter (b : ℝ) (hb : |b| ≤ 1)
    (X d : ℤ) (Y S σ a : ℝ) (hd : 0 ≤ d) (hS : 0 ≤ S)
    (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p q : Vertex)
    (hp : p ∈ connectorWindow b X Y S ∪ connectorWindow b (X+d) (Y+σ*a*S) S)
    (hq : q ∈ connectorWindow b X Y S ∪ connectorWindow b (X+d) (Y+σ*a*S) S) :
    ‖latticeEmbed (q-p)‖ ≤ 2*(d : ℝ)+9*S/2 := by
  obtain ⟨hp₀,hp₁,hp₂⟩ := connector_window_bounds b X d Y S σ a hd hS hσ ha p hp
  obtain ⟨hq₀,hq₁,hq₂⟩ := connector_window_bounds b X d Y S σ a hd hS hσ ha q hq
  have hx : |xCoord (latticeEmbed (q-p))| ≤ (d : ℝ) := by
    change |((q-p).1 : ℝ)| ≤ _
    simp only [Prod.fst_sub,Int.cast_sub]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hr : |rCoord b (latticeEmbed (q-p))| ≤ 9*S/2 := by
    have hh := abs_sub_le (transverse b q-Y) 0 (transverse b p-Y)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    have he : rCoord b (latticeEmbed (q-p))=(transverse b q-Y)-(transverse b p-Y) := by
      simp [rCoord_apply,latticeEmbed,transverse]; ring
    rw [he]
    linarith
  exact (plane_norm_le_shear b hb _).trans (by linarith)

theorem connector_tube_containment (b : ℝ) (hb : |b| ≤ 1)
    (X d : ℤ) (Y S s σ a : ℝ) (hd : 0 ≤ d) (hs : 0 ≤ s) (hS : s ≤ S)
    (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p q : Vertex) (hp : p ∈ connectorWindow b X Y S)
    (hq : q ∈ connectorWindow b (X+d) (Y+σ*a*S) S) :
    SegmentTube p q (s/2) ⊆ (connectorVertices b X d Y S s : Set Vertex) := by
  have hS0 : 0 ≤ S := hs.trans hS
  obtain ⟨hp₀,hp₁,hp₂⟩ := connector_window_bounds b X d Y S σ a hd hS0 hσ ha p (Or.inl hp)
  obtain ⟨hq₀,hq₁,hq₂⟩ := connector_window_bounds b X d Y S σ a hd hS0 hσ ha q (Or.inr hq)
  intro z hz
  obtain ⟨t,ht₀,ht₁,ht⟩ := hz
  have hsegx : xCoord (segmentPoint p q t)=(1-t)*(p.1 : ℝ)+t*(q.1 : ℝ) := by
    simp [segmentPoint,latticeEmbed,xCoord_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply]
    ring
  have hsegr : rCoord b (segmentPoint p q t)-Y=
      (1-t)*(transverse b p-Y)+t*(transverse b q-Y) := by
    simp [segmentPoint,latticeEmbed,rCoord_apply,transverse,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply]
    ring
  have hseg₀ : (X : ℝ) ≤ xCoord (segmentPoint p q t) := by
    rw [hsegx]
    nlinarith [mul_le_mul_of_nonneg_left hp₀ (by linarith : 0 ≤ 1-t),
      mul_le_mul_of_nonneg_left hq₀ ht₀]
  have hseg₁ : xCoord (segmentPoint p q t) ≤ (X : ℝ)+d := by
    rw [hsegx]
    nlinarith [mul_le_mul_of_nonneg_left hp₁ (by linarith : 0 ≤ 1-t),
      mul_le_mul_of_nonneg_left hq₁ ht₀]
  have hseg₂ : |rCoord b (segmentPoint p q t)-Y| ≤ 9*S/4 := by
    rw [hsegr]
    have hh := abs_add_le ((1-t)*(transverse b p-Y)) (t*(transverse b q-Y))
    rw [abs_mul,abs_mul,abs_of_nonneg ht₀,abs_of_nonneg (by linarith : 0 ≤ 1-t)] at hh
    nlinarith [mul_le_mul_of_nonneg_left hp₂ (by linarith : 0 ≤ 1-t),
      mul_le_mul_of_nonneg_left hq₂ ht₀]
  have hx := (plane_coordinate_le_norm (latticeEmbed z-segmentPoint p q t) 0).trans ht
  have hr := (transverse_plane_lipschitz b hb (latticeEmbed z-segmentPoint p q t)).trans
    (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2))
  have hx' : |(z.1 : ℝ)-xCoord (segmentPoint p q t)| ≤ s/2 := by
    simpa [latticeEmbed,PiLp.sub_apply] using hx
  have hr' : |transverse b z-rCoord b (segmentPoint p q t)| ≤ s := by
    have he : 2*(s/2)=s := by ring
    simpa [map_sub,rCoord_apply,latticeEmbed,transverse,he] using hr
  change z ∈ connectorVertices b X d Y S s
  rw [mem_connectorVertices]
  refine ⟨?_,?_,?_⟩
  · linarith [(abs_le.mp hx').1]
  · linarith [(abs_le.mp hx').2]
  · have hh := abs_add_le (transverse b z-rCoord b (segmentPoint p q t))
      (rCoord b (segmentPoint p q t)-Y)
    rw [sub_add_sub_cancel] at hh
    linarith

end PlanarFPP

end OAI
