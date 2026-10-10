import Mathlib
import OAI.Geometry.Cannon.Uniformization.SurjectiveRealizationHomeomorphLimit
import OAI.Geometry.Cannon.Boundary.BoundaryEventualRelativeShrink

namespace OAI

section
noncomputable section
namespace CannonRelease
open Set Metric Filter Topology CannonGraph CannonVisual CannonMobius CannonRealization

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_quasiMobius_uniformizer (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ ψ : Boundary D ≃ₜ Sphere,CannonQM.QuasiMobius ψ := by
  let _ := visualMetricSpace D hδ
  let _ : PathConnectedSpace SphereTwo := CannonCharts.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) :=
    φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  let _ : PathConnectedSpace Sphere :=
    roundChart.symm.surjective.pathConnectedSpace roundChart.symm.continuous
  dsimp only
  obtain ⟨F,hF,hshrink⟩ := boundary_eventual_relative_shrink D hδ φ
  obtain ⟨Q,P,hQ,hP,hpack⟩ := relative_polynomial_packing D hδ
  obtain ⟨ψ,hψ,rest⟩ := surjective_realization_quasiMobius_limit hpack hP.le
    (boundaryDist_le_one D hδ) F hF hshrink
  exact ⟨ψ,hψ⟩
end CannonRelease

end
end
section
section
section
section
section
section
section
section
section
section
section
section
noncomputable section

namespace CannonStereo
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereo_crossRatio {v : E} (hv : ‖v‖=1) (x y z w : (ℝ ∙ v)ᗮ) :
    CannonQM.crossRatio (stereoInvFun hv x) (stereoInvFun hv y)
      (stereoInvFun hv z) (stereoInvFun hv w)=CannonQM.crossRatio x y z w := by
  apply NNReal.coe_injective
  change dist (stereoInvFun hv x) (stereoInvFun hv y)*
    dist (stereoInvFun hv z) (stereoInvFun hv w) /
    (dist (stereoInvFun hv x) (stereoInvFun hv w)*
      dist (stereoInvFun hv y) (stereoInvFun hv z)) =
      dist x y*dist z w/(dist x w*dist y z)
  simp only [stereo_dist]
  have hp (u : (ℝ ∙ v)ᗮ) : Real.sqrt (‖u‖^2+4) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  by_cases hxw : x=w
  · subst w; simp
  by_cases hyz : y=z
  · subst z; simp
  have h1 : dist x w ≠ 0 := (dist_pos.mpr hxw).ne'
  have h2 : dist y z ≠ 0 := (dist_pos.mpr hyz).ne'
  field_simp

end CannonStereo

end
end
noncomputable section
namespace CannonMobius
open Metric Topology
open scoped OnePoint

lemma coe_dist (z w : ℂ) : dist (z:Sphere) (w:Sphere)=
    4*dist z w/(Real.sqrt (‖z‖^2+4)*Real.sqrt (‖w‖^2+4)) := by
  rw [sphere_dist,roundChart_coe,roundChart_coe,CannonStereo.stereo_dist]
  simp only [planeHyperplane.isometry.dist_eq,planeHyperplane.norm_map]

lemma coe_crossRatio (x y z w : ℂ) :
    CannonQM.crossRatio (x:Sphere) (y:Sphere) (z:Sphere) (w:Sphere)=
      CannonQM.crossRatio x y z w := by
  have hh := CannonStereo.stereo_crossRatio north_norm
    (planeHyperplane x) (planeHyperplane y) (planeHyperplane z) (planeHyperplane w)
  simpa only [CannonQM.crossRatio,← roundChart_coe,roundChart_isometry.nndist_eq,
    planeHyperplane.isometry.nndist_eq] using hh

lemma roundChart_crossRatio (p q r s : Sphere) :
    CannonQM.crossRatio (roundChart p) (roundChart q) (roundChart r) (roundChart s)=
      CannonQM.crossRatio p q r s := by
  simp only [CannonQM.crossRatio,roundChart_isometry.nndist_eq]

end CannonMobius

namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

def PreservesProducts (f : Sphere → Sphere) : Prop := ∀ p : Fin 4 → Sphere,
  dist (f (p 0)) (f (p 1))*dist (f (p 2)) (f (p 3))*(dist (p 0) (p 3)*dist (p 1) (p 2)) =
  dist (p 0) (p 1)*dist (p 2) (p 3)*(dist (f (p 0)) (f (p 3))*dist (f (p 1)) (f (p 2)))

lemma preservesProducts_dense {α : Type*} (e : α → Sphere) (he : DenseRange e)
    {f : Sphere → Sphere} (hf : Continuous f)
    (h : ∀ p : Fin 4 → α,
      dist (f (e (p 0))) (f (e (p 1)))*dist (f (e (p 2))) (f (e (p 3)))*
        (dist (e (p 0)) (e (p 3))*dist (e (p 1)) (e (p 2))) =
      dist (e (p 0)) (e (p 1))*dist (e (p 2)) (e (p 3))*
        (dist (f (e (p 0))) (f (e (p 3)))*dist (f (e (p 1))) (f (e (p 2))))) :
    PreservesProducts f := by
  have hd : DenseRange (fun p : Fin 4 → α => fun i => e (p i)) := DenseRange.piMap (fun _ => he)
  let l : (Fin 4 → Sphere) → ℝ := fun p =>
    dist (f (p 0)) (f (p 1))*dist (f (p 2)) (f (p 3))*(dist (p 0) (p 3)*dist (p 1) (p 2))
  let r : (Fin 4 → Sphere) → ℝ := fun p =>
    dist (p 0) (p 1)*dist (p 2) (p 3)*(dist (f (p 0)) (f (p 3))*dist (f (p 1)) (f (p 2)))
  have hl : Continuous l := by dsimp [l]; fun_prop
  have hr : Continuous r := by dsimp [r]; fun_prop
  exact fun p => congrFun (hd.equalizer hl hr (funext h)) p

lemma PreservesProducts.crossRatio {f : Sphere → Sphere} (hf : PreservesProducts f)
    (hi : Function.Injective f) (x y z w : Sphere) (hh : CannonQM.Distinct x y z w) :
    CannonQM.crossRatio (f x) (f y) (f z) (f w)=CannonQM.crossRatio x y z w := by
  apply NNReal.coe_injective
  change dist (f x) (f y)*dist (f z) (f w)/(dist (f x) (f w)*dist (f y) (f z))=
    dist x y*dist z w/(dist x w*dist y z)
  have h1 : dist (f x) (f w)*dist (f y) (f z) ≠ 0 := mul_ne_zero
    (dist_ne_zero.mpr (fun h => hh.2.2.1 (hi h)))
    (dist_ne_zero.mpr (fun h => hh.2.2.2.1 (hi h)))
  have h2 : dist x w*dist y z ≠ 0 := mul_ne_zero
    (dist_ne_zero.mpr hh.2.2.1) (dist_ne_zero.mpr hh.2.2.2.1)
  exact (div_eq_div_iff h1 h2).mpr (hf ![x,y,z,w])

lemma PreservesProducts.controlled {f : Sphere → Sphere} (hf : PreservesProducts f)
    (hi : Function.Injective f) : CannonQM.Controlled f (OrderIso.refl _) :=
  fun x y z w hh => (hf.crossRatio hi x y z w hh).le

lemma inversion_preservesProducts : PreservesProducts inversion := by
  let e : {z : ℂ // z ≠ 0} → Sphere := fun z => (z.val:Sphere)
  have he : DenseRange e := (OnePoint.denseRange_coe (X:=ℂ)).comp
    (denseRange_subtype_val.mpr (dense_compl_singleton (0:ℂ))) OnePoint.continuous_coe
  apply preservesProducts_dense e he inversion.continuous
  intro p
  have hinv (i : Fin 4) : inversion (e (p i))=((p i).val⁻¹:ℂ) := inv_coe (p i).2
  simp only [hinv,e,coe_dist,dist_inv_inv₀ (p _).2 (p _).2]
  have hn (i : Fin 4) : ‖(p i).val‖ ≠ 0 := norm_ne_zero_iff.mpr (p i).2
  have hp (z : ℂ) : Real.sqrt (‖z‖^2+4) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

lemma affine_preservesProducts (a b : ℂ) (ha : a ≠ 0) : PreservesProducts (affine a b ha) := by
  apply preservesProducts_dense (fun z : ℂ => (z:Sphere)) OnePoint.denseRange_coe
    (affine a b ha).continuous
  intro p
  have hdist (i j : Fin 4) : dist (a*p i+b) (a*p j+b)=‖a‖*dist (p i) (p j) := by
    rw [dist_add_right,dist_eq_norm,← mul_sub,norm_mul,← dist_eq_norm]
  have haffi (z : ℂ) : affine a b ha (z:Sphere)=((a*z+b:ℂ):Sphere) := rfl
  simp only [haffi,coe_dist,hdist]
  have hp (z : ℂ) : Real.sqrt (‖z‖^2+4) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

lemma inversion_controlled : CannonQM.Controlled inversion (OrderIso.refl _) :=
  inversion_preservesProducts.controlled inversion.injective
lemma affine_controlled (a b : ℂ) (ha : a ≠ 0) :
    CannonQM.Controlled (affine a b ha) (OrderIso.refl _) :=
  (affine_preservesProducts a b ha).controlled (affine a b ha).injective

end CannonMobius

end
end
section
noncomputable section

namespace CannonMetricQC

def WeakQS (f : ℂ → ℂ) (H : ℝ) : Prop :=
  ∀ x y z, dist x y ≤ dist x z → dist (f x) (f y) ≤ H*dist (f x) (f z)
end CannonMetricQC

namespace CannonQM
open Set Metric Filter Bornology

lemma eventually_dist_large (x : ℂ) (R : ℝ) :
    ∀ᶠ w : ℂ in cobounded ℂ, R < dist w x := by
  have hh := (isBounded_closedBall (x:=x) (r:=R)).compl
  have ht : (closedBall x R)ᶜ ∈ cobounded ℂ := hh
  filter_upwards [ht] with w hw
  exact lt_of_not_ge hw

theorem Controlled.plane_weakQS (f : ℂ ≃ₜ ℂ) {η : Distortion}
    (hf : Controlled f η) : CannonMetricQC.WeakQS f (1+2*(η 2 : ℝ)) := by
  intro x y z hxyz
  have hη0 : 0 ≤ (η 2 : ℝ) := (η 2).coe_nonneg
  have hH : 1 ≤ 1+2*(η 2 : ℝ) := by linarith
  by_cases hxy : x=y
  · subst y; simp; positivity
  by_cases hxz : x=z
  · subst z
    have : x=y := dist_eq_zero.mp (le_antisymm (by simpa using hxyz) dist_nonneg)
    exact (hxy this).elim
  by_cases hyz : y=z
  · subst z
    exact le_mul_of_one_le_left dist_nonneg hH
  have ht : Tendsto f (cobounded ℂ) (cobounded ℂ) := by
    simpa only [cobounded_eq_cocompact] using f.isClosedEmbedding.tendsto_cocompact
  have hs := eventually_dist_large y (dist z y)
  have hi := ht.eventually (eventually_dist_large (f z) (dist (f y) (f z)))
  obtain ⟨w,hw,hwi,hwx⟩ := (hs.and (hi.and (eventually_ne_cobounded x))).exists
  have hwy : w ≠ y := by intro he; rw [he,dist_self] at hw; exact not_lt_of_ge dist_nonneg hw
  have hwz : w ≠ z := by intro he; rw [he] at hw; exact (lt_irrefl _ hw)
  have hquad : Distinct x y w z := ⟨hxy,hwx.symm,hxz,hwy.symm,hyz,hwz⟩
  have hsource : dist w z ≤ 2*dist y w := by
    have hh := dist_triangle w y z
    rw [dist_comm z y] at hw
    rw [dist_comm w y] at hw hh
    linarith
  have htarget : dist (f y) (f w) ≤ 2*dist (f w) (f z) := by
    have hh := dist_triangle (f y) (f z) (f w)
    rw [dist_comm (f z) (f w)] at hh
    linarith
  have hp : 0 < dist x z := dist_pos.mpr hxz
  have hpy : 0 < dist y w := dist_pos.mpr hwy.symm
  have hrat : crossRatio x y w z ≤ 2 := by
    have hh : dist x y*dist w z ≤ 2*(dist x z*dist y w) := by
      calc
        _ ≤ dist x z*(2*dist y w) := mul_le_mul hxyz hsource dist_nonneg dist_nonneg
        _ = _ := by ring
    apply NNReal.coe_le_coe.mp
    change dist x y*dist w z/(dist x z*dist y w) ≤ (2:ℝ)
    exact (div_le_iff₀ (mul_pos hp hpy)).mpr hh
  have hc := (hf x y w z hquad).trans (η.monotone hrat)
  have hfxz : 0 < dist (f x) (f z) := dist_pos.mpr (fun he => hxz (f.injective he))
  have hfyw : 0 < dist (f y) (f w) := dist_pos.mpr (fun he => hwy (f.injective he).symm)
  have hfwz : 0 < dist (f w) (f z) := dist_pos.mpr (fun he => hwz (f.injective he))
  have hcR : dist (f x) (f y)*dist (f w) (f z) ≤
      (η 2 : ℝ)*(dist (f x) (f z)*dist (f y) (f w)) := by
    have hh := NNReal.coe_le_coe.mpr hc
    change dist (f x) (f y)*dist (f w) (f z)/(dist (f x) (f z)*dist (f y) (f w)) ≤ (η 2 : ℝ) at hh
    exact (div_le_iff₀ (mul_pos hfxz hfyw)).mp hh
  have he : dist (f x) (f y) ≤ 2*(η 2 : ℝ)*dist (f x) (f z) := by
    apply (mul_le_mul_iff_left₀ hfwz).mp
    calc
      _ ≤ (η 2 : ℝ)*(dist (f x) (f z)*dist (f y) (f w)) := hcR
      _ ≤ (η 2 : ℝ)*(dist (f x) (f z)*(2*dist (f w) (f z))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htarget dist_nonneg) hη0
      _ = _ := by ring
  nlinarith [dist_nonneg (x:=f x) (y:=f z)]
end CannonQM

end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

def sendToInfty (p : Sphere) : Sphere ≃ₜ Sphere := by
  classical
  exact if p=∞ then 1 else inversion*affine 1 (-coordinate p) one_ne_zero

lemma sendToInfty_apply (p : Sphere) : sendToInfty p p=∞ := by
  by_cases hp : p=∞
  · simp [sendToInfty,hp]
  · rw [sendToInfty,ite_eq_right hp,← coe_coordinate hp]
    change inv (((1*coordinate p + -coordinate p):ℂ):Sphere)=∞
    simp

lemma sendToInfty_controlled (p : Sphere) :
    CannonQM.Controlled (sendToInfty p) (OrderIso.refl _) := by
  by_cases hp : p=∞
  · simp only [sendToInfty,ite_eq_left hp]
    exact fun _ _ _ _ _ => le_rfl
  · rw [sendToInfty,ite_eq_right hp]
    exact inversion_controlled.comp (affine_controlled 1 (-coordinate p) one_ne_zero)
      (affine 1 (-coordinate p) one_ne_zero).injective

lemma restriction_controlled (f : Sphere ≃ₜ Sphere) (hf : f ∞=∞)
    {η : CannonQM.Distortion} (hη : CannonQM.Controlled f η) :
    CannonQM.Controlled (finiteRestriction f hf) η := by
  intro x y z w hh
  have hcoe : Function.Injective (fun z : ℂ => (z:Sphere)) := OnePoint.coe_injective
  have h := hη (x:Sphere) (y:Sphere) (z:Sphere) (w:Sphere) (hh.map hcoe)
  have he (u : ℂ) : f (u:Sphere)=((finiteRestriction f hf u:ℂ):Sphere) :=
    (coe_coordinate (coe_map_ne_infty f hf u)).symm
  simpa only [he,coe_crossRatio] using h

theorem normalized_weakQS (f : Sphere ≃ₜ Sphere) {η : CannonQM.Distortion}
    (hf : CannonQM.Controlled f η) :
    ∃ (M : Sphere ≃ₜ Sphere) (hM : (M*f) ∞=∞),
      M ∈ biholomorphic ∧
      CannonMetricQC.WeakQS (finiteRestriction (M*f) hM) (1+2*(η 2:ℝ)) := by
  let M := sendToInfty (f ∞)
  have hM : (M*f) ∞=∞ := sendToInfty_apply (f ∞)
  refine ⟨M,hM,?_,?_⟩
  · by_cases hp : f ∞=∞
    · simp [M,sendToInfty,hp]
    · exact (by
        dsimp [M,sendToInfty]
        rw [ite_eq_right hp]
        exact biholomorphic.mul_mem inversion_biholomorphic
          (affine_biholomorphic 1 (-coordinate (f ∞)) one_ne_zero))
  · apply CannonQM.Controlled.plane_weakQS
    apply restriction_controlled
    exact (sendToInfty_controlled (f ∞)).comp hf f.injective

end CannonMobius

end
end
section
noncomputable section
namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

def DensityOne (s : Set ℂ) (x : ℂ) : Prop :=
  Tendsto (fun r : ℝ => volume (s ∩ closedBall x r)/volume (closedBall x r))
    (𝓝[>] 0) (𝓝 1)

theorem DensityOne.approximate {s : Set ℂ} (_hs : MeasurableSet s) {x : ℂ}
    (hx : x ∈ s) (hd : DensityOne s x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℂ, dist x y < δ →
      ∃ z ∈ s, dist y z ≤ ε*dist x y := by
  let e := min ε 1
  have he : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have hlim : Tendsto (fun r : ℝ =>
      (volume (s ∩ closedBall x r)/volume (closedBall x r)).toReal)
      (𝓝[>] 0) (𝓝 (1:ℝ)) := by
    simpa only [ENNReal.toReal_one,Function.comp_def] using
      (ENNReal.tendsto_toReal (by norm_num : (1:ℝ≥0∞) ≠ ∞)).comp hd
  have hev := hlim.eventually (lt_mem_nhds (show (1:ℝ)-e^2/8 < 1 by nlinarith [sq_pos_of_pos he]))
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨δ/2,by positivity,?_⟩
  intro y hy
  by_cases hxy : x=y
  · subst y
    exact ⟨x,hx,by simp⟩
  have hp : 0 < dist x y := dist_pos.mpr hxy
  by_contra! hhole
  have hdis : Disjoint (s ∩ closedBall x (2*dist x y)) (ball y (e*dist x y)) := by
    apply Set.disjoint_left.mpr
    intro z hzs hzb
    have h₁ := hhole z hzs.1
    have h₂ : dist y z < e*dist x y := by simpa only [mem_ball,dist_comm] using hzb
    have h₃ := mul_le_mul_of_nonneg_right heε hp.le
    linarith
  have hsub : (s ∩ closedBall x (2*dist x y)) ∪ ball y (e*dist x y) ⊆ closedBall x (2*dist x y) := by
    apply union_subset inter_subset_right
    intro z hz
    have hz' : dist z y < e*dist x y := mem_ball.mp hz
    have ht := dist_triangle z y x
    have hh := mul_le_mul_of_nonneg_right he1 hp.le
    rw [dist_comm y x] at ht
    change dist z x ≤ 2*dist x y
    linarith
  have hm := measure_mono (μ:=volume) hsub
  rw [measure_union hdis isOpen_ball.measurableSet] at hm
  have hfin : volume (closedBall x (2*dist x y)) ≠ ∞ := (isCompact_closedBall _ _).measure_ne_top
  have hr := ENNReal.toReal_mono hfin hm
  have hsf : volume (s ∩ closedBall x (2*dist x y)) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_right)
  have hbf : volume (ball y (e*dist x y)) ≠ ∞ := measure_ball_ne_top
  rw [ENNReal.toReal_add hsf hbf] at hr
  have hvc (r : ℝ) (hr : 0 ≤ r) : (volume (closedBall x r)).toReal=r^2*Real.pi := by
    simp only [Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr,ENNReal.coe_toReal,NNReal.coe_real_pi]
  have hvb : (volume (ball y (e*dist x y))).toReal=(e*dist x y)^2*Real.pi := by
    simp only [Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (mul_nonneg he.le hp.le),ENNReal.coe_toReal,NNReal.coe_real_pi]
  rw [hvc _ (by positivity),hvb] at hr
  have hmem : 2*dist x y ∈ ball (0:ℝ) δ ∩ Ioi 0 := by
    constructor
    · have h2p : 0 < 2*dist x y := by linarith
      simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos h2p] using
        (show 2*dist x y < δ by linarith)
    · change 0 < 2*dist x y
      positivity
  have hnear := hδb hmem
  change 1-e^2/8 < (volume (s ∩ closedBall x (2*dist x y))/volume (closedBall x (2*dist x y))).toReal at hnear
  rw [ENNReal.toReal_div,hvc _ (by positivity)] at hnear
  have hvp : 0 < (2*dist x y)^2*Real.pi := by positivity
  have hh := (lt_div_iff₀ hvp).mp hnear
  have hp' : 0 < e^2*(dist x y)^2*Real.pi := by positivity
  nlinarith
end CannonMetricQC

namespace CannonMetricQC
open Set Metric MeasureTheory Filter Asymptotics
open scoped Topology ENNReal NNReal

theorem derivative_of_density {f : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hlip : ∀ z ∈ s, ∀ y, dist z y < r → dist (f z) (f y) ≤ C*dist z y)
    {x : ℂ} (hx : x ∈ s) (hd : DensityOne s x) {A : ℂ →L[ℝ] ℂ}
    (ha : HasFDerivWithinAt f A s x) : HasFDerivAt f A x := by
  apply HasFDerivAt.of_isLittleO
  apply isLittleO_iff.mpr
  intro ε hε
  let P := C+‖A‖+1
  have hP : 0 < P := by dsimp [P]; positivity
  let e := min (1/2:ℝ) (ε/(4*P))
  have he : 0 < e := lt_min (by norm_num) (div_pos hε (by positivity))
  have he1 : e ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have heP : (C+‖A‖)*e ≤ ε/4 := by
    have h := min_le_right (1/2:ℝ) (ε/(4*P))
    have hh := (le_div_iff₀ (show 0 < 4*P by positivity)).mp h
    have hsmall : (C+‖A‖)*e ≤ P*e := mul_le_mul_of_nonneg_right (by dsimp [P]; linarith) he.le
    nlinarith
  obtain ⟨d,hdp,hda⟩ := hd.approximate hs hx he
  have hev := (isLittleO_iff.mp ha.isLittleO) (show 0 < ε/4 by positivity)
  obtain ⟨b,hbp,hba⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let t := min d (min (b/2) (r/2))
  have htp : 0 < t := lt_min hdp (lt_min (by positivity) (by positivity))
  filter_upwards [ball_mem_nhds x htp] with y hy
  have hxy : dist x y < t := by simpa only [mem_ball,dist_comm] using hy
  have hyd : dist x y < d := hxy.trans_le (min_le_left _ _)
  have hyb : dist x y < b/2 := hxy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hyr : dist x y < r/2 := hxy.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨z,hzs,hz⟩ := hda y hyd
  have hyz : dist y z ≤ dist x y := hz.trans (by nlinarith [dist_nonneg (x:=x) (y:=y)])
  have hxz : dist x z ≤ 2*dist x y := (dist_triangle x y z).trans (by linarith)
  have hzb : z ∈ ball x b ∩ s := by
    refine ⟨?_,hzs⟩
    change dist z x < b
    rw [dist_comm]
    linarith
  have hrem := hba hzb
  change ‖f z-f x-A (z-x)‖ ≤ ε/4*‖z-x‖ at hrem
  have hzy : dist z y < r := by rw [dist_comm]; linarith
  have hfl := hlip z hzs y hzy
  have hid : f y-f x-A (y-x)=(f y-f z)+(f z-f x-A (z-x))-A (y-z) := by
    simp only [map_sub]
    abel
  have hnorm : ‖f y-f x-A (y-x)‖ ≤ dist (f y) (f z)+ε/4*dist x z+‖A‖*dist y z := by
    rw [hid]
    calc
      _ ≤ ‖f y-f z‖+‖f z-f x-A (z-x)‖+‖A (y-z)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by
        rw [← dist_eq_norm z x, dist_comm z x] at hrem
        rw [← dist_eq_norm (f y) (f z)]
        exact add_le_add (add_le_add le_rfl hrem)
          (by simpa only [dist_eq_norm] using A.le_opNorm (y-z))
  have hmult := mul_le_mul_of_nonneg_right heP (dist_nonneg (x:=x) (y:=y))
  have hzlin := mul_le_mul_of_nonneg_left hz (add_nonneg hC (norm_nonneg A))
  have hxzlin := mul_le_mul_of_nonneg_left hxz (show 0 ≤ ε/4 by positivity)
  rw [dist_comm (f z) (f y),dist_comm z y] at hfl
  change ‖f y-f x-A (y-x)‖ ≤ ε*‖y-x‖
  rw [← dist_eq_norm y x,dist_comm y x]
  nlinarith [dist_nonneg (x:=x) (y:=y)]
end CannonMetricQC

namespace CannonMetricQC
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal

def PointwiseLip (f : ℂ → ℂ) (x : ℂ) : Prop :=
  ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ y, dist x y < r → dist (f x) (f y) ≤ C*dist x y

def lipPiece (f : ℂ → ℂ) (n : ℕ) : Set ℂ :=
  {x | ‖x‖ ≤ (n:ℝ)+1 ∧ ∀ y, dist x y < 1/((n:ℝ)+1) →
    dist (f x) (f y) ≤ (n:ℝ)*dist x y}

lemma lipPiece_closed {f : ℂ → ℂ} (hf : Continuous f) (n : ℕ) : IsClosed (lipPiece f n) := by
  have hy (y : ℂ) : IsClosed {x | dist x y < 1/((n:ℝ)+1) →
      dist (f x) (f y) ≤ (n:ℝ)*dist x y} := by
    have h₁ : IsClosed {x : ℂ | 1/((n:ℝ)+1) ≤ dist x y} :=
      isClosed_le continuous_const (continuous_id.dist continuous_const)
    have h₂ : IsClosed {x : ℂ | dist (f x) (f y) ≤ (n:ℝ)*dist x y} :=
      isClosed_le (hf.dist continuous_const) (continuous_const.mul (continuous_id.dist continuous_const))
    have hh := h₁.union h₂
    convert hh using 1
    ext x
    simp only [mem_ofPred_eq,mem_union,← not_lt]
    tauto
  have h₁ : IsClosed {x : ℂ | ‖x‖ ≤ (n:ℝ)+1} := isClosed_le continuous_norm continuous_const
  have hh := h₁.inter (isClosed_iInter hy)
  convert hh using 1
  ext x
  simp only [lipPiece,mem_ofPred_eq,mem_inter_iff,mem_iInter]

lemma lipPiece_lipschitz {f : ℂ → ℂ} (hf : Continuous f) (n : ℕ) :
    ∃ L : ℝ≥0, LipschitzOnWith L f (lipPiece f n) := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) ((n:ℝ)+1)).exists_bound_of_continuousOn hf.continuousOn
  have hMp : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by simp; positivity))
  let L : ℝ≥0 := ⟨(n:ℝ)+2*M*((n:ℝ)+1),by positivity⟩
  refine ⟨L,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hnx : ‖f x‖ ≤ M := hM x (by simpa only [mem_closedBall,dist_zero_right] using hx.1)
  have hny : ‖f y‖ ≤ M := hM y (by simpa only [mem_closedBall,dist_zero_right] using hy.1)
  change dist (f x) (f y) ≤ ((n:ℝ)+2*M*((n:ℝ)+1))*dist x y
  by_cases hd : dist x y < 1/((n:ℝ)+1)
  · exact (hx.2 y hd).trans (mul_le_mul_of_nonneg_right (by nlinarith) dist_nonneg)
  · have hd' : 1 ≤ ((n:ℝ)+1)*dist x y := by
      have hn : 0 < (n:ℝ)+1 := by positivity
      exact (div_le_iff₀ hn).mp (le_of_not_gt hd) |>.trans_eq (mul_comm _ _)
    have ht : dist (f x) (f y) ≤ 2*M := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith)
    have hm := mul_le_mul_of_nonneg_left hd' (show 0 ≤ 2*M by positivity)
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (dist_nonneg (x:=x) (y:=y))]

lemma PointwiseLip.mem_lipPiece {f : ℂ → ℂ} {x : ℂ} (hx : PointwiseLip f x) :
    ∃ n : ℕ, x ∈ lipPiece f n := by
  obtain ⟨C,r,hC,hr,h⟩ := hx
  obtain ⟨n,hn⟩ := exists_nat_gt (max C (max (1/r) ‖x‖))
  have hnC : C < (n:ℝ) := (le_max_left _ _).trans_lt hn
  have hnr : 1/r < (n:ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hn
  have hnx : ‖x‖ < (n:ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hn
  have hn1 : 0 < (n:ℝ)+1 := by positivity
  have hrad : 1/((n:ℝ)+1) ≤ r := by
    apply (div_le_iff₀ hn1).mpr
    have hh := (div_lt_iff₀ hr).mp hnr
    nlinarith
  refine ⟨n, ?_⟩
  change ‖x‖ ≤ (n:ℝ)+1 ∧ _
  refine ⟨by linarith, ?_⟩
  intro y hy
  exact (h y (hy.trans_le hrad)).trans (mul_le_mul_of_nonneg_right hnC.le dist_nonneg)

theorem continuous_ae_differentiable_of_pointwiseLip {f : ℂ → ℂ} (hf : Continuous f)
    (hp : ∀ᵐ x ∂volume, PointwiseLip f x) : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := by
  have hpiece (n : ℕ) : ∀ᵐ x ∂volume, x ∈ lipPiece f n → DifferentiableAt ℝ f x := by
    obtain ⟨L,hL⟩ := lipPiece_lipschitz hf n
    have hm := (lipPiece_closed hf n).measurableSet
    filter_upwards [hL.ae_differentiableWithinAt_of_mem (μ:=volume),
      Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hm] with x hdx hdens hx
    have hd : DensityOne (lipPiece f n) x := by
      simpa only [DensityOne,indicator_of_mem hx,Pi.one_apply] using hdens
    exact (derivative_of_density hm (Nat.cast_nonneg n) (by positivity)
      (fun z hz y hy => hz.2 y hy) hx hd (hdx hx).hasFDerivWithinAt).differentiableAt
  filter_upwards [ae_all_iff.mpr hpiece,hp] with x hx hp
  obtain ⟨n,hn⟩ := hp.mem_lipPiece
  exact hx n hn
end CannonMetricQC

end
end
end
end
end
end
end
end
end
end
end

end OAI
