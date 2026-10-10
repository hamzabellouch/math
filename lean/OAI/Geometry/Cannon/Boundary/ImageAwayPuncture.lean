import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryDist
import OAI.Geometry.Cannon.Conformal.SphereTwo

namespace OAI

section
section
section
section
section
section
noncomputable section
noncomputable section
open Set Topology

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonPaths
open Set Metric

variable {X : Type*} [MetricSpace X]

lemma image_away_from_puncture {x y q : X} {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hy : dist x y ≤ R) (hq : 2*R ≤ dist x q) (f : X → X)
    (h : R*dist y q ≤ L*(dist (f y) (f q)*max R (dist x y)*max R (dist x q))) :
    1/(2*L) ≤ dist (f y) (f q) := by
  have hRq : R ≤ dist x q := by linarith
  rw [max_eq_left hy,max_eq_right hRq] at h
  have hh : dist y q ≤ L*dist (f y) (f q)*dist x q := by
    apply (mul_le_mul_iff_right₀ hR).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  have ht := dist_triangle x y q
  have hdq : 0 < dist x q := lt_of_lt_of_le hR hRq
  apply (div_le_iff₀ (by positivity : 0 < 2*L)).mpr
  have hh' : dist x q ≤ (dist (f y) (f q)*(2*L))*dist x q := by nlinarith
  exact (mul_le_mul_iff_left₀ hdq).mp (by simpa only [one_mul] using hh')

lemma preimage_near_center {x y q : X} {R C e d : ℝ}
    (hR : 0 < R) (hC : 0 < C) (he : 0 < e) (hd : 0 < d)
    (hq : d ≤ dist x q) (hdiam : dist y q ≤ 1) (f : X → X)
    (hfar : e < dist (f y) (f q))
    (h : dist (f y) (f q)*max R (dist x y)*max R (dist x q) ≤ C*R*dist y q) :
    dist x y < (C/(e*d)+1)*R := by
  have hxy := dist_nonneg (x := x) (y := y)
  have hRq : 0 ≤ max R (dist x q) := hR.le.trans (le_max_left _ _)
  have hRy : 0 ≤ max R (dist x y) := hR.le.trans (le_max_left _ _)
  have h1 : e*dist x y*d ≤ dist (f y) (f q)*max R (dist x y)*max R (dist x q) :=
    mul_le_mul (mul_le_mul hfar.le (le_max_right _ _) hxy (dist_nonneg))
      (hq.trans (le_max_right _ _)) hd.le (mul_nonneg dist_nonneg hRy)
  have h2 : e*dist x y*d ≤ C*R := h1.trans (h.trans (mul_le_of_le_one_right (mul_nonneg hC.le hR.le) hdiam))
  have h3 : dist x y ≤ C/(e*d)*R := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (mul_pos he hd)).mpr
    nlinarith
  nlinarith

end CannonPaths

namespace CannonRelease
open CannonGraph CannonVisual CannonPaths Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

theorem boundary_controlled_paths (φ : Boundary D ≃ₜ SphereTwo) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (x u v : Boundary D) (s : ℝ), 0 < s →
      boundaryDist D hδ x u ≤ s → boundaryDist D hδ x v ≤ s →
      JoinedIn {z | boundaryDist D hδ x z < L*s} u v := by
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : PathConnectedSpace SphereTwo := CannonPaths.sphere_pathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  let _ : PathConnectedSpace (Boundary D) := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  have hpuncture (p : Boundary D) : IsPathConnected ({p}ᶜ : Set (Boundary D)) := by
    have hh := (CannonPaths.sphere_punctured_pathConnected (φ p)).image φ.symm.continuous
    convert hh using 1
    ext z
    constructor
    · intro hz
      refine ⟨φ z,?_,φ.symm_apply_apply z⟩
      exact fun h => hz (φ.injective h)
    · rintro ⟨w,hw,hwz⟩ heq
      apply hw
      apply φ.symm.injective
      change z = p at heq
      simpa only [φ.symm_apply_apply] using hwz.trans heq
  let p : SphereTwo := ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ),by simp⟩
  let a := φ.symm p
  let b := φ.symm (-p)
  have hab : a ≠ b := fun h => (ne_neg_of_mem_unit_sphere ℝ p) (φ.symm.injective h)
  let d := dist a b/2
  have hd : 0 < d := half_pos (dist_pos.mpr hab)
  have hfar (x : Boundary D) : ∃ q : Boundary D, d ≤ dist x q := by
    by_cases h : d ≤ dist x a
    · exact ⟨a,h⟩
    · refine ⟨b,?_⟩
      have hh := dist_triangle a x b
      rw [dist_comm a x] at hh
      dsimp [d] at *
      linarith
  let C := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let B := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := Real.exp_pos _
  obtain ⟨e,he,hpaths⟩ := CannonPaths.uniform_avoidance hpuncture
    (show 0 < 1/(2*B) by positivity)
  let t := min 1 (d/(2*A))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hd (by positivity))
  let F := (C/(e*d)+1)*A
  have hF : 0 < F := mul_pos (by positivity) hA
  let L := F+1/t+1
  have hL : 1 ≤ L := by
    have : 0 < 1/t := one_div_pos.mpr ht
    dsimp [L]
    linarith
  refine ⟨L,hL,fun x u v s hs hu hv => ?_⟩
  by_cases hsmall : s ≤ t
  · obtain ⟨k,hk,hk'⟩ := visualScale_near δ hs (hsmall.trans (min_le_left _ _))
    obtain ⟨r,hr⟩ := Quotient.exists_rep x
    subst x
    obtain ⟨q,hq⟩ := hfar (Quotient.mk' r)
    let f := boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹
    have hp : 2*visualScale δ k ≤ boundaryDist D hδ (Quotient.mk' r) q := by
      have hh : 2*A*s ≤ d := by
        have hh := (le_div_iff₀ (by positivity : 0 < 2*A)).mp (hsmall.trans (min_le_right _ _))
        nlinarith
      have hh' : visualScale δ k ≤ A*s := hk'
      nlinarith
    have hu' : 1/(2*B) ≤ dist (f u) (f q) := image_away_from_puncture (X := Boundary D)
      (visualScale_pos δ k) hB (hu.trans hk) hp f (visual_expansion_ray D hδ r k u q).2
    have hv' : 1/(2*B) ≤ dist (f v) (f q) := image_away_from_puncture (X := Boundary D)
      (visualScale_pos δ k) hB (hv.trans hk) hp f (visual_expansion_ray D hδ r k v q).2
    have hj := hpaths (f q) (f u) (f v) (by simpa only [dist_comm] using hu')
      (by simpa only [dist_comm] using hv')
    have hm := hj.map f.symm.continuous.continuousOn
    simp only [f.symm_apply_apply] at hm
    apply hm.mono
    rintro z ⟨w,hw,rfl⟩
    have hz : boundaryDist D hδ (Quotient.mk' r) (f.symm w) < (C/(e*d)+1)*visualScale δ k := by
      apply preimage_near_center (X := Boundary D) (visualScale_pos δ k) hC he hd hq
        (boundaryDist_le_one D hδ _ _) f _ (visual_expansion_ray D hδ r k (f.symm w) q).1
      change e < dist (f q) w at hw
      simpa only [f.apply_symm_apply,dist_comm] using hw
    have hc : 0 ≤ C/(e*d)+1 := by positivity
    have hf : F ≤ L := by
      have : 0 < 1/t := one_div_pos.mpr ht
      dsimp [L]; linarith
    calc
      _ < (C/(e*d)+1)*visualScale δ k := hz
      _ ≤ (C/(e*d)+1)*(A*s) := mul_le_mul_of_nonneg_left hk' hc
      _ = F*s := by dsimp [F]; ring
      _ ≤ L*s := mul_le_mul_of_nonneg_right hf hs.le
  · have hts : t < s := lt_of_not_ge hsmall
    have hbig : 1 < L*s := by
      have hst : 1 < s/t := (lt_div_iff₀ ht).mpr (by simpa using hts)
      have hh : s/t ≤ L*s := by
        have hle : 1/t ≤ L := by dsimp [L]; linarith
        simpa only [one_div,inv_mul_eq_div] using mul_le_mul_of_nonneg_right hle hs.le
      exact hst.trans_le hh
    exact (joinedIn_univ.mpr (PathConnectedSpace.joined u v)).mono (fun z _ =>
      (boundaryDist_le_one D hδ x z).trans_lt hbig)

end CannonRelease

namespace CannonPaths
open Set Metric

lemma expansion_endpoint_clearance {R B A s d q : ℝ}
    (hR : 0<R) (hB : 0<B) (hA : 1 ≤ A) (hs : 0<s) (hq : 0 ≤ q)
    (hsd : s ≤ d) (hRA : R ≤ A*s)
    (hexp : R*d ≤ B*(q*R*max R d)) : 1/(B*A) ≤ q := by
  have hd : 0<d := hs.trans_le hsd
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hmax : max R d ≤ A*d := max_le
    (hRA.trans (mul_le_mul_of_nonneg_left hsd hAp.le)) (by nlinarith)
  have hc : d ≤ B*q*max R d := by
    apply (mul_le_mul_iff_left₀ hR).mp
    nlinarith [hexp]
  have hm := mul_le_mul_of_nonneg_left hmax (mul_nonneg hB.le hq)
  have hh : 1 ≤ B*A*q := by nlinarith [hc,hm]
  apply (div_le_iff₀ (mul_pos hB hAp)).mpr
  nlinarith

lemma expansion_preimage_clearance {R C s d q e : ℝ}
    (hR : 0<R) (hC : 0<C) (hs : 0<s) (hsR : s ≤ R)
    (he : 0<e) (heq : e<q)
    (hexp : q*R*max R d ≤ C*R*d) : (e/C)*s<d := by
  have hq : 0<q := he.trans heq
  have hc : q*max R d ≤ C*d := by
    apply (mul_le_mul_iff_right₀ hR).mp
    nlinarith [hexp]
  have hm := mul_le_mul_of_nonneg_left (le_max_left R d) hq.le
  have heq' := mul_lt_mul_of_pos_right heq hs
  have hsR' := mul_le_mul_of_nonneg_left hsR hq.le
  have ht : e*s<C*d := by linarith
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ hC).mpr (by nlinarith)

end CannonPaths

namespace CannonRelease
open CannonGraph CannonVisual CannonPaths Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance : Setoid (BasedRay D) := raySetoid D

theorem boundary_outside_paths (φ : Boundary D ≃ₜ SphereTwo) :
    ∃ c : ℝ, 0<c ∧ c ≤ 1 ∧ ∀ (x u v : Boundary D) (s : ℝ), 0<s →
      s ≤ boundaryDist D hδ x u → s ≤ boundaryDist D hδ x v →
      JoinedIn {z | c*s < boundaryDist D hδ x z} u v := by
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  have hpuncture (p : Boundary D) : IsPathConnected ({p}ᶜ : Set (Boundary D)) := by
    have hh := (CannonPaths.sphere_punctured_pathConnected (φ p)).image φ.symm.continuous
    convert hh using 1
    ext z
    constructor
    · intro hz
      refine ⟨φ z,?_,φ.symm_apply_apply z⟩
      exact fun h => hz (φ.injective h)
    · rintro ⟨w,hw,hwz⟩ heq
      apply hw
      apply φ.symm.injective
      change z=p at heq
      simpa only [φ.symm_apply_apply] using hwz.trans heq
  let C := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let B := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hC : 0<C := by dsimp [C]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hA : 1 ≤ A := Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) (visualExponent_pos δ).le)
  have hAp : 0<A := zero_lt_one.trans_le hA
  obtain ⟨e,he,hpaths⟩ := CannonPaths.uniform_avoidance hpuncture
    (show 0<1/(B*A) by positivity)
  let c := min 1 (e/C)
  have hc : 0<c := lt_min zero_lt_one (div_pos he hC)
  refine ⟨c,hc,min_le_left _ _,?_⟩
  intro x u v s hs hu hv
  have hsone : s ≤ 1 := hu.trans (boundaryDist_le_one D hδ x u)
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hs hsone
  obtain ⟨r,hr⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryHomeomorph D ⟨δ,hδ⟩ (r.val k)⁻¹
  have hself : boundaryDist D hδ (Quotient.mk' r) (Quotient.mk' r) = 0 := dist_self _
  have hund (y : Boundary D) (hy : s ≤ boundaryDist D hδ (Quotient.mk' r : Boundary D) y) :
      1/(B*A) ≤ (boundaryDist D hδ) (f (Quotient.mk' r : Boundary D)) (f y) := by
    apply expansion_endpoint_clearance (visualScale_pos δ k) hB hA hs dist_nonneg hy hk'
    have h := (visual_expansion_ray D hδ r k (Quotient.mk' r : Boundary D) y).2
    change visualScale δ k*(boundaryDist D hδ) (Quotient.mk' r : Boundary D) y ≤ B*((boundaryDist D hδ) (f (Quotient.mk' r : Boundary D)) (f y)*
      max (visualScale δ k) ((boundaryDist D hδ) (Quotient.mk' r : Boundary D) (Quotient.mk' r : Boundary D))*
      max (visualScale δ k) ((boundaryDist D hδ) (Quotient.mk' r : Boundary D) y)) at h
    simpa only [hself,max_eq_left (visualScale_pos δ k).le] using h
  have hj := hpaths (f (Quotient.mk' r : Boundary D)) (f u) (f v) (hund u hu) (hund v hv)
  have hm := hj.map f.symm.continuous.continuousOn
  simp only [f.symm_apply_apply] at hm
  apply hm.mono
  rintro z ⟨w,hw,rfl⟩
  have h := (visual_expansion_ray D hδ r k (Quotient.mk' r : Boundary D) (f.symm w)).1
  change (boundaryDist D hδ) (f (Quotient.mk' r : Boundary D)) (f (f.symm w))*
    max (visualScale δ k) ((boundaryDist D hδ) (Quotient.mk' r : Boundary D) (Quotient.mk' r : Boundary D))*
    max (visualScale δ k) ((boundaryDist D hδ) (Quotient.mk' r : Boundary D) (f.symm w)) ≤
    C*visualScale δ k*(boundaryDist D hδ) (Quotient.mk' r : Boundary D) (f.symm w) at h
  simp only [f.apply_symm_apply,hself,max_eq_left (visualScale_pos δ k).le] at h
  have hclear := expansion_preimage_clearance (visualScale_pos δ k) hC hs hk he hw h
  exact (mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (e/C)) hs.le).trans_lt hclear

end CannonRelease

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
