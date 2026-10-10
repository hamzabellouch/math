import OAI.Combinatorics.PlanarL1.Surgery

namespace OAI

section



namespace PlanarL1.Topology
open Set Metric Filter

lemma frontier_outward_segment {S : Set ℂ} (hS : Convex ℝ S)
    (h0 : S∈nhds (0:ℂ)) {p : ℂ} (hp : p∈frontier S) {b : ℝ} (hb : 1≤b)
    {z : ℂ} (hz : z∈segment ℝ p (b•p)) (hzS : z∈closure S) : z=p := by
  rw [segment_eq_image' ℝ] at hz
  obtain ⟨u,hu,rfl⟩ := hz
  have he : p+u•(b•p-p)=(1+u*(b-1))•p := by module
  dsimp only at hzS ⊢
  rw [he] at hzS ⊢
  have ht : 1≤1+u*(b-1) := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hb)]
  have hg := (gauge_le_one_iff_mem_closure hS h0).mpr hzS
  rw [gauge_smul_of_nonneg (by linarith : 0≤1+u*(b-1)),
    (gauge_eq_one_iff_mem_frontier hS h0).mpr hp,smul_eq_mul,mul_one] at hg
  rw [le_antisymm hg ht,one_smul]

lemma scalar_segment (p : ℂ) {a b : ℝ} (hab : a≤b) {z : ℂ}
    (hz : z∈segment ℝ (a•p) (b•p)) :
    ∃ u∈Icc a b, z=u•p := by
  rw [segment_eq_image' ℝ] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  refine ⟨a+t*(b-a),⟨by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab)],
    by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]⟩,?_⟩
  module

lemma radial_outer_tail {S : Set ℂ} {p : ℂ} {t : ℝ} (ht : t≤1)
    (hout : ∀ s : ℝ, t<s → s•p∉closure S)
    {z : ℂ} (hz : z∈segment ℝ (t•p) p) (hzS : z∈closure S) : z=t•p := by
  obtain ⟨s,hs,he⟩ := scalar_segment p ht (by simpa only [one_smul] using hz)
  have hst : s=t := le_antisymm (le_of_not_gt (fun h => hout s h (he ▸ hzS))) hs.1
  simpa only [hst] using he

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

noncomputable def retubePoint (B : Set V) (c : ℝ) (t : V → ℝ) (v : V) (q : ℂ) (w : V) : ℂ :=
  by classical exact if w=v then q else P.radialPoint B c t w

def retubeRegion (B : Set V) (c : ℝ) (t : V → ℝ) (v : V) (q : ℂ) (d : ForwardDart G) : Set ℂ :=
  P.radialRegion B c t d ∪ {z | Incident d v ∧ z∈segment ℝ (P.point v) q}

/-- Compress a genuine finite drawing into a new convex tube and extend one
leaf along a segment external to the old disk. Every other exposed leaf is
cut exactly at the new frontier. The exterior residual tails meet the new
closed disk only at their new ports. -/
lemma retube_extend {S T : Set ℂ} {B : Set V} {v : V} {q : ℂ}
    (hS : Convex ℝ S) (hS0 : S∈nhds (0:ℂ)) (hSb : Bornology.IsBounded S)
    (hpoint : ∀ w, P.point w∈closure S)
    (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
    (hport : ∀ w∈B, P.point w∈frontier S)
    (hleaf : ∀ w∈B, ∀ a b, G.Adj w a → G.Adj w b → a=b)
    (hv : v∈B) (hT : Convex ℝ T) (hTop : IsOpen T) (hT0 : (0:ℂ)∈T)
    (hTv : P.point v∈T) (hqT : q∈closure T)
    (hout : ∀ w∈B, w≠v → P.point w∉closure T)
    (hext : ∀ z, z∈segment ℝ (P.point v) q → z∈closure S → z=P.point v) :
    ∃ (c : ℝ) (t : V → ℝ) (Q : PLDrawing G), 0<c ∧ c<1 ∧ t v=1 ∧
      (∀ w∈B, c<t w ∧ t w≤1) ∧ Q.point=P.retubePoint B c t v q ∧
      (∀ d, (Q.chain d).trace ⊆ P.retubeRegion B c t v q d) ∧
      (∀ d, (Q.chain d).trace ⊆ closure T) ∧
      (∀ w, Q.point w∈closure T) ∧
      (∀ w∈B, w≠v → Q.point w∈frontier T) ∧
      (∀ w∈B, w≠v → ∀ z, z∈segment ℝ (Q.point w) (P.point w) →
        z∈closure T → z=Q.point w) := by
  classical
  obtain ⟨c,t,hc,hc1,hcore,htv,ht,hfront,htail⟩ :=
    capsule_radial_data P.point hSb hpoint hT hTop hT0 hout
  obtain ⟨R,hRp,hR⟩ := P.radial_leaf_ports hS hS0 hpoint hport hc hc1 ht htrace hleaf
  have hRpoint (w : V) : R.point w=P.radialPoint B c t w := congrFun hRp w
  have hRpv : R.point v=P.point v := by
    rw [hRpoint]; simp only [radialPoint,ite_eq_left hv,htv,one_smul]
  have hRsubset (d : ForwardDart G) : (R.chain d).trace ⊆ closure S := by
    apply (hR d).trans
    apply P.radialRegion_subset_convex hS.closure
    · intro e z hz
      obtain ⟨z,hz,rfl⟩ := hz
      have : c•z∈segment ℝ 0 z := by
        rw [segment_eq_image' ℝ]; exact ⟨c,⟨hc.le,hc1.le⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (htrace e hz) this
    · intro w hw
      have : t w•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨t w,⟨hc.le.trans (ht w hw).1.le,(ht w hw).2⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
  have hRpts (w : V) : R.point w∈closure S := by
    rw [hRpoint]; unfold radialPoint
    split_ifs with hw
    · have : t w•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨t w,⟨hc.le.trans (ht w hw).1.le,(ht w hw).2⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
    · have : c•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨c,⟨hc.le,hc1.le⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
  have hcross (d : ForwardDart G) (z : ℂ) (hz : z∈(R.chain d).trace)
      (hz' : z∈segment ℝ (P.point v) q) : z=R.point v :=
    (hext z hz' (hRsubset d hz)).trans hRpv.symm
  have hvertex (w : V) (hw : R.point w∈segment ℝ (P.point v) q) : w=v :=
    R.point_injective ((hext (R.point w) hw (hRpts w)).trans hRpv.symm)
  obtain ⟨Q,hQp,hQ⟩ := R.move_leaf (hleaf v hv)
    (right_mem_segment ℝ _ _)
    hvertex hcross (by rw [hRpv]; exact Relation.ReflTransGen.single (fun _ h => h))
  have hpQ : Q.point=P.retubePoint B c t v q := by
    rw [hQp]; funext w
    simp only [movedPoint,retubePoint,hRpoint]
  have hregQ (d : ForwardDart G) : (Q.chain d).trace ⊆ P.retubeRegion B c t v q d := by
    intro z hz
    rcases hQ d hz with hz|hz
    · exact Or.inl (hR d hz)
    · exact Or.inr hz
  have hregT (d : ForwardDart G) : P.radialRegion B c t d ⊆ closure T := by
    apply P.radialRegion_subset_convex hT.closure
    · intro e z hz
      exact subset_closure (hcore (Set.image_mono (htrace e) hz))
    · intro w hw
      by_cases he : w=v
      · subst w; simpa only [htv,one_smul] using subset_closure hTv
      · exact frontier_subset_closure (hfront w hw he)
  refine ⟨c,t,Q,hc,hc1,htv,ht,hpQ,hregQ,?_,?_,?_,?_⟩
  · intro d z hz
    rcases hregQ d hz with hz|hz
    · exact hregT d hz
    · exact hT.closure.segment_subset (subset_closure hTv) hqT hz.2
  · intro w
    rw [congrFun hpQ w]
    simp only [retubePoint,radialPoint]
    split_ifs with he hw
    · exact hqT
    · exact frontier_subset_closure (hfront w hw he)
    · exact subset_closure (hcore ⟨P.point w,hpoint w,rfl⟩)
  · intro w hw he
    rw [congrFun hpQ w]
    simpa only [retubePoint,ite_eq_right he,radialPoint,ite_eq_left hw] using hfront w hw he
  · intro w hw he z hz hzT
    have hpw : Q.point w=t w•P.point w := by
      rw [congrFun hpQ w]; simp only [retubePoint,ite_eq_right he,radialPoint,ite_eq_left hw]
    rw [hpw] at hz ⊢
    exact radial_outer_tail (ht w hw).2 (htail w hw he) hz hzT

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

lemma radialRegion_old {S : Set ℂ} {B : Set V} {c : ℝ} {t : V → ℝ}
    (hS : Convex ℝ S) (h0 : S∈nhds (0:ℂ)) (hc : 0≤c) (hc1 : c≤1)
    (hpoint : ∀ w, P.point w∈closure S)
    (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
    (ht : ∀ w∈B, 0≤t w ∧ t w≤1) (d : ForwardDart G) :
    P.radialRegion B c t d ⊆ closure S := by
  apply P.radialRegion_subset_convex hS.closure
  · intro e z hz
    obtain ⟨z,hz,rfl⟩ := hz
    have : c•z∈segment ℝ 0 z := by
      rw [segment_eq_image' ℝ]; exact ⟨c,⟨hc,hc1⟩,by simp⟩
    exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds h0)) (htrace e hz) this
  · intro w hw
    have : t w•P.point w∈segment ℝ 0 (P.point w) := by
      rw [segment_eq_image' ℝ]; exact ⟨t w,ht w hw,by simp⟩
    exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds h0)) (hpoint w) this

/-- The exact geometric output needed when retubing a tree with exterior stems.
The old disk may be discarded, but no new curve leaves it except along the
selected stem segment. -/
structure PortMove (p : V → ℂ) (Q : PLDrawing G) (B : Set V) (v : V) (q : ℂ) (S T : Set ℂ) : Prop where
  selected : Q.point v=q
  point_mem : ∀ w, Q.point w∈closure T
  trace_mem : ∀ d, (Q.chain d).trace ⊆ closure T
  point_control : ∀ w, Q.point w∈closure S ∪ segment ℝ (p v) q
  trace_control : ∀ d, (Q.chain d).trace ⊆ closure S ∪ segment ℝ (p v) q
  on_frontier : ∀ w∈B, w≠v → Q.point w∈frontier T
  tail_old : ∀ w∈B, w≠v → segment ℝ (Q.point w) (p w) ⊆ closure S
  tail_frontier : ∀ w∈B, w≠v → ∀ z∈segment ℝ (Q.point w) (p w),
    z∈frontier S → z=p w
  tail_new : ∀ w∈B, w≠v → ∀ z∈segment ℝ (Q.point w) (p w),
    z∈closure T → z=Q.point w
  tails_disjoint : ∀ w∈B, w≠v → ∀ u∈B, u≠v → w≠u →
    Disjoint (segment ℝ (Q.point w) (p w)) (segment ℝ (Q.point u) (p u))

lemma retube_controlled {S T : Set ℂ} {B : Set V} {v : V} {q : ℂ}
    (hS : Convex ℝ S) (hS0 : S∈nhds (0:ℂ)) (hSb : Bornology.IsBounded S)
    (hpoint : ∀ w, P.point w∈closure S)
    (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
    (hport : ∀ w∈B, P.point w∈frontier S)
    (hleaf : ∀ w∈B, ∀ a b, G.Adj w a → G.Adj w b → a=b)
    (hv : v∈B) (hT : Convex ℝ T) (hTop : IsOpen T) (hT0 : (0:ℂ)∈T)
    (hTv : P.point v∈T) (hqT : q∈closure T)
    (hout : ∀ w∈B, w≠v → P.point w∉closure T)
    (hext : ∀ z, z∈segment ℝ (P.point v) q → z∈closure S → z=P.point v) :
    ∃ Q : PLDrawing G, PortMove P.point Q B v q S T := by
  classical
  obtain ⟨c,t,Q,hc,hc1,htv,ht,hQ,hreg,hTQ,hpointT,hfront,htail⟩ :=
    P.retube_extend hS hS0 hSb hpoint htrace hport hleaf hv hT hTop hT0 hTv hqT hout hext
  have hp (w : V) : Q.point w=P.retubePoint B c t v q w := congrFun hQ w
  have hpv : Q.point v=q := by rw [hp]; simp [retubePoint]
  have hpw (w : V) (hw : w∈B) (he : w≠v) : Q.point w=t w•P.point w := by
    rw [hp]; simp only [retubePoint,ite_eq_right he,radialPoint,ite_eq_left hw]
  have hscl (w : V) (hw : w≠v) : Q.point w∈closure S := by
    rw [hp]; simp only [retubePoint,ite_eq_right hw,radialPoint]
    split_ifs with hwB
    · have : t w•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨t w,⟨hc.le.trans (ht w hwB).1.le,(ht w hwB).2⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
    · have : c•P.point w∈segment ℝ 0 (P.point w) := by
        rw [segment_eq_image' ℝ]; exact ⟨c,⟨hc.le,hc1.le⟩,by simp⟩
      exact hS.closure.segment_subset (subset_closure (mem_of_mem_nhds hS0)) (hpoint w) this
  have htail_subset (w : V) (hw : w∈B) (he : w≠v) :
      segment ℝ (Q.point w) (P.point w) ⊆ segment ℝ 0 (P.point w) := by
    apply (convex_segment 0 (P.point w)).segment_subset
    · rw [hpw w hw he,segment_eq_image' ℝ]
      exact ⟨t w,⟨hc.le.trans (ht w hw).1.le,(ht w hw).2⟩,by simp⟩
    · exact right_mem_segment ℝ _ _
  refine ⟨Q,⟨hpv,hpointT,hTQ,?_,?_,hfront,?_,?_,htail,?_⟩⟩
  · intro w
    by_cases he : w=v
    · subst w; exact Or.inr (hpv ▸ right_mem_segment ℝ (P.point v) q)
    · exact Or.inl (hscl w he)
  · intro d z hz
    rcases hreg d hz with hz|hz
    · exact Or.inl (P.radialRegion_old hS hS0 hc.le hc1.le hpoint htrace
        (fun w hw => ⟨hc.le.trans (ht w hw).1.le,(ht w hw).2⟩) d hz)
    · exact Or.inr hz.2
  · intro w hw he
    exact hS.closure.segment_subset (hscl w he) (hpoint w)
  · intro w hw he z hz hzfr
    exact convex_frontier_segment hS hS0 (hport w hw) hzfr (htail_subset w hw he hz)
  · intro w hw he u hu hue hwu
    have hdisj := convex_frontier_tails_disjoint hS hS0 (hport w hw) (hport u hu)
      (fun h => hwu (P.point_injective h)) hc hc1.le
    apply hdisj.mono
    · rw [hpw w hw he]
      apply (convex_segment (c•P.point w) (P.point w)).segment_subset
      · rw [segment_eq_image' ℝ]
        refine ⟨(t w-c)/(1-c),?_,?_⟩
        · constructor
          · exact div_nonneg (sub_nonneg.mpr (ht w hw).1.le) (sub_nonneg.mpr hc1.le)
          · apply (div_le_one (sub_pos.mpr hc1)).mpr
            linarith [(ht w hw).2]
        · have hne : (1-c)≠0 := ne_of_gt (sub_pos.mpr hc1)
          have hs : c+((t w-c)/(1-c))*(1-c)=t w := by field_simp; ring
          calc c•P.point w+((t w-c)/(1-c))•(P.point w-c•P.point w)
            = (c+((t w-c)/(1-c))*(1-c))•P.point w := by module
            _ = t w•P.point w := by rw [hs]
      · exact right_mem_segment ℝ _ _
    · rw [hpw u hu hue]
      apply (convex_segment (c•P.point u) (P.point u)).segment_subset
      · rw [segment_eq_image' ℝ]
        refine ⟨(t u-c)/(1-c),?_,?_⟩
        · constructor
          · exact div_nonneg (sub_nonneg.mpr (ht u hu).1.le) (sub_nonneg.mpr hc1.le)
          · apply (div_le_one (sub_pos.mpr hc1)).mpr
            linarith [(ht u hu).2]
        · have hne : (1-c)≠0 := ne_of_gt (sub_pos.mpr hc1)
          have hs : c+((t u-c)/(1-c))*(1-c)=t u := by field_simp; ring
          calc c•P.point u+((t u-c)/(1-c))•(P.point u-c•P.point u)
            = (c+((t u-c)/(1-c))*(1-c))•P.point u := by module
            _ = t u•P.point u := by rw [hs]
      · exact right_mem_segment ℝ _ _

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set Metric Filter
namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V}

lemma affine_image_closure (f : ℂ ≃ᵃ[ℝ] ℂ) (S : Set ℂ) :
    closure (f '' S)=f '' closure S := by
  exact (f.toContinuousAffineEquiv.toHomeomorph.image_closure S).symm
lemma affine_image_frontier (f : ℂ ≃ᵃ[ℝ] ℂ) (S : Set ℂ) :
    frontier (f '' S)=f '' frontier S := by
  exact (f.toContinuousAffineEquiv.toHomeomorph.image_frontier S).symm

lemma PortMove.affine {p : V → ℂ} {Q : PLDrawing G} {B : Set V} {v : V} {q : ℂ} {S T : Set ℂ}
    (h : PortMove p Q B v q S T) (f : ℂ ≃ᵃ[ℝ] ℂ) :
    PortMove (fun w => f (p w)) (Q.affine f) B v (f q) (f '' S) (f '' T) := by
  have hseg (a b : ℂ) : segment ℝ (f a) (f b)=f '' segment ℝ a b := (image_segment ℝ f.toAffineMap a b).symm
  constructor
  · exact congrArg f h.selected
  · intro w; rw [affine_point,affine_image_closure]; exact ⟨Q.point w,h.point_mem w,rfl⟩
  · intro d; rw [Q.affine_trace,affine_image_closure]; exact Set.image_mono (h.trace_mem d)
  · intro w
    rw [affine_point,affine_image_closure,hseg,← Set.image_union]
    exact ⟨Q.point w,h.point_control w,rfl⟩
  · intro d
    rw [Q.affine_trace,affine_image_closure,hseg,← Set.image_union]
    exact Set.image_mono (h.trace_control d)
  · intro w hw he
    rw [affine_point,affine_image_frontier]
    exact ⟨Q.point w,h.on_frontier w hw he,rfl⟩
  · intro w hw he
    rw [affine_point,hseg,affine_image_closure]
    exact Set.image_mono (h.tail_old w hw he)
  · intro w hw he z hz hz'
    rw [affine_point,hseg] at hz
    rw [affine_image_frontier] at hz'
    obtain ⟨z,hz,rfl⟩ := hz
    obtain ⟨z',hz',hzz⟩ := hz'
    have heq : z'=z := f.injective hzz
    subst z'
    exact congrArg f (h.tail_frontier w hw he z hz hz')
  · intro w hw he z hz hz'
    rw [affine_point,hseg] at hz
    rw [affine_image_closure] at hz'
    obtain ⟨z,hz,rfl⟩ := hz
    obtain ⟨z',hz',hzz⟩ := hz'
    have heq : z'=z := f.injective hzz
    subst z'
    exact congrArg f (h.tail_new w hw he z hz hz')
  · intro w hw he u hu hue hwu
    rw [affine_point,affine_point,hseg,hseg]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,hxy⟩
    have hxy' : y=x := f.injective hxy
    subst y
    exact Set.disjoint_left.mp (h.tails_disjoint w hw he u hu hue hwu) hx hy

lemma retube_at (P : PLDrawing G) {S T : Set ℂ} {B : Set V} {v : V} {q a : ℂ}
    (hS : Convex ℝ S) (hSopen : IsOpen S) (hSa : a∈S) (hSb : Bornology.IsBounded S)
    (hpoint : ∀ w, P.point w∈closure S)
    (htrace : ∀ d, (P.chain d).trace ⊆ closure S)
    (hport : ∀ w∈B, P.point w∈frontier S)
    (hleaf : ∀ w∈B, ∀ u w', G.Adj w u → G.Adj w w' → u=w')
    (hv : v∈B) (hT : Convex ℝ T) (hTop : IsOpen T) (hTa : a∈T)
    (hTv : P.point v∈T) (hqT : q∈closure T)
    (hout : ∀ w∈B, w≠v → P.point w∉closure T)
    (hext : ∀ z, z∈segment ℝ (P.point v) q → z∈closure S → z=P.point v) :
    ∃ Q : PLDrawing G, PortMove P.point Q B v q S T := by
  let f := AffineEquiv.constVAdd ℝ ℂ (-a)
  let R := P.affine f
  let S' := f '' S
  let T' := f '' T
  have hS' : Convex ℝ S' := hS.affine_image f.toAffineMap
  have hT' : Convex ℝ T' := hT.affine_image f.toAffineMap
  have hSop : IsOpen S' := f.toContinuousAffineEquiv.toHomeomorph.isOpenMap S hSopen
  have hTop' : IsOpen T' := f.toContinuousAffineEquiv.toHomeomorph.isOpenMap T hTop
  have h0S : (0:ℂ)∈S' := ⟨a,hSa,by simp [f]⟩
  have h0T : (0:ℂ)∈T' := ⟨a,hTa,by simp [f]⟩
  have hSb' : Bornology.IsBounded S' := by
    apply ((isCompact_of_isClosed_isBounded isClosed_closure hSb.closure).image
      f.toContinuousAffineEquiv.toHomeomorph.continuous).isBounded.subset
    exact Set.image_mono subset_closure
  have hcl (U : Set ℂ) : closure (f '' U)=f '' closure U := affine_image_closure f U
  have hfr (U : Set ℂ) : frontier (f '' U)=f '' frontier U := affine_image_frontier f U
  obtain ⟨Q,hQ⟩ := R.retube_controlled hS' (hSop.mem_nhds h0S) hSb'
    (fun w => by rw [hcl]; exact ⟨P.point w,hpoint w,rfl⟩)
    (fun d => by rw [show (R.chain d).trace=f '' (P.chain d).trace from P.affine_trace f d,hcl]; exact Set.image_mono (htrace d))
    (fun w hw => by rw [hfr]; exact ⟨P.point w,hport w hw,rfl⟩)
    hleaf hv hT' hTop' h0T (show f (P.point v)∈T' from ⟨P.point v,hTv,rfl⟩)
    (show f q∈closure T' from by rw [hcl]; exact ⟨q,hqT,rfl⟩)
    (fun w hw he hp => by
      rw [hcl] at hp
      obtain ⟨z,hz,heq⟩ := hp
      apply hout w hw he
      have heq' : z=P.point w := f.injective heq
      exact heq' ▸ hz)
    (fun z hz hz' => by
      change z∈segment ℝ (f (P.point v)) (f q) at hz
      have hs : f '' segment ℝ (P.point v) q=segment ℝ (f (P.point v)) (f q) := image_segment ℝ f.toAffineMap _ _
      rw [← hs] at hz
      rw [hcl] at hz'
      obtain ⟨z,hz,rfl⟩ := hz
      obtain ⟨z',hz',heq⟩ := hz'
      have heq' : z'=z := f.injective heq
      subst z'
      exact congrArg f (hext z hz hz'))
  have hh := hQ.affine f.symm
  refine ⟨Q.affine f.symm,?_⟩
  change PortMove (fun w => f.symm (f (P.point w))) (Q.affine f.symm)
    B v (f.symm (f q)) (f.symm '' (f '' S)) (f.symm '' (f '' T)) at hh
  simpa only [AffineEquiv.symm_apply_apply,Set.image_image,Function.comp_def,
    Set.image_id'] using hh

end PLDrawing
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set

variable {V : Type}

/-- Released radial port tails; unlike `PortMove` this does not prescribe the
selected route, which may already have passed through several bends. -/
structure PortFrame (p a : V → ℂ) (B : Set V) (v : V) (q : ℂ) (S T : Set ℂ) : Prop where
  selected : a v=q
  on_frontier : ∀ w∈B, w≠v → a w∈frontier T
  tail_old : ∀ w∈B, w≠v → segment ℝ (a w) (p w) ⊆ closure S
  tail_frontier : ∀ w∈B, w≠v → ∀ z∈segment ℝ (a w) (p w),
    z∈frontier S → z=p w
  tail_new : ∀ w∈B, w≠v → ∀ z∈segment ℝ (a w) (p w),
    z∈closure T → z=a w
  tails_disjoint : ∀ w∈B, w≠v → ∀ u∈B, u≠v → w≠u →
    Disjoint (segment ℝ (a w) (p w)) (segment ℝ (a u) (p u))

namespace PortFrame
lemma ofMove [LinearOrder V] {G : SimpleGraph V} {p : V → ℂ} {Q : PLDrawing G} {B : Set V}
    {v : V} {q : ℂ} {S T : Set ℂ} (h : PLDrawing.PortMove p Q B v q S T) :
    PortFrame p Q.point B v q S T :=
  ⟨h.selected,h.on_frontier,h.tail_old,h.tail_frontier,h.tail_new,h.tails_disjoint⟩

lemma repoint {p a b : V → ℂ} {B : Set V} {v : V} {q r : ℂ} {S T : Set ℂ}
    (h : PortFrame p a B v q S T) (hv : b v=r) (he : ∀ w, w≠v → b w=a w) :
    PortFrame p b B v r S T := by
  constructor
  · exact hv
  · intro w hw hwv; rw [he w hwv]; exact h.on_frontier w hw hwv
  · intro w hw hwv; rw [he w hwv]; exact h.tail_old w hw hwv
  · intro w hw hwv; rw [he w hwv]; exact h.tail_frontier w hw hwv
  · intro w hw hwv; rw [he w hwv]; exact h.tail_new w hw hwv
  · intro w hw hwv u hu huv hwu
    rw [he w hwv,he u huv]; exact h.tails_disjoint w hw hwv u hu huv hwu
end PortFrame

/-- Actual disjoint exterior polygonal stems, not a promised contour order. -/
structure ExteriorPorts (p target : V → ℂ) (B : Set V) (S : Set ℂ) where
  region : V → Set ℂ
  compact : ∀ w∈B, IsCompact (region w)
  start : ∀ w∈B, p w∈region w
  joined : ∀ w∈B, PolygonallyJoined (region w) (p w) (target w)
  inside : ∀ w∈B, ∀ z∈region w, z∈closure S → z=p w
  disjoint : ∀ w∈B, ∀ u∈B, w≠u → Disjoint (region w) (region u)

namespace ExteriorPorts
variable {p target : V → ℂ} {B : Set V} {S : Set ℂ} (E : ExteriorPorts p target B S)

lemma end_mem (w : V) (hw : w∈B) : target w∈E.region w := by
  have hreach : ∀ y, PolygonallyJoined (E.region w) (p w) y → y∈E.region w := by
    intro y hj
    induction hj with
    | refl => exact E.start w hw
    | @tail y z h hz ih => exact hz (right_mem_segment ℝ _ _)
  exact hreach _ (E.joined w hw)

lemma tail_disjoint_region {a : V → ℂ} {v : V} {q : ℂ} {T : Set ℂ}
    (h : PortFrame p a B v q S T) (hinj : Function.Injective p)
    (hport : ∀ w∈B, p w∈frontier S)
    {w u : V} (hw : w∈B) (he : w≠v) (hu : u∈B) (hwu : w≠u) :
    Disjoint (segment ℝ (a w) (p w)) (E.region u) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have heq := E.inside u hu z hz' (h.tail_old w hw he hz)
  have heqw := h.tail_frontier w hw he z hz (heq ▸ hport u hu)
  exact hwu (hinj (heqw.symm.trans heq))

noncomputable def updatedRegion (a : V → ℂ) (v : V) (U : Set ℂ) (w : V) : Set ℂ := by
  classical exact if w=v then U else segment ℝ (a w) (p w) ∪ E.region w

/-- Replacing one residual stem, and adjoining the released radial tails to
all other stems, preserves literal disjoint exterior routes. -/
noncomputable def update {a : V → ℂ} {v : V} {q : ℂ} {T U : Set ℂ}
    (h : PortFrame p a B v q S T) (hinj : Function.Injective p)
    (hport : ∀ w∈B, p w∈frontier S) (hv : v∈B)
    (hout : ∀ w∈B, w≠v → Disjoint (closure T) (E.region w))
    (hU : IsCompact U) (hqU : q∈U) (hUsub : U ⊆ E.region v)
    (hUin : ∀ z∈U, z∈closure T → z=q)
    (hUjoin : PolygonallyJoined U q (target v)) : ExteriorPorts a target B T where
  region := E.updatedRegion a v U
  compact w hw := by
    classical
    by_cases he : w=v
    · simpa only [updatedRegion,ite_eq_left he] using hU
    · simpa only [updatedRegion,ite_eq_right he] using (compact_segment_complex _ _).union (E.compact w hw)
  start w hw := by
    classical
    by_cases he : w=v
    · subst w; simpa only [updatedRegion,ite_true,h.selected] using hqU
    · simp only [updatedRegion,ite_eq_right he]; exact Or.inl (left_mem_segment ℝ _ _)
  joined w hw := by
    classical
    by_cases he : w=v
    · subst w; simpa only [updatedRegion,ite_true,h.selected] using hUjoin
    · simp only [updatedRegion,ite_eq_right he]
      exact (Relation.ReflTransGen.single (fun z hz => Or.inl hz)).trans
        ((E.joined w hw).mono Set.subset_union_right)
  inside w hw z hz hz' := by
    classical
    by_cases he : w=v
    · subst w
      rw [h.selected]
      exact hUin z (by simpa only [updatedRegion,ite_true] using hz) hz'
    · simp only [updatedRegion,ite_eq_right he] at hz
      rcases hz with hz|hz
      · exact h.tail_new w hw he z hz hz'
      · exact False.elim (Set.disjoint_left.mp (hout w hw he) hz' hz)
  disjoint w hw u hu hwu := by
    classical
    by_cases hwv : w=v <;> by_cases huv : u=v
    · exact False.elim (hwu (hwv.trans huv.symm))
    · subst w
      simp only [updatedRegion,ite_true,ite_eq_right huv]
      apply Disjoint.union_right
      · exact (E.tail_disjoint_region h hinj hport hu huv hv huv).symm.mono_left hUsub
      · exact (E.disjoint v hv u hu hwu).mono_left hUsub
    · subst u
      simp only [updatedRegion,ite_true,ite_eq_right hwv]
      apply Disjoint.union_left
      · exact (E.tail_disjoint_region h hinj hport hw hwv hv hwv).mono_right hUsub
      · exact (E.disjoint w hw v hv hwu).mono_right hUsub
    · simp only [updatedRegion,ite_eq_right hwv,ite_eq_right huv]
      apply Disjoint.union_left
      · apply Disjoint.union_right
        · exact h.tails_disjoint w hw hwv u hu huv hwu
        · exact E.tail_disjoint_region h hinj hport hw hwv hu hwu
      · apply Disjoint.union_right
        · exact (E.tail_disjoint_region h hinj hport hu huv hw (Ne.symm hwu)).symm
        · exact E.disjoint w hw u hu hwu

end ExteriorPorts
end PlanarL1.Topology




namespace PlanarL1.Topology
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y (n+1))

noncomputable def tail : SegmentChain S (P.vertex 1) y n where
  vertex i := P.vertex (i+1)
  start := rfl
  finish := P.finish
  segment_mem i hi := P.segment_mem (i+1) (by omega)

lemma tail_trace : P.trace=segment ℝ x (P.vertex 1) ∪ P.tail.trace := by
  apply Set.Subset.antisymm
  · rintro z (hz|hz)
    · have he : z=x := hz; subst z; exact Or.inl (left_mem_segment ℝ _ _)
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      by_cases he : (i:ℕ)=0
      · exact Or.inl (by simpa only [he,zero_add,P.start] using hi)
      · apply Or.inr; apply Or.inr; apply Set.mem_iUnion.mpr
        refine ⟨⟨i-1,by omega⟩,?_⟩
        simpa only [tail,show (i:ℕ)-1+1=i by omega] using hi
  · rintro z (hz|hz)
    · apply Or.inr; apply Set.mem_iUnion.mpr
      exact ⟨⟨0,by omega⟩,by simpa only [zero_add,P.start] using hz⟩
    · rcases hz with hz|hz
      · have he : z=P.vertex 1 := hz; subst z
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨0,by omega⟩,
          by simpa only [zero_add,P.start] using right_mem_segment ℝ x (P.vertex 1)⟩)
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i+1,by omega⟩,hi⟩)

lemma tail_simple (hP : P.IsSimple) : P.tail.IsSimple := by
  constructor
  · intro i hi j hj he
    change i≤n at hi
    change j≤n at hj
    have he' := hP.1 (show i+1∈Iic (n+1) from Nat.add_le_add_right hi 1)
      (show j+1∈Iic (n+1) from Nat.add_le_add_right hj 1) he
    omega
  · intro i j hij hjn z hz hz'
    obtain ⟨he,hz⟩ := hP.2 (i+1) (j+1) (by omega) (by omega) z hz hz'
    exact ⟨by omega,hz⟩

lemma head_tail_intersection (hP : P.IsSimple) {z : E}
    (hz : z∈segment ℝ x (P.vertex 1)) (hz' : z∈P.tail.trace) : z=P.vertex 1 := by
  rcases hz' with hz'|hz'
  · exact hz'
  · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz'
    obtain ⟨he,he'⟩ := hP.2 0 (i+1) (by omega) (by omega) z (by simpa only [P.start,zero_add] using hz) hi
    simpa only [he,zero_add] using he'

lemma first_ne (hP : P.IsSimple) : P.vertex 1≠x := by
  intro he
  have hh := hP.1 (show 1∈Iic (n+1) from Nat.le_add_left 1 n) (show 0∈Iic (n+1) from Nat.zero_le _)
    (he.trans P.start.symm)
  omega

lemma start_not_tail (hP : P.IsSimple) : x∉P.tail.trace := by
  intro hx
  exact P.first_ne hP (P.head_tail_intersection hP (left_mem_segment ℝ _ _) hx).symm

lemma finish_not_first (P : SegmentChain S x y (n+1+1)) (hP : P.IsSimple) :
    y∉segment ℝ x (P.vertex 1) := by
  intro hy
  have hlast : y∈segment ℝ (P.vertex (n+1)) (P.vertex (n+1+1)) := by
    rw [P.finish]; exact right_mem_segment ℝ _ _
  obtain ⟨he,he'⟩ := hP.2 0 (n+1) (by omega) (by omega) y
    (by simpa only [P.start,zero_add] using hy) hlast
  have hi := hP.1 (show n+1+1∈Iic (n+1+1) from by simp)
    (show n+1∈Iic (n+1+1) from Nat.le_succ _) (P.finish.trans he')
  omega

noncomputable def cutFirst (z : E) (hz : z∈segment ℝ x (P.vertex 1)) :
    SegmentChain S z y (n+1) where
  vertex i := if i=0 then z else P.vertex i
  start := by simp
  finish := by simpa using P.finish
  segment_mem i hi := by
    by_cases he : i=0
    · subst i
      simp only [ite_true,Nat.zero_add,one_ne_zero,ite_false]
      apply (P.segment_mem 0 (by omega)).trans' -- rewrite the first endpoint
      simpa only [P.start,zero_add] using (convex_segment x (P.vertex 1)).segment_subset hz (right_mem_segment ℝ _ _)
    · simpa only [ite_eq_right he,Nat.succ_ne_zero,ite_false] using P.segment_mem i hi

lemma cutFirst_trace (z : E) (hz : z∈segment ℝ x (P.vertex 1)) :
    (P.cutFirst z hz).trace=segment ℝ z (P.vertex 1) ∪ P.tail.trace := by
  rw [(P.cutFirst z hz).tail_trace]
  rfl

lemma cutFirst_subset (z : E) (hz : z∈segment ℝ x (P.vertex 1)) : (P.cutFirst z hz).trace ⊆ P.trace := by
  rw [P.cutFirst_trace,P.tail_trace]
  exact Set.union_subset_union ((convex_segment x (P.vertex 1)).segment_subset hz (right_mem_segment ℝ _ _)) Set.Subset.rfl

lemma cutFirst_simple (hP : P.IsSimple) (z : E) (hz : z∈segment ℝ x (P.vertex 1))
    (hne : z≠P.vertex 1) : (P.cutFirst z hz).IsSimple := by
  have hzhead : segment ℝ z (P.vertex 1) ⊆ segment ℝ x (P.vertex 1) :=
    (convex_segment x (P.vertex 1)).segment_subset hz (right_mem_segment ℝ _ _)
  have hztail : z∉P.tail.trace := fun h => hne (P.head_tail_intersection hP hz h)
  constructor
  · intro i hi j hj he
    by_cases hi0 : i=0 <;> by_cases hj0 : j=0
    · omega
    · subst i
      have he' : z=P.vertex j := by simpa only [cutFirst,ite_true,ite_eq_right hj0] using he
      exfalso; apply hztail
      rw [he']
      have hm := P.tail.vertex_mem_trace (j-1) (by change j≤n+1 at hj; omega)
      simpa only [tail,show j-1+1=j by omega] using hm
    · subst j
      have he' : P.vertex i=z := by simpa only [cutFirst,ite_true,ite_eq_right hi0] using he
      exfalso; apply hztail
      rw [← he']
      have hm := P.tail.vertex_mem_trace (i-1) (by change i≤n+1 at hi; omega)
      simpa only [tail,show i-1+1=i by omega] using hm
    · exact hP.1 hi hj (by simpa only [cutFirst,ite_eq_right hi0,ite_eq_right hj0] using he)
  · intro i j hij hjn w hw hw'
    have hj0 : j≠0 := by omega
    have hw₂ : w∈segment ℝ (P.vertex j) (P.vertex (j+1)) := by
      simpa only [cutFirst,ite_eq_right hj0,Nat.succ_ne_zero,ite_false] using hw'
    by_cases hi0 : i=0
    · subst i
      have hw₁ : w∈segment ℝ x (P.vertex 1) := hzhead
        (by simpa only [cutFirst,ite_true,zero_add,one_ne_zero,ite_false] using hw)
      obtain ⟨he,hw⟩ := hP.2 0 j hij hjn w (by simpa only [P.start,zero_add] using hw₁) hw₂
      exact ⟨he,by simpa only [cutFirst,ite_eq_right hj0] using hw⟩
    · obtain ⟨he,hw⟩ := hP.2 i j hij hjn w
        (by simpa only [cutFirst,ite_eq_right hi0,Nat.succ_ne_zero,ite_false] using hw) hw₂
      exact ⟨he,by simpa only [cutFirst,ite_eq_right hj0] using hw⟩

end SegmentChain
end PlanarL1.Topology



end

end OAI
