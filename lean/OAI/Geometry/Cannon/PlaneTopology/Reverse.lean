import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Lift
import OAI.Geometry.Cannon.PlaneTopology.FiniteSupport
import OAI.Geometry.Cannon.PlaneTopology.TameGraphFlatChart
import OAI.Geometry.Cannon.PlanarGraphs.ClosureRegionInside

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner

def reverse (a : Arc ℂ) : Arc ℂ where
  map := a.path.symm.toContinuousMap
  injective := fun _ _ h => unitInterval.symm_bijective.injective (a.injective h)
@[simp] lemma reverse_apply (a : Arc ℂ) (t : I) : a.reverse t=a (unitInterval.symm t) := rfl
@[simp] lemma reverse_zero (a : Arc ℂ) : a.reverse 0=a 1 := by simp
@[simp] lemma reverse_one (a : Arc ℂ) : a.reverse 1=a 0 := by simp
@[simp] lemma reverse_range (a : Arc ℂ) : range a.reverse=range a :=
  Path.symm_range a.path

lemma local_arc_flat {K : Set ℂ} {x : ℂ} (a : Arc ℂ)
    (Q : Finset (ℂ × ℂ)) (hQ : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) (ht : a t=x)
    {U : Set ℂ} (hU : IsOpen U) (hxU : x∈U)
    (hUK : ∀ z∈U, z∈K ↔ z∈range a) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ x∈W ∧
      H (0,0)=x ∧ ∀ z∈W, (z∈K ↔ z∈H '' horizontal) := by
  obtain ⟨H,W,hW,htW,h₀,hW'⟩ := tame_graph_flat_chart (fun _ : Unit => a)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) Q (fun _ => hQ) () ht₀ ht₁
  refine ⟨H,W∩U,hW.inter hU,⟨ht ▸ htW,hxU⟩,h₀.trans ht,?_⟩
  intro z hz
  exact (hUK z hz.2).trans (by simpa only [iUnion_const] using hW' z hz.1)

lemma pair_start_local_arc (a b : Arc ℂ) (hab : a 0=b 0)
    (hc : ∀ s t, a s=b t → (s=0∨s=1) ∧ (t=0∨t=1)) :
    ∃ (c : Arc ℂ) (t : I) (U : Set ℂ), 0<t ∧ t<1 ∧ c t=a 0 ∧
      IsOpen U ∧ a 0∈U ∧ range c⊆range a∪range b ∧
      ∀ z∈U, (z∈range a∪range b ↔ z∈range c) := by
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm₀ : 0 < m := by change (0:ℝ)<1/2; norm_num
  have hm₁ : m < 1 := by change (1/2:ℝ)<1; norm_num
  let A := a.subarc 0 m hm₀.ne
  let B := b.subarc 0 m hm₀.ne
  let p : Path (a m) (a 0) := A.path.symm.cast (by simp [A]) (by simp [A])
  let q : Path (a 0) (b m) := B.path.cast (by simpa [B] using hab) (by simp [B])
  have hp (s : I) : p s=a (Icc.convexComb 0 m (unitInterval.symm s)) := rfl
  have hq (s : I) : q s=b (Icc.convexComb 0 m s) := rfl
  have hpq (s t : I) (he : p s=q t) : s=1 ∧ t=0 := by
    obtain ⟨hs,ht⟩ := hc _ _ he
    have hsₘ : Icc.convexComb 0 m (unitInterval.symm s) ≤ m := Icc.convexComb_le hm₀.le _
    have htₘ : Icc.convexComb 0 m t ≤ m := Icc.convexComb_le hm₀.le _
    have hs₀ : Icc.convexComb 0 m (unitInterval.symm s)=0 := hs.resolve_right (fun h => hm₁.not_ge (h ▸ hsₘ))
    have ht₀ : Icc.convexComb 0 m t=0 := ht.resolve_right (fun h => hm₁.not_ge (h ▸ htₘ))
    have hsval := congrArg Subtype.val hs₀
    have htval := congrArg Subtype.val ht₀
    constructor <;> apply Subtype.ext
    · simp only [Icc.coe_convexComb,unitInterval.coe_symm_eq] at hsval
      change (s:ℝ)=1
      dsimp [m] at hsval
      linarith
    · simp only [Icc.coe_convexComb] at htval
      change (t:ℝ)=0
      dsimp [m] at htval
      linarith
  have hpi : Function.Injective p := fun s t he =>
    unitInterval.symm_bijective.injective (A.injective he)
  have hqi : Function.Injective q := B.injective
  let c : Arc ℂ := ⟨(p.trans q).toContinuousMap,trans_injective p q hpi hqi hpq⟩
  have hcrange : range c=a '' Icc 0 m ∪ b '' Icc 0 m := by
    change range (p.trans q)=_
    rw [Path.trans_range]
    have hpR : range p=range A := by exact Path.symm_range A.path
    rw [hpR]
    change range A∪range B=_
    rw [subarc_range_eq a hm₀,subarc_range_eq b hm₀]
  let T : Set ℂ := a '' Ici m ∪ b '' Ici m
  have hT : IsClosed T :=
    (isClosed_Ici.isCompact.image a.continuous).isClosed.union
      (isClosed_Ici.isCompact.image b.continuous).isClosed
  have hxT : a 0∉T := by
    rintro (⟨s,hs,he⟩|⟨s,hs,he⟩)
    · have he₀ := a.injective he
      subst s
      exact hm₀.not_ge hs
    · have he₀ := b.injective (he.trans hab)
      subst s
      exact hm₀.not_ge hs
  refine ⟨c,m,Tᶜ,hm₀,hm₁,?_,hT.isOpen_compl,hxT,?_,?_⟩
  · change (p.trans q) m=a 0
    rw [Path.trans_apply]
    split_ifs with h
    · have hr : (⟨2*(m:ℝ),(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨m.2.1,h⟩⟩:I)=1 := by apply Subtype.ext; dsimp [m]; norm_num
      rw [hr,Path.target]
    · exact (h (by change (1/2:ℝ)≤1/2; rfl)).elim
  · rw [hcrange]
    exact union_subset_union (image_subset_range _ _) (image_subset_range _ _)
  · intro z hz
    rw [hcrange]
    constructor
    · rintro (⟨s,rfl⟩|⟨s,rfl⟩)
      · exact Or.inl ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hm => hz (Or.inl ⟨s,hm,rfl⟩))⟩,rfl⟩
      · exact Or.inr ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hm => hz (Or.inr ⟨s,hm,rfl⟩))⟩,rfl⟩
    · intro hh
      exact union_subset_union (image_subset_range _ _) (image_subset_range _ _) hh
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner CannonFaceIncidence

lemma pair_start_flat (a b : Arc ℂ) (hab : a 0 = b 0)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a 0 ∈ W ∧
      H (0,0)=a 0 ∧ ∀ z∈W, (z∈range a ∪ range b ↔ z∈H '' horizontal) := by
  obtain ⟨c,t,U,ht₀,ht₁,ht,hU,hxU,hsub,hUK⟩ := pair_start_local_arc a b hab hc
  exact local_arc_flat c Q (fun z hz => (hsub hz).elim (fun h => ha h) (fun h => hb h)) ht₀ ht₁ ht hU hxU hUK

theorem pair_flat_at_left (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2) (t : I) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a t ∈ W ∧
      H (0,0)=a t ∧ ∀ z∈W, (z∈range a ∪ range b ↔ z∈H '' horizontal) := by
  by_cases ht₀ : t=0
  · subst t
    exact pair_start_flat a b hab₀ hc Q ha hb
  by_cases ht₁ : t=1
  · subst t
    have hc' : ∀ s t, a.reverse s = b.reverse t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := by
      intro s t he
      obtain ⟨hs,ht⟩ := hc _ _ he
      simpa only [unitInterval.symm_eq_zero,unitInterval.symm_eq_one,or_comm] using And.intro hs ht
    have hh := pair_start_flat a.reverse b.reverse (by simpa) hc' Q
      (by simpa using ha) (by simpa using hb)
    simpa using hh
  have ht₀' : 0<t := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht₀)
  have ht₁' : t<1 := lt_of_le_of_ne (unitInterval.le_one t) ht₁
  have htB : a t ∉ range b := by
    rintro ⟨s,hs⟩
    exact ((hc t s hs.symm).1).elim ht₀ ht₁
  exact local_arc_flat a Q ha ht₀' ht₁' rfl
    b.compact_range.isClosed.isOpen_compl htB (fun z hz => or_iff_left hz)

theorem pair_incident_labels (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
    {π : ((range a ∪ range b)ᶜ : Set ℂ) → D} (hπ : Continuous π) :
    ∃ labels : Bool → D, ∀ x∈range a ∪ range b,
      incident _ π x=range labels := by
  let K : Set ℂ := range a ∪ range b
  have hK : IsPreconnected K :=
    IsPreconnected.union' ⟨a 0,mem_range_self 0,⟨0,hab₀.symm⟩⟩
      (isPreconnected_range a.continuous) (isPreconnected_range b.continuous)
  have hflat : ∀ x∈K, ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ x∈W ∧
      H (0,0)=x ∧ ∀ z∈W, (z∈K ↔ z∈H '' horizontal) := by
    rintro x (⟨t,rfl⟩|⟨t,rfl⟩)
    · exact pair_flat_at_left a b hab₀ hab₁ hc Q ha hb t
    · have hh := pair_flat_at_left b a hab₀.symm hab₁.symm
        (fun s t he => (hc t s he.symm).symm) Q hb ha t
      simpa only [K,union_comm] using hh
  have hloc₀ : ∀ x∈K, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∃ labels : Bool → D, ∀ y∈U∩K, incident _ π y=range labels := by
    intro x hx
    obtain ⟨H,W,hW,hxW,h₀,hW'⟩ := hflat x hx
    have he (z : ℂ) : z∈H '' horizontal ↔ (H.symm z).2=0 := by
      rw [H.image_eq_preimage_symm]
      rfl
    obtain ⟨U,hU,h₀U,_,labels,hlabels⟩ := flat_chart_incidence hπ H hW (h₀.symm ▸ hxW)
      (fun z hz => not_congr ((hW' z hz).trans (he z)))
    exact ⟨U,hU,h₀ ▸ h₀U,labels,by simpa only [compl_compl] using hlabels⟩
  have hloc : ∀ x∈K, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∀ y∈K∩U, incident _ π y=incident _ π x := by
    intro x hx
    obtain ⟨U,hU,hxU,l,hl⟩ := hloc₀ x hx
    exact ⟨U,hU,hxU,fun y hy => (hl y hy.symm).trans (hl x ⟨hxU,hx⟩).symm⟩
  have hxK : a 0∈K := Or.inl (mem_range_self 0)
  obtain ⟨U,hU,hxU,l,hl⟩ := hloc₀ (a 0) hxK
  refine ⟨l,fun x hx => ?_⟩
  exact (incident_constant_on_preconnected hK hloc x hx (a 0) hxK).trans (hl (a 0) ⟨hxU,hxK⟩)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem pair_labels_surjective (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
    {π : ((range a ∪ range b)ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (hπs : Function.Surjective π) :
    ∃ labels : Bool → D, Function.Surjective labels ∧
      ∀ x∈range a ∪ range b, incident _ π x=range labels := by
  obtain ⟨l,hl⟩ := pair_incident_labels a b hab₀ hab₁ hc Q ha hb hπ
  refine ⟨l,?_,hl⟩
  intro d
  obtain ⟨z,hz⟩ := hπs d
  have hd : (region _ π d).Nonempty := ⟨z.val,z.property,hz⟩
  have hK : IsClosed (range a ∪ range b) := a.compact_range.isClosed.union b.compact_range.isClosed
  obtain ⟨x,hx,_,hxd⟩ := region_boundary_hits hK (T:=∅) isClosed_empty (empty_subset _)
    (by simpa using (isPreconnected_univ : IsPreconnected (univ : Set ℂ)))
    ⟨a 0,Or.inl (mem_range_self 0),notMem_empty _⟩ hπ d hd
  change d∈range l
  rw [←hl x hx]
  exact hxd
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma centered_chord_endpoints (A B : ℂ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1/2) :
    let x := A+(1/2:ℝ)•(B-A)
    let c := ε•(B-A)
    x-c∈segment ℝ A B ∧ x+c∈segment ℝ A B := by
  dsimp
  rw [segment_eq_image']
  constructor
  · refine ⟨1/2-ε,⟨by linarith,by linarith⟩,?_⟩
    simp only [sub_smul]
    abel
  · refine ⟨1/2+ε,⟨by linarith,by linarith⟩,?_⟩
    simp only [add_smul]
    abel

lemma centered_chord_ball (A B : ℂ) (hAB : A≠B) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : z∈segment ℝ A B)
    (hb : z∈ball (A+(1/2:ℝ)•(B-A)) ‖ε•(B-A)‖) :
    z∈segment ℝ (A+(1/2:ℝ)•(B-A)-ε•(B-A))
      (A+(1/2:ℝ)•(B-A)+ε•(B-A)) := by
  rw [segment_eq_image'] at hz ⊢
  obtain ⟨s,hs,rfl⟩ := hz
  have hD : 0 < ‖B-A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  have he : A+s•(B-A)-(A+(1/2:ℝ)•(B-A))=(s-1/2)•(B-A) := by rw [sub_smul]; abel
  have habs : |s-1/2| < ε := by
    rw [mem_ball,dist_eq_norm,he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hε] at hb
    exact (mul_lt_mul_iff_left₀ hD).mp hb
  have hlo := (abs_lt.mp habs).1
  have hhi := (abs_lt.mp habs).2
  refine ⟨(s-1/2+ε)/(2*ε),⟨div_nonneg (by linarith) (by positivity),
    (div_le_one (by positivity : 0 < 2*ε)).mpr (by linarith)⟩,?_⟩
  have hd : (A+(1/2:ℝ)•(B-A)+ε•(B-A))-
      (A+(1/2:ℝ)•(B-A)-ε•(B-A))=(2*ε)•(B-A) := by
    rw [mul_smul,two_smul]; abel
  dsimp only
  rw [hd,smul_smul,div_mul_cancel₀ _ (by positivity : 2*ε≠0)]
  simp only [add_smul,sub_smul]
  abel

theorem pair_isolated_chord (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ)) (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ (u v : I) (x c : ℂ), u < v ∧ c≠0 ∧ a u=x-c ∧ a v=x+c ∧
      a '' Icc u v=segment ℝ (a u) (a v) ∧
      (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v := by
  let m : I := ⟨1/2,by constructor  <;> norm_num⟩
  obtain ⟨p,q,hpm,hmq,hleft,_,_⟩ := tame_interior_corner Q a ha
    (t:=m) (by change (0:ℝ) < 1/2; norm_num) (by change (1/2:ℝ) < 1; norm_num)
  let D := a m-a p
  have hD : D≠0 := sub_ne_zero.mpr (a.injective.ne hpm.ne.symm)
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  let x := a p+(1/2:ℝ)•D
  have hxseg : x∈segment ℝ (a p) (a m) := by
    rw [segment_eq_image']
    exact ⟨1/2,by constructor  <;> norm_num,rfl⟩
  obtain ⟨w,hw,hwx⟩ := hleft.symm ▸ hxseg
  have hxp : x≠a p := by
    intro he
    have hh : (1/2:ℝ)•D=0 := by
      change a p+(1/2:ℝ)•D=a p at he
      exact add_left_cancel (he.trans (add_zero (a p)).symm)
    exact hD ((smul_eq_zero.mp hh).resolve_left (by norm_num))
  have hxm : x≠a m := by
    intro he
    have hh : (1/2:ℝ)•D=D := by
      change a p+(1/2:ℝ)•D=a m at he
      exact eq_sub_of_add_eq (by rwa [add_comm])
    have hh' : ((1/2:ℝ)-1)•D=0 := by rw [sub_smul,one_smul,hh,sub_self]
    exact hD ((smul_eq_zero.mp hh').resolve_left (by norm_num))
  have hpw : p < w := lt_of_le_of_ne hw.1 (fun he => hxp (he ▸ hwx).symm)
  have hwm : w  <  m := lt_of_le_of_ne hw.2 (fun he => hxm (he ▸ hwx).symm)
  let T : Set ℂ := a '' Iic p ∪ a '' Ici m ∪ range b
  have hT : IsClosed T :=
    ((isClosed_Iic.isCompact.image a.continuous).isClosed.union
      (isClosed_Ici.isCompact.image a.continuous).isClosed).union b.compact_range.isClosed
  have hxT : x∉T := by
    rintro ((⟨s,hs,he⟩|⟨s,hs,he⟩)|⟨s,hs⟩)
    · have he' := a.injective (he.trans hwx.symm)
      subst s
      exact hpw.not_ge hs
    · have he' := a.injective (he.trans hwx.symm)
      subst s
      exact hwm.not_ge hs
    · rcases (hc w s (hwx.trans hs.symm)).2 with rfl | rfl
      · have hwzero := a.injective ((hwx.trans hs.symm).trans hab₀.symm)
        exact (not_lt_of_ge (show (0:I) ≤ p from p.2.1)) (hwzero ▸ hpw)
      · have hwone := a.injective ((hwx.trans hs.symm).trans hab₁.symm)
        exact (not_lt_of_ge (show m ≤ (1:I) from m.2.2)) (hwone ▸ hwm)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hT.isOpen_compl.mem_nhds hxT)
  let ε := min (1/4) (δ/(2*‖D‖))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hε₁ : ε < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
  let c : ℂ := ε•D
  have hcn : ‖c‖=ε*‖D‖ := by simp [c,Real.norm_eq_abs,abs_of_pos hε]
  have hc₀ : c≠0 := smul_ne_zero hε.ne' hD
  have hcδ : ‖c‖ < δ := by
    rw [hcn]
    have hh : ε*(2*‖D‖) ≤ δ := (le_div_iff₀ (by positivity)).mp (min_le_right (1/4) (δ/(2*‖D‖)))
    nlinarith
  have hend := centered_chord_endpoints (a p) (a m) hε hε₁
  change x-c∈segment ℝ (a p) (a m) ∧ x+c∈segment ℝ (a p) (a m) at hend
  obtain ⟨u,hu,hu'⟩ := hleft.symm ▸ hend.1
  obtain ⟨v,hv,hv'⟩ := hleft.symm ▸ hend.2
  have huv : u≠v := by
    intro he
    have hh : x-c=x+c := hu'.symm.trans (he ▸ hv')
    have hh' : c+c=0 := by linear_combination -hh
    exact hc₀ (by linear_combination (1/2:ℂ)*hh')
  have hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ segment ℝ (x-c) (x+c) := by
    rintro z ⟨hz,hzb⟩
    have hzT : z∉T := hball (ball_subset_ball hcδ.le hzb)
    rcases hz with ⟨s,rfl⟩|hz
    · have hsp : p ≤ s := le_of_not_ge (fun hh => hzT (Or.inl (Or.inl ⟨s,hh,rfl⟩)))
      have hsm : s  ≤  m := le_of_not_ge (fun hh => hzT (Or.inl (Or.inr ⟨s,hh,rfl⟩)))
      exact centered_chord_ball (a p) (a m) (a.injective.ne hpm.ne) hε
        (hleft ▸ ⟨s,⟨hsp,hsm⟩,rfl⟩) hzb
    · exact (hzT (Or.inr hz)).elim
  rcases lt_or_gt_of_ne huv with huv|hvu
  · have he := segment_subarc_image a hpm huv hleft
      (fun s hs => ⟨hu.1.trans hs.1,hs.2.trans hv.2⟩)
    refine ⟨u,v,x,c,huv,hc₀,hu',hv',he,?_⟩
    rw [he,hu',hv']
    exact hsmall
  · have he := segment_subarc_image a hpm hvu hleft
      (fun s hs => ⟨hv.1.trans hs.1,hs.2.trans hu.2⟩)
    refine ⟨v,u,x,-c,hvu,neg_ne_zero.mpr hc₀,?_,?_,he,?_⟩
    · simpa using hv'
    · simpa only [sub_eq_add_neg] using hu'
    · rw [norm_neg,he,hv',hu',segment_symm]
      exact hsmall
end CannonEmbeddedArc.Arc

noncomputable section
open Set Topology unitInterval

namespace CannonWinding
open Set Topology unitInterval

lemma turn_path_trans {a b c : Circle} (p : Path a b) (q : Path b c) :
    turn (p.trans q).toContinuousMap=turn p.toContinuousMap+turn q.toContinuousMap := by
  let f := lift p.toContinuousMap
  let g := lift q.toContinuousMap
  let P : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
  let Q : Path (f 1) (g 1+f 1-g 0) :=
    ⟨⟨fun t => g t+f 1-g 0,by fun_prop⟩,by ring,rfl⟩
  have hP (t : I) : Circle.exp (P t)=p t := lift_exp _ t
  have hQ (t : I) : Circle.exp (Q t)=q t := by
    change Circle.exp (g t+f 1-g 0)=q t
    simp only [Circle.exp_sub,Circle.exp_add,f,g,lift_exp]
    simp
  have hL (t : I) : Circle.exp ((P.trans Q) t)=(p.trans q) t := by
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs <;> simp only [hP,hQ]
  rw [turn_eq_of_lift _ (P.trans Q).toContinuousMap hL]
  change (P.trans Q) 1-(P.trans Q) 0=_
  rw [Path.target,Path.source]
  dsimp only [turn,f,g]
  ring

lemma winding_path_trans {a b c : ℂ} (p : Path a b) (q : Path b c)
    (z : ℂ) (hp : z∉range p) (hq : z∉range q) :
    winding (p.trans q).toContinuousMap z (by change z∉range (p.trans q); rw [Path.trans_range]; exact not_or.mpr ⟨hp,hq⟩)=
      winding p.toContinuousMap z hp+winding q.toContinuousMap z hq := by
  let f := direction (p.toContinuousMap-.const I z) (fun t ht => hp ⟨t,sub_eq_zero.mp ht⟩)
  let g := direction (q.toContinuousMap-.const I z) (fun t ht => hq ⟨t,sub_eq_zero.mp ht⟩)
  have hfg : f 1=g 0 := by
    apply Circle.ext
    simp [f,g,direction_coe]
  let P : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
  let Q : Path (f 1) (g 1) := ⟨g,hfg.symm,rfl⟩
  have he : direction ((p.trans q).toContinuousMap-.const I z)
      (fun t ht => (show z∉range (p.trans q) by rw [Path.trans_range]; exact not_or.mpr ⟨hp,hq⟩)
        ⟨t,sub_eq_zero.mp ht⟩)=(P.trans Q).toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change ((p.trans q) t-z)/(‖(p.trans q) t-z‖:ℂ)=((P.trans Q) t:ℂ)
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs <;> rfl
  change turn (direction _ _)=turn f+turn g
  rw [he]
  exact turn_path_trans P Q

lemma winding_path_homotopy {a : ℂ} {p q : Path a a} (H : p.Homotopy q)
    (z : ℂ) (hz : z∉range H) :
    winding p.toContinuousMap z (fun ⟨t,ht⟩ => hz ⟨(0,t),by simpa using ht⟩)=
      winding q.toContinuousMap z (fun ⟨t,ht⟩ => hz ⟨(1,t),by simpa using ht⟩) := by
  exact winding_eq_of_homotopy _ _ _ _ _ H.toHomotopy.toContinuousMap
    (fun s => (H.source s).trans (H.target s).symm)
    (fun t => H.map_zero_left t) (fun t => H.map_one_left t) hz

def blendPaths {a b : ℂ} (p q : Path a b) : p.Homotopy q where
  toFun st := (1-(st.1:ℝ)) • p st.2+(st.1:ℝ) • q st.2
  continuous_toFun := by fun_prop
  map_zero_left := by intro t; simp
  map_one_left := by intro t; simp
  prop' := by
    intro s t ht
    rcases ht with rfl|ht
    · simp
      ring
    · have : t=1 := ht
      subst t
      simp
      ring

def upperSemi : Path (-1 : ℂ) 1 where
  toFun t := Circle.exp (Real.pi*(1-(t:ℝ)))
  continuous_toFun := by fun_prop
  source' := by change (Circle.exp (Real.pi*(1-(0:ℝ))):ℂ)= -1; simp [Circle.coe_exp]
  target' := by simp

def lowerSemi : Path (-1 : ℂ) 1 where
  toFun t := Circle.exp (Real.pi*(1+(t:ℝ)))
  continuous_toFun := by fun_prop
  source' := by change (Circle.exp (Real.pi*(1+(0:ℝ))):ℂ)= -1; simp [Circle.coe_exp]
  target' := by
    change (Circle.exp (Real.pi*(1+(1:ℝ))):ℂ)=1
    rw [show Real.pi*(1+(1:ℝ))=2*Real.pi by ring,Circle.exp_two_pi]
    rfl

lemma upperSemi_norm (t : I) : ‖upperSemi t‖=1 := Circle.norm_coe _
lemma lowerSemi_norm (t : I) : ‖lowerSemi t‖=1 := Circle.norm_coe _
lemma upperSemi_im (t : I) : 0≤(upperSemi t).im := by
  change 0≤(Circle.exp (Real.pi*(1-(t:ℝ))):ℂ).im
  rw [Circle.coe_exp,Complex.exp_ofReal_mul_I_im]
  exact Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg Real.pi_pos.le (sub_nonneg.mpr t.property.2),
    by nlinarith [t.property.1,Real.pi_pos]⟩
lemma lowerSemi_im (t : I) : (lowerSemi t).im≤0 := by
  change (Circle.exp (Real.pi*(1+(t:ℝ))):ℂ).im≤0
  rw [Circle.coe_exp,Complex.exp_ofReal_mul_I_im,
    show Real.pi*(1+(t:ℝ))=(Real.pi*(t:ℝ))+Real.pi by ring,Real.sin_add_pi]
  exact neg_nonpos.mpr (Real.sin_nonneg_of_mem_Icc
    ⟨mul_nonneg Real.pi_pos.le t.property.1,mul_le_of_le_one_right Real.pi_pos.le t.property.2⟩)

lemma winding_upperSemi :
    winding upperSemi.toContinuousMap 0 (by rintro ⟨t,ht⟩; change upperSemi t=0 at ht; have := upperSemi_norm t; rw [ht,norm_zero] at this; norm_num at this) = -Real.pi := by
  let f : C(I,ℝ) := ⟨fun t => Real.pi*(1-(t:ℝ)),by fun_prop⟩
  have he : direction (upperSemi.toContinuousMap-.const I 0) (by
      intro t ht
      have hn := upperSemi_norm t
      change upperSemi t-0=0 at ht
      rw [sub_zero] at ht
      rw [ht,norm_zero] at hn
      norm_num at hn)=Circle.exp.comp f := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change (upperSemi t-0)/(‖upperSemi t-0‖:ℂ)=(Circle.exp (f t):ℂ)
    simp only [sub_zero,upperSemi_norm,Complex.ofReal_one,div_one]
    rfl
  change turn (direction _ _)=_
  rw [he,turn_eq_of_lift _ f (fun _ => rfl)]
  simp [f]

lemma winding_lowerSemi :
    winding lowerSemi.toContinuousMap 0 (by rintro ⟨t,ht⟩; change lowerSemi t=0 at ht; have := lowerSemi_norm t; rw [ht,norm_zero] at this; norm_num at this) = Real.pi := by
  let f : C(I,ℝ) := ⟨fun t => Real.pi*(1+(t:ℝ)),by fun_prop⟩
  have he : direction (lowerSemi.toContinuousMap-.const I 0) (by
      intro t ht
      have hn := lowerSemi_norm t
      change lowerSemi t-0=0 at ht
      rw [sub_zero] at ht
      rw [ht,norm_zero] at hn
      norm_num at hn)=Circle.exp.comp f := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change (lowerSemi t-0)/(‖lowerSemi t-0‖:ℂ)=(Circle.exp (f t):ℂ)
    simp only [sub_zero,lowerSemi_norm,Complex.ofReal_one,div_one]
    rfl
  change turn (direction _ _)=_
  rw [he,turn_eq_of_lift _ f (fun _ => rfl)]
  simp [f]
  ring
end CannonWinding

namespace CannonWinding
open Set Topology unitInterval Metric

lemma path_outside_avoids {a b : ℂ} (p : Path a b) (hp : ∀ t, 1≤‖p t‖)
    {z : ℂ} (hz : ‖z‖<1) : z∉range p := by
  rintro ⟨t,rfl⟩
  exact (hp t).not_gt hz

lemma winding_outside_move {a : ℂ} (p : Path a a) (hp : ∀ t, 1≤‖p t‖)
    {z : ℂ} (hz : ‖z‖<1) :
    winding p.toContinuousMap z (path_outside_avoids p hp hz)=
      winding p.toContinuousMap 0 (path_outside_avoids p hp (by simp)) := by
  have hw (s : I) : ‖Path.segment z 0 s‖<1 := by
    have hs : Path.segment z 0 s∈ball (0:ℂ) 1 := by
      apply (convex_ball (0:ℂ) 1).segment_subset
        (by simpa [mem_ball,dist_zero_right] using hz) (show (0:ℂ)∈ball (0:ℂ) 1 by simp)
      rw [←Path.range_segment]
      exact mem_range_self s
    simpa [mem_ball,dist_zero_right] using hs
  have he := winding_moving_point p.toContinuousMap (by change p 0=p 1; simp)
    (Path.segment z 0).toContinuousMap (fun s => path_outside_avoids p hp (hw s))
  change winding _ (Path.segment z 0 0) _=winding _ (Path.segment z 0 1) _ at he
  simpa only [Path.source,Path.target] using he

lemma segment_diameter_im (t : I) : (Path.segment (-1:ℂ) 1 t).im=0 := by
  simp [Path.segment,AffineMap.lineMap_apply]

theorem winding_chord_replace (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (q : Path (-1:ℂ) 1) (hq : ∀ t, ‖q t‖=1)
    (sgn : ℝ) (hsgn : sgn=1 ∨ sgn= -1) (hside : ∀ t, sgn*(q t).im≤0)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    ∃ hz : ((sgn*η:ℝ):ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ),
      winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap
        (((sgn*η:ℝ):ℂ)*Complex.I) hz =
      winding (q.trans γ).toContinuousMap 0 (by
        apply path_outside_avoids (q.trans γ) _ (by simp)
        intro t
        rw [Path.trans_apply]
        split_ifs
        · exact (hq _).ge
        · exact hγ _) := by
  let z : ℂ := ((sgn*η:ℝ):ℂ)*Complex.I
  have hnz : ‖z‖<1 := by
    rcases hsgn with rfl|rfl <;> simpa [z,norm_mul,Complex.norm_I,abs_of_pos hη] using hη₁
  have himz : sgn*z.im=η := by
    rcases hsgn with rfl|rfl <;> simp [z]
  have him (s t : I) : sgn*(blendPaths (Path.segment (-1:ℂ) 1) q (s,t)).im≤0 := by
    change sgn*(((1-(s:ℝ)) • Path.segment (-1:ℂ) 1 t+(s:ℝ) • q t).im)≤0
    simp only [Complex.add_im,Complex.smul_im,smul_eq_mul,segment_diameter_im,mul_zero,zero_add]
    nlinarith [hside t,s.property.1]
  let H := (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ)
  have hzH : z∉range H := by
    rintro ⟨⟨s,t⟩,he⟩
    change (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ) (s,t)=z at he
    rw [Path.Homotopy.hcomp_apply] at he
    split_ifs at he with h
    · change blendPaths (Path.segment (-1:ℂ) 1) q (s,_) = z at he
      have hh := him s ⟨2*(t:ℝ),(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,h⟩⟩
      rw [he,himz] at hh
      exact hη.not_ge hh
    · exact path_outside_avoids γ hγ hnz ⟨_,he⟩
  have hp : z∉range ((Path.segment (-1:ℂ) 1).trans γ) := by
    rintro ⟨t,ht⟩
    exact hzH ⟨(0,t),by simpa [H] using ht⟩
  refine ⟨hp,?_⟩
  have he := winding_path_homotopy H z hzH
  change winding _ z hp=_
  rw [he]
  apply winding_outside_move (q.trans γ) _ hnz
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact (hq _).ge
  · exact hγ _

theorem chord_winding_jump (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    ∃ (hplus : (η:ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ))
      (hminus : -(η:ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ)),
    winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap ((η:ℂ)*Complex.I) hplus -
      winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap (-(η:ℂ)*Complex.I) hminus
      =2*Real.pi := by
  obtain ⟨hp,hp'⟩ := winding_chord_replace γ hγ lowerSemi lowerSemi_norm 1 (Or.inl rfl)
    (fun t => by simpa using lowerSemi_im t) η hη hη₁
  obtain ⟨hm,hm'⟩ := winding_chord_replace γ hγ upperSemi upperSemi_norm (-1) (Or.inr rfl)
    (fun t => by simpa using upperSemi_im t) η hη hη₁
  simp only [one_mul,neg_one_mul,Complex.ofReal_neg] at hp hm hp' hm'
  refine ⟨hp,hm,?_⟩
  have hγ₀ := path_outside_avoids γ hγ (z:=0) (by simp)
  have hl₀ := path_outside_avoids lowerSemi (fun t => (lowerSemi_norm t).ge) (z:=0) (by simp)
  have hu₀ := path_outside_avoids upperSemi (fun t => (upperSemi_norm t).ge) (z:=0) (by simp)
  rw [hp',hm',winding_path_trans lowerSemi γ 0 hl₀ hγ₀,
    winding_path_trans upperSemi γ 0 hu₀ hγ₀,winding_lowerSemi,winding_upperSemi]
  ring
end CannonWinding

namespace CannonWinding
open Set Topology unitInterval

lemma winding_on_component (f : C(I,ℂ)) (hf : f 0=f 1) {z w : ℂ}
    (hz : z∉range f) (hw : w∈connectedComponentIn (range f)ᶜ z) :
    winding f z hz=winding f w (connectedComponentIn_subset _ _ hw) := by
  let V : Set ℂ := (range f)ᶜ
  let z' : V := ⟨z,hz⟩
  let w' : V := ⟨w,connectedComponentIn_subset _ _ hw⟩
  have hwc : w'∈connectedComponent z' := by
    have hwi : w∈Subtype.val '' connectedComponent z' :=
      (connectedComponentIn_eq_image (F:=V) (x:=z) hz) ▸ hw
    obtain ⟨v,hv,hve⟩ := hwi
    have he : v=w' := Subtype.ext hve
    exact he ▸ hv
  exact (winding_locally_constant f hf).apply_eq_of_isPreconnected
    (s:=connectedComponent z') isPreconnected_connectedComponent
    (x:=z') (y:=w') (mem_connectedComponent (x:=z')) hwc

theorem chord_separates (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    -(η:ℂ)*Complex.I∉connectedComponentIn
      (range ((Path.segment (-1:ℂ) 1).trans γ))ᶜ ((η:ℂ)*Complex.I) := by
  obtain ⟨hp,hm,he⟩ := chord_winding_jump γ hγ η hη hη₁
  intro hh
  have hc : ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap 0=
      ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap 1 := by
    change ((Path.segment (-1:ℂ) 1).trans γ) 0=((Path.segment (-1:ℂ) 1).trans γ) 1
    simp
  have heq := winding_on_component _ hc hp hh
  rw [heq,sub_self] at he
  linarith [Real.pi_pos]
end CannonWinding

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
end
end
end
end
end
end
end
end

end OAI
