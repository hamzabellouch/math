import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Reverse

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

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

def portion (a : Arc ℂ) (u v : I) : Path (a u) (a v) where
  toFun t := a (Icc.convexComb u v t)
  continuous_toFun := a.continuous.comp (Icc.continuous_convexComb u v)
  source' := by simp
  target' := by simp
@[simp] lemma portion_apply (a : Arc ℂ) (u v t : I) :
    a.portion u v t=a (Icc.convexComb u v t) := rfl
lemma portion_range (a : Arc ℂ) {u v : I} (huv : u ≤ v) :
    range (a.portion u v)=a '' Icc u v := by
  rcases huv.eq_or_lt with he|hl
  · subst v
    simp [portion,Icc.convexComb_eq]
  · exact subarc_range_eq a hl

lemma pair_closing_path (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (u v : I) :
    ∃ γ : Path (a v) (a u), range γ=
      a '' Icc v 1 ∪ range b ∪ a '' Icc 0 u := by
  let p : Path (a 1) (a 0) := b.path.symm.cast hab₁ hab₀
  refine ⟨((a.portion v 1).trans p).trans (a.portion 0 u),?_⟩
  rw [Path.trans_range,Path.trans_range,portion_range a (unitInterval.le_one v),
    portion_range a (unitInterval.nonneg u)]
  have hp : range p=range b := Path.symm_range b.path
  rw [hp]

lemma isolated_chord_closer (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {u v : I} (huv : u < v) {x c : ℂ} (hu : a u=x-c) (hv : a v=x+c)
    (he : a '' Icc u v=segment ℝ (a u) (a v))
    (hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v) :
    ∃ γ : Path (a v) (a u),
      range (Path.segment (a u) (a v))∪range γ=range a∪range b ∧
      ∀ t, ‖c‖ ≤ dist (γ t) x := by
  obtain ⟨γ,hγ⟩ := pair_closing_path a b hab₀ hab₁ u v
  have hball : ∀ z∈(range a∪range b)∩ball x ‖c‖,
      ∃ s∈Ioo u v, a s=z := by
    intro z hz
    obtain ⟨s,hs,hsz⟩ := hsmall hz
    have hsu : s≠u := by
      intro h
      have hh := hz.2
      rw [←hsz,h,hu,mem_ball,dist_eq_norm] at hh
      have hd : x-c-x=-c := by abel
      rw [hd,norm_neg] at hh
      exact lt_irrefl _ hh
    have hsv : s≠v := by
      intro h
      have hh := hz.2
      rw [←hsz,h,hv,mem_ball,dist_eq_norm,add_sub_cancel_left] at hh
      exact lt_irrefl _ hh
    exact ⟨s,⟨lt_of_le_of_ne hs.1 hsu.symm,lt_of_le_of_ne hs.2 hsv⟩,hsz⟩
  refine ⟨γ,?_,?_⟩
  · rw [Path.range_segment,hγ,←he]
    apply Subset.antisymm
    · exact union_subset (fun _ h => Or.inl (image_subset_range _ _ h))
        (union_subset (union_subset (fun _ h => Or.inl (image_subset_range _ _ h)) subset_union_right)
          (fun _ h => Or.inl (image_subset_range _ _ h)))
    · rintro z (⟨s,rfl⟩|hz)
      · rcases lt_trichotomy s u with hsu | rfl | hus
        · exact Or.inr (Or.inr ⟨s,⟨unitInterval.nonneg s,hsu.le⟩,rfl⟩)
        · exact Or.inl ⟨s,⟨le_rfl,huv.le⟩,rfl⟩
        · by_cases hvs : v < s
          · exact Or.inr (Or.inl (Or.inl ⟨s,⟨hvs.le,unitInterval.le_one s⟩,rfl⟩))
          · exact Or.inl ⟨s,⟨hus.le,le_of_not_gt hvs⟩,rfl⟩
      · exact Or.inr (Or.inl (Or.inr hz))
  · intro t
    apply le_of_not_gt
    intro ht
    have htγ := mem_range_self (f:=γ) t
    rw [hγ] at htγ
    have htK : γ t∈range a∪range b := by
      rcases htγ with ((⟨s,_,he'⟩|hh)|⟨s,_,he'⟩)
      · exact Or.inl ⟨s,he'⟩
      · exact Or.inr hh
      · exact Or.inl ⟨s,he'⟩
    obtain ⟨s,hs,hse⟩ := hball (γ t) ⟨htK,ht⟩
    rcases htγ with ((⟨r,hr,he'⟩|⟨r,he'⟩)|⟨r,hr,he'⟩)
    · have hsr := a.injective (hse.trans he'.symm)
      subst r
      exact hs.2.not_ge hr.1
    · have hh := (hc s r (hse.trans he'.symm)).1
      rcases hh with hh|hh
      · exact (not_lt_of_ge (show (0:I) ≤ u from u.2.1)) (hh ▸ hs.1)
      · exact (not_lt_of_ge (show v ≤ (1:I) from v.2.2)) (hh ▸ hs.2)
    · have hsr := a.injective (hse.trans he'.symm)
      subst r
      exact hs.1.not_ge hr.2
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma isolated_chord_not_preconnected (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {u v : I} (huv : u < v) {x c : ℂ} (hc₀ : c≠0) (hu : a u=x-c) (hv : a v=x+c)
    (he : a '' Icc u v=segment ℝ (a u) (a v))
    (hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v) :
    ¬IsPreconnected (range a ∪ range b)ᶜ := by
  obtain ⟨γ,hγK,hγ⟩ := isolated_chord_closer a b hab₀ hab₁ hc huv hu hv he hsmall
  let L : ℂ ≃ₜ ℂ := (Homeomorph.addRight (-x)).trans
    (Homeomorph.mulRight₀ c⁻¹ (inv_ne_zero hc₀))
  have hL (z : ℂ) : L z=(z-x)/c := by rfl
  have hLu : L (a u)=-1 := by rw [hL,hu]; simp [sub_sub_cancel_left,hc₀]
  have hLv : L (a v)=1 := by rw [hL,hv]; simp [hc₀]
  let Γ : Path (1:ℂ) (-1) := (γ.map L.continuous).cast hLv.symm hLu.symm
  have hΓ (t : I) : 1 ≤ ‖Γ t‖ := by
    change 1 ≤ ‖L (γ t)‖
    rw [hL,norm_div]
    apply (le_div_iff₀ (norm_pos_iff.mpr hc₀)).mpr
    simpa only [one_mul,dist_eq_norm] using hγ t
  let N : ℂ →ᵃ[ℝ] ℂ := {
    toFun := fun z => (z-x)/c
    linear := {
      toFun := fun z => z/c
      map_add' := fun z w => add_div z w c
      map_smul' := fun r z => by simp only [Complex.real_smul, RingHom.id_apply]; ring }
    map_vadd' := fun z w => by change (w+z-x)/c=w/c+(z-x)/c; ring }
  have hseg : L '' segment ℝ (a u) (a v)=segment ℝ (-1:ℂ) 1 := by
    change N '' segment ℝ (a u) (a v)=_
    rw [image_segment ℝ N]
    change segment ℝ (L (a u)) (L (a v))=_
    rw [hLu,hLv]
  have hΓR : range Γ=L '' range γ := by
    change range (L ∘ γ)=_
    exact range_comp L γ
  let f := (Path.segment (-1:ℂ) 1).trans Γ
  have hfR : range f=L '' (range a∪range b) := by
    rw [show f=(Path.segment (-1:ℂ) 1).trans Γ from rfl,Path.trans_range,
      Path.range_segment,←hseg,hΓR,←image_union,←Path.range_segment,hγK]
  intro hconn
  have hconn' : IsPreconnected (range f)ᶜ := by
    rw [hfR,←L.image_compl]
    exact hconn.image L L.continuous.continuousOn
  obtain ⟨hp,hm,_⟩ := CannonWinding.chord_winding_jump Γ hΓ (1/2)
    (by norm_num) (by norm_num)
  exact CannonWinding.chord_separates Γ hΓ (1/2) (by norm_num) (by norm_num)
    (hconn'.subset_connectedComponentIn hp subset_rfl hm)

theorem pair_complement_not_preconnected (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ)) (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ¬IsPreconnected (range a ∪ range b)ᶜ := by
  obtain ⟨u,v,x,c,huv,hc₀,hu,hv,he,hs⟩ := pair_isolated_chord a b hab₀ hab₁ hc Q ha
  exact isolated_chord_not_preconnected a b hab₀ hab₁ hc huv hc₀ hu hv he hs
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem tame_pair_jordan (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ labels : Bool ≃ ConnectedComponents ((range a ∪ range b)ᶜ : Set ℂ),
      ∀ x∈range a ∪ range b,
        incident _ ConnectedComponents.mk x=range labels := by
  let K : Set ℂ := range a ∪ range b
  have hK : IsClosed K := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  obtain ⟨l,hls,hl⟩ := pair_labels_surjective a b hab₀ hab₁ hc Q ha hb
    (π:=ConnectedComponents.mk) ConnectedComponents.continuous_coe ConnectedComponents.surjective_coe
  have hne : l false ≠ l true := by
    intro he
    have hconst (s t : Bool) : l s=l t := by
      cases s <;> cases t
      · rfl
      · exact he
      · exact he.symm
      · rfl
    have hsub (d e : ConnectedComponents (Kᶜ : Set ℂ)) : d=e := by
      obtain ⟨s,rfl⟩ := hls d
      obtain ⟨t,rfl⟩ := hls e
      exact hconst s t
    have hconn : PreconnectedSpace (Kᶜ : Set ℂ) := by
      rw [preconnectedSpace_iff_connectedComponent]
      intro x
      apply eq_univ_of_forall
      intro y
      exact ConnectedComponents.coe_eq_coe'.mp (hsub _ _)
    exact pair_complement_not_preconnected a b hab₀ hab₁ hc Q ha
      (isPreconnected_iff_preconnectedSpace.mpr hconn)
  have hli : Function.Injective l := by
    intro s t h
    cases s <;> cases t
    · rfl
    · exact (hne h).elim
    · exact (hne h.symm).elim
    · rfl
  exact ⟨Equiv.ofBijective l ⟨hli,hls⟩,hl⟩
end CannonEmbeddedArc.Arc

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
