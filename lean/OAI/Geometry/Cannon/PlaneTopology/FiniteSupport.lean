import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Plane
import OAI.Geometry.Cannon.PlaneTopology.Arc
import OAI.Geometry.Cannon.PlaneTopology.HomeoPlane

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

namespace CannonEmbeddedArc
namespace Arc
variable {X : Type*} [TopologicalSpace X]
lemma trans_injective {x y z : X} (a : Path x y) (b : Path y z)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hmeet : ∀ s t, a s=b t → s=1 ∧ t=0) : Function.Injective (a.trans b) := by
  intro s t he
  rw [Path.trans_apply,Path.trans_apply] at he
  split_ifs at he with hs ht ht
  · have h := congrArg Subtype.val (ha he)
    apply Subtype.ext
    dsimp at h
    linarith
  · obtain ⟨h₁,h₂⟩ := hmeet _ _ he
    have h₁' := congrArg Subtype.val h₁
    have h₂' := congrArg Subtype.val h₂
    apply Subtype.ext
    dsimp at h₁' h₂'
    linarith
  · obtain ⟨h₁,h₂⟩ := hmeet _ _ he.symm
    have h₁' := congrArg Subtype.val h₁
    have h₂' := congrArg Subtype.val h₂
    apply Subtype.ext
    dsimp at h₁' h₂'
    linarith
  · have h := congrArg Subtype.val (hb he)
    apply Subtype.ext
    dsimp at h
    linarith

theorem extend_arc [T2Space X] (a b : Arc X) (hab : a 1=b 0)
    (hy : b 1∉range a) :
    ∃ c : Arc X, c 0=a 0 ∧ c 1=b 1 ∧ range c⊆range a∪range b := by
  have hc : IsCompact (b ⁻¹' range a) :=
    (a.compact_range.isClosed.preimage b.continuous).isCompact
  have hn : (b ⁻¹' range a).Nonempty := ⟨0,⟨1,hab⟩⟩
  obtain ⟨v,hv⟩ := hc.exists_isGreatest hn
  obtain ⟨u,hu⟩ := hv.1
  have hv₁ : v≠1 := fun h => hy (h ▸ hv.1)
  let d := b.subarc v 1 hv₁
  have hd₀ : d 0=a u := (subarc_zero ..).trans hu.symm
  have hd₁ : d 1=b 1 := subarc_one ..
  have hds : range d⊆range b := subarc_range_subset ..
  have hmeet : ∀ s t, a s=d t → s=u ∧ t=0 := by
    intro s t he
    have hin : Icc.convexComb v 1 t∈b ⁻¹' range a := ⟨s,he⟩
    have hle := hv.2 hin
    have hvlt : (v:ℝ)<1 := lt_of_le_of_ne v.property.2 (fun h => hv₁ (Subtype.ext h))
    have hle' : (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1≤v := by
      change (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1≤v at hle
      exact hle
    have ht : t=0 := by
      apply Subtype.ext
      dsimp
      nlinarith [t.property.1]
    refine ⟨?_,ht⟩
    apply a.injective
    simpa only [ht,hd₀] using he
  by_cases hu₀ : u=0
  · refine ⟨d,by simpa only [hu₀] using hd₀,hd₁,hds.trans subset_union_right⟩
  · let c := a.subarc 0 u (Ne.symm hu₀)
    let p : Path (a 0) (a u) := ⟨c.map,subarc_zero ..,subarc_one ..⟩
    let q : Path (a u) (b 1) := ⟨d.map,hd₀,hd₁⟩
    have hpq : ∀ s t, p s=q t → s=1 ∧ t=0 := by
      intro s t he
      obtain ⟨hs,ht⟩ := hmeet (Icc.convexComb 0 u s) t he
      refine ⟨?_,ht⟩
      have huc : (u:ℝ)≠0 := fun h => hu₀ (Subtype.ext h)
      have hh := congrArg Subtype.val hs
      simp only [Icc.coe_convexComb] at hh
      apply Subtype.ext
      dsimp at hh ⊢
      have heq : ((s:ℝ)-1)*(u:ℝ)=0 := by nlinarith [hh]
      exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right huc)
    refine ⟨⟨(p.trans q).toContinuousMap,trans_injective p q c.injective d.injective hpq⟩,
      (p.trans q).source,(p.trans q).target,?_⟩
    change range (p.trans q)⊆range a∪range b
    rw [Path.trans_range]
    exact union_subset_union (subarc_range_subset a 0 u (Ne.symm hu₀)) hds
end Arc
end CannonEmbeddedArc

namespace CannonPolygonal
open CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def FiniteSupport (S : Set E) : Prop :=
  ∃ P : Finset (E×E), S⊆⋃ p∈P, segment ℝ p.1 p.2
lemma FiniteSupport.mono {S T : Set E} (hT : FiniteSupport T) (hST : S⊆T) :
    FiniteSupport S := by
  obtain ⟨P,hP⟩ := hT
  exact ⟨P,hST.trans hP⟩
lemma FiniteSupport.segment (x y : E) : FiniteSupport (segment ℝ x y) := by
  classical
  exact ⟨{(x,y)},by simp⟩
lemma FiniteSupport.union {S T : Set E} (hS : FiniteSupport S) (hT : FiniteSupport T) :
    FiniteSupport (S∪T) := by
  classical
  obtain ⟨P,hP⟩ := hS
  obtain ⟨Q,hQ⟩ := hT
  refine ⟨P∪Q,?_⟩
  intro x hx
  rcases hx with hx|hx
  · obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hP hx)
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_union_left Q hp,hx⟩
  · obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hQ hx)
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_union_right P hp,hx⟩

def PolyJoined (U : Set E) : E → E → Prop :=
  Relation.ReflTransGen (fun x y => segment ℝ x y⊆U)

lemma polyJoined_of_open_preconnected {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y : E} (hx : x∈U) (hy : y∈U) : PolyJoined U x y := by
  let V := {z | z∈U ∧ PolyJoined U x z}
  let W := {z | z∈U ∧ ¬PolyJoined U x z}
  have hstep (z : E) (hz : z∈U) :
      ∃ ε : ℝ, 0<ε ∧ ∀ w∈ball z ε, segment ℝ z w⊆U := by
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU z hz
    exact ⟨ε,hε,fun w hw => ((convex_ball z ε).segment_subset (mem_ball_self hε) hw).trans hεU⟩
  have hV : IsOpen V := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨ε,hε,hs⟩ := hstep z hz.1
    refine ⟨ε,hε,fun w hw => ⟨(hs w hw) (right_mem_segment ..),hz.2.tail (hs w hw)⟩⟩
  have hW : IsOpen W := by
    apply Metric.isOpen_iff.mpr
    intro z hz
    obtain ⟨ε,hε,hs⟩ := hstep z hz.1
    refine ⟨ε,hε,fun w hw => ⟨(hs w hw) (right_mem_segment ..),?_⟩⟩
    intro hj
    apply hz.2 (hj.tail ?_)
    simpa only [segment_symm] using hs w hw
  have hs : U⊆V∪W := by intro z hz; by_cases hj : PolyJoined U x z <;> simp_all [V,W]
  have hd : Disjoint V W := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hz'.2 hz.2
  have hv : x∈U∩V := ⟨hx,hx,.refl⟩
  exact (hc.subset_left_of_subset_union hV hW hd hs ⟨x,hv⟩ hy).2

theorem polyJoined_arc {U : Set E} {x y : E} (h : PolyJoined U x y) (hne : x≠y) :
    ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) := by
  have hh : x=y ∨ ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) := by
    clear hne
    induction h with
    | refl => exact Or.inl rfl
    | @tail y z _ hyz ih =>
      by_cases hxz : x=z
      · exact Or.inl hxz
      · apply Or.inr
        rcases ih with rfl|⟨a,ha₀,ha₁,haU,haS⟩
        · let b : Arc E := ⟨(Path.segment x z).toContinuousMap,Path.segment_injective_of_ne hxz⟩
          refine ⟨b,(Path.segment x z).source,(Path.segment x z).target,?_,?_⟩
          · change range (Path.segment x z)⊆U
            rwa [Path.range_segment]
          · change FiniteSupport (range (Path.segment x z))
            rw [Path.range_segment]
            exact FiniteSupport.segment x z
        · by_cases hz : z∈range a
          · obtain ⟨t,ht⟩ := hz
            have ht₀ : (0:I)≠t := fun h => hxz (ha₀.symm.trans ((congrArg a h).trans ht))
            refine ⟨a.subarc 0 t ht₀,(subarc_zero ..).trans ha₀,(subarc_one ..).trans ht,
              (subarc_range_subset ..).trans haU,haS.mono (subarc_range_subset ..)⟩
          · have hyz' : y≠z := fun h => hz ⟨1,ha₁.trans h⟩
            let b : Arc E := ⟨(Path.segment y z).toContinuousMap,Path.segment_injective_of_ne hyz'⟩
            have hb₀ : b 0=y := (Path.segment y z).source
            have hb₁ : b 1=z := (Path.segment y z).target
            have hbR : range b=segment ℝ y z := Path.range_segment y z
            obtain ⟨c,hc₀,hc₁,hcs⟩ := extend_arc a b (ha₁.trans hb₀.symm) (by simpa only [hb₁] using hz)
            refine ⟨c,hc₀.trans ha₀,hc₁.trans hb₁,hcs.trans (union_subset haU ?_),
              (haS.union ?_).mono hcs⟩
            · rwa [hbR]
            · rw [hbR]
              exact FiniteSupport.segment y z
  exact hh.resolve_left hne

theorem open_preconnected_arc {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {x y : E} (hx : x∈U) (hy : y∈U) (hne : x≠y) :
    ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) :=
  polyJoined_arc (polyJoined_of_open_preconnected hU hc hx hy) hne
end CannonPolygonal

namespace CannonRegularDisk
variable {X : Type*} [TopologicalSpace X]
lemma IsRegularDisk.isPathConnected {U : Set X} (hU : IsRegularDisk U) : IsPathConnected U := by
  obtain ⟨h⟩ := hU.homeo_plane
  let _ : PathConnectedSpace U := h.symm.surjective.pathConnectedSpace h.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

lemma IsRegularDisk.punctured_pathConnected [T1Space X] {U : Set X}
    (hU : IsRegularDisk U) (p : X) : IsPathConnected (U\{p}) := by
  by_cases hp : p∈U
  · obtain ⟨h⟩ := hU.homeo_plane
    let q : U := ⟨p,hp⟩
    have hc := isPathConnected_compl_singleton_of_one_lt_rank (E:=Plane)
      (by rw [←Module.finrank_eq_rank]; simp) (h q)
    have hi := hc.image (continuous_subtype_val.comp h.symm.continuous)
    have heq : (fun z : Plane => (h.symm z).val) '' {h q}ᶜ=U\{p} := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨(h.symm z).property,?_⟩
        intro he
        have he' : h.symm z=q := Subtype.ext (mem_singleton_iff.mp he)
        have hh := congrArg h he'
        exact hz (by simpa using hh)
      · rintro ⟨hx,hxp⟩
        refine ⟨h ⟨x,hx⟩,?_,by simp⟩
        intro he
        apply hxp
        have hh := h.injective (mem_singleton_iff.mp he)
        exact mem_singleton_iff.mpr (congrArg Subtype.val hh)
    change IsPathConnected ((fun z : Plane => (h.symm z).val) '' {h q}ᶜ) at hi
    rwa [heq] at hi
  · have heq : U\{p}=U := by
      ext x
      simp only [mem_sdiff,mem_singleton_iff]
      exact ⟨And.left,fun hx => ⟨hx,fun h => hp (h ▸ hx)⟩⟩
    rw [heq]
    exact hU.isPathConnected
end CannonRegularDisk

namespace CannonPolygonal
open CannonEmbeddedArc CannonEmbeddedArc.Arc CannonRegularDisk

variable {X : Type*} [TopologicalSpace X] [T1Space X]

theorem regular_disk_chart_arc (e : Plane → X) (he : IsOpenEmbedding e)
    (p : X) (hrange : range e={p}ᶜ) {U : Set X} (hU : IsRegularDisk U)
    {x y : X} (hx : x∈U) (hy : y∈U) (hxp : x≠p) (hyp : y≠p) (hxy : x≠y) :
    ∃ a : Arc X, a 0=x ∧ a 1=y ∧ range a⊆U ∧
      ∃ P : Finset (Plane×Plane), range a⊆e '' (⋃ q∈P, segment ℝ q.1 q.2) := by
  let V := U\{p}
  have hV : IsOpen V := hU.isOpen.sdiff isClosed_singleton
  have hVc : IsPathConnected V := hU.punctured_pathConnected p
  have hVs : V⊆range e := by intro z hz; rw [hrange]; exact hz.2
  have hc : IsPreconnected (e ⁻¹' V) :=
    hVc.isConnected.isPreconnected.preimage_of_isOpenMap he.injective he.isOpenMap hVs
  obtain ⟨u,hu⟩ := hVs ⟨hx,by simpa using hxp⟩
  obtain ⟨v,hv⟩ := hVs ⟨hy,by simpa using hyp⟩
  have huv : u≠v := fun h => hxy (hu.symm.trans ((congrArg e h).trans hv))
  obtain ⟨b,hb₀,hb₁,hbV,P,hP⟩ := open_preconnected_arc (hV.preimage he.continuous) hc
    (show u∈e ⁻¹' V from by rw [mem_preimage,hu]; exact ⟨hx,by simpa using hxp⟩)
    (show v∈e ⁻¹' V from by rw [mem_preimage,hv]; exact ⟨hy,by simpa using hyp⟩) huv
  let a : Arc X := ⟨⟨fun t => e (b t),he.continuous.comp b.continuous⟩,he.injective.comp b.injective⟩
  refine ⟨a,(congrArg e hb₀).trans hu,(congrArg e hb₁).trans hv,?_,P,?_⟩
  · rintro _ ⟨t,rfl⟩
    exact (hbV (mem_range_self t)).1
  · rintro _ ⟨t,rfl⟩
    exact ⟨b t,hP (mem_range_self t),rfl⟩
end CannonPolygonal

end
end
end
end
end
end
end
end

end OAI
