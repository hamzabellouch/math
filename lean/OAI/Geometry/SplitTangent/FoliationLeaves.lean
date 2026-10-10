import Mathlib

namespace OAI

/-! Foliation Leaves. -/

noncomputable section
open Set Filter Topology
universe u v w

structure PlaqueSystem {ι : Type v} (X : Type u) [TopologicalSpace X]
    (A B : ι → Type w) [∀i,TopologicalSpace (A i)] [∀i,TopologicalSpace (B i)] where
  chart : ∀i,OpenPartialHomeomorph X (A i × B i)
  covering : ∀x,∃i,x∈(chart i).source

namespace PlaqueSystem
variable {ι : Type v} {X : Type u} [TopologicalSpace X]
  {A B : ι → Type w} [∀i,TopologicalSpace (A i)] [∀i,TopologicalSpace (B i)]
  (P : PlaqueSystem X A B)

def Related (x y : X) : Prop := ∃(i : ι) (b : B i) (U : Set (A i)),
  IsPreconnected U ∧ (∀a∈U,(a,b)∈(P.chart i).target) ∧
  ∃a₀∈U,∃a₁∈U,(P.chart i).symm (a₀,b)=x ∧ (P.chart i).symm (a₁,b)=y

def Reachable := Relation.ReflTransGen P.Related

def leaf (x : X) : Set X := {y | P.Reachable x y}

lemma Related.symm {x y : X} (h : P.Related x y) : P.Related y x := by
  obtain ⟨i,b,U,hU,hT,a₀,ha₀,a₁,ha₁,h₀,h₁⟩ := h
  exact ⟨i,b,U,hU,hT,a₁,ha₁,a₀,ha₀,h₁,h₀⟩

lemma Reachable.refl (x : X) : P.Reachable x x := Relation.ReflTransGen.refl
lemma Reachable.trans {x y z : X} (h : P.Reachable x y) (k : P.Reachable y z) :
    P.Reachable x z := Relation.ReflTransGen.trans h k
lemma Reachable.symm {x y : X} (h : P.Reachable x y) : P.Reachable y x := by
  induction h with
  | refl => exact .refl P _
  | @tail y z _ hyz ih => exact (Relation.ReflTransGen.single (Related.symm P hyz)).trans ih

lemma leaf_saturated {x y z : X} (hy : y∈P.leaf x) (h : P.Related y z) : z∈P.leaf x :=
  Relation.ReflTransGen.tail hy h

lemma related_in_rectangle {i : ι} {U : Set (A i)} {V : Set (B i)}
    (hU : IsPreconnected U) (hrect : U ×ˢ V ⊆ (P.chart i).target)
    {a₀ a₁ : A i} {b : B i} (ha₀ : a₀∈U) (ha₁ : a₁∈U) (hb : b∈V) :
    P.Related ((P.chart i).symm (a₀,b)) ((P.chart i).symm (a₁,b)) :=
  ⟨i,b,U,hU,fun _ ha => hrect ⟨ha,hb⟩,a₀,ha₀,a₁,ha₁,rfl,rfl⟩

 

theorem closure_saturated {x : X} {i : ι} {U : Set (A i)} {V : Set (B i)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hVo : IsOpen V)
    (hrect : U ×ˢ V ⊆ (P.chart i).target)
    {a₀ a₁ : A i} {b : B i} (ha₀ : a₀∈U) (ha₁ : a₁∈U) (hb : b∈V)
    (hx : (P.chart i).symm (a₀,b)∈closure (P.leaf x)) :
    (P.chart i).symm (a₁,b)∈closure (P.leaf x) := by
  let Q := P.chart i
  let y₀ := Q.symm (a₀,b)
  let H : X → X := fun y => Q.symm (a₁,(Q y).2)
  have ht₀ : (a₀,b)∈Q.target := hrect ⟨ha₀,hb⟩
  have ht₁ : (a₁,b)∈Q.target := hrect ⟨ha₁,hb⟩
  have hy₀ : y₀∈Q.source := Q.map_target ht₀
  have he : Q y₀=(a₀,b) := Q.right_inv ht₀
  have hQ : ContinuousAt Q y₀ := Q.continuousAt hy₀
  have hn : ∀ᶠ y in 𝓝 y₀,y∈Q.source ∧ Q y∈U ×ˢ V := by
    have hh : Q ⁻¹' (U ×ˢ V)∈𝓝 y₀ := hQ.preimage_mem_nhds (by
      rw [he]
      exact (hUo.prod hVo).mem_nhds ⟨ha₀,hb⟩)
    filter_upwards [Q.open_source.mem_nhds hy₀,hh] with y hy hh
    exact ⟨hy,hh⟩
  have hH : ContinuousAt H y₀ :=
    (Q.symm.continuousAt ht₁).comp_of_eq
      (continuousAt_const.prodMk hQ.snd) (by rw [he])
  have hfreq : ∃ᶠ y in 𝓝 y₀,H y∈P.leaf x := by
    apply ((mem_closure_iff_frequently.mp hx).and_eventually hn).mono
    intro y hy
    apply P.leaf_saturated hy.1
    have hr := P.related_in_rectangle hUc hrect hy.2.2.1 ha₁ hy.2.2.2
    simpa only [Q,Q.left_inv hy.2.1] using hr
  have hh := (hH.frequently hfreq).mem_closure
  simpa only [H,he] using hh

 

def LocallySinglePlaque (Z : Set X) (z : X) : Prop :=
  ∃(i : ι) (U : Set (A i)) (V : Set (B i)), IsOpen U ∧ IsPreconnected U ∧ IsOpen V ∧
    U ×ˢ V ⊆ (P.chart i).target ∧ z∈(P.chart i).source ∧ (P.chart i) z∈U ×ˢ V ∧
    ∀y∈Z,y∈(P.chart i).source → (P.chart i) y∈U ×ˢ V →
      ((P.chart i) y).2=((P.chart i) z).2

theorem leaf_isClosed_of_locallySinglePlaque (x : X)
    (h : ∀z∈closure (P.leaf x),P.LocallySinglePlaque (closure (P.leaf x)) z) :
    IsClosed (P.leaf x) := by
  apply isClosed_of_closure_subset
  intro z hz
  obtain ⟨i,U,V,hUo,hUc,hVo,hrect,hzs,hzUV,huniq⟩ := h z hz
  let Q := P.chart i
  have hn : ∀ᶠ y in 𝓝 z,y∈Q.source ∧ Q y∈U ×ˢ V :=
    Filter.Eventually.and (Q.open_source.mem_nhds hzs)
      ((Q.continuousAt hzs).preimage_mem_nhds ((hUo.prod hVo).mem_nhds hzUV))
  obtain ⟨y,hy,hys,hyUV⟩ := ((mem_closure_iff_frequently.mp hz).and_eventually hn).exists
  have he := huniq y (subset_closure hy) hys hyUV
  apply P.leaf_saturated hy
  have hr := P.related_in_rectangle hUc hrect hyUV.1 hzUV.1 hyUV.2
  have ht : Q.symm ((Q z).1,(Q y).2)=z := by rw [he]; exact Q.left_inv hzs
  change P.Related (Q.symm ((Q y).1,(Q y).2))
    (Q.symm ((Q z).1,(Q y).2)) at hr
  rwa [Prod.mk.eta,Q.left_inv hys,ht] at hr

 

theorem locallySinglePlaque_of_finite_transversal {Z : Set X} {z : X}
    {i : ι} [T1Space (B i)] {U : Set (A i)} {V : Set (B i)}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hVo : IsOpen V)
    (hUV : U ×ˢ V ⊆ (P.chart i).target) (hzs : z∈(P.chart i).source)
    (hzUV : (P.chart i) z∈U ×ˢ V)
    {T : Set (B i)} (hT : T.Finite)
    (hZ : ∀y∈Z,y∈(P.chart i).source → (P.chart i) y∈U ×ˢ V →
      ((P.chart i) y).2∈T) : P.LocallySinglePlaque Z z := by
  let b := ((P.chart i) z).2
  let V' := V ∩ (T \ {b})ᶜ
  have hV'o : IsOpen V' := hVo.inter ((hT.sdiff (t := {b})).isClosed.isOpen_compl)
  have hb : b∈V' := ⟨hzUV.2,by simp⟩
  refine ⟨i,U,V',hUo,hUc,hV'o,fun p hp => hUV ⟨hp.1,hp.2.1⟩,
    hzs,⟨hzUV.1,hb⟩,?_⟩
  intro y hy hys hyUV
  have ht := hZ y hy hys ⟨hyUV.1,hyUV.2.1⟩
  by_contra hn
  exact hyUV.2.2 ⟨ht,by simpa only [Set.mem_singleton_iff] using hn⟩

end PlaqueSystem

end

end OAI
