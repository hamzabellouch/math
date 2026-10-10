import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Criticality.FiniteChanges
import OAI.Probability.UnimodularPercolation.Encounter.Counts
import OAI.Probability.UnimodularPercolation.Encounter.TreeBranches

namespace OAI

/-! Exterior branches and finite encounter surgery. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem infinite_cluster_sdiff_contains (G : BondGraph V E) (ω : Set E)
    (F : Set E) (hF : F.Finite) (x : V) (hx : (cluster G ω x).Infinite) :
    ∃ z, Conn G ω x z ∧ (cluster G (ω \ F) z).Infinite := by
  have he : (ω \ F) ∪ (ω ∩ F) = ω := by ext e; simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff]; tauto
  obtain ⟨z,hz,hzi⟩ := infinite_cluster_union_contains G (ω \ F) (ω ∩ F) (hF.inter_of_right ω) x (by rw [he]; exact hx)
  exact ⟨z,by simpa only [he] using hz,hzi⟩

theorem conn_eq_of_no_incident (G : BondGraph V E) (ω : Set E) (x y : V)
    (hx : ∀ e ∈ ω, x ∉ G e) (hxy : Conn G ω x y) : y = x := by
  induction hxy with
  | refl => rfl
  | @tail y z hy hed ih =>
    obtain ⟨e,he,hGe⟩ := hed
    exact False.elim (hx e he (by rw [hGe,ih]; simp))

theorem cluster_singleton_of_no_incident (G : BondGraph V E) (ω : Set E) (x : V)
    (hx : ∀ e ∈ ω, x ∉ G e) : cluster G ω x = {x} := by
  ext y
  constructor
  · intro h; exact conn_eq_of_no_incident G ω x y hx h
  · rintro rfl; exact mem_cluster_self G ω _

theorem deleted_cluster_singleton (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (A : Finset V) (x : V) (hx : x ∈ A) :
    cluster G (ω \ (incidentSupport G hloc A:Set E)) x = {x} := by
  apply cluster_singleton_of_no_incident
  intro e he hxe
  exact he.2 ((mem_incidentSupport G hloc A e).mpr ⟨x,hx,hxe⟩)

theorem conn_exterior_attachment (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (A : Finset V) (x : V) (hx : x ∈ A) {z : V} (hxz : Conn G ω x z) :
    z ∈ A ∨ ∃ v ∈ A, ∃ w, w ∉ A ∧ ∃ e ∈ ω, G e = s(v,w) ∧
      Conn G (ω \ (incidentSupport G hloc A:Set E)) w z := by
  induction hxz with
  | refl => exact Or.inl hx
  | @tail y z hy hed ih =>
    by_cases hz : z ∈ A
    · exact Or.inl hz
    right
    obtain ⟨e,he,hGe⟩ := hed
    rcases ih with hyA | ⟨v,hv,w,hw,f,hf,hGf,hwy⟩
    · exact ⟨y,hyA,z,hz,e,he,hGe,conn_refl G _ z⟩
    · have hyA : y ∉ A := by
        intro hya
        have hs := deleted_cluster_singleton G hloc ω A y hya
        have hyy : w ∈ cluster G (ω \ (incidentSupport G hloc A:Set E)) y := conn_symm G _ hwy
        rw [hs] at hyy
        exact hw (hyy ▸ hya)
      refine ⟨v,hv,w,hw,f,hf,hGf,hwy.tail ⟨e,⟨he,?_⟩,hGe⟩⟩
      intro hei
      obtain ⟨a,ha,hage⟩ := (mem_incidentSupport G hloc A e).mp hei
      rw [hGe,Sym2.mem_iff] at hage
      rcases hage with rfl | rfl
      · exact hyA ha
      · exact hz ha

theorem infinite_exterior_attachment (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (A : Finset V) (x : V) (hx : x ∈ A) (hi : (cluster G ω x).Infinite) :
    ∃ v ∈ A, ∃ w, w ∉ A ∧ ∃ e ∈ ω, G e = s(v,w) ∧ Conn G ω x w ∧
      (cluster G (ω \ (incidentSupport G hloc A:Set E)) w).Infinite := by
  obtain ⟨z,hxz,hz⟩ := infinite_cluster_sdiff_contains G ω _ (incidentSupport G hloc A).finite_toSet x hi
  have hn : z ∉ A := by
    intro hzA
    rw [deleted_cluster_singleton G hloc ω A z hzA] at hz
    exact hz (Set.finite_singleton z)
  obtain ⟨v,hv,w,hw,e,he,hGe,hwz⟩ := (conn_exterior_attachment G hloc ω A x hx hxz).resolve_left hn
  refine ⟨v,hv,w,hw,e,he,hGe,conn_trans G ω hxz (conn_symm G ω (conn_mono G Set.sdiff_subset hwz)),?_⟩
  rwa [cluster_eq_of_conn G _ hwz]

theorem exists_finite_connected_envelope (G : BondGraph V E) (hconn : Connected G)
    (x : V) (R : Finset V) : ∃ A : Finset V, R ⊆ A ∧
      ((openSimpleGraph G Set.univ).induce (A:Set V)).Connected := by
  obtain ⟨F,hF⟩ := finite_connecting_edges G hconn x R
  have hf := cluster_finite_of_finite_edges G F.finite_toSet x
  refine ⟨hf.toFinset,?_,?_⟩
  · intro y hy
    exact hf.mem_toFinset.mpr (hF y hy)
  · rw [hf.coe_toFinset]
    exact cluster_induce_connected G Set.univ (F:Set E) (Set.subset_univ _) x
end Percolation

namespace Percolation
open SimpleGraph
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deleted_envelope_separated (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (A : Finset V) (w : Fin 3 → V)
    (hsep : ∀ i j, Conn G (ω \ (incidentSupport G hloc A:Set E)) (w i) (w j) → i = j)
    (a b : V) (ha : a ∈ A ∪ Finset.univ.image w) (hb : b ∈ A ∪ Finset.univ.image w)
    (hab : Conn G (ω \ (incidentSupport G hloc A:Set E)) a b) : a = b := by
  rcases Finset.mem_union.mp ha with ha | ha
  · have hh := deleted_cluster_singleton G hloc ω A a ha
    have hm : b ∈ cluster G (ω \ (incidentSupport G hloc A:Set E)) a := hab
    rw [hh] at hm
    exact hm.symm
  rcases Finset.mem_union.mp hb with hb | hb
  · have hh := deleted_cluster_singleton G hloc ω A b hb
    have hm : a ∈ cluster G (ω \ (incidentSupport G hloc A:Set E)) b := conn_symm G _ hab
    rw [hh] at hm
    exact hm
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
  exact congrArg w (hsep i j hab)

theorem encounter_surgery_of_attachments (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (A : Finset V) (v w : Fin 3 → V)
    (hv : ∀ i, v i ∈ A) (hw : ∀ i, w i ∉ A) (hwi : Function.Injective w)
    (hadj : ∀ i, (openSimpleGraph G Set.univ).Adj (v i) (w i))
    (hA : ((openSimpleGraph G Set.univ).induce (A:Set V)).Connected)
    (hsep : ∀ i j, Conn G (ω \ (incidentSupport G hloc A:Set E)) (w i) (w j) → i = j)
    (hinf : ∀ i, (cluster G (ω \ (incidentSupport G hloc A:Set E)) (w i)).Infinite) :
    ∃ P : Finset E, P ⊆ incidentSupport G hloc A ∧
      ∃ x, IsEncounter G (finiteOverwrite (incidentSupport G hloc A) P ω) x := by
  obtain ⟨D,hD,hSD,T,hTK,hT,x,a,b,c,hx,ha,hb,hc,hab,hac,hbc⟩ :=
    exists_terminal_tree (openSimpleGraph G Set.univ) A v w hv hw hwi hadj hA
  let F := incidentSupport G hloc A
  let η := ω \ (F:Set E)
  let f : (D:Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let P := F.filter (fun e => ∃ a b : (D:Set V), T.Adj a b ∧ G e = s(a.val,b.val))
  have hPF : P ⊆ F := Finset.filter_subset _ _
  have hP (e : E) (he : e ∈ P) : ∃ a b, T.Adj a b ∧ G e = s(f a,f b) :=
    (Finset.mem_filter.mp he).2
  have hPres (a b : (D:Set V)) (hab : T.Adj a b) : ∃ e ∈ (P:Set E), G e = s(f a,f b) := by
    have hk := hTK hab
    obtain ⟨e,_,he⟩ := hk.1.2
    refine ⟨e,Finset.mem_filter.mpr ⟨?_,⟨a,b,hab,he⟩⟩,he⟩
    apply (mem_incidentSupport G hloc A e).mpr
    rcases terminalGraph_touch _ A v w hv hk with ha | hb
    · exact ⟨a.val,ha,by rw [he]; simp⟩
    · exact ⟨b.val,hb,by rw [he]; simp⟩
  have hsepD (a b : (D:Set V)) (h : Conn G η (f a) (f b)) : a = b := by
    apply Subtype.ext
    exact deleted_envelope_separated G hloc ω A w hsep a.val b.val (hD a.property) (hD b.property) h
  obtain ⟨r,hr,hrη⟩ := exists_cluster_retraction G η f hsepD x
  have hr' (a : (D:Set V)) : r a.val = a := hr a
  have hcut : η ⊆ cutConfig G (η ∪ (P:Set E)) x.val := by
    intro e he
    refine ⟨Or.inl he,?_⟩
    intro hxe
    exact he.2 ((mem_incidentSupport G hloc A e).mpr ⟨x.val,hx,hxe⟩)
  have hInf (z : (D:Set V)) (hz : z.val ∈ Finset.univ.image w) :
      (cluster G (cutConfig G (η ∪ (P:Set E)) x.val) z.val).Infinite := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hz
    apply (hinf i).mono
    intro y hy
    rw [hi] at hy
    exact conn_mono G hcut hy
  have hnew : finiteOverwrite F P ω = η ∪ (P:Set E) := by rfl
  refine ⟨P,hPF,x.val,?_⟩
  rw [hnew]
  refine ⟨a.val,b.val,c.val,?_,?_,?_,hInf a ha,hInf b hb,hInf c hc,?_,?_,?_⟩
  · exact glued_conn G _ T f hT.connected
      (fun a b h => let ⟨e,he,hGe⟩ := hPres a b h; ⟨e,Or.inr he,hGe⟩) x a
  · exact glued_conn G _ T f hT.connected
      (fun a b h => let ⟨e,he,hGe⟩ := hPres a b h; ⟨e,Or.inr he,hGe⟩) x b
  · exact glued_conn G _ T f hT.connected
      (fun a b h => let ⟨e,he,hGe⟩ := hPres a b h; ⟨e,Or.inr he,hGe⟩) x c
  · intro h
    have hh := glued_cut_conn G η (P:Set E) T f r hr hrη hP x h
    exact hab (by simpa only [hr'] using hh)
  · intro h
    have hh := glued_cut_conn G η (P:Set E) T f r hr hrη hP x h
    exact hac (by simpa only [hr'] using hh)
  · intro h
    have hh := glued_cut_conn G η (P:Set E) T f r hr hrη hP x h
    exact hbc (by simpa only [hr'] using hh)

theorem encounter_surgery_of_three (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (ω : Set E) (z : Fin 3 → V)
    (hinf : ∀ i, (cluster G ω (z i)).Infinite)
    (hsep : ∀ i j, Conn G ω (z i) (z j) → i = j) :
    ∃ F P : Finset E, P ⊆ F ∧ ∃ x, IsEncounter G (finiteOverwrite F P ω) x := by
  obtain ⟨A,hA,hAc⟩ := exists_finite_connected_envelope G hconn (z 0) (Finset.univ.image z)
  have hattach (i : Fin 3) := infinite_exterior_attachment G hloc ω A (z i)
    (hA (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)) (hinf i)
  choose v hv w hw e he hGe hzw hInf using hattach
  have hext (i j : Fin 3)
      (h : Conn G (ω \ (incidentSupport G hloc A:Set E)) (w i) (w j)) : i = j :=
    hsep i j (conn_trans G ω (hzw i)
      (conn_trans G ω (conn_mono G Set.sdiff_subset h) (conn_symm G ω (hzw j))))
  have hwi : Function.Injective w := by
    intro i j h
    apply hext
    rw [h]
    exact conn_refl G _ _
  have hadj (i : Fin 3) : (openSimpleGraph G Set.univ).Adj (v i) (w i) := by
    refine ⟨?_,e i,Set.mem_univ _,hGe i⟩
    intro h
    exact hw i (h ▸ hv i)
  obtain ⟨P,hPF,x,hx⟩ := encounter_surgery_of_attachments G hloc ω A v w hv hw hwi hadj hAc hext hInf
  exact ⟨incidentSupport G hloc A,P,hPF,x,hx⟩

theorem three_of_infinite_count (G : BondGraph V E) (ω : Set E)
    (h : (infiniteClusters G ω).Infinite) :
    ∃ z : Fin 3 → V, (∀ i, (cluster G ω (z i)).Infinite) ∧
      ∀ i j, Conn G ω (z i) (z j) → i = j := by
  let e := Set.Infinite.natEmbedding (infiniteClusters G ω) h
  let C (i : Fin 3) := e i.val
  choose z hz using (fun i : Fin 3 => (C i).property.2)
  refine ⟨z,?_,?_⟩
  · intro i; rw [←hz i]; exact (C i).property.1
  · intro i j hij
    have hc : C i = C j := by
      apply Subtype.ext
      rw [hz i,hz j]
      exact cluster_eq_of_conn G ω hij
    exact Fin.ext (e.injective hc)
end Percolation

end OAI
