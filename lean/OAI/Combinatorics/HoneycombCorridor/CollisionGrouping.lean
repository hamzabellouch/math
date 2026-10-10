import Mathlib
import OAI.Combinatorics.HoneycombCorridor.CollisionStems

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem sum_record_three {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (t : α → Finset β) (u : α → β → Finset γ) (F : α × β × γ → ℂ) :
    (∑ z ∈ s.biUnion (fun a => ((t a).biUnion (fun b =>
      (u a b).image (fun c => (b,c)))).image (fun bc => (a,bc))), F z) =
      ∑ a ∈ s, ∑ b ∈ t a, ∑ c ∈ u a b, F (a,b,c) := by
  have h := sum_record_fibers s (fun a => (t a).biUnion (fun b =>
    (u a b).image (fun c => (b,c)))) F
  apply h.trans
  apply Finset.sum_congr rfl
  intro a ha
  exact sum_record_fibers (t a) (u a) (fun bc => F (a,bc))



theorem collision_splice_surjective (D : Finset Vertex) (v : Vertex)
    (e : RayRecord) (he : e ∈ rayCollisions D v) :
    ∃ (P : Polygon) (s c : RayRecord), P ∈ polygons D ∧ s ∈ polygonStems D v P ∧
      c ∈ cyclesAt P (stemEnd v s).1 ∧ spliceRecord v s c = e := by
  classical
  rcases e with ⟨k,w⟩
  have hs := (mem_rayCollisions D v (k,w)).mp he
  let g := rayGerm v k
  have hn := (stopped_iff_trace _ _ _).mp hs.1
  have hm : (terminalGerm g w).1 ∈ traced g w :=
    hn.2.2.resolve_left (not_not.mpr hs.2)
  obtain ⟨u,b,r,hw,hroot⟩ := mem_traced_split g w (terminalGerm g w).1 hm
  have hN : (traced g (u ++ b :: r)).Nodup := hw ▸ hn.1
  have hd : ∀ a ∈ traced g (u ++ b :: r), a ∈ D.erase v := hw ▸ hn.2.1
  have hna := List.nodup_append.mp (show (traced g u ++ traced (terminalGerm g u) (b :: r)).Nodup by
    rwa [← traced_append])
  let f := terminalGerm g u
  have hf : (terminalGerm f (b :: r)).1 = f.1 := by
    change (terminalGerm (terminalGerm g u) (b :: r)).1 = _
    rw [← terminalGerm_append,← hw]
    exact hroot.symm
  have hback : (reverseGerm f).1 ∉ traced f (b :: r) := by
    apply split_back_not_mem g u b r hN
    intro hm
    have hv := (Finset.mem_erase.mp (hd _ hm)).1
    apply hv
    simp [g,rayGerm,reverseGerm]
  obtain ⟨hslot,ha⟩ := collision_root_slots f b r hna.2.1 hf hback
  let t := terminalGerm f (b :: r)
  have ht : t.1 = f.1 := hf
  have htr : traced t ((!b) :: r) = traced f (b :: r) := by
    change t.1 :: traced (advance t (!b)) r = _
    rw [ha,ht]
    rfl
  have hNt : (traced t ((!b) :: r)).Nodup := htr ▸ hna.2.1
  have hct : terminalGerm t ((!b) :: r) = t := by
    change terminalGerm (advance t (!b)) r = _
    rw [ha]
    rfl
  let P := polygonOfClosed t ((!b) :: r) (by simp) hNt hct
  have hPv : P.vertices = (traced f (b :: r)).toFinset := by
    rw [polygonOfClosed_vertices,htr]
  have hPD : P ∈ polygons D := by
    apply (mem_polygons D P).mpr
    rw [hPv]
    intro a ha
    exact Finset.mem_of_mem_erase (hd a (by rw [traced_append]; exact List.mem_append_right _ (List.mem_toFinset.mp ha)))
  have hnv : v ∉ P.vertices := by
    rw [hPv]
    intro hv
    exact (Finset.mem_erase.mp (hd v (by rw [traced_append]; exact List.mem_append_right _ (List.mem_toFinset.mp hv)))).1 rfl
  have hsf : (k,u) ∈ polygonStems D v P := by
    rw [mem_polygonStems]
    refine ⟨hnv,(stopped_iff_trace _ _ _).mpr ⟨hna.1,?_,Or.inl ?_⟩,?_⟩
    · intro a ha
      have hDa := hd a (by rw [traced_append]; exact List.mem_append_left _ ha)
      refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hDa).1,Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hDa,?_⟩⟩
      rw [hPv]
      intro hPa
      exact hna.2.2 a ha a (List.mem_toFinset.mp hPa) rfl
    · intro ha
      have hnot := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase ha)).2
      apply hnot
      rw [hPv]
      simp only [List.mem_toFinset,traced,List.mem_cons]
      exact Or.inl rfl
    · change f.1 ∈ P.vertices
      rw [hPv]
      simp [traced]
  have het : (f.1,t.2) = t := Prod.ext ht.symm rfl
  refine ⟨P,(k,u),(t.2,(!b) :: r),hPD,hsf,?_,?_⟩
  · rw [mem_cyclesAt]
    change P.Traverses (f.1,t.2) ((!b) :: r)
    rw [het]
    exact ⟨by simp,hNt,hct,rfl⟩
  · simp only [spliceRecord,attachWord,Bool.not_not]
    exact Prod.ext rfl hw.symm

theorem spliceRecord_terminal {D : Finset Vertex} (v : Vertex) (P : Polygon) (s c : RayRecord)
    (hs : IsPolygonStem D v P s) (hc : c ∈ cyclesAt P (stemEnd v s).1) :
    stemEnd v (spliceRecord v s c) = ((stemEnd v s).1,c.1) := by
  change terminalGerm (rayGerm v s.1) (s.2 ++ attachWord c) = _
  rw [terminalGerm_append]
  exact (attached_trace P (stemEnd v s) c hc hs.back_outside).2

theorem collision_splice_injective (D : Finset Vertex) (v : Vertex)
    (P Q : Polygon) (s t c d : RayRecord)
    (hs : s ∈ polygonStems D v P) (ht : t ∈ polygonStems D v Q)
    (hc : c ∈ cyclesAt P (stemEnd v s).1) (hd : d ∈ cyclesAt Q (stemEnd v t).1)
    (he : spliceRecord v s c = spliceRecord v t d) : P = Q ∧ s = t ∧ c = d := by
  have hs' := (mem_polygonStems D v P s).mp hs
  have ht' := (mem_polygonStems D v Q t).mp ht
  have hends := congrArg (stemEnd v) he
  rw [spliceRecord_terminal v P s c hs' hc,spliceRecord_terminal v Q t d ht' hd] at hends
  have hends := Prod.mk.inj hends
  have hwords : s.1 = t.1 ∧
      s.2 ++ attachWord c = t.2 ++ attachWord d := Prod.mk.inj he
  have hst : s.2 = t.2 := by
    apply first_cut_unique (rayGerm v s.1) (stemEnd v s).1 s.2 (attachWord c) t.2 (attachWord d) hwords.2 rfl
    · rw [hwords.1]
      exact hends.1.symm
    · exact fun h => hs'.trace_disjoint _ h hs'.2.2
    · rw [hwords.1]
      exact fun h => ht'.trace_disjoint _ h (hends.1.symm ▸ ht'.2.2)
  have hst' : s = t := Prod.ext hwords.1 hst
  subst t
  have hcdw := attachWord_injective_on_words c d (List.append_cancel_left hwords.2)
  have hcd : c = d := Prod.ext hends.2 hcdw
  subst d
  have hp := (mem_cyclesAt _ _ _).mp hc
  have hq := (mem_cyclesAt _ _ _).mp hd
  exact ⟨Subtype.ext (hp.2.2.2.symm.trans hq.2.2.2),rfl,rfl⟩

noncomputable def collisionData (D : Finset Vertex) (v : Vertex) : Finset (Polygon × RayRecord × RayRecord) := by
  classical
  exact (polygons D).biUnion fun P =>
    ((polygonStems D v P).biUnion fun s =>
      (cyclesAt P (stemEnd v s).1).image fun c => (s,c)).image fun sc => (P,sc)

@[simp] theorem mem_collisionData (D : Finset Vertex) (v : Vertex) (P : Polygon) (s c : RayRecord) :
    (P,s,c) ∈ collisionData D v ↔ P ∈ polygons D ∧ s ∈ polygonStems D v P ∧
      c ∈ cyclesAt P (stemEnd v s).1 := by
  classical
  simp only [collisionData,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨Q,hQ,⟨t,d⟩,⟨z,hz,a,ha,hza⟩,hQz⟩
    have he := Prod.mk.inj hQz
    have he' := Prod.mk.inj hza
    rcases he with ⟨rfl,he⟩
    have hzs : z = s := he'.1.trans (congrArg Prod.fst he)
    have hac : a = c := he'.2.trans (congrArg Prod.snd he)
    subst z
    subst a
    exact ⟨hQ,hz,ha⟩
  · rintro ⟨hP,hs,hc⟩
    exact ⟨P,hP,(s,c),⟨s,hs,c,hc,rfl⟩,rfl⟩

theorem collisionData_sum (D : Finset Vertex) (v : Vertex) :
    (∑ z ∈ collisionData D v, wordWeight (spliceRecord v z.2.1 z.2.2).2) =
      ∑ P ∈ polygons D, ∑ s ∈ polygonStems D v P,
        ∑ c ∈ cyclesAt P (stemEnd v s).1, wordWeight (spliceRecord v s c).2 := by
  classical
  unfold collisionData
  convert sum_record_three (polygons D) (polygonStems D v)
    (fun P s => cyclesAt P (stemEnd v s).1)
    (fun z : Polygon × RayRecord × RayRecord => wordWeight (spliceRecord v z.2.1 z.2.2).2) using 1
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext z
  simp only [Finset.mem_biUnion,Finset.mem_image]

theorem collision_sum_grouped (D : Finset Vertex) (v : Vertex) :
    (∑ e ∈ rayCollisions D v, wordWeight e.2) =
      ∑ P ∈ polygons D, ∑ s ∈ polygonStems D v P,
        ∑ c ∈ cyclesAt P (stemEnd v s).1, wordWeight (spliceRecord v s c).2 := by
  classical
  have hsum : (∑ z ∈ collisionData D v, wordWeight (spliceRecord v z.2.1 z.2.2).2) =
      ∑ e ∈ rayCollisions D v, wordWeight e.2 := by
    apply Finset.sum_bij (fun z _ => spliceRecord v z.2.1 z.2.2)
    · intro z hz
      have h := (mem_collisionData D v z.1 z.2.1 z.2.2).mp hz
      exact spliceRecord_mem D v z.1 h.1 z.2.1 h.2.1 z.2.2 h.2.2
    · intro z hz y hy he
      have h := (mem_collisionData D v z.1 z.2.1 z.2.2).mp hz
      have h' := (mem_collisionData D v y.1 y.2.1 y.2.2).mp hy
      have heq := collision_splice_injective D v z.1 y.1 z.2.1 y.2.1 z.2.2 y.2.2 h.2.1 h'.2.1 h.2.2 h'.2.2 he
      exact Prod.ext heq.1 (Prod.ext heq.2.1 heq.2.2)
    · intro e he
      obtain ⟨P,s,c,hP,hs,hc,rfl⟩ := collision_splice_surjective D v e he
      exact ⟨(P,s,c),(mem_collisionData D v P s c).mpr ⟨hP,hs,hc⟩,rfl⟩
    · intro z hz
      rfl
  exact hsum.symm.trans (collisionData_sum D v)

end PolynomialVacuumBridge.Corridor

end

end OAI
