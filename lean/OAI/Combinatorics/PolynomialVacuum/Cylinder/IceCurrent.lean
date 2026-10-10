import OAI.Combinatorics.PolynomialVacuum.Cylinder.NetworkComponents

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

theorem dartSign_ne_zero (g : Germ M) : dartSign g≠0 := by
  rcases g with ⟨v,k⟩; cases v <;> simp [dartSign]

theorem orientedFlow_eq_zero_iff (q : Edge M →₀ ℤ) (g : Germ M) :
    orientedFlow q g=0 ↔ q (edgeOf g)=0 := by
  rw [orientedFlow_eq,mul_eq_zero]
  exact or_iff_right (dartSign_ne_zero g)

theorem flow_zero_outside_vertices (q : Edge M →₀ ℤ) (P : Polygon M)
    (hs : q.support⊆P.val) (v : Vertex M) (hv : v∉P.vertices) (k : Fin 3) :
    orientedFlow q (v,k)=0 := by
  apply (orientedFlow_eq_zero_iff q (v,k)).mpr
  apply not_ne_iff.mp
  intro hn
  have he := hs (Finsupp.mem_support_iff.mpr hn)
  apply hv
  exact Finset.mem_biUnion.mpr ⟨edgeOf (v,k),he,by simp⟩

theorem outgoingSlot_ne (g : Germ M) (b : Bool) : outgoingSlot g b≠g.2 := by
  rcases g with ⟨v,k⟩; fin_cases k <;> cases b <;> simp only [outgoingSlot] <;> decide

theorem wordContour_localIce (q : Edge M →₀ ℤ) (g : Germ M) (w : List Bool)
    (hc : WordContour q g w) (v : Vertex M) (hv : v∈traced g w) : LocalIce q v := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inr ⟨g.2,outgoingSlot g b,(outgoingSlot_ne g b).symm,hc.1⟩
    · exact ih (advance g b) hc.2 hv

theorem simple_word_localIce (g : Germ M) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w=g) :
    ∀ v,LocalIce (wordFlow g w) v := by
  intro v
  by_cases hv : v∈traced g w
  · exact wordContour_localIce _ _ _ (simple_closed_word_contour g w hN hc) v hv
  · left
    intro k
    rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
    exact turnVisit_eq_zero_of_not_mem g w v k hv

theorem LocalIce.sum_zero {q : Edge M →₀ ℤ} {v : Vertex M} (h : LocalIce q v) :
    ∑ k : Fin 3,orientedFlow q (v,k)=0 := by
  rcases h with hz | ⟨i,o,_,h⟩
  · simp [hz]
  · simp_rw [h]
    rw [Finset.sum_sub_distrib]
    simp

theorem allLocalIce_conserved (q : Edge M →₀ ℤ) (hq : ∀ v,LocalIce q v) : Conserved q := by
  constructor
  · intro i j
    have h:=(hq (.up i j)).sum_zero
    simpa [Fin.sum_univ_succ,orientedFlow_up,add_assoc] using h
  · intro i j
    have h:=(hq (.down i j)).sum_zero
    simp [Fin.sum_univ_succ,orientedFlow_down,edgeOf] at h
    omega

theorem Conserved.sum_zero {q : Edge M →₀ ℤ} (hq : Conserved q) (v : Vertex M) :
    ∑ k : Fin 3,orientedFlow q (v,k)=0 := by
  cases v with
  | up i j => simpa [Fin.sum_univ_succ,orientedFlow_up,add_assoc] using hq.up i j
  | down i j =>
    have h:=hq.down i j
    simp [Fin.sum_univ_succ,orientedFlow_down,edgeOf]
    omega

namespace ClosedNetwork
variable (C : ClosedNetwork M)

theorem component_flow_localIce (P : Polygon M) (hP : P∈C.polygons) :
    ∀ v,LocalIce (C.componentFlow P) v := by
  obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp hP
  rw [C.componentFlow_word]
  exact simple_word_localIce _ _ (C.orbit_nodup u) (C.orbit_terminal u)

theorem component_oriented_at (v u : C.sites) (hu : C.next.SameCycle v u) (k : Fin 3) :
    orientedFlow (C.componentFlow (C.polygon v)) (u.val,k)=
      (if k=C.exit u then 1 else 0)-(if k=C.enter u then 1 else 0) := by
  rw [C.polygon_eq_of_sameCycle v u hu,C.componentFlow_word]
  obtain ⟨l,hl⟩:=Nat.exists_eq_succ_of_ne_zero (C.period_pos u).ne'
  have hN:=C.orbit_nodup u
  have hc:=C.orbit_terminal u
  rw [hl,word] at hN hc ⊢
  change orientedFlow (wordFlow (C.germ u) (C.turn u::C.word l (C.next u))) ((C.germ u).1,k)=_
  rw [simple_closed_word_local _ _ _ hN hc,C.outgoing_turn]
  rfl

end ClosedNetwork
end PolynomialVacuumCylinder

end OAI
