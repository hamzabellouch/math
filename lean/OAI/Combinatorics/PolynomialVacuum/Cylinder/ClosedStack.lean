import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackEquiv
import OAI.Combinatorics.PolynomialVacuum.Cylinder.ClosedDomain
import OAI.Combinatorics.PolynomialVacuum.Pairing.StackReindex

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

def EmptyStackBoundary (c : StackCoordinates M H) : Prop :=
  c.1 0=(fun _=>.zero) ∧ c.1 (Fin.last H)=(fun _=>.zero)

private theorem empty_vertical_outside (v : Fin (H+1) → ZMod M → Spin)
    (hv : v 0=(fun _=>.zero) ∧ v (Fin.last H)=(fun _=>.zero))
    (j : ℤ) (hj : j≤0 ∨ (H : ℤ)≤j) : extendSpins v j=(fun _=>.zero) := by
  by_cases h0 : j=0
  · subst j
    simpa using (extendSpins_nat v 0).trans hv.1
  by_cases hH : j=(H : ℤ)
  · subst j
    simpa using (extendSpins_nat v (Fin.last H)).trans hv.2
  apply extendSpins_outside
  omega

 
theorem empty_stack_outside (c : StackCoordinates M H) (hc : EmptyStackBoundary c)
    (v : Vertex M) (hv : v∉bandSites M H) (s : Fin 3) :
    orientedFlow (coordinatesCurrent c) (v,s)=0 := by
  have hj : ¬(0≤vertexLayer v ∧ vertexLayer v<(H : ℤ)) := by simpa [mem_bandSites,InBand] using hv
  cases v with
  | up i j =>
    dsimp [vertexLayer] at hj
    have hz:=empty_vertical_outside c.1 hc j (by omega)
    have ha:=extendSpins_outside c.2.1 j hj
    have hk:=extendSpins_outside c.2.2 j hj
    fin_cases s <;> simp [orientedFlow_up,coordinatesCurrent,stackValues,hz,ha,hk,charge]
  | down i j =>
    dsimp [vertexLayer] at hj
    have hz:=empty_vertical_outside c.1 hc (j+1) (by omega)
    have ha:=extendSpins_outside c.2.1 j hj
    have hk:=extendSpins_outside c.2.2 j hj
    fin_cases s <;> simp [orientedFlow_down,edgeOf,coordinatesCurrent,stackValues,hz,ha,hk,charge]

theorem empty_stack_active (c : StackCoordinates M H) (hc : EmptyStackBoundary c) :
    activeSites (coordinatesCurrent c)⊆bandSites M H := by
  intro v hv
  by_contra hn
  obtain ⟨s,hs⟩:=(mem_activeSites _ _).mp hv
  exact hs (empty_stack_outside c hc v hn s)

theorem empty_stack_legal (c : LegalStack M H) (hc : EmptyStackBoundary c.val) :
    ∀v,LocalIce (coordinatesCurrent c.val) v := by
  intro v
  by_cases hv : v∈bandSites M H
  · exact c.property v hv
  · exact Or.inl (empty_stack_outside c.val hc v hv)

theorem closed_domain_boundary (q : ClosedDomainFlow (bandSites M H)) :
    EmptyStackBoundary (recoverCoordinates (H:=H) q.val.val) := by
  have hz (v : Vertex M) (hv : v∉bandSites M H) (s : Fin 3) : orientedFlow q.val.val (v,s)=0 := by
    by_contra hh
    exact hv (q.property ((mem_activeSites _ _).mpr ⟨s,hh⟩))
  have h0 (i : ZMod M) : q.val.val ((i,0),0)=0 := by
    have he:=hz (.down i (-1)) (by simp [mem_bandSites,InBand,vertexLayer]) 0
    simpa [orientedFlow_down,edgeOf] using he
  have hH (i : ZMod M) : q.val.val ((i,(H : ℤ)),0)=0 := by
    simpa only [orientedFlow_up] using hz (.up i H) (by simp [mem_bandSites,InBand,vertexLayer]) 0
  constructor <;> funext i <;> simp [recoverCoordinates,recoverVertical,h0,hH,spinOfCharge]

abbrev ClosedStack (M H : ℕ) [NeZero M] := {c : LegalStack M H // EmptyStackBoundary c.val}

noncomputable def closedStackEquiv (hH : 0<H) : ClosedStack M H ≃ ClosedDomainFlow (bandSites M H) where
  toFun c:=⟨⟨coordinatesCurrent c.val.val,empty_stack_legal c.val c.property⟩,empty_stack_active c.val.val c.property⟩
  invFun q:=⟨⟨recoverCoordinates q.val.val,by
    have hs : SupportedAt (bandSites M H) q.val.val := by
      intro g hg _
      by_contra hn
      have ha : g.1∈activeSites q.val.val := (mem_activeSites _ _).mpr ⟨g.2,hn⟩
      exact (hg (q.property ha)).elim
    have he : coordinatesCurrent (recoverCoordinates (H:=H) q.val.val)=q.val.val :=
      recover_stack _ (fun v _=>q.val.property v) hs
    rw [he]
    exact fun v _=>q.val.property v⟩,closed_domain_boundary q⟩
  left_inv c:=by
    apply Subtype.ext
    apply Subtype.ext
    apply coordinatesCurrent_injective
    exact recover_stack _ c.val.property (stack_supported hH c.val.val.1 c.val.val.2.1 c.val.val.2.2)
  right_inv q:=by
    apply Subtype.ext
    apply Subtype.ext
    apply recover_stack _ (fun v _=>q.val.property v)
    intro g hg _
    by_contra hn
    exact (hg (q.property ((mem_activeSites _ _).mpr ⟨g.2,hn⟩))).elim

end PolynomialVacuumCylinder

end OAI
