import OAI.Probability.ClassicalON.SeparatedAnnuli

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph

def extendAnnulusSign (G : LatticeGraph) (N : ℤ) (z : Site)
    (s : (G.annulusGraph N z).vertices → Bool) (v : G.vertices) : Bool :=
  if h : v.val∈annulusSites N z then
    s ⟨v.val,Finset.mem_filter.mpr ⟨v.property,h⟩⟩ else decide (2*N<siteRadius z v.val)

theorem extendAnnulusSign_in (G : LatticeGraph) (N : ℤ) (z : Site)
    (s : (G.annulusGraph N z).vertices → Bool) (v : (G.annulusGraph N z).vertices) :
    G.extendAnnulusSign N z s (G.restrictVertex _ v)=s v := by
  simp only [extendAnnulusSign,show (G.restrictVertex _ v).val∈annulusSites N z from
    (Finset.mem_filter.mp v.property).2,↓reduceDIte]
  rfl

theorem extendAnnulusSign_inner (G : LatticeGraph) (N : ℤ) (hN : 0<N) (z : Site)
    (s : (G.annulusGraph N z).vertices → Bool)
    (hs : ∀ v∈G.annulusPins N z,s v=layerSigns (G.annulusInner N z) v)
    (v : G.vertices) (hv : siteRadius z v.val≤N) : G.extendAnnulusSign N z s v=false := by
  unfold extendAnnulusSign
  split_ifs with h
  · let w : (G.annulusGraph N z).vertices := ⟨v.val,Finset.mem_filter.mpr ⟨v.property,h⟩⟩
    have hw : w∈G.annulusInner N z := le_antisymm hv h.1
    have hh := hs w (Or.inl hw)
    simpa only [layerSigns,hw,ite_true] using hh
  · have hh : ¬2*N<siteRadius z v.val := by omega
    simp only [decide_eq_false hh]

theorem extendAnnulusSign_outer (G : LatticeGraph) (N : ℤ) (hN : 0<N) (z : Site)
    (s : (G.annulusGraph N z).vertices → Bool)
    (hs : ∀ v∈G.annulusPins N z,s v=layerSigns (G.annulusInner N z) v)
    (v : G.vertices) (hv : 2*N≤ siteRadius z v.val) : G.extendAnnulusSign N z s v=true := by
  unfold extendAnnulusSign
  split_ifs with h
  · let w : (G.annulusGraph N z).vertices := ⟨v.val,Finset.mem_filter.mpr ⟨v.property,h⟩⟩
    have hw : w∈G.annulusOuter N z := le_antisymm h.2 hv
    have hw' : w∉G.annulusInner N z := by change siteRadius z v.val≠N; omega
    have hh := hs w (Or.inr hw)
    simpa only [layerSigns,hw',ite_false] using hh
  · have hh : 2*N<siteRadius z v.val := by
      by_contra hn
      apply h
      change N≤ siteRadius z v.val ∧ siteRadius z v.val≤2*N
      omega
    simp only [decide_eq_true hh]

theorem extendAnnulusSign_compatible (G : LatticeGraph) (N : ℤ) (hN : 0<N) (z : Site)
    (η : G.edges → Bool) (s : (G.annulusGraph N z).vertices → Bool)
    (hs : s∈prescribedCompatibleSigns (fun e : (G.annulusGraph N z).edges => e.val.1)
      (fun e => e.val.2) (G.annulusPins N z) (layerSigns (G.annulusInner N z))
      (fun e => η (G.restrictEdge _ e))) :
    G.extendAnnulusSign N z s∈compatibleSigns (fun e : G.edges => e.val.1) (fun e => e.val.2) η := by
  intro e he
  have hstep := siteRadius_neighbor_step z (Or.inl (G.nearest e.val e.property))
  by_cases hl : siteRadius z e.val.1.val<N
  · rw [G.extendAnnulusSign_inner N hN z s hs.2 e.val.1 (by omega),
      G.extendAnnulusSign_inner N hN z s hs.2 e.val.2 (by omega)]
  by_cases hl' : 2*N<siteRadius z e.val.1.val
  · rw [G.extendAnnulusSign_outer N hN z s hs.2 e.val.1 (by omega),
      G.extendAnnulusSign_outer N hN z s hs.2 e.val.2 (by omega)]
  by_cases hr : siteRadius z e.val.2.val<N
  · rw [G.extendAnnulusSign_inner N hN z s hs.2 e.val.1 (by omega),
      G.extendAnnulusSign_inner N hN z s hs.2 e.val.2 (by omega)]
  by_cases hr' : 2*N<siteRadius z e.val.2.val
  · rw [G.extendAnnulusSign_outer N hN z s hs.2 e.val.1 (by omega),
      G.extendAnnulusSign_outer N hN z s hs.2 e.val.2 (by omega)]
  have h1 : e.val.1.val∈annulusSites N z := ⟨by omega,by omega⟩
  have h2 : e.val.2.val∈annulusSites N z := ⟨by omega,by omega⟩
  let e' := G.restrictEdgeEquiv (·∈annulusSites N z) ⟨e,h1,h2⟩
  have hcomp := hs.1 e' he
  rw [← G.extendAnnulusSign_in N z s e'.val.1,← G.extendAnnulusSign_in N z s e'.val.2] at hcomp
  exact hcomp

theorem annulus_crossing_of_connected (G : LatticeGraph) (N : ℤ) (hN : 0<N) (z : Site)
    (η : G.edges → Bool) (x y : G.vertices) (hx : siteRadius z x.val≤N) (hy : 2*N≤ siteRadius z y.val)
    (hxy : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y) :
    G.annulusIndicator N z η=1 := by
  have hd : Disjoint (G.annulusInner N z) (G.annulusOuter N z) := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    change siteRadius z v.val=N at hv
    change siteRadius z v.val=2*N at hw
    omega
  have hc : bondCrossing (fun e : (G.annulusGraph N z).edges => e.val.1) (fun e => e.val.2)
      (G.annulusInner N z) (G.annulusOuter N z) (fun e => η (G.restrictEdge _ e)) := by
    by_contra hn
    obtain ⟨s,hs⟩ := (layerSigns_consistent_iff (fun e : (G.annulusGraph N z).edges => e.val.1)
      (fun e => e.val.2) _ _ hd _).mpr hn
    have he := compatibleSigns_connected _ _ η (G.extendAnnulusSign_compatible N hN z η s hs) hxy
    rw [G.extendAnnulusSign_inner N hN z s hs.2 x hx,G.extendAnnulusSign_outer N hN z s hs.2 y hy] at he
    cases he
  exact ite_eq_left hc

theorem annulus_crossing_of_component (G : LatticeGraph) (N : ℤ) (hN : 0<N)
    (η : G.edges → Bool) (x y w : G.vertices) (hfar : 4*N≤ siteRadius x.val y.val)
    (hxy : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y)
    (hxw : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x w)
    (z : Site) (hw : siteRadius z w.val≤N) : G.annulusIndicator N z η=1 := by
  have hout : 2*N≤ siteRadius z x.val ∨ 2*N≤ siteRadius z y.val := by
    have ht := siteRadius_triangle x.val z y.val
    rw [siteRadius_symm x.val z] at ht
    omega
  rcases hout with hx | hy
  · exact G.annulus_crossing_of_connected N hN z η w x hw hx (bondConnected_symm _ _ _ hxw)
  · exact G.annulus_crossing_of_connected N hN z η w y hw hy
      (bondConnected_trans _ _ _ (bondConnected_symm _ _ _ hxw) hxy)

end ClassicalON.LatticeGraph

end

end OAI
