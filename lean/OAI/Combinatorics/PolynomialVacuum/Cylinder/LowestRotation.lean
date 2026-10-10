import OAI.Combinatorics.PolynomialVacuum.Cylinder.TurnMin

namespace OAI

namespace PolynomialVacuumCylinder
open Classical

 

theorem exists_lowest_rotation (g : PlaneGerm) (w : List Bool) (d : ℤ)
    (hne : w≠[]) (hc : PolynomialVacuumBridge.Corridor.terminalGerm g w=translateGerm d g) :
    ∃ (u z : List Bool) (b : Bool) (i j : ℤ), w=u++b::z ∧
      PolynomialVacuumBridge.Corridor.terminalGerm g u=(.up i j,if b then 2 else 1) ∧
      ∀ v∈PolynomialVacuumBridge.Corridor.traced (.up i j,if b then 2 else 1) (b::(z++u)),j≤layer v := by
  have hn : (PolynomialVacuumBridge.Corridor.traced g w).toFinset.Nonempty := by
    cases w with
    | nil => contradiction
    | cons b w => exact ⟨g.1,by simp [PolynomialVacuumBridge.Corridor.traced]⟩
  obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image _ height hn
  obtain ⟨u,b,z,hw,hv'⟩ := PolynomialVacuumBridge.Corridor.mem_traced_split g w v (List.mem_toFinset.mp hv)
  subst w
  let g' := PolynomialVacuumBridge.Corridor.terminalGerm g u
  have hC := periodic_closed_rotate g u (b::z) d hc
  have hH := periodic_rotate_height g u (b::z) d (height v) hc (by simpa using hmin)
  have hg : g'.1=v := hv'
  have hout : height g'.1≤height (PolynomialVacuumBridge.Corridor.advance g' b).1 := by
    cases hz : z++u with
    | nil =>
      have ha : PolynomialVacuumBridge.Corridor.advance g' b=translateGerm d g' := by simpa only [List.cons_append,hz,PolynomialVacuumBridge.Corridor.terminalGerm] using hC
      rw [ha]
      simp [translateGerm]
    | cons c W =>
      rw [hg]
      apply hH
      change (PolynomialVacuumBridge.Corridor.advance g' b).1∈PolynomialVacuumBridge.Corridor.traced g' (b::(z++u))
      rw [hz]
      simp [PolynomialVacuumBridge.Corridor.traced]
  have hin : height g'.1≤height (PolynomialVacuumBridge.Corridor.neighbor g'.1 g'.2) := by
    have hh := incoming_height_lower g' ((b::z)++u) (by simp) (height v) hH
    rw [hC] at hh
    simpa only [translateGerm,← translate_neighbor,height_translate,← hg] using hh
  obtain ⟨i,j,hg'⟩ := lowest_turn g' b hin hout
  refine ⟨u,z,b,i,j,rfl,hg',?_⟩
  intro q hq
  have hh := hH q (by simpa [g',hg'] using hq)
  have hvj : v=PolynomialVacuumBridge.Corridor.Vertex.up i j := hg.symm.trans (congrArg Prod.fst hg')
  rw [hvj] at hh
  cases q <;> simp [height,layer] at hh ⊢ <;> omega

end PolynomialVacuumCylinder

end OAI
