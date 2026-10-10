import OAI.Combinatorics.PolynomialVacuum.Cylinder.BottomTurn
import OAI.Combinatorics.HoneycombCorridor.CollisionCancellation

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}

def height : PlaneVertex → ℤ
  | .up _ j => 3*j+1
  | .down _ j => 3*j+2

@[simp] theorem height_translate (d : ℤ) (v : PlaneVertex) : height (translateVertex d v)=height v := by cases v <;> rfl

theorem lowest_turn (g : PlaneGerm) (b : Bool)
    (hin : height g.1≤height (PolynomialVacuumBridge.Corridor.neighbor g.1 g.2))
    (hout : height g.1≤height (PolynomialVacuumBridge.Corridor.advance g b).1) :
    ∃ i j : ℤ, g=(PolynomialVacuumBridge.Corridor.Vertex.up i j,if b then 2 else 1) := by
  rcases g with ⟨v,k⟩
  cases v with
  | up i j =>
    refine ⟨i,j,?_⟩
    fin_cases k <;> cases b <;>
      simp [height,PolynomialVacuumBridge.Corridor.advance,PolynomialVacuumBridge.Corridor.neighbor,PolynomialVacuumBridge.Corridor.outgoingSlot] at hin hout ⊢ <;> omega
  | down i j =>
    fin_cases k <;> cases b <;>
      simp [height,PolynomialVacuumBridge.Corridor.advance,PolynomialVacuumBridge.Corridor.neighbor,PolynomialVacuumBridge.Corridor.outgoingSlot] at hin hout

theorem incoming_height_lower (g : PlaneGerm) (w : List Bool) (hne : w≠[]) (A : ℤ)
    (hA : ∀ v∈PolynomialVacuumBridge.Corridor.traced g w, A≤height v) :
    A≤height (PolynomialVacuumBridge.Corridor.neighbor (PolynomialVacuumBridge.Corridor.terminalGerm g w).1 (PolynomialVacuumBridge.Corridor.terminalGerm g w).2) := by
  induction w generalizing g with
  | nil => contradiction
  | cons b w ih =>
    cases w with
    | nil =>
      have h := hA g.1 (by simp [PolynomialVacuumBridge.Corridor.traced])
      simpa [PolynomialVacuumBridge.Corridor.terminalGerm,PolynomialVacuumBridge.Corridor.advance,
        PolynomialVacuumBridge.Corridor.neighbor_neighbor] using h
    | cons c w =>
      exact ih (PolynomialVacuumBridge.Corridor.advance g b) (by simp) (by intro v hv; exact hA v (List.mem_cons_of_mem _ hv))

theorem periodic_closed_rotate (g : PlaneGerm) (u w : List Bool) (d : ℤ)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm g (u++w)=translateGerm d g) :
    PolynomialVacuumBridge.Corridor.terminalGerm (PolynomialVacuumBridge.Corridor.terminalGerm g u) (w++u)=
      translateGerm d (PolynomialVacuumBridge.Corridor.terminalGerm g u) := by
  rw [PolynomialVacuumBridge.Corridor.terminalGerm_append] at hc ⊢
  rw [hc,← translate_terminal]

theorem periodic_rotate_height (g : PlaneGerm) (u w : List Bool) (d A : ℤ)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm g (u++w)=translateGerm d g)
    (hA : ∀ v∈PolynomialVacuumBridge.Corridor.traced g (u++w), A≤height v) :
    ∀ v∈PolynomialVacuumBridge.Corridor.traced (PolynomialVacuumBridge.Corridor.terminalGerm g u) (w++u), A≤height v := by
  intro v hv
  rw [PolynomialVacuumBridge.Corridor.terminalGerm_append] at hc
  rw [PolynomialVacuumBridge.Corridor.traced_append,hc,← translate_traced,List.mem_append] at hv
  rcases hv with hv | hv
  · exact hA v (by simp [PolynomialVacuumBridge.Corridor.traced_append,hv])
  · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv
    simpa using hA q (by simp [PolynomialVacuumBridge.Corridor.traced_append,hq])

 

theorem periodic_turn_zero (g : PlaneGerm) (w : List Bool) (d : ℤ)
    (hne : w≠[]) (hc : PolynomialVacuumBridge.Corridor.terminalGerm g w=translateGerm d g)
    (hd : (d : ZMod M)=0) (hd0 : d≠0)
    (hN : (traced (projectGerm M g) w).Nodup) : PolynomialVacuumBridge.Corridor.turnUnits w=0 := by
  classical
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
  have hclosed : terminalGerm (projectGerm M g) (u++b::z)=projectGerm M g := by
    rw [← project_terminal,hc]
    simp [projectGerm,translateGerm,project_translate d hd]
  have hn' := (closed_word_rotate (projectGerm M g) u (b::z) hN hclosed).1
  change (traced (terminalGerm (projectGerm M g) u) ((b::z)++u)).Nodup at hn'
  rw [← project_terminal] at hn'
  have ht := bottom_periodic_turn_zero (M:=M) i j d b (z++u) hd hd0
    (by simpa [g',hg'] using hC) (by simpa [g',hg'] using hn') ?_
  · simp only [PolynomialVacuumBridge.Corridor.turnUnits_append] at ht ⊢
    simp only [PolynomialVacuumBridge.Corridor.turnUnits,List.map_cons,List.sum_cons,List.map_append,List.sum_append] at ht ⊢
    omega
  · intro q hq
    have hh := hH q (by simpa [g',hg'] using hq)
    have hvj : v=PolynomialVacuumBridge.Corridor.Vertex.up i j := hg.symm.trans (congrArg Prod.fst hg')
    rw [hvj] at hh
    cases q <;> simp [height,layer] at hh ⊢ <;> omega

end PolynomialVacuumCylinder

end OAI
