import OAI.Combinatorics.PolynomialVacuum.Cylinder.Box

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}

theorem repeatWord_front (w : List Bool) (n : ℕ) : repeatWord w (n+1)=w++repeatWord w n := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih =>
    change repeatWord w (n+1)++w=w++(repeatWord w n++w)
    rw [ih,List.append_assoc]

theorem repeat_layers (g : PlaneGerm) (w : List Bool) (d A : ℤ)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm g w=translateGerm d g)
    (hA : ∀ v∈PolynomialVacuumBridge.Corridor.traced g w, A≤layer v) (n : ℕ) :
    ∀ v∈PolynomialVacuumBridge.Corridor.traced g (repeatWord w n), A≤layer v := by
  intro v hv
  rw [traced_repeat _ _ _ hc] at hv
  obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp hv
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hk
  simpa using hA u hu

theorem bottom_start_advance (i j : ℤ) (b : Bool) :
    PolynomialVacuumBridge.Corridor.advance (.up i j,0) (!b)=PolynomialVacuumBridge.Corridor.advance (.up i j,(if b then 2 else 1)) b := by
  cases b <;> simp [PolynomialVacuumBridge.Corridor.advance,PolynomialVacuumBridge.Corridor.outgoingSlot,PolynomialVacuumBridge.Corridor.neighbor]

theorem bottom_end_advance (i j : ℤ) (b : Bool) :
    PolynomialVacuumBridge.Corridor.advance (.up i j,(if b then 2 else 1)) (!b)=(.down i (j-1),0) := by
  cases b <;> simp [PolynomialVacuumBridge.Corridor.advance,PolynomialVacuumBridge.Corridor.outgoingSlot,PolynomialVacuumBridge.Corridor.neighbor]

 

theorem bottom_periodic_turn_zero (i j d : ℤ) (b : Bool) (w : List Bool)
    (hd : (d : ZMod M)=0) (hd0 : d≠0)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm (.up i j,(if b then 2 else 1)) (b::w)=
      translateGerm d (.up i j,(if b then 2 else 1)))
    (hN : (traced (projectGerm M (.up i j,(if b then 2 else 1))) (b::w)).Nodup)
    (hA : ∀ v∈PolynomialVacuumBridge.Corridor.traced (.up i j,(if b then 2 else 1)) (b::w), j≤layer v) :
    PolynomialVacuumBridge.Corridor.turnUnits (b::w)=0 := by
  let g : PlaneGerm := (.up i j,(if b then 2 else 1))
  let g0 : PlaneGerm := (.up i j,0)
  let W := w++repeatWord (b::w) 7
  have hword : repeatWord (b::w) 8=b::W := by
    rw [show (8 : ℕ)=7+1 from rfl,repeatWord_front]
    rfl
  have hfirst : PolynomialVacuumBridge.Corridor.advance g0 (!b)=PolynomialVacuumBridge.Corridor.advance g b := bottom_start_advance i j b
  have ht : PolynomialVacuumBridge.Corridor.terminalGerm g0 ((!b)::W)=translateGerm (8*d) g := by
    simp only [PolynomialVacuumBridge.Corridor.terminalGerm,hfirst]
    have hh := terminal_repeat g (b::w) d hc 8
    rw [hword] at hh
    simpa [PolynomialVacuumBridge.Corridor.terminalGerm] using hh
  have htr : PolynomialVacuumBridge.Corridor.traced g0 ((!b)::W)=PolynomialVacuumBridge.Corridor.traced g (repeatWord (b::w) 8) := by
    rw [hword]
    simp only [PolynomialVacuumBridge.Corridor.traced,hfirst]
    rfl
  let walk := ((!b)::W)++[!b]
  have he : PolynomialVacuumBridge.Corridor.terminalGerm g0 walk=(.down (i+8*d) (j-1),0) := by
    rw [show walk=((!b)::W)++[!b] from rfl,PolynomialVacuumBridge.Corridor.terminalGerm_append,ht]
    simpa [PolynomialVacuumBridge.Corridor.terminalGerm,translateGerm,translateVertex,g] using bottom_end_advance (i+8*d) j b
  have htrace : PolynomialVacuumBridge.Corridor.traced g0 walk=PolynomialVacuumBridge.Corridor.traced g (repeatWord (b::w) 8)++[(translateGerm (8*d) g).1] := by
    rw [show walk=((!b)::W)++[!b] from rfl,PolynomialVacuumBridge.Corridor.traced_append,htr,ht]
    rfl
  have hfull : (PolynomialVacuumBridge.Corridor.traced g0 walk).Nodup := by
    have hn := repeated_trace_nodup g (b::w) d hc hd hd0 hN 9
    rw [show repeatWord (b::w) 9=repeatWord (b::w) 8++(b::w) from rfl,
      PolynomialVacuumBridge.Corridor.traced_append,terminal_repeat _ _ _ hc,PolynomialVacuumBridge.Corridor.traced] at hn
    rw [htrace]
    exact (List.nodup_append.mp hn).1.append
      (by simp) (by
        intro v hv hu
        simp only [List.mem_singleton] at hu
        exact (List.nodup_append.mp hn).2.2 v hv _ (by simp [g]) hu)
  have hheight : ∀ v∈PolynomialVacuumBridge.Corridor.traced g0 walk, j≤layer v := by
    intro v hv
    rw [htrace,List.mem_append] at hv
    rcases hv with hv | hv
    · exact repeat_layers g (b::w) d j hc hA 8 v hv
    · simp only [List.mem_singleton] at hv
      rw [hv]
      simp [translateGerm,translateVertex,g,layer]
  obtain ⟨R,hR⟩ := finite_above_box j (PolynomialVacuumBridge.Corridor.traced g0 walk).toFinset (by simpa using hheight)
  have hout : (PolynomialVacuumBridge.Corridor.terminalGerm g0 walk).1∉aboveBox j R := by
    rw [he]
    simp [mem_aboveBox,layer]
  have hexc : PolynomialVacuumBridge.Corridor.IsExcursion (aboveBox j R) (g0,walk) := by
    refine ⟨hR (by simp [walk,PolynomialVacuumBridge.Corridor.traced,g0]),?_,PolynomialVacuumBridge.Corridor.stopped_of_trace _ _ _ hfull ?_ hout,hout⟩
    · simp [g0,PolynomialVacuumBridge.Corridor.reverseGerm,PolynomialVacuumBridge.Corridor.neighbor,mem_aboveBox,layer]
    · intro v hv
      exact hR (List.mem_toFinset.mpr hv)
  have hturn := PolynomialVacuumBridge.Corridor.convex_excursion_turn_bound _ (aboveBox_convex j R) (g0,walk) hexc
  have hsum : PolynomialVacuumBridge.Corridor.turnUnits walk=8*PolynomialVacuumBridge.Corridor.turnUnits (b::w)+3*(if b then (-1 : ℤ) else 1) := by
    have hr := turnUnits_repeat (b::w) 8
    rw [hword] at hr
    simp only [PolynomialVacuumBridge.Corridor.turnUnits,List.map_cons,List.sum_cons] at hr
    rw [show walk=((!b)::W)++[!b] from rfl,PolynomialVacuumBridge.Corridor.turnUnits_append]
    cases b <;> simp [PolynomialVacuumBridge.Corridor.turnUnits,PolynomialVacuumBridge.Corridor.turnUnit] at hr ⊢ <;> omega
  change -3≤PolynomialVacuumBridge.Corridor.turnUnits walk ∧ PolynomialVacuumBridge.Corridor.turnUnits walk≤3 at hturn
  rw [hsum] at hturn
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hturn <;> omega

end PolynomialVacuumCylinder

end OAI
