import OAI.Combinatorics.PolynomialVacuum.Cylinder.LowestRotation
import OAI.Combinatorics.PolynomialVacuum.Cylinder.BottomCalibration
import OAI.Combinatorics.PolynomialVacuum.Cylinder.Ends

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

theorem contractible_signed_turn (g : PlaneGerm) (w : List Bool) (ε : ℤ)
    (hne : w≠[]) (hc : PolynomialVacuumBridge.Corridor.terminalGerm g w=g)
    (hN : (traced (projectGerm M g) w).Nodup)
    (hvals : ∀ a, potential (wordFlow (projectGerm M g) w) a=0 ∨
      potential (wordFlow (projectGerm M g) w) a=ε) :
    PolynomialVacuumBridge.Corridor.turnUnits w=6*ε := by
  obtain ⟨u,z,b,i,j,rfl,hg,hH⟩ := exists_lowest_rotation g w 0 hne (by simpa using hc)
  have hclosed : terminalGerm (projectGerm M g) (u++b::z)=projectGerm M g := by rw [← project_terminal,hc]
  obtain ⟨hn',hc',hq⟩ := closed_word_rotate (projectGerm M g) u (b::z) hN hclosed
  have hpg : terminalGerm (projectGerm M g) u = projectGerm M (.up i j,if b then 2 else 1) := by rw [← project_terminal,hg]
  rw [hpg] at hn' hc' hq
  have hCc : PolynomialVacuumBridge.Corridor.terminalGerm (.up i j,if b then 2 else 1) (b::(z++u))=(.up i j,if b then 2 else 1) := by
    have hh := periodic_closed_rotate g u (b::z) 0 (by simpa using hc)
    simpa [hg] using hh
  have hNc : (PolynomialVacuumBridge.Corridor.traced (.up i j,if b then 2 else 1) (b::(z++u))).Nodup := by
    have hh : ((PolynomialVacuumBridge.Corridor.traced (.up i j,if b then 2 else 1) (b::(z++u))).map (projectVertex M)).Nodup := by
      simpa only [project_traced,List.cons_append] using hn'
    exact List.Nodup.of_map _ hh
  have he := bottom_cylinder_sign (M:=M) i j b (z++u) ε (by simpa using hc') (by simpa using hn') hH ?_
  · have ht := bottom_contractible_turn i j b (z++u) hCc hNc hH
    rw [← he] at ht
    simp only [PolynomialVacuumBridge.Corridor.turnUnits_append] at ht ⊢
    simp only [PolynomialVacuumBridge.Corridor.turnUnits,List.map_cons,List.sum_cons,List.map_append,List.sum_append] at ht ⊢
    omega
  · intro a
    have hv := hvals a
    have hq' : wordFlow (projectGerm M (.up i j,if b then 2 else 1)) (b::(z++u))=wordFlow (projectGerm M g) (u++b::z) := by simpa only [List.cons_append] using hq
    simpa only [hq'] using hv

 

theorem cylinder_turn_and_winding [NeZero M] (g : PlaneGerm) (w : List Bool)
    (hne : w≠[]) (hN : (traced (projectGerm M g) w).Nodup)
    (hc : terminalGerm (projectGerm M g) w=projectGerm M g) :
    ∃ (ε d : ℤ), (ε=1 ∨ ε = -1) ∧
      (∀ a, potential (wordFlow (projectGerm M g) w) a=0 ∨ potential (wordFlow (projectGerm M g) w) a=ε) ∧
      PolynomialVacuumBridge.Corridor.terminalGerm g w=translateGerm d g ∧
      ((d=0 ∧ topValue (wordFlow (projectGerm M g) w)=0 ∧ PolynomialVacuumBridge.Corridor.turnUnits w=6*ε) ∨
       (d=(M : ℤ)*ε ∧ topValue (wordFlow (projectGerm M g) w)=ε ∧ PolynomialVacuumBridge.Corridor.turnUnits w=0)) := by
  obtain ⟨ε,hε,hvals⟩ := simple_closed_word_indicator _ w hne hN hc
  obtain ⟨d,hd,hD⟩ := closure_is_translate g w hc
  refine ⟨ε,d,hε,hvals,hD,?_⟩
  have hw := winding_eq_topValue g w d hD hd
  have hM : (M : ℤ)≠0 := by exact_mod_cast NeZero.ne M
  by_cases hd0 : d=0
  · left
    have hu : topValue (wordFlow (projectGerm M g) w)=0 := (mul_eq_zero.mp (hw.symm.trans hd0)).resolve_left hM
    refine ⟨hd0,hu,contractible_signed_turn g w ε hne ?_ hN hvals⟩
    simpa [hd0] using hD
  · right
    have hu : topValue (wordFlow (projectGerm M g) w)=ε := by
      have h := hvals (0,(flowRadius (wordFlow (projectGerm M g) w) : ℤ)+1)
      change topValue (wordFlow (projectGerm M g) w)=0 ∨ topValue (wordFlow (projectGerm M g) w)=ε at h
      exact h.resolve_left (by intro hz; rw [hz,mul_zero] at hw; exact hd0 hw)
    exact ⟨hw.trans (congrArg ((M : ℤ)* ·) hu),hu,periodic_turn_zero g w d hne hD hd hd0 hN⟩

end PolynomialVacuumCylinder

end OAI
