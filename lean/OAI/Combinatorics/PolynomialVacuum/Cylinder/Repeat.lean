import OAI.Combinatorics.PolynomialVacuum.Cylinder.Lift

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}

def repeatWord (w : List Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => repeatWord w n++w

@[simp] theorem terminal_repeat (g : PlaneGerm) (w : List Bool) (d : ℤ)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm g w=translateGerm d g) (n : ℕ) :
    PolynomialVacuumBridge.Corridor.terminalGerm g (repeatWord w n)=translateGerm ((n : ℤ)*d) g := by
  induction n with
  | zero => simp [repeatWord,PolynomialVacuumBridge.Corridor.terminalGerm]
  | succ n ih =>
    rw [repeatWord,PolynomialVacuumBridge.Corridor.terminalGerm_append,ih,← translate_terminal,hc,translateGerm_add]
    congr 1
    push_cast
    ring

theorem traced_repeat (g : PlaneGerm) (w : List Bool) (d : ℤ)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm g w=translateGerm d g) (n : ℕ) :
    PolynomialVacuumBridge.Corridor.traced g (repeatWord w n)=
      (List.range n).flatMap (fun (k : ℕ) => (PolynomialVacuumBridge.Corridor.traced g w).map (translateVertex ((k : ℤ)*d))) := by
  induction n with
  | zero => simp [repeatWord,PolynomialVacuumBridge.Corridor.traced]
  | succ n ih =>
    simp only [repeatWord,PolynomialVacuumBridge.Corridor.traced_append,ih,terminal_repeat _ _ _ hc,
      List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [translate_traced]

theorem traced_project_injective (g : PlaneGerm) (w : List Bool)
    (hN : (traced (projectGerm M g) w).Nodup) :
    Set.InjOn (projectVertex M) {v | v∈PolynomialVacuumBridge.Corridor.traced g w} := by
  have hm : ((PolynomialVacuumBridge.Corridor.traced g w).map (projectVertex M)).Nodup := by simpa using hN
  exact (List.nodup_map_iff_inj_on hm.of_map).mp hm

theorem translated_trace_disjoint (g : PlaneGerm) (w : List Bool) (d : ℤ)
    (hd : (d : ZMod M)=0) (hd0 : d≠0)
    (hN : (traced (projectGerm M g) w).Nodup) (k l : ℕ) (hkl : k≠l) :
    List.Disjoint ((PolynomialVacuumBridge.Corridor.traced g w).map (translateVertex ((k : ℤ)*d)))
      ((PolynomialVacuumBridge.Corridor.traced g w).map (translateVertex ((l : ℤ)*d))) := by
  intro v hv hu
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
  obtain ⟨b,hb,he⟩ := List.mem_map.mp hu
  have he' := congrArg (projectVertex M) he
  have hk : (((k : ℤ)*d : ℤ) : ZMod M)=0 := by simp [hd]
  have hl : (((l : ℤ)*d : ℤ) : ZMod M)=0 := by simp [hd]
  rw [project_translate _ hl,project_translate _ hk] at he'
  have hab := traced_project_injective g w hN hb ha he'
  subst b
  have hmul := (translateVertex_cancel _ _ a).mp he
  have hcast : (l : ℤ)=(k : ℤ) := mul_right_cancel₀ hd0 hmul
  exact hkl (by omega)

theorem repeated_trace_nodup (g : PlaneGerm) (w : List Bool) (d : ℤ)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm g w=translateGerm d g)
    (hd : (d : ZMod M)=0) (hd0 : d≠0)
    (hN : (traced (projectGerm M g) w).Nodup) (n : ℕ) :
    (PolynomialVacuumBridge.Corridor.traced g (repeatWord w n)).Nodup := by
  have hp : (PolynomialVacuumBridge.Corridor.traced g w).Nodup := by
    apply List.Nodup.of_map (f:=projectVertex M)
    simpa using hN
  induction n with
  | zero => simp [repeatWord,PolynomialVacuumBridge.Corridor.traced]
  | succ n ih =>
    rw [repeatWord,PolynomialVacuumBridge.Corridor.traced_append,terminal_repeat _ _ _ hc,← translate_traced]
    apply List.nodup_append.mpr
    refine ⟨ih,hp.map (translateVertex_injective _),?_⟩
    intro v hv u hu he
    subst u
    rw [traced_repeat _ _ _ hc] at hv
    obtain ⟨k,hk,hkv⟩ := List.mem_flatMap.mp hv
    exact translated_trace_disjoint g w d hd hd0 hN k n (by simpa using Nat.ne_of_lt (List.mem_range.mp hk)) hkv hu

@[simp] theorem turnUnits_repeat (w : List Bool) (n : ℕ) :
    PolynomialVacuumBridge.Corridor.turnUnits (repeatWord w n)=(n : ℤ)*PolynomialVacuumBridge.Corridor.turnUnits w := by
  induction n with
  | zero => simp [repeatWord,PolynomialVacuumBridge.Corridor.turnUnits]
  | succ n ih => rw [repeatWord,PolynomialVacuumBridge.Corridor.turnUnits_append,ih]; push_cast; ring

end PolynomialVacuumCylinder

end OAI
