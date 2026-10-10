import OAI.Probability.DilutedSpin.ScheduledTopology

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- Before its first scheduled branching, the realized topology is exactly
an initial unary stem; all later vertex assignments are unchanged. -/
lemma realize_stem (n r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d+r ≤ q v) :
    realize (n+r) d S q = PrescribedTree.stem (realize n (d+r) S q) r := by
  induction r generalizing d with
  | zero => rfl
  | succ r ih =>
    have hh : ∀ v, d+1+r ≤ q v := by intro v; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq v
    cases S with
    | leaf =>
      change PrescribedTree.unary (realize (n+r) (d+1) leaf q) =
        PrescribedTree.unary (PrescribedTree.stem (realize n (d+(r+1)) leaf q) r)
      congr 1
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (d+1) hh
    | node k hk C =>
      have hd : d<q none := by have := hq none; omega
      change realize (n+r+1) d (node k hk C) q = _
      rw [realize,ite_eq_left hd]
      change PrescribedTree.unary _ = PrescribedTree.unary _
      apply congrArg PrescribedTree.unary
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (d+1) hh

/-- One assigned branching coordinate and all its later child coordinates. -/
def rootSchedule {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (t : ℕ) (Q : (i : Fin k) → (C i).Vertex → ℕ) : (node k hk C).Vertex → ℕ :=
  fun v => match v with
  | none => t
  | some a => Q a.1 a.2

/-- The realized topology with one ranged root depth is the literal
split family, not just an isomorphic unordered or unlabeled tree. -/
theorem realize_splitFamily (k : ℕ+) (hk : 2 ≤ (k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : (i : Fin k) → (C i).Vertex → ℕ) (n r d : ℕ)
    (hQ : ∀ i v, d+r+1 ≤ Q i v) (t : Fin (r+1)) :
    realize (n+r+1) d (node k hk C) (rootSchedule (d+t.val) Q) =
      PrescribedTree.splitFamily k (fun i => realize n (d+r+1) (C i) (Q i)) r t := by
  induction r generalizing d with
  | zero =>
    have ht : t=0 := Fin.eq_zero t
    subst t
    simp only [Nat.add_zero,Fin.val_zero,realize,rootSchedule,lt_self_iff_false,
      ite_false,PrescribedTree.splitFamily]
  | succ r ih =>
    refine Fin.cases ?_ (fun t => ?_) t
    · rw [PrescribedTree.splitFamily_zero]
      simp only [Fin.val_zero,Nat.add_zero,realize,rootSchedule,lt_self_iff_false,
        ite_false]
      congr 1
      funext i
      have hh := realize_stem n (r+1) (d+1) (C i) (Q i) (by
        intro v
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hQ i v)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    · rw [PrescribedTree.splitFamily_succ]
      have hd : d<d+t.succ.val := by simp only [Fin.val_succ]; omega
      rw [realize]
      change (if d<d+t.succ.val then _ else _) = _
      rw [ite_eq_left hd]
      apply congrArg PrescribedTree.unary
      have hh := ih (d+1) (by
        intro i v
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hQ i v) t
      convert hh using 1 <;> simp only [Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
      rfl

/-- Genuine one-coordinate energy bound for a scheduled reduced topology.
Every descendant depth is held fixed while the current branching depth is
ranged over the full available interval. All transition kernels are arbitrary. -/
theorem scheduled_split_energy_le (k : ℕ+) (hk : 2 ≤ (k:ℕ)) (C : Fin k → ReducedTopology)
    (Q : (i : Fin k) → (C i).Vertex → ℕ) (n r d : ℕ)
    (hQ : ∀ i v, d+r+1 ≤ Q i v)
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    (∑ t : Fin r,
      (PrescribedTree.treeMean
        (realize (n+r+1) d (node k hk C) (rootSchedule (d+t.val) Q)) T f -
       PrescribedTree.treeMean
        (realize (n+r+1) d (node k hk C) (rootSchedule (d+t.val+1) Q)) T f)^2) ≤ (k:ℝ)^2 := by
  have h := PrescribedTree.splitShiftEnergy_le k
    (fun i => realize n (d+r+1) (C i) (Q i)) r T f hf
  unfold PrescribedTree.splitShiftEnergy at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro t _
  congr 2
  · exact congrArg (fun S => PrescribedTree.treeMean S T f)
      (realize_splitFamily k hk C Q n r d hQ t.castSucc)
  · have he := realize_splitFamily k hk C Q n r d hQ t.succ
    simpa only [Fin.val_succ,Nat.add_assoc] using congrArg (fun S => PrescribedTree.treeMean S T f) he

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
