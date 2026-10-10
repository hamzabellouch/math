import OAI.LinearAlgebra.MatrixMultiplication.Duality.ProgramIndependence
import OAI.LinearAlgebra.MatrixMultiplication.Completion.ProgramPrefixes
import OAI.LinearAlgebra.MatrixMultiplication.Completion.TerminationLaw
import OAI.LinearAlgebra.MatrixMultiplication.Duality.InformationTransport

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

open MatrixMultiplication.Foundation CompletionLabels CompletionLabels.TopologicalFlatten
open CompletionColorLaws DualInformation DualInformationTransport
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

universe u w
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]
  {Code : Type w} [Fintype Code] [Inhabited Code] {depth : ℕ}

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] in
theorem termination_label_succ (S : FlaggedTensor X Y Z) (first second : Color)
    (hne : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (hcontext : ∀ a, p.context a = leafColor S a)
    (hview : ∀ c a, p.view c a = coordinate a.val c)
    (k : ℕ) (a : RetainedLeaf S first second) :
    (terminationProgram S first second hne p hcontext hview).labels (1 + k) a =
      Sum.inr (p.labels k a.val) := by
  exact Program.append_labels_right _ _ _ _ _ k a

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] in
theorem termination_pair_succ (S : FlaggedTensor X Y Z) (first second : Color)
    (hne : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (hcontext : ∀ a, p.context a = leafColor S a)
    (hview : ∀ c a, p.view c a = coordinate a.val c) (k : ℕ) :
    (terminationProgram S first second hne p hcontext hview).pair (1 + k) = p.pair k := by
  simp [terminationProgram, Program.append, Program.recode, terminationInherited,
    Program.pullback]

omit [Fintype X] [Fintype Y] [Fintype Z] [Fintype Code] in
theorem termination_record_eq_iff (S : FlaggedTensor X Y Z) (first second : Color)
    (hne : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (hcontext : ∀ a, p.context a = leafColor S a)
    (hview : ∀ c a, p.view c a = coordinate a.val c)
    (k : ℕ) (a b : RetainedLeaf S first second) :
    labelRecordOf (terminationProgram S first second hne p hcontext hview).labels (1 + k) a =
        labelRecordOf (terminationProgram S first second hne p hcontext hview).labels (1 + k) b ↔
      leafColor S a.val = leafColor S b.val ∧
        labelRecordOf p.labels k a.val = labelRecordOf p.labels k b.val := by
  trans
    (labelRecordOf (terminationRoot S first second hne).labels 1 a =
      labelRecordOf (terminationRoot S first second hne).labels 1 b ∧
      labelRecordOf (terminationInherited S first second p hview).labels k a =
        labelRecordOf (terminationInherited S first second p hview).labels k b)
  · exact (Program.append_record_eq_iff _ _ _ _ _ k a b).trans
      (and_congr
        (Program.recode_record_eq_iff _ _ _ _ 1 a b)
        (Program.recode_record_eq_iff _ _ _ _ k a b))
  simp only [terminationRoot, Program.single, labelRecordOf,
    terminationInherited, Program.pullback]
  have hpull (v : RetainedLeaf S first second) :
      labelRecordOf (fun n (b : RetainedLeaf S first second) => p.labels n b.val) k v =
        labelRecordOf p.labels k v.val := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [labelRecordOf, ih]; rfl
  rw [hpull a, hpull b]
  constructor
  · rintro ⟨he, hr⟩
    exact ⟨congrArg Prod.snd he, hr⟩
  · rintro ⟨he, hr⟩
    refine ⟨?_, hr⟩
    rw [he]

theorem termination_factorization (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : ∀ c, FiniteLaw (ColorSlice S c)) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (h : ProgramLawsIndependent S r p) (k : Fin r.depth)
    (hk : r.program.pair k.val = .yz) :
    ConditionalMassFactorization
      (CompletionTerminationLaw.law S .B .C (p .B) (p .C) a ha ha')
      (labelRecordOf (terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels (1 + k.val))
      ((terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels (1 + k.val))
      (fun w => w.val.val.1) := by
  let μ := CompletionTerminationLaw.law S .B .C (p .B) (p .C) a ha ha'
  let q := colorMix S .B .C (p .B) (p .C) a ha ha'
  let prior := labelRecordOf r.program.labels k.val
  let label := r.program.labels k.val
  let xx : Leaf S → X := fun w => w.val.1
  have hq : ConditionalMassFactorization q (fun w => (leafColor S w, prior w)) label xx :=
    colorMix_factorization S .B .C (by intro h; cases h) (p .B) (p .C) a ha ha'
      prior label xx (h .B k hk) (h .C k hk)
  have hmass : (μ.map Subtype.val).mass = q.mass := by
    funext w
    exact (CompletionTerminationLaw.law_map_mass S .B .C (p .B) (p .C)
      a ha ha' id w).trans (q.map_mass_apply id Function.injective_id w)
  have hmapped : ConditionalMassFactorization (μ.map Subtype.val)
      (fun w => (leafColor S w, prior w)) label xx :=
    (mass_factorization_congr_mass_iff (μ.map Subtype.val) q hmass _ _ _).mpr hq
  have hμ := (mass_factorization_map_iff μ Subtype.val
    (fun w => (leafColor S w, prior w)) label xx).mp hmapped
  apply mass_factorization_of_same_partitions μ
    (fun w => (leafColor S w.val, prior w.val))
    (fun w => label w.val) (fun w => xx w.val)
    (labelRecordOf (terminationProgram S .B .C (by intro h; cases h)
      r.program r.context_eq r.view_eq).labels (1 + k.val))
    ((terminationProgram S .B .C (by intro h; cases h)
      r.program r.context_eq r.view_eq).labels (1 + k.val))
    (fun w => w.val.val.1) ?_ ?_ ?_ hμ
  · intro u v
    simp only [Prod.mk.injEq]
    exact (termination_record_eq_iff S .B .C (by intro h; cases h)
      r.program r.context_eq r.view_eq k.val u v).symm
  · intro u v
    simp only [termination_label_succ, Sum.inr.injEq]
    rfl
  · intro u v
    rfl

theorem termination_independent (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : ∀ c, FiniteLaw (ColorSlice S c)) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (h : ProgramLawsIndependent S r p)
    (n : Fin (1 + r.depth))
    (hn : (terminationProgram S .B .C (by intro h; cases h)
      r.program r.context_eq r.view_eq).pair n.val = .yz) :
    ConditionalIndependent
      (CompletionTerminationLaw.law S .B .C (p .B) (p .C) a ha ha')
      (labelRecordOf (terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels n.val)
      ((terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels n.val)
      (fun w => w.val.val.1) := by
  rcases n with ⟨n, hnd⟩
  cases n with
  | zero =>
      simp [terminationProgram, Program.append, Program.recode,
        terminationRoot, Program.single, ownerPair] at hn
  | succ k =>
      have hkd : k < r.depth := Nat.lt_of_succ_lt_succ
        (by simpa only [Nat.one_add] using hnd)
      simp only [Fin.val_mk] at hn ⊢
      simp only [Nat.add_comm k 1] at hn
      have hk : r.program.pair k = .yz :=
        (termination_pair_succ S .B .C (by intro h; cases h)
          r.program r.context_eq r.view_eq k).symm.trans hn
      apply conditionalIndependent_of_mass_factorization
      let labels := (terminationProgram S .B .C (by intro h; cases h)
        r.program r.context_eq r.view_eq).labels
      have hf := termination_factorization S r p a ha ha' h ⟨k, hkd⟩ hk
      exact Eq.mp
        (congrArg
          (fun n : ℕ => ConditionalMassFactorization
            (CompletionTerminationLaw.law S .B .C (p .B) (p .C) a ha ha')
            (labelRecordOf labels n) (labels n) (fun w => w.val.val.1))
          (Nat.one_add k))
        hf

end MatrixMultiplication.DualProgramIndependence

end

end OAI
