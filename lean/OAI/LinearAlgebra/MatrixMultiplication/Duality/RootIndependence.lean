import OAI.LinearAlgebra.MatrixMultiplication.Duality.CompletionIndependence
import OAI.LinearAlgebra.MatrixMultiplication.Duality.InformationLabelConditioning
import OAI.LinearAlgebra.MatrixMultiplication.Duality.UniformMixtures

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u w

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionColorLaws CompletionProductLaws DualUniformProducts
open DualInformation DualInformationTransport DualUniformMixtures TopologicalFlatten
open scoped BigOperators
theorem rootColor_inj_before_three {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    rootColor i = rootColor j ↔ i = j := by
  interval_cases i <;> interval_cases j <;> simp [rootColor]

private theorem completion_index_decomposition {n m depth : ℕ}
    (hn : n < 3 + m * depth) (hn3 : ¬ n < 3) :
    0 < depth ∧ n - 3 < m * depth ∧
      n = 3 + ((n - 3) / depth * depth + (n - 3) % depth) := by
  have hd : 0 < depth := by
    by_contra h
    have hz : depth = 0 := by omega
    simp only [hz, mul_zero, add_zero] at hn
    omega
  refine ⟨hd, by omega, ?_⟩
  have h : (n - 3) / depth * depth + (n - 3) % depth = n - 3 := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod (n - 3) depth
  omega

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} {Code : Type w} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype Code] [Inhabited Code] {depth m : ℕ}

theorem conditionalCompletionLaw_pattern_factorization (S : FlaggedTensor X Y Z)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hm : 0 < m)
    (hcommon : ∀ x, (pc.map (fun a => a.val.val.1)).mass x =
      (po.map (fun a => a.val.val.1)).mass x) :
    ConditionalMassFactorization
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun _ => (PUnit.unit : PUnit.{1})) (fun a => pattern S center m a.val)
      (fun a => a.val.val.1) := by
  let mix := colorMix S center output pc po α hα hα'.le
  have hs (c : Color) (x : X) :
      (mix.map (fun a => (leafColor S a, a.val.1))).mass (c, x) =
        (mix.map (leafColor S)).mass c * (mix.map (fun a => a.val.1)).mass x := by
    have h := colorMix_independent_common S center output pc po α hα hα'.le
      (fun a => a.val.1) hcommon x c
    simpa only [FiniteLaw.map_mass, Prod.mk.injEq, and_comm, mul_comm] using h
  have hw : ConditionalMassFactorization (iidColorLaw S center output pc po m α hα hα'.le)
      (fun _ => (PUnit.unit : PUnit.{1})) (fun a j => leafColor S (a j)) (fun a j => (a j).val.1) := by
    apply (mass_factorization_const_iff _ _ _).mpr
    exact independentProduct_independent (fun _ : Fin m => mix)
      (fun _ => leafColor S) (fun _ a => a.val.1) (fun _ => hs)
  let Q : (Fin m → Color) → Prop := fun c =>
    raisedFlag center output (fun j => c j = output) ∧
      ∀ j, c j = center ∨ c j = output
  have hcondition := conditionalMassFactorization_condition_label
    (iidColorLaw S center output pc po m α hα hα'.le)
    (fun a j => leafColor S (a j)) (fun a j => (a j).val.1) Q
    (completionEvent_mass_pos S center output pc po m hm α hα hα') hw
  let e := conditionalLeafEquiv S center output m
  let q := condition (iidColorLaw S center output pc po m α hα hα'.le)
    (completionEvent S center output m)
    (completionEvent_mass_pos S center output pc po m hm α hα hα')
  have hslot (a : {w : Fin m → Leaf S // completionEvent S center output m w}) :
      slot S center m (e.symm a).val = a.val :=
    congrArg Subtype.val (e.apply_symm_apply a)
  change ConditionalMassFactorization (q.map e.symm) _ _ _
  rw [mass_factorization_map_iff]
  apply mass_factorization_of_same_partitions q (fun _ => (PUnit.unit : PUnit.{1}))
    (fun a j => leafColor S (a.val j)) (fun a j => (a.val j).val.1)
  · intro a b
    rfl
  · intro a b
    rfl
  · intro a b
    rfl
  · exact hcondition

theorem conditionalCompletionLaw_root_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hm : 0 < m)
    (n : ℕ) (hn : n < 3)
    (hcommon : ownerPair center output = .yz → ∀ x,
      (pc.map (fun a => a.val.val.1)).mass x =
        (po.map (fun a => a.val.val.1)).mass x)
    (hpair : (completionLocalProgram S center m p context_eq view_eq).pair n = .yz) :
    ConditionalMassFactorization
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => labelRecordOf
        (completionLocalProgram S center m p context_eq view_eq).labels n a.val)
      (fun a => (completionLocalProgram S center m p context_eq view_eq).labels n a.val)
      (fun a => a.val.val.1) := by
  let law := conditionalCompletionLaw S center output pc po m hm α hα hα'
  let cp := completionLocalProgram S center m p context_eq view_eq
  have hroot (j : ℕ) (hj : j < 3) (a : ColorSlice (complete S center m) output) :
      cp.labels j a.val = encodePattern
        (if output = rootColor j then some (pattern S center m a.val) else none) := by
    rw [completionLocalProgram_label_root S center m p context_eq view_eq j hj, a.property]
    split_ifs <;> rfl
  by_cases hactive : output = rootColor n
  · have hp : ownerPair center output = .yz := by
      rw [completionLocalProgram_pair_root S center m p context_eq view_eq n hn,
        ← hactive] at hpair
      exact hpair
    have hprev (a b : ColorSlice (complete S center m) output) :
        labelRecordOf cp.labels n a.val = labelRecordOf cp.labels n b.val := by
      apply (labelRecordOf_eq_iff _ _ _ _).mpr
      intro j hj
      have hj3 : j < 3 := lt_trans hj hn
      have hne : output ≠ rootColor j := by
        intro he
        have hnj : n = j := (rootColor_inj_before_three hn hj3).mp (hactive.symm.trans he)
        exact (Nat.ne_of_lt hj) hnj.symm
      rw [hroot j hj3 a, hroot j hj3 b, ite_eq_right hne, ite_eq_right hne]
    apply mass_factorization_of_same_partitions law (fun _ => (PUnit.unit : PUnit.{1}))
      (fun a => pattern S center m a.val) (fun a => a.val.val.1)
    · intro a b
      exact iff_of_true rfl (hprev a b)
    · intro a b
      rw [hroot n hn a, hroot n hn b, ite_eq_left hactive, ite_eq_left hactive]
      simp only [encodePattern, Option.some.injEq, Sum.inl.injEq]
    · intro a b
      rfl
    · exact conditionalCompletionLaw_pattern_factorization S center output pc po α hα hα' hm
        (hcommon hp)
  · have hlabel : (fun a : ColorSlice (complete S center m) output => cp.labels n a.val) =
        (fun _ => encodePattern (Code := Code) none) := by
      funext a
      rw [hroot n hn a, ite_eq_right hactive]
    change ConditionalMassFactorization law _ _ _
    rw [hlabel]
    exact factorization_constant_label law _ _ _

theorem conditionalCompletionLaw_program_factorization (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (hbranch : center ≠ output ∨ α = 0)
    (hm : 0 < m)
    (hcommon : ownerPair center output = .yz → ∀ x,
      (pc.map (fun a => a.val.val.1)).mass x =
        (po.map (fun a => a.val.val.1)).mass x)
    (hc : ∀ n : Fin depth, p.pair n.val = .yz →
      ConditionalMassFactorization pc (fun a => labelRecordOf p.labels n.val a.val)
        (fun a => p.labels n.val a.val) (fun a => a.val.val.1))
    (ho : ∀ n : Fin depth, p.pair n.val = .yz →
      ConditionalMassFactorization po (fun a => labelRecordOf p.labels n.val a.val)
        (fun a => p.labels n.val a.val) (fun a => a.val.val.1))
    (n : Fin (3 + m * depth))
    (hpair : (completionLocalProgram S center m p context_eq view_eq).pair n.val = .yz) :
    ConditionalMassFactorization
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => labelRecordOf
        (completionLocalProgram S center m p context_eq view_eq).labels n.val a.val)
      (fun a => (completionLocalProgram S center m p context_eq view_eq).labels n.val a.val)
      (fun a => a.val.val.1) := by
  by_cases hn : n.val < 3
  · exact conditionalCompletionLaw_root_factorization S p context_eq view_eq
      center output pc po α hα hα' hm n.val hn hcommon hpair
  · obtain ⟨hd, hnm, hdecomp⟩ := completion_index_decomposition n.isLt hn
    let i : Fin m := ⟨(n.val - 3) / depth, (Nat.div_lt_iff_lt_mul hd).mpr hnm⟩
    let k : ℕ := (n.val - 3) % depth
    have hk : k < depth := Nat.mod_lt _ hd
    have hsplit : n.val = 3 + (i.val * depth + k) := hdecomp
    rw [hsplit, completionLocalProgram_pair_slot S center m p context_eq view_eq i k hk] at hpair
    apply mass_factorization_of_same_partitions
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => labelRecordOf
        (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a.val)
      (fun a => (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a.val)
      (fun a => a.val.val.1)
    · intro a b
      simp only [labelRecordOf_eq_iff, ← hsplit]
    · intro a b
      simp only [← hsplit]
    · intro a b
      rfl
    · exact conditionalCompletionLaw_inherited_factorization
        S p context_eq view_eq center output pc po α hα hα' hbranch hm i k hk
          (hc ⟨k, hk⟩ hpair) (ho ⟨k, hk⟩ hpair)

end MatrixMultiplication.DualProgramIndependence

end

end OAI
