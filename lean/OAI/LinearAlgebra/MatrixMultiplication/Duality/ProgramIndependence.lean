import OAI.LinearAlgebra.MatrixMultiplication.Duality.Information
import OAI.LinearAlgebra.MatrixMultiplication.Completion.ColorLaws
import OAI.LinearAlgebra.MatrixMultiplication.Duality.UniformProducts

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u v w z

open MatrixMultiplication.Foundation DualInformation CompletionProductLaws
open CompletionColorLaws CompletionLabels RecursiveCompletion DualEntropyHelpers
open DualUniformProducts
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type u} {R : I → Type v} {L : I → Type w} {X : I → Type z}
  [∀ i, Fintype (A i)] [∀ i, Fintype (R i)]
  [∀ i, Fintype (L i)] [∀ i, Fintype (X i)]

theorem independentProduct_triple_mass
    (p : ∀ i, FiniteLaw (A i)) (prior : ∀ i, A i → R i)
    (label : ∀ i, A i → L i) (x : ∀ i, A i → X i)
    (r : ∀ i, R i) (l : ∀ i, L i) (xx : ∀ i, X i) :
    ((independentProduct p).map (fun a => ((fun i => prior i (a i)),
      ((fun i => label i (a i)), (fun i => x i (a i)))))).mass (r, (l, xx)) =
      ∏ i, ((p i).map (fun a => (prior i a, (label i a, x i a)))).mass
        (r i, (l i, xx i)) := by
  rw [← independentProduct_map_mass p
    (fun i a => (prior i a, (label i a, x i a)))
    (fun i => (r i, (l i, xx i)))]
  simp only [FiniteLaw.map_mass]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Prod.mk.injEq, funext_iff, forall_and]

theorem independentProduct_factorization
    (p : ∀ i, FiniteLaw (A i)) (prior : ∀ i, A i → R i)
    (label : ∀ i, A i → L i) (x : ∀ i, A i → X i)
    (h : ∀ i, ConditionalMassFactorization (p i) (prior i) (label i) (x i)) :
    ConditionalMassFactorization (independentProduct p)
      (fun a i => prior i (a i)) (fun a i => label i (a i))
      (fun a i => x i (a i)) := by
  intro r l xx
  rw [independentProduct_triple_mass p prior label x r l xx,
    independentProduct_map_mass p prior r,
    independentProduct_joint_mass p prior label r l,
    independentProduct_joint_mass p prior x r xx,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact h i (r i) (l i) (xx i)

section Constant

variable {B : Type u} {P : Type v} {C : Type w} {Y : Type z}
  [Fintype B] [Fintype P] [Fintype C] [Fintype Y]

theorem factorization_constant_label (p : FiniteLaw B) (prior : B → P)
    (c : C) (x : B → Y) :
    ConditionalMassFactorization p prior (fun _ => c) x := by
  intro r l xx
  by_cases h : c = l
  · subst l
    simp only [FiniteLaw.map_mass, Prod.mk.injEq, true_and, and_true]
    ring
  · simp only [FiniteLaw.map_mass, Prod.mk.injEq, h, false_and, and_false,
      ite_false, Finset.sum_const_zero, zero_mul]

end Constant

section ColorMixture

variable {SX SY SZ : Type u} {P : Type v} {C : Type w} {V : Type z}
  [Fintype SX] [Fintype SY] [Fintype SZ]
  [Fintype P] [Fintype C] [Fintype V]

theorem colorSlice_context_mass (S : FlaggedTensor SX SY SZ) (color c : Color)
    (p : FiniteLaw (ColorSlice S color)) (f : Leaf S → V) (v : V) :
    ((p.map Subtype.val).map (fun a => (leafColor S a, f a))).mass (c, v) =
      if color = c then (p.map (fun a => f a.val)).mass v else 0 := by
  rw [map_comp_mass]
  simp only [FiniteLaw.map_mass, Prod.mk.injEq]
  by_cases h : color = c
  · simp only [show ∀ a : ColorSlice S color, leafColor S a.val = color from
      fun a => a.property, h, true_and, ite_true]
  · simp only [show ∀ a : ColorSlice S color, leafColor S a.val = color from
      fun a => a.property, h, false_and, ite_false, Finset.sum_const_zero]

theorem colorMix_context_mass (S : FlaggedTensor SX SY SZ) (center output c : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (f : Leaf S → V) (v : V) :
    ((colorMix S center output pc po α hα hα').map
      (fun a => (leafColor S a, f a))).mass (c, v) =
      α * (if center = c then (pc.map (fun a => f a.val)).mass v else 0) +
        (1 - α) * (if output = c then (po.map (fun a => f a.val)).mass v else 0) := by
  rw [colorMix_map_mass, colorSlice_context_mass, colorSlice_context_mass]

theorem colorMix_refined_context_mass (S : FlaggedTensor SX SY SZ)
    (center output c : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1)
    (prior : Leaf S → P) (f : Leaf S → V) (r : P) (v : V) :
    ((colorMix S center output pc po α hα hα').map
      (fun a => ((leafColor S a, prior a), f a))).mass ((c, r), v) =
      α * (if center = c then
        (pc.map (fun a => (prior a.val, f a.val))).mass (r, v) else 0) +
        (1 - α) * (if output = c then
          (po.map (fun a => (prior a.val, f a.val))).mass (r, v) else 0) := by
  rw [← colorMix_context_mass S center output c pc po α hα hα'
    (fun a => (prior a, f a)) (r, v)]
  simp only [FiniteLaw.map_mass, Prod.mk.injEq, and_assoc]

theorem colorMix_factorization (S : FlaggedTensor SX SY SZ) (center output : Color)
    (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1)
    (prior : Leaf S → P) (label : Leaf S → C) (x : Leaf S → V)
    (hc : ConditionalMassFactorization pc (fun a => prior a.val)
      (fun a => label a.val) (fun a => x a.val))
    (ho : ConditionalMassFactorization po (fun a => prior a.val)
      (fun a => label a.val) (fun a => x a.val)) :
    ConditionalMassFactorization (colorMix S center output pc po α hα hα')
      (fun a => (leafColor S a, prior a)) label x := by
  rintro ⟨c, r⟩ l xx
  rw [colorMix_refined_context_mass, colorMix_context_mass,
    colorMix_refined_context_mass, colorMix_refined_context_mass]
  by_cases hcc : center = c
  · subst c
    have hoc : output ≠ center := Ne.symm hne
    simp only [ite_true, ite_eq_right hoc, mul_zero, add_zero]
    calc
      _ = α ^ 2 *
          ((pc.map (fun a => (prior a.val, (label a.val, x a.val)))).mass (r, (l, xx)) *
            (pc.map (fun a => prior a.val)).mass r) := by ring
      _ = _ := by rw [hc r l xx]; ring
  · by_cases hoc : output = c
    · subst c
      simp only [ite_eq_right hne, ite_true, mul_zero, zero_add]
      calc
        _ = (1 - α) ^ 2 *
            ((po.map (fun a => (prior a.val, (label a.val, x a.val)))).mass (r, (l, xx)) *
              (po.map (fun a => prior a.val)).mass r) := by ring
        _ = _ := by rw [ho r l xx]; ring
    · simp only [ite_eq_right hcc, ite_eq_right hoc, mul_zero, zero_add]

theorem colorMix_recorded_factorization (S : FlaggedTensor SX SY SZ)
    (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (hbranch : center ≠ output ∨ α = 0)
    (prior : Leaf S → P) (label : Leaf S → C) (x : Leaf S → V)
    (hc : ConditionalMassFactorization pc (fun a => prior a.val)
      (fun a => label a.val) (fun a => x a.val))
    (ho : ConditionalMassFactorization po (fun a => prior a.val)
      (fun a => label a.val) (fun a => x a.val)) :
    ConditionalMassFactorization (colorMix S center output pc po α hα hα')
      (fun a => (leafColor S a, prior a)) label x := by
  rcases hbranch with hne | hz
  · exact colorMix_factorization S center output hne pc po α hα hα' prior label x hc ho
  · subst α
    rintro ⟨c, r⟩ l xx
    rw [colorMix_refined_context_mass, colorMix_context_mass,
      colorMix_refined_context_mass, colorMix_refined_context_mass]
    by_cases hoc : output = c
    · simp only [zero_mul, zero_add, sub_zero, one_mul, ite_eq_left hoc]
      exact ho r l xx
    · simp only [zero_mul, zero_add, sub_zero, one_mul, ite_eq_right hoc]

end ColorMixture

section ProgramInvariant

variable {SX SY SZ : Type u} [Fintype SX] [Fintype SY] [Fintype SZ]

def ProgramLawsIndependent (S : FlaggedTensor SX SY SZ) (r : ReadableTensor S)
    (p : ∀ c, FiniteLaw (ColorSlice S c)) : Prop :=
  ∀ c, ∀ n : Fin r.depth, r.program.pair n.val = .yz →
    ConditionalMassFactorization (p c)
      (fun a => labelRecordOf r.program.labels n.val a.val)
      (fun a => r.program.labels n.val a.val)
      (fun a => a.val.val.1)

end ProgramInvariant

end MatrixMultiplication.DualProgramIndependence

end

end OAI
