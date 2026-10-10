import OAI.GroupTheory.PolycyclicRecognition.Algebra.EnvelopingTruncation
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace OAI

/-! # The finite truncated enveloping algebra and its faithful generators

A given nilpotent representation bounds the truncation degree and certifies
injectivity. No PBW theorem or additional representation input is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "η" => UniversalEnvelopingAlgebra.ι R (L := L)

abbrev TruncatedEnvelopingAlgebra (R L : Type*) [CommRing R] [LieRing L]
    [LieAlgebra R L] (c : ℕ) :=
  (envelopingTruncationIdeal (R := R) (L := L) c).ringCon.Quotient

def truncatedEnvelopingProjection (c : ℕ) : U →ₐ[R] TruncatedEnvelopingAlgebra R L c :=
  RingCon.mkₐ R (envelopingTruncationIdeal (R := R) (L := L) c).ringCon

def truncatedEnvelopingGenerator (c : ℕ) : L →ₗ⁅R⁆ TruncatedEnvelopingAlgebra R L c :=
  ((truncatedEnvelopingProjection (R := R) (L := L) c).toLieHom).comp η

theorem truncatedEnvelopingProjection_surjective (c : ℕ) :
    Function.Surjective (truncatedEnvelopingProjection (R := R) (L := L) c) :=
  RingCon.mkₐ_surjective _

theorem truncatedEnvelopingProjection_eq_zero (c : ℕ) (u : U) :
    truncatedEnvelopingProjection c u = 0 ↔ u ∈ envelopingTruncationIdeal (R := R) c :=
  RingCon.eq _

theorem truncatedEnvelopingGenerator_prod_eq_zero (c : ℕ) (l : List L)
    (hl : c ≤ l.length) : (l.map (truncatedEnvelopingGenerator (R := R) c)).prod = 0 := by
  have h := (truncatedEnvelopingProjection_eq_zero c _).mpr
    (longWord_mem_envelopingTruncationIdeal (R := R) c l hl)
  simpa only [map_list_prod, List.map_map, Function.comp_def,
    truncatedEnvelopingGenerator, LieHom.coe_comp, AlgHom.coe_toLieHom] using h

theorem truncatedEnveloping_adjoin_basis {ι : Type*} [Fintype ι]
    (b : Basis ι R L) (c : ℕ) :
    Algebra.adjoin R (Set.range fun i => truncatedEnvelopingGenerator (R := R) c (b i)) = ⊤ := by
  classical
  let S := Algebra.adjoin R
    (Set.range fun i => truncatedEnvelopingGenerator (R := R) c (b i))
  have hgen (x : L) : truncatedEnvelopingGenerator (R := R) c x ∈ S := by
    rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
    apply S.sum_mem
    intro i _
    apply S.smul_mem
    exact Algebra.subset_adjoin (s := Set.range fun i =>
      truncatedEnvelopingGenerator (R := R) c (b i)) ⟨i, rfl⟩
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨u, rfl⟩ := truncatedEnvelopingProjection_surjective (R := R) (L := L) c z
  induction u using enveloping_induction with
  | hscalar r => exact S.algebraMap_mem r
  | hgen x => exact hgen x
  | hadd a b ha hb => exact S.add_mem ha hb
  | hmul a b ha hb => exact S.mul_mem ha hb

theorem truncatedEnvelopingGenerator_injective {A : Type*} [Ring A] [Algebra R A]
    (c : ℕ) (j : L →ₗ⁅R⁆ A) (hj : Function.Injective j)
    (hnil : ∀ l : List L, c ≤ l.length → (l.map j).prod = 0) :
    Function.Injective (truncatedEnvelopingGenerator (R := R) (L := L) c) := by
  let f : U →ₐ[R] A := UniversalEnvelopingAlgebra.lift R j
  have hk {u : U} (hu : u ∈ envelopingTruncationIdeal (R := R) c) : f u = 0 := by
    induction hu using TwoSidedIdeal.span_induction with
    | mem u hu =>
      obtain ⟨l, hl, rfl⟩ := hu
      dsimp only [f]
      simpa only [map_list_prod, List.map_map, Function.comp_def,
        UniversalEnvelopingAlgebra.lift_ι_apply] using hnil l hl
    | zero => exact map_zero f
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | neg a _ ha => rw [map_neg, ha, neg_zero]
    | left_absorb a b _ hb => rw [map_mul, hb, mul_zero]
    | right_absorb b a _ ha => rw [map_mul, ha, zero_mul]
  intro x y hxy
  apply hj
  have hrel : (envelopingTruncationIdeal (R := R) c).ringCon (η x) (η y) :=
    (RingCon.eq _).mp hxy
  have hz := hk (((envelopingTruncationIdeal (R := R) c).rel_iff _ _).mp hrel)
  simpa only [map_sub, f, UniversalEnvelopingAlgebra.lift_ι_apply, sub_eq_zero] using hz

section FiniteDimensional
variable {K : Type*} [Field K] [LieAlgebra K L]

theorem finiteDimensional_truncatedEnvelopingAlgebra {ι : Type*} [Fintype ι]
    (b : Basis ι K L) (c : ℕ) : FiniteDimensional K (TruncatedEnvelopingAlgebra K L c) := by
  apply finiteDimensional_of_bounded_generator_products
    (fun i => truncatedEnvelopingGenerator (R := K) c (b i)) c
    (truncatedEnveloping_adjoin_basis b c)
  intro l hl
  have h := truncatedEnvelopingGenerator_prod_eq_zero (R := K) c (l.map b)
    (by simpa only [List.length_map] using hl.le)
  simpa only [List.map_map, Function.comp_def] using h

end FiniteDimensional
end PolycyclicRecognition

end

end OAI
