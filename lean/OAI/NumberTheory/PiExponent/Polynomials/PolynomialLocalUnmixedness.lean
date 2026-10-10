import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalUnmixedness

section RegularPair
variable {S : Type*} [CommRing S]

def pairRelation (f g : S) : (S × S) →ₗ[S] S where
  toFun z := f * z.1 + g * z.2
  map_add' x y := by dsimp; ring
  map_smul' r x := by simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]; ring

def pairBoundary (f g : S) : S →ₗ[S] S × S where
  toFun t := (-g * t, f * t)
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' r x := by ext <;> simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul] <;> ring

theorem regular_pair_components (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    IsSMulRegular S f ∧ IsSMulRegular (S ⧸ Ideal.span {f}) g := by
  refine ⟨((RingTheory.Sequence.isRegular_cons_iff S f [g]).mp hreg).1, ?_⟩
  have hg := hreg.toIsWeaklyRegular.regular_mod_prev 1 (by simp)
  change IsSMulRegular (S ⧸ (Ideal.ofList [f] • (⊤ : Submodule S S))) g at hg
  have hideal : (Ideal.ofList [f] • (⊤ : Submodule S S)) = Ideal.span {f} := by
    change Ideal.ofList [f] * (⊤ : Ideal S) = Ideal.span {f}
    rw [Ideal.mul_top, Ideal.ofList_singleton]
  exact ((Submodule.quotEquivOfEq _ _ hideal).isSMulRegular_congr g).mp hg

theorem regular_pair_syzygy (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) (a b : S)
    (hab : f * a + g * b = 0) :
    ∃ t : S, a = -g * t ∧ b = f * t := by
  obtain ⟨hf, hg⟩ := regular_pair_components f g hreg
  have hgb : g * b ∈ Ideal.span ({f} : Set S) := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-a, ?_⟩
    linear_combination hab
  have hb : b ∈ Ideal.span ({f} : Set S) :=
    mem_of_isSMulRegular_quotient_of_smul_mem hg hgb
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨t, ?_, rfl⟩
  apply hf
  change f * a = f * (-g * t)
  linear_combination hab

theorem regular_pair_range_boundary_eq_kernel (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    LinearMap.range (pairBoundary f g) = LinearMap.ker (pairRelation f g) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨t, rfl⟩
    change f * (-g * t) + g * (f * t) = 0
    ring
  · intro hz
    obtain ⟨t, ha, hb⟩ := regular_pair_syzygy f g hreg z.1 z.2 hz
    exact ⟨t, Prod.ext ha.symm hb.symm⟩

theorem regular_pair_boundary_injective (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    Function.Injective (pairBoundary f g) := by
  intro x y hxy
  apply (regular_pair_components f g hreg).1
  exact congrArg Prod.snd hxy

theorem pair_relation_range (f g : S) :
    LinearMap.range (pairRelation f g) = Ideal.ofList [f, g] := by
  apply le_antisymm
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    have hf : f ∈ Ideal.ofList [f, g] := Ideal.subset_span (by simp)
    have hg : g ∈ Ideal.ofList [f, g] := Ideal.subset_span (by simp)
    change f * a + g * b ∈ Ideal.ofList [f, g]
    exact Ideal.add_mem _ (by simpa [mul_comm] using (Ideal.ofList [f, g]).smul_mem a hf)
      (by simpa [mul_comm] using (Ideal.ofList [f, g]).smul_mem b hg)
  · apply Ideal.span_le.mpr
    intro r hr
    have hr : r = f ∨ r = g := by simpa using hr
    rcases hr with rfl | rfl
    · exact ⟨(1, 0), by simp [pairRelation]⟩
    · exact ⟨(0, 1), by simp [pairRelation]⟩

theorem pair_relation_range_eq_quotient_kernel (f g : S) :
    LinearMap.range (pairRelation f g) = LinearMap.ker (Ideal.ofList [f, g]).mkQ := by
  rw [Submodule.ker_mkQ, pair_relation_range]

def pairToIdeal (f g : S) : (S × S) →ₗ[S] Ideal.ofList [f, g] :=
  (pairRelation f g).codRestrict (Ideal.ofList [f, g]) (fun z => by
    rw [← pair_relation_range]
    exact LinearMap.mem_range_self _ _)

theorem pairToIdeal_surjective (f g : S) : Function.Surjective (pairToIdeal f g) := by
  intro x
  obtain ⟨z, hz⟩ : ∃ z, pairRelation f g z = (x : S) := by
    apply LinearMap.mem_range.mp
    rw [pair_relation_range]
    exact x.property
  exact ⟨z, Subtype.ext hz⟩

theorem regular_pair_range_boundary_eq_kernel_toIdeal (f g : S)
    (hreg : RingTheory.Sequence.IsRegular S [f, g]) :
    LinearMap.range (pairBoundary f g) = LinearMap.ker (pairToIdeal f g) := by
  simpa only [pairToIdeal, LinearMap.ker_codRestrict] using
    regular_pair_range_boundary_eq_kernel f g hreg

theorem ideal_subtype_range_eq_quotient_kernel (f g : S) :
    LinearMap.range (Ideal.ofList [f, g]).subtype =
      LinearMap.ker (Ideal.ofList [f, g]).mkQ := by
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

end RegularPair

variable (k : Type*) [Field k] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime]

abbrev PolynomialLocal := Localization.AtPrime Q

theorem polynomial_local_regular_pair_resolution
    (f g : PolynomialLocal k n Q)
    (hreg : RingTheory.Sequence.IsRegular (PolynomialLocal k n Q) [f, g]) :
    Function.Injective (pairBoundary f g) ∧
    LinearMap.range (pairBoundary f g) = LinearMap.ker (pairRelation f g) ∧
    LinearMap.range (pairRelation f g) = LinearMap.ker (Ideal.ofList [f, g]).mkQ ∧
    Function.Surjective (Ideal.ofList [f, g]).mkQ :=
  ⟨regular_pair_boundary_injective f g hreg,
    regular_pair_range_boundary_eq_kernel f g hreg,
    pair_relation_range_eq_quotient_kernel f g, Submodule.mkQ_surjective _⟩

theorem polynomial_local_regular_pair_dimension_drop
    (f g : PolynomialLocal k n Q)
    (hreg : RingTheory.Sequence.IsRegular (PolynomialLocal k n Q) [f, g]) :
    ringKrullDim (PolynomialLocal k n Q ⧸ Ideal.ofList [f, g]) + 2 =
      ringKrullDim (PolynomialLocal k n Q) := by
  simpa using ringKrullDim_add_length_eq_ringKrullDim_of_isRegular [f, g] hreg

def PolynomialLocalPairUnmixednessTarget : Prop :=
  ∀ f g : PolynomialLocal k n Q,
    RingTheory.Sequence.IsRegular (PolynomialLocal k n Q) [f, g] →
    ∀ P : Ideal (PolynomialLocal k n Q),
      IsAssociatedPrime P (PolynomialLocal k n Q ⧸ Ideal.ofList [f, g]) →
        P.height = 2

end PiExponentJets.PolynomialLocalUnmixedness

end

end OAI
