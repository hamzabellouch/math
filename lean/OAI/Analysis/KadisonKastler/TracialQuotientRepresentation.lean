import OAI.Analysis.KadisonKastler.TracialQuotientVonNeumann
import OAI.Analysis.KadisonKastler.FaithfulTracePullback

namespace OAI

/-! # The trace-preserving represented tracial quotient -/

namespace KadisonKastler

open Filter

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

local notation "Q" => TracialSequenceQuotient τ ω
local notation "φ" => tracialQuotientTrace τ ω
local instance : PartialOrder Q := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing Q := CStarAlgebra.spectralOrderedRing _
local notation "K" => TraceStateHilbert φ
local notation "π" => traceStateRepresentation φ

theorem tracialSequenceAlgebra_in_range (hω : (ω : Filter ℕ) ≤ atTop)
    (T : K →L[ℂ] K) (hT : T ∈ tracialSequenceAlgebra τ ω) : ∃ b : Q, π b = T := by
  by_cases hzero : T = 0
  · exact ⟨0, by rw [map_zero, hzero]⟩
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  obtain ⟨a, ha⟩ := tracialSequenceAlgebra_contraction_in_range τ ω hω
    ((‖T‖ : ℂ)⁻¹ • T) ((tracialSequenceAlgebra τ ω).toStarSubalgebra.smul_mem hT _) hsmall
  refine ⟨(‖T‖ : ℂ) • a, ?_⟩
  rw [map_smul, ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

theorem tracialSequenceRepresentation_mem (a : Q) : π a ∈ tracialSequenceAlgebra τ ω :=
  subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩

attribute [local irreducible] tracialSequenceAlgebra

def tracialSequenceHom : Q →⋆ₐ[ℂ] Algebra (tracialSequenceAlgebra τ ω) :=
  (traceStateRepresentation φ).codRestrict (tracialSequenceAlgebra τ ω).toStarSubalgebra
    (tracialSequenceRepresentation_mem τ ω)

theorem tracialSequenceHom_injective : Function.Injective (tracialSequenceHom τ ω) := by
  intro a b h
  have hv := congrArg Subtype.val h
  change π a = π b at hv
  exact traceStateRepresentation_injective φ hv

theorem tracialSequenceHom_surjective (hω : (ω : Filter ℕ) ≤ atTop) :
    Function.Surjective (tracialSequenceHom τ ω) :=
  starAlgHom_codRestrict_surjective (traceStateRepresentation φ)
    (tracialSequenceAlgebra τ ω).toStarSubalgebra _
    (tracialSequenceAlgebra_in_range (B := B) τ ω hω)

def tracialSequenceEquiv (hω : (ω : Filter ℕ) ≤ atTop) :
    Q ≃⋆ₐ[ℂ] Algebra (tracialSequenceAlgebra τ ω) :=
  StarAlgEquiv.ofBijective (tracialSequenceHom τ ω)
    ⟨tracialSequenceHom_injective τ ω, tracialSequenceHom_surjective τ ω hω⟩

@[simp] theorem tracialSequenceEquiv_coe (hω : (ω : Filter ℕ) ≤ atTop) (a : Q) :
    (tracialSequenceEquiv τ ω hω a).val = π a := rfl

def representedTracialQuotientTrace (hω : (ω : Filter ℕ) ≤ atTop) :
    FaithfulTracialState (Algebra (tracialSequenceAlgebra τ ω)) :=
  (tracialQuotientTrace τ ω).comap (tracialSequenceEquiv τ ω hω).symm.toStarAlgHom
    (tracialSequenceEquiv τ ω hω).symm.injective

@[simp] theorem representedTracialQuotientTrace_equiv (hω : (ω : Filter ℕ) ≤ atTop) (a : Q) :
    (representedTracialQuotientTrace τ ω hω).toLinearMap (tracialSequenceEquiv τ ω hω a) =
      (tracialQuotientTrace τ ω).toLinearMap a := by
  change (tracialQuotientTrace τ ω).toLinearMap ((tracialSequenceEquiv τ ω hω).symm (tracialSequenceEquiv τ ω hω a)) = _
  rw [StarAlgEquiv.symm_apply_apply]

/-- Faithfulness and traciality force every isometry to be unitary. -/
theorem FaithfulTracialState.finite {A : Type*} [CStarAlgebra A]
    (σ : FaithfulTracialState A) (v : A) (hv : star v * v = 1) : v * star v = 1 := by
  have he : star (1 - v * star v) * (1 - v * star v) = 1 - v * star v := by
    simp only [star_sub, star_one, star_mul, star_star, sub_mul, mul_sub, one_mul, mul_one]
    rw [mul_assoc v (star v), ← mul_assoc (star v) v, hv, one_mul]
    abel
  have hz : σ.toLinearMap (star (1 - v * star v) * (1 - v * star v)) = 0 := by
    rw [he, map_sub, σ.tracial, hv, sub_self]
  exact (sub_eq_zero.mp (σ.faithful _ hz)).symm

theorem tracialSequenceAlgebra_finite (hω : (ω : Filter ℕ) ≤ atTop)
    (v : Algebra (tracialSequenceAlgebra τ ω)) (hv : star v * v = 1) : v * star v = 1 :=
  (representedTracialQuotientTrace τ ω hω).finite v hv

end

end KadisonKastler

end OAI
