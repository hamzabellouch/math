import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveAnnihilatorPropagation
import Mathlib.Algebra.MonoidAlgebra.Module

namespace OAI

/-! # The positive-relation criterion for a character half-space -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {Q M : Type} [CommGroup Q] [AddCommGroup M]

def characterNonnegativeMonoid (χ : Q →* Multiplicative ℝ) : Submonoid Q where
  carrier := {q | 0 ≤ (χ q).toAdd}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change 0 ≤ (χ (a * b)).toAdd
    rw [map_mul]
    exact add_nonneg ha hb

def representationOrbitSet (ρ : Representation ℤ Q M) (s : Set M) : Set M :=
  {x | ∃ q : Q, ∃ y ∈ s, ρ q y = x}

def positiveCharacterOrbitSet (ρ : Representation ℤ Q M)
    (χ : Q →* Multiplicative ℝ) (s : Set M) : Set M :=
  {x | ∃ q : Q, 0 ≤ (χ q).toAdd ∧ ∃ y ∈ s, ρ q y = x}

theorem positiveCharacterOrbitSpan_stable (ρ : Representation ℤ Q M)
    (χ : Q →* Multiplicative ℝ) (s : Set M) (q : Q) (hq : 0 ≤ (χ q).toAdd)
    (x : M) (hx : x ∈ Submodule.span ℤ (positiveCharacterOrbitSet ρ χ s)) :
    ρ q x ∈ Submodule.span ℤ (positiveCharacterOrbitSet ρ χ s) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, z, hz, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨q * r, ?_, z, hz, ?_⟩
    · rw [map_mul]
      exact add_nonneg hq hr
    · rw [map_mul, Module.End.mul_apply]
  | zero => simpa only [map_zero] using
      (Submodule.span ℤ (positiveCharacterOrbitSet ρ χ s)).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using
      (Submodule.span ℤ (positiveCharacterOrbitSet ρ χ s)).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using
      (Submodule.span ℤ (positiveCharacterOrbitSet ρ χ s)).smul_mem r hx

theorem positiveCharacterOrbitSpan_eq_top (ρ : Representation ℤ Q M)
    (χ : Q →* Multiplicative ℝ) (s : Set M)
    (hgen : Submodule.span ℤ (representationOrbitSet ρ s) = ⊤)
    (a : Finset Q) (c : Q → ℤ) {δ : ℝ} (hδ : 0 < δ)
    (ha : ∀ g ∈ a, δ ≤ (χ g).toAdd)
    (hrec : ∀ x : M, x = ∑ g ∈ a, c g • ρ g x) :
    Submodule.span ℤ (positiveCharacterOrbitSet ρ χ s) = ⊤ := by
  let U := Submodule.span ℤ (positiveCharacterOrbitSet ρ χ s)
  have hU := submodule_stable_of_positive_relation ρ χ a c hδ ha hrec U
    (positiveCharacterOrbitSpan_stable ρ χ s)
  have hs : s ⊆ U := by
    intro x hx
    apply Submodule.subset_span
    exact ⟨1, by simp, x, hx, by simp⟩
  have hle : Submodule.span ℤ (representationOrbitSet ρ s) ≤ U := by
    apply Submodule.span_le.mpr
    rintro y ⟨q, x, hx, rfl⟩
    exact hU q x (hs hx)
  rw [hgen] at hle
  exact top_unique hle

def characterMonoidRepresentation (ρ : Representation ℤ Q M)
    (χ : Q →* Multiplicative ℝ) :
    Representation ℤ (characterNonnegativeMonoid χ) M :=
  ρ.comp (characterNonnegativeMonoid χ).subtype

theorem finite_characterMonoidModule_of_orbitSpan (ρ : Representation ℤ Q M)
    (χ : Q →* Multiplicative ℝ) (s : Finset M)
    (hgen : Submodule.span ℤ (positiveCharacterOrbitSet ρ χ (s : Set M)) = ⊤) :
    Module.Finite ℤ[characterNonnegativeMonoid χ] (characterMonoidRepresentation ρ χ).asModule := by
  classical
  let σ := characterMonoidRepresentation ρ χ
  let t := s.image σ.asModuleEquiv.symm
  let U : Submodule ℤ[characterNonnegativeMonoid χ] σ.asModule :=
    Submodule.span _ (t : Set σ.asModule)
  let W : Submodule ℤ M :=
    (U.restrictScalars ℤ).comap σ.asModuleEquiv.symm.toLinearMap
  have hW : Submodule.span ℤ (positiveCharacterOrbitSet ρ χ (s : Set M)) ≤ W := by
    apply Submodule.span_le.mpr
    rintro y ⟨q, hq, x, hx, rfl⟩
    change σ.asModuleEquiv.symm (ρ q x) ∈ U
    change σ.asModuleEquiv.symm (σ ⟨q, hq⟩ x) ∈ U
    rw [Representation.asModuleEquiv_symm_map_rho]
    apply U.smul_mem
    exact Submodule.subset_span (Finset.mem_image_of_mem σ.asModuleEquiv.symm hx)
  have hUt : U = ⊤ := by
    apply top_unique
    intro x _
    have hw : σ.asModuleEquiv x ∈ W := hW (hgen ▸ Submodule.mem_top)
    change σ.asModuleEquiv.symm (σ.asModuleEquiv x) ∈ U at hw
    simpa only [LinearEquiv.symm_apply_apply] using hw
  exact Module.Finite.of_fg_top ⟨t, hUt⟩

end PolycyclicRecognition

end

end OAI
