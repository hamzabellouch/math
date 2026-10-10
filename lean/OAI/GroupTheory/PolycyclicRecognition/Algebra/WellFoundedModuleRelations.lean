import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveAnnihilatorCriterion

namespace OAI

/-! # Finite generation from decreasing group-ring relations

A natural-number height measures distance from a submonoid. A bounded layer
has finitely many representatives modulo that monoid. Relations which strictly
decrease the height then give actual finite module generators.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {Q M : Type} [CommGroup Q] [AddCommGroup M]

def submonoidRepresentationOrbit (ρ : Representation ℤ Q M) (S : Submonoid Q)
    (s : Set M) : Set M := {x | ∃ q : S, ∃ y ∈ s, ρ q y = x}

theorem submonoidRepresentationOrbit_span_stable (ρ : Representation ℤ Q M)
    (S : Submonoid Q) (s : Set M) (q : S) (x : M)
    (hx : x ∈ Submodule.span ℤ (submonoidRepresentationOrbit ρ S s)) :
    ρ q x ∈ Submodule.span ℤ (submonoidRepresentationOrbit ρ S s) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, z, hz, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨q * r, z, hz, ?_⟩
    change ρ ((q : Q) * (r : Q)) z = ρ q (ρ r z)
    rw [map_mul, Module.End.mul_apply]
  | zero => simpa only [map_zero] using
      (Submodule.span ℤ (submonoidRepresentationOrbit ρ S s)).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using
      (Submodule.span ℤ (submonoidRepresentationOrbit ρ S s)).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using
      (Submodule.span ℤ (submonoidRepresentationOrbit ρ S s)).smul_mem r hx

theorem finite_submonoidRepresentation_of_orbitSpan (ρ : Representation ℤ Q M)
    (S : Submonoid Q) (s : Finset M)
    (hgen : Submodule.span ℤ (submonoidRepresentationOrbit ρ S (s : Set M)) = ⊤) :
    Module.Finite ℤ[S] (Representation.asModule (ρ.comp S.subtype)) := by
  classical
  let σ : Representation ℤ S M := ρ.comp S.subtype
  let t := s.image σ.asModuleEquiv.symm
  let U : Submodule ℤ[S] σ.asModule := Submodule.span _ (t : Set σ.asModule)
  let W : Submodule ℤ M := (U.restrictScalars ℤ).comap σ.asModuleEquiv.symm.toLinearMap
  have hW : Submodule.span ℤ (submonoidRepresentationOrbit ρ S (s : Set M)) ≤ W := by
    apply Submodule.span_le.mpr
    rintro y ⟨q, x, hx, rfl⟩
    change σ.asModuleEquiv.symm (σ q x) ∈ U
    rw [Representation.asModuleEquiv_symm_map_rho]
    exact U.smul_mem _ (Submodule.subset_span (Finset.mem_image_of_mem _ hx))
  have hU : U = ⊤ := by
    apply top_unique
    intro x _
    have hx : σ.asModuleEquiv x ∈ W := hW (hgen ▸ Submodule.mem_top)
    change σ.asModuleEquiv.symm (σ.asModuleEquiv x) ∈ U at hx
    simpa only [LinearEquiv.symm_apply_apply] using hx
  exact Module.Finite.of_fg_top ⟨t, hU⟩

theorem representation_translate_identity (ρ : Representation ℤ Q M)
    (a : ℤ[Q]) (ha : ρ.asAlgebraHom a = 1) (q : Q) (x : M) :
    ρ q x = ∑ g ∈ a.coeff.support, a.coeff g • ρ (q * g) x := by
  have hx : x = ∑ g ∈ a.coeff.support, a.coeff g • ρ g x := by
    rw [← representation_groupRing_apply, ha]
    rfl
  calc
    ρ q x = ρ q (∑ g ∈ a.coeff.support, a.coeff g • ρ g x) := congrArg (ρ q) hx
    _ = _ := by simp only [map_sum, map_smul, map_mul, Module.End.mul_apply]

/-- The finite descent argument used after the character geometry constructs
a distance-to-cone height. Every relation is an actual identity on the module. -/
theorem finite_submonoidModule_of_decreasing_relations
    (ρ : Representation ℤ Q M) [Module.Finite ℤ[Q] ρ.asModule]
    (S : Submonoid Q) (height : Q → ℕ) (D : ℕ) (B : Finset Q)
    (hbase : ∀ q, height q ≤ D → ∃ b ∈ B, ∃ u : S, (u : Q) * b = q)
    (hrel : ∀ q, D < height q → ∃ a : ℤ[Q], ρ.asAlgebraHom a = 1 ∧
      ∀ g ∈ a.coeff.support, height (q * g) < height q) :
    Module.Finite ℤ[S] (Representation.asModule (ρ.comp S.subtype)) := by
  classical
  obtain ⟨s, hs⟩ := representation_finite_orbit_generators ρ
  let T := (B ×ˢ s).image (fun p => ρ p.1 p.2)
  let W := Submodule.span ℤ (submonoidRepresentationOrbit ρ S (T : Set M))
  have hall : ∀ n : ℕ, ∀ q, height q = n → ∀ x ∈ s, ρ q x ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hq x hx
      by_cases hb : height q ≤ D
      · obtain ⟨b, hbB, u, rfl⟩ := hbase q hb
        rw [map_mul, Module.End.mul_apply]
        apply submonoidRepresentationOrbit_span_stable ρ S (T : Set M) u
        apply Submodule.subset_span
        refine ⟨1, ρ b x, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨(b, x), Finset.mem_product.mpr ⟨hbB, hx⟩, rfl⟩
        · simp
      · obtain ⟨a, ha, hdec⟩ := hrel q (Nat.lt_of_not_ge hb)
        rw [representation_translate_identity ρ a ha q x]
        apply W.sum_mem
        intro g hg
        apply W.smul_mem
        exact ih (height (q * g)) (hq ▸ hdec g hg) (q * g) rfl x hx
  have hle : Submodule.span ℤ (representationOrbitSet ρ (s : Set M)) ≤ W := by
    apply Submodule.span_le.mpr
    rintro y ⟨q, x, hx, rfl⟩
    exact hall (height q) q rfl x hx
  have hW : W = ⊤ := top_unique (hs ▸ hle)
  exact finite_submonoidRepresentation_of_orbitSpan ρ S T hW

end PolycyclicRecognition

end

end OAI
