import OAI.Probability.SignedSweeps.Irreducibility

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma finrank_le_translates {G E A Q : Type*} [Group G]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A] [Fintype Q]
    (ρ : Representation ℂ G E) [ρ.IsIrreducible] (f : A →ₗ[ℂ] E) (hf : f ≠ 0)
    (rep : Q → G) (index : G → Q)
    (hrep : ∀ g x, ∃ y, ρ g (f x) = ρ (rep (index g)) (f y)) :
    finrank ℂ E ≤ Fintype.card Q * finrank ℂ A := by
  classical
  let L : (Q → A) →ₗ[ℂ] E :=
    { toFun := fun w => ∑ i, ρ (rep i) (f (w i))
      map_add' := by intro w z; simp [Finset.sum_add_distrib]
      map_smul' := by intro z w; simp [Finset.smul_sum] }
  have horbit (g : G) (x : A) : ρ g (f x) ∈ LinearMap.range L := by
    obtain ⟨y, hy⟩ := hrep g x
    refine ⟨Pi.single (index g) y, ?_⟩
    rw [hy]
    simp [L, Pi.single_apply, apply_ite, map_zero]
  let S : Subrepresentation ρ :=
    { toSubmodule := LinearMap.range L
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨w, rfl⟩ := hx
        change ρ g (∑ i, ρ (rep i) (f (w i))) ∈ LinearMap.range L
        rw [map_sum]
        apply Submodule.sum_mem
        intro i hi
        rw [← Module.End.mul_apply, ← map_mul]
        exact horbit (g * rep i) (w i) }
  have hS : S ≠ ⊥ := by
    intro he
    apply hf
    ext x
    have hx := horbit 1 x
    rw [map_one, Module.End.one_apply] at hx
    have hbot : LinearMap.range L = ⊥ := congrArg Subrepresentation.toSubmodule he
    rw [hbot] at hx
    exact hx
  have htop : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hS
  have hsur : Function.Surjective L := LinearMap.range_eq_top.mp
    (congrArg Subrepresentation.toSubmodule htop)
  calc
    finrank ℂ E ≤ finrank ℂ (Q → A) := LinearMap.finrank_le_finrank_of_surjective hsur
    _ = Fintype.card Q * finrank ℂ A := by simp [Module.finrank_pi_fintype]

def ColoringOrbit {n : ℕ} {I : Type*} (c : Fin n → I) : Type _ :=
  Set.range (fun g : SymmetricGroup n => c ∘ (g⁻¹ : SymmetricGroup n))

instance coloringOrbitFinite {n : ℕ} {I : Type*} (c : Fin n → I) : Finite (ColoringOrbit c) :=
  Set.finite_range _

instance coloringOrbitFintype {n : ℕ} {I : Type*} (c : Fin n → I) : Fintype (ColoringOrbit c) :=
  Fintype.ofFinite _

def coloringOrbitIndex {n : ℕ} {I : Type*} (c : Fin n → I) (g : SymmetricGroup n) :
    ColoringOrbit c := ⟨c ∘ (g⁻¹ : SymmetricGroup n), ⟨g, rfl⟩⟩

def coloringOrbitRep {n : ℕ} {I : Type*} (c : Fin n → I) (q : ColoringOrbit c) :
    SymmetricGroup n := q.property.choose

lemma coloringOrbitRep_property {n : ℕ} {I : Type*} (c : Fin n → I) (g : SymmetricGroup n) :
    (coloringOrbitRep c (coloringOrbitIndex c g))⁻¹ * g ∈ fiberSubgroup c := by
  let r := coloringOrbitRep c (coloringOrbitIndex c g)
  have he : c ∘ (r⁻¹ : SymmetricGroup n) = c ∘ (g⁻¹ : SymmetricGroup n) := (coloringOrbitIndex c g).property.choose_spec
  intro x
  have h := congrFun he (g x)
  simpa using h

lemma finrank_le_coloringOrbit {n : ℕ} {I E A : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ρ : Representation ℂ (SymmetricGroup n) E) [ρ.IsIrreducible]
    (f : A →ₗ[ℂ] E) (hf : f ≠ 0) (c : Fin n → I)
    (hstable : ∀ g : fiberSubgroup c, ∀ x : A, ∃ y, ρ g.1 (f x) = f y) :
    finrank ℂ E ≤ Fintype.card (ColoringOrbit c) * finrank ℂ A := by
  apply finrank_le_translates ρ f hf (coloringOrbitRep c) (coloringOrbitIndex c)
  intro g x
  let r := coloringOrbitRep c (coloringOrbitIndex c g)
  obtain ⟨y, hy⟩ := hstable ⟨r⁻¹ * g, coloringOrbitRep_property c g⟩ x
  refine ⟨y, ?_⟩
  rw [← hy, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

end SignedSweeps
end

end OAI
