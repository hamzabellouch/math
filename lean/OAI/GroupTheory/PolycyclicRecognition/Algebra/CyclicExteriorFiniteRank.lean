import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteCyclicOrbit

namespace OAI

/-! # A cyclic module over a field with finite exterior square has finite rank -/

noncomputable section
namespace PolycyclicRecognition
variable {K : Type} [Field K]
open scoped MonoidAlgebra
variable {M : Type} [AddCommGroup M] [Module K M]

def rationalCyclicOrbitSpan (ρ : Representation K (Multiplicative ℤ) M) (v : M) :
    Submodule K M := Submodule.span K (Set.range (fun i : ℤ => ρ (Multiplicative.ofAdd i) v))

theorem rationalCyclicOrbitSpan_invariant
    (ρ : Representation K (Multiplicative ℤ) M) (v : M) (g : Multiplicative ℤ)
    {x : M} (hx : x ∈ rationalCyclicOrbitSpan ρ v) :
    ρ g x ∈ rationalCyclicOrbitSpan ρ v := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨g.toAdd + i, rfl⟩
  | zero => simpa only [map_zero] using (rationalCyclicOrbitSpan ρ v).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using
      (rationalCyclicOrbitSpan ρ v).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using (rationalCyclicOrbitSpan ρ v).smul_mem r hx

theorem rational_cyclic_finite_rank
    (ρ : Representation K (Multiplicative ℤ) M)
    [Module.Finite K[Multiplicative ℤ] ρ.asModule]
    [Module.Finite K[Multiplicative ℤ] (rationalExteriorSquareRepresentation ρ).asModule] :
    FiniteDimensional K M := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top :
    (⊤ : Submodule K[Multiplicative ℤ] ρ.asModule).FG)
  let U₀ : s → Submodule K M := fun a => rationalCyclicOrbitSpan ρ (ρ.asModuleEquiv a.val)
  let U : Submodule K M := ⨆ a, U₀ a
  let (a : s) : FiniteDimensional K (U₀ a) :=
    cyclic_orbit_span_finite_of_finite_exterior ρ (ρ.asModuleEquiv a.val)
  let : FiniteDimensional K U := inferInstance
  have hstable (g : Multiplicative ℤ) : U ≤ U.comap (ρ g) := by
    apply iSup_le
    intro a x hx
    exact (le_iSup U₀ a) (rationalCyclicOrbitSpan_invariant ρ _ g hx)
  let V : Submodule K ρ.asModule := U.comap ρ.asModuleEquiv.toLinearMap
  have hVstable (g : Multiplicative ℤ) (x : ρ.asModule) (hx : x ∈ V) :
      MonoidAlgebra.of K (Multiplicative ℤ) g • x ∈ V := by
    change ρ.asModuleEquiv (MonoidAlgebra.single g 1 • x) ∈ U
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
      LinearMap.smul_apply, one_smul]
    exact hstable g hx
  let W : Submodule K[Multiplicative ℤ] ρ.asModule :=
    MonoidAlgebra.submoduleOfSMulMem V hVstable
  have hW : Submodule.span K[Multiplicative ℤ] (s : Set ρ.asModule) ≤ W := by
    apply Submodule.span_le.mpr
    intro x hx
    change ρ.asModuleEquiv x ∈ U
    apply le_iSup U₀ ⟨x, hx⟩
    have h : ρ (Multiplicative.ofAdd (0 : ℤ)) (ρ.asModuleEquiv x) ∈ U₀ ⟨x, hx⟩ :=
      Submodule.subset_span ⟨0, rfl⟩
    simpa using h
  have htop (x : M) : x ∈ U := by
    have h : ρ.asModuleEquiv.symm x ∈ W := hW (hs ▸ Submodule.mem_top)
    change ρ.asModuleEquiv (ρ.asModuleEquiv.symm x) ∈ U at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  exact Module.Finite.of_surjective U.subtype (fun x => ⟨⟨x, htop x⟩, rfl⟩)

end PolycyclicRecognition

end

end OAI
