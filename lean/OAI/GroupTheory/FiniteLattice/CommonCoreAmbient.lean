import OAI.GroupTheory.FiniteLattice.CommonCore

namespace OAI

namespace FiniteLattice.CommonCore

section

variable {D : Type*} [Group D]

/-- A subgroup contained in K, viewed inside K, is canonically the same group. -/
def subgroupInsideEquiv (A K : Subgroup D) (hAK : A ≤ K) : A.subgroupOf K ≃* A where
  toFun a := ⟨(a.val : D), a.property⟩
  invFun a := ⟨⟨a.val, hAK a.property⟩, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end

/-- Compatible extensions in a finite group glue uniquely over their generated join,
whose relative core retains the inner automorphisms. -/
def AmbientStatement (D T : Type*) [Group D] [Finite D] [Group T] [IsSimpleGroup T]
    (ι : Type*) [Finite ι] [Nonempty ι]
    (A : Subgroup D) (U : ι → Subgroup D) (hAU : ∀ i, A ≤ U i)
    (alpha : A →* MulAut T) (beta : ∀ i, U i →* MulAut T) : Prop :=
  (∃ x y : T, x * y ≠ y * x) →
  (∀ i, ∀ a : A, beta i (Subgroup.inclusion (hAU i) a) = alpha a) →
  (∀ i, (MulAut.conj : T →* MulAut T).range ≤
    (((A.subgroupOf (U i)).normalCore.map (U i).subtype).comap A.subtype).map alpha) →
  let K : Subgroup D := ⨆ i, U i
  (MulAut.conj : T →* MulAut T).range ≤
      (((A.subgroupOf K).normalCore.map K.subtype).comap A.subtype).map alpha ∧
    ∃! b : K →* MulAut T,
      ∀ i, ∀ u : U i, b ⟨u, (le_iSup U i) u.property⟩ = beta i u

/-- The common-core criterion for extension domains in a finite ambient group. -/
theorem common_core_ambient (D T : Type*) [Group D] [Finite D] [Group T]
    [IsSimpleGroup T] (ι : Type*) [Finite ι] [Nonempty ι]
    (A : Subgroup D) (U : ι → Subgroup D) (hAU : ∀ i, A ≤ U i)
    (alpha : A →* MulAut T) (beta : ∀ i, U i →* MulAut T) :
    AmbientStatement D T ι A U hAU alpha beta := by
  classical
  intro hna hext hcore
  let K : Subgroup D := ⨆ i, U i
  have hUK (i : ι) : U i ≤ K := le_iSup U i
  have hAK : A ≤ K := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (hAU i).trans (hUK i)
  let A' : Subgroup K := A.subgroupOf K
  let U' : ι → Subgroup K := fun i => (U i).subgroupOf K
  let ea : A' ≃* A := subgroupInsideEquiv A K hAK
  let eu (i : ι) : U' i ≃* U i := subgroupInsideEquiv (U i) K (hUK i)
  have hAU' (i : ι) : A' ≤ U' i := fun _ hx => hAU i hx
  have hgen' : (⨆ i, U' i) = ⊤ := by
    let B : Subgroup K := ⨆ i, U' i
    have hKB : K ≤ B.map K.subtype := by
      apply iSup_le
      intro i x hx
      exact ⟨⟨x, hUK i hx⟩, (le_iSup U' i) hx, rfl⟩
    apply top_unique
    intro x _
    obtain ⟨y, hy, he⟩ := hKB x.property
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy
  let alpha' : A' →* MulAut T := alpha.comp ea.toMonoidHom
  let beta' (i : ι) : U' i →* MulAut T := (beta i).comp (eu i).toMonoidHom
  have hext' (i : ι) (a : A') :
      beta' i (Subgroup.inclusion (hAU' i) a) = alpha' a := by
    exact hext i (ea a)
  have hcore' (i : ι) : (MulAut.conj : T →* MulAut T).range ≤
      (((A'.subgroupOf (U' i)).normalCore.map (U' i).subtype).comap A'.subtype).map
        alpha' := by
    intro y hy
    obtain ⟨a, ha, hay⟩ := hcore i hy
    obtain ⟨u, hu, hua⟩ := ha
    refine ⟨ea.symm a, ?_, hay⟩
    refine ⟨(eu i).symm u, ?_, ?_⟩
    · intro v
      change ((v : K) : D) * (u : D) * ((v : K) : D)⁻¹ ∈ A
      exact hu (eu i v)
    · apply Subtype.ext
      exact hua
  obtain ⟨hfirst, b, hb, hunique⟩ :=
    common_core K T ι A' U' hAU' alpha' beta' hna hgen' hext' hcore'
  refine ⟨?_, b, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, hay⟩ := hfirst hy
    refine ⟨ea a, ?_, hay⟩
    exact ⟨(a : K), ha, rfl⟩
  · intro i u
    exact hb i ((eu i).symm u)
  · intro b' hb'
    apply hunique b'
    intro i u
    exact hb' i (eu i u)

end FiniteLattice.CommonCore

end OAI
