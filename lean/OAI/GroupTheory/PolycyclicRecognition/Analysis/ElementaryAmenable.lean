import OAI.GroupTheory.PolycyclicRecognition.Algebra.Nilpotent

namespace OAI

/-!
# Elementary amenability of the height extension

We use the closure definition: finite and abelian groups, subgroups, quotients,
extensions, and directed unions. For the last operation it suffices to use the
directed union of the finitely generated subgroups. This formulation is exactly
what is needed when the corrected height kernel is locally virtually nilpotent.
In particular, no finite generation of that kernel is imposed.
-/

namespace PolycyclicRecognition

universe u

/-- The elementary amenable class, with directed-union closure expressed by the
canonical directed family of all finitely generated subgroups. -/
inductive IsElementaryAmenable : (G : Type u) → [Group G] → Prop where
  | finite (G : Type u) [Group G] [Finite G] : IsElementaryAmenable G
  | abelian (G : Type u) [Group G] (comm : ∀ x y : G, x * y = y * x) :
      IsElementaryAmenable G
  | of_injective {G H : Type u} [Group G] [Group H]
      (hG : IsElementaryAmenable G) (f : H →* G) (hf : Function.Injective f) :
      IsElementaryAmenable H
  | of_surjective {G H : Type u} [Group G] [Group H]
      (hG : IsElementaryAmenable G) (f : G →* H) (hf : Function.Surjective f) :
      IsElementaryAmenable H
  | extension {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
      (hN : IsElementaryAmenable N) (hQ : IsElementaryAmenable (G ⧸ N)) :
      IsElementaryAmenable G
  | locally {G : Type u} [Group G]
      (h : ∀ J : Subgroup G, Group.FG J → IsElementaryAmenable J) :
      IsElementaryAmenable G

open scoped IsMulCommutative

/-- A finite derived series places a group in the elementary amenable class. -/
theorem elementaryAmenable_of_derivedSeries_eq_bot (n : ℕ) :
    ∀ (G : Type u) [Group G], derivedSeries G n = ⊥ → IsElementaryAmenable G := by
  induction n with
  | zero =>
    intro G _ hn
    have : Subsingleton G := by
      constructor
      intro x y
      have hx : x = 1 := by
        have h : x ∈ derivedSeries G 0 := Subgroup.mem_top x
        simpa only [hn, Subgroup.mem_bot] using h
      have hy : y = 1 := by
        have h : y ∈ derivedSeries G 0 := Subgroup.mem_top y
        simpa only [hn, Subgroup.mem_bot] using h
      exact hx.trans hy.symm
    exact .finite G
  | succ n ih =>
    intro G _ hn
    let N := commutator G
    have hnN : derivedSeries N n = ⊥ := by
      apply Subgroup.map_injective (f := N.subtype) Subtype.val_injective
      rw [Subgroup.map_bot, map_derivedSeries_commutator, hn]
    exact .extension N (ih N hnN) (.abelian _ mul_comm)

theorem elementaryAmenable_of_solvable (G : Type u) [Group G] [Group.IsSolvable G] :
    IsElementaryAmenable G := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  exact elementaryAmenable_of_derivedSeries_eq_bot n G hn

/-- Elementary amenability passes from a finite-index subgroup to its ambient
group, using the normal core without assuming the original subgroup normal. -/
theorem elementaryAmenable_of_finiteIndex {G : Type u} [Group G]
    (H : Subgroup G) [H.FiniteIndex] (hH : IsElementaryAmenable H) :
    IsElementaryAmenable G := by
  let N := H.normalCore
  let f : N →* H := Subgroup.inclusion H.normalCore_le
  exact .extension N (hH.of_injective f (Subgroup.inclusion_injective _))
    (.finite (G ⧸ N))

/-- A finite extension of a solvable subgroup is elementary amenable. Normality
is obtained by taking the finite-index normal core. -/
theorem elementaryAmenable_of_finiteIndex_solvable {G : Type u} [Group G]
    (H : Subgroup G) [H.FiniteIndex] [Group.IsSolvable H] : IsElementaryAmenable G := by
  let N := H.normalCore
  let f : N →* H := Subgroup.inclusion H.normalCore_le
  have hf : Function.Injective f := Subgroup.inclusion_injective H.normalCore_le
  exact .extension N
    ((elementaryAmenable_of_solvable H).of_injective f hf) (.finite (G ⧸ N))

theorem elementaryAmenable_of_virtuallyNilpotent {G : Type u} [Group G]
    (hG : Group.IsVirtuallyNilpotent G) : IsElementaryAmenable G := by
  obtain ⟨N, hnil, hindex⟩ := hG
  let := hnil
  let := hindex
  exact elementaryAmenable_of_finiteIndex_solvable N

/-- Local virtual nilpotence is sufficient even for an infinitely generated
group, as occurs for a nondiscrete height homomorphism. -/
theorem elementaryAmenable_of_locallyVirtuallyNilpotent {G : Type u} [Group G]
    (hG : ∀ J : Subgroup G, Group.FG J → Group.IsVirtuallyNilpotent J) :
    IsElementaryAmenable G := by
  exact .locally fun J hJ => elementaryAmenable_of_virtuallyNilpotent (hG J hJ)

/-- An abelian height quotient and a locally virtually nilpotent kernel give
elementary amenability of the domain. -/
theorem elementaryAmenable_of_height_kernel {G A : Type u} [Group G] [CommGroup A]
    (τ : G →* A)
    (hker : ∀ J : Subgroup τ.ker, Group.FG J → Group.IsVirtuallyNilpotent J) :
    IsElementaryAmenable G := by
  apply IsElementaryAmenable.extension τ.ker
  · exact elementaryAmenable_of_locallyVirtuallyNilpotent hker
  · let e := QuotientGroup.quotientKerEquivRange τ
    exact (IsElementaryAmenable.abelian τ.range mul_comm).of_injective
      e.toMonoidHom e.injective

end PolycyclicRecognition

end OAI
