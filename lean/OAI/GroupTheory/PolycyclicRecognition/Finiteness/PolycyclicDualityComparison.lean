import OAI.GroupTheory.PolycyclicRecognition.Finiteness.DualityEndgame

namespace OAI

/-! # The algebraic Poincaré-duality comparison group

Only two standard published consequences are needed here:

* D. J. S. Robinson, *A Course in the Theory of Groups*, second edition,
  GTM 80, Springer (1996), Theorem 5.4.15(i), p.153: every polycyclic
  group has a finite-index poly-infinite-cyclic subgroup. We use only its
  torsion-free consequence, not normality or a chosen infinite-cyclic series.
* R. Bieri, *Homological Dimension of Discrete Groups*, second edition
  (1981), Theorems 9.9 and 9.10, and their explicit consequence on p.176:
  every torsion-free polycyclic group is an integral Poincaré-duality group.

These are explicit conditional inputs. The resulting recognition theorem
retains elementary amenability as a hypothesis.
-/

namespace PolycyclicRecognition

/-- Group-theoretic torsion freeness. This only excludes nonidentity finite-order
elements; it does not impose the unique-root property on a noncommutative group. -/
def HasNoNontrivialTorsion (P : Type) [Group P] : Prop :=
  ∀ (g : P) (n : ℕ), n ≠ 0 → g ^ n = 1 → g = 1

/-- The torsion-free consequence of Robinson 5.4.15(i). -/
def PolycyclicTorsionFreeIndexInput : Prop :=
  ∀ (P : Type) [Group P], IsPolycyclic P →
    ∃ Γ : Subgroup P, Γ.FiniteIndex ∧ HasNoNontrivialTorsion Γ

/-- The precise polycyclic specialization of Bieri's duality theorems. -/
def BieriPolycyclicDualityInput : Prop :=
  ∀ (P : Type) [Group P], HasNoNontrivialTorsion P → IsPolycyclic P →
    ∃ n : ℕ, IsIntegralPoincareDualityGroup P n

/-- A virtual-polycyclic comparison group supplies an actual finitely
generated integral duality group in the same coarse equivalence class. -/
theorem exists_coarse_poincareDuality_comparison
    (tf : PolycyclicTorsionFreeIndexInput) (pd : BieriPolycyclicDualityInput)
    (P H : Type) [Group P] [Group H] [Group.FG P]
    (hP : IsVirtuallyPolycyclic P) (e : GroupCoarseEquivalence P H) :
    ∃ (K : Subgroup P) (Γ : Subgroup K),
      K.FiniteIndex ∧ Γ.FiniteIndex ∧ Group.FG Γ ∧
      Nonempty (GroupCoarseEquivalence Γ H) ∧
      ∃ n : ℕ, IsIntegralPoincareDualityGroup Γ n := by
  obtain ⟨K, hKindex, hKpoly⟩ := hP
  let := hKindex
  obtain ⟨Γ, hΓindex, hΓtf⟩ := tf K hKpoly
  let := hΓindex
  have hΓpoly : IsPolycyclic Γ := hKpoly.of_injective Γ.subtype Subtype.val_injective
  obtain ⟨n, hΓPD⟩ := pd Γ hΓtf hΓpoly
  exact ⟨K, Γ, hKindex, hΓindex, inferInstance,
    ⟨(finiteIndexCoarseEquivalence Γ).trans ((finiteIndexCoarseEquivalence K).trans e)⟩,
    n, hΓPD⟩

/-- An elementary amenable group coarsely equivalent to a virtually
polycyclic group is virtually polycyclic, given the finiteness and duality
inputs. -/
theorem virtuallyPolycyclic_of_elementaryAmenable_coarse_virtualPolycyclic
    (tf : PolycyclicTorsionFreeIndexInput) (pd : BieriPolycyclicDualityInput)
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    (P H : Type) [Group P] [Group H] [Group.FG P] [Group.FG H]
    (hP : IsVirtuallyPolycyclic P) (e : GroupCoarseEquivalence P H)
    (hEA : IsElementaryAmenable H) : IsVirtuallyPolycyclic H := by
  obtain ⟨K, Γ, _, _, hfg, ⟨eΓ⟩, n, hΓPD⟩ :=
    exists_coarse_poincareDuality_comparison tf pd P H hP e
  let := hfg
  exact virtuallyPolycyclic_of_elementaryAmenable_coarse_PD liFP eaFP liPD bieri Γ H eΓ hEA n hΓPD

end PolycyclicRecognition

end OAI
