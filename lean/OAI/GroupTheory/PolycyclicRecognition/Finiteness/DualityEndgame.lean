import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CohomologicalFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseEquivalence

namespace OAI

/-!
# The conditional finiteness and duality endgame

Elementary amenability is an explicit premise. Finiteness transfer, elementary
amenable finiteness, duality transfer, and solvable duality are retained as
separate parameters with the following mathematical sources.

* Xin Li, *Dynamic characterizations of quasi-isometry and applications to
  cohomology*, AGT 18 (2018), Corollaries 4.47 and 4.48.
* Kropholler–Martínez-Pérez–Nucinkis, *Cohomological finiteness conditions for
  elementary amenable groups*, J. reine angew. Math. 637 (2009), Theorem 1.1
  (viii) ⇒ (v) and the structural conclusion in §2. We use only their consequence
  that an elementary amenable group of type FP∞ has a finite-index solvable
  subgroup of finite integral cohomological dimension: intersect the solvable
  subgroup with the type-F subgroup.
* R. Bieri, *Homological dimension of discrete groups*, 2nd ed. (1981),
  Theorem 9.23: solvable integral Poincaré duality groups are polycyclic.

The propositions concern group-ring resolutions, group cohomology, and
finite-index subgroups.
-/

namespace PolycyclicRecognition

/-- Li, Corollary 4.47, specialized to integral coefficients and finitely
generated groups. The choice of left coarse structure is changed to Li's right
coarse structure by inversion. -/
def LiFinitenessInput : Prop :=
  ∀ (Γ H : Type) [Group Γ] [Group H] [Group.FG Γ] [Group.FG H],
    GroupCoarseEquivalence Γ H → ∀ n, TypeFP Γ n → TypeFP H n

/-- The precise finiteness/solvability consequence of Kropholler–Martínez-Pérez–
Nucinkis used in the manuscript. This does not assert polycyclicity. -/
def ElementaryAmenableFinitenessInput : Prop :=
  ∀ (H : Type) [Group H] [Group.FG H],
    IsElementaryAmenable H → TypeFPInfinity H →
    ∃ V : Subgroup H, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V

/-- Li, Corollary 4.48, integral Poincaré duality transfer with both finite
cohomological dimension hypotheses retained. -/
def LiDualityInput : Prop :=
  ∀ (Γ H : Type) [Group Γ] [Group H] [Group.FG Γ] [Group.FG H],
    GroupCoarseEquivalence Γ H →
    HasFiniteIntegralCohomologicalDimension Γ →
    HasFiniteIntegralCohomologicalDimension H →
    ∀ n, IsIntegralPoincareDualityGroup Γ n → IsIntegralPoincareDualityGroup H n

/-- Bieri, Theorem 9.23, in the integral case needed here. -/
def BieriDualityInput : Prop :=
  ∀ (H : Type) [Group H] [Group.IsSolvable H],
    ∀ n, IsIntegralPoincareDualityGroup H n → IsPolycyclic H

/-- Elementary amenability, coarse equivalence to an integral duality group,
and the finiteness and duality inputs imply virtual polycyclicity. -/
theorem virtuallyPolycyclic_of_elementaryAmenable_coarse_PD
    (liFP : LiFinitenessInput) (eaFP : ElementaryAmenableFinitenessInput)
    (liPD : LiDualityInput) (bieri : BieriDualityInput)
    (Γ H : Type) [Group Γ] [Group H] [Group.FG Γ] [Group.FG H]
    (e : GroupCoarseEquivalence Γ H) (hEA : IsElementaryAmenable H)
    (n : ℕ) (hΓPD : IsIntegralPoincareDualityGroup Γ n) :
    IsVirtuallyPolycyclic H := by
  have hFP : TypeFPInfinity H :=
    fun i => liFP Γ H e i (hΓPD.typeFPInfinity Γ i)
  obtain ⟨V, hindex, hsolv, hVcd⟩ := eaFP H hEA hFP
  let := hindex
  let := hsolv
  let eV : GroupCoarseEquivalence Γ V := e.trans (finiteIndexCoarseEquivalence V).symm
  have hVPD := liPD Γ V eV (hΓPD.finiteCohomologicalDimension Γ) hVcd n hΓPD
  exact ⟨V, hindex, bieri V n hVPD⟩

end PolycyclicRecognition

end OAI
