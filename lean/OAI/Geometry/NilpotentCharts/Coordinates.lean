import Mathlib
import OAI.Geometry.NilpotentCharts.Polynomials

namespace OAI

/-! Rational triangular coordinates, second-kind axes and lattice chart structures. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RationalLattice
structure RealCoordinates (G : Type*) [Group G] [TopologicalSpace G] (n : ℕ) where
  coord : G ≃ₜ (Fin n → ℝ)
  one_coord : ∀ i, coord 1 i = 0
  correction : (i : Fin n) → MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ
  mul_coord : ∀ g h i, coord (g*h) i = coord g i + coord h i +
    MvPolynomial.eval₂ (algebraMap ℚ ℝ)
      (Sum.elim (fun j => coord g ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j => coord h ⟨j.val,lt_trans j.isLt i.isLt⟩)) (correction i)

end RationalLattice

namespace MalcevCharacters
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n : ℕ} (c : RealCoordinates G n)

def axis (i : Fin n) (t : ℝ) : G := c.coord.symm (Pi.single i t)

structure SecondKind : Prop where
  axis_add : ∀ (i : Fin n) (s t : ℝ), axis c i (s+t) = axis c i s * axis c i t
  ordered : ∀ g : G, g = (List.ofFn (fun i : Fin n => axis c i (c.coord g i))).prod

end MalcevCharacters

namespace CubeFaces
structure Filtration (G : Type*) [Group G] where
  level : ℕ → Subgroup G
  antitone : Antitone level
  commutator_le : ∀ i j, ⁅level i, level j⁆ ≤ level (i + j)
end CubeFaces

namespace SourceProductChart
open RationalLattice MalcevCharacters CubeFaces
structure Chart (s : ℕ) (G : Type) [Group G] [TopologicalSpace G] (Γ : Subgroup G) where
  dim : ℕ
  coords : RealCoordinates G dim
  second : SecondKind coords
  filtration : Filtration G
  weight : Fin dim → ℕ
  level_iff : ∀ k g, g ∈ filtration.level k ↔ ∀ j, weight j < k → coords.coord g j = 0
  weight_pos : ∀ j, 0 < weight j
  lattice_iff : ∀ g, g ∈ Γ ↔ ∀ j, ∃ z : ℤ, coords.coord g j = z
  weight_mono : Monotone weight
  level0 : filtration.level 0 = ⊤
  level1 : filtration.level 1 = ⊤
  step : filtration.level (s+1) = ⊥

end SourceProductChart

open scoped Manifold ContDiff Topology
namespace SourceRawChartGap
open SourceProductChart

 

def RawChartExists : Prop :=
  ∀ (s d : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) G]
    [LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin d))) ∞ G]
    [T2Space G] [SecondCountableTopology G] [ConnectedSpace G] [SimplyConnectedSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)],
    (⊤ : Subgroup G).lowerCentralSeries s = ⊥ →
    Nonempty (Chart s G Γ)

end SourceRawChartGap

namespace RationalLattice
open RawPolynomial
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
  (c : RealCoordinates G n) {σ : Type*}
def IsPolyCoord (f : (σ → ℝ) → G) : Prop := ∀ j, IsPoly (fun x => c.coord (f x) j)

lemma isPoly_correction (j : Fin n) : IsPoly (fun a : Fin j.val ⊕ Fin j.val → ℝ =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) a (c.correction j)) := by
  refine ⟨MvPolynomial.map (algebraMap ℚ ℝ) (c.correction j),?_⟩
  intro a
  rw [MvPolynomial.eval_map]

lemma IsPolyCoord.const (g : G) : IsPolyCoord c (fun _ : σ → ℝ => g) := fun _ => isPoly_const _

lemma IsPolyCoord.mul {f g : (σ → ℝ) → G} (hf : IsPolyCoord c f) (hg : IsPolyCoord c g) :
    IsPolyCoord c (fun x => f x * g x) := by
  intro j
  have hq := (isPoly_correction c j).comp (g := fun x => Sum.elim
    (fun k : Fin j.val => c.coord (f x) ⟨k.val,lt_trans k.isLt j.isLt⟩)
    (fun k : Fin j.val => c.coord (g x) ⟨k.val,lt_trans k.isLt j.isLt⟩))
      (fun i => by cases i with | inl k => exact hf _ | inr k => exact hg _)
  exact ((hf j).add (hg j) |>.add hq).congr (fun x => (c.mul_coord (f x) (g x) j).symm)

lemma IsPolyCoord.inv {f : (σ → ℝ) → G} (hf : IsPolyCoord c f) :
    IsPolyCoord c (fun x => (f x)⁻¹) := by
  have aux : ∀ k : ℕ, ∀ hk : k < n, IsPoly (fun x => c.coord ((f x)⁻¹) ⟨k,hk⟩) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let j : Fin n := ⟨k,hk⟩
      have hq := (isPoly_correction c j).comp (g := fun x => Sum.elim
        (fun i : Fin k => c.coord (f x) ⟨i.val,lt_trans i.isLt hk⟩)
        (fun i : Fin k => c.coord ((f x)⁻¹) ⟨i.val,lt_trans i.isLt hk⟩))
          (fun i => by
            cases i with
            | inl i => exact hf _
            | inr i => exact ih i.val i.isLt (lt_trans i.isLt hk))
      apply ((hf j).neg.sub hq).congr
      intro x
      have he := c.mul_coord (f x) ((f x)⁻¹) j
      rw [mul_inv_cancel,c.one_coord] at he
      linarith
  intro j
  exact aux j.val j.isLt

open scoped commutatorElement
lemma IsPolyCoord.bracket {f g : (σ → ℝ) → G} (hf : IsPolyCoord c f) (hg : IsPolyCoord c g) :
    IsPolyCoord c (fun x => ⁅f x,g x⁆) := hf.mul c hg |>.mul c (hf.inv c) |>.mul c (hg.inv c)
end RationalLattice
end

end OAI
