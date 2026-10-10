import OAI.Analysis.KadisonKastler.FiniteCenter
import OAI.Analysis.KadisonKastler.FiniteNeighbor
import OAI.Analysis.FactorGeneration.Subfactors

namespace OAI

/-! # Recovering scalar centre from central projections

The centre is represented as the intersection with the concrete commutant.
Spectral approximation in this von Neumann algebra reduces scalarity of its
whole algebra to triviality of its projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The intersection of two concrete von Neumann algebras. -/
def vonNeumannIntersection (M N : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := M.toStarSubalgebra ⊓ N.toStarSubalgebra
  centralizer_centralizer' := by
    apply Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
    intro x hx
    constructor
    · have h : Set.centralizer (Set.centralizer
          ((M.toStarSubalgebra ⊓ N.toStarSubalgebra : StarSubalgebra ℂ (H →L[ℂ] H)) :
            Set (H →L[ℂ] H))) ⊆ Set.centralizer (Set.centralizer (M : Set (H →L[ℂ] H))) :=
        Set.centralizer_subset (Set.centralizer_subset (fun _ hy => hy.1))
      exact M.centralizer_centralizer ▸ h hx
    · have h : Set.centralizer (Set.centralizer
          ((M.toStarSubalgebra ⊓ N.toStarSubalgebra : StarSubalgebra ℂ (H →L[ℂ] H)) :
            Set (H →L[ℂ] H))) ⊆ Set.centralizer (Set.centralizer (N : Set (H →L[ℂ] H))) :=
        Set.centralizer_subset (Set.centralizer_subset (fun _ hy => hy.2))
      exact N.centralizer_centralizer ▸ h hx

/-- The concrete centre, retaining its von Neumann structure. -/
def concreteCenter (N : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  vonNeumannIntersection N N.commutant

/-- Spectral approximation upgrades trivial central projections to scalar
centre. No finiteness or trace is needed for this upgrade. -/
theorem scalar_center_of_trivial_central_projections (N : VonNeumannAlgebra H)
    (hproj : ∀ q : Algebra N, IsStarProjection q →
      (∀ a : Algebra N, a * q = q * a) → q = 0 ∨ q = 1)
    (c : Algebra N) (hc : ∀ a : Algebra N, a * c = c * a) :
    ∃ z : ℂ, c = z • (1 : Algebra N) := by
  let C := concreteCenter N
  let inc : Algebra C →⋆ₐ[ℂ] Algebra N := StarSubalgebra.inclusion (show
      C.toStarSubalgebra ≤ N.toStarSubalgebra from fun _ hx => hx.1)
  have hinj : Function.Injective inc := StarSubalgebra.inclusion_injective _
  let cC : Algebra C := ⟨c.val, c.property, by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact congrArg Subtype.val (hc ⟨a, ha⟩)⟩
  let p : Generator.Tracial.AlgebraProjection C := ⟨1, IsStarProjection.one _⟩
  have hmin : ∀ q : Generator.Tracial.AlgebraProjection C, q ≤ p → q.val = 0 ∨ q.val = p.val := by
    intro q _
    have hq : IsStarProjection (inc q.val) := q.property.map inc
    have hqc : ∀ a : Algebra N, a * inc q.val = inc q.val * a := by
      intro a
      apply Subtype.ext
      exact VonNeumannAlgebra.mem_commutant_iff.mp q.val.property.2 a.val a.property
    rcases hproj (inc q.val) hq hqc with h | h
    · left
      apply hinj
      change inc q.val = inc 0
      rw [map_zero]
      exact h
    · right
      apply hinj
      change inc q.val = inc 1
      rw [map_one]
      exact h
  obtain ⟨z, hz⟩ := Generator.Tracial.corner_scalar_of_projections p hmin cC
    (by change 1 * cC = cC; exact one_mul _) (by change cC * 1 = cC; exact mul_one _)
  refine ⟨z, ?_⟩
  have he := congrArg (fun x : Algebra C => (x : H →L[ℂ] H)) hz
  exact Subtype.ext he

/-- The nearby algebra has scalar centre; the faithful trace is constructed
from the given concrete II₁ factor. -/
theorem scalar_center_of_near_II1 {M N : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hgap : kkDistance M N < 1 / 10) :
    ∀ c : Algebra N, (∀ a : Algebra N, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra N) := by
  apply scalar_center_of_trivial_central_projections
  intro q hq hqc
  exact central_projection_trivial_of_near (concreteTraceEmbedding hM)
    (concreteTraceEmbedding_norm hM) (concreteFactorTrace_finiteVector hM)
    (fun b hb => by
      obtain ⟨c, hc⟩ := hM.factor b hb
      exact ⟨c, by simpa only [Algebra.algebraMap_eq_smul_one] using hc⟩)
    hgap q hq hqc


/-- The full finite-neighbor conclusion for an initial II₁ factor: the
nearby algebra is finite and has scalar centre. -/
theorem finite_factor_of_near_II1 {M N : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hgap : kkDistance M N < 1 / 10) :
    (∀ c : Algebra N, (∀ a : Algebra N, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra N)) ∧
    (∀ v : Algebra N, star v * v = 1 → v * star v = 1) := by
  refine ⟨scalar_center_of_near_II1 hM hgap, ?_⟩
  exact finite_of_near_finite_factor (fun c hc => by
    obtain ⟨z, hz⟩ := hM.factor c hc
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩) hM.finite hgap

end

end KadisonKastler

end OAI
