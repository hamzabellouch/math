import OAI.Combinatorics.Progressions.Linear.PhysicalJetTentKernel

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_physicalJetTent_sampled_density (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ}, 0 ≤ P → (Fintype.card X : ℝ) ≤ P →
    (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P →
    ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
    ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (cover : ℕ) [NeZero cover],
    (cover : ℝ) ≤ Real.exp P → ∀ (stride : X → ℕ), (∀ x, 0 < stride x) →
    ∀ {R S ρ ε : ℝ}, 0 ≤ S → S ≤ Real.exp P → 0 < ρ → 0 < ε →
    1 / ρ ≤ Real.exp P → 1 / ε ≤ Real.exp P → (∀ x, (stride x : ℝ) ≤ S) →
    ∀ (H : X → ℝ), (∀ x, Real.exp ((P + A) ^ A) ≤ H x) →
    (∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j)) → Real.exp ((P + A) ^ A) ≤ R →
    ∀ (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)), cells.Nonempty →
    ∀ (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z),
    (∀ z, ρ * H z.2 ≤ V z) →
    ∀ {n : ℕ}, 0 < n → ∀ {δ L : ℝ}, 0 < δ → 0 ≤ L →
    (Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) J) : ℝ) ≤ L →
    (n : ℝ) ^ (Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) J) + 1) ≤ Real.exp L →
    δ⁻¹ ≤ Real.exp L → Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) *
      (2 * (n : ℝ) ^ Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) J)) ≤ Real.exp P →
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      ∀ y, |(selectedResidueFiniteLaw stride cells V hV hZ).mean (fun z =>
        physicalJetTentKernel U ν n
          (physicalCubeEuclideanSample U cover p hm (standardPhysicalCubeOutput z.val)) y) - 1| ≤ 2 * δ + ε := by
  obtain ⟨A, hA, htest⟩ := exists_physical_jet_density_mass m dim
  refine ⟨A, hA, ?_⟩
  intro X _ _ J _ P hP hnX hdim U _ _ _ μ _ _ ν _ _ p hp hm cover _ hcoverP
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth
    n hn δ L hδ hL hamb hLip hδL hfreqP hcoeffP
  have hlocal (y : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1))) :
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
        |selectedResidueDensityMass stride cells V (fun z => physicalJetTentKernel U ν n y
          (physicalCubeEuclideanSample U cover p hm (standardPhysicalCubeOutput z))) - 1| ≤ 2 * δ + ε := by
    obtain ⟨F, inst, frequency, c, hfreq, hsum, happrox⟩ :=
      exists_physicalJetTent_fourier U ν hn y hδ hL hamb hLip hδL
    let _ := inst
    have hkernel := physicalJetTentKernel_properties U ν hn y
    exact htest hP hnX hdim U μ ν (Real.exp_pos _).le hfreqP frequency hfreq c
      (by positivity) hcoeffP hsum p hp hm cover (Nat.pos_of_ne_zero (NeZero.ne cover)) hcoverP
      stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth
      (physicalJetTentKernel U ν n y) hkernel.2.1 hkernel.2.2.1 hδ.le happrox
  obtain ⟨hZ, _⟩ := hlocal 0
  refine ⟨hZ, ?_⟩
  intro y
  have hsym (z : Option (Fin dim) × X → ℤ) :
      physicalJetTentKernel U ν n
        (physicalCubeEuclideanSample U cover p hm (standardPhysicalCubeOutput z)) y =
      physicalJetTentKernel U ν n y
        (physicalCubeEuclideanSample U cover p hm (standardPhysicalCubeOutput z)) :=
    ambientTentKernel_symm _ _ _ _ _
  simp_rw [hsym]
  rw [selectedResidueFiniteLaw_densityMass stride cells V hV hZ
    (fun z => physicalJetTentKernel U ν n y
      (physicalCubeEuclideanSample U cover p hm (standardPhysicalCubeOutput z)))]
  exact (hlocal y).choose_spec

end Erdos3.BooleanCubeKernel

end

end OAI
