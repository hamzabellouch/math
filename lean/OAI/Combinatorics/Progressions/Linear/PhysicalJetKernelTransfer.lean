import OAI.Combinatorics.Progressions.Sampling.PhysicalJetTentSampling

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {X : Type*} [Fintype X]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))

theorem physicalJetTent_transfer
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (cover : ℕ) [NeZero cover] (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride))
    (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z) {n : ℕ} (hn : 0 < n) :
    let sample := fun z : Option (Fin dim) × X → ℤ =>
      physicalCubeEuclideanSample U cover p hm (standardPhysicalCubeOutput z)
    let law := selectedResidueFiniteLaw stride cells V hV hZ
    ∀ {err : ℝ}, err ≤ 1 →
    (∀ y, |law.mean (fun z => physicalJetTentKernel U ν n (sample z.val) y) - 1| ≤ err) →
    ∀ (φ : EuclideanJetLayers U jets → ℂ), Integrable φ haar →
    ∀ (ψ : (JetAmbientIndex jets J → UnitAddCircle) → ℂ) {L : ℝ≥0}, LipschitzWith L ψ →
    Integrable (fun y => ψ (coveredJetAmbientTorus U 1 y)) haar →
    ∀ F : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖F z‖ ≤ 1) →
    let obs := finiteKernelObservable law (fun z => physicalJetTentKernel U ν n (sample z.val)) 2 (fun z => F z.val)
    Measurable obs ∧ (∀ y, ‖obs y‖ ≤ 1) ∧ Integrable (fun y => φ y * obs y) haar ∧
      ‖(∑' z, ((selectedResidueSmoothPMF stride cells V hV hZ z).toReal : ℂ) *
          (φ (sample z) * F z)) - (∫ y, φ y * obs y ∂haar) * 2‖ ≤
        selectedResidueDensityMass stride cells V
          (fun z => ‖φ (sample z) - ψ (coveredJetAmbientTorus U 1 (sample z))‖) +
        (L : ℝ) * (4 / (n : ℝ)) + 2 * ∫ y, ‖ψ (coveredJetAmbientTorus U 1 y) - φ y‖ ∂haar := by
  intro sample law err herr hclose φ hφ ψ L hL hψ F hF obs
  let : ∀ j, (Measure.pi (fun _ : jets j => ν j)).IsAddLeftInvariant :=
    fun _ => Measure.pi.isAddLeftInvariant _
  let : (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))).IsAddLeftInvariant :=
    Measure.pi.isAddLeftInvariant _
  let : MeasurableAdd₂ (EuclideanJetLayers U jets) :=
    ⟨(continuous_fst.add continuous_snd).measurable⟩
  let f := coveredJetAmbientHom (O := jets) U 1
  have hf : Continuous f := coveredJetAmbientTorus_continuous U 1
  have hden (y) : law.mean (fun z => ambientTentKernel haar f n (sample z.val) y) ≤ 2 := by
    have h := (abs_le.mp (hclose y)).2
    change law.mean (fun z => ambientTentKernel haar f n (sample z.val) y) - 1 ≤ err at h
    linarith only [h, herr]
  obtain ⟨hobs, hbound, hint, herror⟩ := finiteAmbientKernel_transfer haar f hf hn law
    (fun z => sample z.val) (by norm_num : (0 : ℝ) < 2) hden φ hφ ψ hL hψ
    (fun z => F z.val) (fun z => hF z.val)
  refine ⟨hobs, hbound, hint, ?_⟩
  have hfeq (y : EuclideanJetLayers U jets) : f y = coveredJetAmbientTorus U 1 y := rfl
  simp_rw [hfeq] at herror
  change ‖(selectedResidueFiniteLaw stride cells V hV hZ).complexMean
      (fun z => φ (sample z.val) * F z.val) - (∫ y, φ y * obs y ∂haar) * 2‖ ≤
    (selectedResidueFiniteLaw stride cells V hV hZ).mean
      (fun z => ‖φ (sample z.val) - ψ (coveredJetAmbientTorus U 1 (sample z.val))‖) +
      (L : ℝ) * (4 / (n : ℝ)) + 2 * ∫ y, ‖ψ (coveredJetAmbientTorus U 1 y) - φ y‖ ∂haar at herror
  rw [selectedResidueFiniteLaw_complexMean stride cells V hV hZ (fun z => φ (sample z) * F z),
    selectedResidueFiniteLaw_densityMass stride cells V hV hZ
      (fun z => ‖φ (sample z) - ψ (coveredJetAmbientTorus U 1 (sample z))‖)] at herror
  exact herror

end Erdos3.BooleanCubeKernel

end

end OAI
