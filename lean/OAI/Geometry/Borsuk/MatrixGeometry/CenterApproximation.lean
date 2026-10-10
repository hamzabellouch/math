import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixCompression
import OAI.Geometry.Borsuk.MatrixGeometry.SymmetricEntries
import OAI.Geometry.Borsuk.MatrixGeometry.FibreContinuity
import OAI.Geometry.Borsuk.Projectors.CoordinateSum
import OAI.Geometry.Borsuk.Projectors.FiniteSmoothSliceMissesBounded

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section CenterApproximation
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "D" => EuclideanSpace ℝ (UpperTriangle (Fin k))
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "N" => Matrix (Fin k) (Fin k) ℝ
local notation "M" => Matrix (Fin (k+1)) (Fin (k+1)) ℝ
local notation "op" => Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)

lemma matrixFibre_range {u : E} (e : W →ₗᵢ[ℝ] E)
    (he : ∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) {Q : M} (hQ : Q ∈ matrixFibre u) :
    LinearMap.range (Matrix.toEuclideanLin Q) ≤ LinearMap.range e.toLinearMap := by
  rintro v ⟨b,rfl⟩
  obtain ⟨x,hx⟩ := he (op Q b) (matrix_image_orthogonal_kernel hQ.1.isSelfAdjoint hQ.2.2 b)
  exact ⟨x,hx⟩

lemma matrixCompress_mem_slice {u : E} (e : W →ₗᵢ[ℝ] E)
    (he : ∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) {Q : M} (hQ : Q ∈ matrixFibre u) :
    0 ≤ matrixCompress e Q ∧ Matrix.trace (matrixCompress e Q) = 1 :=
  ⟨matrixCompress_nonneg e hQ.1,
    (matrixCompress_trace e hQ.1.isSelfAdjoint (matrixFibre_range e he hQ)).trans hQ.2.1⟩

lemma Admissible.center_approximation {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)] {c : E}
    (hc : c ∈ safeNormals (activeVectors f I)) (e : W →ₗᵢ[ℝ] E)
    (he : ∀ x, ⟪c,e x⟫ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D → EuclideanSpace ℝ ↥(Iᶜ : Finset ι), ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, ∑ i, a x i = 1) ∧
      ∀ x, 0 ≤ symmetricCoordinates x → Matrix.trace (symmetricCoordinates x) = 1 →
        ‖a x - negativeCoordinates f I (matrixEmbed e (symmetricCoordinates x))‖ < ε := by
  let g : D → EuclideanSpace ℝ ↥(Iᶜ : Finset ι) :=
    fun x => negativeCoordinates f I (matrixEmbed e ((symmetricCoordinates x)⁺))
  have hP : Continuous (fun x : D => (symmetricCoordinates x)⁺) :=
    matrix_posPart_continuousOn.comp_continuous symmetricCoordinates.continuous_of_finiteDimensional
      (fun x => symmetricCoordinates_selfAdjoint x)
  have hg : Continuous g :=
    (hf.negativeCoordinates_continuousOn I).comp_continuous
      ((matrixEmbed e).continuous_of_finiteDimensional.comp hP)
      (fun x => matrixEmbed_nonneg e (CFC.posPart_nonneg _))
  let K : Set D := {x | 0 ≤ symmetricCoordinates x ∧ Matrix.trace (symmetricCoordinates x) = 1}
  have hs : ∀ x ∈ K, coordinateSum (g x) = 1 := by
    intro x hx
    change ∑ i, negativeCoordinates f I (matrixEmbed e ((symmetricCoordinates x)⁺)) i = 1
    rw [(CFC.posPart_eq_self _).mpr hx.1]
    apply hf.negativeCoordinates_sum hc
    exact ⟨matrixEmbed_nonneg _ hx.1,(matrixEmbed_trace _ _).trans hx.2,matrixEmbed_kernel e _ he⟩
  obtain ⟨a,ha,has,hae⟩ := continuous_simplex_approx g hg hs hε
  refine ⟨a,ha,has,?_⟩
  intro x hx ht
  have hh := hae x ⟨hx,ht⟩
  simpa only [g,(CFC.posPart_eq_self _).mpr hx] using hh

lemma Admissible.finite_center_approximations {κ : Type*} [Fintype κ]
    {f : E → ι → ℝ} (hf : Admissible f) {I : Finset ι}
    (hd : Fintype.card (UpperTriangle (Fin k)) < Fintype.card ↥(Iᶜ : Finset ι))
    (c : κ → E) (hc : ∀ j, c j ∈ safeNormals (activeVectors f I)) (hcn : ∀ j, ‖c j‖ = 1) :
    ∃ z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι), (∀ i, (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹ < z i) ∧
      (∑ i, z i) = 1 ∧
      ∃ g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι), (∀ j, Continuous (g j)) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), (∑ i, g j Q i) = 1) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ <
          (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹) ∧
        (∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) := by
  have hj : 0 < Fintype.card ↥(Iᶜ : Finset ι) := lt_of_le_of_lt (Nat.zero_le _) hd
  let : Nonempty ↥(Iᶜ : Finset ι) := Fintype.card_pos_iff.mp hj
  let ε : ℝ := (2*(Fintype.card ↥(Iᶜ : Finset ι):ℝ))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  choose e he hes using (fun j => orthogonal_frame k (hcn j))
  choose a ha has hae using (fun j => hf.center_approximation (hc j) (e j) (he j) hε)
  let L : D →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin k) ℝ ℝ).toContinuousLinearMap.comp
    (symmetricCoordinates (ν := Fin k)).toContinuousLinearMap
  have hendim : Module.finrank ℝ D < Fintype.card ↥(Iᶜ : Finset ι) := by simpa using hd
  obtain ⟨z,hzp,hzs,hzm⟩ := finite_smooth_slice_misses_general hendim (fun _ : κ => L) a ha
  let g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι) :=
    fun j Q => a j (symmetricEntries (matrixCompress (e j) Q))
  refine ⟨z,hzp,hzs,g,?_,?_,?_,?_⟩
  · intro j
    exact (ha j).continuous.comp (symmetricEntries.continuous_of_finiteDimensional.comp
      (matrixCompress (e j)).continuous_of_finiteDimensional)
  · intro j Q hQ
    exact has j _
  · intro j Q hQ
    have hCQ := matrixCompress_mem_slice (e j) (hes j) hQ
    have hSC := symmetricCoordinates_entries hCQ.1.isSelfAdjoint
    have hEQ := matrixEmbed_compress (e j) hQ.1.isSelfAdjoint (matrixFibre_range (e j) (hes j) hQ)
    have hh := hae j (symmetricEntries (matrixCompress (e j) Q))
      (by rw [hSC]; exact hCQ.1) (by rw [hSC]; exact hCQ.2)
    simpa only [hSC,hEQ,g,ε] using hh
  · intro j Q hQ
    apply hzm j _
    change Matrix.trace (symmetricCoordinates (symmetricEntries (matrixCompress (e j) Q))) = 1
    have hCQ := matrixCompress_mem_slice (e j) (hes j) hQ
    rw [symmetricCoordinates_entries hCQ.1.isSelfAdjoint]
    exact hCQ.2

end CenterApproximation
end BorsukNine

end OAI
