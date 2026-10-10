import OAI.Geometry.Immersion.ClosedSurface.ExplicitIncrement

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open Set
open ClosedSurfaceR4.QuadraticMean (sumDisplacement displacement)


def FreeBudget.shrink {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    {c : SupportedFreeChart F φ ψ S} {u : Base → ℝ} {τ t s : ℝ} {q m : ℕ}
    (b : FreeBudget c u τ s q m) (ht : 0 ≤ t) (htτ : t ≤ τ) :
    FreeBudget c u t s q m :=
  { b with coordinateDerivative := fun v hv => (b.coordinateDerivative v hv).shrink_scale ht htτ }

def ForcedGeometryBudget.shrink {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    {c : SupportedSolveChart F φ S} {τ t s : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) (ht : 0 ≤ t) (htτ : t ≤ τ) :
    ForcedGeometryBudget c t s q m :=
  { b with coordinateDerivative := fun v hv => (b.coordinateDerivative v hv).shrink_scale ht htτ }

lemma FreeBudget.factors_eq {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    {c : SupportedFreeChart F φ ψ S} {u u' : Base → ℝ} {τ τ' s s' : ℝ} {q m : ℕ}
    (b : FreeBudget c u τ s q m) (b' : FreeBudget c u' τ' s' q m)
    (hK : b.K = b'.K) (hC : b.C = b'.C) (hN : b.N = b'.N)
    (hJ : b.J = b'.J) (hD : b.D = b'.D) {r : ℕ} (hr : r ≤ m) :
    b.slowSize = b'.slowSize ∧ (b.mono_order hr).size = (b'.mono_order hr).size ∧
      (b.mono_order hr).errorFactor = (b'.mono_order hr).errorFactor := by
  simp only [FreeBudget.slowSize, FreeBudget.mono_order, FreeBudget.size,
    FreeBudget.errorFactor, FreeBudget.seedConstant, hK, hC, hN, hJ, hD, and_self]



theorem constructed_finite_increment_uniform {ι α : Type*} [Fintype ι] [DecidableEq ι]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {φ ψ : ι → Base → ℝ}
    {u : α → ι → Base → ℝ} {S : ι → Set Base}
    (c : ∀ i, SupportedFreeChart F (φ i) (ψ i) (S i))
    (d : ∀ l : QuadraticLabel ι, SupportedSolveChart F (quadraticPhase φ l) (quadraticSupport S l))
    {s P : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hP : 0 ≤ P)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (q m : ℕ) (a₀ : α)
    (b : ∀ a i, FreeBudget (c i) (u a i) s s q (m + 1 + q + 1 + 1))
    (g : ∀ l, ForcedGeometryBudget (d l) s s q (m + 1))
    (hnum : ∀ a i, (b a i).K = (b a₀ i).K ∧ (b a i).C = (b a₀ i).C ∧
      (b a i).N = (b a₀ i).N ∧ (b a i).J = (b a₀ i).J ∧ (b a i).D = (b a₀ i).D)
    (hpφ : ∀ i v, ‖v‖ ≤ 1 → WeightedBound univ s (m + 1 + q + 1) P (coordDeriv v (φ i))) :
    ∃ C E T : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ 0 ≤ T ∧
      ∀ a : α, ∀ τ : ℝ, 0 < τ → τ ≤ s → ∀ δ : ℝ, 0 ≤ δ → δ ≤ τ →
      let Z := fun i => (c i).amplitude (u a i) δ τ q
      let X := sumDisplacement τ φ Z
      let V := fun p => ∑ l, (d l).solve τ (quadraticAmplitude τ φ Z l) q p
      let U := fun p => X p + V p
      ContDiff ℝ ∞ U ∧ tsupport U ⊆ ⋃ i, S i ∧
      WeightedBound univ τ m (C * (δ * τ)) U ∧
      WeightedBound univ τ m (E * δ * (τ / s) ^ (q + 1) + T * (δ ^ 3 / τ))
        (fun p => realMetricTensor (fun x => F x + U x) p - realMetricTensor F p - zeroPhaseSum τ φ Z p) := by
  classical
  let low := fun i => (b a₀ i).mono_order (r := m + 1) (by omega)
  let A : ℝ := ∑ i, (low i).size
  let L : ℝ := ∑ i, (low i).errorFactor
  let Q : ℝ := 4 * 2 ^ (m + 1 + q + 1) * ((1 + 2 ^ (m + 1 + q + 1) * P) * ∑ i, (b a₀ i).slowSize) ^ 2
  let B := (∑ l, (g l).sizeFactor) * Q
  let R := (∑ l, (g l).errorFactor) * Q
  have hbase := constructed_finite_increment_explicit hF c d hs hs le_rfl hs1 hP hφ q m (b a₀) g hpφ
  refine ⟨A + B, L + R, 4 * 2 ^ m * (2 * A * B + B ^ 2),
    hbase.1, hbase.2.1, hbase.2.2.1, ?_⟩
  intro a τ hτ hτs
  let bt := fun i => (b a i).shrink hτ.le hτs
  let gt := fun l => (g l).shrink hτ.le hτs
  have he (i) := (bt i).factors_eq (b a₀ i) (hnum a i).1 (hnum a i).2.1
    (hnum a i).2.2.1 (hnum a i).2.2.2.1 (hnum a i).2.2.2.2 (r := m + 1) (by omega)
  have hh := constructed_finite_increment_explicit hF c d hτ hs hτs hs1 hP hφ q m bt gt hpφ
  dsimp only at hh
  simp only [he, ForcedGeometryBudget.sizeFactor,
    ForcedGeometryBudget.errorFactor, ForcedGeometryBudget.forcingFactor] at hh
  exact hh.2.2.2

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude zeroPair)
open ClosedSurfaceR4.RootMean
open Set Filter

lemma phaseZeroTensor_congr_left {n : ℕ} (τ : ℝ) (Z : Field n)
    {φ ψ : Base → ℝ} {p : Base} (he : φ =ᶠ[nhds p] ψ) :
    phaseZeroTensor τ φ Z p = phaseZeroTensor τ ψ Z p := by
  ext i
  simp only [phaseZeroTensor, derivativeAmplitude, he.fderiv_eq]



lemma phaseZeroTensor_supported_phase {n : ℕ} {U S : Set Base} (hU : IsOpen U)
    (hSU : S ⊆ U) {φ ψ : Base → ℝ} (he : EqOn φ ψ U)
    {Z : Field n} (hZ : tsupport Z ⊆ S) (τ : ℝ) :
    phaseZeroTensor τ φ Z = phaseZeroTensor τ ψ Z := by
  funext p
  by_cases hp : p ∈ U
  · exact phaseZeroTensor_congr_left τ Z
      (Filter.Eventually.mono (hU.mem_nhds hp) fun z hz => he hz)
  · have hn : p ∉ tsupport Z := fun hz => hp (hSU (hZ hz))
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    rw [phaseZeroTensor_congr_right τ φ hz, phaseZeroTensor_congr_right τ ψ hz]
    change phaseZeroTensor τ φ (fun _ => 0) p = phaseZeroTensor τ ψ (fun _ => 0) p
    rw [phaseZeroTensor_zero, phaseZeroTensor_zero]

lemma SupportedFreeChart.mean_phase {F : RField 4} {φ ψ u : Base → ℝ} {S : Set Base}
    (c : SupportedFreeChart F φ ψ S) (hu : ContDiffOn ℝ ∞ (phaseAmplitude ψ u) c.V)
    (δ τ : ℝ) (q : ℕ) :
    phaseZeroTensor τ φ (c.amplitude u δ τ q) =
      phaseZeroTensor τ (fun p => (c.χ p).1) (c.amplitude u δ τ q) := by
  exact phaseZeroTensor_supported_phase c.openU c.supportU
    (fun p hp => (c.phase p hp).symm) (c.amplitude_smooth hu δ τ q).2 τ

end ClosedSurfaceR4.RealModes

end

end OAI
