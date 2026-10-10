import OAI.Geometry.Immersion.ClosedSurface.GeometryBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open Set

def FreeBudget.mono_order {F : RField 4} {φ ψ : Base → ℝ} {S : Set Base}
    {c : SupportedFreeChart F φ ψ S} {u : Base → ℝ} {τ s : ℝ} {q m r : ℕ}
    (b : FreeBudget c u τ s q m) (hr : r ≤ m) : FreeBudget c u τ s q r where
  K := b.K
  C := b.C
  N := b.N
  J := b.J
  D := b.D
  nonnegK := b.nonnegK
  nonnegC := b.nonnegC
  nonnegN := b.nonnegN
  oneLEJ := b.oneLEJ
  nonnegD := b.nonnegD
  smoothAmplitude := b.smoothAmplitude
  coefficients := b.coefficients.mono_order (by omega)
  amplitude := b.amplitude.mono_order (by omega)
  normal := b.normal.mono_order (by omega)
  coordinate := fun j hj hle => b.coordinate j hj (hle.trans hr)
  coordinateDerivative := fun v hv => (b.coordinateDerivative v hv).mono_order hr

def ForcedGeometryBudget.sizeFactor {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    {c : SupportedSolveChart F φ S} {τ s : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) : ℝ :=
  (m.factorial : ℝ) * (2 ^ m * (forcedModeConstant n m b.K q * b.forcingFactor)) * b.J ^ m

def ForcedGeometryBudget.errorFactor {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    {c : SupportedSolveChart F φ S} {τ s : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) : ℝ :=
  4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) *
    (2 ^ m * (fullErrorConstant n (m + q) b.K ^ (q + 1) * b.forcingFactor)) *
    b.J ^ m) * b.D) * b.D)

lemma ForcedGeometryBudget.sizeFactor_nonneg {n : ℕ} {F : RField n}
    {φ : Base → ℝ} {S : Set Base} {c : SupportedSolveChart F φ S} {τ s : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) : 0 ≤ b.sizeFactor := by
  have hc := forcedModeConstant_nonneg n m q b.nonnegK
  have hj := zero_le_one.trans b.oneLEJ
  have hf := b.forcingFactor_nonneg
  unfold ForcedGeometryBudget.sizeFactor
  positivity

lemma ForcedGeometryBudget.errorFactor_nonneg {n : ℕ} {F : RField n}
    {φ : Base → ℝ} {S : Set Base} {c : SupportedSolveChart F φ S} {τ s : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) : 0 ≤ b.errorFactor := by
  have hc := fullErrorConstant_nonneg n (m + q) b.nonnegK
  have hj := zero_le_one.trans b.oneLEJ
  have hf := b.forcingFactor_nonneg
  have hd := b.nonnegD
  unfold ForcedGeometryBudget.errorFactor
  positivity

lemma ForcedGeometryBudget.toSolveBudget_size {n : ℕ} {F : RField n}
    {φ : Base → ℝ} {S : Set Base} {c : SupportedSolveChart F φ S} {τ s C : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {A : Base → ComplexTensor} (hA : ContDiff ℝ ∞ A)
    (hbA : WeightedBound univ s (m + q + 1) C A) :
    (b.toSolveBudget hs hs1 hC hA hbA).size = b.sizeFactor * C := by
  dsimp [SolveBudget.size, ForcedGeometryBudget.toSolveBudget, ForcedGeometryBudget.sizeFactor]
  ring

lemma ForcedGeometryBudget.toSolveBudget_residual {n : ℕ} {F : RField n}
    {φ : Base → ℝ} {S : Set Base} {c : SupportedSolveChart F φ S} {τ s C : ℝ} {q m : ℕ}
    (b : ForcedGeometryBudget c τ s q m) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {A : Base → ComplexTensor} (hA : ContDiff ℝ ∞ A)
    (hbA : WeightedBound univ s (m + q + 1) C A) :
    (b.toSolveBudget hs hs1 hC hA hbA).residual =
      b.errorFactor * (τ / s) ^ (q + 1) * C := by
  dsimp [SolveBudget.residual, ForcedGeometryBudget.toSolveBudget, ForcedGeometryBudget.errorFactor]
  ring




theorem constructed_quadratic_correction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {φ ψ u : ι → Base → ℝ} {S : ι → Set Base}
    (c : ∀ i, SupportedFreeChart F (φ i) (ψ i) (S i))
    (d : ∀ l : QuadraticLabel ι, SupportedSolveChart F (quadraticPhase φ l) (quadraticSupport S l))
    {τ s P : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hP : 0 ≤ P) (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (q r m : ℕ)
    (b : ∀ i, FreeBudget (c i) (u i) τ s q (m + r + 1 + 1))
    (g : ∀ l, ForcedGeometryBudget (d l) τ s r m)
    (hpφ : ∀ i v, ‖v‖ ≤ 1 → WeightedBound univ s (m + r + 1) P (coordDeriv v (φ i))) :
    ∃ B R : ℝ, 0 ≤ B ∧ 0 ≤ R ∧ ∀ δ : ℝ, 0 ≤ δ →
      let Z := fun i => (c i).amplitude (u i) δ τ q
      let V := fun p => ∑ l, (d l).solve τ (quadraticAmplitude τ φ Z l) r p
      ContDiff ℝ ∞ V ∧ tsupport V ⊆ ⋃ i, S i ∧
      WeightedBound univ τ m (B * δ ^ 2) V ∧
      WeightedBound univ τ m (R * (τ / s) ^ (r + 1) * δ ^ 2)
        (fun p => realLinearizedTensor F V p + nonzeroPhaseSum τ φ Z p) := by
  classical
  let Q : ℝ := 4 * 2 ^ (m + r + 1) * ((1 + 2 ^ (m + r + 1) * P) * ∑ i, (b i).slowSize) ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨(∑ l, (g l).sizeFactor) * Q, (∑ l, (g l).errorFactor) * Q,
    mul_nonneg (Finset.sum_nonneg fun l _ => (g l).sizeFactor_nonneg) hQ,
    mul_nonneg (Finset.sum_nonneg fun l _ => (g l).errorFactor_nonneg) hQ, ?_⟩
  intro δ hδ
  dsimp only
  let Z := fun i => (c i).amplitude (u i) δ τ q
  have hZ (i) := (c i).amplitude_smooth (b i).smoothAmplitude δ τ q
  have hbA := weighted_free_quadraticAmplitude c hδ hτ hs hτs hs1 hP hφ b hpφ
  have hA := quadraticAmplitude_smooth hφ (fun i => (hZ i).1) τ
  let budget := fun l => (g l).toSolveBudget hs hs1 (mul_nonneg hQ (sq_nonneg δ)) (hA l) (hbA l)
  obtain ⟨hsm, hsp, hsize, hres⟩ := finite_quadratic_cancellation hF hφ
    (fun i => (hZ i).1) (fun i => (hZ i).2) d hτ hs hτs hs1 r m budget
  refine ⟨hsm, hsp, ?_, ?_⟩
  · have he : (∑ l, (budget l).size) = ((∑ l, (g l).sizeFactor) * Q) * δ ^ 2 := by
      simp only [budget, ForcedGeometryBudget.toSolveBudget_size, ← Finset.sum_mul]
      ring
    rwa [he] at hsize
  · have he : (∑ l, (budget l).residual) =
        ((∑ l, (g l).errorFactor) * Q) * (τ / s) ^ (r + 1) * δ ^ 2 := by
      simp only [budget, ForcedGeometryBudget.toSolveBudget_residual, ← Finset.sum_mul]
      ring
    rwa [he] at hres

end ClosedSurfaceR4.RealModes

end

end OAI
