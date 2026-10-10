import OAI.Geometry.Immersion.ClosedSurface.JetBounds
import OAI.Geometry.Immersion.ClosedSurface.TensorBounds
import OAI.Geometry.Immersion.ClosedSurface.ExtendedCancellation
import OAI.Geometry.Immersion.ClosedSurface.QuadraticSupport

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter

lemma contDiffOn_displacement {n : ℕ} {U : Set Base} {φ : Base → ℝ} {Z : Field n}
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (displacement τ φ Z) U := by
  have he : ContDiffOn ℝ ∞ (fun p => QuadraticMean.phase (φ p / τ)) U := by
    exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hφ.div_const τ)).mul contDiffOn_const).cexp
  exact (QuadraticMean.realPartCLM n).contDiff.comp_contDiffOn (he.smul hZ)



structure SupportedSolveChart {n : ℕ} (F : RField n) (φ : Base → ℝ) (S : Set Base) where
  U : Set Base
  V : Set Base
  χ : Base → Base
  e : Base → Base
  openU : IsOpen U
  closedS : IsClosed S
  supportU : S ⊆ U
  smoothFe : ContDiff ℝ ∞ (F ∘ e)
  domain : ModeDomain (fun p => complexify (F (e p))) V
  smoothχ : ContDiffOn ℝ ∞ χ U
  smoothe : ContDiffOn ℝ ∞ e V
  maps : MapsTo χ U V
  inverse : EqOn (e ∘ χ) id U
  phase : ∀ p ∈ U, (χ p).1 = φ p

def SupportedSolveChart.solve {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    (c : SupportedSolveChart F φ S) (τ : ℝ) (A : Base → ComplexTensor) (q : ℕ) : RField n :=
  c.U.indicator (phaseCanceller τ F c.χ c.e A q)



structure SolveBudget {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    (c : SupportedSolveChart F φ S) (A : Base → ComplexTensor) (τ s : ℝ) (q m : ℕ) where
  K : ℝ
  C : ℝ
  J : ℝ
  D : ℝ
  nonnegK : 0 ≤ K
  nonnegC : 0 ≤ C
  oneLEJ : 1 ≤ J
  nonnegD : 0 ≤ D
  smoothA : ContDiffOn ℝ ∞ (coordinateTarget c.e A) c.V
  coefficients : ReconstructionCoefficientBound (fun p => complexify (F (c.e p)))
    c.V s (m + q + 1) K
  forcing : WeightedBound c.V s (m + q + 1) C (coordinateTarget c.e A)
  coordinate : ∀ j, 1 ≤ j → j ≤ m → ∀ p ∈ c.U,
    ‖iteratedFDerivWithin ℝ j c.χ c.U p‖ ≤ J
  coordinateDerivative : ∀ v, ‖v‖ ≤ 1 → WeightedBound c.U τ m D (coordDeriv v c.χ)

def SolveBudget.size {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    {c : SupportedSolveChart F φ S} {A : Base → ComplexTensor} {τ s : ℝ} {q m : ℕ}
    (b : SolveBudget c A τ s q m) : ℝ :=
  (m.factorial : ℝ) * (2 ^ m * (forcedModeConstant n m b.K q * b.C)) * b.J ^ m

def SolveBudget.residual {n : ℕ} {F : RField n} {φ : Base → ℝ} {S : Set Base}
    {c : SupportedSolveChart F φ S} {A : Base → ComplexTensor} {τ s : ℝ} {q m : ℕ}
    (b : SolveBudget c A τ s q m) : ℝ :=
  4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) *
    (2 ^ m * (fullErrorConstant n (m + q) b.K ^ (q + 1) * (τ / s) ^ (q + 1) * b.C)) *
    b.J ^ m) * b.D) * b.D)

theorem SupportedSolveChart.solve_spec {n : ℕ} {F : RField n} {φ : Base → ℝ}
    {S : Set Base} (c : SupportedSolveChart F φ S) (hF : ContDiff ℝ ∞ F)
    {A : Base → ComplexTensor} (hAsp : tsupport A ⊆ S)
    {τ s : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    {q m : ℕ} (b : SolveBudget c A τ s q m) :
    ContDiff ℝ ∞ (c.solve τ A q) ∧ tsupport (c.solve τ A q) ⊆ S ∧
    WeightedBound univ τ m b.size (c.solve τ A q) ∧
    WeightedBound univ τ m b.residual
      (fun p => realLinearizedTensor F (c.solve τ A q) p + displacement τ φ A p) := by
  have hh := weighted_extended_phaseCanceller c.smoothFe c.openU c.domain c.closedS c.supportU
    c.smoothχ c.smoothe c.maps c.inverse hF.contDiffOn hAsp hτ hs hτs hs1
    b.nonnegK b.nonnegC b.oneLEJ b.nonnegD b.smoothA q m b.coefficients b.forcing
    b.coordinate b.coordinateDerivative
  dsimp only at hh
  refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
  have he : displacement τ (fun p => (c.χ p).1) A = displacement τ φ A := by
    funext p
    by_cases hp : p ∈ c.U
    · simp only [displacement, c.phase p hp]
    · have hz : A p = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hp (c.supportU (hAsp hh)))
      rw [displacement_zero_value τ _ hz, displacement_zero_value τ _ hz]
  simpa only [he, SupportedSolveChart.solve, SolveBudget.residual] using hh.2.2.2



theorem finite_forced_solve {n : ℕ} {ι : Type*} [Fintype ι]
    {F : RField n} (hF : ContDiff ℝ ∞ F) {φ : ι → Base → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) {A : ι → Base → ComplexTensor}
    (hA : ∀ i, ContDiff ℝ ∞ (A i)) {S : ι → Set Base}
    (hAsp : ∀ i, tsupport (A i) ⊆ S i) (c : ∀ i, SupportedSolveChart F (φ i) (S i))
    {τ s : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (q m : ℕ) (b : ∀ i, SolveBudget (c i) (A i) τ s q m) :
    let X := fun p => ∑ i, (c i).solve τ (A i) q p
    ContDiff ℝ ∞ X ∧ tsupport X ⊆ ⋃ i, S i ∧
    WeightedBound univ τ m (∑ i, (b i).size) X ∧
    WeightedBound univ τ m (∑ i, (b i).residual)
      (fun p => realLinearizedTensor F X p + ∑ i, displacement τ (φ i) (A i) p) := by
  classical
  dsimp only
  have hh (i) := (c i).solve_spec hF (hAsp i) hτ hs hτs hs1 (b i)
  have hsm := fun i => (hh i).1
  refine ⟨ContDiff.sum fun i _ => hsm i, ?_, ?_, ?_⟩
  · apply closure_minimal _ (isClosed_iUnion_of_finite fun i => (c i).closedS)
    intro p hp
    by_contra hn
    apply hp
    apply Finset.sum_eq_zero
    intro i _
    exact image_eq_zero_of_notMem_tsupport
      (fun hh' => hn (mem_iUnion.mpr ⟨i, (hh i).2.1 hh'⟩))
  · exact WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => (hsm i).contDiffOn) (fun i _ => (hh i).2.2.1)
  · have he (p) : realLinearizedTensor F (fun x => ∑ i, (c i).solve τ (A i) q x) p +
        ∑ i, displacement τ (φ i) (A i) p =
        ∑ i, (realLinearizedTensor F ((c i).solve τ (A i) q) p +
          displacement τ (φ i) (A i) p) := by
      rw [realLinearized_sum_right F (fun i => (hsm i).differentiable (by simp) p)]
      exact (Finset.sum_add_distrib).symm
    simp_rw [he]
    exact WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ _ _
      (fun i _ => (contDiffOn_realLinearizedTensor isOpen_univ hF.contDiffOn
        (hsm i).contDiffOn).add (contDiffOn_displacement (hφ i).contDiffOn (hA i).contDiffOn τ))
      (fun i _ => (hh i).2.2.2)

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter

lemma quadraticPhase_smooth {ι : Type*} {φ : ι → Base → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) :
    ∀ l : QuadraticLabel ι, ContDiff ℝ ∞ (quadraticPhase φ l) := by
  intro l
  rcases l with i | ⟨i, j, b⟩
  · exact contDiff_const.mul (hφ i)
  · cases b
    · exact (hφ i).add (hφ j)
    · exact (hφ i).sub (hφ j)




theorem finite_quadratic_cancellation {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : RField n} (hF : ContDiff ℝ ∞ F) {φ : ι → Base → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) {Z : ι → Field n}
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i)) {S : ι → Set Base}
    (hZsp : ∀ i, tsupport (Z i) ⊆ S i)
    (c : ∀ l : QuadraticLabel ι, SupportedSolveChart F (quadraticPhase φ l) (quadraticSupport S l))
    {τ s : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (q m : ℕ) (b : ∀ l, SolveBudget (c l) (quadraticAmplitude τ φ Z l) τ s q m) :
    let V := fun p => ∑ l, (c l).solve τ (quadraticAmplitude τ φ Z l) q p
    ContDiff ℝ ∞ V ∧ tsupport V ⊆ ⋃ i, S i ∧
    WeightedBound univ τ m (∑ l, (b l).size) V ∧
    WeightedBound univ τ m (∑ l, (b l).residual)
      (fun p => realLinearizedTensor F V p + nonzeroPhaseSum τ φ Z p) := by
  classical
  dsimp only
  obtain ⟨hsm, hsp, hb, hr⟩ := finite_forced_solve hF (quadraticPhase_smooth hφ)
    (quadraticAmplitude_smooth hφ hZ τ) (quadraticAmplitude_tsupport τ φ Z hZsp)
    c hτ hs hτs hs1 q m b
  refine ⟨hsm, hsp.trans ?_, hb, ?_⟩
  · intro p hp
    obtain ⟨l, hl⟩ := mem_iUnion.mp hp
    rcases l with i | ⟨i, j, b⟩
    · exact mem_iUnion.mpr ⟨i, hl⟩
    · exact mem_iUnion.mpr ⟨i, hl.1⟩
  · simpa only [nonzeroPhaseSum_eq_quadraticFamily] using hr

end ClosedSurfaceR4.RealModes

end

end OAI
