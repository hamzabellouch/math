import OAI.Analysis.CircleDomains.Sobolev.ModelRealEnergy
import OAI.Analysis.CircleDomains.Transfer.ModelRealTerminals
import OAI.Analysis.CircleDomains.Transfer.RealTransferStage

namespace OAI

/-! The real part of a mixed model satisfies the existing real-stage
interface. Its map and metric are the same ones used by its period tests. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def ModelRealSubfamily.realTransferStage
    {S I : Type*} [Fintype I] {n m N : ℕ}
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {A Flag : Set S} [Fintype A] (hA : A.Finite) (hFlag : Flag ⊆ A)
    {O : S → Set Sphere}
    (D : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : A => σ s) (fun s => O s))
    {H : I → ℂ ≃ₜ ℂ} {K K₀ : Set (ℝ × ℝ)}
    {M : Fin n → Set (ℝ × ℝ)} {f : Fin n → (ℝ × ℝ) → UnitAddCircle}
    {χ : (ℝ × ℝ) → ℝ} {θ : Fin n → ℝ} {ε : ℝ}
    {Q : MaskedModelData D.H H (realChartDomain G) K M f χ N θ ε}
    {ι : Fin m → Fin n} {r : Fin m → (ℝ × ℝ) → ℝ}
    (W : ModelRealSubfamily Q ι r)
    (hG : IsOpen G) (hK : IsClosed K) (hK₀K : K₀ ⊆ interior K)
    (hKG : K ⊆ realChartDomain G) (hKc : IsCompact (closure Kᶜ))
    (hKQ : sphericalCore K ⊆ openCompletedRegion D.H)
    (hRM : ∀ j, M (ι j) = univ)
    (hr : ∀ j, ContDiffOn ℝ ∞ (r j) (realChartDomain G))
    (hr2 : ∀ j, MemLp (planarGradient (r j)) 2 (volume.restrict (realChartDomain G)))
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (a b : Fin m → S → ℝ) (hwidth : ∀ j s, 0 ≤ b j s - a j s)
    (hwidth2 : ∀ j, Summable (fun s => (b j s - a j s) ^ 2))
    (hTH : ∀ s i, Disjoint (closure (jordanInterior (D.H s))) (closure (jordanInterior (H i))))
    (hTC : ∀ s, Disjoint (closedTerminalCap (D.H s)) (cutoffCore χ))
    (hbound : ∀ (s : A) j x, x ∈ frontier (jordanInterior (D.H s)) →
      ∀ y ∈ frontier (jordanInterior (D.H s)),
        |shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j))
            (r j (Complex.equivRealProdCLM x)) -
          shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j))
            (r j (Complex.equivRealProdCLM y))| ≤ b j s - a j s + 4 * reciprocalGridStep N)
    (hcard : reciprocalGridStep N * Real.sqrt (Fintype.card A : ℝ) < ε / 8) :
    RealTransferStage G π σ r a b Flag O K₀ ε := by
  classical
  have hε : 0 < ε := by
    have hpos := lt_of_le_of_lt
      (mul_nonneg (reciprocalGridStep_pos N).le (Real.sqrt_nonneg (Fintype.card A : ℝ))) hcard
    linarith
  have hosc := W.terminal_oscillation hTH hTC (fun s j => b j s - a j s)
    (fun s j => hwidth j s) hbound
  have hexcess (j : Fin m) : Real.sqrt (∑ s : A,
      max (terminalOscillation (D.H s) (W.functions j) - (b j s - a j s)) 0 ^ 2) < ε := by
    have h := sqrt_sum_terminal_excess_sq_lt Finset.univ Finset.univ (Subset.refl _)
      (fun s : A => terminalOscillation (D.H s) (W.functions j))
      (fun s : A => b j s - a j s) (reciprocalGridStep_pos N).le
      (fun s _ => hosc s j) (by simpa only [Finset.card_univ] using hcard)
    exact h.trans (by linarith)
  refine {
    indices := A
    finite_indices := hA
    flags := hFlag
    terminals := D
    core := K
    core_closed := hK
    core_contains := hK₀K
    core_source := hKG
    core_cocompact := hKc
    core_model := hKQ
    functions := W.functions
    extension := realChartDomain G ∪ ⋃ i, realJordanInterior (H i)
    extension_open := (isOpen_realChartDomain hG).union
      (isOpen_iUnion fun i => (realJordanInterior_geometry (H i)).1)
    extension_contains := W.extension_contains
    functions_smooth := W.filled.1
    retained := W.retained
    radius := Q.radius
    radius_pos := Q.radius_pos
    metric := Q.metric
    metric_smooth := Q.metric_smooth
    metric_pos := Q.metric_pos
    metric_core := Q.metric_core
    metric_far := Q.metric_far
    source_energy := fun j E hE hEK => W.source_energy (isOpen_realChartDomain hG)
      hRM hr hrproj j hE hEK
    excess := ?_
    oscillation := ?_
    domain := Q.domain
    forward := Q.forward
    inverse := Q.inverse
    circle_domain := Q.circle_domain
    equivalence := Q.equivalence
    conformal_core := Q.conformal_core
    principal := Q.principal
    metric_conformal := W.metric_conformal
    integrable := ?_
    transported_smooth := fun j => (W.transported j).1 }
  · intro j
    simpa only [tsum_fintype] using hexcess j
  · intro j
    rw [tsum_fintype]
    exact (CircleDomainRigidity.sqrt_sum_sq_le_band_add_excess
      (fun s : A => terminalOscillation (D.H s) (W.functions j))
      (fun s : A => b j s - a j s) (fun _ => Metric.diam_nonneg)
      (fun s => hwidth j s)).trans_lt
      (add_lt_add_of_le_of_lt (CircleDomainRigidity.finite_label_band_norm_le
        (fun s : A => (s : S)) Subtype.val_injective (fun s => b j s - a j s) (hwidth2 j))
        (hexcess j))
  · intro j
    exact integrableOn_gradientEnergy_with_cofinite_core
      ((isOpen_realChartDomain hG).union (isOpen_iUnion fun i =>
        (realJordanInterior_geometry (H i)).1))
      (isClosed_real_completedRegion D.H) W.extension_contains hK hKc hKG (W.filled.1 j)
      (integrable_gradientEnergy_spherical_of_memLp (hr2 j))
      (W.retained.mono fun _ hz => hz j) Q.metric_smooth.continuous Q.metric_pos Q.metric_core

end CircleDomainRigidity.FiniteTransfer

end

end OAI
