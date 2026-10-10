import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.JensenAt
import OAI.Analysis.BiholderTransport.Regularity.FamilyComparison

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma WeakMTW.family_jensen_samples (hmtw : WeakMTW (n := n) (M := M))
    {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {Kp : Set P} (hKp : IsCompact Kp)
    (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) {Lφ : ℝ≥0}
    (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ R>0,∃ δ>0,∀ p∈Kp,∀ u:M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ∀ ψ:ℝ → ℝ,Continuous ψ → ∀ τ:ℝ,0<τ → τ<1/2 → τ<δ →
      ∀ c:M,extChartAt 𝓘(ℝ,Model n) a c∈ball (extChartAt 𝓘(ℝ,Model n) a a) R →
      let χ := extChartAt 𝓘(ℝ,Model n) a
      let w := fun y=>ψ (cTransform u y)
      let g := fun y=>Φ (p,cTransform u y)
      (∀ᶠ z in 𝓝 (χ c),chartOuterEnvelope w (1-τ) a z+chartCenterEnvelope g (1-τ) a z≤
        chartOuterEnvelope w (1-τ) a (χ c)+chartCenterEnvelope g (1-τ) a (χ c)) →
      ∀ N:Set (Model n),volume N=0 → Nonempty (JensenSamplesAt w g (1-τ) a c N) := by
  obtain ⟨R,hR,δ,hδ,H⟩ := hmtw.family_comparison_local_data hΦ hKp hmono hφL A B a
  refine ⟨R,hR,δ,hδ,?_⟩
  intro p hp u hu hb ψ hψ τ hτ hhalf hτδ c hc
  dsimp only
  intro hm N hN
  obtain ⟨r,hr,JF,JG,JY,JP,Y,hF,hG,hFL,hGL,hYL,hPL,hact⟩ :=
    H p hp u hu hb ψ hψ τ hτ hhalf hτδ c hc
  exact jensen_samples_at isOpen_ball (mem_ball_self hr) hF hG hFL hGL hYL hPL hact hm hN

end WeakMTWTransport

end

end OAI
