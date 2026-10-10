import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition
import OAI.Analysis.BiholderTransport.Convexity.FamilyShortEnvelope

namespace OAI

section

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section FamilyGlobal
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mdifferentiableAt_of_chart_differentiable_of_mem {f : M → ℝ} {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hd : DifferentiableAt ℝ (fun y=>f ((extChartAt 𝓘(ℝ,Model n) a).symm y))
      (extChartAt 𝓘(ℝ,Model n) a x)) :
    MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x := by
  have H := hd.hasFDerivAt.hasMFDerivAt.comp x
    (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,Model n))
      (show x∈(chartAt (Model n) a).source from by simpa only [extChartAt_source] using hx)).hasMFDerivAt
  apply (H.congr_of_eventuallyEq ?_).mdifferentiableAt
  filter_upwards [(isOpen_extChartAt_source a).mem_nhds hx] with y hy
  simp only [Function.comp_apply,(extChartAt 𝓘(ℝ,Model n) a).left_inv hy]

lemma uniform_family_short_mdifferentiable {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s)))
    {Lφ : ℝ≥0} (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s))) (A B : ℝ) :
    ∃ δ>0,∀ p∈Kp,∀ u:M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ∀ τ:ℝ,0<τ → τ<δ →
      MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax τ (fun y=>Φ (p,cTransform u y))) := by
  classical
  choose J JY r hr δ hδ H using fun a:M=>
    uniform_family_short_envelope_data (n := n) hΦ hKp hmono hφL A B a
  let U : M → Set M := fun a=>
    (extChartAt 𝓘(ℝ,Model n) a).source ∩
      (extChartAt 𝓘(ℝ,Model n) a) ⁻¹' ball (extChartAt 𝓘(ℝ,Model n) a a) (r a)
  have hU : ∀ a,U a∈𝓝 a := by
    intro a
    exact inter_mem (extChartAt_source_mem_nhds a)
      (((continuousOn_extChartAt a).continuousAt (extChartAt_source_mem_nhds a)).preimage_mem_nhds
        (ball_mem_nhds _ (hr a)))
  obtain ⟨s,hs⟩ := CompactSpace.elim_nhds_subcover U hU
  have ht : ∀ᶠ τ:ℝ in 𝓝 0,∀ a∈s,τ<δ a := by
    apply (eventually_all_finset s).mpr
    intro a ha
    exact eventually_lt_nhds (hδ a)
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨ε,hε,?_⟩
  intro p hp u hu hb τ hτ hτε x
  have hτδ : ∀ a∈s,τ<δ a := hεsub (by simpa [mem_ball,dist_zero_right,abs_of_pos hτ] using hτε)
  have hx : x∈⋃ a∈s,U a := by rw [hs]; trivial
  obtain ⟨a,ha,hx⟩ := mem_iUnion₂.mp hx
  have hd := (H a p hp u hu hb τ hτ (hτδ a ha)).1 _ hx.2
  apply mdifferentiableAt_of_chart_differentiable_of_mem hx.1
  have HH := hd.const_mul τ⁻¹
  simpa only [←mul_assoc,inv_mul_cancel₀ hτ.ne',one_mul] using HH
end FamilyGlobal
end WeakMTWTransport

end
end

end OAI
