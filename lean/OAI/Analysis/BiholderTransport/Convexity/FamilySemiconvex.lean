import Mathlib
import OAI.Analysis.BiholderTransport.Contact.HopfSupports
import OAI.Analysis.BiholderTransport.Convexity.StrongCostConvexity
import OAI.Analysis.BiholderTransport.Convexity.ParametricSemiconvex

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma uniform_family_chart_semiconvex {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ K>0,∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r⊆(extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ p∈Kp,∀ u : M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ConvexOn ℝ (ball (extChartAt 𝓘(ℝ,Model n) a a) r)
        (fun z => Φ (p,cTransform u ((extChartAt 𝓘(ℝ,Model n) a).symm z))+K/2*‖z‖^2) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨K0,hK0,r0,hr0,hr0T,hSup⟩ := uniform_cTransform_chart_lower (n := n) a
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨L,r1,hr1,hr1T,hL⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩
  obtain ⟨K,hK,H⟩ := scalar_family_uniform_semiconvex (E := Model n) hΦ hKp hmono A B K0 hK0.le (D*L)
  let r := min r0 r1
  have hr : 0 < r := lt_min hr0 hr1
  have hsub0 : ball (χ a) r⊆ball (χ a) r0 := ball_subset_ball (min_le_left _ _)
  have hsub1 : ball (χ a) r⊆ball (χ a) r1 := ball_subset_ball (min_le_right _ _)
  refine ⟨K,hK,r,hr,fun z hz => hr0T (hsub0 hz),?_⟩
  intro p hp u hu hb
  apply H p hp _ (convex_ball _ _) _
  · exact (cTransform_lipschitz hu (fun x y =>
      Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))).comp_lipschitzOnWith (hL.mono hsub1)
  · exact fun z hz => hb _
  · intro z hz
    obtain ⟨l,hl⟩ := hSup u hu z (hsub0 hz)
    exact ⟨l,fun y hy => hl y (hsub0 hy)⟩

lemma uniform_family_short_action_strongConvex {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s))) (A B : ℝ) (a : M) :
    ∃ m>0,∃ r>0,∃ V∈𝓝 (extChartAt 𝓘(ℝ,Model n) a a),∃ δ>0,
      closedBall (extChartAt 𝓘(ℝ,Model n) a a) r⊆(extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ p∈Kp,∀ u : M → ℝ,Continuous u → (∀ y,cTransform u y∈Icc A B) →
      ∀ t : ℝ,0<t → t<δ → ∀ z∈V,
      StrongConvexOn (closedBall (extChartAt 𝓘(ℝ,Model n) a a) r) m
        (fun y => t*Φ (p,cTransform u ((extChartAt 𝓘(ℝ,Model n) a).symm y))+
          chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm z) y) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨K,hK,R,hR,hRT,hsemi⟩ := uniform_family_chart_semiconvex (n := n) hΦ hKp hmono A B a
  obtain ⟨m,hm,r0,hr0,V,hV,hstrong⟩ := chartCost_uniform_strongConvex
    (mem_extChartAt_target (I := 𝓘(ℝ,Model n)) a)
  let r := min r0 (R/2)
  have hr : 0 < r := lt_min hr0 (half_pos hR)
  have hsub0 : closedBall (χ a) r⊆closedBall (χ a) r0 := closedBall_subset_closedBall (min_le_left _ _)
  have hsubR : closedBall (χ a) r⊆ball (χ a) R := closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hR))
  refine ⟨m / 2,half_pos hm,r,hr,V,hV,m / (2*K),by positivity,fun z hz => hRT (hsubR hz),?_⟩
  intro p hp u hu hb t ht htδ z hz
  have hs : StrongConvexOn (closedBall (χ a) r) m (chartCost a (χ.symm z)) :=
    ⟨convex_closedBall _ _,fun {x} hx {y} hy {p} {q} hp hq hsum => (hstrong z hz).2 (hsub0 hx) (hsub0 hy) hp hq hsum⟩
  have hh := strongConvexOn_add_semiconvex hs
    ((hsemi p hp u hu hb).subset hsubR (convex_closedBall _ _)) ht.le
  have htK : t*K< m / 2 := by
    apply (lt_div_iff₀ hK).mp
    simpa only [div_div] using htδ
  have hle : m / 2 ≤ m-t*K := by linarith
  have H := _root_.StrongConvexOn.mono hle hh
  simpa only [add_comm] using H
end WeakMTWTransport

end

end OAI
