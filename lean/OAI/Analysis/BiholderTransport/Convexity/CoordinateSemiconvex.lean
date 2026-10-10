import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHull
import OAI.Analysis.BiholderTransport.Contact.CoordinateSupport

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
section CoordinateSemiconvex
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cTransform_uniform_smooth_coordinate_semiconvex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ψ : E → M} (hψ : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,Model n) ∞ ψ 0) :
    ∃ r>0, ∃ K>0, ∀ v : M → ℝ, Continuous v →
      ConvexOn ℝ (Metric.ball (0:E) r)
        (fun h => cTransform v (ψ h)+K*‖h‖^2) := by
  let x := ψ 0
  let Y := fun z : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp z.1 ((1/2:ℝ) • z.2)
  have hY : Continuous Y := (contMDiff_riemannianExp (n := n) (M := M)).continuous.comp
    ((contMDiff_tangentScale (E := Model n) (M := M)).continuous.comp
      (continuous_const.prodMk continuous_id))
  let P := fun r K : ℝ => fun h : E => fun Z : TangentBundle 𝓘(ℝ,Model n) M =>
    Z.1=ψ h → ∀ z∈Metric.ball (0:E) r, ∃ l : E →L[ℝ] ℝ,
      ∀ w∈Metric.ball (0:E) r,
        2*(cost (ψ w) (Y Z)-cost (ψ z) (Y Z))-
          l (w-z) ≤ K*‖w-z‖^2
  have hmono : ∀ {r R b B : ℝ}, 0<r → r≤R → b≤B → ∀ h Z, P R b h Z → P r B h Z := by
    intro r R b B hr hrR hbB h Z HP he z hz
    obtain ⟨l,hl⟩ := HP he z (Metric.ball_subset_ball hrR hz)
    exact ⟨l,fun w hw => (hl w (Metric.ball_subset_ball hrR hw)).trans
      (mul_le_mul_of_nonneg_right hbB (sq_nonneg _))⟩
  have hlocal : ∀ Z : TangentBundle 𝓘(ℝ,Model n) M,
      Z.2∈minimizingVectors Z.1 →
      ∃ r>0, ∃ b>0, ∀ᶠ q : E×TangentBundle 𝓘(ℝ,Model n) M in 𝓝 (0,Z),
        P r b q.1 q.2 := by
    rintro ⟨a,p⟩ hp
    by_cases ha : a=x
    · subst a
      obtain ⟨r,hr,b,hb,H⟩ := smooth_coordinate_half_cost_quadratic hψ (hY.continuousAt (x := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M))) rfl hp rfl
      refine ⟨r,hr,b,hb,?_⟩
      filter_upwards [continuousAt_snd.tendsto.eventually H] with q hq
      exact fun _ => hq
    · have hbase : Continuous (fun q : E×TangentBundle 𝓘(ℝ,Model n) M => q.2.1) :=
        (FiberBundle.continuous_proj _ _).comp continuous_snd
      have hexp : ContinuousAt (fun q : E×TangentBundle 𝓘(ℝ,Model n) M => ψ q.1) (0,⟨a,p⟩) :=
        ContinuousAt.comp (x := ((0:E),(⟨a,p⟩ : TangentBundle 𝓘(ℝ,Model n) M))) (f := Prod.fst) hψ.continuousAt continuousAt_fst
      have H : ∀ᶠ q : E×TangentBundle 𝓘(ℝ,Model n) M in 𝓝 (0,⟨a,p⟩),
          q.2.1≠ψ q.1 :=
        (hbase.continuousAt.prodMk hexp).preimage_mem_nhds
          (isClosed_diagonal.isOpen_compl.mem_nhds (by simpa only [mem_compl_iff,mem_diagonal_iff] using ha))
      exact ⟨1,by norm_num,1,by norm_num,H.mono (fun _ h he => (h he).elim)⟩
  obtain ⟨r,hr,K,hK,H⟩ := compact_eventually_uniform_radius_bound
    (isCompact_total_minimizingVectors (n := n) (M := M)) hmono hlocal
  obtain ⟨δ,hδ,Hδ⟩ := Metric.mem_nhds_iff.mp H
  refine ⟨min r δ,lt_min hr hδ,K,hK,?_⟩
  intro v hv
  apply convexOn_of_quadratic_lower_support (convex_ball _ _)
  intro z hz
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (ψ z)
  have HZ := Hδ (Metric.ball_subset_ball (min_le_right r δ) hz)
    ⟨ψ z,p⟩ hp.1 rfl
  obtain ⟨l,hl⟩ := HZ z (Metric.ball_subset_ball (min_le_left r δ) hz)
  refine ⟨-l,?_⟩
  intro w hw
  have HH := hl w (Metric.ball_subset_ball (min_le_left r δ) hw)
  have hs := active_split_lower_support hv hp.1 hp.2
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (ψ w)
  simp only [neg_apply]
  dsimp only [Y] at HH
  linarith

end CoordinateSemiconvex
end WeakMTWTransport

end

end

end

end OAI
