import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.TotalInjectivity
import OAI.Analysis.BiholderTransport.Coordinates.CompactEventuallyFiberwise

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniformly_shifted_injectivityDomain_near_one (R : ℝ) :
    ∀ᶠ h in 𝓝 (1:ℝ), ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖ ≤ R → (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  let Z : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => tangentScale (1-q.1) (sprayFlow q.1 q.2)
  have hZ : ContMDiff (𝓘(ℝ,ℝ).prod (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Z :=
    contMDiff_tangentScale.comp ((contMDiff_const.sub contMDiff_fst).prodMk contMDiff_sprayFlow)
  have H := compact_eventually_fiberwise
    (isCompact_bundle_disk (B := M) (F := Model n)
      (E := fun x => TangentSpace 𝓘(ℝ,Model n) x) R)
    (f := fun _ => ()) continuous_const (g := fun _ : ℝ => ())
    (continuousAt_const (x := 1)) (P := fun h p => (Z (h,p)).2∈injectivityDomain (Z (h,p)).1)
    (by
      intro p _ _
      change ∀ᶠ q in 𝓝 (1,p), Z q ∈ {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈injectivityDomain z.1}
      apply hZ.continuous.continuousAt.eventually
      apply isOpen_total_injectivityDomain.mem_nhds
      change (1-(1:ℝ)) • (sprayFlow 1 p).2∈injectivityDomain (sprayFlow 1 p).1
      rw [sub_self,zero_smul]
      exact zero_mem_injectivityDomain _)
  exact H.mono fun _ hshift base velocity hbound =>
    hshift ⟨base,velocity⟩ hbound rfl

lemma exists_uniform_regular_split (R : ℝ) :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧ ∀ x : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖ ≤ R → p∈minimizingVectors x →
      h • p∈injectivityDomain x ∧
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  have H : ∀ᶠ h in 𝓝[<] (1:ℝ), 0 < h ∧ h < 1 ∧ ∀ x : M,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖ ≤ R →
      (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
    filter_upwards [(uniformly_shifted_injectivityDomain_near_one (n := n) (M := M) R).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with h hh h0 h1
    exact ⟨h0,h1,hh⟩
  obtain ⟨h,h0,h1,hh⟩ := H.exists
  exact ⟨h,h0,h1,fun x p hp hm =>
    ⟨contracted_minimizer_mem_injectivityDomain hm h0 h1,hh x p hp⟩⟩

end WeakMTWTransport

end

end OAI
