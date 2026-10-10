import OAI.Analysis.CircleDomains.Transfer.TransportedTerminalBranches

namespace OAI

/-!
# Finite-chart cluster bounds from the assigned sphere ends

The line-payment lemma uses planar cluster points. They are the same
finite cluster values controlled by the inverse terminal-boundary
argument, so no boundary extension of the finite uniformization is needed.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem planar_mapClusterPt_mem_componentClusterValues
    {V : Set Sphere} {p : Sphere} {q : ℂ} {w : Sphere → ℝ} {t : ℝ}
    (hq : (q : Sphere) ∈ connectedComponentIn Vᶜ p)
    (ht : MapClusterPt t (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] q)
      (w ∘ ((↑) : ℂ → Sphere))) :
    t ∈ componentClusterValues V p w := by
  obtain ⟨x, hwx, hx⟩ := ht.exists_seq_tendsto
  have hx' := tendsto_nhdsWithin_iff.mp hx
  refine ⟨(q : Sphere), hq, (fun n => (x n : Sphere)), ?_, ?_, hwx⟩
  · exact OnePoint.continuous_coe.continuousAt.tendsto.comp hx'.1
  · exact hx'.2

theorem TerminalComponentAssignment.planar_cluster_gap_le
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (w : Sphere → ℝ)
    (hw : ∀ q ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)), ContinuousAt w q)
    (hbounded : Bornology.IsBounded
      (w '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)))))
    {p q : ℂ} {u v : ℝ}
    (hp : (p : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hq : (q : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hu : MapClusterPt u (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] p)
      ((w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
    (hv : MapClusterPt v (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] q)
      ((w ∘ fi) ∘ ((↑) : ℂ → Sphere))) :
    |v - u| ≤ Metric.diam
      (w '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)))) := by
  have hsub := a.cluster_values_subset_boundary hf i w hw
  have hu' := hsub (planar_mapClusterPt_mem_componentClusterValues hp hu)
  have hv' := hsub (planar_mapClusterPt_mem_componentClusterValues hq hv)
  simpa only [Real.dist_eq] using Metric.dist_le_diam_of_mem hbounded hv' hu'

theorem TerminalComponentAssignment.real_planar_cluster_gap_le
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (w : (ℝ × ℝ) → ℝ)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hAO : frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O)
    {p q : ℂ} {u v : ℝ}
    (hp : (p : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hq : (q : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hu : MapClusterPt u (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] p)
      ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
    (hv : MapClusterPt v (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] q)
      ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))) :
    |v - u| ≤ Metric.diam (w '' frontier (realJordanInterior (T i))) := by
  have hfront := frontier_realJordanInterior (T i)
  have himage : sphereRealFunction w '' (((↑) : ℂ → Sphere) ''
      frontier (jordanInterior (T i))) = w '' frontier (realJordanInterior (T i)) := by
    rw [hfront, image_image, image_image]
    rfl
  have hbounded : Bornology.IsBounded (w '' frontier (realJordanInterior (T i))) :=
    ((realJordanInterior_geometry (T i)).2.1.image_of_continuousOn (hw.mono hAO)).isBounded
  rw [← himage]
  apply a.planar_cluster_gap_le hf i (sphereRealFunction w) _ (himage.symm ▸ hbounded) hp hq hu hv
  rintro q ⟨z, hz, rfl⟩
  apply continuousAt_sphereRealFunction
  apply hw.continuousAt (hO.mem_nhds (hAO ?_))
  rw [hfront]
  exact mem_image_of_mem _ hz

end CircleDomainRigidity

end

end OAI
