import OAI.Geometry.SurfaceImmersion.Geometry.ResolvedPrefixAppend
import OAI.Geometry.SurfaceImmersion.Whitney.EndpointRegularArcs
import OAI.Geometry.SurfaceImmersion.Geometry.OriginalRegularSegment

namespace OAI

/-! Finish a resolved smooth prefix at the original final endpoint. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {T : ι → ℝ} {O : Set M}

theorem finish_smooth_tail (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    (B : ∀ i, LocalCornerBridge γ (T i) O) {J : Set ι} {a A : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hAa : A < a) (hA : 0 ≤ A)
    (hJ : ∀ i ∈ J, (B i).right ≤ a)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (hreg : ∀ t ∈ Ioo A 1, ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t))
    (P : SmoothArcTail γ.extend a)
    (hPi : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆ resolvedPrefixImage γ B J a) :
    ∃ R : SmoothCompactArc planeModel M,
      R.curve R.start = P.arc.curve P.arc.start ∧ R.curve R.finish = q ∧
      R.curve '' Icc R.start R.finish ⊆ resolvedPrefixImage γ B J 1 := by
  obtain ⟨Q,l,hal,hl1,hQs,hQf,hQmatch,hQend,hQgerm⟩ :=
    last_regular_arc hγ hi (sub_pos.mpr ha1) (by linarith)
  have hal' : a < l := by linarith
  obtain ⟨S,hSs,hSf,hSc⟩ := original_regular_segment hi isOpen_Ioo
    (fun _ ht => ⟨hA.trans_lt ht.1,ht.2⟩) hreg hal'
    (fun u hu => ⟨hAa.trans_le hu.1,hu.2.trans_lt hl1⟩)
  obtain ⟨P',hP'i,hP's⟩ := append_resolved_segment B hi ha.le hal' hl1.le hJ hsep P hPi S hSs hSf hSc
  have hJ' : ∀ i ∈ J, (B i).right ≤ l := fun i hiJ => (hJ i hiJ).trans hal'.le
  have hcross : ∀ s ∈ Icc P'.arc.start P'.arc.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P'.arc.curve s ≠ Q.curve t := by
    intro s hs t ht
    have ht' : t ∈ Ioc l 1 := by simpa only [hQs,hQf] using ht
    rw [hQmatch t ⟨ht'.1.le,ht'.2⟩]
    exact resolvedPrefixImage_avoids_future B hi hl1.le hJ' hsep _
      (hP'i (mem_image_of_mem P'.arc.curve hs)) t ht'
  have hidg : Q.curve =ᶠ[𝓝 Q.start] γ.extend ∘ id := hQgerm
  obtain ⟨R,e,hes,hei,hem,hRs,hRf,hRi,hRstart,hRend,_,_⟩ :=
    join_shared_parameter_arcs γ.extend P'.arc Q P'.parameter id P'.smooth contDiff_id
      P'.forward (by simp) (P'.value.trans hQs.symm) P'.germ hidg hcross
  refine ⟨R,hRstart.trans hP's,hRend.trans hQend,?_⟩
  rw [hRi]
  apply union_subset
  · exact hP'i.trans (resolvedPrefixImage_mono B (Subset.refl _) hl1.le)
  · intro x hx
    obtain ⟨u,hu,rfl⟩ := hx
    have hu' : u ∈ Icc l 1 := by simpa only [hQs,hQf] using hu
    rw [hQmatch u hu']
    exact Or.inl ⟨u,⟨ha.le.trans (hal'.le.trans hu'.1),hu'.2⟩,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
