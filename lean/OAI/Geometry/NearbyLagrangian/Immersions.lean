import Mathlib
import OAI.Geometry.NearbyLagrangian.GeneratingGeometry

namespace OAI

/-! Local split-derivative immersions and compact smooth embeddings. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.LocalGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]

theorem exists_smooth_local_inverse_on {f : E → F} {S : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) {x : E} (hx : x ∈ S)
    (A : E ≃L[ℝ] F) (hA : HasFDerivAt f (A : E →L[ℝ] F) x) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ x ∈ e.source ∧
      e.source ⊆ S ∧ ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  have hfx := hf.contDiffAt (hS.mem_nhds hx)
  let e₀ := hfx.toOpenPartialHomeomorph f hA (by simp)
  have hderiv : ContinuousAt (fderiv ℝ f) x :=
    (hf.continuousOn_fderiv_of_isOpen hS (by simp) x hx).continuousAt (hS.mem_nhds hx)
  have hInv : (fderiv ℝ f) ⁻¹'
      Set.range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F) ∈ 𝓝 x := by
    exact hderiv.preimage_mem_nhds (hA.fderiv.symm ▸ A.nhds)
  obtain ⟨T, hTsub, hT, hxT⟩ := _root_.mem_nhds_iff.mp (inter_mem (hS.mem_nhds hx) hInv)
  let e := e₀.restr T
  have he : (e : E → F) = f := rfl
  have hesub : e.source ⊆ S := fun y hy => (hTsub (hT.interior_eq ▸ hy.2)).1
  refine ⟨e, he, ⟨hfx.mem_toOpenPartialHomeomorph_source hA (by simp),
    hT.interior_eq.symm ▸ hxT⟩, hesub, ?_, ?_⟩
  · simpa only [he] using hf.mono hesub
  · intro y hy
    have hxy := hTsub (hT.interior_eq ▸ (e.map_target hy).2)
    obtain ⟨B, hB⟩ := hxy.2
    have hfs := hf.contDiffAt (hS.mem_nhds hxy.1)
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hy (f₀' := B)
    · rw [he, hB]
      exact (hfs.differentiableAt (by simp)).hasFDerivAt
    · simpa only [he] using hfs

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

theorem isImmersionAt_of_split_derivative_on {f : E → F} {S : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) {x : E} (hx : x ∈ S) (A : (E × C) ≃L[ℝ] F)
    (hA : HasFDerivAt f
      ((A : (E × C) →L[ℝ] F).comp (ContinuousLinearMap.inl ℝ E C)) x) :
    Manifold.IsImmersionAtOfComplement C 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  let H : E × C → F := fun p => f p.1 + A (0, p.2)
  have hH : ContDiffOn ℝ ∞ H (S ×ˢ (Set.univ : Set C)) :=
    (hf.comp contDiff_fst.contDiffOn (fun _ h => h.1)).add
      (A.contDiff.comp (contDiff_const.prodMk contDiff_snd)).contDiffOn
  have hdH : HasFDerivAt H (A : E × C →L[ℝ] F) (x, 0) := by
    convert! (hA.comp (x, (0 : C)) (hasFDerivAt_fst (p := (x, (0 : C))))).add
      (A.hasFDerivAt.comp (x, (0 : C))
        ((hasFDerivAt_const (0 : E) (x, (0 : C))).prodMk
          (hasFDerivAt_snd (p := (x, (0 : C)))))) using 1
    apply ContinuousLinearMap.ext
    intro p
    change A p = A (p.1, 0) + A (0, p.2)
    rw [← map_add]
    congr 1
    simp
  obtain ⟨e, he, hxe, _, heSmooth, heInvSmooth⟩ := exists_smooth_local_inverse_on
    (hS.prod isOpen_univ) hH ⟨hx, mem_univ _⟩ A hdH
  have hHeq (y : E) : H (y, 0) = f y := by simp [H]
  let U : Set E := (fun y : E => (y, (0 : C))) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (continuous_id.prodMk continuous_const)
  let d := (OpenPartialHomeomorph.refl E).restr U
  let a : OpenPartialHomeomorph (E × C) F := A.toHomeomorph.toOpenPartialHomeomorph
  let c : OpenPartialHomeomorph F F := e.symm.trans a
  have hd : (d : E → E) = id := rfl
  have hd' : (d.symm : E → E) = id := rfl
  have hc : (c : F → F) = fun y => A (e.symm y) := rfl
  have hc' : (c.symm : F → F) = fun y => e (A.symm y) := rfl
  have hcsource : c.source = e.target := by simp [c, a]
  have hctarget : c.target = A.symm ⁻¹' e.source := by simp [c, a]
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt (hf.contDiffAt (hS.mem_nhds hx)).continuousAt
    A d c
  · show x ∈ Set.univ ∩ interior U
    exact ⟨mem_univ _, hU.interior_eq.symm ▸ hxe⟩
  · rw [hcsource, ← hHeq, ← he]
    exact e.map_source hxe
  · apply d.mem_maximalAtlas_of_contMDiffOn
    · rw [contMDiffOn_iff_contDiffOn, hd]
      exact contDiff_id.contDiffOn
    · rw [contMDiffOn_iff_contDiffOn, hd']
      exact contDiff_id.contDiffOn
  · apply c.mem_maximalAtlas_of_contMDiffOn
    · rw [contMDiffOn_iff_contDiffOn, hc, hcsource]
      exact A.contDiff.comp_contDiffOn heInvSmooth
    · rw [contMDiffOn_iff_contDiffOn, hc', hctarget]
      exact heSmooth.comp A.symm.contDiff.contDiffOn (fun y hy => hy)
  · intro y hy
    have hyU : y ∈ U := by
      simpa [d, hU.interior_eq, mfld_simps] using hy
    change A (e.symm (f y)) = A (y, 0)
    apply congrArg A
    rw [← hHeq y, ← he]
    exact e.left_inv hyU

omit [CompleteSpace E] in

theorem exists_split_linear_equiv [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (D : E →L[ℝ] F) (hD : Function.Injective D) :
    ∃ A : (E × EuclideanSpace ℝ (Fin (Module.finrank ℝ F - Module.finrank ℝ E))) ≃L[ℝ] F,
      (A : (E × EuclideanSpace ℝ (Fin (Module.finrank ℝ F - Module.finrank ℝ E))) →L[ℝ] F).comp
        (ContinuousLinearMap.inl ℝ E _) = D := by
  let P := D.toLinearMap.range
  obtain ⟨Q, hQ⟩ := P.exists_isCompl
  let eP : E ≃ₗ[ℝ] P := LinearEquiv.ofInjective D.toLinearMap hD
  have hdimP : Module.finrank ℝ E = Module.finrank ℝ P := eP.finrank_eq
  have hdimQ : Module.finrank ℝ Q = Module.finrank ℝ F - Module.finrank ℝ E := by
    have h := Submodule.finrank_add_eq_of_isCompl hQ
    omega
  let eQ : EuclideanSpace ℝ (Fin (Module.finrank ℝ F - Module.finrank ℝ E)) ≃ₗ[ℝ] Q :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hdimQ])
  let A := ((eP.prodCongr eQ).trans (P.prodEquivOfIsCompl Q hQ)).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  apply ContinuousLinearMap.ext
  intro y
  simp [A, eP]
  rfl

theorem isImmersionAt_of_injective_derivative_on
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    {x : E} (hx : x ∈ S) (hD : Function.Injective (fderiv ℝ f x)) :
    Manifold.IsImmersionAtOfComplement
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ F - Module.finrank ℝ E)))
      𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  obtain ⟨A, hA⟩ := exists_split_linear_equiv (fderiv ℝ f x) hD
  apply isImmersionAt_of_split_derivative_on hS hf hx A
  rw [hA]
  exact ((hf.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, F) ∞ N]

omit [CompleteSpace E] in

theorem trans_mem_maximalAtlas {d : OpenPartialHomeomorph M E}
    {e : OpenPartialHomeomorph E E}
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ E) :
    d.trans e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := by
  apply (d.trans e).mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas he).comp
      ((contMDiffOn_of_mem_maximalAtlas hd).mono inter_subset_left) (fun _ h => h.2)
  · exact (contMDiffOn_symm_of_mem_maximalAtlas hd).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left) (fun _ h => h.2)

omit [CompleteSpace E] [CompleteSpace C] in

theorem isImmersionAt_of_chart {f : M → N} {x : M}
    (hf : ContinuousAt f x) (d : OpenPartialHomeomorph M E)
    (c : OpenPartialHomeomorph N F) (hx : x ∈ d.source) (hfx : f x ∈ c.source)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N)
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(ℝ, E) 𝓘(ℝ, F) ∞
      (c ∘ f ∘ d.symm) (d x)) :
    Manifold.IsImmersionAtOfComplement C 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt hf h.equiv
    (d.trans h.domChart) (c.trans h.codChart)
  · exact ⟨hx, h.mem_domChart_source⟩
  · refine ⟨hfx, ?_⟩
    change c (f x) ∈ h.codChart.source
    simpa only [Function.comp_apply, d.left_inv hx] using h.mem_codChart_source
  · exact trans_mem_maximalAtlas hd h.domChart_mem_maximalAtlas
  · exact trans_mem_maximalAtlas hc h.codChart_mem_maximalAtlas
  · intro y hy
    have hy₀ : y ∈ (d.trans h.domChart).target := by
      simpa only [mfld_simps] using hy
    have hy' : y ∈ (h.domChart.extend 𝓘(ℝ, E)).target := by
      simpa only [mfld_simps] using hy₀.1
    simpa only [mfld_simps, Function.comp_apply] using h.writtenInCharts hy'

theorem manifold_isImmersionAt_of_injective_mfderiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) {x : M}
    (hD : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    Manifold.IsImmersionAtOfComplement
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ F - Module.finrank ℝ E)))
      𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  let d₀ := chartAt E x
  let c := chartAt F (f x)
  let S : Set M := f ⁻¹' c.source
  have hS : IsOpen S := c.open_source.preimage hf.continuous
  let d := d₀.restr S
  have hxS : x ∈ S := mem_chart_source F (f x)
  have hx : x ∈ d.source :=
    ⟨mem_chart_source E x, hS.interior_eq.symm ▸ hxS⟩
  have hd : d ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ 𝓘(ℝ, E)) (IsManifold.chart_mem_maximalAtlas x) hS
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N := IsManifold.chart_mem_maximalAtlas (f x)
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (c ∘ f ∘ d.symm) d.target :=
    (contMDiffOn_of_mem_maximalAtlas hc).comp
      (hf.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hd))
      (by
        intro y hy
        change d.symm y ∈ S
        exact hS.interior_eq ▸ (d.map_target hy).2)
  have hmd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f x :=
    hf.mdifferentiable (by simp) x
  have hder : Function.Injective (fderiv ℝ (c ∘ f ∘ d.symm) (d x)) := by
    rw [hmd.mfderiv] at hD
    simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ] at hD
    convert! hD using 1
  apply isImmersionAt_of_chart hf.continuous.continuousAt d c hx hxS hd hc
  exact isImmersionAt_of_injective_derivative_on d.open_target
    (contMDiffOn_iff_contDiffOn.mp hg) (d.map_source hx) hder

theorem manifold_isImmersion_of_injective_mfderiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hD : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  apply Manifold.IsImmersionOfComplement.isImmersion
    (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ F - Module.finrank ℝ E)))
  intro x
  exact manifold_isImmersionAt_of_injective_mfderiv hf (hD x)

theorem isSmoothEmbedding_of_compact_injective_mfderiv
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [CompactSpace M] [T2Space N]
    {f : M → N} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hinj : Function.Injective f)
    (hD : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f :=
  ⟨manifold_isImmersion_of_injective_mfderiv hf hD,
    (hf.continuous.isClosedEmbedding hinj).isEmbedding⟩

end NearbyLagrangian.LocalGeometry

namespace NearbyLagrangian.CotangentGeometry

theorem bundleTotalSpace_t2Space {B F : Type*} {V : B → Type*}
    [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (V b)]
    [TopologicalSpace (Bundle.TotalSpace F V)] [FiberBundle F V]
    [T2Space B] [T2Space F] : T2Space (Bundle.TotalSpace F V) := by
  refine t2_iff_nhds.mpr ?_
  intro x y h
  let : NeBot (𝓝 x ⊓ 𝓝 y) := h
  have hxy : x.proj = y.proj := tendsto_nhds_unique
    ((FiberBundle.continuous_proj F V).continuousAt.mono_left inf_le_left)
    ((FiberBundle.continuous_proj F V).continuousAt.mono_left inf_le_right)
  let e := trivializationAt F V x.proj
  have hx : x ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have hy : y ∈ e.source := e.mem_source.mpr (hxy ▸ mem_baseSet_trivializationAt F V x.proj)
  exact e.injOn hx hy (tendsto_nhds_unique
    ((e.toOpenPartialHomeomorph.continuousAt hx).mono_left inf_le_left)
    ((e.toOpenPartialHomeomorph.continuousAt hy).mono_left inf_le_right))

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.Generating

variable {Q W : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma vertical_eq_partial {f : Q × W → ℝ} {x : Q × W}
    (hf : DifferentiableAt ℝ f x) :
    vertical f x = fderiv ℝ (fun w => f (x.1, w)) x.2 := by
  have hi : HasFDerivAt (fun w : W => (x.1, w)) (ContinuousLinearMap.inr ℝ Q W) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have h := hf.hasFDerivAt.comp x.2 hi
  exact h.fderiv.symm

lemma momentum_eq_partial {f : Q × W → ℝ} {x : Q × W}
    (hf : DifferentiableAt ℝ f x) :
    momentum f x = fderiv ℝ (fun q => f (q, x.2)) x.1 := by
  have hi : HasFDerivAt (fun q : Q => (q, x.2)) (ContinuousLinearMap.inl ℝ Q W) x.1 :=
    (hasFDerivAt_id x.1).prodMk (hasFDerivAt_const x.2 x.1)
  have h := hf.hasFDerivAt.comp x.1 hi
  exact h.fderiv.symm

end NearbyLagrangian.Generating

end

end OAI
