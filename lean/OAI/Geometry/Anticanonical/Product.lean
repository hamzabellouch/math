import OAI.Geometry.Anticanonical.Transport

namespace OAI

/-! Product decompositions of canonical bundles and naturality of anticanonical sections. -/

noncomputable section
open Bundle Set Filter
open scoped Manifold Bundle Topology BoundedContinuousFunction

namespace CanonicalProduct
open AnticanonicalTransport
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

abbrev scalarEquiv (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] : CanonicalBundle.Model E ≃L[ℂ] ℂ :=
  CanonicalBundle.modelScalarEquiv.toContinuousLinearEquiv

 

def productForm (α : CanonicalBundle.Model E) (β : CanonicalBundle.Model F) :
    CanonicalBundle.Model (E × F) :=
  (scalarEquiv (E × F)).symm ((scalarEquiv E α) * (scalarEquiv F β))

 
theorem scalarEquiv_congr (A : E ≃L[ℂ] E) (α : CanonicalBundle.Model E) :
    scalarEquiv E (A.continuousAlternatingMapCongr (ContinuousLinearEquiv.refl ℂ ℂ) α) =
      LinearMap.det A.symm.toLinearMap * scalarEquiv E α := by
  have he : α.toAlternatingMap = (scalarEquiv E α) • (Module.finBasis ℂ E).det := by
    exact AlternatingMap.eq_smul_basis_det (Module.finBasis ℂ E) α.toAlternatingMap
  change α (fun i => A.symm (Module.finBasis ℂ E i)) = _
  change α.toAlternatingMap (fun i => A.symm (Module.finBasis ℂ E i)) = _
  rw [he]
  change (scalarEquiv E α) * (Module.finBasis ℂ E).det
    (A.symm.toLinearMap ∘ Module.finBasis ℂ E) = _
  rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one, mul_comm]

 
theorem productForm_natural (A : E ≃L[ℂ] E) (B : F ≃L[ℂ] F)
    (α : CanonicalBundle.Model E) (β : CanonicalBundle.Model F) :
    (A.prodCongr B).continuousAlternatingMapCongr (ContinuousLinearEquiv.refl ℂ ℂ)
        (productForm α β) =
      productForm (A.continuousAlternatingMapCongr (ContinuousLinearEquiv.refl ℂ ℂ) α)
        (B.continuousAlternatingMapCongr (ContinuousLinearEquiv.refl ℂ ℂ) β) := by
  apply (scalarEquiv (E × F)).injective
  rw [scalarEquiv_congr]
  simp only [productForm, ContinuousLinearEquiv.apply_symm_apply]
  rw [scalarEquiv_congr, scalarEquiv_congr]
  have hd : LinearMap.det (A.prodCongr B).symm.toLinearMap =
      LinearMap.det A.symm.toLinearMap * LinearMap.det B.symm.toLinearMap :=
    LinearMap.det_prodMap A.symm.toLinearMap B.symm.toLinearMap
  rw [hd]
  ring

 
def productOperator : CanonicalBundle.Model E →L[ℂ]
    (CanonicalBundle.Model F →L[ℂ] CanonicalBundle.Model (E × F)) :=
  (scalarEquiv E).toContinuousLinearMap.smulRight
    ((scalarEquiv F).trans (scalarEquiv (E × F)).symm).toContinuousLinearMap

theorem productOperator_apply (α : CanonicalBundle.Model E) (β : CanonicalBundle.Model F) :
    productOperator α β = productForm α β := by
  change (scalarEquiv E α) • (scalarEquiv (E × F)).symm (scalarEquiv F β) = _
  simp only [productForm, ← map_smul, smul_eq_mul]

 
def productEquiv (α : CanonicalBundle.Model E) (hα : α ≠ 0) :
    CanonicalBundle.Model F ≃L[ℂ] CanonicalBundle.Model (E × F) :=
  (scalarEquiv F).trans
    ((LinearEquiv.smulOfNeZero ℂ ℂ (scalarEquiv E α) (by
      intro hh
      apply hα
      apply (scalarEquiv E).injective
      simpa using hh)).toContinuousLinearEquiv.trans (scalarEquiv (E × F)).symm)

theorem productEquiv_apply (α : CanonicalBundle.Model E) (hα : α ≠ 0)
    (β : CanonicalBundle.Model F) :
    productEquiv α hα β = productForm α β := by
  rfl

theorem productEquiv_coe (α : CanonicalBundle.Model E) (hα : α ≠ 0) :
    (productEquiv (F := F) α hα).toContinuousLinearMap = productOperator (F := F) α := by
  apply ContinuousLinearMap.ext
  intro β
  change productEquiv α hα β = productOperator α β
  rw [productEquiv_apply, productOperator_apply]

variable {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, F) (⊤ : WithTop ℕ∞) N]

local instance productCharts : ChartedSpace (E × F) (M × N) :=
  inferInstanceAs (ChartedSpace (ModelProd E F) (M × N))
local instance productManifold : IsManifold 𝓘(ℂ, E × F) (⊤ : WithTop ℕ∞) (M × N) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℂ, E)) (I' := 𝓘(ℂ, F)) M N

 
omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem tangent_triv_prod (x₀ x : M) (y₀ y : N)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).baseSet)
    (hy : y ∈ (trivializationAt F (TangentSpace 𝓘(ℂ, F)) y₀).baseSet) :
    (trivializationAt (E × F) (TangentSpace 𝓘(ℂ, E × F)) (x₀,y₀)).continuousLinearEquivAt ℂ
      (x,y) (show (x,y) ∈ (trivializationAt (E × F) (TangentSpace 𝓘(ℂ, E × F)) (x₀,y₀)).baseSet
        from ⟨hx,hy⟩) =
    ((trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).continuousLinearEquivAt ℂ x hx).prodCongr
      ((trivializationAt F (TangentSpace 𝓘(ℂ, F)) y₀).continuousLinearEquivAt ℂ y hy) := by
  apply DFunLike.ext
  intro v
  change E × F at v
  have hxy : (x,y) ∈ (trivializationAt (E × F) (TangentSpace 𝓘(ℂ, E × F)) (x₀,y₀)).baseSet :=
    ⟨hx,hy⟩
  change _ =
    ((trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).continuousLinearEquivAt ℂ x hx v.1,
      (trivializationAt F (TangentSpace 𝓘(ℂ, F)) y₀).continuousLinearEquivAt ℂ y hy v.2)
  simp only [Bundle.Trivialization.coe_continuousLinearEquivAt_eq]
  erw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ _ hxy,
    Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ _ hx,
    Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ _ hy]
  simp only [TangentBundle.trivializationAt_apply, mfld_simps, fderivWithin_univ]
  change (fderiv ℂ (Prod.map ((chartAt E x₀) ∘ (chartAt E x).symm)
    ((chartAt F y₀) ∘ (chartAt F y).symm)) ((chartAt E x) x, (chartAt F y) y)) v = _
  have Dx : DifferentiableAt ℂ ((chartAt E x₀) ∘ (chartAt E x).symm) ((chartAt E x) x) := by
    have hh := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ,E)) (n := (⊤ : WithTop ℕ∞)) x₀ x
      (y := (chartAt E x) x) (by simp [mfld_simps, show x ∈ (chartAt E x₀).source from hx])
    simpa [mfld_simps, differentiableWithinAt_univ] using hh.differentiableWithinAt (by simp)
  have Dy : DifferentiableAt ℂ ((chartAt F y₀) ∘ (chartAt F y).symm) ((chartAt F y) y) := by
    have hh := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ,F)) (n := (⊤ : WithTop ℕ∞)) y₀ y
      (y := (chartAt F y) y) (by simp [mfld_simps, show y ∈ (chartAt F y₀).source from hy])
    simpa [mfld_simps, differentiableWithinAt_univ] using hh.differentiableWithinAt (by simp)
  rw [(HasFDerivAt.prodMap ((chartAt E x) x, (chartAt F y) y) Dx.hasFDerivAt Dy.hasFDerivAt).fderiv]
  rfl

 
theorem canonical_product_coords (x₀ x : M) (y₀ y : N)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).baseSet)
    (hy : y ∈ (trivializationAt F (TangentSpace 𝓘(ℂ, F)) y₀).baseSet)
    (α : CanonicalBundle.Fiber (E := E) x) (β : CanonicalBundle.Fiber (E := F) y) :
    (trivializationAt (canonical (E := E × F) (M := M × N)).Model
      (canonical (E := E × F) (M := M × N)).Fiber (x₀,y₀)).continuousLinearEquivAt ℂ
        (x,y) ⟨⟨hx,hy⟩, Set.mem_univ _⟩ (productForm α β) =
    productForm
      ((trivializationAt (canonical (E := E) (M := M)).Model
        (canonical (E := E) (M := M)).Fiber x₀).continuousLinearEquivAt ℂ x
          ⟨hx,Set.mem_univ _⟩ α)
      ((trivializationAt (canonical (E := F) (M := N)).Model
        (canonical (E := F) (M := N)).Fiber y₀).continuousLinearEquivAt ℂ y
          ⟨hy,Set.mem_univ _⟩ β) := by
  have hxyT : (x,y) ∈ (trivializationAt (E × F) (TangentSpace 𝓘(ℂ,E × F)) (x₀,y₀)).baseSet :=
    ⟨hx,hy⟩
  rw [canonical_triv_equiv (E := E × F) (M := M × N) (x₀,y₀) (x,y) hxyT,
    tangent_triv_prod x₀ x y₀ y hx hy, canonical_triv_equiv (E := E) x₀ x hx,
    canonical_triv_equiv (E := F) y₀ y hy]
  exact productForm_natural (E := E) (F := F) _ _ α β

 
def frameInsert
    (α : ContMDiffSection 𝓘(ℂ,E) (CanonicalBundle.Model E) (⊤ : WithTop ℕ∞)
      (CanonicalBundle.Fiber (E := E) (M := M)))
    (hα : ∀ x, α x ≠ 0) (p : M × N) :
    (canonical (E := F) (M := N)).Fiber p.2 ≃L[ℂ]
      (canonical (E := E × F) (M := M × N)).Fiber p :=
  productEquiv (E := E) (F := F) (α p.1) (hα p.1)

theorem frameInsert_inCoordinates
    (α : ContMDiffSection 𝓘(ℂ,E) (CanonicalBundle.Model E) (⊤ : WithTop ℕ∞)
      (CanonicalBundle.Fiber (E := E) (M := M)))
    (hα : ∀ x, α x ≠ 0) (x₀ x : M) (y₀ y : N)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).baseSet)
    (hy : y ∈ (trivializationAt F (TangentSpace 𝓘(ℂ, F)) y₀).baseSet) :
    ContinuousLinearMap.inCoordinates (canonical (E := F) (M := N)).Model
      (canonical (E := F) (M := N)).Fiber
      (canonical (E := E × F) (M := M × N)).Model
      (canonical (E := E × F) (M := M × N)).Fiber
      y₀ y (x₀,y₀) (x,y) (frameInsert α hα (x,y)).toContinuousLinearMap =
    productOperator ((trivializationAt (CanonicalBundle.Model E)
      (CanonicalBundle.Fiber (E := E) (M := M)) x₀) ⟨x,α x⟩).2 := by
  have hyK : y ∈ (trivializationAt (canonical (E := F) (M := N)).Model
      (canonical (E := F) (M := N)).Fiber y₀).baseSet := ⟨hy,Set.mem_univ _⟩
  have hxyK : (x,y) ∈ (trivializationAt (canonical (E := E × F) (M := M × N)).Model
      (canonical (E := E × F) (M := M × N)).Fiber (x₀,y₀)).baseSet := ⟨⟨hx,hy⟩,Set.mem_univ _⟩
  rw [ContinuousLinearMap.inCoordinates_eq hyK hxyK]
  apply ContinuousLinearMap.ext
  intro β
  change (trivializationAt (canonical (E := E × F) (M := M × N)).Model
    (canonical (E := E × F) (M := M × N)).Fiber (x₀,y₀)).continuousLinearEquivAt ℂ
      (x,y) hxyK (productForm (E := E) (F := F) (α x)
        (((trivializationAt (canonical (E := F) (M := N)).Model
          (canonical (E := F) (M := N)).Fiber y₀).continuousLinearEquivAt ℂ y hyK).symm β)) = _
  rw [canonical_product_coords x₀ x y₀ y hx hy (α x)]
  simp only [ContinuousLinearEquiv.apply_symm_apply, productOperator_apply]
  congr 1

 
theorem contMDiffAt_frameInsert
    (α : ContMDiffSection 𝓘(ℂ,E) (CanonicalBundle.Model E) (⊤ : WithTop ℕ∞)
      (CanonicalBundle.Fiber (E := E) (M := M)))
    (hα : ∀ x, α x ≠ 0) (p₀ : M × N) :
    ContMDiffAt 𝓘(ℂ,E × F)
      𝓘(ℂ, CanonicalBundle.Model F →L[ℂ] CanonicalBundle.Model (E × F))
      (⊤ : WithTop ℕ∞)
      (fun p => ContinuousLinearMap.inCoordinates (canonical (E := F) (M := N)).Model
        (canonical (E := F) (M := N)).Fiber
        (canonical (E := E × F) (M := M × N)).Model
        (canonical (E := E × F) (M := M × N)).Fiber
        p₀.2 p.2 p₀ p (frameInsert α hα p).toContinuousLinearMap) p₀ := by
  have hp : ContMDiffAt 𝓘(ℂ,E × F) 𝓘(ℂ,E) (⊤ : WithTop ℕ∞)
      (Prod.fst : M × N → M) p₀ := by
    rw [modelWithCornersSelf_prod]
    exact contMDiffAt_fst
  have hc := ((contMDiffAt_section p₀.1).mp (α.contMDiff p₀.1)).comp p₀ hp
  have ho : ContMDiff 𝓘(ℂ, CanonicalBundle.Model E)
      𝓘(ℂ, CanonicalBundle.Model F →L[ℂ] CanonicalBundle.Model (E × F))
      (⊤ : WithTop ℕ∞) (productOperator (E := E) (F := F)) := by
    exact ContinuousLinearMap.contMDiff _
  have hh := ho.contMDiffAt.comp p₀ hc
  apply hh.congr_of_eventuallyEq
  have hb : (trivializationAt (E × F) (TangentSpace 𝓘(ℂ,E × F)) p₀).baseSet ∈ nhds p₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  filter_upwards [hb] with p hpp
  have hpp' : p.1 ∈ (trivializationAt E (TangentSpace 𝓘(ℂ,E)) p₀.1).baseSet ∧
      p.2 ∈ (trivializationAt F (TangentSpace 𝓘(ℂ,F)) p₀.2).baseSet := hpp
  exact frameInsert_inCoordinates α hα p₀.1 p.1 p₀.2 p.2 hpp'.1 hpp'.2

 
omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]
  [IsManifold 𝓘(ℂ, F) (⊤ : WithTop ℕ∞) N] in
theorem product_homPull_inCoordinates
    (A B : AnalyticBundle (E := F) N)
    (A' B' : AnalyticBundle (E := E × F) (M × N)) (x₀ x : N) (y₀ y : M × N)
    (a : A.Fiber x ≃L[ℂ] A'.Fiber y) (b : B'.Fiber y ≃L[ℂ] B.Fiber x)
    (hA : x ∈ (trivializationAt A.Model A.Fiber x₀).baseSet)
    (hB : x ∈ (trivializationAt B.Model B.Fiber x₀).baseSet)
    (hA' : y ∈ (trivializationAt A'.Model A'.Fiber y₀).baseSet)
    (hB' : y ∈ (trivializationAt B'.Model B'.Fiber y₀).baseSet) :
    ContinuousLinearMap.inCoordinates (hom A' B').Model (hom A' B').Fiber
      (hom A B).Model (hom A B).Fiber y₀ y x₀ x (a.symm.arrowCongr b).toContinuousLinearMap =
      ((ContinuousLinearMap.inCoordinates A.Model A.Fiber A'.Model A'.Fiber
        x₀ x y₀ y a.toContinuousLinearMap).precomp B.Model).comp
      ((ContinuousLinearMap.inCoordinates B'.Model B'.Fiber B.Model B.Fiber
        y₀ y x₀ x b.toContinuousLinearMap).postcomp A'.Model) := by
  have hAB : x ∈ (trivializationAt (hom A B).Model (hom A B).Fiber x₀).baseSet := ⟨hA,hB⟩
  have hAB' : y ∈ (trivializationAt (hom A' B').Model (hom A' B').Fiber y₀).baseSet := ⟨hA',hB'⟩
  rw [ContinuousLinearMap.inCoordinates_eq hAB' hAB,
    hom_triv_equiv A B x₀ x hA hB, hom_triv_equiv A' B' y₀ y hA' hB',
    ContinuousLinearMap.inCoordinates_eq hA hA', ContinuousLinearMap.inCoordinates_eq hB' hB]
  rfl

 
def antiSplit
    (α : ContMDiffSection 𝓘(ℂ,E) (CanonicalBundle.Model E) (⊤ : WithTop ℕ∞)
      (CanonicalBundle.Fiber (E := E) (M := M)))
    (hα : ∀ x, α x ≠ 0) : (d : ℕ) → (p : M × N) →
    (anti (E := E × F) (M := M × N) d).Fiber p ≃L[ℂ]
      (anti (E := F) (M := N) d).Fiber p.2
  | 0, _ => ContinuousLinearEquiv.refl ℂ ℂ
  | d+1, p => (frameInsert α hα p).symm.arrowCongr (antiSplit α hα d p)

 
theorem contMDiffAt_antiSplit
    (α : ContMDiffSection 𝓘(ℂ,E) (CanonicalBundle.Model E) (⊤ : WithTop ℕ∞)
      (CanonicalBundle.Fiber (E := E) (M := M)))
    (hα : ∀ x, α x ≠ 0) (d : ℕ) (p₀ : M × N) :
    ContMDiffAt 𝓘(ℂ,E × F)
      𝓘(ℂ, (anti (E := E × F) (M := M × N) d).Model →L[ℂ]
        (anti (E := F) (M := N) d).Model) (⊤ : WithTop ℕ∞)
      (fun p => ContinuousLinearMap.inCoordinates
        (anti (E := E × F) (M := M × N) d).Model
        (anti (E := E × F) (M := M × N) d).Fiber
        (anti (E := F) (M := N) d).Model (anti (E := F) (M := N) d).Fiber
        p₀ p p₀.2 p.2 (antiSplit α hα d p).toContinuousLinearMap) p₀ := by
  induction d with
  | zero =>
    change ContMDiffAt 𝓘(ℂ,E × F) 𝓘(ℂ,ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
      (fun p => ((Bundle.Trivial.trivialization N ℂ).continuousLinearMapAt ℂ p.2).comp
        ((ContinuousLinearMap.id ℂ ℂ).comp ((Bundle.Trivial.trivialization (M × N) ℂ).symmL ℂ p))) p₀
    simpa using
      (contMDiffAt_const : ContMDiffAt 𝓘(ℂ,E × F) 𝓘(ℂ,ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
        (fun _ : M × N => ContinuousLinearMap.id ℂ ℂ) p₀)
  | succ d ih =>
    have hh := ((contMDiffAt_frameInsert α hα p₀).clm_precomp
      (F₃ := (anti (E := F) (M := N) d).Model)).clm_comp
      (ih.clm_postcomp (F₁ := CanonicalBundle.Model (E × F)))
    apply hh.congr_of_eventuallyEq
    have base (A : AnalyticBundle (E := E × F) (M × N)) :
        (trivializationAt A.Model A.Fiber p₀).baseSet ∈ nhds p₀ :=
      (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
    have baseN (A : AnalyticBundle (E := F) N) :
        Prod.snd ⁻¹' (trivializationAt A.Model A.Fiber p₀.2).baseSet ∈ nhds p₀ :=
      continuous_snd.continuousAt.preimage_mem_nhds
        ((trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
    filter_upwards [base canonical, base (anti d), baseN canonical, baseN (anti d)]
      with p hA' hB' hA hB
    exact product_homPull_inCoordinates canonical (anti d) canonical (anti d)
      p₀.2 p.2 p₀ p (frameInsert α hα p) (antiSplit α hα d p) hA hB hA' hB'

 
theorem contMDiff_antiSplit_apply
    (α : ContMDiffSection 𝓘(ℂ,E) (CanonicalBundle.Model E) (⊤ : WithTop ℕ∞)
      (CanonicalBundle.Fiber (E := E) (M := M)))
    (hα : ∀ x, α x ≠ 0) (d : ℕ)
    {G P : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [TopologicalSpace P]
    [ChartedSpace G P] [IsManifold 𝓘(ℂ,G) (⊤ : WithTop ℕ∞) P]
    (p : P → M × N) (hp : ContMDiff 𝓘(ℂ,G) 𝓘(ℂ,E × F) (⊤ : WithTop ℕ∞) p)
    (v : ∀ x, (anti (E := E × F) (M := M × N) d).Fiber (p x))
    (hv : ContMDiff 𝓘(ℂ,G)
      ((𝓘(ℂ,E × F)).prod 𝓘(ℂ,(anti (E := E × F) (M := M × N) d).Model))
      (⊤ : WithTop ℕ∞)
      (fun x => (⟨p x, v x⟩ : TotalSpace (anti (E := E × F) (M := M × N) d).Model
        (anti (E := E × F) (M := M × N) d).Fiber))) :
    ContMDiff 𝓘(ℂ,G) ((𝓘(ℂ,F)).prod 𝓘(ℂ,(anti (E := F) (M := N) d).Model))
      (⊤ : WithTop ℕ∞)
      (fun x => (⟨(p x).2, antiSplit α hα d (p x) (v x)⟩ :
        TotalSpace (anti (E := F) (M := N) d).Model (anti (E := F) (M := N) d).Fiber)) := by
  intro x₀
  have hs : ContMDiffAt 𝓘(ℂ,E × F) 𝓘(ℂ,F) (⊤ : WithTop ℕ∞)
      (Prod.snd : M × N → N) (p x₀) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiffAt_snd
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := (anti (E := E × F) (M := M × N) d).Model)
    (E₁ := (anti (E := E × F) (M := M × N) d).Fiber)
    (F₂ := (anti (E := F) (M := N) d).Model) (E₂ := (anti (E := F) (M := N) d).Fiber)
    (IB₁ := 𝓘(ℂ,E × F)) (IB₂ := 𝓘(ℂ,F)) (b₁ := p) (b₂ := fun x => (p x).2)
    (ϕ := fun x => (antiSplit α hα d (p x)).toContinuousLinearMap) (v := v)
    ((contMDiffAt_antiSplit α hα d (p x₀)).comp x₀ (hp x₀)) (hv x₀) (hs.comp x₀ (hp x₀))

variable {f : M → M} {g : N → N}
  (hf : IsLocalDiffeomorph 𝓘(ℂ,E) 𝓘(ℂ,E) (⊤ : WithTop ℕ∞) f)
  (hg : IsLocalDiffeomorph 𝓘(ℂ,F) 𝓘(ℂ,F) (⊤ : WithTop ℕ∞) g)
  (hfg : IsLocalDiffeomorph 𝓘(ℂ,E × F) 𝓘(ℂ,E × F) (⊤ : WithTop ℕ∞) (Prod.map f g))

 
omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]
  [IsManifold 𝓘(ℂ, F) (⊤ : WithTop ℕ∞) N] in
theorem derivativeEquiv_prod (p : M × N) :
    hfg.mfderivToContinuousLinearEquiv (by simp) p =
      (hf.mfderivToContinuousLinearEquiv (by simp) p.1).prodCongr
        (hg.mfderivToContinuousLinearEquiv (by simp) p.2) := by
  apply ContinuousLinearEquiv.coe_injective
  change mfderiv 𝓘(ℂ,E × F) 𝓘(ℂ,E × F) (Prod.map f g) p =
    (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) f p.1).prodMap (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) g p.2)
  rw [modelWithCornersSelf_prod]
  exact mfderiv_prodMap ((hf p.1).mdifferentiableAt (by simp))
    ((hg p.2).mdifferentiableAt (by simp))

 
theorem canonicalPush_product (p : M × N)
    (α : CanonicalBundle.Fiber (E := E) p.1) (β : CanonicalBundle.Fiber (E := F) p.2) :
    canonicalPush hfg p (productForm (E := E) (F := F) α β) =
      productForm (E := E) (F := F) (canonicalPush hf p.1 α) (canonicalPush hg p.2 β) := by
  unfold canonicalPush
  rw [derivativeEquiv_prod hf hg hfg]
  exact productForm_natural (E := E) (F := F) _ _ α β

variable (α : ContMDiffSection 𝓘(ℂ,E) (CanonicalBundle.Model E) (⊤ : WithTop ℕ∞)
      (CanonicalBundle.Fiber (E := E) (M := M)))
    (hα : ∀ x, α x ≠ 0)
    (hαf : ∀ x, canonicalPush hf x (α x) = α (f x))

include hαf in
 
theorem frameInsert_natural (p : M × N) (β : (canonical (E := F) (M := N)).Fiber p.2) :
    canonicalPush hfg p (frameInsert α hα p β) =
      frameInsert α hα (Prod.map f g p) (canonicalPush hg p.2 β) := by
  change canonicalPush hfg p (productForm (E := E) (F := F) (α p.1) β) =
    productForm (E := E) (F := F) (α (f p.1)) (canonicalPush hg p.2 β)
  rw [canonicalPush_product hf hg hfg, hαf]

include hαf in
 
theorem antiSplit_natural (d : ℕ) (p : M × N) :
    (antiPull hfg d p).trans (antiSplit α hα d p) =
      (antiSplit α hα d (Prod.map f g p)).trans (antiPull hg d p.2) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    apply DFunLike.ext
    intro L
    change (canonical (E := E × F) (M := M × N)).Fiber (Prod.map f g p) →L[ℂ]
      (anti (E := E × F) (M := M × N) d).Fiber (Prod.map f g p) at L
    apply ContinuousLinearMap.ext
    intro β
    change antiSplit α hα d p (antiPull hfg d p
        (L (canonicalPush hfg p (frameInsert α hα p β)))) =
      antiPull hg d p.2 (antiSplit α hα d (Prod.map f g p)
        (L (frameInsert α hα (Prod.map f g p) (canonicalPush hg p.2 β))))
    have ih' (v : (anti (E := E × F) (M := M × N) d).Fiber (Prod.map f g p)) :
        antiSplit α hα d p (antiPull hfg d p v) =
          antiPull hg d p.2 (antiSplit α hα d (Prod.map f g p) v) :=
      DFunLike.congr_fun ih v
    rw [ih', frameInsert_natural hf hg hfg α hα hαf]



end CanonicalProduct

end

end OAI
