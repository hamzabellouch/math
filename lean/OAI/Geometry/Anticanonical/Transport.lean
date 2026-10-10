import OAI.Geometry.Anticanonical.CanonicalBundle

namespace OAI

/-! Dual tensor powers of canonical bundles and pullback under holomorphic local diffeomorphisms. -/

noncomputable section
open Bundle Set Filter
open scoped Manifold Bundle Topology BoundedContinuousFunction

namespace AnticanonicalTransport

 
structure AnalyticBundle {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] where
  Model : Type
  [modelNormedAdd : NormedAddCommGroup Model]
  [modelNormedSpace : NormedSpace ℂ Model]
  [modelFinite : FiniteDimensional ℂ Model]
  Fiber : M → Type
  [fiberAdd : ∀ x, AddCommGroup (Fiber x)]
  [fiberModule : ∀ x, Module ℂ (Fiber x)]
  [fiberTopology : ∀ x, TopologicalSpace (Fiber x)]
  [fiberTopAdd : ∀ x, IsTopologicalAddGroup (Fiber x)]
  [fiberSMul : ∀ x, ContinuousSMul ℂ (Fiber x)]
  [totalTopology : TopologicalSpace (TotalSpace Model Fiber)]
  [fiberBundle : FiberBundle Model Fiber]
  [vectorBundle : VectorBundle ℂ Model Fiber]
  [analytic : ContMDiffVectorBundle (⊤ : WithTop ℕ∞) Model Fiber 𝓘(ℂ, E)]

attribute [instance] AnalyticBundle.modelNormedAdd AnalyticBundle.modelNormedSpace
  AnalyticBundle.modelFinite AnalyticBundle.fiberAdd AnalyticBundle.fiberModule
  AnalyticBundle.fiberTopology AnalyticBundle.fiberTopAdd AnalyticBundle.fiberSMul
  AnalyticBundle.totalTopology AnalyticBundle.fiberBundle AnalyticBundle.vectorBundle
  AnalyticBundle.analytic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]

 
abbrev canonical : AnalyticBundle (E := E) M where
  Model := CanonicalBundle.Model E
  Fiber := CanonicalBundle.Fiber (E := E) (M := M)
  analytic := CanonicalBundle.canonical_isAnalytic

 
abbrev scalar : AnalyticBundle (E := E) M where
  Model := ℂ
  Fiber := Bundle.Trivial M ℂ

 
abbrev hom (A B : AnalyticBundle (E := E) M) : AnalyticBundle (E := E) M where
  Model := A.Model →L[ℂ] B.Model
  Fiber := fun x => A.Fiber x →L[ℂ] B.Fiber x

 
def anti : ℕ → AnalyticBundle (E := E) M
  | 0 => scalar
  | d + 1 => hom canonical (anti d)

abbrev H0 (d : ℕ) :=
  ContMDiffSection 𝓘(ℂ, E) (anti (E := E) (M := M) d).Model (⊤ : WithTop ℕ∞) (anti (E := E) (M := M) d).Fiber

 
theorem anti_rank_one (d : ℕ) : Module.finrank ℂ (anti (E := E) (M := M) d).Model = 1 := by
  induction d with
  | zero => exact Module.finrank_self ℂ
  | succ d ih =>
    change Module.finrank ℂ ((CanonicalBundle.Model E) →L[ℂ] (anti (E := E) (M := M) d).Model) = 1
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ)
      (E := CanonicalBundle.Model E) (F' := (anti (E := E) (M := M) d).Model)).finrank_eq,
      Module.finrank_linearMap, CanonicalBundle.canonical_rank_one, ih, one_mul]

 
omit [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M] in
theorem hom_triv_equiv (A B : AnalyticBundle (E := E) M) (x₀ x : M)
    (hA : x ∈ (trivializationAt A.Model A.Fiber x₀).baseSet)
    (hB : x ∈ (trivializationAt B.Model B.Fiber x₀).baseSet) :
    (trivializationAt (hom A B).Model (hom A B).Fiber x₀).continuousLinearEquivAt ℂ x
      (show x ∈ (trivializationAt (hom A B).Model (hom A B).Fiber x₀).baseSet from ⟨hA,hB⟩) =
      ((trivializationAt A.Model A.Fiber x₀).continuousLinearEquivAt ℂ x hA).arrowCongr
        ((trivializationAt B.Model B.Fiber x₀).continuousLinearEquivAt ℂ x hB) := by
  apply DFunLike.ext
  intro L
  change A.Fiber x →L[ℂ] B.Fiber x at L
  change _ = (_ : A.Model →L[ℂ] B.Model)
  apply DFunLike.ext
  intro v
  change ((trivializationAt B.Model B.Fiber x₀).continuousLinearMapAt ℂ x)
    ((L : A.Fiber x →L[ℂ] B.Fiber x) ((trivializationAt A.Model A.Fiber x₀).symmL ℂ x v)) = _
  simp only [ContinuousLinearEquiv.arrowCongr_apply,
    Bundle.Trivialization.coe_continuousLinearEquivAt_eq,
    Bundle.Trivialization.symm_continuousLinearEquivAt_eq]

 
theorem canonical_triv_equiv (x₀ x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).baseSet) :
    (trivializationAt (canonical (E := E) (M := M)).Model (canonical (E := E) (M := M)).Fiber x₀).continuousLinearEquivAt ℂ x
      (show x ∈ (trivializationAt (canonical (E := E) (M := M)).Model
        (canonical (E := E) (M := M)).Fiber x₀).baseSet from ⟨hx, Set.mem_univ _⟩) =
    ((trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).continuousLinearEquivAt ℂ x hx).continuousAlternatingMapCongr (ContinuousLinearEquiv.refl ℂ ℂ) := by
  apply DFunLike.ext
  intro f
  change CanonicalBundle.Fiber (E := E) x at f
  change _ = (_ : CanonicalBundle.Model E)
  apply DFunLike.ext
  intro v
  change ((trivializationAt ℂ (Bundle.Trivial M ℂ) x₀).continuousLinearMapAt ℂ x)
    ((f : CanonicalBundle.Fiber (E := E) x) (fun i => (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).symmL ℂ x (v i))) = _
  simp [ContinuousLinearEquiv.continuousAlternatingMapCongr_apply]
  congr 1
  funext i
  exact Bundle.Trivialization.symmL_apply _ hx _

section Lift
variable {N : Type} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) N]
  {q : M → N} (hq : IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) q)

 
theorem contMDiffAt_inverseDerivative (x₀ : M) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E →L[ℂ] E) (⊤ : WithTop ℕ∞)
      (fun x => ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℂ, E) (M := N))
        E (TangentSpace 𝓘(ℂ, E) (M := M)) (q x₀) (q x) x₀ x
        ((hq.mfderivToContinuousLinearEquiv (by simp) x).symm : _ →L[ℂ] _)) x₀ := by
  let D := fun x => hq.mfderivToContinuousLinearEquiv (by simp) x
  have hd : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E →L[ℂ] E) (⊤ : WithTop ℕ∞)
      (fun x => ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℂ, E) (M := M))
        E (TangentSpace 𝓘(ℂ, E) (M := N)) x₀ x (q x₀) (q x) (D x : _ →L[ℂ] _)) x₀ :=
    (hq x₀).contMDiffAt.mfderiv_const (by simp)
  have hinv := (show ContMDiffAt 𝓘(ℂ, E →L[ℂ] E) 𝓘(ℂ, E →L[ℂ] E)
      (⊤ : WithTop ℕ∞) ContinuousLinearMap.inverse
      (ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℂ, E) (M := M))
        E (TangentSpace 𝓘(ℂ, E) (M := N)) x₀ x₀ (q x₀) (q x₀) (D x₀ : _ →L[ℂ] _)) from by
    apply ContDiffAt.contMDiffAt
    apply ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
    rw [ContinuousLinearMap.inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' (q x₀))]
    simp only [ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv]
    exact ContinuousLinearMap.isInvertible_equiv (f := D x₀)).comp x₀ hd
  apply hinv.congr_of_eventuallyEq
  have hA : (trivializationAt E (TangentSpace 𝓘(ℂ, E) (M := M)) x₀).baseSet ∈ nhds x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  have hB : q ⁻¹' (trivializationAt E (TangentSpace 𝓘(ℂ, E) (M := N)) (q x₀)).baseSet ∈ nhds x₀ :=
    (hq x₀).contMDiffAt.continuousAt.preimage_mem_nhds
      ((trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  filter_upwards [hA,hB] with x hx hqx
  dsimp only [Function.comp_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hqx hx, ContinuousLinearMap.inCoordinates_eq hx hqx]
  simp only [ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearMap.inverse_equiv]
  rfl

 
def canonicalPush (x : M) :
    (canonical (E := E) (M := M)).Fiber x ≃L[ℂ]
      (canonical (E := E) (M := N)).Fiber (q x) :=
  (hq.mfderivToContinuousLinearEquiv (by simp) x).continuousAlternatingMapCongr
    (ContinuousLinearEquiv.refl ℂ ℂ)

 
theorem canonicalPush_inCoordinates (x₀ x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℂ, E) (M := M)) x₀).baseSet)
    (hqx : q x ∈ (trivializationAt E (TangentSpace 𝓘(ℂ, E) (M := N)) (q x₀)).baseSet) :
    ContinuousLinearMap.inCoordinates (canonical (E := E) (M := M)).Model
      (canonical (E := E) (M := M)).Fiber (canonical (E := E) (M := N)).Model
      (canonical (E := E) (M := N)).Fiber x₀ x (q x₀) (q x) (canonicalPush hq x : _ →L[ℂ] _) =
      ContinuousAlternatingMap.compContinuousLinearMapCLM (F := ℂ) (ι := Fin (Module.finrank ℂ E))
        (ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℂ, E) (M := N))
          E (TangentSpace 𝓘(ℂ, E) (M := M)) (q x₀) (q x) x₀ x
          ((hq.mfderivToContinuousLinearEquiv (by simp) x).symm : _ →L[ℂ] _)) := by
  have hxK : x ∈ (trivializationAt (canonical (E := E) (M := M)).Model
      (canonical (E := E) (M := M)).Fiber x₀).baseSet := ⟨hx, Set.mem_univ _⟩
  have hqK : q x ∈ (trivializationAt (canonical (E := E) (M := N)).Model
      (canonical (E := E) (M := N)).Fiber (q x₀)).baseSet := ⟨hqx, Set.mem_univ _⟩
  rw [ContinuousLinearMap.inCoordinates_eq hxK hqK,
    canonical_triv_equiv x₀ x hx, canonical_triv_equiv (q x₀) (q x) hqx,
    ContinuousLinearMap.inCoordinates_eq hqx hx]
  rfl

 
theorem contMDiffAt_canonicalPush (x₀ : M) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, CanonicalBundle.Model E →L[ℂ] CanonicalBundle.Model E)
      (⊤ : WithTop ℕ∞)
      (fun x => ContinuousLinearMap.inCoordinates (canonical (E := E) (M := M)).Model
        (canonical (E := E) (M := M)).Fiber (canonical (E := E) (M := N)).Model
        (canonical (E := E) (M := N)).Fiber x₀ x (q x₀) (q x) (canonicalPush hq x : _ →L[ℂ] _)) x₀ := by
  have h : ContMDiffAt 𝓘(ℂ, E)
      𝓘(ℂ, CanonicalBundle.Model E →L[ℂ] CanonicalBundle.Model E) (⊤ : WithTop ℕ∞)
      (fun x => ContinuousAlternatingMap.compContinuousLinearMapCLM (F := ℂ) (ι := Fin (Module.finrank ℂ E))
        (ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℂ, E) (M := N))
          E (TangentSpace 𝓘(ℂ, E) (M := M)) (q x₀) (q x) x₀ x
          ((hq.mfderivToContinuousLinearEquiv (by simp) x).symm : _ →L[ℂ] _))) x₀ := by
    apply CanonicalBundle.contMDiffAt_clm
    intro f
    apply CanonicalBundle.contMDiffAt_alt
    intro v
    change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞)
      (fun x => f (fun i => (ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℂ, E) (M := N))
          E (TangentSpace 𝓘(ℂ, E) (M := M)) (q x₀) (q x) x₀ x
          ((hq.mfderivToContinuousLinearEquiv (by simp) x).symm : _ →L[ℂ] _)) (v i))) x₀
    exact f.toContinuousMultilinearMap.contDiff.contMDiff.contMDiffAt.comp x₀
      (contMDiffAt_pi_space.mpr (fun i => (contMDiffAt_inverseDerivative hq x₀).clm_apply contMDiffAt_const))
  apply h.congr_of_eventuallyEq
  have hA : (trivializationAt E (TangentSpace 𝓘(ℂ, E) (M := M)) x₀).baseSet ∈ nhds x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  have hB : q ⁻¹' (trivializationAt E (TangentSpace 𝓘(ℂ, E) (M := N)) (q x₀)).baseSet ∈ nhds x₀ :=
    (hq x₀).contMDiffAt.continuousAt.preimage_mem_nhds
      ((trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  filter_upwards [hA,hB] with x hx hqx
  exact canonicalPush_inCoordinates hq x₀ x hx hqx

 
omit [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) N] in
theorem homPull_inCoordinates (A B : AnalyticBundle (E := E) M)
    (A' B' : AnalyticBundle (E := E) N) (x₀ x : M) (y₀ y : N)
    (a : A.Fiber x ≃L[ℂ] A'.Fiber y) (b : B'.Fiber y ≃L[ℂ] B.Fiber x)
    (hA : x ∈ (trivializationAt A.Model A.Fiber x₀).baseSet)
    (hB : x ∈ (trivializationAt B.Model B.Fiber x₀).baseSet)
    (hA' : y ∈ (trivializationAt A'.Model A'.Fiber y₀).baseSet)
    (hB' : y ∈ (trivializationAt B'.Model B'.Fiber y₀).baseSet) :
    ContinuousLinearMap.inCoordinates (hom A' B').Model (hom A' B').Fiber
      (hom A B).Model (hom A B).Fiber y₀ y x₀ x (a.symm.arrowCongr b : _ →L[ℂ] _) =
      ((ContinuousLinearMap.inCoordinates A.Model A.Fiber A'.Model A'.Fiber
        x₀ x y₀ y (a : _ →L[ℂ] _)).precomp B.Model).comp
      ((ContinuousLinearMap.inCoordinates B'.Model B'.Fiber B.Model B.Fiber
        y₀ y x₀ x (b : _ →L[ℂ] _)).postcomp A'.Model) := by
  have hAB : x ∈ (trivializationAt (hom A B).Model (hom A B).Fiber x₀).baseSet := ⟨hA,hB⟩
  have hAB' : y ∈ (trivializationAt (hom A' B').Model (hom A' B').Fiber y₀).baseSet := ⟨hA',hB'⟩
  rw [ContinuousLinearMap.inCoordinates_eq hAB' hAB,
    hom_triv_equiv A B x₀ x hA hB, hom_triv_equiv A' B' y₀ y hA' hB',
    ContinuousLinearMap.inCoordinates_eq hA hA', ContinuousLinearMap.inCoordinates_eq hB' hB]
  rfl

 
def antiPull : (d : ℕ) → (x : M) →
    (anti (E := E) (M := N) d).Fiber (q x) ≃L[ℂ] (anti (E := E) (M := M) d).Fiber x
  | 0, _ => ContinuousLinearEquiv.refl ℂ ℂ
  | d + 1, x => (canonicalPush hq x).symm.arrowCongr (antiPull d x)

 
theorem contMDiffAt_antiPull (d : ℕ) (x₀ : M) :
    ContMDiffAt 𝓘(ℂ, E)
      𝓘(ℂ, (anti (E := E) (M := N) d).Model →L[ℂ] (anti (E := E) (M := M) d).Model)
      (⊤ : WithTop ℕ∞)
      (fun x => ContinuousLinearMap.inCoordinates (anti (E := E) (M := N) d).Model
        (anti (E := E) (M := N) d).Fiber (anti (E := E) (M := M) d).Model
        (anti (E := E) (M := M) d).Fiber (q x₀) (q x) x₀ x (antiPull hq d x : _ →L[ℂ] _)) x₀ := by
  induction d with
  | zero =>
    change ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
      (fun x => ((Bundle.Trivial.trivialization M ℂ).continuousLinearMapAt ℂ x).comp
        ((ContinuousLinearMap.id ℂ ℂ).comp ((Bundle.Trivial.trivialization N ℂ).symmL ℂ (q x)))) x₀
    simpa using
      (contMDiffAt_const : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
        (fun _ : M => ContinuousLinearMap.id ℂ ℂ) x₀)
  | succ d ih =>
    have h := ((contMDiffAt_canonicalPush hq x₀).clm_precomp
      (F₃ := (anti (E := E) (M := M) d).Model)).clm_comp
      (ih.clm_postcomp (F₁ := CanonicalBundle.Model E))
    apply h.congr_of_eventuallyEq
    have base (A : AnalyticBundle (E := E) M) :
        (trivializationAt A.Model A.Fiber x₀).baseSet ∈ nhds x₀ :=
      (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
    have base' (A : AnalyticBundle (E := E) N) :
        q ⁻¹' (trivializationAt A.Model A.Fiber (q x₀)).baseSet ∈ nhds x₀ :=
      (hq x₀).contMDiffAt.continuousAt.preimage_mem_nhds
        ((trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
    filter_upwards [base canonical, base (anti d), base' canonical, base' (anti d)] with x hA hB hA' hB'
    exact homPull_inCoordinates canonical (anti d) canonical (anti d) x₀ x (q x₀) (q x)
      (canonicalPush hq x) (antiPull hq d x) hA hB hA' hB'

 

theorem contMDiff_antiPull_section (d : ℕ) (s : H0 (E := E) (M := N) d) :
    ContMDiff 𝓘(ℂ, E) ((𝓘(ℂ, E)).prod 𝓘(ℂ, (anti (E := E) (M := M) d).Model))
      (⊤ : WithTop ℕ∞)
      (fun x => (⟨x, antiPull hq d x (s (q x))⟩ :
        TotalSpace (anti (E := E) (M := M) d).Model (anti (E := E) (M := M) d).Fiber)) := by
  intro x
  have hv : ContMDiffAt 𝓘(ℂ, E)
      ((𝓘(ℂ, E)).prod 𝓘(ℂ, (anti (E := E) (M := N) d).Model)) (⊤ : WithTop ℕ∞)
      (fun y => (⟨q y, s (q y)⟩ : TotalSpace (anti (E := E) (M := N) d).Model
        (anti (E := E) (M := N) d).Fiber)) x :=
    s.contMDiff.contMDiffAt.comp x (hq x).contMDiffAt
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := (anti (E := E) (M := N) d).Model) (E₁ := (anti (E := E) (M := N) d).Fiber)
    (F₂ := (anti (E := E) (M := M) d).Model) (E₂ := (anti (E := E) (M := M) d).Fiber)
    (IB₁ := 𝓘(ℂ, E)) (IB₂ := 𝓘(ℂ, E)) (b₁ := q) (b₂ := id)
    (ϕ := fun (y : M) => ((antiPull hq d y).toContinuousLinearMap :
      (anti (E := E) (M := N) d).Fiber (q y) →L[ℂ] (anti (E := E) (M := M) d).Fiber y))
    (v := fun (y : M) => s (q y)) (contMDiffAt_antiPull hq d x) hv contMDiffAt_id

 
def pullSection (d : ℕ) : H0 (E := E) (M := N) d →ₗ[ℂ] H0 (E := E) (M := M) d where
  toFun s := ⟨fun x => antiPull hq d x (s (q x)), contMDiff_antiPull_section hq d s⟩
  map_add' s t := by ext x; exact (antiPull hq d x).map_add (s (q x)) (t (q x))
  map_smul' c s := by ext x; exact (antiPull hq d x).map_smul c (s (q x))

 
theorem pullSection_injective (d : ℕ) (hsurj : Function.Surjective q) :
    Function.Injective (pullSection hq d) := by
  intro s t h
  apply DFunLike.ext
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  apply (antiPull hq d x).injective
  exact DFunLike.congr_fun h x

section Composition
variable {P : Type} [TopologicalSpace P] [ChartedSpace E P]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) P]
  {r : N → P} (hr : IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) r)

 
omit [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) N]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) P] in
theorem derivativeEquiv_comp (x : M) :
    (show IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) (r ∘ q)
      from fun x => (hq x).comp 𝓘(ℂ, E) P (hr (q x))).mfderivToContinuousLinearEquiv (by simp) x =
      (hq.mfderivToContinuousLinearEquiv (by simp) x).trans
        (hr.mfderivToContinuousLinearEquiv (by simp) (q x)) := by
  apply ContinuousLinearEquiv.coe_injective
  exact mfderiv_comp x ((hr (q x)).mdifferentiableAt (by simp))
    ((hq x).mdifferentiableAt (by simp))

 
theorem canonicalPush_comp (x : M) :
    canonicalPush (fun x => (hq x).comp 𝓘(ℂ, E) P (hr (q x))) x =
      (canonicalPush hq x).trans (canonicalPush hr (q x)) := by
  unfold canonicalPush
  rw [derivativeEquiv_comp hq hr x]
  rfl

theorem antiPull_comp (d : ℕ) (x : M) :
    antiPull (fun x => (hq x).comp 𝓘(ℂ, E) P (hr (q x))) d x =
      (antiPull hr d (q x)).trans (antiPull hq d x) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [antiPull, canonicalPush_comp hq hr x, ih]
    rfl

theorem pullSection_comp (d : ℕ) :
    pullSection (fun x => (hq x).comp 𝓘(ℂ, E) P (hr (q x))) d =
      (pullSection hq d).comp (pullSection hr d) := by
  apply LinearMap.ext
  intro s
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (antiPull_comp hq hr d x) (s (r (q x)))

end Composition

 
theorem pullSection_deck (d : ℕ) {g : M → M}
    (hg : IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) g)
    (hdeck : q ∘ g = q) (s : H0 (E := E) (M := N) d) :
    pullSection hg d (pullSection hq d s) = pullSection hq d s := by
  have hh := DFunLike.congr_fun (pullSection_comp hg hq d) s
  have he : pullSection (fun x => (hg x).comp 𝓘(ℂ, E) N (hq (g x))) d = pullSection hq d := by
    congr 1
  exact hh.symm.trans (DFunLike.congr_fun he s)

end Lift

 
theorem antiPull_id (d : ℕ) (x : M) :
    antiPull (Diffeomorph.refl 𝓘(ℂ,E) M (⊤ : WithTop ℕ∞)).isLocalDiffeomorph d x =
      ContinuousLinearEquiv.refl ℂ ((anti (E := E) (M := M) d).Fiber x) := by
  have hk : canonicalPush (Diffeomorph.refl 𝓘(ℂ,E) M (⊤ : WithTop ℕ∞)).isLocalDiffeomorph x =
      ContinuousLinearEquiv.refl ℂ ((canonical (E := E) (M := M)).Fiber x) := by
    unfold canonicalPush
    have hd : (Diffeomorph.refl 𝓘(ℂ,E) M (⊤ : WithTop ℕ∞)).isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x =
        ContinuousLinearEquiv.refl ℂ (TangentSpace 𝓘(ℂ,E) x) := by
      apply ContinuousLinearEquiv.coe_injective
      exact mfderiv_id
    rw [hd]
    rfl
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [antiPull, hk, ih]
    rfl

 
theorem pullSection_id (d : ℕ) :
    pullSection (Diffeomorph.refl 𝓘(ℂ,E) M (⊤ : WithTop ℕ∞)).isLocalDiffeomorph d =
      LinearMap.id (R := ℂ) (M := H0 (E := E) (M := M) d) := by
  ext s x
  exact DFunLike.congr_fun (antiPull_id d x) (s x)

variable {N : Type} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(ℂ,E) (⊤ : WithTop ℕ∞) N]

 
theorem pullSection_inverse (e : M ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,E), 𝓘(ℂ,E)⟯ N)
    (d : ℕ) (s : H0 (E := E) (M := M) d) :
    pullSection e.isLocalDiffeomorph d (pullSection e.symm.isLocalDiffeomorph d s) = s := by
  have hh := DFunLike.congr_fun (pullSection_comp e.isLocalDiffeomorph e.symm.isLocalDiffeomorph d) s
  have hi : (e.symm : N → M) ∘ (e : M → N) = id := funext e.symm_apply_apply
  have he : pullSection (fun x => (e.isLocalDiffeomorph x).comp 𝓘(ℂ,E) M
      (e.symm.isLocalDiffeomorph (e x))) d =
      pullSection (Diffeomorph.refl 𝓘(ℂ,E) M (⊤ : WithTop ℕ∞)).isLocalDiffeomorph d := by
    congr 1
  rw [he, pullSection_id] at hh
  exact hh.symm

 
def pullSectionEquiv (e : M ≃ₘ^(⊤ : WithTop ℕ∞)⟮𝓘(ℂ,E), 𝓘(ℂ,E)⟯ N) (d : ℕ) :
    H0 (E := E) (M := N) d ≃ₗ[ℂ] H0 (E := E) (M := M) d where
  toLinearMap := pullSection e.isLocalDiffeomorph d
  invFun := pullSection e.symm.isLocalDiffeomorph d
  left_inv := pullSection_inverse e.symm d
  right_inv := pullSection_inverse e d


end AnticanonicalTransport

end

end OAI
