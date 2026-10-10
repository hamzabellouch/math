import Mathlib

namespace OAI

/-! Canonical bundles as alternating top forms and their one-dimensional model. -/

noncomputable section
open Bundle Set Filter
open scoped Manifold Bundle Topology BoundedContinuousFunction

namespace CanonicalBundle

section Evaluation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E]
  {ι : Type*} [Fintype ι]

 
def altCoordinates : (E [⋀^ι]→L[ℂ] F) →ₗ[ℂ] ((ι → Fin (Module.finrank ℂ E)) → F) where
  toFun f v := f (fun i => Module.finBasis ℂ E (v i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem altCoordinates_injective : Function.Injective (altCoordinates (E := E) (F := F) (ι := ι)) := by
  intro f g h
  apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : ι => Module.finBasis ℂ E)
  exact fun v => congrFun h v

instance altFiniteDimensional [FiniteDimensional ℂ F] :
    FiniteDimensional ℂ (E [⋀^ι]→L[ℂ] F) :=
  Module.Finite.of_injective altCoordinates altCoordinates_injective

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℂ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞} {s : Set B}

theorem contMDiffOn_alt [FiniteDimensional ℂ F] {f : B → E [⋀^ι]→L[ℂ] F}
    (hf : ∀ v : ι → E, ContMDiffOn IB 𝓘(ℂ, F) n (fun x => f x v) s) :
    ContMDiffOn IB 𝓘(ℂ, E [⋀^ι]→L[ℂ] F) n f s := by
  classical
  let ev := altCoordinates (E := E) (F := F) (ι := ι)
  obtain ⟨back, hback⟩ := ev.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr altCoordinates_injective)
  have hc : ContMDiffOn IB 𝓘(ℂ, E [⋀^ι]→L[ℂ] F) n (fun x => back (ev (f x))) s :=
    back.toContinuousLinearMap.contMDiff.comp_contMDiffOn
      (contMDiffOn_pi_space.mpr (fun v => hf _))
  have heq : (fun x => back (ev (f x))) = f := by
    funext x
    exact LinearMap.congr_fun hback (f x)
  rwa [heq] at hc

 
theorem contMDiffOn_clm [FiniteDimensional ℂ F] {f : B → E →L[ℂ] F}
    (hf : ∀ v : E, ContMDiffOn IB 𝓘(ℂ, F) n (fun x => f x v) s) :
    ContMDiffOn IB 𝓘(ℂ, E →L[ℂ] F) n f s := by
  let ev : (E →L[ℂ] F) →ₗ[ℂ] (Fin (Module.finrank ℂ E) → F) :=
    { toFun := fun L i => L (Module.finBasis ℂ E i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro f g h
    apply ContinuousLinearMap.coe_injective
    have he : f.toLinearMap = g.toLinearMap :=
      (Module.finBasis ℂ E).ext (fun i => congrFun h i)
    exact he
  obtain ⟨back, hback⟩ := ev.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  have hc : ContMDiffOn IB 𝓘(ℂ, E →L[ℂ] F) n (fun x => back (ev (f x))) s :=
    back.toContinuousLinearMap.contMDiff.comp_contMDiffOn
      (contMDiffOn_pi_space.mpr (fun v => hf _))
  have heq : (fun x => back (ev (f x))) = f := by
    funext x
    exact LinearMap.congr_fun hback (f x)
  rwa [heq] at hc

theorem contMDiffAt_alt [FiniteDimensional ℂ F] {f : B → E [⋀^ι]→L[ℂ] F} {x : B}
    (hf : ∀ v : ι → E, ContMDiffAt IB 𝓘(ℂ, F) n (fun x => f x v) x) :
    ContMDiffAt IB 𝓘(ℂ, E [⋀^ι]→L[ℂ] F) n f x := by
  classical
  let ev := altCoordinates (E := E) (F := F) (ι := ι)
  obtain ⟨back, hback⟩ := ev.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr altCoordinates_injective)
  have hc : ContMDiffAt IB 𝓘(ℂ, E [⋀^ι]→L[ℂ] F) n (fun x => back (ev (f x))) x :=
    back.toContinuousLinearMap.contMDiff.contMDiffAt.comp x
      (contMDiffAt_pi_space.mpr (fun v => hf _))
  have heq : (fun x => back (ev (f x))) = f := by
    funext x
    exact LinearMap.congr_fun hback (f x)
  rwa [heq] at hc

theorem contMDiffAt_clm [FiniteDimensional ℂ F] {f : B → E →L[ℂ] F} {x : B}
    (hf : ∀ v : E, ContMDiffAt IB 𝓘(ℂ, F) n (fun x => f x v) x) :
    ContMDiffAt IB 𝓘(ℂ, E →L[ℂ] F) n f x := by
  let ev : (E →L[ℂ] F) →ₗ[ℂ] (Fin (Module.finrank ℂ E) → F) :=
    { toFun := fun L i => L (Module.finBasis ℂ E i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro f g h
    apply ContinuousLinearMap.coe_injective
    have he : f.toLinearMap = g.toLinearMap :=
      (Module.finBasis ℂ E).ext (fun i => congrFun h i)
    exact he
  obtain ⟨back, hback⟩ := ev.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  have hc : ContMDiffAt IB 𝓘(ℂ, E →L[ℂ] F) n (fun x => back (ev (f x))) x :=
    back.toContinuousLinearMap.contMDiff.contMDiffAt.comp x
      (contMDiffAt_pi_space.mpr (fun v => hf _))
  have heq : (fun x => back (ev (f x))) = f := by
    funext x
    exact LinearMap.congr_fun hback (f x)
  rwa [heq] at hc

end Evaluation
section AlternatingBundle

open Bundle.Pretrivialization
variable {B F₁ F₂ : Type*} {n : WithTop ℕ∞} {ι : Type*} [Fintype ι]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℂ (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℂ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle ℂ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle ℂ F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul ℂ (E₂ x)]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

omit [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul ℂ (E₂ x)] in
theorem contMDiffOn_altCoordChange
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(ℂ, (F₁ [⋀^ι]→L[ℂ] F₂) →L[ℂ] (F₁ [⋀^ι]→L[ℂ] F₂)) n
      (continuousAlternatingMapCoordChange ℂ ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  apply contMDiffOn_clm
  intro v
  apply contMDiffOn_alt
  intro w
  let S := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)
  have h₁ : ContMDiffOn IB 𝓘(ℂ, F₁ →L[ℂ] F₁) n
      (fun b => (e₁'.coordChangeL ℂ e₁ b : F₁ →L[ℂ] F₁)) S :=
    (contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)).mono (by intro b hb; exact ⟨hb.2.1, hb.1.1⟩)
  have h₂ : ContMDiffOn IB 𝓘(ℂ, F₂ →L[ℂ] F₂) n
      (fun b => (e₂.coordChangeL ℂ e₂' b : F₂ →L[ℂ] F₂)) S :=
    (contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)).mono (by intro b hb; exact ⟨hb.1.2, hb.2.2⟩)
  change ContMDiffOn IB 𝓘(ℂ, F₂) n
    (fun b => (e₂.coordChangeL ℂ e₂' b)
      (v (fun i => (e₁'.coordChangeL ℂ e₁ b) (w i)))) S
  exact h₂.clm_apply (v.toContinuousMultilinearMap.contDiff.contMDiff.comp_contMDiffOn
    (contMDiffOn_pi_space.mpr (fun i => h₁.clm_apply contMDiffOn_const)))

instance altVectorPrebundle_isContMDiff :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle ℂ ι F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange ℂ ι e₁ e₁' e₂ e₂',
      contMDiffOn_altCoordChange,
      continuousAlternatingMapCoordChange_apply⟩

instance altContMDiffVectorBundle :
    ContMDiffVectorBundle n (F₁ [⋀^ι]→L[ℂ] F₂)
      (fun b => E₁ b [⋀^ι]→L[ℂ] E₂ b) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle ℂ ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end AlternatingBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) (⊤ : WithTop ℕ∞) M]

abbrev Model (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  E [⋀^Fin (Module.finrank ℂ E)]→L[ℂ] ℂ

abbrev Fiber (x : M) :=
  (TangentSpace 𝓘(ℂ, E) x) [⋀^Fin (Module.finrank ℂ E)]→L[ℂ] ℂ

theorem canonical_isAnalytic :
    ContMDiffVectorBundle (⊤ : WithTop ℕ∞) (Model E) (Fiber (E := E) (M := M)) 𝓘(ℂ, E) := by
  exact altContMDiffVectorBundle (E₁ := TangentSpace 𝓘(ℂ, E))
    (E₂ := Bundle.Trivial M ℂ)

theorem canonical_finiteDimensional : FiniteDimensional ℂ (Model E) := by
  infer_instance

 
def detForm : Model E where
  toAlternatingMap := (Module.finBasis ℂ E).det
  cont := by
    change Continuous (fun v => ((Module.finBasis ℂ E).toMatrix v).det)
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ((Module.finBasis ℂ E).coord i).toContinuousLinearMap.continuous.comp
      (continuous_apply j)

 
def modelScalarEquiv : Model E ≃ₗ[ℂ] ℂ where
  toFun f := f (Module.finBasis ℂ E)
  invFun c := c • detForm
  left_inv f := by
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    exact (AlternatingMap.eq_smul_basis_det (Module.finBasis ℂ E) f.toAlternatingMap).symm
  right_inv c := by
    change c • (Module.finBasis ℂ E).det (Module.finBasis ℂ E) = c
    rw [Module.Basis.det_self, smul_eq_mul, mul_one]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem canonical_rank_one : Module.finrank ℂ (Model E) = 1 := by
  rw [modelScalarEquiv.finrank_eq, Module.finrank_self]

end CanonicalBundle

end

end OAI
