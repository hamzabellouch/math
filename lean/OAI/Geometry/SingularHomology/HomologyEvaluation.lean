import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

section ModuleCocycles

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

def moduleHomologyEvaluation (S : ShortComplex (ModuleCat R))
    (φ : S.X₂ →ₗ[R] M) (hφ : ∀ w : S.X₁, φ (S.f.hom w) = 0) :
    S.homology →ₗ[R] M :=
  ((LinearMap.range S.moduleCatToCycles).liftQ
    (φ.comp (LinearMap.ker S.g.hom).subtype)
    (by
      rintro z ⟨w, rfl⟩
      exact hφ w)).comp S.moduleCatHomologyIso.toLinearEquiv.toLinearMap

@[simp]
theorem moduleHomologyEvaluation_class (S : ShortComplex (ModuleCat R))
    (φ : S.X₂ →ₗ[R] M) (hφ : ∀ w : S.X₁, φ (S.f.hom w) = 0)
    (z : S.X₂) (hz : S.g.hom z = 0) :
    moduleHomologyEvaluation S φ hφ (moduleHomologyClass S z hz) = φ z := by
  unfold moduleHomologyEvaluation moduleHomologyClass
  erw [LinearMap.comp_apply]
  erw [LinearEquiv.apply_symm_apply]
  rfl

theorem moduleHomologyClass_surjective (S : ShortComplex (ModuleCat R)) :
    Function.Surjective (fun z : LinearMap.ker S.g.hom =>
      moduleHomologyClass S z.val z.property) := by
  exact S.moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
    (Submodule.Quotient.mk_surjective (LinearMap.range S.moduleCatToCycles))

theorem moduleHomologyClass_ne_zero_of_evaluation
    (S : ShortComplex (ModuleCat R))
    (φ : S.X₂ →ₗ[R] M) (hφ : ∀ w : S.X₁, φ (S.f.hom w) = 0)
    (z : S.X₂) (hz : S.g.hom z = 0) (hne : φ z ≠ 0) :
    moduleHomologyClass S z hz ≠ 0 := by
  intro hzero
  apply hne
  rw [← moduleHomologyEvaluation_class S φ hφ z hz, hzero, map_zero]

theorem moduleHomologyEvaluation_unique (S : ShortComplex (ModuleCat R))
    (φ : S.X₂ →ₗ[R] M) (hφ : ∀ w : S.X₁, φ (S.f.hom w) = 0)
    (ψ : S.homology →ₗ[R] M)
    (hψ : ∀ (z : S.X₂) (hz : S.g.hom z = 0),
      ψ (moduleHomologyClass S z hz) = φ z) :
    ψ = moduleHomologyEvaluation S φ hφ := by
  ext v
  obtain ⟨z, rfl⟩ := moduleHomologyClass_surjective S v
  exact (hψ z.val z.property).trans
    (moduleHomologyEvaluation_class S φ hφ z.val z.property).symm

theorem moduleCycle_map {S T : ShortComplex (ModuleCat R)} (f : S ⟶ T)
    (z : S.X₂) (hz : S.g.hom z = 0) :
    T.g.hom (f.τ₂.hom z) = 0 := by
  have h := congrArg (fun k : S.X₂ ⟶ T.X₃ => k.hom z) f.comm₂₃
  change T.g.hom (f.τ₂.hom z) = f.τ₃.hom (S.g.hom z) at h
  simpa only [hz, map_zero] using h

theorem moduleHomologyEvaluation_naturality
    {S T : ShortComplex (ModuleCat R)} (f : S ⟶ T)
    (φ : S.X₂ →ₗ[R] M) (hφ : ∀ w : S.X₁, φ (S.f.hom w) = 0)
    (ψ : T.X₂ →ₗ[R] M) (hψ : ∀ w : T.X₁, ψ (T.f.hom w) = 0)
    (hcomm : ψ.comp f.τ₂.hom = φ) :
    (moduleHomologyEvaluation T ψ hψ).comp (ShortComplex.homologyMap f).hom =
      moduleHomologyEvaluation S φ hφ := by
  apply moduleHomologyEvaluation_unique
  intro z hz
  change moduleHomologyEvaluation T ψ hψ
    ((ShortComplex.homologyMap f).hom (moduleHomologyClass S z hz)) = φ z
  rw [moduleHomologyClass_map f z hz (moduleCycle_map f z hz),
    moduleHomologyEvaluation_class]
  exact LinearMap.congr_fun hcomm z

end ModuleCocycles

section SingularCocycles

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

def realSingularHomologyEvaluation (X : Type) [TopologicalSpace X] (n : ℕ)
    (φ : (realSingularChainComplex X).X n →ₗ[ℝ] M)
    (hφ : ∀ w : (realSingularChainComplex X).X (n + 1),
      φ (((realSingularChainComplex X).d (n + 1) n).hom w) = 0) :
    RealSingularHomology n X →ₗ[ℝ] M :=
  moduleHomologyEvaluation ((realSingularChainComplex X).sc n) φ (by
    change ∀ w : (realSingularChainComplex X).X ((ComplexShape.down ℕ).prev n),
      φ (((realSingularChainComplex X).d ((ComplexShape.down ℕ).prev n) n).hom w) = 0
    rw [show (ComplexShape.down ℕ).prev n = n + 1 from ChainComplex.prev ℕ n]
    exact hφ)

def positiveRealSingularCycleClass (X : Type) [TopologicalSpace X] (n : ℕ)
    (z : (realSingularChainComplex X).X (n + 1))
    (hz : ((realSingularChainComplex X).d (n + 1) n).hom z = 0) :
    RealSingularHomology (n + 1) X :=
  moduleHomologyClass ((realSingularChainComplex X).sc (n + 1)) z (by
    change ((realSingularChainComplex X).d (n + 1)
      ((ComplexShape.down ℕ).next (n + 1))).hom z = 0
    rw [show (ComplexShape.down ℕ).next (n + 1) = n from ChainComplex.next_nat_succ n]
    exact hz)

@[simp]
theorem realSingularHomologyEvaluation_cycleClass
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (φ : (realSingularChainComplex X).X (n + 1) →ₗ[ℝ] M)
    (hφ : ∀ w : (realSingularChainComplex X).X (n + 1 + 1),
      φ (((realSingularChainComplex X).d (n + 1 + 1) (n + 1)).hom w) = 0)
    (z : (realSingularChainComplex X).X (n + 1))
    (hz : ((realSingularChainComplex X).d (n + 1) n).hom z = 0) :
    realSingularHomologyEvaluation X (n + 1) φ hφ
      (positiveRealSingularCycleClass X n z hz) = φ z :=
  moduleHomologyEvaluation_class _ _ _ _ _

theorem positiveRealSingularCycleClass_ne_zero_of_evaluation
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (φ : (realSingularChainComplex X).X (n + 1) →ₗ[ℝ] M)
    (hφ : ∀ w : (realSingularChainComplex X).X (n + 1 + 1),
      φ (((realSingularChainComplex X).d (n + 1 + 1) (n + 1)).hom w) = 0)
    (z : (realSingularChainComplex X).X (n + 1))
    (hz : ((realSingularChainComplex X).d (n + 1) n).hom z = 0)
    (hne : φ z ≠ 0) : positiveRealSingularCycleClass X n z hz ≠ 0 := by
  intro hzero
  apply hne
  rw [← realSingularHomologyEvaluation_cycleClass X n φ hφ z hz, hzero, map_zero]

theorem realSingularHomologyEvaluation_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : X → Y) (hf : Continuous f)
    (φ : (realSingularChainComplex X).X n →ₗ[ℝ] M)
    (hφ : ∀ w : (realSingularChainComplex X).X (n + 1),
      φ (((realSingularChainComplex X).d (n + 1) n).hom w) = 0)
    (ψ : (realSingularChainComplex Y).X n →ₗ[ℝ] M)
    (hψ : ∀ w : (realSingularChainComplex Y).X (n + 1),
      ψ (((realSingularChainComplex Y).d (n + 1) n).hom w) = 0)
    (hcomm : ψ.comp ((realSingularChainMap f hf).f n).hom = φ) :
    (realSingularHomologyEvaluation Y n ψ hψ).comp (realHomologyMap n f hf) =
      realSingularHomologyEvaluation X n φ hφ := by
  let F : (realSingularChainComplex X).sc n ⟶ (realSingularChainComplex Y).sc n :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℝ) (ComplexShape.down ℕ) n).map
      (realSingularChainMap f hf)
  exact moduleHomologyEvaluation_naturality F φ _ ψ _ hcomm

theorem positiveRealSingularCycleClass_eq_zero_iff
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (z : (realSingularChainComplex X).X (n + 1))
    (hz : ((realSingularChainComplex X).d (n + 1) n).hom z = 0) :
    positiveRealSingularCycleClass X n z hz = 0 ↔
      ∃ w : (realSingularChainComplex X).X (n + 1 + 1),
        ((realSingularChainComplex X).d (n + 1 + 1) (n + 1)).hom w = z := by
  unfold positiveRealSingularCycleClass
  erw [moduleHomologyClass_eq_zero_iff]
  change (∃ w : (realSingularChainComplex X).X ((ComplexShape.down ℕ).prev (n + 1)),
    ((realSingularChainComplex X).d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1)).hom w = z) ↔ _
  rw [show (ComplexShape.down ℕ).prev (n + 1) = n + 1 + 1 from
    ChainComplex.prev ℕ (n + 1)]

end SingularCocycles

end Problem340

end

end OAI
