import OAI.RepresentationTheory.RestrictedTilting.BoundedOriginTarget

namespace OAI

namespace FiberFunctorProof
open scoped Pointwise
universe u
noncomputable section
variable {k : Type u} [Field k]
local notation "A" => MvPolynomial (Fin 2) k
variable (M N : Type u) [AddCommGroup M] [Module k M] [Module (MvPolynomial (Fin 2) k) M]
  [IsScalarTower k (MvPolynomial (Fin 2) k) M] [AddCommGroup N] [Module k N] [Module (MvPolynomial (Fin 2) k) N] [IsScalarTower k (MvPolynomial (Fin 2) k) N]

abbrev planeFibreRelations (a : Fin 2 → k) : Submodule k M :=
  ((planePointIdeal a • (⊤ : Submodule A M))).restrictScalars k

lemma planeFibre_mk_smul (a : Fin 2 → k) (P : A) (m : M) :
    (planeFibreRelations M a).mkQ (P • m) =
      MvPolynomial.eval a P • (planeFibreRelations M a).mkQ m := by
  rw [← map_smul]
  apply (Submodule.Quotient.eq _).mpr
  change P • m - MvPolynomial.eval a P • m ∈ planePointIdeal a • (⊤ : Submodule A M)
  have h : P - MvPolynomial.C (MvPolynomial.eval a P) ∈ planePointIdeal a := by
    simp [planePointIdeal, RingHom.mem_ker]
  convert Submodule.smul_mem_smul h (show m ∈ (⊤ : Submodule A M) from trivial) using 1
  simp only [sub_smul, MvPolynomial.C_eq_algebraMap, algebraMap_smul]

lemma planeFibre_map_mem (a : Fin 2 → k) (f : M →ₗ[A] N) :
    planeFibreRelations M a ≤ (planeFibreRelations N a).comap (f.restrictScalars k) := by
  intro m hm
  change f m ∈ planePointIdeal a • (⊤ : Submodule A N)
  have hf : (planePointIdeal a • (⊤ : Submodule A M)).map f ≤
      planePointIdeal a • (⊤ : Submodule A N) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right (planePointIdeal a) le_top
  exact hf (Submodule.mem_map_of_mem hm)

def planeFibreMap (a : Fin 2 → k) (f : M →ₗ[A] N) :
    (M ⧸ planeFibreRelations M a) →ₗ[k] (N ⧸ planeFibreRelations N a) :=
  (planeFibreRelations M a).mapQ (planeFibreRelations N a) (f.restrictScalars k)
    (planeFibre_map_mem M N a f)

@[simp] lemma planeFibreMap_mk (a : Fin 2 → k) (f : M →ₗ[A] N) (m : M) :
    planeFibreMap M N a f ((planeFibreRelations M a).mkQ m) =
      (planeFibreRelations N a).mkQ (f m) := rfl

 

def planeFibreEquivOfSplit (a : Fin 2 → k) (f : M →ₗ[A] N) (g : N →ₗ[A] M)
    (s : A) (hs : MvPolynomial.eval a s = 1)
    (hgf : ∀ m, g (f m) = s • m) (hfg : ∀ n, f (g n) = s • n) :
    (M ⧸ planeFibreRelations M a) ≃ₗ[k] (N ⧸ planeFibreRelations N a) :=
  LinearEquiv.ofLinearMap (planeFibreMap M N a f) (planeFibreMap N M a g)
    (by apply LinearMap.ext; intro n; obtain ⟨n,rfl⟩ := (planeFibreRelations N a).mkQ_surjective n
        change (planeFibreRelations N a).mkQ (f (g n)) = (planeFibreRelations N a).mkQ n
        rw [hfg, planeFibre_mk_smul, hs, one_smul])
    (by apply LinearMap.ext; intro m; obtain ⟨m,rfl⟩ := (planeFibreRelations M a).mkQ_surjective m
        change (planeFibreRelations M a).mkQ (g (f m)) = (planeFibreRelations M a).mkQ m
        rw [hgf, planeFibre_mk_smul, hs, one_smul])

variable (ι : Type u) [Fintype ι] [DecidableEq ι]

def planeVectorEval (a : Fin 2 → k) : (ι → A) →ₗ[k] (ι → k) where
  toFun v i := MvPolynomial.eval a (v i)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

def planeVectorConstant : (ι → k) →ₗ[k] (ι → A) where
  toFun v i := MvPolynomial.C (v i)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp [MvPolynomial.C_mul, Algebra.smul_def]

omit [Fintype ι] [DecidableEq ι] in
lemma planeVectorEval_relations (a : Fin 2 → k) :
    planeFibreRelations (ι → A) a ≤ (planeVectorEval ι a).ker := by
  intro v hv
  change v ∈ planePointIdeal a • (⊤ : Submodule A (ι → A)) at hv
  change planeVectorEval ι a v = 0
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro r hr n hn
    ext i
    change MvPolynomial.eval a (r * n i) = 0
    have hr0 : MvPolynomial.eval a r = 0 := hr
    simp [hr0]
  · intro x y hx hy
    simp only [map_add, hx, hy, add_zero]

def planeFreeFibreEval (a : Fin 2 → k) :
    ((ι → A) ⧸ planeFibreRelations (ι → A) a) →ₗ[k] (ι → k) :=
  (planeFibreRelations (ι → A) a).liftQ (planeVectorEval ι a) (planeVectorEval_relations ι a)

lemma planeFreeFibre_constant_eval (a : Fin 2 → k) (v : ι → A) :
    (planeFibreRelations (ι → A) a).mkQ (planeVectorConstant ι (planeVectorEval ι a v)) =
      (planeFibreRelations (ι → A) a).mkQ v := by
  apply (Submodule.Quotient.eq _).mpr
  change planeVectorConstant ι (planeVectorEval ι a v) - v ∈
    planePointIdeal a • (⊤ : Submodule A (ι → A))
  have he : planeVectorConstant ι (planeVectorEval ι a v) - v =
      ∑ i : ι, (MvPolynomial.C (MvPolynomial.eval a (v i)) - v i) • Pi.single i (1 : A) := by
    ext j
    simp [planeVectorConstant, planeVectorEval, Pi.single_apply]
  rw [he]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem_smul _ (Submodule.mem_top)
  simp [planePointIdeal, RingHom.mem_ker]

def planeFreeFibreEquiv (a : Fin 2 → k) :
    ((ι → A) ⧸ planeFibreRelations (ι → A) a) ≃ₗ[k] (ι → k) :=
  LinearEquiv.ofLinearMap (planeFreeFibreEval ι a)
    ((planeFibreRelations (ι → A) a).mkQ.comp (planeVectorConstant ι))
    (by apply LinearMap.ext; intro v; ext i; simp [planeFreeFibreEval, planeVectorEval, planeVectorConstant])
    (by apply LinearMap.ext; intro v; obtain ⟨v,rfl⟩ := (planeFibreRelations (ι → A) a).mkQ_surjective v
        exact planeFreeFibre_constant_eval ι a v)

@[simp] lemma planeFreeFibreEquiv_mk (a : Fin 2 → k) (v : ι → A) :
    planeFreeFibreEquiv ι a ((planeFibreRelations (ι → A) a).mkQ v) = planeVectorEval ι a v := rfl

end
end FiberFunctorProof

end OAI
