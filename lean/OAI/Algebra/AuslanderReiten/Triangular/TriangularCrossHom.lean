import OAI.Algebra.AuslanderReiten.Triangular.TriangularCochain
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCategory
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomTransport

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory CochainComplex.HomComplex

universe u

variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def crossHomAdd (M N : ModuleCat.{u} R) :
    (M ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj N) →+
      ((jFunctor k R F).obj M ⟶ (eFunctor k R F).obj N) where
  toFun f := ModuleCat.ofHom (jHom f.hom)
  map_zero' := by
    apply ModuleCat.hom_ext
    apply jHomEquiv.injective
    exact map_zero jHomEquiv |>.symm
  map_add' f g := by
    apply ModuleCat.hom_ext
    apply jHomEquiv.injective
    ext z
    rfl

theorem crossHomAdd_source {M N L : ModuleCat.{u} R} (f : M ⟶ N)
    (g : N ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj L) :
    crossHomAdd M L (f ≫ g) = (jFunctor k R F).map f ≫ crossHomAdd N L g := by
  apply ModuleCat.hom_ext
  apply jHomEquiv.injective
  rfl

theorem crossHomAdd_target {M N L : ModuleCat.{u} R}
    (f : M ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj N)
    (g : N ⟶ L) :
    crossHomAdd M L (f ≫ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).map g) =
      crossHomAdd M N f ≫ (eFunctor k R F).map g := by
  apply ModuleCat.hom_ext
  apply jHomEquiv.injective
  rfl

abbrev tensorCochain (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).mapHomologicalComplex _).obj P

variable (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)

def crossCochainEquiv : Cochain P (tensorCochain (k := k) (F := F) Q) n ≃+
    Cochain (jCochain (k := k) (F := F) P) (eCochain (k := k) (F := F) Q) n where
  toFun x := Cochain.mk fun p q hpq => crossHomAdd (P.X p) (Q.X q) (x.v p q hpq)
  invFun x := Cochain.mk fun p q hpq => ModuleCat.ofHom (TriangularModule.bottomMap (x.v p q hpq).hom)
  left_inv x := by
    apply Cochain.ext
    intro p q hpq
    rfl
  right_inv x := by
    apply Cochain.ext
    intro p q hpq
    apply ModuleCat.hom_ext
    exact jHom_bottomMap _
  map_add' x y := by
    apply Cochain.ext
    intro p q hpq
    exact map_add (crossHomAdd (P.X p) (Q.X q)) (x.v p q hpq) (y.v p q hpq)

@[simp] theorem crossCochainEquiv_v
    (x : Cochain P (tensorCochain (k := k) (F := F) Q) n) (p q : ℤ) (hpq : p+n=q) :
    (crossCochainEquiv P Q n x).v p q hpq = crossHomAdd (P.X p) (Q.X q) (x.v p q hpq) := rfl

theorem crossCochainEquiv_differential (m : ℤ)
    (x : Cochain P (tensorCochain (k := k) (F := F) Q) n) :
    δ n m (crossCochainEquiv P Q n x) = crossCochainEquiv P Q m (δ n m x) := by
  by_cases hnm : n+1=m
  · apply Cochain.ext
    intro p q hpq
    simp only [δ_v n m hnm _ p q hpq (q-1) (p+1) rfl rfl, crossCochainEquiv_v]
    let x₁ : P.X p ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj (Q.X (q-1)) :=
      x.v p (q-1) (by omega)
    let x₂ : P.X (p+1) ⟶ (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).obj (Q.X q) :=
      x.v (p+1) q (by omega)
    change crossHomAdd _ _ x₁ ≫ (eFunctor k R F).map (Q.d (q-1) q) +
      m.negOnePow • ((jFunctor k R F).map (P.d p (p+1)) ≫ crossHomAdd _ _ x₂) =
      crossHomAdd (P.X p) (Q.X q) (x₁ ≫
        (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)).map (Q.d (q-1) q) +
          m.negOnePow • (P.d p (p+1) ≫ x₂))
    rw [map_add]
    simp only [Units.smul_def, map_zsmul]
    rw [crossHomAdd_target, crossHomAdd_source]
  · rw [δ_shape n m hnm, δ_shape n m hnm, map_zero]

def crossFullHomEquivalence : FullHomEquivalence P (tensorCochain (k := k) (F := F) Q)
    (jCochain (k := k) (F := F) P) (eCochain (k := k) (F := F) Q) where
  cochain := crossCochainEquiv P Q
  differential := crossCochainEquiv_differential P Q

def crossCohomologyEquiv :
    CohomologyClass P (tensorCochain (k := k) (F := F) Q) n ≃+
      CohomologyClass (jCochain (k := k) (F := F) P) (eCochain (k := k) (F := F) Q) n :=
  (crossFullHomEquivalence P Q).cohomology n

variable {P Q n}

def crossChainMap (f : P ⟶ tensorCochain (k := k) (F := F) Q) :
    jCochain (k := k) (F := F) P ⟶ eCochain (k := k) (F := F) Q where
  f i := crossHomAdd (P.X i) (Q.X i) (f.f i)
  comm' i j _ := by
    change crossHomAdd _ _ (f.f i) ≫ (eFunctor k R F).map (Q.d i j) =
      (jFunctor k R F).map (P.d i j) ≫ crossHomAdd _ _ (f.f j)
    exact (crossHomAdd_target (f.f i) (Q.d i j)).symm.trans
      ((congrArg (crossHomAdd (P.X i) (Q.X j)) (f.comm i j)).trans
        (crossHomAdd_source (P.d i j) (f.f j)))

theorem crossChainMap_ofHom (f : P ⟶ tensorCochain (k := k) (F := F) Q) :
    crossCochainEquiv P Q 0 (Cochain.ofHom f) = Cochain.ofHom (crossChainMap f) := by
  apply Cochain.ext₀
  intro p
  simp only [crossCochainEquiv_v, Cochain.ofHom_v, crossChainMap]

variable {L : CochainComplex (ModuleCat.{u} R) ℤ} {m : ℤ}

theorem crossCochainEquiv_source (a : Cochain P Q n)
    (b : Cochain Q (tensorCochain (k := k) (F := F) L) m) :
    crossCochainEquiv P L (n+m) (a.comp b rfl) =
      (a.map (jFunctor k R F)).comp (crossCochainEquiv Q L m b) rfl := by
  apply Cochain.ext
  intro p q hpq
  simp only [crossCochainEquiv_v, Cochain.comp_v a b rfl p (p+n) q rfl (by omega),
    Cochain.comp_v (a.map (jFunctor k R F)) (crossCochainEquiv Q L m b) rfl
      p (p+n) q rfl (by omega), Cochain.map_v]
  exact crossHomAdd_source _ _

theorem crossCochainEquiv_target
    (a : Cochain P (tensorCochain (k := k) (F := F) Q) n) (b : Cochain Q L m) :
    crossCochainEquiv P L (n+m)
        (a.comp (b.map (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F))) rfl) =
      (crossCochainEquiv P Q n a).comp (b.map (eFunctor k R F)) rfl := by
  apply Cochain.ext
  intro p q hpq
  simp only [crossCochainEquiv_v,
    Cochain.comp_v a (b.map (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F))) rfl
      p (p+n) q rfl (by omega),
    Cochain.comp_v (crossCochainEquiv P Q n a) (b.map (eFunctor k R F)) rfl
      p (p+n) q rfl (by omega), Cochain.map_v]
  exact crossHomAdd_target _ _

end ArExplicit.TriangularInduction

end

end OAI
