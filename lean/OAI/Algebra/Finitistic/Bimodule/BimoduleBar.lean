import OAI.Algebra.Finitistic.Bimodule.BimoduleTensor

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

section FreeMaps
variable (V W U : Type u) [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]

/-- Balanced tensor on a map of free modules, in the explicit field-tensor coordinates. -/
def freeMap (h : D ⊗[k] V →ₗ[D] D ⊗[k] W) : X ⊗[k] V →ₗ[D] X ⊗[k] W :=
  (descend k D X W).comp ((map k D X _ _ h).comp (insert k D X V))

/-- Coordinate change commutes with every free-module differential. -/
theorem freeMap_descend (h : D ⊗[k] V →ₗ[D] D ⊗[k] W)
    (z : tensor k D X (D ⊗[k] V)) :
    freeMap k D X V W h (descend k D X V z) =
      descend k D X W (map k D X _ _ h z) := by
  change descend k D X W (map k D X _ _ h (insert k D X V (descend k D X V z))) = _
  rw [show insert k D X V (descend k D X V z) = z from
    LinearMap.congr_fun (insert_descend k D X V) z]

theorem freeMap_comp (h : D ⊗[k] V →ₗ[D] D ⊗[k] W)
    (g : D ⊗[k] W →ₗ[D] D ⊗[k] U) :
    freeMap k D X V U (g.comp h) =
      (freeMap k D X W U g).comp (freeMap k D X V W h) := by
  apply LinearMap.ext
  intro z
  change descend k D X U (map k D X _ _ (g.comp h) (insert k D X V z)) =
    freeMap k D X W U g (descend k D X W (map k D X _ _ h (insert k D X V z)))
  rw [freeMap_descend, map_comp]
  rfl

@[simp] theorem freeMap_zero : freeMap k D X V W 0 = 0 := by
  apply LinearMap.ext
  intro z
  simp only [freeMap, LinearMap.comp_apply, map_zero, LinearMap.zero_apply, _root_.map_zero]
end FreeMaps

variable (N : Type u) [AddCommGroup N] [Module k N] [Module D N] [IsScalarTower k D N]

/-- The two-sided bar differential for arbitrary bimodule coefficients X. -/
def barDifferential (n : ℕ) : X ⊗[k] DerivedBar.term k D N (n+1) →ₗ[D]
    X ⊗[k] DerivedBar.term k D N n :=
  freeMap k D X _ _ (DerivedBar.differential k D N (n+1))

/-- Independent endpoint-minus-tail formula, including the noncommutative right action. -/
theorem barDifferential_tmul (n : ℕ) (x : X) (z : DerivedBar.term k D N (n+1)) :
    barDifferential k D X N n (x ⊗ₜ[k] z) =
      collapse k D X (DerivedBar.term k D N n) (x ⊗ₜ[k] z) -
        x ⊗ₜ[k] DerivedBar.differential k D N n z := by
  change descend k D X (DerivedBar.term k D N n)
    (map k D X _ _ (DerivedBar.differential k D N (n+1))
      (insert k D X (DerivedBar.term k D N (n+1)) (x ⊗ₜ[k] z))) = _
  rw [insert_tmul, map_quotient, DerivedBar.differential_succ_tmul, one_smul,
    TensorProduct.tmul_sub, _root_.map_sub, _root_.map_sub,
    descend_quotient, descend_quotient, collapse_tmul, MulOpposite.op_one, one_smul]

theorem barDifferential_sq (n : ℕ) :
    (barDifferential k D X N n).comp (barDifferential k D X N (n+1)) = 0 := by
  unfold barDifferential
  rw [← freeMap_comp, DerivedBar.differential_sq, freeMap_zero]

/-- Balanced X tensor of the actual free projective resolution of N. -/
def tensorResolution : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (tensor k D X (DerivedBar.term k D N (n+1))))
    (fun n => ModuleCat.ofHom (map k D X _ _ (DerivedBar.differential k D N (n+1))))
    (fun n => by
      apply ModuleCat.hom_ext
      change (map k D X _ _ (DerivedBar.differential k D N (n+1))).comp
        (map k D X _ _ (DerivedBar.differential k D N (n+1+1))) = 0
      rw [← map_comp, DerivedBar.differential_sq, map_zero])

/-- The explicit two-sided X,D,N bar complex, with no D-flatness assumption. -/
def barComplex : ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (X ⊗[k] DerivedBar.term k D N n))
    (fun n => ModuleCat.ofHom (barDifferential k D X N n))
    (fun n => ModuleCat.hom_ext (barDifferential_sq k D X N n))

/-- The explicit two-sided bar is isomorphic to genuine balanced tensor of the free resolution. -/
def tensorResolutionIso : tensorResolution k D X N ≅ barComplex k D X N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (freeEquiv k D X (DerivedBar.term k D N n)).toModuleIso)
    (by
      intro i j hij
      change j+1 = i at hij
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      simp only [tensorResolution, barComplex, ChainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearEquiv.toModuleIso_hom]
      exact freeMap_descend k D X (DerivedBar.term k D N (j+1))
        (DerivedBar.term k D N j) (DerivedBar.differential k D N (j+1)) z)
end DerivedBar.BimoduleTensor

end

end OAI
