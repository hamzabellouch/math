import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.PlethDual
import OAI.RepresentationTheory.FoulkesSixth.Vanishing
import OAI.RepresentationTheory.FoulkesSixth.Rows

namespace OAI

noncomputable section

namespace Foulkes
universe u
variable (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]

instance symAddCommGroup : AddCommGroup (Sym n V) := (Sym n V).addCommGroup
instance symModule : Module ℂ (Sym n V) := (Sym n V).module
instance symFinite [FiniteDimensional ℂ V] : FiniteDimensional ℂ (Sym n V) :=
  inferInstance
instance symFree : Module.Free ℂ (Sym n V) := inferInstance

end Foulkes

namespace Foulkes.Canonical
universe u
open Module MvPolynomial SymmetricTensor Polarization
variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {n : ℕ} (B : Basis (Fin n) ℂ V) (a b : ℕ)

def firstEquiv : Sym a V ≃ₗ[ℂ] R a n 1 :=
  (symEquiv a (oneEquiv V).symm).trans (Rows.equiv B a 1)

def firstMap : Sym a V →ₗ[ℂ] P a n :=
  (R a n 1).subtype.comp (firstEquiv B a).toLinearMap

lemma firstMap_mem (x : Sym a V) : firstMap B a x ∈ R a n 1 :=
  (firstEquiv B a x).property

@[simp] lemma firstMap_power (v : V) : firstMap B a (power a V v) = z (a := a) (B.equivFun v) := by
  change Rows.invariantMap B a 1
    (symMap a (oneEquiv V).symm.toLinearMap (power a V v)) = _
  rw [symMap_power, LinearEquiv.coe_coe, oneEquiv_symm]
  change Rows.tensorMap B a 1
    (PiTensorProduct.tprod ℂ (fun _ : Fin a => power 1 V v)) = _
  rw [Rows.tensorMap_powers]
  simp only [pureRows, pow_one, z]

def productPolynomial : Sym b (Sym a V) →ₗ[ℂ] P a n :=
  SymAlgebra.multiply b (firstMap B a)

@[simp] lemma productPolynomial_power (q : Sym a V) :
    productPolynomial B a b (power b (Sym a V) q) = firstMap B a q ^ b :=
  SymAlgebra.multiply_power b (firstMap B a) q

lemma productPolynomial_mem (x : Sym b (Sym a V)) : productPolynomial B a b x ∈ R a n b := by
  have h : Submodule.span ℂ (Set.range (power b (Sym a V))) ≤
      (R a n b).comap (productPolynomial B a b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    change productPolynomial B a b (power b (Sym a V) q) ∈ R a n b
    rw [productPolynomial_power]
    constructor
    · have hq := (firstMap_mem B a q).1.pow b
      simpa [W, Pi.smul_def] using hq
    · intro σ
      rw [map_pow, (firstMap_mem B a q).2 σ]
  rw [span_power] at h
  exact h (Submodule.mem_top : x ∈ ⊤)

lemma productPolynomial_project (q : Fin b → Sym a V) :
    productPolynomial B a b (project b (Sym a V) (PiTensorProduct.tprod ℂ q)) =
      ∏ i, firstMap B a (q i) := by
  exact (SymAlgebra.multiply_project b (firstMap B a) _).trans
    (SymAlgebra.tensorMul_tprod b (firstMap B a) q)

lemma products_in_range (y : Fin b → Fin n → ℂ) :
    (∏ j, z (a := a) (y j)) ∈ (productPolynomial B a b).range := by
  refine ⟨project b (Sym a V) (PiTensorProduct.tprod ℂ
    (fun j => power a V (B.equivFun.symm (y j)))), ?_⟩
  rw [productPolynomial_project]
  simp only [firstMap_power, LinearEquiv.apply_symm_apply]

theorem productPolynomial_range (ha : 1 ≤ a) (hb0 : 1 ≤ b) (hb : a*(a-1) ≤ b) :
    (productPolynomial B a b).range = R a n b := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact productPolynomial_mem B a b x
  · intro p hp
    by_contra hnot
    obtain ⟨l, hlp, hlrange⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hkill (f : P a n) (hf : f ∈ (productPolynomial B a b).range) : l f = 0 := by
      have hh : l f ∈ ((productPolynomial B a b).range).map l := Submodule.mem_map.mpr ⟨f,hf,rfl⟩
      rwa [hlrange, Submodule.mem_bot] at hh
    let lav := l.comp (Polarization.average a n)
    have hs : Vanishing.Symmetric lav := by
      intro σ f
      change l (Polarization.average a n (renameRow σ f)) = l (Polarization.average a n f)
      rw [Vanishing.average_renameRow]
    have hz : Vanishing.ProductsVanish lav b := by
      intro y
      change l (Polarization.average a n (∏ j, z (y j))) = 0
      rw [Polarization.average_eq (show (∏ j, z (a := a) (y j)) ∈ rowInvariants a n from by
        intro σ; simp)]
      exact hkill _ (products_in_range B a b y)
    have hh := Vanishing.vanishing a ha hb0 hb hs hz p hp.1
    change l (Polarization.average a n p) = 0 at hh
    rw [Polarization.average_eq hp.2] at hh
    exact hlp hh

def map : Sym b (Sym a V) →ₗ[ℂ] Sym a (Sym b V) :=
  (Rows.equiv B a b).symm.toLinearMap.comp
    ((productPolynomial B a b).codRestrict (R a n b) (productPolynomial_mem B a b))

@[simp] lemma map_polynomial (x : Sym b (Sym a V)) :
    Rows.invariantMap B a b (map B a b x) = productPolynomial B a b x := by
  change (Rows.equiv B a b
    ((Rows.equiv B a b).symm ⟨productPolynomial B a b x, productPolynomial_mem B a b x⟩) : P a n) = _
  rw [LinearEquiv.apply_symm_apply]

theorem surjective (ha : 1 ≤ a) (hb0 : 1 ≤ b) (hb : a*(a-1) ≤ b) :
    Function.Surjective (map B a b) := by
  intro x
  have hp : Rows.invariantMap B a b x ∈ (productPolynomial B a b).range := by
    rw [productPolynomial_range B a b ha hb0 hb]
    exact (Rows.equiv B a b x).property
  obtain ⟨y, hy⟩ := hp
  refine ⟨y, (Rows.invariantMap_injective B a b) ?_⟩
  rw [map_polynomial, hy]

end Foulkes.Canonical

namespace Foulkes.Canonical
universe u
open Module MvPolynomial SymmetricTensor Polarization
variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {n : ℕ} (B : Basis (Fin n) ℂ V) (a b : ℕ)

omit [FiniteDimensional ℂ V] in
section

def substitution (g : V →ₗ[ℂ] V) : P a n →ₐ[ℂ] P a n :=
  aeval (fun ik : Fin a × Fin n =>
    Rows.row ik.1 (SymPolynomial.linearPolynomial B (g (B ik.2))))

lemma linearPolynomial_basis (k : Fin n) : SymPolynomial.linearPolynomial B (B k) = X k := by
  classical
  simp only [SymPolynomial.linearPolynomial_apply, B.equivFun_self]
  simp

lemma substitution_row_linear (g : V →ₗ[ℂ] V) (i : Fin a) (v : V) :
    substitution B a g (Rows.row i (SymPolynomial.linearPolynomial B v)) =
      Rows.row i (SymPolynomial.linearPolynomial B (g v)) := by
  have hh : (substitution B a g).toLinearMap.comp
      ((Rows.row i).toLinearMap.comp (SymPolynomial.linearPolynomial B)) =
      (Rows.row i).toLinearMap.comp ((SymPolynomial.linearPolynomial B).comp g) := by
    apply B.ext
    intro k
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, linearPolynomial_basis]
    simp [Rows.row, substitution]
  exact DFunLike.congr_fun hh v

lemma substitution_rowForm (g : V →ₗ[ℂ] V) (i : Fin a) (v : V) :
    substitution B a g (rowForm i (B.equivFun v)) = rowForm i (B.equivFun (g v)) := by
  simpa only [Rows.row_linear] using substitution_row_linear B a g i v

lemma substitution_z (g : V →ₗ[ℂ] V) (v : V) :
    substitution B a g (z (a := a) (B.equivFun v)) = z (a := a) (B.equivFun (g v)) := by
  simp only [z, map_prod, substitution_rowForm]

lemma row_polynomial_natural (g : V →ₗ[ℂ] V) (i : Fin a) (q : Sym b V) :
    Rows.row i (SymPolynomial.polynomial B b (symMap b g q)) =
      substitution B a g (Rows.row i (SymPolynomial.polynomial B b q)) := by
  have hh : (Rows.row i).toLinearMap.comp ((SymPolynomial.polynomial B b).comp (symMap b g)) =
      (substitution B a g).toLinearMap.comp
        ((Rows.row i).toLinearMap.comp (SymPolynomial.polynomial B b)) := by
    apply symMap_ext
    intro v
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, symMap_power,
      SymPolynomial.polynomial_power, map_pow, substitution_row_linear]
  exact DFunLike.congr_fun hh q

lemma tensorMap_natural (g : V →ₗ[ℂ] V) (x : T a (Sym b V)) :
    Rows.tensorMap B a b (PiTensorProduct.map (fun _ : Fin a => symMap b g) x) =
      substitution B a g (Rows.tensorMap B a b x) := by
  have hh : (Rows.tensorMap B a b).comp (PiTensorProduct.map (fun _ : Fin a => symMap b g)) =
      (substitution B a g).toLinearMap.comp (Rows.tensorMap B a b) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      Rows.tensorMap_tprod, AlgHom.toLinearMap_apply, map_prod, row_polynomial_natural]
  exact DFunLike.congr_fun hh x

lemma invariantMap_natural (g : V →ₗ[ℂ] V) (x : Sym a (Sym b V)) :
    Rows.invariantMap B a b (symMap a (symMap b g) x) =
      substitution B a g (Rows.invariantMap B a b x) :=
  tensorMap_natural B a b g x

end

lemma firstMap_natural (g : V →ₗ[ℂ] V) (q : Sym a V) :
    firstMap B a (symMap a g q) = substitution B a g (firstMap B a q) := by
  have hh : (firstMap B a).comp (symMap a g) =
      (substitution B a g).toLinearMap.comp (firstMap B a) := by
    apply symMap_ext
    intro v
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, symMap_power,
      firstMap_power, substitution_z]
  exact DFunLike.congr_fun hh q

lemma productPolynomial_natural (g : V →ₗ[ℂ] V) (x : Sym b (Sym a V)) :
    productPolynomial B a b (symMap b (symMap a g) x) =
      substitution B a g (productPolynomial B a b x) := by
  have hh : (productPolynomial B a b).comp (symMap b (symMap a g)) =
      (substitution B a g).toLinearMap.comp (productPolynomial B a b) := by
    apply symMap_ext
    intro q
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, symMap_power,
      productPolynomial_power, firstMap_natural, map_pow]
  exact DFunLike.congr_fun hh x

theorem natural (g : V →ₗ[ℂ] V) (x : Sym b (Sym a V)) :
    map B a b (symMap b (symMap a g) x) = symMap a (symMap b g) (map B a b x) := by
  apply Rows.invariantMap_injective B a b
  rw [map_polynomial, invariantMap_natural, map_polynomial, productPolynomial_natural]

end Foulkes.Canonical

namespace Foulkes.PlethDual
universe u
open Module SymmetricTensor
variable (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

lemma natural_congr (g : V →ₗ[ℂ] V) (d : Sym a (Sym b (Dual ℂ V))) (x : Sym a (Sym b V)) :
    equiv a b V (symMap a (symMap b g.dualMap) d) x =
      equiv a b V d (symMap a (symMap b g) x) := by
  have hi : (dualEquiv b (V := V)).toLinearMap.comp (symMap b g.dualMap) =
      (symMap b g).dualMap.comp (dualEquiv b (V := V)).toLinearMap := by
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro v
    exact pairing_map b g q v
  have hs := congrArg (fun (f : Sym b (Dual ℂ V) →ₗ[ℂ] Dual ℂ (Sym b V)) =>
    symMap a f d) hi
  simp only [symMap_comp, LinearMap.comp_apply] at hs
  simp only [equiv_apply, hs]
  exact pairing_map a (symMap b g) _ x

end Foulkes.PlethDual

namespace Foulkes.Injection
universe u
open Module
variable (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def map : Sym a (Sym b V) →ₗ[ℂ] Sym b (Sym a V) :=
  (PlethDual.flipEquiv b a V).symm.toLinearMap.comp
    ((Canonical.map (Module.finBasis ℂ (Dual ℂ V)) a b).dualMap.comp
      (PlethDual.flipEquiv a b V).toLinearMap)

lemma adjoint (x : Sym a (Sym b V)) (d : Sym b (Sym a (Dual ℂ V))) :
    PlethDual.equiv b a V d (map a b V x) =
      PlethDual.equiv a b V (Canonical.map (Module.finBasis ℂ (Dual ℂ V)) a b d) x := by
  change PlethDual.flipEquiv b a V
    ((PlethDual.flipEquiv b a V).symm
      ((Canonical.map (Module.finBasis ℂ (Dual ℂ V)) a b).dualMap
        (PlethDual.flipEquiv a b V x))) d = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma injective (ha : 1 ≤ a) (hb0 : 1 ≤ b) (hb : a*(a-1) ≤ b) :
    Function.Injective (map a b V) :=
  (PlethDual.flipEquiv b a V).symm.injective.comp
    ((LinearMap.dualMap_injective_of_surjective
      (Canonical.surjective (Module.finBasis ℂ (Dual ℂ V)) a b ha hb0 hb)).comp
      (PlethDual.flipEquiv a b V).injective)

theorem natural (g : V →ₗ[ℂ] V) (x : Sym a (Sym b V)) :
    map a b V (symMap a (symMap b g) x) = symMap b (symMap a g) (map a b V x) := by
  apply (PlethDual.flipEquiv b a V).injective
  apply LinearMap.ext
  intro d
  change PlethDual.equiv b a V d (map a b V (symMap a (symMap b g) x)) =
    PlethDual.equiv b a V d (symMap b (symMap a g) (map a b V x))
  calc
    _ = PlethDual.equiv a b V (Canonical.map (Module.finBasis ℂ (Dual ℂ V)) a b d)
        (symMap a (symMap b g) x) := adjoint a b V _ d
    _ = PlethDual.equiv a b V
        (symMap a (symMap b g.dualMap) (Canonical.map (Module.finBasis ℂ (Dual ℂ V)) a b d)) x :=
      (PlethDual.natural a b V g _ x).symm
    _ = PlethDual.equiv a b V
        (Canonical.map (Module.finBasis ℂ (Dual ℂ V)) a b (symMap b (symMap a g.dualMap) d)) x := by
      rw [Canonical.natural]
    _ = PlethDual.equiv b a V (symMap b (symMap a g.dualMap) d) (map a b V x) :=
      (adjoint a b V x _).symm
    _ = _ := PlethDual.natural b a V g d (map a b V x)

theorem quadratic_comparison (ha : 2 ≤ a) (hb : a*(a-1) ≤ b) :
    ∃ i : Sym a (Sym b V) →ₗ[ℂ] Sym b (Sym a V), Function.Injective i ∧
      ∀ (g : V ≃ₗ[ℂ] V) (x : Sym a (Sym b V)),
        i (symMap a (symMap b g.toLinearMap) x) = symMap b (symMap a g.toLinearMap) (i x) := by
  have hb0 : 1 ≤ b := le_trans (Nat.mul_pos (by omega) (by omega)) hb
  exact ⟨map a b V, injective a b V (by omega) hb0 hb, fun g x => natural a b V g.toLinearMap x⟩

theorem sixth_large (b : ℕ) (hb : 30 ≤ b)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    ∃ i : Sym 6 (Sym b V) →ₗ[ℂ] Sym b (Sym 6 V), Function.Injective i ∧
      ∀ (g : V ≃ₗ[ℂ] V) (x : Sym 6 (Sym b V)),
        i (symMap 6 (symMap b g.toLinearMap) x) = symMap b (symMap 6 g.toLinearMap) (i x) :=
  quadratic_comparison 6 b V (by omega) (by omega)

end Foulkes.Injection

end

end OAI
