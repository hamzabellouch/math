import Mathlib
import OAI.GroupTheory.FiniteType.ProductCoefficient

namespace OAI

noncomputable section
open CategoryTheory
namespace Representation
open scoped _root_.Representation
open _root_.TensorProduct
variable {k G V W X : Type*} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]
  {ρ : Representation k G V} {σ : Representation k G W}

def coinvariantsLTensorEquiv (τ : Representation k G X) (e : ρ.Equiv σ) :
    (τ.tprod ρ).Coinvariants ≃ₗ[k] (τ.tprod σ).Coinvariants :=
  LinearEquiv.ofLinearMap
    (_root_.Representation.Coinvariants.map _ _ (e.toIntertwiningMap.lTensor τ))
    (_root_.Representation.Coinvariants.map _ _ (e.symm.toIntertwiningMap.lTensor τ))
    (by
      apply _root_.Representation.Coinvariants.hom_ext
      apply _root_.TensorProduct.ext
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro b
      change _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] e (e.symm b)) = _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] b)
      rw [_root_.Representation.Equiv.apply_symm_apply])
    (by
      apply _root_.Representation.Coinvariants.hom_ext
      apply _root_.TensorProduct.ext
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro b
      change _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] e.symm (e b)) = _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] b)
      rw [_root_.Representation.Equiv.symm_apply_apply])

@[simp] lemma coinvariantsLTensorEquiv_mk_tmul (τ : Representation k G X)
    (e : ρ.Equiv σ) (a : X) (b : V) :
    coinvariantsLTensorEquiv τ e (_root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] b)) =
      _root_.Representation.Coinvariants.mk _ (a ⊗ₜ[k] e b) := rfl

end Representation

namespace RelativeStandardFree
open MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (k G : Type) [CommRing k] [Group G] (A : Rep k G)

def repEquiv (n : ℕ) : (Rep.diagonal k G (n+1)).ρ.Equiv (Rep.free k G (Fin n → G)).ρ :=
  Representation.Equiv.mk (linearEquiv k G n) (linearEquiv_intertwines k G n)

@[simp] lemma repEquiv_apply (n : ℕ) (z : MonoidAlgebra k (Fin (n+1) → G)) :
    repEquiv k G n z = linearEquiv k G n z := rfl

def freeCoinvariantEquiv (n : ℕ) :
    (A.ρ.tprod (Representation.free k G (Fin n → G))).Coinvariants ≃ₗ[k]
      ((Fin n → G) →₀ A) := by
  classical
  exact Rep.coinvariantsTensorFreeLEquiv A (Fin n → G)

def coinvariantEquiv (n : ℕ) :
    (A ⊗ Rep.diagonal k G (n+1)).ρ.Coinvariants ≃ₗ[k] ((Fin n → G) →₀ A) :=
  (Representation.coinvariantsLTensorEquiv A.ρ (repEquiv k G n)).trans
    (freeCoinvariantEquiv k G A n)

@[simp] lemma coinvariantEquiv_mk_tmul_single (n : ℕ) (a : A)
    (c : Fin (n+1) → G) (r : k) :
    coinvariantEquiv k G A n (Coinvariants.mk _ (a ⊗ₜ[k] MonoidAlgebra.single c r)) =
      Finsupp.single (fun i => (c 0)⁻¹*c i.succ) (r • A.ρ (c 0)⁻¹ a) := by
  classical
  change Rep.coinvariantsTensorFreeToFinsupp A (Fin n → G)
    (Representation.coinvariantsLTensorEquiv A.ρ (repEquiv k G n)
      (Coinvariants.mk _ (a ⊗ₜ[k] MonoidAlgebra.single c r))) = _
  rw [coinvariantsLTensorEquiv_mk_tmul,repEquiv_apply,linearEquiv_single]
  exact Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single A a _ _ r

end RelativeStandardFree

namespace ListChains
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

def standardProductEquiv (n : ℕ) :
    ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ.Coinvariants ≃ₗ[ℤ]
      productChains G I C n :=
  (RelativeStandardFree.coinvariantEquiv ℤ G (ProductCoefficient.rep G I C) n).trans
    (productTupleEquiv G I C n)

lemma mapChain_relative_tuple (n : ℕ) (s : Fin (n+1) → G) :
    mapChain G (fun x => s 0*x)
      (Finsupp.single (1,List.ofFn (fun i : Fin n => (s 0)⁻¹*s i.succ)) 1) =
        fromTuples G n (Finsupp.single s 1) := by
  simp only [fromTuples_single,mapChain_single,List.map_ofFn,mul_one]
  congr 3
  funext i
  exact mul_inv_cancel_left _ _

lemma place_shifted_tuple (n : ℕ) (s : Fin (n+1) → G) (a : C × G →₀ ℤ) :
    place G C (ProductCoefficient.rightShift G C (s 0)⁻¹ a)
      (Finsupp.single (1,List.ofFn (fun i : Fin n => (s 0)⁻¹*s i.succ)) 1) =
        place G C a (fromTuples G n (Finsupp.single s 1)) := by
  rw [← mapChain_relative_tuple]
  have h := place_rightShift_translate G C
    (ProductCoefficient.rightShift G C (s 0)⁻¹ a)
    (Finsupp.single (1,List.ofFn (fun i : Fin n => (s 0)⁻¹*s i.succ)) 1) (s 0)
  have he : ProductCoefficient.rightShift G C (s 0)
      (ProductCoefficient.rightShift G C (s 0)⁻¹ a) = a := by
    rw [← LinearMap.comp_apply,← ProductCoefficient.rightShift_mul,mul_inv_cancel,
      ProductCoefficient.rightShift_one,LinearMap.id_apply]
  rw [he] at h
  exact h.symm

@[simp] lemma standardProductEquiv_mk_tmul_single (n : ℕ)
    (a : ProductCoefficient.Module G I C) (s : Fin (n+1) → G) (r : ℤ) (i : I) :
    (standardProductEquiv G I C n
      (Coinvariants.mk _ (a ⊗ₜ[ℤ] MonoidAlgebra.single s r))).val i =
        place G C (a i) (fromTuples G n (Finsupp.single s r)) := by
  change (productTupleEquiv G I C n
    (RelativeStandardFree.coinvariantEquiv ℤ G (ProductCoefficient.rep G I C) n
      (Coinvariants.mk _ (a ⊗ₜ[ℤ] MonoidAlgebra.single s r)))).val i = _
  rw [RelativeStandardFree.coinvariantEquiv_mk_tmul_single,productTupleEquiv_single_place]
  change place G C (r • ProductCoefficient.rightShift G C (s 0)⁻¹ (a i)) _ = _
  rw [map_smul,LinearMap.smul_apply,place_shifted_tuple]
  have hs : Finsupp.single s r = r • Finsupp.single s (1 : ℤ) := by
    simp [Finsupp.smul_single]
  rw [hs,map_smul,map_smul]

lemma standardProductEquiv_mk_tmul (n : ℕ) (a : ProductCoefficient.Module G I C)
    (z : MonoidAlgebra ℤ (Fin (n+1) → G)) (i : I) :
    (standardProductEquiv G I C n (Coinvariants.mk _ (a ⊗ₜ[ℤ] z))).val i =
      place G C (a i) (fromTuples G n (MonoidAlgebra.coeffLinearEquiv ℤ z)) := by
  let L := (LinearMap.proj i).comp ((productChains G I C n).subtype.comp
    ((standardProductEquiv G I C n).toLinearMap.comp
      ((Coinvariants.mk _).comp ((TensorProduct.mk ℤ _ _) a))))
  have h : L = (place G C (a i)).comp
      ((fromTuples G n).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap) := by
    apply MonoidAlgebra.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    exact standardProductEquiv_mk_tmul_single G I C n a s r i
  exact LinearMap.congr_fun h z

end ListChains

namespace ControlledChains

variable (G : Type) [Group G]

abbrev Simplex (n : ℕ) := Fin (n+1) → G
abbrev Chain (n : ℕ) := Simplex G n →₀ ℤ

def boundary (n : ℕ) : Chain G (n+1) →ₗ[ℤ] Chain G n :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap ∘ₗ
    Rep.standardComplex.d ℤ G (n+1) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap

omit [Group G] in
@[simp] lemma boundary_single (n : ℕ) (c : Simplex G (n+1)) (r : ℤ) :
    boundary G n (Finsupp.single c r) =
      ∑ p : Fin (n+2), Finsupp.single (c ∘ p.succAbove) (r * (-1 : ℤ) ^ p.val) :=
  by
    simp only [boundary, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    simpa using congrArg (MonoidAlgebra.coeffLinearEquiv ℤ)
      (Rep.standardComplex.d_single (k := ℤ) c r)

lemma boundary_boundary (n : ℕ) (c : Chain G (n+2)) :
    boundary G n (boundary G (n+1) c) = 0 := by
  let c' : MonoidAlgebra ℤ (Simplex G (n+2)) :=
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm c
  have h := congrArg (fun h : (Rep.standardComplex ℤ G).X (n+2) ⟶
    (Rep.standardComplex ℤ G).X n => h.hom c')
    ((Rep.standardComplex ℤ G).d_comp_d (n+2) (n+1) n)
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply,
    Rep.standardComplex.d_apply, Rep.zero_hom,
    Representation.IntertwiningMap.coe_zero, Pi.zero_apply] at h
  change (MonoidAlgebra.coeffLinearEquiv ℤ)
    (Rep.standardComplex.d ℤ G (n+1) (Rep.standardComplex.d ℤ G (n+2) c')) = 0
  exact (congrArg (MonoidAlgebra.coeffLinearEquiv ℤ) h).trans rfl

def mapChain {K : Type} (f : G → K) (n : ℕ) : Chain G n →ₗ[ℤ] Chain K n :=
  Finsupp.lmapDomain ℤ ℤ (fun c => f ∘ c)

omit [Group G] in
@[simp] lemma mapChain_single {K : Type} (f : G → K) (n : ℕ)
    (c : Simplex G n) (r : ℤ) :
    mapChain G f n (Finsupp.single c r) = Finsupp.single (f ∘ c) r := by
  simp [mapChain]

omit [Group G] in
lemma boundary_mapChain {K : Type} (f : G → K) (n : ℕ) (c : Chain G (n+1)) :
    boundary K n (mapChain G f (n+1) c) = mapChain G f n (boundary G n c) := by
  have h : boundary K n ∘ₗ mapChain G f (n+1) =
      mapChain G f n ∘ₗ boundary G n := by
    apply Finsupp.lhom_ext
    intro q r
    simp only [LinearMap.comp_apply, boundary_single, mapChain_single, map_sum,
      Function.comp_assoc]
  exact LinearMap.congr_fun h c

def cone (g : G) (n : ℕ) : Chain G n →ₗ[ℤ] Chain G (n+1) :=
  Finsupp.lmapDomain ℤ ℤ (fun c : Simplex G n => (Fin.cons g c : Simplex G (n+1)))

omit [Group G] in
@[simp] lemma cone_single (g : G) (n : ℕ) (q : Simplex G n) (r : ℤ) :
    cone G g n (Finsupp.single q r) = Finsupp.single (Fin.cons g q) r := by
  simp [cone]

omit [Group G] in
lemma boundary_cone (g : G) (n : ℕ) (c : Chain G (n+1)) :
    boundary G (n+1) (cone G g (n+1) c) + cone G g n (boundary G n c) = c := by
  have h : boundary G (n+1) ∘ₗ cone G g (n+1) +
      cone G g n ∘ₗ boundary G n = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro q r
    simp only [LinearMap.add_apply, LinearMap.comp_apply, cone_single,
      boundary_single, map_sum, LinearMap.id_apply]
    rw [Fin.sum_univ_succ]
    have hz : Fin.cons g q ∘ (0 : Fin (n+3)).succAbove = q := by
      ext i
      simp [Fin.succAbove_zero]
    rw [hz]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      Fin.cons_comp_succ_succAbove, pow_succ, mul_neg, Finsupp.single_neg]
    have hn : (∑ i : Fin (n+2), -Finsupp.single (Fin.cons g (i.removeNth q))
        (r * (-1 : ℤ) ^ i.val)) =
        -(∑ i : Fin (n+2), Finsupp.single (Fin.cons g (q ∘ i.succAbove) : Simplex G (n+1))
          (r * (-1 : ℤ) ^ i.val)) := by
      rw [← Finset.sum_neg_distrib]
      rfl
    rw [hn]
    abel
  exact LinearMap.congr_fun h c

def augmentation : Chain G 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : Simplex G 0 => (1 : ℤ))

omit [Group G] in
@[simp] lemma augmentation_single (q : Simplex G 0) (r : ℤ) :
    augmentation G (Finsupp.single q r) = r := by
  simp [augmentation]

omit [Group G] in
lemma boundary_cone_zero (g : G) (c : Chain G 0) :
    boundary G 0 (cone G g 0 c) =
      c - Finsupp.single (fun _ : Fin 1 => g) (augmentation G c) := by
  have h : boundary G 0 ∘ₗ cone G g 0 =
      LinearMap.id - Finsupp.lsingle (fun _ : Fin 1 => g) ∘ₗ augmentation G := by
    apply Finsupp.lhom_ext
    intro q r
    simp only [LinearMap.comp_apply, cone_single, boundary_single,
      LinearMap.sub_apply, LinearMap.id_apply, augmentation_single, Finsupp.lsingle_apply]
    rw [Fin.sum_univ_two]
    have h0 : Fin.cons g q ∘ (0 : Fin 2).succAbove = q := by ext i; simp
    have h1 : Fin.cons g q ∘ (1 : Fin 2).succAbove = (fun _ : Fin 1 => g) := by
      ext i
      fin_cases i
      rfl
    rw [h0, h1]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, mul_neg_one,
      Finsupp.single_neg, sub_eq_add_neg]
  exact LinearMap.congr_fun h c

omit [Group G] in
lemma augmentation_boundary (c : Chain G 1) : augmentation G (boundary G 0 c) = 0 := by
  have h : augmentation G ∘ₗ boundary G 0 = 0 := by
    apply Finsupp.lhom_ext
    intro q r
    simp only [LinearMap.comp_apply, boundary_single, map_sum, augmentation_single,
      LinearMap.zero_apply]
    simp [Fin.sum_univ_two]
  exact LinearMap.congr_fun h c

end ControlledChains

end

end OAI
