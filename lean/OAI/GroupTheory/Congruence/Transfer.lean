import Mathlib

namespace OAI

noncomputable section

/-!
Odd-index transfer, comparison of bar resolutions, and homology-coinvariant models.
-/

section
open CategoryTheory
open scoped BigOperators

namespace CoboundaryExpanders.Transfer

section
open Representation

variable {k G V W : Type*} [CommRing k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def inclusion (ρ : Representation k G V) (S : Subgroup G) :
    Coinvariants (ρ.comp S.subtype) →ₗ[k] ρ.Coinvariants :=
  Coinvariants.lift _ (Coinvariants.mk ρ) fun s => by
    ext v
    exact Coinvariants.mk_self_apply ρ s v

@[simp] theorem inclusion_mk (ρ : Representation k G V) (S : Subgroup G) (v : V) :
    inclusion ρ S (Coinvariants.mk (ρ.comp S.subtype) v) = Coinvariants.mk ρ v := rfl

variable (ρ : Representation k G V) (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

omit [Fintype (G ⧸ S)] in
@[simp] theorem quotient_action_mk (g : G) (v : V) :
    ρ.quotientToCoinvariants S (g : G ⧸ S) (Coinvariants.mk _ v) =
      Coinvariants.mk _ (ρ g v) := rfl

def normTransfer : ρ.Coinvariants →ₗ[k] Coinvariants (ρ.comp S.subtype) :=
  Coinvariants.lift _
    ((ρ.quotientToCoinvariants S).norm ∘ₗ Coinvariants.mk (ρ.comp S.subtype)) fun g => by
      ext v
      change (ρ.quotientToCoinvariants S).norm (Coinvariants.mk _ (ρ g v)) = _
      rw [← quotient_action_mk]
      exact Representation.norm_self_apply _ _ _

@[simp] theorem normTransfer_mk (v : V) :
    normTransfer ρ S (Coinvariants.mk ρ v) =
      ∑ q : G ⧸ S, ρ.quotientToCoinvariants S q (Coinvariants.mk _ v) := by
  simp [normTransfer, Representation.norm]

omit [Fintype (G ⧸ S)] in
@[simp] theorem inclusion_quotient_action (q : G ⧸ S)
    (v : Coinvariants (ρ.comp S.subtype)) :
    inclusion ρ S (ρ.quotientToCoinvariants S q v) = inclusion ρ S v := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    induction v using Coinvariants.induction_on with
    | h v => simp

theorem inclusion_normTransfer :
    inclusion ρ S ∘ₗ normTransfer ρ S =
      (Fintype.card (G ⧸ S) : k) • LinearMap.id := by
  apply Coinvariants.hom_ext
  ext v
  simp [LinearMap.comp_apply, map_sum, nsmul_eq_mul, Nat.cast_smul_eq_nsmul]

variable {ρ S}

omit [S.Normal] [Fintype (G ⧸ S)] in
theorem inclusion_natural {τ : Representation k G W} (φ : ρ.IntertwiningMap τ) :
    Coinvariants.map ρ τ φ ∘ₗ inclusion ρ S =
      inclusion τ S ∘ₗ Coinvariants.map (ρ.comp S.subtype) (τ.comp S.subtype)
        ⟨φ.toLinearMap, fun s => φ.isIntertwining' s⟩ := by
  apply Coinvariants.hom_ext
  ext v
  rfl

theorem normTransfer_natural {τ : Representation k G W} (φ : ρ.IntertwiningMap τ) :
    Coinvariants.map (ρ.comp S.subtype) (τ.comp S.subtype)
        ⟨φ.toLinearMap, fun s => φ.isIntertwining' s⟩ ∘ₗ normTransfer ρ S =
      normTransfer τ S ∘ₗ Coinvariants.map ρ τ φ := by
  apply Coinvariants.hom_ext
  ext v
  simp only [LinearMap.comp_apply, normTransfer_mk, map_sum, Coinvariants.map_mk]
  apply Finset.sum_congr rfl
  intro q _
  induction q using QuotientGroup.induction_on with
  | H g =>
    simp only [quotient_action_mk, Coinvariants.map_mk]
    exact congrArg (Coinvariants.mk _) (LinearMap.congr_fun (φ.isIntertwining' g) v)

end

universe u
variable {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

abbrev subgroupCoinvariantsFunctor : Rep k G ⥤ ModuleCat k :=
  Rep.resFunctor S.subtype ⋙ Rep.coinvariantsFunctor k S

def inclusionNatTrans : subgroupCoinvariantsFunctor (k := k) S ⟶
    Rep.coinvariantsFunctor k G where
  app A := ModuleCat.ofHom (inclusion A.ρ S)
  naturality {A B} φ := by
    apply ModuleCat.hom_ext
    exact (inclusion_natural (S := S) φ.hom).symm

def transferNatTrans : Rep.coinvariantsFunctor k G ⟶
    subgroupCoinvariantsFunctor (k := k) S where
  app A := ModuleCat.ofHom (normTransfer A.ρ S)
  naturality {A B} φ := by
    apply ModuleCat.hom_ext
    exact (normTransfer_natural (S := S) φ.hom).symm

theorem transfer_inclusion (hindex : (Fintype.card (G ⧸ S) : k) = 1) :
    transferNatTrans (k := k) S ≫ inclusionNatTrans S = 𝟙 _ := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  change inclusion A.ρ S ∘ₗ normTransfer A.ρ S = LinearMap.id
  simpa only [hindex, one_smul] using inclusion_normTransfer A.ρ S

abbrev subgroupChains (C : ChainComplex (Rep k G) ℕ) : ChainComplex (ModuleCat k) ℕ :=
  ((subgroupCoinvariantsFunctor (k := k) S).mapHomologicalComplex _).obj C

abbrev ambientChains (C : ChainComplex (Rep k G) ℕ) : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj C

def chainInclusion (C : ChainComplex (Rep k G) ℕ) :
    subgroupChains S C ⟶ ambientChains C :=
  ((inclusionNatTrans (k := k) S).mapHomologicalComplex _).app C

def chainTransfer (C : ChainComplex (Rep k G) ℕ) :
    ambientChains C ⟶ subgroupChains S C :=
  ((transferNatTrans (k := k) S).mapHomologicalComplex _).app C

theorem chainTransfer_inclusion (C : ChainComplex (Rep k G) ℕ)
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) :
    chainTransfer S C ≫ chainInclusion S C = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  change inclusion (C.X n).ρ S ∘ₗ normTransfer (C.X n).ρ S = LinearMap.id
  simpa only [hindex, one_smul] using inclusion_normTransfer (C.X n).ρ S

theorem homology_chainInclusion_surjective (C : ChainComplex (Rep k G) ℕ)
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap (chainInclusion S C) j) := by
  have hh : HomologicalComplex.homologyMap (chainTransfer S C) j ≫
      HomologicalComplex.homologyMap (chainInclusion S C) j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, chainTransfer_inclusion S C hindex,
      HomologicalComplex.homologyMap_id]
  intro y
  refine ⟨HomologicalComplex.homologyMap (chainTransfer S C) j y, ?_⟩
  exact congrArg (fun f => ModuleCat.Hom.hom f y) hh

end CoboundaryExpanders.Transfer

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp

namespace CoboundaryExpanders.BarComparison
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  (S : Subgroup G)

abbrev restrictedBar : ProjectiveResolution (Rep.trivial k S k) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G)

def inclusionF (n : ℕ) :
    (Rep.barComplex k S).X n ⟶
      (Rep.resFunctor S.subtype).obj ((Rep.barComplex k G).X n) :=
  Rep.freeLift k S _ (fun x : Fin n → S =>
    Finsupp.single (fun i => (x i : G)) (.single (1 : G) (1 : k)))

omit [DecidableEq G] in
@[simp] theorem inclusionF_single (n : ℕ) (x : Fin n → S) (h : S) (r : k) :
    (inclusionF (k := k) S n).hom (Finsupp.single x (.single h r)) =
      Finsupp.single (fun i => (x i : G)) (.single (h : G) r) := by
  change (Representation.freeLift
    ((Representation.free k G (Fin n → G)).comp S.subtype)
    (fun x : Fin n → S => Finsupp.single (fun i => (x i : G)) (.single (1 : G) (1 : k))))
    (Finsupp.single x (.single h r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free k G (Fin n → G) (h : G) _ = _
  rw [Representation.free_single_single]
  simp

def inclusion : (Rep.barComplex k S) ⟶ (restrictedBar (k := k) S).complex where
  f n := inclusionF S n
  comm' i j hij := by
    cases hij
    apply Rep.free_ext
    intro x
    change ((Rep.barComplex k G).d (j + 1) j).hom
      ((inclusionF (k := k) S (j + 1)).hom (Finsupp.single x (.single 1 1))) =
      (inclusionF (k := k) S j).hom
      (((Rep.barComplex k S).d (j + 1) j).hom (Finsupp.single x (.single 1 1)))
    have hdG : (Rep.barComplex k G).d (j + 1) j = Rep.barComplex.d k G j :=
      Rep.barComplex.d_def k G (n := j)
    have hdS : (Rep.barComplex k S).d (j + 1) j = Rep.barComplex.d k S j :=
      Rep.barComplex.d_def k S (n := j)
    have hincl : ∀ (n : ℕ) (x : Fin n → S) (h : S) (r : k),
        (inclusionF (k := k) S n).hom (Finsupp.single x (.single h r)) =
          Finsupp.single (fun i => (x i : G)) (.single (h : G) r) :=
      inclusionF_single S
    rw [hdG, hdS, hincl]
    simp only [Subgroup.coe_one]
    rw [Rep.barComplex.d_single, Rep.barComplex.d_single]
    simp only [map_add, map_sum, hincl]

    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    exact (Fin.comp_contractNth (· * ·) (· * ·) (fun a b : S => rfl) i x).symm

open Rep TensorProduct

omit [DecidableEq G] in
lemma diagonal_inv_single (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G n).inv.hom (single x (.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (single x (.single g r)) = .single g 1 ⊗ₜ[k] .single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step1]
  simp only [Action.tensorObj_V, tensor_V, tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, x) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by
      rw [one_mul]
      exact congrArg (fun f : Fin (n + 1) → G => MonoidAlgebra.single f r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x))

omit [DecidableEq G] in
@[simp] theorem bar_augmentation_single (x : Fin 0 → G) (g : G) (r : k) :
    ((Rep.barResolution k G).π.f 0).hom (single x (.single g r)) = r := by
  change (Rep.standardComplex.ε k G).hom
    ((Rep.diagonalSuccIsoFree k G 0).inv.hom (single x (.single g r))) = r
  rw [diagonal_inv_single]
  simp [Rep.standardComplex.ε]

omit [DecidableEq G] in
theorem inclusion_augmentation :
    inclusion (k := k) S ≫ (restrictedBar S).π = (Rep.barResolution k S).π := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution k G).π.f 0).hom
      ((inclusionF (k := k) S 0).hom (single x (.single 1 1))) =
      ((Rep.barResolution k S).π.f 0).hom (single x (.single 1 1))
    rw [inclusionF_single, bar_augmentation_single, bar_augmentation_single]
  | succ n =>
    apply Limits.IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_single_obj_X (V := Rep k S)
      (ComplexShape.down ℕ) 0 (Rep.trivial k S k) (n + 1) (by omega)

def inclusionHomotopy : Homotopy (inclusion (k := k) S)
    ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).hom :=
  ProjectiveResolution.liftHomotopy (P := Rep.barResolution k S) (Q := restrictedBar S)
    (𝟙 (Rep.trivial k S k)) (inclusion S)
    ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).hom
    (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact inclusion_augmentation (k := k) S)
    (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact ProjectiveResolution.homotopyEquiv_hom_π _ _)

def inclusionEquiv : HomotopyEquiv (Rep.barComplex k S) (restrictedBar (k := k) S).complex where
  hom := inclusion S
  inv := ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).inv
  homotopyHomInvId :=
    ((inclusionHomotopy S).compRight _).trans
      ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).homotopyHomInvId
  homotopyInvHomId :=
    ((inclusionHomotopy S).compLeft _).trans
      ((Rep.barResolution k S).homotopyEquiv (restrictedBar S)).homotopyInvHomId

end CoboundaryExpanders.BarComparison

end

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.CoinvariantModel
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]

abbrev complex : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj (Rep.barComplex k G)

def chainsIso : groupHomology.inhomogeneousChains (Rep.trivial k G k) ≅
    complex (k := k) (G := G) :=
  groupHomology.inhomogeneousChainsIso (Rep.trivial k G k) ≪≫
    (NatIso.mapHomologicalComplex
      (Functor.isoWhiskerRight (leftUnitorNatIso (Rep k G)) (Rep.coinvariantsFunctor k G)) _).app
        (Rep.barComplex k G)

@[simp] theorem chainsIso_hom_single (n : ℕ) (x : Fin n → G) (r : k) :
    (chainsIso (k := k) (G := G)).hom.f n (single x r) =
      Representation.Coinvariants.mk (Representation.free k G (Fin n → G))
        (single x (.single (1 : G) r)) := by
  change (Rep.coinvariantsFunctor k G).map (λ_ (Rep.free k G (Fin n → G))).hom
    (Rep.finsuppToCoinvariantsTensorFree (Rep.trivial k G k) (Fin n → G)
      (single x r)) = _
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  simp

end CoboundaryExpanders.CoinvariantModel

namespace CoboundaryExpanders.Transfer

section
open CategoryTheory Representation Finsupp
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

def barCoinvariantInclusion :
    CoinvariantModel.complex (k := k) (G := S) ⟶ subgroupChains S (Rep.barComplex k G) :=
  ((Rep.coinvariantsFunctor k S).mapHomologicalComplex _).map
    (BarComparison.inclusion (k := k) S)

def trivialInclusion : Rep.trivial k S k ⟶ Rep.res S.subtype (Rep.trivial k G k) :=
  𝟙 (Rep.trivial k S k)

omit [S.Normal] [Fintype (G ⧸ S)] in
theorem chain_factorization :
    CoinvariantModel.chainsIso.hom ≫ barCoinvariantInclusion (k := k) S ≫
      chainInclusion S (Rep.barComplex k G) =
    groupHomology.chainsMap S.subtype (trivialInclusion (k := k) S) ≫
      (CoinvariantModel.chainsIso (k := k) (G := G)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x r
  change inclusion (Representation.free k G (Fin n → G)) S
    (Representation.Coinvariants.map _ _ (BarComparison.inclusionF (k := k) S n).hom
      ((CoinvariantModel.chainsIso (k := k) (G := S)).hom.f n (single x r))) =
    (CoinvariantModel.chainsIso (k := k) (G := G)).hom.f n
      ((groupHomology.chainsMap S.subtype (trivialInclusion (k := k) S)).f n (single x r))
  rw [CoinvariantModel.chainsIso_hom_single, Coinvariants.map_mk,
    BarComparison.inclusionF_single, inclusion_mk,
    groupHomology.chainsMap_f_single, CoinvariantModel.chainsIso_hom_single]
  rfl

theorem homology_surjective_of_homotopyEquiv
    {C D : ChainComplex (ModuleCat k) ℕ} (e : HomotopyEquiv C D) (j : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap e.hom j) := by
  have h : HomologicalComplex.homologyMap e.inv j ≫
      HomologicalComplex.homologyMap e.hom j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp,
      e.homotopyInvHomId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
  intro y
  refine ⟨HomologicalComplex.homologyMap e.inv j y, ?_⟩
  exact congrArg (fun f => ModuleCat.Hom.hom f y) h

omit [DecidableEq G] [S.Normal] [Fintype (G ⧸ S)] in
theorem homology_barCoinvariantInclusion_surjective (j : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap
      (barCoinvariantInclusion (k := k) S) j) :=
  homology_surjective_of_homotopyEquiv
    ((Rep.coinvariantsFunctor k S).mapHomotopyEquiv (BarComparison.inclusionEquiv S)) j

theorem groupHomology_inclusion_surjective
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ) :
    Function.Surjective
      (groupHomology.map S.subtype (trivialInclusion (k := k) S) j) := by
  let eS := CoinvariantModel.chainsIso (k := k) (G := S)
  let eG := CoinvariantModel.chainsIso (k := k) (G := G)
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f j)
    (chain_factorization (k := k) S)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  intro y
  obtain ⟨b, hb⟩ := homology_chainInclusion_surjective S (Rep.barComplex k G) hindex j
    (HomologicalComplex.homologyMap eG.hom j y)
  obtain ⟨c, hc⟩ := homology_barCoinvariantInclusion_surjective (k := k) S j b
  obtain ⟨z, hz⟩ := homology_surjective_of_homotopyEquiv (HomotopyEquiv.ofIso eS) j c
  refine ⟨z, ?_⟩
  have hi : Function.Injective (HomologicalComplex.homologyMap eG.hom j) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hi
  have he := congrArg (fun f => ModuleCat.Hom.hom f z) hf
  change HomologicalComplex.homologyMap (chainInclusion S (Rep.barComplex k G)) j
    (HomologicalComplex.homologyMap (barCoinvariantInclusion (k := k) S) j
      (HomologicalComplex.homologyMap eS.hom j z)) =
    HomologicalComplex.homologyMap eG.hom j
      (groupHomology.map S.subtype (trivialInclusion (k := k) S) j z) at he
  change HomologicalComplex.homologyMap eS.hom j z = c at hz
  rw [hz, hc, hb] at he
  exact he.symm

theorem odd_index_groupHomology_inclusion_surjective
    {G : Type} [Group G] [DecidableEq G] (S : Subgroup G) [S.Normal]
    [Fintype (G ⧸ S)] (hindex : Odd (Fintype.card (G ⧸ S))) (j : ℕ) :
    Function.Surjective
      (groupHomology.map S.subtype (trivialInclusion (k := ZMod 2) S) j) := by
  apply groupHomology_inclusion_surjective
  rcases hindex with ⟨r, hr⟩
  rw [hr]
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [Nat.cast_add, Nat.cast_mul, htwo]

variable {H : Type u} [Group H]

def trivialCoefficients (f : H →* G) :
    Rep.trivial k H k ⟶ Rep.res f (Rep.trivial k G k) :=
  𝟙 (Rep.trivial k H k)

omit [DecidableEq G] in
theorem homology_equiv_surjective (e : H ≃* G) (j : ℕ) :
    Function.Surjective
      (groupHomology.map e.toMonoidHom (trivialCoefficients (k := k) e.toMonoidHom) j) := by
  let E := groupHomology.mapIso (A := Rep.trivial k H k) (B := Rep.trivial k G k)
    e (LinearEquiv.refl k k) (fun _ => rfl) j
  have he : groupHomology.map e.toMonoidHom
      (trivialCoefficients (k := k) e.toMonoidHom) j = E.hom := by
    exact groupHomology.map_congr rfl rfl j
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso E.hom).surjective

theorem nested_subgroup_inclusion_surjective (H K : Subgroup G) (hHK : H ≤ K)
    [(H.subgroupOf K).Normal] [Fintype (K ⧸ H.subgroupOf K)]
    (hindex : (Fintype.card (K ⧸ H.subgroupOf K) : k) = 1) (j : ℕ) :
    Function.Surjective (groupHomology.map (Subgroup.inclusion hHK)
      (trivialCoefficients (k := k) (Subgroup.inclusion hHK)) j) := by
  let e := (Subgroup.subgroupOfEquivOfLe hHK).symm
  have he := homology_equiv_surjective (k := k) e j
  have hi := groupHomology_inclusion_surjective (k := k) (H.subgroupOf K) hindex j
  have hcomp : groupHomology.map (Subgroup.inclusion hHK)
      (trivialCoefficients (k := k) (Subgroup.inclusion hHK)) j =
      groupHomology.map e.toMonoidHom (trivialCoefficients (k := k) e.toMonoidHom) j ≫
      groupHomology.map (H.subgroupOf K).subtype
        (trivialInclusion (k := k) (H.subgroupOf K)) j := by
    rw [← groupHomology.map_comp]
    exact groupHomology.map_congr rfl rfl j
  rw [hcomp]
  exact hi.comp he

end

open Representation
universe u
variable {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

def quotientActionNatTrans (q : G ⧸ S) :
    subgroupCoinvariantsFunctor (k := k) S ⟶ subgroupCoinvariantsFunctor S where
  app A := ModuleCat.ofHom (A.ρ.quotientToCoinvariants S q)
  naturality {A B} φ := by
    apply ModuleCat.hom_ext
    apply Coinvariants.hom_ext
    ext v
    induction q using QuotientGroup.induction_on with
    | H g =>
      change Coinvariants.mk (B.ρ.comp S.subtype) (B.ρ g (φ.hom v)) =
        Coinvariants.mk (B.ρ.comp S.subtype) (φ.hom (A.ρ g v))
      exact congrArg (Coinvariants.mk _) (LinearMap.congr_fun (φ.hom.isIntertwining' g) v).symm

def chainQuotientAction (C : ChainComplex (Rep k G) ℕ) (q : G ⧸ S) :
    subgroupChains S C ⟶ subgroupChains S C :=
  ((quotientActionNatTrans (k := k) S q).mapHomologicalComplex _).app C

theorem normTransfer_inclusion (V : Type*) [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    normTransfer ρ S ∘ₗ inclusion ρ S = ∑ q : G ⧸ S, ρ.quotientToCoinvariants S q := by
  apply Coinvariants.hom_ext
  ext v
  simp [LinearMap.comp_apply, LinearMap.sum_apply]

theorem chainInclusion_transfer (C : ChainComplex (Rep k G) ℕ) :
    chainInclusion S C ≫ chainTransfer S C = ∑ q : G ⧸ S, chainQuotientAction S C q := by
  apply HomologicalComplex.hom_ext
  intro n
  have hsum : (∑ q : G ⧸ S, chainQuotientAction (k := k) S C q).f n =
      ∑ q : G ⧸ S, (chainQuotientAction S C q).f n :=
    map_sum (HomologicalComplex.Hom.fAddMonoidHom n) _ _
  rw [hsum]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  change normTransfer (C.X n).ρ S ∘ₗ inclusion (C.X n).ρ S =
    ∑ q : G ⧸ S, (C.X n).ρ.quotientToCoinvariants S q
  exact normTransfer_inclusion S _ _

theorem homology_chainInclusion_injective (C : ChainComplex (Rep k G) ℕ)
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ)
    (htriv : ∀ q, HomologicalComplex.homologyMap (chainQuotientAction S C q) j = 𝟙 _) :
    Function.Injective (HomologicalComplex.homologyMap (chainInclusion S C) j) := by
  have hh : HomologicalComplex.homologyMap (chainInclusion S C) j ≫
      HomologicalComplex.homologyMap (chainTransfer S C) j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, chainInclusion_transfer]
    change (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) j).map
      (∑ q : G ⧸ S, chainQuotientAction S C q) = _
    rw [Functor.map_sum]
    change (∑ q : G ⧸ S, HomologicalComplex.homologyMap (chainQuotientAction S C q) j) = _
    simp only [htriv, Finset.sum_const, Finset.card_univ]
    ext v
    change (Fintype.card (G ⧸ S)) • v = v
    rw [← Nat.cast_smul_eq_nsmul k, hindex, one_smul]
  intro x y hxy
  have hx := congrArg (fun f => ModuleCat.Hom.hom f x) hh
  have hy := congrArg (fun f => ModuleCat.Hom.hom f y) hh
  exact hx.symm.trans ((congrArg (HomologicalComplex.homologyMap (chainTransfer S C) j) hxy).trans hy)

end CoboundaryExpanders.Transfer

namespace CoboundaryExpanders.BarComparison
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal]

def adjustedF (g : G) (n : ℕ) :
    (Rep.barComplex k S).X n ⟶
      (Rep.resFunctor S.subtype).obj ((Rep.barComplex k G).X n) :=
  Rep.freeLift k S _ (fun x : Fin n → S =>
    Finsupp.single (fun i => g * (x i : G) * g⁻¹) (.single g⁻¹ (1 : k)))

omit [DecidableEq G] [S.Normal] in
@[simp] theorem adjustedF_single (g : G) (n : ℕ) (x : Fin n → S) (h : S) (r : k) :
    (adjustedF (k := k) S g n).hom (Finsupp.single x (.single h r)) =
      Finsupp.single (fun i => g * (x i : G) * g⁻¹) (.single ((h : G) * g⁻¹) r) := by
  change (Representation.freeLift
    ((Representation.free k G (Fin n → G)).comp S.subtype)
    (fun x : Fin n → S => Finsupp.single (fun i => g * (x i : G) * g⁻¹)
      (.single g⁻¹ (1 : k)))) (Finsupp.single x (.single h r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free k G (Fin n → G) (h : G) _ = _
  rw [Representation.free_single_single]
  simp

omit [DecidableEq G] in
theorem bar_d_single_coeff (n : ℕ) (x : Fin (n + 1) → G) (h : G) :
    (Rep.barComplex.d k G n).hom (single x (.single h (1 : k))) =
      single (fun i => x i.succ) (.single (h * x 0) 1) +
      ∑ i : Fin (n + 1), single (i.contractNth (· * ·) x)
        (.single h ((-1 : k) ^ (i.val + 1))) := by
  have hh := Rep.hom_comm_apply (Rep.barComplex.d k G n) h
    (single x (.single 1 (1 : k)))
  change (Rep.barComplex.d k G n).hom
    (Representation.free k G (Fin (n + 1) → G) h (single x (.single 1 1))) =
    Representation.free k G (Fin n → G) h
      ((Rep.barComplex.d k G n).hom (single x (.single 1 1))) at hh
  rw [Representation.free_single_single, mul_one, Rep.barComplex.d_single] at hh
  rw [hh]
  simp [map_add, map_sum]

def adjusted (g : G) : (Rep.barComplex k S) ⟶ (restrictedBar (k := k) S).complex where
  f n := adjustedF S g n
  comm' i j hij := by
    cases hij
    apply Rep.free_ext
    intro x
    change ((Rep.barComplex k G).d (j + 1) j).hom
      ((adjustedF (k := k) S g (j + 1)).hom (Finsupp.single x (.single 1 1))) =
      (adjustedF (k := k) S g j).hom
      (((Rep.barComplex k S).d (j + 1) j).hom (Finsupp.single x (.single 1 1)))
    rw [Rep.barComplex.d_def, Rep.barComplex.d_def, adjustedF_single]
    have hadj : ∀ (n : ℕ) (x : Fin n → S) (h : S) (r : k),
        (adjustedF (k := k) S g n).hom (single x (.single h r)) =
          single (fun i => g * (x i : G) * g⁻¹) (.single ((h : G) * g⁻¹) r) :=
      adjustedF_single S g
    rw [bar_d_single_coeff, Rep.barComplex.d_single]
    simp only [map_add, map_sum, hadj, Subgroup.coe_one, one_mul]
    congr 1
    · simp only [mul_assoc, inv_mul_cancel_left]
    · apply Finset.sum_congr rfl
      intro i _
      congr 2
      exact (Fin.comp_contractNth (· * ·) (· * ·)
        (f := fun a : S => g * (a : G) * g⁻¹)
        (fun a b : S => by simp [mul_assoc]) i x).symm

omit [DecidableEq G] [S.Normal] in
theorem adjusted_augmentation (g : G) :
    adjusted (k := k) S g ≫ (restrictedBar S).π = (Rep.barResolution k S).π := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution k G).π.f 0).hom
      ((adjustedF (k := k) S g 0).hom (single x (.single 1 1))) =
      ((Rep.barResolution k S).π.f 0).hom (single x (.single 1 1))
    rw [adjustedF_single, bar_augmentation_single, bar_augmentation_single]
  | succ n =>
    apply Limits.IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_single_obj_X (V := Rep k S)
      (ComplexShape.down ℕ) 0 (Rep.trivial k S k) (n + 1) (by omega)

def adjustedHomotopy (g : G) :
    Homotopy (adjusted (k := k) S g) (inclusion S) :=
  ProjectiveResolution.liftHomotopy (P := Rep.barResolution k S) (Q := restrictedBar S)
    (𝟙 (Rep.trivial k S k)) (adjusted S g) (inclusion S)
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact adjusted_augmentation S g)
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact inclusion_augmentation S)

end CoboundaryExpanders.BarComparison

namespace CoboundaryExpanders.Transfer
open Representation Finsupp
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

def barCoinvariantAdjusted (g : G) : CoinvariantModel.complex (k := k) (G := S) ⟶
    subgroupChains S (Rep.barComplex k G) :=
  ((Rep.coinvariantsFunctor k S).mapHomologicalComplex _).map
    (BarComparison.adjusted S g)

omit [DecidableEq G] [S.Normal] [Fintype (G ⧸ S)] in
theorem homology_adjusted (g : G) (j : ℕ) :
    HomologicalComplex.homologyMap (barCoinvariantAdjusted (k := k) S g) j =
      HomologicalComplex.homologyMap (barCoinvariantInclusion (k := k) S) j :=
  ((Rep.coinvariantsFunctor k S).mapHomotopy (BarComparison.adjustedHomotopy S g)).homologyMap_eq j

omit [Fintype (G ⧸ S)] in
theorem chain_conjugation_factorization (g : G) :
    (CoinvariantModel.chainsIso (k := k) (G := S)).hom ≫ barCoinvariantAdjusted S g ≫
      chainQuotientAction S (Rep.barComplex k G) (g : G ⧸ S) =
    groupHomology.chainsMap (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) ≫
      (CoinvariantModel.chainsIso (k := k) (G := S)).hom ≫ barCoinvariantInclusion S := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x r
  change (Representation.free k G (Fin n → G)).quotientToCoinvariants S (g : G ⧸ S)
    (Coinvariants.map _ _ (BarComparison.adjustedF (k := k) S g n).hom
      ((CoinvariantModel.chainsIso (k := k) (G := S)).hom.f n (single x r))) =
    Coinvariants.map _ _ (BarComparison.inclusionF (k := k) S n).hom
      ((CoinvariantModel.chainsIso (k := k) (G := S)).hom.f n
        ((groupHomology.chainsMap (MulAut.conjNormal (H := S) g).toMonoidHom
          (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom)).f n (single x r)))
  rw [CoinvariantModel.chainsIso_hom_single, Coinvariants.map_mk,
    BarComparison.adjustedF_single, quotient_action_mk,
    Representation.free_single_single,
    groupHomology.chainsMap_f_single, CoinvariantModel.chainsIso_hom_single,
    Coinvariants.map_mk, BarComparison.inclusionF_single]
  simp only [Subgroup.coe_one, one_mul, mul_inv_cancel]
  rfl

omit [Fintype (G ⧸ S)] in
theorem homology_quotientAction_eq_id (j : ℕ)
    (hconj : ∀ g : G, groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j = 𝟙 _) :
    ∀ q : G ⧸ S, HomologicalComplex.homologyMap
      (chainQuotientAction S (Rep.barComplex k G) q) j = 𝟙 _ := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hf := congrArg (fun f => HomologicalComplex.homologyMap f j)
      (chain_conjugation_factorization (k := k) S g)
    simp only [HomologicalComplex.homologyMap_comp, homology_adjusted] at hf
    change HomologicalComplex.homologyMap CoinvariantModel.chainsIso.hom j ≫
      HomologicalComplex.homologyMap (barCoinvariantInclusion S) j ≫
      HomologicalComplex.homologyMap (chainQuotientAction S (Rep.barComplex k G) (g : G ⧸ S)) j =
      groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
        (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j ≫
      HomologicalComplex.homologyMap CoinvariantModel.chainsIso.hom j ≫
      HomologicalComplex.homologyMap (barCoinvariantInclusion S) j at hf
    rw [hconj, Category.id_comp] at hf
    have hs := (homology_barCoinvariantInclusion_surjective (k := k) S j).comp
      (homology_surjective_of_homotopyEquiv
        (HomotopyEquiv.ofIso (CoinvariantModel.chainsIso (k := k) (G := S))) j)
    ext v
    obtain ⟨x, rfl⟩ := hs v
    exact congrArg (fun f => ModuleCat.Hom.hom f x) hf

theorem homology_injective_of_homotopyEquiv
    {C D : ChainComplex (ModuleCat k) ℕ} (e : HomotopyEquiv C D) (j : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap e.hom j) := by
  have hh : HomologicalComplex.homologyMap e.hom j ≫
      HomologicalComplex.homologyMap e.inv j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp,
      e.homotopyHomInvId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
  intro x y hxy
  have hx := congrArg (fun f => ModuleCat.Hom.hom f x) hh
  have hy := congrArg (fun f => ModuleCat.Hom.hom f y) hh
  exact hx.symm.trans ((congrArg (HomologicalComplex.homologyMap e.inv j) hxy).trans hy)

theorem groupHomology_inclusion_injective
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ)
    (hconj : ∀ g : G, groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j = 𝟙 _) :
    Function.Injective
      (groupHomology.map S.subtype (trivialInclusion (k := k) S) j) := by
  have hi := homology_chainInclusion_injective S (Rep.barComplex k G) hindex j
    (homology_quotientAction_eq_id S j hconj)
  have hb := homology_injective_of_homotopyEquiv
    ((Rep.coinvariantsFunctor k S).mapHomotopyEquiv (BarComparison.inclusionEquiv S)) j
  have hs := homology_injective_of_homotopyEquiv
    (HomotopyEquiv.ofIso (CoinvariantModel.chainsIso (k := k) (G := S))) j
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f j)
    (chain_factorization (k := k) S)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  intro x y hxy
  apply hs
  apply hb
  apply hi
  have hx := congrArg (fun f => ModuleCat.Hom.hom f x) hf
  have hy := congrArg (fun f => ModuleCat.Hom.hom f y) hf
  exact hx.trans ((congrArg
    (HomologicalComplex.homologyMap (CoinvariantModel.chainsIso (k := k) (G := G)).hom j)
    hxy).trans hy.symm)

theorem subgroup_homology_isZero_of_conjugation
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ)
    (hconj : ∀ g : G, groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j = 𝟙 _)
    (hzero : Limits.IsZero (groupHomology (Rep.trivial k G k) j)) :
    Limits.IsZero (groupHomology (Rep.trivial k S k) j) := by
  let f := groupHomology.map S.subtype (trivialInclusion (k := k) S) j
  have : Mono f := (ModuleCat.mono_iff_injective f).mpr
    (groupHomology_inclusion_injective S hindex j hconj)
  exact Limits.IsZero.of_mono f hzero

end CoboundaryExpanders.Transfer

end

end OAI
