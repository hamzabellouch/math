import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.JetRelations
import OAI.RepresentationTheory.RestrictedTilting.WeightBounds

namespace OAI

/-! Plane jet modules, homogeneous layers and equivariant inclusions. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
open scoped TensorProduct BigOperators Pointwise
universe u
variable (k : Type u) [Field k]
variable {M : Type u} [AddCommGroup M] [Module k M]
  [Module (MvPolynomial (Fin 2) k) M] [IsScalarTower k (MvPolynomial (Fin 2) k) M]

noncomputable abbrev planeJetRelation (j : ℕ) : Submodule k M :=
  (jetRelation (M := M) (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) j).restrictScalars k

noncomputable def jetMonomialBasis (j : ℕ) :
    Module.Basis (Fin (j+1)) k (MvPolynomial.homogeneousSubmodule (Fin 2) k j) :=
  (binaryBasis k j).reindex Fin.revPerm

lemma jetMonomialBasis_apply (j : ℕ) (i : Fin (j+1)) :
    (jetMonomialBasis k j i).val =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)^i.val * MvPolynomial.X 1^(j-i.val) := by
  simp only [jetMonomialBasis, Module.Basis.reindex_apply, Fin.revPerm_symm,
    Fin.revPerm_apply, binaryBasis_apply, Fin.val_rev]
  congr 2 <;> omega

lemma homogeneous_smul_mem_jet (j : ℕ)
    (P : MvPolynomial.homogeneousSubmodule (Fin 2) k j) (v : M) :
    P.val • v ∈ planeJetRelation (M := M) k j := by
  have hp := (jetMonomialBasis k j).sum_repr P
  have hv := congrArg (fun Q : MvPolynomial.homogeneousSubmodule (Fin 2) k j => Q.val • v) hp
  have he : P.val • v = binarySum (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) j
      (fun i => (jetMonomialBasis k j).repr P i • v) := by
    rw [← hv, binarySum_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_smul,
      jetMonomialBasis_apply, smul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  exact ⟨_,he.symm⟩

lemma homogeneous_smul_pair_mem_next (j : ℕ)
    (P : MvPolynomial.homogeneousSubmodule (Fin 2) k j) (v : M)
    (hv : v ∈ planeJetRelation (M := M) k 1) : P.val • v ∈ planeJetRelation (M := M) k (j+1) := by
  have hp := (jetMonomialBasis k j).sum_repr P
  have he : P.val • v = binarySum (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) j
      (fun i => (jetMonomialBasis k j).repr P i • v) := by
    rw [← congrArg (fun Q : MvPolynomial.homogeneousSubmodule (Fin 2) k j => Q.val • v) hp,
      binarySum_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_smul,
      jetMonomialBasis_apply, smul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  rw [he]
  apply binarySum_pairRelation
  intro i
  change _ ∈ (jetRelation (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) 1).restrictScalars k at hv
  have : (jetMonomialBasis k j).repr P i • v ∈ planeJetRelation (M := M) k 1 :=
    (planeJetRelation (M := M) k 1).smul_mem _ hv
  simpa only [planeJetRelation, Submodule.restrictScalars_mem, jetRelation_one] using this

 
def PlaneCompatible (σ : Representation k (SL2 k) M) : Prop :=
  ∀ (g : SL2 k) (P : MvPolynomial (Fin 2) k) (v : M),
    σ g (P • v) = linearChange (dualMatrix k g) P • σ g v

lemma planeJetRelation_stable (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) (g : SL2 k) :
    planeJetRelation (M := M) k j ≤ (planeJetRelation (M := M) k j).comap (σ g) := by
  rintro m ⟨v,rfl⟩
  change σ g (binarySum (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) j v) ∈ planeJetRelation (M := M) k j
  rw [binarySum_apply, map_sum]
  apply (planeJetRelation (M := M) k j).sum_mem
  intro i _
  rw [hσ]
  have hh : ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k)^i.val *
      MvPolynomial.X 1^(j-i.val)).IsHomogeneous j := by
    rw [← jetMonomialBasis_apply k j i]
    exact (jetMonomialBasis k j i).property
  exact homogeneous_smul_mem_jet k j
    ⟨_, linearChange_homogeneous (dualMatrix k g) hh⟩ _

noncomputable def planeJetRep (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) :
    Representation k (SL2 k) (M ⧸ planeJetRelation (M := M) k j) :=
  Representation.quotient σ (planeJetRelation (M := M) k j) (planeJetRelation_stable k σ hσ j)

lemma planeJetRep_mk (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) (g : SL2 k) (v : M) :
    planeJetRep k σ hσ j g ((planeJetRelation (M := M) k j).mkQ v) =
      (planeJetRelation (M := M) k j).mkQ (σ g v) := rfl

lemma planeJetRep_rational (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (hr : IsRational k σ) (j : ℕ) :
    IsRational k (planeJetRep k σ hσ j) := by
  intro v l
  obtain ⟨w, rfl⟩ := (planeJetRelation (M := M) k j).mkQ_surjective v
  obtain ⟨P,hP⟩ := hr w (l.comp (planeJetRelation (M := M) k j).mkQ)
  exact ⟨P,hP⟩

noncomputable abbrev planeJetLayerRelation (j : ℕ) : Submodule k (planeJetRelation (M := M) k j) :=
  (planeJetRelation (M := M) k (j+1)).comap (planeJetRelation (M := M) k j).subtype
noncomputable abbrev planeJetLayer (j : ℕ) := (planeJetRelation (M := M) k j) ⧸ planeJetLayerRelation (M := M) k j

noncomputable def planeHomogeneousMultiply (j : ℕ)
    (P : MvPolynomial.homogeneousSubmodule (Fin 2) k j) : M →ₗ[k] planeJetRelation (M := M) k j where
  toFun v := ⟨P.val • v, homogeneous_smul_mem_jet k j P v⟩
  map_add' _ _ := Subtype.ext (smul_add _ _ _)
  map_smul' _ _ := Subtype.ext (smul_comm _ _ _)

noncomputable def planeLayerMul (j : ℕ) (P : MvPolynomial.homogeneousSubmodule (Fin 2) k j) :
    M →ₗ[k] planeJetLayer (M := M) k j :=
  (planeJetLayerRelation (M := M) k j).mkQ.comp (planeHomogeneousMultiply k j P)

lemma planeLayerMul_ker (j : ℕ) (P : MvPolynomial.homogeneousSubmodule (Fin 2) k j) :
    planeJetRelation (M := M) k 1 ≤ (planeLayerMul k j P).ker := by
  intro v hv
  exact (Submodule.Quotient.mk_eq_zero _).mpr (homogeneous_smul_pair_mem_next k j P v hv)

noncomputable def planeLayerBilinear (j : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 2) k j) →ₗ[k]
      ((M ⧸ planeJetRelation (M := M) k 1) →ₗ[k] planeJetLayer (M := M) k j) where
  toFun P := (planeJetRelation (M := M) k 1).liftQ (planeLayerMul k j P) (planeLayerMul_ker k j P)
  map_add' P Q := by
    apply LinearMap.ext
    intro t
    obtain ⟨v,rfl⟩ := (planeJetRelation (M := M) k 1).mkQ_surjective t
    change (planeJetLayerRelation (M := M) k j).mkQ _ =
      (planeJetLayerRelation (M := M) k j).mkQ _ + (planeJetLayerRelation (M := M) k j).mkQ _
    rw [← map_add]
    congr 1
    exact Subtype.ext (add_smul P.val Q.val v)
  map_smul' a P := by
    apply LinearMap.ext
    intro t
    obtain ⟨v,rfl⟩ := (planeJetRelation (M := M) k 1).mkQ_surjective t
    change (planeJetLayerRelation (M := M) k j).mkQ _ = a • (planeJetLayerRelation (M := M) k j).mkQ _
    rw [← map_smul]
    congr 1
    exact Subtype.ext (smul_assoc a P.val v)

noncomputable def planeLayerMultiply (j : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 2) k j) ⊗[k]
      (M ⧸ planeJetRelation (M := M) k 1) →ₗ[k] planeJetLayer (M := M) k j :=
  TensorProduct.lift (planeLayerBilinear k j)

lemma planeLayerMultiply_tmul_mk (j : ℕ)
    (P : MvPolynomial.homogeneousSubmodule (Fin 2) k j) (v : M) :
    planeLayerMultiply k j (P ⊗ₜ[k] (planeJetRelation (M := M) k 1).mkQ v) =
      (planeJetLayerRelation (M := M) k j).mkQ ⟨P.val • v, homogeneous_smul_mem_jet k j P v⟩ := rfl

lemma planeLayerMultiply_sum (j : ℕ) (v : Fin (j+1) → M) :
    planeLayerMultiply k j (∑ i, jetMonomialBasis k j i ⊗ₜ[k] (planeJetRelation (M := M) k 1).mkQ (v i)) =
      (planeJetLayerRelation (M := M) k j).mkQ
        ⟨binarySum (MvPolynomial.X 0) (MvPolynomial.X 1) j v, ⟨v,rfl⟩⟩ := by
  rw [map_sum]
  simp only [planeLayerMultiply_tmul_mk, ← map_sum]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_sum, jetMonomialBasis_apply, binarySum_apply]

lemma tensor_basis_decomposition {H T : Type u} [AddCommGroup H] [Module k H]
    [AddCommGroup T] [Module k T] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k H) (z : H ⊗[k] T) :
    ∃ v : ι → T, z = ∑ i, b i ⊗ₜ[k] v i := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul h t =>
    refine ⟨fun i => b.repr h i • t, ?_⟩
    conv_lhs => rw [← b.sum_repr h, TensorProduct.sum_tmul]
    apply Finset.sum_congr rfl
    intro i _
    rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add z w hz hw =>
    obtain ⟨v,rfl⟩ := hz
    obtain ⟨w,rfl⟩ := hw
    exact ⟨v+w, by simp only [Pi.add_apply, TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

lemma planeLayerMultiply_surjective (j : ℕ) :
    Function.Surjective (planeLayerMultiply (M := M) k j) := by
  intro z
  obtain ⟨⟨m,v,rfl⟩,rfl⟩ := (planeJetLayerRelation (M := M) k j).mkQ_surjective z
  exact ⟨_, planeLayerMultiply_sum k j v⟩

lemma planeLayerMultiply_injective
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • m))
    (hy : ∀ v n : M, (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n →
      ∃ w : M, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w) (j : ℕ) :
    Function.Injective (planeLayerMultiply (M := M) k j) := by
  have hzero : ∀ z, planeLayerMultiply (M := M) k j z = 0 → z = 0 := by
    intro z hz
    obtain ⟨v,rfl⟩ := tensor_basis_decomposition k (jetMonomialBasis k j) z
    choose w hw using fun i => (planeJetRelation (M := M) k 1).mkQ_surjective (v i)
    have he : v = fun i => (planeJetRelation (M := M) k 1).mkQ (w i) := funext fun i => (hw i).symm
    rw [he, planeLayerMultiply_sum] at hz
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
    have hc := (binarySum_mem_next_iff (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)
      (MvPolynomial.X 1) hx hy j w).mp hm
    have hv : ∀ i, v i = 0 := by
      intro i
      rw [← hw i]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      simpa only [planeJetRelation, Submodule.restrictScalars_mem, jetRelation_one] using hc i
    simp only [hv, TensorProduct.tmul_zero, Finset.sum_const_zero]
  intro a b hab
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub,hab,sub_self]

noncomputable def planeLayerEquiv
    (hx : Function.Injective (fun m : M => (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • m))
    (hy : ∀ v n : M, (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) • v =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • n →
      ∃ w : M, v = (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) • w) (j : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 2) k j) ⊗[k]
      (M ⧸ planeJetRelation (M := M) k 1) ≃ₗ[k] planeJetLayer (M := M) k j :=
  LinearEquiv.ofBijective (planeLayerMultiply k j)
    ⟨planeLayerMultiply_injective k hx hy j, planeLayerMultiply_surjective k j⟩

noncomputable def planeJetSubrep (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) :
    Representation k (SL2 k) (planeJetRelation (M := M) k j) :=
  Representation.subrepresentation σ _ (planeJetRelation_stable k σ hσ j)

lemma planeJetLayerRelation_stable (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) (g : SL2 k) :
    planeJetLayerRelation (M := M) k j ≤
      (planeJetLayerRelation k j).comap (planeJetSubrep k σ hσ j g) := by
  intro v hv
  exact planeJetRelation_stable k σ hσ (j+1) g hv

noncomputable def planeJetLayerRep (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) :
    Representation k (SL2 k) (planeJetLayer (M := M) k j) :=
  Representation.quotient (planeJetSubrep k σ hσ j) _
    (planeJetLayerRelation_stable k σ hσ j)

lemma planeLayerMultiply_intertwines (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) (g : SL2 k)
    (z : (MvPolynomial.homogeneousSubmodule (Fin 2) k j) ⊗[k]
      (M ⧸ planeJetRelation (M := M) k 1)) :
    planeLayerMultiply (M := M) k j
      (Representation.tprod ((homogeneousRepresentation j).comp (dualMatrix k))
        (planeJetRep k σ hσ 1) g z) =
      planeJetLayerRep k σ hσ j g (planeLayerMultiply k j z) := by
  induction z using TensorProduct.inductionOn with
  | tmul P v =>
    obtain ⟨w,rfl⟩ := (planeJetRelation (M := M) k 1).mkQ_surjective v
    simp only [Representation.tprod_apply, TensorProduct.map_tmul,
      planeJetRep_mk, planeLayerMultiply_tmul_mk]
    change (planeJetLayerRelation k j).mkQ ⟨_,_⟩ =
      (planeJetLayerRelation k j).mkQ ⟨σ g (P.val • w),_⟩
    congr 1
    apply Subtype.ext
    exact (hσ g P.val w).symm
  | add x y hx hy => simp only [map_add, hx, hy]

lemma planeLayer_finite [Module.Finite k (M ⧸ planeJetRelation (M := M) k 1)] (j : ℕ) :
    Module.Finite k (planeJetLayer (M := M) k j) :=
  Module.Finite.of_surjective (planeLayerMultiply k j) (planeLayerMultiply_surjective k j)

lemma planeJetRelation_succ_le (j : ℕ) :
    planeJetRelation (M := M) k (j+1) ≤ planeJetRelation (M := M) k j :=
  jetRelation_succ_le (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) (MvPolynomial.X 1) j

lemma planeJetRelation_zero : planeJetRelation (M := M) k 0 = ⊤ := by
  simp only [planeJetRelation, jetRelation_zero, Submodule.restrictScalars_top]

noncomputable def planeJetTransition (j : ℕ) :
    (M ⧸ planeJetRelation (M := M) k (j+1)) →ₗ[k] (M ⧸ planeJetRelation (M := M) k j) :=
  (planeJetRelation k (j+1)).mapQ (planeJetRelation k j) LinearMap.id
    (planeJetRelation_succ_le k j)

lemma planeJetTransition_mk (j : ℕ) (v : M) :
    planeJetTransition k j ((planeJetRelation (M := M) k (j+1)).mkQ v) =
      (planeJetRelation (M := M) k j).mkQ v := rfl

lemma planeJetTransition_surjective (j : ℕ) :
    Function.Surjective (planeJetTransition (M := M) k j) := by
  intro v
  obtain ⟨w,rfl⟩ := (planeJetRelation (M := M) k j).mkQ_surjective v
  exact ⟨(planeJetRelation k (j+1)).mkQ w,rfl⟩

noncomputable def planeJetLayerInclusion (j : ℕ) :
    planeJetLayer (M := M) k j →ₗ[k] (M ⧸ planeJetRelation (M := M) k (j+1)) :=
  (planeJetLayerRelation k j).liftQ
    ((planeJetRelation k (j+1)).mkQ.comp (planeJetRelation k j).subtype) (by
      intro v hv
      exact (Submodule.Quotient.mk_eq_zero _).mpr hv)

lemma planeJetLayerInclusion_mk (j : ℕ) (v : planeJetRelation (M := M) k j) :
    planeJetLayerInclusion k j ((planeJetLayerRelation k j).mkQ v) =
      (planeJetRelation (M := M) k (j+1)).mkQ v.val := rfl

lemma planeJetLayerInclusion_injective (j : ℕ) :
    Function.Injective (planeJetLayerInclusion (M := M) k j) := by
  apply (LinearMap.ker_eq_bot (f := planeJetLayerInclusion (M := M) k j)).mp
  apply (LinearMap.ker_eq_bot' (f := planeJetLayerInclusion (M := M) k j)).mpr
  intro v hv
  obtain ⟨w,rfl⟩ := (planeJetLayerRelation (M := M) k j).mkQ_surjective v
  rw [planeJetLayerInclusion_mk] at hv
  have hw : w.val ∈ planeJetRelation (M := M) k (j+1) :=
    (Submodule.Quotient.mk_eq_zero (planeJetRelation k (j+1))).mp hv
  exact (Submodule.Quotient.mk_eq_zero _).mpr hw

lemma planeJet_shortExact (j : ℕ) :
    Function.Exact (planeJetLayerInclusion (M := M) k j) (planeJetTransition k j) := by
  intro v
  obtain ⟨w,rfl⟩ := (planeJetRelation (M := M) k (j+1)).mkQ_surjective v
  constructor
  · intro hw
    have hj : w ∈ planeJetRelation (M := M) k j := (Submodule.Quotient.mk_eq_zero _).mp hw
    exact ⟨(planeJetLayerRelation k j).mkQ ⟨w,hj⟩,rfl⟩
  · rintro ⟨z,hz⟩
    obtain ⟨t,rfl⟩ := (planeJetLayerRelation (M := M) k j).mkQ_surjective z
    rw [← hz, planeJetLayerInclusion_mk, planeJetTransition_mk]
    exact (Submodule.Quotient.mk_eq_zero _).mpr t.property

lemma planeJet_finite [Module.Finite k (M ⧸ planeJetRelation (M := M) k 1)] (j : ℕ) :
    Module.Finite k (M ⧸ planeJetRelation (M := M) k j) := by
  induction j with
  | zero =>
    rw [planeJetRelation_zero]
    infer_instance
  | succ j ih =>
    let := ih
    let := planeLayer_finite (M := M) k j
    exact Module.Finite.of_exact (planeJet_shortExact k j) (planeJetTransition_surjective k j)

lemma planeJetTransition_intertwines (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) (g : SL2 k)
    (v : M ⧸ planeJetRelation (M := M) k (j+1)) :
    planeJetTransition k j (planeJetRep k σ hσ (j+1) g v) =
      planeJetRep k σ hσ j g (planeJetTransition k j v) := by
  obtain ⟨w,rfl⟩ := (planeJetRelation (M := M) k (j+1)).mkQ_surjective v
  rfl

lemma planeJetLayerInclusion_intertwines (σ : Representation k (SL2 k) M)
    (hσ : PlaneCompatible k σ) (j : ℕ) (g : SL2 k)
    (v : planeJetLayer (M := M) k j) :
    planeJetLayerInclusion k j (planeJetLayerRep k σ hσ j g v) =
      planeJetRep k σ hσ (j+1) g (planeJetLayerInclusion k j v) := by
  obtain ⟨w,rfl⟩ := (planeJetLayerRelation (M := M) k j).mkQ_surjective v
  rfl
end FiberFunctorProof
end

end OAI
