import Mathlib
import OAI.Probability.ThorpRouting.Casimir.BlockProduct

namespace OAI

namespace ThorpNine.Casimir

namespace Thorp
open scoped BigOperators Classical

def pairAssembleEquiv (B C H : Type*) :
    ((H × (B → C × C)) × H) ≃ (((B → C) × H) × ((B → C) × H)) where
  toFun w := (((fun b => (w.1.2 b).1),w.1.1),((fun b => (w.1.2 b).2),w.2))
  invFun w := ((w.1.2,fun b => (w.1.1 b,w.2.1 b)),w.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

def palindromeStageEquiv (r L : ℕ) :
    ((OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) ≃ BenesCoins (L+r) :=
  (pairAssembleEquiv _ _ _).trans
    (Equiv.prodCongr (parallelSplitCoinEquiv r L) (parallelSplitCoinEquiv r L))

lemma palindromeStageEquiv_apply (r L : ℕ)
    (w : (OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) :
    palindromeStageEquiv r L w=
      (assembleBits r L (fun x => (w.1.2 x.1).1 x.2) w.1.1,
       assembleBits r L (fun x => (w.1.2 x.1).2 x.2) w.2) := by
  simp only [palindromeStageEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,pairAssembleEquiv,
    Equiv.coe_fn_mk,Prod.map_apply,parallelSplitCoinEquiv_apply]

def modifiedAssembleEquiv (B C H U : Type*) :
    ((H × (B → U × (C × C))) × H) ≃ (B → U) × (((B → C) × H) × ((B → C) × H)) where
  toFun w := ((fun b => (w.1.2 b).1),
    (((fun b => (w.1.2 b).2.1),w.1.1),((fun b => (w.1.2 b).2.2),w.2)))
  invFun w := ((w.2.1.2,fun b => (w.1 b,(w.2.1.1 b,w.2.2.1 b))),w.2.2.2)
  left_inv _w := rfl
  right_inv _w := rfl

def modifiedStageEquiv (r L : ℕ) :
    ((OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) ≃
      ModifiedCoins L r :=
  (modifiedAssembleEquiv _ _ _ _).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (parallelSplitCoinEquiv r L) (parallelSplitCoinEquiv r L)))

lemma modifiedStageEquiv_apply (r L : ℕ)
    (w : (OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) :
    modifiedStageEquiv r L w=
      ((fun b => (w.1.2 b).1),
       (assembleBits r L (fun x => (w.1.2 x.1).2.1 x.2) w.1.1,
        assembleBits r L (fun x => (w.1.2 x.1).2.2 x.2) w.2)) := by
  simp only [modifiedStageEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,modifiedAssembleEquiv,
    Equiv.coe_fn_mk,Prod.map_apply,Equiv.refl_apply,parallelSplitCoinEquiv_apply]

lemma palindrome_stage (r L : ℕ)
    (w : (OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) :
    splitPerm r L (palindromePerm (L+r) (palindromeStageEquiv r L w))=
      outerPerm r L w.1.1*ParallelBlocks.lift (fun b => palindromePerm L (w.1.2 b))*
        (outerPerm r L w.2)⁻¹ := by
  rw [palindromeStageEquiv_apply]
  change splitPerm r L (_*_⁻¹)=_
  rw [map_mul,map_inv,splitPerm_butterfly,splitPerm_butterfly,mul_inv_rev]
  rw [mul_assoc,←mul_assoc (ParallelBlocks.lift _),←map_inv,←map_mul,←mul_assoc]
  rfl

noncomputable def localModifiedPerm (L : ℕ) (e : Bool)
    (w : Equiv.Perm (Card L) × BenesCoins L) : Equiv.Perm (Card L) :=
  if e then 1 else butterflyPerm L (decodeButterfly L w.2.1)*w.1⁻¹

lemma modified_stage (r L : ℕ) (E : Finset (Card r))
    (w : (OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) :
    splitPerm r L (modifiedPerm L r E (modifiedStageEquiv r L w))=
      outerPerm r L w.1.1*ParallelBlocks.lift (fun b => localModifiedPerm L (decide (b∈E)) (w.1.2 b))*
        (outerPerm r L w.2)⁻¹ := by
  rw [modifiedStageEquiv_apply]
  unfold modifiedPerm modifiedInputTree
  rw [map_mul,map_inv,splitPerm_butterfly,splitPerm_boundaryTree,mul_inv_rev]
  rw [mul_assoc,←mul_assoc (ParallelBlocks.lift _),←map_inv,←map_mul,←mul_assoc]
  congr 2
  apply congrArg ParallelBlocks.lift
  funext b
  simp only [Pi.mul_apply,Pi.inv_apply,modifiedBoundary,boundaryOutput_split,localModifiedPerm]
  by_cases h : b∈E <;> simp [h]

end Thorp
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
variable {G : Type*} [Group G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_sandwich (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (P : Ω → G) (Q : Ξ → G) :
    sampleOperator ρ (fun w : (Ω × Ξ) × Ω => P w.1.1*Q w.1.2*(P w.2)⁻¹)=
      sampleOperator ρ P*sampleOperator ρ Q*(sampleOperator ρ P).adjoint := by
  rw [sampleOperator_prod ρ (fun w : Ω × Ξ => P w.1*Q w.2) (fun w : Ω => (P w)⁻¹),
    sampleOperator_prod ρ P Q,sampleOperator_inv ρ hρ]

lemma localModified_average (L : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card L)) V) (e : Bool) :
    sampleOperator ρ (localModifiedPerm L e)=if e then 1 else uniformOperator ρ := by
  cases e
  · simp only [Bool.false_eq_true,ite_false]
    rw [←sampleOperator_equiv ρ _ (Equiv.prodComm _ _)]
    exact sampleOperator_uniform_mul ρ (fun w : BenesCoins L => butterflyPerm L (decodeButterfly L w.1))
  · simp only [ite_true]
    exact sampleOperator_one ρ

end Thorp.UnitaryFinite

namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma sampleOperator_palindrome_stage (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) :
    sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (palindromePerm (L+r))=
      sampleOperator ρ (outerPerm r L)*
        sampleOperator ρ (fun w : Card r → BenesCoins L => ParallelBlocks.lift (fun b => palindromePerm L (w b)))*
          (sampleOperator ρ (outerPerm r L)).adjoint := by
  have he : ((splitPerm r L).toMonoidHom ∘ palindromePerm (L+r)) ∘ palindromeStageEquiv r L=
      fun w => outerPerm r L w.1.1*ParallelBlocks.lift (fun b => palindromePerm L (w.1.2 b))*
        (outerPerm r L w.2)⁻¹ := funext (palindrome_stage r L)
  calc
    _ = sampleOperator ρ (((splitPerm r L).toMonoidHom ∘ palindromePerm (L+r)) ∘ palindromeStageEquiv r L) :=
      (sampleOperator_equiv ρ ((splitPerm r L).toMonoidHom ∘ palindromePerm (L+r)) (palindromeStageEquiv r L)).symm
    _ = _ := (congrArg (sampleOperator ρ) he).trans
      (sampleOperator_sandwich ρ hρ (outerPerm r L)
        (fun w : Card r → BenesCoins L => ParallelBlocks.lift (fun b => palindromePerm L (w b))))

lemma sampleOperator_modified_stage (r L : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) :
    sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (modifiedPerm L r E)=
      sampleOperator ρ (outerPerm r L)*
        sampleOperator ρ (fun w : Card r → Equiv.Perm (Card L) × BenesCoins L =>
          ParallelBlocks.lift (fun b => localModifiedPerm L (decide (b∈E)) (w b)))*
          (sampleOperator ρ (outerPerm r L)).adjoint := by
  have he : ((splitPerm r L).toMonoidHom ∘ modifiedPerm L r E) ∘ modifiedStageEquiv r L=
      fun w => outerPerm r L w.1.1*ParallelBlocks.lift
        (fun b => localModifiedPerm L (decide (b∈E)) (w.1.2 b))*(outerPerm r L w.2)⁻¹ :=
    funext (modified_stage r L E)
  calc
    _ = sampleOperator ρ (((splitPerm r L).toMonoidHom ∘ modifiedPerm L r E) ∘ modifiedStageEquiv r L) :=
      (sampleOperator_equiv ρ ((splitPerm r L).toMonoidHom ∘ modifiedPerm L r E) (modifiedStageEquiv r L)).symm
    _ = _ := (congrArg (sampleOperator ρ) he).trans
      (sampleOperator_sandwich ρ hρ (outerPerm r L)
        (fun w : Card r → Equiv.Perm (Card L) × BenesCoins L =>
          ParallelBlocks.lift (fun b => localModifiedPerm L (decide (b∈E)) (w b))))

end Thorp
namespace Thorp.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def retain (P : ι → V →L[ℂ] V) (E : Finset ι) (i : ι) : V →L[ℂ] V :=
  if i∈E then 1 else P i

omit [CompleteSpace V] [Fintype ι] in
lemma retain_commute (P : ι → V →L[ℂ] V) (hP : ∀ i j, Commute (P i) (P j))
    (E : Finset ι) (i j : ι) : Commute (retain P E i) (retain P E j) := by
  unfold retain
  split_ifs <;> first | exact Commute.one_left _ | exact Commute.one_right _ | exact hP _ _

omit [CompleteSpace V] in
lemma blocks_retain (P : ι → V →L[ℂ] V) (hP : ∀ i j, Commute (P i) (P j)) (E : Finset ι) :
    blocks (retain P E) (retain_commute P hP E)=coarse P hP E := by
  have hs : E∪Eᶜ=(Finset.univ : Finset ι) := Finset.union_compl E
  have hh := Finset.noncommProd_union_of_disjoint (s := E) (t := Eᶜ) disjoint_compl_right
    (retain P E) (fun _ _ _ _ _ => retain_commute P hP E _ _)
  simp only [hs] at hh
  change blocks (retain P E) (retain_commute P hP E)=_ at hh
  rw [hh]
  have he : E.noncommProd (retain P E) (fun _ _ _ _ _ => retain_commute P hP E _ _)=1 := by
    exact (Finset.noncommProd_eq_pow_card E (retain P E)
      (fun i _ j _ _ => retain_commute P hP E i j) 1 (by intro i hi; exact ite_eq_left hi)).trans (one_pow _)
  rw [he,one_mul]
  apply Finset.noncommProd_congr rfl
  intro i hi
  exact ite_eq_right (Finset.mem_compl.mp hi)

end Thorp.CommutingBlocks

namespace Thorp.ParallelBlocks
open scoped BigOperators Classical
open UnitaryFinite
variable {B X : Type*} [Fintype B] [Fintype X] [DecidableEq X]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def centralProjection (ρ : Representation ℂ (Equiv.Perm (B × X)) V) (b : B) : V →L[ℂ] V :=
  uniformOperator (ρ.comp (injection b))

omit [Fintype B] in
lemma centralProjection_commute (ρ : Representation ℂ (Equiv.Perm (B × X)) V) (b c : B) :
    Commute (centralProjection ρ b) (centralProjection ρ c) := by
  simpa only [centralProjection,sampleOperator_uniform] using
    local_average_commute ρ (fun _ => id : B → Equiv.Perm X → Equiv.Perm X) b c

omit [Fintype B] in
lemma local_central_commute {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (ρ : Representation ℂ (Equiv.Perm (B × X)) V) (P : B → Ω → Equiv.Perm X) (b c : B) :
    Commute (sampleOperator (ρ.comp (injection b)) (P b)) (centralProjection ρ c) := by
  by_cases h : b=c
  · subst c
    change _*uniformOperator _=uniformOperator _*_
    rw [sampleOperator_uniform_absorb,sampleOperator_weighted,weighted_uniform_right,sampleLaw_sum,one_smul]
  · unfold centralProjection
    rw [←sampleOperator_uniform,sampleOperator_comp,sampleOperator_comp]
    exact sampleOperator_commute ρ _ _ (fun _ _ => injection_commute h _ _)

end Thorp.ParallelBlocks
namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite ParallelBlocks CommutingBlocks
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma modified_central_average (r L : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) :
    sampleOperator ρ (fun w : Card r → Equiv.Perm (Card L) × BenesCoins L =>
      lift (fun b => localModifiedPerm L (decide (b∈E)) (w b)))=
      coarse (centralProjection ρ) (centralProjection_commute ρ) E := by
  rw [sampleOperator_parallel ρ (fun b => localModifiedPerm L (decide (b∈E))),←blocks_retain]
  apply Finset.noncommProd_congr rfl
  · intro b _
    rw [localModified_average]
    simp only [retain,centralProjection,decide_eq_true_eq]
  · intro b _ c _ _
    exact local_average_commute ρ (fun b => localModifiedPerm L (decide (b∈E))) b c

lemma central_local_gap (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) (b : Card r) :
    ‖sampleOperator (ρ.comp (injection b)) (palindromePerm L)*(1-centralProjection ρ b)‖≤blockGap L := by
  change ‖sampleOperator _ _*(1-uniformOperator _)‖≤_
  rw [mul_sub,mul_one,sampleOperator_uniform_absorb,sampleOperator_weighted]
  exact palindrome_off_invariants_gap L _ (unitary_comp ρ hρ _)

lemma central_blocks_exception_bound (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ)
    (B : V →L[ℂ] V) (hB0 : ‖B‖≤1) (n : ℕ) :
    ‖B*blocks (fun b : Card r => sampleOperator (ρ.comp (injection b)) (palindromePerm L))
      (local_average_commute ρ (fun _ => palindromePerm L))*B.adjoint‖ ≤
      (blockGap L)^n + ∑ E : Finset (Card r), if E.card<n then
        ‖B*coarse (centralProjection ρ) (centralProjection_commute ρ) E*B.adjoint‖ else 0 := by
  have hB : ‖B.adjoint‖≤1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hB0
  have h := blocks_exception_bound (centralProjection ρ) (centralProjection_commute ρ)
    (fun b => uniformOperator_projection (ρ.comp (injection b)) (unitary_comp ρ hρ _))
    (fun b : Card r => sampleOperator (ρ.comp (injection b)) (palindromePerm L))
    (local_average_commute ρ (fun _ => palindromePerm L))
    (local_central_commute ρ (fun _ => palindromePerm L))
    (fun b => sampleOperator_norm_le (ρ.comp (injection b)) (unitary_comp ρ hρ _) (palindromePerm L))
    (blockGap L) (blockGap_pos L).le (blockGap_lt_one L).le (central_local_gap r L ρ hρ)
    B.adjoint hB n
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h

theorem palindrome_exception_bound (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) (n : ℕ) :
    ‖sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (palindromePerm (L+r))‖ ≤
      (blockGap L)^n + ∑ E : Finset (Card r), if E.card<n then
        ‖sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (modifiedPerm L r E)‖ else 0 := by
  rw [sampleOperator_palindrome_stage r L ρ hρ]
  rw [sampleOperator_parallel ρ (fun _ => palindromePerm L)]
  apply (central_blocks_exception_bound r L ρ hρ (sampleOperator ρ (outerPerm r L))
    (sampleOperator_norm_le ρ hρ _) n).trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro E _
  split_ifs
  · rw [sampleOperator_modified_stage r L E ρ hρ,modified_central_average]
  · rfl

end Thorp

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X Ω : Type*} [Group G] [Fintype G] [Fintype X] [Fintype Ω]

noncomputable def actionKernel (a : G →* Equiv.Perm X) (P : Ω → G) (x y : X) : ℝ :=
  finiteMean (fun ω => if a (P ω) x=y then 1 else 0)

omit [Fintype G] in
lemma actionKernel_apply (a : G →* Equiv.Perm X) (P : Ω → G)
    (v : EuclideanSpace ℂ X) (x : X) :
    DensityTransfer.applyKernel (actionKernel a P) v x =
      (Fintype.card Ω:ℂ)⁻¹ * ∑ ω, v (a (P ω) x) := by
  simp only [DensityTransfer.applyKernel_apply,actionKernel,finiteMean,
    Complex.ofReal_sum,div_eq_mul_inv,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ ω, (Fintype.card Ω:ℂ)⁻¹ * ∑ y : X, if a (P ω) x=y then v y else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp_all
    _ = _ := by simp [Finset.mul_sum]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def randomOperator (ρ : Representation ℂ G V) (P : Ω → G) : Module.End ℂ V :=
  (Fintype.card Ω:ℂ)⁻¹ • ∑ ω, ρ (P ω)⁻¹

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma coefficient_random (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (P : Ω → G) (w : V) (hw : IsFixed a x₀ ρ w) (v : V) :
    DensityTransfer.applyKernel (actionKernel a P) (normalizedCoefficient a x₀ ha ρ w v) =
      normalizedCoefficient a x₀ ha ρ w (randomOperator ρ P v) := by
  ext x
  rw [actionKernel_apply]
  simp only [normalizedCoefficient,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,
    coefficient,randomOperator,LinearMap.smul_apply,LinearMap.sum_apply,
    inner_smul_right,inner_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have h := coefficient_action a x₀ ha ρ hρ w hw v (P ω) x
  change inner ℂ (ρ (representative a x₀ ha (a (P ω) x)) w) v =
    inner ℂ (ρ (representative a x₀ ha x) w) (ρ (P ω)⁻¹ v) at h
  rw [h]
  ring

noncomputable def fixedSpace (a : G →* Equiv.Perm X) (x₀ : X) (ρ : Representation ℂ G V) :
    Submodule ℂ V where
  carrier := {w | IsFixed a x₀ ρ w}
  zero_mem' := fun g hg => map_zero _
  add_mem' := fun hw hz g hg => by rw [map_add,hw g hg,hz g hg]
  smul_mem' := fun c w hw g hg => by rw [map_smul,hw g hg]

theorem operator_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (P : Ω → G)
    (hsym : ∀ x y, actionKernel a P x y=actionKernel a P y x)
    (hrow : ∀ x, ∑ y, actionKernel a P x y=1)
    (b z M : ℝ) (hb : 0≤b) (hz : 0<z) (hM0 : 0≤M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*actionKernel a P x y)^(1+b)) ≤ M)
    (hm : 0 < Module.finrank ℂ (fixedSpace a x₀ ρ)) (v : V) (hv : ‖v‖=1) :
    ‖randomOperator ρ P v‖ ≤ M*z^(-b)+Real.sqrt (z/(Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ)) := by
  let K := fixedSpace a x₀ ρ
  let m := Module.finrank ℂ K
  let : Nonempty X := ⟨x₀⟩
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let B := stdOrthonormalBasis ℂ K
  let w : Fin m → V := fun i => (B i : V)
  have hfix (i : Fin m) : IsFixed a x₀ ρ (w i) := (B i).2
  have hw : Orthonormal ℂ w := B.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hc := normalizedCoefficient_orthonormal a x₀ ha ρ hρ w hw hfix v hv
  have hn (i : Fin m) : ‖DensityTransfer.applyKernel (actionKernel a P)
      (normalizedCoefficient a x₀ ha ρ (w i) v)‖ = ‖randomOperator ρ P v‖ := by
    rw [coefficient_random a x₀ ha ρ hρ P (w i) (hfix i),
      normalizedCoefficient_norm a x₀ ha ρ hρ (w i) (hfix i) (hw.norm_eq_one i)]
  have h := DensityTransfer.multiplicity_amplification (actionKernel a P)
    (fun x y => finiteMean_nonneg (fun _ => by split_ifs <;> norm_num)) hsym hrow
    b z M hb hz hM0 hM _ hc (‖randomOperator ρ P v‖) (fun i => (hn i).ge)
  simpa only [Fintype.card_fin] using h

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

def tupleAction : Equiv.Perm α →* Equiv.Perm (ι ↪ α) where
  toFun p :=
    { toFun := fun e => e.trans p.toEmbedding
      invFun := fun e => e.trans p.symm.toEmbedding
      left_inv := fun e => by ext i; exact p.symm_apply_apply (e i)
      right_inv := fun e => by ext i; exact p.apply_symm_apply (e i) }
  map_one' := by ext e i; rfl
  map_mul' p q := by ext e i; rfl

omit [Fintype α] [Fintype ι] in
@[simp] lemma tupleAction_apply (p : Equiv.Perm α) (e : ι ↪ α) (i : ι) :
    tupleAction p e i=p (e i) := rfl

omit [Fintype α] in
lemma tupleAction_transitive (e f : ι ↪ α) : ∃ p, tupleAction p e=f := by
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair e f e.injective f.injective
  exact ⟨p,Function.Embedding.ext hp⟩

omit [Fintype α] in
lemma tupleAction_fixed_iff [DecidableEq α] (e : ι ↪ α) (p : Equiv.Perm α) :
    tupleAction p e=e ↔ ∀ x ∈ Finset.univ.image e, p x=x := by
  constructor
  · intro h x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact congrArg (fun f : ι ↪ α => f i) h
  · intro h
    ext i
    exact h (e i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

omit [Fintype α] in
lemma tupleAction_kernel [DecidableEq α] {Ω : Type*} [Fintype Ω] (P : Ω → Equiv.Perm α)
    (e f : ι ↪ α) : actionKernel tupleAction P e f=PairRouting.tupleProbability P e f := by
  unfold actionKernel PairRouting.tupleProbability
  congr 1
  funext ω
  congr 1
  exact propext Function.Embedding.ext_iff

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

lemma irreducible_of_equiv {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : Representation.Equiv ρ σ) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible σ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hi := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let f : ρ.asModule →ₗ[MonoidAlgebra ℂ G] σ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  have hf : Function.Bijective f := e.toLinearEquiv.bijective
  exact (f.isSimpleModule_iff_of_bijective hf).mp hi

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

lemma unitaryRepresentation_coe (μ : YoungDiagram) (p : Equiv.Perm (Cell μ))
    (v : hilbertSpace μ) :
    (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ)) =
      PermutationHilbert.act (tabloidAct p) v := by
  obtain ⟨w,rfl⟩ := (spaceHilbertEquiv μ).surjective v
  change hilbertEquiv μ (tabloidRep μ p w) = _
  exact hilbert_action μ p w

noncomputable def unitaryEquiv (μ : YoungDiagram) :
    Representation.Equiv (representation μ) (unitaryRepresentation μ) :=
  Representation.Equiv.mk (spaceHilbertEquiv μ) (by
    intro p
    apply LinearMap.ext
    intro v
    change spaceHilbertEquiv μ (representation μ p v) =
      spaceHilbertEquiv μ (representation μ p ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ v)))
    rw [LinearEquiv.symm_apply_apply])

lemma unitaryRepresentation_irreducible (μ : YoungDiagram) :
    Representation.IsIrreducible (unitaryRepresentation μ) := by
  let := representation_irreducible μ
  exact UnitaryFinite.irreducible_of_equiv _ _ (unitaryEquiv μ)

lemma unitaryRepresentation_unitary (μ : YoungDiagram) :
    UnitaryFinite.IsUnitary (G := Equiv.Perm (Cell μ)) (V := hilbertSpace μ) (unitaryRepresentation μ) := by
  intro p v w
  change inner ℂ (unitaryRepresentation μ p v : PermutationHilbert.H (Tabloid μ))
      (unitaryRepresentation μ p w : PermutationHilbert.H (Tabloid μ)) = _
  rw [unitaryRepresentation_coe,unitaryRepresentation_coe]
  exact (PermutationHilbert.act (tabloidAct p)).inner_map_map v w


noncomputable def tupleFixedEquiv (μ : YoungDiagram) {ι : Type*} [Fintype ι]
    (e : ι ↪ Cell μ) :
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction e (unitaryRepresentation μ) ≃ₗ[ℂ]
      fixedHilbert μ (Finset.univ.image e) where
  toFun v := ⟨v.1.1,v.1.2,by
    intro p hp
    have h := v.2 p ((UnitaryFinite.tupleAction_fixed_iff e p).mpr hp)
    exact (unitaryRepresentation_coe μ p v.1).symm.trans (congrArg Subtype.val h)⟩
  invFun v := ⟨⟨v.1,v.2.1⟩,by
    intro p hp
    apply Subtype.ext
    exact (unitaryRepresentation_coe μ p _).trans
      (v.2.2 p ((UnitaryFinite.tupleAction_fixed_iff e p).mp hp))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tupleFixed_dimension (μ : YoungDiagram) {ι : Type*} [Fintype ι]
    (e : ι ↪ Cell μ) :
    Module.finrank ℂ (hilbertSpace μ) * (Fintype.card ι).choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction e (unitaryRepresentation μ)) *
        μ.card.choose (μ.card-μ.rowLen 0) := by
  rw [(tupleFixedEquiv μ e).finrank_eq,finrank_hilbertSpace]
  have h := fixedHilbert_dimension μ (Finset.univ.image e)
  simpa only [Finset.card_image_of_injective _ e.injective,Finset.card_univ] using h

end Thorp.Specht
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G H X Ω : Type*} [Group G] [Group H] [Fintype G] [Fintype X] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in
lemma sampleOperator_inv_apply (ρ : Representation ℂ G V) (P : Ω → G) (v : V) :
    sampleOperator ρ (fun ω => (P ω)⁻¹) v=randomOperator ρ P v := by
  simp only [sampleOperator,randomOperator,smul_apply,
    sum_apply,continuousRepresentation_apply,LinearMap.smul_apply,LinearMap.sum_apply]

theorem sampleOperator_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (P : Ω → G)
    (hsym : ∀ x y, actionKernel a P x y=actionKernel a P y x)
    (hrow : ∀ x, ∑ y, actionKernel a P x y=1)
    (b z M : ℝ) (hb : 0≤b) (hz : 0<z) (hM0 : 0≤M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*actionKernel a P x y)^(1+b)) ≤ M)
    (hm : 0 < Module.finrank ℂ (fixedSpace a x₀ ρ)) :
    ‖sampleOperator ρ P‖ ≤ M*z^(-b)+Real.sqrt (z/(Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ)) := by
  rw [←ContinuousLinearMap.adjoint.norm_map (sampleOperator ρ P),←sampleOperator_inv ρ hρ]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  rw [sampleOperator_inv_apply]
  exact operator_amplification a x₀ ha ρ hρ P hsym hrow b z M hb hz hM0 hM hm v hv

omit [Fintype G] [Fintype X] [Fintype Ω] [FiniteDimensional ℂ V] in
noncomputable def subrepresentationEquiv (ρ : Representation ℂ G V) (e : H ≃* G) :
    Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ where
  toFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun g v hv => by
        have h := U.apply_mem_toSubmodule (e.symm g) hv
        change ρ (e (e.symm g)) v∈U.toSubmodule at h
        simpa only [e.apply_symm_apply] using h }
  invFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := fun h _ hv => U.apply_mem_toSubmodule (e h) hv }
  left_inv U := by apply Subrepresentation.toSubmodule_injective; rfl
  right_inv U := by apply Subrepresentation.toSubmodule_injective; rfl
  map_rel_iff' := Iff.rfl

omit [Fintype G] [Fintype X] [Fintype Ω] [FiniteDimensional ℂ V] in
lemma irreducible_comp_equiv (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (e : H ≃* G) : Representation.IsIrreducible (ρ.comp e.toMonoidHom) := by
  exact (subrepresentationEquiv ρ e).isSimpleOrder_iff.mpr inferInstance

end Thorp.UnitaryFinite

namespace Thorp.Specht
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

omit [Fintype α] in
lemma relabelledUnitary_unitary (μ : YoungDiagram) (e : α ≃ Cell μ) :
    UnitaryFinite.IsUnitary (V := hilbertSpace μ) (relabelledUnitary μ e) := by
  intro g v w
  exact unitaryRepresentation_unitary μ (e.permCongr g) v w

omit [Fintype α] in
lemma relabelledUnitary_irreducible (μ : YoungDiagram) (e : α ≃ Cell μ) :
    Representation.IsIrreducible (relabelledUnitary μ e) := by
  let := unitaryRepresentation_irreducible μ
  exact UnitaryFinite.irreducible_comp_equiv (V := hilbertSpace μ) (unitaryRepresentation μ) e.permCongrHom

noncomputable def relabelledTupleFixed (μ : YoungDiagram) (e : α ≃ Cell μ) (f : ι ↪ α) :
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction f (relabelledUnitary μ e) ≃ₗ[ℂ]
    UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction (f.trans e.toEmbedding) (unitaryRepresentation μ) where
  toFun v := ⟨v.1,by
    intro g hg
    have hp : UnitaryFinite.tupleAction (e.symm.permCongr g) f=f := by
      apply Function.Embedding.ext
      intro i
      have hh := congrArg (fun f : ι ↪ Cell μ => f i) hg
      change g (e (f i))=e (f i) at hh
      simp only [UnitaryFinite.tupleAction_apply,Equiv.permCongr_apply,Equiv.symm_symm,e.symm_apply_apply,hh]
    have hh := v.2 (e.symm.permCongr g) hp
    change unitaryRepresentation μ (e.permCongr (e.symm.permCongr g)) v=v at hh
    have he : e.permCongr (e.symm.permCongr g)=g := by
      apply Equiv.ext
      intro x
      simp only [Equiv.permCongr_apply,Equiv.symm_symm,e.apply_symm_apply]
    simpa only [he] using hh⟩
  invFun v := ⟨v.1,by
    intro g hg
    have hp : UnitaryFinite.tupleAction (e.permCongr g) (f.trans e.toEmbedding)=f.trans e.toEmbedding := by
      apply Function.Embedding.ext
      intro i
      have hh := congrArg (fun f : ι ↪ α => f i) hg
      change g (f i)=f i at hh
      simp only [UnitaryFinite.tupleAction_apply,Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply,Equiv.permCongr_apply,e.symm_apply_apply,hh]
    exact v.2 (e.permCongr g) hp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype α] in
lemma relabelled_tuple_dimension (μ : YoungDiagram) (e : α ≃ Cell μ) (f : ι ↪ α) :
    Module.finrank ℂ (hilbertSpace μ) * (Fintype.card ι).choose (μ.card-μ.rowLen 0) ≤
      Module.finrank ℂ (UnitaryFinite.fixedSpace (V := hilbertSpace μ) UnitaryFinite.tupleAction f (relabelledUnitary μ e)) *
        μ.card.choose (μ.card-μ.rowLen 0) := by
  rw [(relabelledTupleFixed μ e f).finrank_eq]
  exact tupleFixed_dimension μ (f.trans e.toEmbedding)

end Thorp.Specht

namespace Thorp.SparseContact
open scoped BigOperators Classical

noncomputable def pointStabilizer {α : Type*} (A : Finset α) : Subgroup (Equiv.Perm α) where
  carrier := {p | ∀ x ∈ A, p x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by intro p q hp hq x hx; change p (q x) = x; rw [hq x hx, hp x hx]
  inv_mem' := by intro p hp x hx; exact (Equiv.Perm.inv_eq_iff_eq).mpr (hp x hx).symm

lemma swap_mem_pointStabilizer {α : Type*} [DecidableEq α] (A : Finset α)
    (x y : α) (hx : x ∉ A) (hy : y ∉ A) : Equiv.swap x y ∈ pointStabilizer A := by
  intro z hz
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ hz)) (fun h => hy (h ▸ hz))

lemma point_symmetrizer_zero (μ : YoungDiagram) (A : Finset (Specht.Cell μ))
    (hA : A.card < μ.card - μ.rowLen 0) (v : Specht.Tabloid μ → ℂ) (hv : v ∈ Specht.space μ) :
    Specht.symmetrizer (pointStabilizer A) (Specht.tabloidRep μ) v = 0 := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p,rfl⟩ := hv
    let e : {x : Specht.Cell μ // p x ∉ A} ≃ {x : Specht.Cell μ // x ∉ A} :=
      { toFun := fun x => ⟨p x.1,x.2⟩
        invFun := fun x => ⟨p.symm x.1, by simpa only [p.apply_symm_apply] using x.2⟩
        left_inv := fun x => by apply Subtype.ext; exact p.symm_apply_apply _
        right_inv := fun x => by apply Subtype.ext; exact p.apply_symm_apply _ }
    have hc : μ.rowLen 0 < Fintype.card {x : Specht.Cell μ // p x ∉ A} := by
      rw [Fintype.card_congr e, Fintype.card_subtype_compl, Specht.card_cell, Fintype.card_coe]
      have hr := Specht.rowLen_zero_le_card μ
      omega
    obtain ⟨x,y,hne,hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun x : {x : Specht.Cell μ // p x ∉ A} => Specht.colIndex x.1)
      (by simpa only [Fintype.card_fin] using hc)
    have hxy : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
    let h : pointStabilizer A := ⟨Equiv.swap (p x.1) (p y.1),
      swap_mem_pointStabilizer A _ _ x.2 y.2⟩
    apply Specht.symmetrizer_eq_zero_of_neg _ _ h
    change Specht.tabloidRep μ (Equiv.swap (p x.1) (p y.1))
      (Specht.tabloidRep μ p (Specht.polytabloid μ)) = -Specht.tabloidRep μ p (Specht.polytabloid μ)
    rw [←Module.End.mul_apply, ←map_mul, ←Equiv.mul_swap_eq_swap_mul]
    rw [map_mul, Module.End.mul_apply,
      Specht.swap_polytabloid x.1 y.1 hxy (congrArg Fin.val hcol), map_neg]
  | zero => exact map_zero _
  | add v w hv hw ihv ihw => simp only [map_add,ihv,ihw,add_zero]
  | smul a v hv ih => simp only [map_smul,ih,smul_zero]

lemma point_fixed_zero (μ : YoungDiagram) (A : Finset (Specht.Cell μ))
    (hA : A.card < μ.card - μ.rowLen 0) (v : Specht.Tabloid μ → ℂ) (hv : v ∈ Specht.space μ)
    (hfix : ∀ p, p ∈ pointStabilizer A → Specht.tabloidRep μ p v = v) : v = 0 := by
  classical
  have hz := point_symmetrizer_zero μ A hA v hv
  have he : Specht.symmetrizer (pointStabilizer A) (Specht.tabloidRep μ) v =
      (Fintype.card (pointStabilizer A) : ℂ) • v := by
    simp only [Specht.symmetrizer, LinearMap.sum_apply, hfix _ (Subtype.prop _),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  rw [he] at hz
  exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

lemma point_unitary_fixed_zero (μ : YoungDiagram) (A : Finset (Specht.Cell μ))
    (hA : A.card < μ.card - μ.rowLen 0) (v : Specht.hilbertSpace μ)
    (hfix : ∀ p, p ∈ pointStabilizer A → Specht.unitaryRepresentation μ p v = v) : v = 0 := by
  let w := (Specht.spaceHilbertEquiv μ).symm v
  have hw : ∀ p, p ∈ pointStabilizer A → Specht.tabloidRep μ p w.val = w.val := by
    intro p hp
    have he := congrArg ((Specht.spaceHilbertEquiv μ).symm) (hfix p hp)
    change Specht.representation μ p w = w at he
    exact congrArg Subtype.val he
  have hz := point_fixed_zero μ A hA w.val w.prop hw
  have hw0 : w = 0 := Subtype.ext hz
  have he := congrArg (Specht.spaceHilbertEquiv μ) hw0
  simpa only [w, LinearEquiv.apply_symm_apply, map_zero] using he

lemma point_relabelled_fixed_zero {α : Type*} [Fintype α] (μ : YoungDiagram)
    (e : α ≃ Specht.Cell μ) (A : Finset α) (hA : A.card < μ.card - μ.rowLen 0)
    (v : Specht.hilbertSpace μ)
    (hfix : ∀ p, p ∈ pointStabilizer A → Specht.relabelledUnitary μ e p v = v) : v = 0 := by
  classical
  apply point_unitary_fixed_zero μ (A.image e) (by simpa only [Finset.card_image_of_injective _ e.injective] using hA) v
  intro p hp
  have hf : e.symm.permCongr p ∈ pointStabilizer A := by
    intro x hx
    have hh := hp (e x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, hh, e.symm_apply_apply]
  have hh := hfix _ hf
  change Specht.unitaryRepresentation μ (e.permCongr (e.symm.permCongr p)) v = v at hh
  have he : e.permCongr (e.symm.permCongr p) = p := by
    apply Equiv.ext
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, e.apply_symm_apply]
  simpa only [he] using hh


lemma small_dominating_set {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : ∀ v, ∃ w, G.Adj v w) :
    ∃ R : Finset V, 2 * R.card ≤ Fintype.card V ∧
      ∀ v, v ∉ R → ∃ w ∈ R, G.Adj v w := by
  classical
  obtain ⟨F, hFG, hF, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  let c := hF.coloringTwo
  have hneigh (v : V) : ∃ w, F.Adj v w := by
    obtain ⟨w, hvw⟩ := hG v
    have hr : F.Reachable v w := by rw [hreach]; exact hvw.reachable
    exact hr.nonempty_neighborSet_left hvw.ne
  let A : Finset V := Finset.univ.filter (fun v => c v = 0)
  let B : Finset V := Finset.univ.filter (fun v => c v ≠ 0)
  have hab : A.card + B.card = Fintype.card V := by
    exact Finset.card_filter_add_card_filter_not _
  have hcolor {v w : V} (hvw : F.Adj v w) : c v ≠ c w := c.valid hvw
  by_cases h : A.card ≤ B.card
  · refine ⟨A, by omega, ?_⟩
    intro v hv
    obtain ⟨w, hvw⟩ := hneigh v
    have hv0 : c v ≠ 0 := by simpa [A] using hv
    have hw0 : c w = 0 := by
      have hv1 : c v = 1 := by omega
      have hn := hcolor hvw
      omega
    exact ⟨w, by simp [A, hw0], hFG hvw⟩
  · refine ⟨B, by omega, ?_⟩
    intro v hv
    obtain ⟨w, hvw⟩ := hneigh v
    have hv0 : c v = 0 := by simpa [B] using hv
    have hw0 : c w ≠ 0 := by simpa [hv0] using (hcolor hvw).symm
    exact ⟨w, by simp [B, hw0], hFG hvw⟩

lemma powerset_weight_le_exp {V : Type*} [DecidableEq V] (S : Finset V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) :
    (∑ L ∈ S.powerset, ∏ v ∈ L, p v) ≤ Real.exp (∑ v ∈ S, p v) := by
  rw [← Finset.prod_one_add, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro v _; exact add_nonneg (by norm_num) (hp v)
  · intro v _
    have h := Real.add_one_le_exp (p v)
    linarith

lemma fixed_size_weight_le {V : Type*} [DecidableEq V] (S : Finset V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (∑ L ∈ S.powersetCard m, ∏ v ∈ L, p v) ≤
      δ^m * Real.exp ((∑ v ∈ S, p v)/δ) := by
  have hsplit (L : Finset V) (hL : L ∈ S.powersetCard m) :
      (∏ v ∈ L, p v) = δ^m * ∏ v ∈ L, (p v / δ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hL).2]
    field_simp
  calc
    _ = δ^m * ∑ L ∈ S.powersetCard m, ∏ v ∈ L, (p v/δ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hsplit
    _ ≤ δ^m * ∑ L ∈ S.powerset, ∏ v ∈ L, (p v/δ) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ.le _)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro L hL
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hL).1
      · intro L _ _; exact Finset.prod_nonneg (fun v _ => div_nonneg (hp v) hδ.le)
    _ ≤ δ^m * Real.exp (∑ v ∈ S, p v/δ) :=
      mul_le_mul_of_nonneg_left
        (powerset_weight_le_exp S (fun v => p v/δ) (fun v => div_nonneg (hp v) hδ.le))
        (pow_nonneg hδ.le _)
    _ = _ := by rw [Finset.sum_div]

noncomputable def neighborhood {V : Type*} [Fintype V] (G : SimpleGraph V)
    (R : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => ∃ v ∈ R, G.Adj v w)

lemma neighborhood_weight_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (δ : ℝ)
    (hdeg : ∀ v, (∑ w, if G.Adj v w then p w else 0) ≤ δ) (R : Finset V) :
    (∑ w ∈ neighborhood G R, p w) ≤ R.card * δ := by
  classical
  calc
    _ ≤ ∑ w ∈ neighborhood G R, ∑ v ∈ R, if G.Adj v w then p w else 0 := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨v, hv, hvw⟩ := (Finset.mem_filter.mp hw).2
      have h : (if G.Adj v w then p w else 0) ≤
          ∑ u ∈ R, if G.Adj u w then p w else 0 :=
        Finset.single_le_sum (f := fun u => if G.Adj u w then p w else 0) (fun u _ => by split_ifs; exact hp w; exact le_rfl) hv
      simpa only [ite_eq_left hvw] using h
    _ ≤ ∑ w, ∑ v ∈ R, if G.Adj v w then p w else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro w _ _
      exact Finset.sum_nonneg (fun v _ => by split_ifs; exact hp w; exact le_rfl)
    _ = ∑ v ∈ R, ∑ w, if G.Adj v w then p w else 0 := Finset.sum_comm
    _ ≤ ∑ v ∈ R, δ := Finset.sum_le_sum (fun v _ => hdeg v)
    _ = _ := by simp

lemma root_leaves_weight_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (k : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdeg : ∀ v, (∑ w, if G.Adj v w then p w else 0) ≤ δ)
    (R : Finset V) (hR : 2 * R.card ≤ k) :
    (∑ L ∈ (neighborhood G R).powersetCard (k-R.card), ∏ v ∈ L, p v) ≤
      δ^((k:ℝ)/2) * Real.exp R.card := by
  classical
  have hmass := neighborhood_weight_le G p hp δ hdeg R
  have hpow : δ^(k-R.card) ≤ δ^((k:ℝ)/2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    have hr : R.card ≤ k := by omega
    rw [Nat.cast_sub hr]
    have hh : (2:ℝ)*R.card ≤ k := by exact_mod_cast hR
    linarith
  apply (fixed_size_weight_le (neighborhood G R) p hp _ δ hδ).trans
  apply mul_le_mul hpow
  · apply Real.exp_le_exp.mpr
    exact (div_le_iff₀ hδ).mpr hmass
  · positivity
  · positivity

def NoIsolated {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v ∈ S, ∃ w ∈ S, G.Adj v w

lemma small_dominating_subset {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (hS : NoIsolated G S) :
    ∃ R : Finset V, R ⊆ S ∧ 2 * R.card ≤ S.card ∧ S \ R ⊆ neighborhood G R := by
  classical
  let H := G.induce (S : Set V)
  have hH : ∀ v : S, ∃ w : S, H.Adj v w := by
    intro v
    obtain ⟨w, hw, hvw⟩ := hS v v.2
    exact ⟨⟨w, hw⟩, hvw⟩
  obtain ⟨R, hR, hdom⟩ := small_dominating_set H hH
  let T := R.image (fun v : S => (v : V))
  have hc : T.card = R.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨T, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · simpa [hc, H] using hR
  · intro v hv
    have hvS := (Finset.mem_sdiff.mp hv).1
    have hvR : (⟨v, hvS⟩ : S) ∉ R := by
      intro hh
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨⟨v,hvS⟩, hh, rfl⟩)
    obtain ⟨w, hw, hvw⟩ := hdom ⟨v,hvS⟩ hvR
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨w, Finset.mem_image.mpr ⟨w,hw,rfl⟩, hvw.symm⟩⟩

end Thorp.SparseContact

end ThorpNine.Casimir

end OAI
