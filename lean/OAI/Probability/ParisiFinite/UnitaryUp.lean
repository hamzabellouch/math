import Mathlib
import OAI.Probability.ParisiFinite.Labels

namespace OAI

/-! Unitary Up. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology

namespace HilbertChain
variable (H : ℕ → Type*) [∀n, NormedAddCommGroup (H n)] [∀n, InnerProductSpace ℂ (H n)]
variable (step : ∀n, H n →ₗᵢ[ℂ] H (n+1))
variable (U : ∀n, H n ≃ₗᵢ[ℂ] H n) (N : ℕ)
variable (hU : ∀n, N ≤ n → ∀x, step n (U n x)=U (n+1) (step n x))

include hU in
lemma unitary_up (n m : ℕ) (hn : N ≤ n) (hnm : n ≤ m) (x : H n) :
    up H step n m hnm (U n x)=U m (up H step n m hnm x) := by
  induction m,hnm using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    rw [up_succ H step n m h]
    change step m (up H step n m h (U n x))=U (m+1) (step m (up H step n m h x))
    rw [ih,hU m (hn.trans h)]

include hU in
lemma embed_unitary_up (n m : ℕ) (hn : N ≤ n) (hnm : n ≤ m) (x : H n) :
    embed H step m (U m (up H step n m hnm x))=embed H step n (U n x) := by
  rw [←unitary_up H step U N hU n m hn hnm,embed_up]

 

def unitaryStage (n : ℕ) : H n →ₗᵢ[ℂ] Space H step :=
  (embed H step (n+N)).comp ((U (n+N)).toLinearIsometry.comp
    (up H step n (n+N) (Nat.le_add_right n N)))

include hU in
lemma unitaryStage_eq (n k : ℕ) (hnk : n ≤ k) (hk : N ≤ k) (x : H n) :
    unitaryStage H step U N n x=embed H step k (U k (up H step n k hnk x)) := by
  let m := n+N+k
  have hnm : n+N ≤ m := Nat.le_add_right _ _
  have hkm : k ≤ m := by dsimp [m]; omega
  have hN : N ≤ n+N := Nat.le_add_left _ _
  have he₁ := embed_unitary_up H step U N hU (n+N) m hN hnm
    (up H step n (n+N) (Nat.le_add_right _ _) x)
  have he₂ := embed_unitary_up H step U N hU k m hk hkm (up H step n k hnk x)
  have hc₁ := congrArg (fun T => T x)
    (up_comp H step n (n+N) m (Nat.le_add_right _ _) hnm)
  have hc₂ := congrArg (fun T => T x) (up_comp H step n k m hnk hkm)
  change up H step (n+N) m hnm (up H step n (n+N) _ x)=_ at hc₁
  change up H step k m hkm (up H step n k hnk x)=_ at hc₂
  rw [hc₁] at he₁
  rw [hc₂] at he₂
  exact he₁.symm.trans he₂

include hU in
lemma unitaryStage_compat (n : ℕ) (x : H n) :
    unitaryStage H step U N (n+1) (step n x)=unitaryStage H step U N n x := by
  let k := n+1+N
  have hnk : n+1 ≤ k := Nat.le_add_right _ _
  have hk : N ≤ k := Nat.le_add_left _ _
  rw [unitaryStage_eq H step U N hU (n+1) k hnk hk,
    unitaryStage_eq H step U N hU n k ((Nat.le_succ n).trans hnk) hk]
  congr 2
  have h := congrArg (fun T => T x) (up_comp H step n (n+1) k (Nat.le_succ n) hnk)
  simpa using h

def limitIsometry : Space H step →ₗᵢ[ℂ] Space H step :=
  lift H step (unitaryStage H step U N) (unitaryStage_compat H step U N hU)

@[simp] lemma limitIsometry_embed (n : ℕ) (hn : N ≤ n) (x : H n) :
    limitIsometry H step U N hU (embed H step n x)=embed H step n (U n x) := by
  rw [limitIsometry,lift_embed,unitaryStage_eq H step U N hU n n le_rfl hn]
  simp

include hU in
lemma symm_compat (n : ℕ) (hn : N ≤ n) (x : H n) :
    step n ((U n).symm x)=(U (n+1)).symm (step n x) := by
  apply (U (n+1)).injective
  rw [←hU n hn,(U n).apply_symm_apply,(U (n+1)).apply_symm_apply]

lemma limitIsometry_inverse (x : Space H step) :
    limitIsometry H step (fun n => (U n).symm) N (symm_compat H step U N hU)
      (limitIsometry H step U N hU x)=x := by
  apply congrFun ((denseRange_embed H step).equalizer
    ((limitIsometry H step (fun n => (U n).symm) N (symm_compat H step U N hU)).continuous.comp
      (limitIsometry H step U N hU).continuous) continuous_id ?_) x
  funext ⟨n,y⟩
  simp only [Function.comp_apply, id_eq]
  have he := embed_up H step n (n+N) (Nat.le_add_right n N) y
  rw [←he,limitIsometry_embed _ _ _ _ _ _ (Nat.le_add_left N n),
    limitIsometry_embed _ _ _ _ _ _ (Nat.le_add_left N n),(U (n+N)).symm_apply_apply]

 

def limitUnitary : Space H step ≃ₗᵢ[ℂ] Space H step where
  toFun := limitIsometry H step U N hU
  map_add' := (limitIsometry H step U N hU).map_add
  map_smul' := (limitIsometry H step U N hU).map_smul
  norm_map' := (limitIsometry H step U N hU).norm_map
  invFun := limitIsometry H step (fun n => (U n).symm) N (symm_compat H step U N hU)
  left_inv := limitIsometry_inverse H step U N hU
  right_inv x := by
    have h := limitIsometry_inverse H step (fun n => (U n).symm) N
      (symm_compat H step U N hU) x
    simpa only [LinearIsometryEquiv.symm_symm] using h

@[simp] lemma limitUnitary_embed (n : ℕ) (hn : N ≤ n) (x : H n) :
    limitUnitary H step U N hU (embed H step n x)=embed H step n (U n x) :=
  limitIsometry_embed H step U N hU n hn x

@[simp] lemma limitUnitary_symm_embed (n : ℕ) (hn : N ≤ n) (x : H n) :
    (limitUnitary H step U N hU).symm (embed H step n x)=embed H step n ((U n).symm x) :=
  limitIsometry_embed H step (fun n => (U n).symm) N (symm_compat H step U N hU) n hn x
end HilbertChain

namespace PointedTree
 
def ordinaryInfinity (w : List Gate) : WholeInfinity ≃ₗᵢ[ℂ] WholeInfinity :=
  HilbertChain.limitUnitary Level wholeStep (fun n => (ordinary w n).op) w.length
    (ordinary_compatible w)

@[simp] theorem ordinaryInfinity_embed (w : List Gate) (n : ℕ) (hn : w.length ≤ n) (x : Level n) :
    ordinaryInfinity w (wholeEmbed n x)=wholeEmbed n ((ordinary w n).op x) :=
  HilbertChain.limitUnitary_embed _ _ _ _ _ _ hn x

@[simp] theorem ordinaryInfinity_symm_embed (w : List Gate) (n : ℕ) (hn : w.length ≤ n) (x : Level n) :
    (ordinaryInfinity w).symm (wholeEmbed n x)=wholeEmbed n ((ordinary w n).op.symm x) :=
  HilbertChain.limitUnitary_symm_embed _ _ _ _ _ _ hn x
end PointedTree

 

open scoped InnerProductSpace Topology

namespace PointedTree
open CoherentFock

theorem gammaEmbedding_comp {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (T : E →ₗᵢ[ℂ] F) (S : F →ₗᵢ[ℂ] G) :
    (gammaEmbedding S).comp (gammaEmbedding T)=gammaEmbedding (S.comp T) := by
  ext x
  exact congrArg (fun A => A x) (Gamma_comp T S)

@[simp] theorem modeEmbed_step (n : ℕ) (x : Mode n) :
    modeEmbed (n+1) (modeStep n x)=modeEmbed n x :=
  HilbertChain.embed_step ModeSpace modeStep n x

 
def topFockMap (n : ℕ) : Level (n+1) →ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  spinMap (gammaEmbedding (modeEmbed n))

@[simp] theorem topFockMap_step (n : ℕ) (x : Level (n+1)) :
    topFockMap (n+1) (wholeStep (n+1) x)=topFockMap n x := by
  change spinMap (gammaEmbedding (modeEmbed (n+1)))
    (spinMap (gammaEmbedding (modeStep n)) x)=spinMap (gammaEmbedding (modeEmbed n)) x
  have hm : (modeEmbed (n+1)).comp (modeStep n)=modeEmbed n := by
    ext d
    exact modeEmbed_step n d
  ext i
  change gammaEmbedding (modeEmbed (n+1)) (gammaEmbedding (modeStep n) (x i)) =
    gammaEmbedding (modeEmbed n) (x i)
  have h := gammaEmbedding_comp (modeStep n) (modeEmbed (n+1))
  rw [hm] at h
  exact congrArg (fun T => T (x i)) h

def unfoldStage (n : ℕ) : Level n →ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  (topFockMap n).comp (wholeStep n)

@[simp] theorem unfoldStage_compat (n : ℕ) (x : Level n) :
    unfoldStage (n+1) (wholeStep n x)=unfoldStage n x :=
  topFockMap_step n (wholeStep n x)

 
def unfoldTree : WholeInfinity →ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  HilbertChain.lift Level wholeStep unfoldStage unfoldStage_compat

@[simp] theorem unfoldTree_embed_succ (n : ℕ) (x : Level (n+1)) :
    unfoldTree (wholeEmbed (n+1) x)=topFockMap n x := by
  rw [unfoldTree,HilbertChain.lift_embed]
  exact topFockMap_step n x

@[simp] theorem unfoldTree_vacuum : unfoldTree vacuumInfinity=vacuum ModeInfinity := by
  rw [←embed_vac 1,unfoldTree_embed_succ]
  ext i
  change gammaEmbedding (modeEmbed 0) (vacuum (Mode 0) i)=vacuum ModeInfinity i
  simp only [vacuum_apply,map_smul,gammaEmbedding_coherent,map_zero]

 
def spinSingleAux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (i : Fin 2) : E →ₗᵢ[ℂ] SpinOperators.Double E where
  toFun x := PiLp.single 2 i x
  map_add' x y := PiLp.single_add 2 i
  map_smul' z x := by
    apply WithLp.ofLp_injective
    exact Pi.single_smul (f := fun _ : Fin 2 => E) i z x
  norm_map' x := PiLp.norm_single 2 (fun _ : Fin 2 => E) i x

def spinSingle (i : Fin 2) : Space ModeInfinity →ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  spinSingleAux i

@[simp] theorem spinSingle_apply (i : Fin 2) (x : Space ModeInfinity) :
    spinSingle i x=PiLp.single 2 i x := rfl

lemma spinMap_single {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (T : E →ₗᵢ[ℂ] F)
    (i : Fin 2) (x : E) : spinMap T (PiLp.single 2 i x)=PiLp.single 2 i (T x) := by
  ext j
  by_cases h : j=i
  · subst j; simp [spinMap_apply]
  · simp [spinMap_apply,h]

lemma coherent_in_unfoldTree_range (i : Fin 2) (d : ModeInfinity) :
    spinSingle i (coherent d) ∈ Set.range unfoldTree := by
  have hclosed : IsClosed (Set.range unfoldTree) :=
    unfoldTree.isometry.antilipschitzWith.isClosed_range unfoldTree.isometry.uniformContinuous
  refine (HilbertChain.denseRange_embed ModeSpace modeStep).induction_on
    (p := fun d => spinSingle i (coherent d) ∈ Set.range unfoldTree) d
    (hclosed.preimage ((spinSingle i).continuous.comp continuous_coherent)) ?_
  rintro ⟨n,e⟩
  refine ⟨wholeEmbed (n+1) (PiLp.single 2 i (coherent e)),?_⟩
  rw [unfoldTree_embed_succ]
  change spinMap (gammaEmbedding (modeEmbed n)) (PiLp.single 2 i (coherent e))=_
  rw [spinMap_single,gammaEmbedding_coherent]
  rfl

lemma spinSingle_in_unfoldTree_range (i : Fin 2) (x : Space ModeInfinity) :
    spinSingle i x ∈ Set.range unfoldTree := by
  have hclosed : IsClosed (Set.range unfoldTree) :=
    unfoldTree.isometry.antilipschitzWith.isClosed_range unfoldTree.isometry.uniformContinuous
  let R := unfoldTree.toLinearMap.range
  change spinSingle i x ∈ R
  refine UniformSpace.Completion.induction_on x
    (hclosed.preimage (spinSingle i).continuous) fun y => ?_
  rw [coe_eq_sum]
  simp only [Finsupp.sum,map_sum,map_smul]
  exact Submodule.sum_mem R fun e he => Submodule.smul_mem R _ (coherent_in_unfoldTree_range i e)

 

theorem unfoldTree_surjective : Function.Surjective unfoldTree := by
  intro x
  let R := unfoldTree.toLinearMap.range
  have h : (∑i : Fin 2,spinSingle i (x i)) ∈ R :=
    Submodule.sum_mem R fun i hi => spinSingle_in_unfoldTree_range i (x i)
  have he : (∑i : Fin 2,spinSingle i (x i))=x := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_two]
  rwa [he] at h

 
def treeFockEquiv : WholeInfinity ≃ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  LinearIsometryEquiv.ofSurjective unfoldTree unfoldTree_surjective

@[simp] lemma treeFockEquiv_apply (x : WholeInfinity) : treeFockEquiv x=unfoldTree x := rfl
end PointedTree

 

open scoped InnerProductSpace Topology
namespace HilbertChain
variable (H : ℕ → Type*) [∀n, NormedAddCommGroup (H n)] [∀n, InnerProductSpace ℂ (H n)]
variable (step : ∀n, H n →ₗᵢ[ℂ] H (n+1))
variable {F : Type*} [TopologicalSpace F] [T2Space F]

theorem continuous_ext_above (N : ℕ) {f g : Space H step → F}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀n, N ≤ n → ∀x, f (embed H step n x)=g (embed H step n x)) : f=g := by
  apply (denseRange_embed H step).equalizer hf hg
  funext ⟨n,x⟩
  simp only [Function.comp_apply]
  rw [←embed_up H step n (n+N) (Nat.le_add_right n N) x]
  exact h (n+N) (Nat.le_add_left N n) _
end HilbertChain

namespace PointedTree
open CoherentFock RootSpin

 
def rootInfinity (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) :
    WholeInfinity ≃ₗᵢ[ℂ] WholeInfinity :=
  HilbertChain.limitUnitary Level wholeStep (fun n => rootEquiv n A hA) 0 (by
    intro n hn x
    exact (congrArg (wholeStep n) (rootEquiv_apply n A hA x)).trans
      ((root_empty n A x).trans (rootEquiv_apply (n+1) A hA (wholeStep n x)).symm))

@[simp] theorem rootInfinity_embed (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (n : ℕ) (x : Level n) :
    rootInfinity A hA (wholeEmbed n x)=wholeEmbed n (root n A x) := by
  exact (HilbertChain.limitUnitary_embed _ _ _ _ _ n (Nat.zero_le n) x).trans
    (congrArg (wholeEmbed n) (rootEquiv_apply n A hA x))

@[simp] theorem rootInfinity_unfold (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (x : WholeInfinity) :
    unfoldTree (rootInfinity A hA x)=SpinOperators.act A (unfoldTree x) := by
  apply congrFun (HilbertChain.continuous_ext_above Level wholeStep 1
    (unfoldTree.continuous.comp (rootInfinity A hA).continuous)
    ((SpinOperators.act A).continuous.comp unfoldTree.continuous) ?_) x
  intro n hn y
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  simp only [Function.comp_apply]
  rw [rootInfinity_embed,unfoldTree_embed_succ,unfoldTree_embed_succ]
  exact spinMap_root (gammaEmbedding (modeEmbed k)) A y

 

theorem actual_insertionInfinity (w : List Gate) :
    modeInWhole (insertionInfinity w)=
      (ordinaryInfinity w).symm (rootInfinity Z Z_unitary (ordinaryInfinity w vacuumInfinity)) := by
  rw [insertionInfinity,modeInWhole_embed,←embed_vac w.length,
    ordinaryInfinity_embed w w.length le_rfl,rootInfinity_embed,
    ordinaryInfinity_symm_embed w w.length le_rfl]
  rfl

 
theorem ordinaryInfinity_cost (w : List Gate) (γ : ℝ) (x : WholeInfinity) :
    unfoldTree (ordinaryInfinity (.cost γ::w) x)=
      WZ (-(γ:ℂ) • insertionInfinity w) (unfoldTree (ordinaryInfinity w x)) := by
  apply congrFun (HilbertChain.continuous_ext_above Level wholeStep (w.length+1)
    (unfoldTree.continuous.comp (ordinaryInfinity (.cost γ::w)).continuous)
    ((WZ (-(γ:ℂ) • insertionInfinity w)).continuous.comp (unfoldTree.continuous.comp (ordinaryInfinity w).continuous)) ?_) x
  intro n hn y
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  have hw : w.length ≤ k := by omega
  simp only [Function.comp_apply]
  rw [ordinaryInfinity_embed (.cost γ::w) _ (by simpa using hn),
    ordinaryInfinity_embed w _ (by omega),unfoldTree_embed_succ,unfoldTree_embed_succ]
  change spinMap (gammaEmbedding (modeEmbed k))
    (WZ (-(γ:ℂ) • (ordinary w k).insertion) ((ordinary w (k+1)).op y))=_
  rw [spinMap_cost,map_smul,insertionInfinity_stable w k hw]
  rfl

theorem ordinaryInfinity_mixer (w : List Gate) (β : ℝ) (x : WholeInfinity) :
    unfoldTree (ordinaryInfinity (.mixer β::w) x)=
      SpinOperators.act (R β) (unfoldTree (ordinaryInfinity w x)) := by
  apply congrFun (HilbertChain.continuous_ext_above Level wholeStep (w.length+1)
    (unfoldTree.continuous.comp (ordinaryInfinity (.mixer β::w)).continuous)
    ((SpinOperators.act (R β)).continuous.comp (unfoldTree.continuous.comp (ordinaryInfinity w).continuous)) ?_) x
  intro n hn y
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  simp only [Function.comp_apply]
  rw [ordinaryInfinity_embed (.mixer β::w) _ (by simpa using hn),
    ordinaryInfinity_embed w _ (by omega),unfoldTree_embed_succ,unfoldTree_embed_succ]
  exact spinMap_root (gammaEmbedding (modeEmbed k)) (R β) ((ordinary w (k+1)).op y)

end PointedTree

 

open scoped InnerProductSpace Topology
namespace PointedTree
open CoherentFock RootSpin

 
def modeFock : ModeInfinity →ₗᵢ[ℂ] SpinSpace ModeInfinity := unfoldTree.comp modeInWhole

 
def ordinaryLocal (w : List Gate) : SpinSpace ModeInfinity ≃ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  (treeFockEquiv.symm.trans (ordinaryInfinity w)).trans treeFockEquiv

@[simp] theorem ordinaryLocal_apply (w : List Gate) (x : SpinSpace ModeInfinity) :
    ordinaryLocal w x=unfoldTree (ordinaryInfinity w (treeFockEquiv.symm x)) := rfl

@[simp] theorem ordinaryLocal_unfold (w : List Gate) (x : WholeInfinity) :
    ordinaryLocal w (unfoldTree x)=unfoldTree (ordinaryInfinity w x) := by
  change unfoldTree (ordinaryInfinity w (treeFockEquiv.symm (treeFockEquiv x)))=_
  rw [LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem ordinaryLocal_nil (x : SpinSpace ModeInfinity) : ordinaryLocal [] x=x := by
  obtain ⟨y,rfl⟩ := unfoldTree_surjective x
  rw [ordinaryLocal_unfold]
  congr 1
  apply congrFun (HilbertChain.continuous_ext_above Level wholeStep 0
    (ordinaryInfinity []).continuous continuous_id ?_) y
  intro n hn z
  simp only [ordinaryInfinity_embed [] n (Nat.zero_le n),ordinary,EvenUnitary.ident]
  rfl

@[simp] theorem ordinaryLocal_cost (w : List Gate) (γ : ℝ) (x : SpinSpace ModeInfinity) :
    ordinaryLocal (.cost γ::w) x=WZ (-(γ:ℂ) • insertionInfinity w) (ordinaryLocal w x) := by
  exact ordinaryInfinity_cost w γ (treeFockEquiv.symm x)

@[simp] theorem ordinaryLocal_mixer (w : List Gate) (β : ℝ) (x : SpinSpace ModeInfinity) :
    ordinaryLocal (.mixer β::w) x=SpinOperators.act (R β) (ordinaryLocal w x) := by
  exact ordinaryInfinity_mixer w β (treeFockEquiv.symm x)

@[simp] theorem modeFock_insertion (w : List Gate) :
    modeFock (insertionInfinity w)=
      (ordinaryLocal w).symm (SpinOperators.act Z (ordinaryLocal w (vacuum ModeInfinity))) := by
  apply (ordinaryLocal w).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change ordinaryLocal w (unfoldTree (modeInWhole (insertionInfinity w)))=_
  rw [ordinaryLocal_unfold,actual_insertionInfinity,LinearIsometryEquiv.apply_symm_apply,
    rootInfinity_unfold,←unfoldTree_vacuum,ordinaryLocal_unfold]

 
@[simp] theorem insertionInfinity_cost (w : List Gate) (γ : ℝ) :
    insertionInfinity (.cost γ::w)=insertionInfinity w := by
  rw [←insertionInfinity_stable w (w.length+1) (by omega)]
  change modeEmbed (w.length+1) (ordinary (.cost γ::w) (w.length+1)).insertion=_
  congr 1
  exact EvenUnitary.cost_insertion _ _ _ _

 
def toggledProbe (β τ : ℝ) (w : List Gate) : List Gate :=
  .mixer (-β):: .cost τ:: .mixer β::w

@[simp] theorem ordinaryLocal_toggledProbe (w : List Gate) (β τ : ℝ)
    (x : SpinSpace ModeInfinity) :
    ordinaryLocal (toggledProbe β τ w) x=
      probe (R β) (-(τ:ℂ) • insertionInfinity (.mixer β::w)) (ordinaryLocal w x) := by
  simp only [toggledProbe,ordinaryLocal_mixer,ordinaryLocal_cost,probe_apply,R_star]

 

theorem modeFock_rotated_insertion (w : List Gate) (β : ℝ) :
    modeFock (insertionInfinity (.mixer β::w))=
      (ordinaryLocal w).symm
        (SpinOperators.act ((R β).conjTranspose*Z*R β) (ordinaryLocal w (vacuum ModeInfinity))) := by
  rw [modeFock_insertion]
  apply (ordinaryLocal (.mixer β::w)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simp only [ordinaryLocal_mixer,SpinOperators.act_mul,ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.apply_symm_apply]
  exact (root_right_inverse (R β) (R_unitary β) _).symm

 
def insertionYInfinity (w : List Gate) : ModeInfinity := insertionInfinity (.mixer (Real.pi/4)::w)

@[simp] theorem modeFock_insertionY (w : List Gate) :
    modeFock (insertionYInfinity w)=
      (ordinaryLocal w).symm (SpinOperators.act Y (ordinaryLocal w (vacuum ModeInfinity))) := by
  rw [insertionYInfinity,modeFock_rotated_insertion,R_quarter_conjugate_Z]

 
theorem rotated_insertion_eq (w : List Gate) (β : ℝ) :
    insertionInfinity (.mixer β::w)=
      (Real.cos (2*β):ℂ) • insertionInfinity w+
        (Real.sin (2*β):ℂ) • insertionYInfinity w := by
  apply modeFock.injective
  rw [map_add,map_smul,map_smul,modeFock_rotated_insertion,modeFock_insertion,
    modeFock_insertionY,R_conjugate_Z]
  change (ordinaryLocal w).symm (SpinOperators.rep (_) (_))=_
  simp only [map_add,map_smul,SpinOperators.rep_apply,add_apply,smul_apply]

end PointedTree

 

open scoped InnerProductSpace Topology
namespace PointedTree
open CoherentFock RootSpin

 
abbrev ShortPulse := ℝ × ℝ

 
def probePrefix (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) : ℕ → List Gate
  | 0 => w
  | k+1 => toggledProbe (a k).1 (r*(a k).2) (probePrefix r w a k)

def actualProbeDirection (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) : ModeInfinity :=
  insertionInfinity (.mixer (a k).1::probePrefix r w a k)

def actualProbe (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) :
    SpinSpace ModeInfinity →L[ℂ] SpinSpace ModeInfinity :=
  probe (R (a k).1) (-((r*(a k).2 : ℝ):ℂ) • actualProbeDirection r w a k)

 
def probeGain (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) :
    SpinSpace ModeInfinity ≃ₗᵢ[ℂ] SpinSpace ModeInfinity :=
  (ordinaryLocal w).symm.trans (ordinaryLocal (probePrefix r w a k))

@[simp] theorem norm_actualProbeDirection (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) :
    ‖actualProbeDirection r w a k‖=1 := norm_insertionInfinity _

@[simp] theorem probeGain_apply (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (x : SpinSpace ModeInfinity) :
    probeGain r w a k x=ordinaryLocal (probePrefix r w a k) ((ordinaryLocal w).symm x) := rfl

@[simp] theorem probeGain_zero (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse)
    (x : SpinSpace ModeInfinity) : probeGain r w a 0 x=x := by
  exact (ordinaryLocal w).apply_symm_apply x

@[simp] theorem probeGain_succ (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (x : SpinSpace ModeInfinity) :
    probeGain r w a (k+1) x=actualProbe r w a k (probeGain r w a k x) := by
  exact ordinaryLocal_toggledProbe (probePrefix r w a k) (a k).1 (r*(a k).2)
    ((ordinaryLocal w).symm x)

 

theorem probeGain_product (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ)
    (x : SpinSpace ModeInfinity) :
    probeGain r w a k x=ProbeProduct.act (actualProbe r w a) (List.range k).reverse x := by
  induction k with
  | zero => simpa only [List.range_zero,List.reverse_nil,ProbeProduct.act_nil] using probeGain_zero r w a x
  | succ k ih =>
    rw [probeGain_succ,ih,List.range_succ,List.reverse_append]
    rfl

 
theorem actual_hermitian_diagonal (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) :
    ⟪actualProbeDirection r w a k,insertionInfinity w⟫_ℂ=
      ⟪SpinOperators.act ((R (a k).1).conjTranspose*Z*R (a k).1)
          (probeGain r w a k (ordinaryLocal w (vacuum ModeInfinity))),
        probeGain r w a k (SpinOperators.act Z (ordinaryLocal w (vacuum ModeInfinity)))⟫_ℂ := by
  rw [←modeFock.inner_map_map]
  change ⟪modeFock (insertionInfinity (.mixer (a k).1::probePrefix r w a k)),
    modeFock (insertionInfinity w)⟫_ℂ=_
  rw [modeFock_rotated_insertion,modeFock_insertion]
  rw [←(ordinaryLocal (probePrefix r w a k)).inner_map_map]
  simp only [LinearIsometryEquiv.apply_symm_apply,probeGain_apply,LinearIsometryEquiv.symm_apply_apply]

 

theorem actual_direction_change_bound (r : ℝ) (w : List Gate) (a : ℕ → ShortPulse) (k : ℕ) :
    ‖actualProbeDirection r w a k-insertionInfinity (.mixer (a k).1::w)‖≤
      ‖probeGain r w a k (ordinaryLocal w (vacuum ModeInfinity))-
          ordinaryLocal w (vacuum ModeInfinity)‖+
      ‖probeGain r w a k (SpinOperators.act ((R (a k).1).conjTranspose*Z*R (a k).1)
          (ordinaryLocal w (vacuum ModeInfinity)))-
        SpinOperators.act ((R (a k).1).conjTranspose*Z*R (a k).1)
          (ordinaryLocal w (vacuum ModeInfinity))‖ := by
  let P := (R (a k).1).conjTranspose*Z*R (a k).1
  have hPu : P ∈ unitary _ := mul_mem (mul_mem (root_adjoint_unitary _ (R_unitary _)) Z_unitary) (R_unitary _)
  have h := ForwardControl.insertion_from_forward
    (ordinaryLocal (probePrefix r w a k)) (ordinaryLocal w) (SpinOperators.act P)
    (fun x => (SpinOperators.norm_act hPu x).le) (vacuum ModeInfinity) 1
  rw [←modeFock.norm_map (actualProbeDirection r w a k-insertionInfinity (.mixer (a k).1::w)),map_sub]
  change ‖modeFock (insertionInfinity (.mixer (a k).1::probePrefix r w a k))-
    modeFock (insertionInfinity (.mixer (a k).1::w))‖≤_
  rw [modeFock_rotated_insertion,modeFock_rotated_insertion]
  simpa only [one_smul,LinearIsometryEquiv.apply_symm_apply,probeGain_apply,
    LinearIsometryEquiv.symm_apply_apply] using h

end PointedTree

namespace ForwardControl
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 
theorem identity_error_split (V : H ≃ₗᵢ[ℂ] H) (o s ρ : H) :
    ‖V (o+s+ρ)-(o+s+ρ)‖≤‖V o-o‖+2*‖s‖+2*‖ρ‖ := by
  have he : V (o+s+ρ)-(o+s+ρ)=(V o-o)+(V s-s)+(V ρ-ρ) := by
    simp only [map_add]
    abel
  rw [he]
  have h1 := norm_add_le (V o-o) (V s-s)
  have h2 := norm_add_le ((V o-o)+(V s-s)) (V ρ-ρ)
  have h3 := norm_sub_le (V s) s
  have h4 := norm_sub_le (V ρ) ρ
  simp only [V.norm_map] at h3 h4
  linarith

 

theorem conjugation_error_split (V : H ≃ₗᵢ[ℂ] H) (P : H →L[ℂ] H)
    (hP : ∀x,‖P x‖≤‖x‖) (o s ρ : H) :
    ‖V (o+s+ρ)-(o+s+ρ)‖+‖V (P (o+s+ρ))-P (o+s+ρ)‖≤
      ‖V o-o‖+‖V (P o)-P o‖+4*‖s‖+4*‖ρ‖ := by
  have h1 := identity_error_split V o s ρ
  have h2 := identity_error_split V (P o) (P s) (P ρ)
  simp only [map_add] at *
  have h3 := hP s
  have h4 := hP ρ
  linarith

end ForwardControl

 

open scoped InnerProductSpace
namespace CoherentFock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
@[simp] theorem spinMass_prePhaseZ (θ : ℝ) (x : PreSpin E) :
    spinMass (prePhaseZ θ x)=spinMass x := by
  simp only [spinMass,prePhaseZ,mass_smul,Complex.norm_exp_ofReal_mul_I,one_mul]

omit [InnerProductSpace ℂ E] in
theorem SpinRadiusLE.prePhaseZ {x : PreSpin E} {B : ℝ} (hx : SpinRadiusLE x B) (θ : ℝ) :
    SpinRadiusLE (prePhaseZ θ x) B := fun i => (hx i).smul _

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem spinMass_preProbePhase (A : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (x : PreSpin E) :
    spinMass (preProbePhase A θ x)≤ matrixMass A.conjTranspose*matrixMass A*spinMass x := by
  unfold preProbePhase
  calc
    _ ≤ matrixMass A.conjTranspose*spinMass (prePhaseZ θ (preRoot A x)) := spinMass_preRoot _ _
    _ = matrixMass A.conjTranspose*spinMass (preRoot A x) := by rw [spinMass_prePhaseZ]
    _ ≤ matrixMass A.conjTranspose*(matrixMass A*spinMass x) :=
      mul_le_mul_of_nonneg_left (spinMass_preRoot _ _) (matrixMass_nonneg _)
    _ = _ := by ring

omit [InnerProductSpace ℂ E] in
theorem SpinRadiusLE.preProbePhase {x : PreSpin E} {B : ℝ} (hx : SpinRadiusLE x B)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) : SpinRadiusLE (preProbePhase A θ x) B :=
  ((hx.preRoot A).prePhaseZ θ).preRoot A.conjTranspose

 

def preCenteredProbe (A : Matrix (Fin 2) (Fin 2) ℂ) (D e : E) (x : PreSpin E) : PreSpin E :=
  preProbePhase A (-2*(⟪D,e⟫_ℂ).im) (preProbe A D x)

@[simp] theorem spinCoe_preCenteredProbe (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (D e : E) (x : PreSpin E) :
    spinCoe (preCenteredProbe A D e x)=spinW (-e) (probe A D (spinW e (spinCoe x))) := by
  rw [preCenteredProbe,spinCoe_preProbePhase,spinCoe_preProbe,centered_toggled_probe A hA]

theorem spinMass_preCenteredProbe (A : Matrix (Fin 2) (Fin 2) ℂ) (D e : E) (x : PreSpin E)
    (M : ℝ) (hM : 0≤M) (hA : matrixMass A≤M) (hAs : matrixMass A.conjTranspose≤M) :
    spinMass (preCenteredProbe A D e x)≤M^4*spinMass x := by
  have h1 := spinMass_preProbePhase A (-2*(⟪D,e⟫_ℂ).im) (preProbe A D x)
  have h2 := spinMass_preProbe A D x
  calc
    _ ≤ matrixMass A.conjTranspose*matrixMass A*spinMass (preProbe A D x) := h1
    _ ≤ M*M*(M*M*spinMass x) := by
      have hm : matrixMass A.conjTranspose*matrixMass A≤M*M :=
        mul_le_mul hAs hA (matrixMass_nonneg _) hM
      exact mul_le_mul hm (h2.trans (mul_le_mul_of_nonneg_right hm (spinMass_nonneg _)))
        (spinMass_nonneg _) (mul_nonneg hM hM)
    _ = _ := by ring

theorem SpinRadiusLE.preCenteredProbe {x : PreSpin E} {B : ℝ} (hx : SpinRadiusLE x B)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (D e : E) :
    SpinRadiusLE (preCenteredProbe A D e x) (‖D‖+B) :=
  (hx.preProbe A D).preProbePhase A _

 

theorem spinCoe_coreCentered {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (D : ι → E) (e : E)
    (hA : ∀j∈l,A j∈unitary _) (x : PreSpin E) :
    spinCoe (ProbeProduct.coreAct (fun j => preCenteredProbe (A j) (D j) e) l x)=
      spinW (-e) (ProbeProduct.act (fun j => probe (A j) (D j)) l (spinW e (spinCoe x))) := by
  induction l with
  | nil => simp [ProbeProduct.coreAct,ProbeProduct.act]
  | cons j l ih =>
    rw [ProbeProduct.coreAct_cons,spinCoe_preCenteredProbe _ (hA j (by simp)),
      ih (fun k hk => hA k (by simp [hk])),spinW_inv',ProbeProduct.act_cons]

 
theorem spinMass_coreCentered {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (D : ι → E) (e : E) (M : ℝ)
    (hM : 0≤M) (hA : ∀j∈l,matrixMass (A j)≤M)
    (hAs : ∀j∈l,matrixMass (A j).conjTranspose≤M) (x : PreSpin E) :
    spinMass (ProbeProduct.coreAct (fun j => preCenteredProbe (A j) (D j) e) l x)≤
      (M^4)^l.length*spinMass x := by
  induction l with
  | nil => simp [ProbeProduct.coreAct]
  | cons j l ih =>
    rw [ProbeProduct.coreAct_cons]
    apply (spinMass_preCenteredProbe _ _ _ _ M hM (hA j (by simp)) (hAs j (by simp))).trans
    calc
      _ ≤ M^4*((M^4)^l.length*spinMass x) := mul_le_mul_of_nonneg_left
        (ih (fun k hk => hA k (by simp [hk])) (fun k hk => hAs k (by simp [hk]))) (by positivity)
      _ = _ := by simp only [List.length_cons,pow_succ]; ring

 
theorem radius_coreCentered {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (D : ι → E) (e : E) (B L : ℝ)
    (hD : ∀j∈l,‖D j‖≤L) (x : PreSpin E) (hx : SpinRadiusLE x B) :
    SpinRadiusLE (ProbeProduct.coreAct (fun j => preCenteredProbe (A j) (D j) e) l x)
      (B+l.length*L) := by
  induction l with
  | nil => simpa [ProbeProduct.coreAct] using hx
  | cons j l ih =>
    rw [ProbeProduct.coreAct_cons]
    have hh := (ih (fun k hk => hD k (by simp [hk]))).preCenteredProbe (A j) (D j) e
    intro i
    apply (hh i).mono
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    have h := hD j (by simp)
    linarith

end CoherentFock

namespace RootSpin
open CoherentFock

theorem matrixMass_R_le (β : ℝ) : matrixMass (R β)≤4 := by
  have hc : |Real.cos β|≤1 := abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hs : |Real.sin β|≤1 := abs_le.mpr ⟨Real.neg_one_le_sin _,Real.sin_le_one _⟩
  simp only [matrixMass,Fin.sum_univ_two,R_apply]
  norm_num [norm_mul,Real.norm_eq_abs,-Complex.ofReal_cos,-Complex.ofReal_sin]
  linarith

end RootSpin

end

end OAI
