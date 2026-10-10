import Mathlib
import OAI.Probability.ParisiFinite.PacketRegular

namespace OAI

/-! Space. -/

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
namespace HilbertPair
variable {E F G K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev Space (E F : Type*) := WithLp 2 (E × F)

def inl : E →ₗᵢ[ℂ] Space E F := LinearMap.isometryOfInner
  ((WithLp.linearEquiv 2 ℂ (E × F)).symm.toLinearMap.comp (LinearMap.inl ℂ E F))
  (by intro x y; simp)

def inr : F →ₗᵢ[ℂ] Space E F := LinearMap.isometryOfInner
  ((WithLp.linearEquiv 2 ℂ (E × F)).symm.toLinearMap.comp (LinearMap.inr ℂ E F))
  (by intro x y; simp)

@[simp] theorem inl_apply (x : E) : (inl x : Space E F)=WithLp.toLp 2 (x,0) := rfl
@[simp] theorem inr_apply (x : F) : (inr x : Space E F)=WithLp.toLp 2 (0,x) := rfl
@[simp] theorem inl_inner_inr (x : E) (y : F) : ⟪(inl x:Space E F),inr y⟫_ℂ=0 := by simp
@[simp] theorem inr_inner_inl (y : F) (x : E) : ⟪(inr y:Space E F),inl x⟫_ℂ=0 := by simp

@[simp] theorem inl_add_inr (x : Space E F) : inl x.fst + inr x.snd=x := by
  apply WithLp.ofLp_injective 2
  change (x.ofLp.1+0,0+x.ofLp.2)=x.ofLp
  simp only [add_zero,zero_add,Prod.mk.eta]

def map (T : E →ₗᵢ[ℂ] G) (U : F →ₗᵢ[ℂ] K) : Space E F →ₗᵢ[ℂ] Space G K :=
  LinearMap.isometryOfInner
    (((WithLp.linearEquiv 2 ℂ (G × K)).symm.toLinearMap.comp
      (T.toLinearMap.prodMap U.toLinearMap)).comp (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap)
    (by intro x y; simp)

@[simp] theorem map_apply (T : E →ₗᵢ[ℂ] G) (U : F →ₗᵢ[ℂ] K) (x : Space E F) :
    map T U x=WithLp.toLp 2 (T x.fst,U x.snd) := rfl

@[simp] theorem map_inl (T : E →ₗᵢ[ℂ] G) (U : F →ₗᵢ[ℂ] K) (x : E) :
    map T U (inl x)=inl (T x) := by simp

@[simp] theorem map_inr (T : E →ₗᵢ[ℂ] G) (U : F →ₗᵢ[ℂ] K) (x : F) :
    map T U (inr x)=inr (U x) := by simp

def congr (T : E ≃ₗᵢ[ℂ] G) (U : F ≃ₗᵢ[ℂ] K) : Space E F ≃ₗᵢ[ℂ] Space G K where
  toFun := map T.toLinearIsometry U.toLinearIsometry
  invFun := map T.symm.toLinearIsometry U.symm.toLinearIsometry
  left_inv x := by
    apply WithLp.ofLp_injective 2
    change (T.symm (T x.ofLp.1),U.symm (U x.ofLp.2))=x.ofLp
    rw [T.symm_apply_apply,U.symm_apply_apply]
  right_inv x := by
    apply WithLp.ofLp_injective 2
    change (T (T.symm x.ofLp.1),U (U.symm x.ofLp.2))=x.ofLp
    rw [T.apply_symm_apply,U.apply_symm_apply]
  map_add' := (map T.toLinearIsometry U.toLinearIsometry).map_add
  map_smul' := (map T.toLinearIsometry U.toLinearIsometry).map_smul
  norm_map' := (map T.toLinearIsometry U.toLinearIsometry).norm_map

@[simp] theorem congr_apply (T : E ≃ₗᵢ[ℂ] G) (U : F ≃ₗᵢ[ℂ] K) (x : Space E F) :
    congr T U x=WithLp.toLp 2 (T x.fst,U x.snd) := rfl

end HilbertPair

 

namespace SeededTree
open PointedTree CoherentFock RootSpin

abbrev External := EuclideanSpace ℂ (Fin 2)
abbrev gaussianNode (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : PointedData where
  Carrier := SpinSpace E
  vac := vacuum E
  norm_vac := norm_vacuum

abbrev base : PointedData := gaussianNode External
abbrev next (H : PointedData) : PointedData := gaussianNode (HilbertPair.Space External (centered H))

abbrev centeredData (A : PointedData) : HilbertData where
  Carrier := centered A

abbrev pairData (A B : HilbertData) : HilbertData where
  Carrier := HilbertPair.Space A B

abbrev nextTop (H : HilbertData) : HilbertData :=
  pairData { Carrier := External } (centeredData (gaussianNode H))

@[reducible] def topData : ℕ → HilbertData
  | 0 => { Carrier := External }
  | n+1 => nextTop (topData n)
abbrev TopMode (n : ℕ) := (topData n).Carrier
abbrev level (n : ℕ) : PointedData := gaussianNode (TopMode n)
abbrev Level (n : ℕ) : Type := (level n).Carrier
abbrev Mode (n : ℕ) := centered (level n)
def vac (n : ℕ) : Level n := (level n).vac
@[simp] theorem norm_vac (n : ℕ) : ‖vac n‖=1 := (level n).norm_vac

 
def gaussianMap {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (T : E →ₗᵢ[ℂ] F) :
    PointedMap (gaussianNode E) (gaussianNode F) where
  toLinearIsometry := spinMap (gammaEmbedding T)
  map_vac := by ext i; simp [vacuum_apply]

def nextMap {H K : PointedData} (T : PointedMap H K) : PointedMap (next H) (next K) :=
  gaussianMap (HilbertPair.map LinearIsometry.id (centeredMap T))

def empty : (n : ℕ) → PointedMap (level n) (level (n+1))
  | 0 => gaussianMap HilbertPair.inl
  | n+1 => nextMap (empty n)

@[simp] theorem empty_vac (n : ℕ) : (empty n).toLinearIsometry (vac n)=vac (n+1) :=
  (empty n).map_vac

def topStep : (n : ℕ) → TopMode n →ₗᵢ[ℂ] TopMode (n+1)
  | 0 => HilbertPair.inl
  | n+1 => HilbertPair.map LinearIsometry.id (centeredMap (empty n))

@[simp] theorem empty_apply (n : ℕ) (x : Level n) :
    (empty n).toLinearIsometry x=spinMap (gammaEmbedding (topStep n)) x := by cases n <;> rfl

def external : (n : ℕ) → External →ₗᵢ[ℂ] TopMode n
  | 0 => LinearIsometry.id
  | _+1 => HilbertPair.inl

def endogenous (n : ℕ) : Mode n →ₗᵢ[ℂ] TopMode (n+1) := HilbertPair.inr

@[simp] theorem topStep_external (n : ℕ) (e : External) :
    topStep n (external n e)=external (n+1) e := by
  cases n with
  | zero => rfl
  | succ n => exact HilbertPair.map_inl LinearIsometry.id (centeredMap (empty n)) e

@[simp] theorem topStep_endogenous (n : ℕ) (d : Mode n) :
    topStep (n+1) (endogenous n d)=endogenous (n+1) (centeredMap (empty n) d) := by
  exact HilbertPair.map_inr LinearIsometry.id (centeredMap (empty n)) d

@[simp] theorem external_inner_endogenous (n : ℕ) (e : External) (d : Mode n) :
    ⟪external (n+1) e,endogenous n d⟫_ℂ=0 := HilbertPair.inl_inner_inr e d

 
def gaussianSymmetry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E ≃ₗᵢ[ℂ] E) (hT : Function.Involutive T) : Symmetry (gaussianNode E) where
  op := (spinEquiv (secondQuantization T)).trans (SpinOperators.actEquiv X X_unitary)
  invariant := by
    change SpinOperators.act X (spinEquiv (secondQuantization T) (vacuum E))=vacuum E
    ext i
    fin_cases i <;> simp [vacuum_apply,secondQuantization,X]
  square x := by
    change SpinOperators.act X (spinMap (gammaEmbedding T.toLinearIsometry)
      (SpinOperators.act X (spinMap (gammaEmbedding T.toLinearIsometry) x)))=x
    apply spinFlip_twice
    intro y
    have hc : T.toLinearIsometry.comp T.toLinearIsometry=LinearIsometry.id := by
      ext v
      exact hT v
    have h := congrArg (fun A => A y) (Gamma_comp T.toLinearIsometry T.toLinearIsometry)
    change Gamma T.toLinearIsometry (Gamma T.toLinearIsometry y)=y
    simpa [hc] using h

def externalFlip : External ≃ₗᵢ[ℂ] External := LinearIsometryEquiv.neg ℂ
@[simp] theorem externalFlip_apply (e : External) : externalFlip e=-e := rfl

def nextSymmetry {H : PointedData} (S : Symmetry H) : Symmetry (next H) :=
  gaussianSymmetry (HilbertPair.congr externalFlip S.centered) (by
    intro x
    apply WithLp.ofLp_injective 2
    change (-(-x.ofLp.1),S.centered (S.centered x.ofLp.2))=x.ofLp
    rw [neg_neg,S.centered_square])

def symmetry : (n : ℕ) → Symmetry (level n)
  | 0 => gaussianSymmetry externalFlip (fun e => neg_neg e)
  | n+1 => nextSymmetry (symmetry n)

def topFlip : (n : ℕ) → TopMode n ≃ₗᵢ[ℂ] TopMode n
  | 0 => externalFlip
  | n+1 => HilbertPair.congr externalFlip (symmetry n).centered

@[simp] theorem symmetry_apply (n : ℕ) (x : Level n) : (symmetry n).op x=
    SpinOperators.act X (spinMap (gammaEmbedding (topFlip n).toLinearIsometry) x) := by cases n <;> rfl

@[simp] theorem topFlip_external (n : ℕ) (e : External) :
    topFlip n (external n e)=-external n e := by
  cases n with
  | zero => rfl
  | succ n =>
    change HilbertPair.map externalFlip.toLinearIsometry (symmetry n).centered.toLinearIsometry
      (HilbertPair.inl e)=-(HilbertPair.inl e : TopMode (n+1))
    rw [HilbertPair.map_inl]
    change (HilbertPair.inl (-e) : TopMode (n+1))=-HilbertPair.inl e
    exact (HilbertPair.inl : External →ₗᵢ[ℂ] TopMode (n+1)).map_neg e

@[simp] theorem topFlip_endogenous (n : ℕ) (d : Mode n) :
    topFlip (n+1) (endogenous n d)=endogenous n ((symmetry n).centered d) := by
  change HilbertPair.map externalFlip.toLinearIsometry (symmetry n).centered.toLinearIsometry
    (HilbertPair.inr d)=HilbertPair.inr ((symmetry n).centered d)
  exact HilbertPair.map_inr _ _ d

@[simp] theorem symmetry_vac (n : ℕ) : (symmetry n).op (vac n)=vac n := (symmetry n).invariant

def root (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) : Level n →L[ℂ] Level n :=
  SpinOperators.act A
@[simp] theorem root_apply (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Level n) :
    root n A x=SpinOperators.act A x := by cases n <;> rfl

@[simp] theorem symmetry_rootZ (n : ℕ) (x : Level n) :
    (symmetry n).op (root n Z x)=-root n Z ((symmetry n).op x) := by
  rw [SeededTree.symmetry_apply,SeededTree.symmetry_apply]
  change SpinOperators.act X (spinMap (gammaEmbedding (topFlip n).toLinearIsometry) (SpinOperators.act Z x))=
    -SpinOperators.act Z (SpinOperators.act X (spinMap (gammaEmbedding (topFlip n).toLinearIsometry) x))
  exact flipMap_rootZ (gammaEmbedding (topFlip n).toLinearIsometry) x

@[simp] theorem symmetry_rootR (n : ℕ) (t : ℝ) (x : Level n) :
    (symmetry n).op (root n (R t) x)=root n (R t) ((symmetry n).op x) := by
  rw [SeededTree.symmetry_apply,SeededTree.symmetry_apply]
  change SpinOperators.act X (spinMap (gammaEmbedding (topFlip n).toLinearIsometry) (SpinOperators.act (R t) x))=
    SpinOperators.act (R t) (SpinOperators.act X (spinMap (gammaEmbedding (topFlip n).toLinearIsometry) x))
  exact flipMap_rootR (gammaEmbedding (topFlip n).toLinearIsometry) t x

def rootEquiv (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) : Level n ≃ₗᵢ[ℂ] Level n :=
  SpinOperators.actEquiv A hA
@[simp] theorem rootEquiv_apply (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) (x : Level n) :
    rootEquiv n A hA x=root n A x := by cases n <;> rfl
@[simp] theorem norm_rootZ (n : ℕ) (x : Level n) : ‖root n Z x‖=‖x‖ := by
  simpa only [rootEquiv_apply] using (rootEquiv n Z Z_unitary).norm_map x

structure EvenUnitary (n : ℕ) where
  op : Level n ≃ₗᵢ[ℂ] Level n
  commutes : ∀x, (symmetry n).op (op x)=op ((symmetry n).op x)

namespace EvenUnitary

def ident (n : ℕ) : EvenUnitary n where
  op := LinearIsometryEquiv.refl ℂ (Level n)
  commutes _ := rfl

def followedBy {n : ℕ} (U V : EvenUnitary n) : EvenUnitary n where
  op := U.op.trans V.op
  commutes x := by
    change (symmetry n).op (V.op (U.op x))=V.op (U.op ((symmetry n).op x))
    rw [V.commutes,U.commutes]

theorem symm_commutes {n : ℕ} (U : EvenUnitary n) (x : Level n) :
    (symmetry n).op (U.op.symm x)=U.op.symm ((symmetry n).op x) := by
  apply U.op.injective
  rw [← U.commutes,U.op.apply_symm_apply,U.op.apply_symm_apply]

def insertion {n : ℕ} (U : EvenUnitary n) : Mode n :=
  ⟨U.op.symm (root n Z (U.op (vac n))),by
    apply odd_centered (symmetry n)
    rw [U.symm_commutes,symmetry_rootZ,U.commutes,symmetry_vac,map_neg]⟩
@[simp] theorem insertion_coe {n : ℕ} (U : EvenUnitary n) :
    (U.insertion:Level n)=U.op.symm (root n Z (U.op (vac n))) := rfl
@[simp] theorem norm_insertion {n : ℕ} (U : EvenUnitary n) : ‖U.insertion‖=1 := by
  change ‖U.op.symm (root n Z (U.op (vac n)))‖=1
  rw [U.op.symm.norm_map,norm_rootZ,U.op.norm_map,norm_vac]
@[simp] theorem insertion_odd {n : ℕ} (U : EvenUnitary n) :
    (symmetry n).centered U.insertion=-U.insertion := by
  apply Subtype.ext
  change (symmetry n).op (U.op.symm (root n Z (U.op (vac n))))=-U.op.symm (root n Z (U.op (vac n)))
  rw [U.symm_commutes,symmetry_rootZ,U.commutes,symmetry_vac,map_neg]

def mixer (n : ℕ) (t : ℝ) : EvenUnitary n where
  op := rootEquiv n (R t) (R_unitary t)
  commutes x := by simpa only [rootEquiv_apply] using symmetry_rootR n t x

def pulse (n : ℕ) (d : TopMode n) (hd : topFlip n d=-d) : EvenUnitary n where
  op := costEquiv d
  commutes x := by
    change (symmetry n).op (WZ d x)=WZ d ((symmetry n).op x)
    rw [symmetry_apply,symmetry_apply]
    change (topFlip n).toLinearIsometry d=-d at hd
    rw [spinMap_cost,hd]
    exact congrArg (fun A : SpinSpace (TopMode n) →L[ℂ] SpinSpace (TopMode n) =>
      A (spinMap (gammaEmbedding (topFlip n).toLinearIsometry) x)) (WZ_rootX d).symm

@[simp] theorem pulse_apply (n : ℕ) (d : TopMode n) (hd : topFlip n d=-d) (x : Level n) :
    (pulse n d hd).op x=WZ d x := by cases n <;> rfl

 
def seed (n : ℕ) (a : Fin 2 → ℝ) : EvenUnitary n :=
  pulse n (external n (WithLp.toLp 2 (fun j => -(a j:ℂ)))) (topFlip_external n _)

def cost (n : ℕ) (U : EvenUnitary n) (t : ℝ) : EvenUnitary (n+1) :=
  pulse (n+1) (-(t:ℂ) • endogenous n U.insertion) (by
    rw [map_smul,topFlip_endogenous,U.insertion_odd,map_neg,smul_neg,neg_smul])

end EvenUnitary
end SeededTree

namespace SeededTree
open PointedTree CoherentFock RootSpin

@[simp] theorem root_empty (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Level n) :
    (empty n).toLinearIsometry (root n A x)=root (n+1) A ((empty n).toLinearIsometry x) := by
  rw [SeededTree.empty_apply,SeededTree.empty_apply]
  exact spinMap_root (gammaEmbedding (topStep n)) A x

@[simp] theorem pulse_empty (n : ℕ) (d : TopMode n) (x : Level n) :
    (empty n).toLinearIsometry (WZ d x)=WZ (topStep n d) ((empty n).toLinearIsometry x) := by
  rw [SeededTree.empty_apply,SeededTree.empty_apply]
  exact spinMap_cost (topStep n) d x

namespace EvenUnitary

def Compatible {n : ℕ} (U : SeededTree.EvenUnitary n) (V : SeededTree.EvenUnitary (n+1)) : Prop :=
  ∀x, (empty n).toLinearIsometry (U.op x)=V.op ((empty n).toLinearIsometry x)

theorem Compatible.symm_apply {n : ℕ} {U : SeededTree.EvenUnitary n} {V : SeededTree.EvenUnitary (n+1)}
    (h : Compatible U V) (x : Level n) :
    (empty n).toLinearIsometry (U.op.symm x)=V.op.symm ((empty n).toLinearIsometry x) := by
  apply V.op.injective
  rw [←h,U.op.apply_symm_apply,V.op.apply_symm_apply]

theorem Compatible.insertion {n : ℕ} {U : SeededTree.EvenUnitary n} {V : SeededTree.EvenUnitary (n+1)}
    (h : Compatible U V) : centeredMap (empty n) U.insertion=V.insertion := by
  apply Subtype.ext
  change (empty n).toLinearIsometry (U.op.symm (root n Z (U.op (vac n))))=
    V.op.symm (root (n+1) Z (V.op (vac (n+1))))
  rw [h.symm_apply,root_empty,h,empty_vac]

theorem Compatible.followedBy {n : ℕ} {U₀ V₀ : SeededTree.EvenUnitary n}
    {U₁ V₁ : SeededTree.EvenUnitary (n+1)} (hU : Compatible U₀ U₁) (hV : Compatible V₀ V₁) :
    Compatible (U₀.followedBy V₀) (U₁.followedBy V₁) := by
  intro x
  change (empty n).toLinearIsometry (V₀.op (U₀.op x))=V₁.op (U₁.op ((empty n).toLinearIsometry x))
  rw [hV,hU]

theorem compatible_ident (n : ℕ) : Compatible (ident n) (ident (n+1)) := fun _ => rfl

theorem compatible_mixer (n : ℕ) (t : ℝ) : Compatible (mixer n t) (mixer (n+1) t) := by
  intro x
  change (empty n).toLinearIsometry (root n (R t) x)=root (n+1) (R t) ((empty n).toLinearIsometry x)
  exact root_empty n _ x

theorem compatible_pulse (n : ℕ) (d : TopMode n) (e : TopMode (n+1))
    (hd : topFlip n d=-d) (he : topFlip (n+1) e=-e) (h : topStep n d=e) :
    Compatible (pulse n d hd) (pulse (n+1) e he) := by
  intro x
  change (empty n).toLinearIsometry (WZ d x)=WZ e ((empty n).toLinearIsometry x)
  rw [SeededTree.pulse_empty,h]

theorem compatible_seed (n : ℕ) (a : Fin 2 → ℝ) : Compatible (seed n a) (seed (n+1) a) :=
  compatible_pulse n _ _ _ _ (topStep_external n _)

theorem compatible_cost (n : ℕ) (U : SeededTree.EvenUnitary n) (V : SeededTree.EvenUnitary (n+1))
    (h : Compatible U V) (t : ℝ) : Compatible (cost n U t) (cost (n+1) V t) := by
  apply compatible_pulse
  rw [map_smul,topStep_endogenous,h.insertion]

 
theorem pulse_insertion (n : ℕ) (U : SeededTree.EvenUnitary n) (d : TopMode n)
    (hd : topFlip n d=-d) : (U.followedBy (pulse n d hd)).insertion=U.insertion := by
  apply Subtype.ext
  change U.op.symm ((costEquiv d).symm (SpinOperators.act Z (costEquiv d (U.op (vac n)))))=
    U.op.symm (SpinOperators.act Z (U.op (vac n)))
  congr 1
  apply (costEquiv d).injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (fun A : SpinSpace (TopMode n) →L[ℂ] SpinSpace (TopMode n) => A (U.op (vac n)))
    (WZ_rootZ d).symm

end EvenUnitary

 
inductive Gate
  | mixer (beta : ℝ)
  | cost (gamma : ℝ)
  | seed (angles : Fin 2 → ℝ)

 
def circuit : List Gate → (n : ℕ) → SeededTree.EvenUnitary n
  | [], n => EvenUnitary.ident n
  | Gate.mixer beta :: w, n => (circuit w n).followedBy (EvenUnitary.mixer n beta)
  | Gate.seed a :: w, n => (circuit w n).followedBy (EvenUnitary.seed n a)
  | Gate.cost _ :: w, 0 => circuit w 0
  | Gate.cost gamma :: w, n+1 => (circuit w (n+1)).followedBy (EvenUnitary.cost n (circuit w n) gamma)

theorem circuit_compatible (w : List Gate) (n : ℕ) (hn : w.length ≤ n) :
    EvenUnitary.Compatible (circuit w n) (circuit w (n+1)) := by
  induction w generalizing n with
  | nil => exact EvenUnitary.compatible_ident n
  | cons g w ih =>
    cases g with
    | mixer beta =>
      exact (ih n (by simpa using le_trans (Nat.le_succ w.length) hn)).followedBy
        (EvenUnitary.compatible_mixer n beta)
    | seed a =>
      exact (ih n (by simpa using le_trans (Nat.le_succ w.length) hn)).followedBy
        (EvenUnitary.compatible_seed n a)
    | cost gamma =>
      cases n with
      | zero => simp at hn
      | succ n =>
        have hn' : w.length ≤ n := by simpa using hn
        exact (ih (n+1) (hn'.trans (Nat.le_succ n))).followedBy
          (EvenUnitary.compatible_cost n _ _ (ih n hn') gamma)

@[simp] theorem circuit_insertion_empty (w : List Gate) (n : ℕ) (hn : w.length ≤ n) :
    centeredMap (empty n) (circuit w n).insertion=(circuit w (n+1)).insertion :=
  (circuit_compatible w n hn).insertion

 

def rootShift (n : ℕ) : Mode n →ₗᵢ[ℂ] Mode (n+1) where
  toFun d := ⟨plusEmbedding (creationVacuum (endogenous n d)),by
    rw [mem_centered]
    change ⟪plusEmbedding (coherent (0:TopMode (n+1))),plusEmbedding (creationVacuum (endogenous n d))⟫_ℂ=0
    exact (plusEmbedding.inner_map_map (coherent (0:TopMode (n+1)))
      (creationVacuum (endogenous n d))).trans (creationVacuum_orthogonal (endogenous n d))⟩
  map_add' d e := by
    apply Subtype.ext
    change plusEmbedding (creationEmbedding (endogenous n (d+e)))=
      plusEmbedding (creationEmbedding (endogenous n d))+plusEmbedding (creationEmbedding (endogenous n e))
    simp only [map_add]
  map_smul' z d := by
    apply Subtype.ext
    change plusEmbedding (creationEmbedding (endogenous n (z • d)))=
      z • plusEmbedding (creationEmbedding (endogenous n d))
    simp only [map_smul]
  norm_map' d := by
    exact (plusEmbedding.norm_map _).trans ((norm_creationVacuum _).trans ((endogenous n).norm_map d))

@[simp] theorem rootShift_coe (n : ℕ) (d : Mode n) :
    (rootShift n d : Level (n+1))=plusEmbedding (creationVacuum (endogenous n d)) := rfl

@[simp] theorem rootShift_empty (n : ℕ) (d : Mode n) :
    centeredMap (empty (n+1)) (rootShift n d)=rootShift (n+1) (centeredMap (empty n) d) := by
  apply Subtype.ext
  change (empty (n+1)).toLinearIsometry (plusEmbedding (creationVacuum (endogenous n d)))=
    plusEmbedding (creationVacuum (endogenous (n+1) (centeredMap (empty n) d)))
  rw [empty_apply,spinMap_plusEmbedding]
  change plusEmbedding (Gamma (topStep (n+1)) (creationVacuum (endogenous n d)))=_
  rw [Gamma_creationVacuum,topStep_endogenous]

def treeEnergy (n : ℕ) (d : Mode n) : ℝ := (⟪centeredMap (empty n) d,rootShift n d⟫_ℂ).re

@[simp] theorem treeEnergy_empty (n : ℕ) (d : Mode n) :
    treeEnergy (n+1) (centeredMap (empty n) d)=treeEnergy n d := by
  unfold treeEnergy
  rw [←rootShift_empty]
  exact congrArg Complex.re ((centeredMap (empty (n+1))).inner_map_map _ _)

theorem abs_treeEnergy_le (n : ℕ) (d : Mode n) : |treeEnergy n d| ≤ ‖d‖^2 := by
  calc
    _ ≤ ‖⟪centeredMap (empty n) d,rootShift n d⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖centeredMap (empty n) d‖*‖rootShift n d‖ := norm_inner_le_norm _ _
    _ = ‖d‖^2 := by rw [(centeredMap (empty n)).norm_map,(rootShift n).norm_map]; ring

def value (w : List Gate) : ℝ := treeEnergy w.length (circuit w w.length).insertion

theorem value_eq_height (w : List Gate) (n : ℕ) (hn : w.length ≤ n) :
    value w=treeEnergy n (circuit w n).insertion := by
  induction n,hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [←circuit_insertion_empty w n hn,treeEnergy_empty,←ih]

theorem abs_value_le (w : List Gate) : |value w| ≤ 1 := by
  exact (abs_treeEnergy_le _ _).trans_eq (by rw [EvenUnitary.norm_insertion,one_pow])

end SeededTree

namespace CoherentFock
open PointedTree Complex
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}

 
def PacketForm (x : X) (D : (X → E) → Prop) (v : X → SpinSpace E) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : X → ι → Fin 2 → ℂ) (d : X → ι → E),
    (∀i q, AnalyticAt ℝ (fun t => a t i q) x) ∧
    (∀i, D (fun t => d t i)) ∧ (∀t, v t=spinPacket (a t) (d t))

namespace PacketForm
variable {D : (X → E) → Prop}

theorem inner (hD : ∀d e, D d → D e → AnalyticAt ℝ (fun t => ⟪d t,e t⟫_ℂ) x)
    {v w : X → SpinSpace E} (hv : PacketForm x D v) (hw : PacketForm x D w) :
    AnalyticAt ℝ (fun t => ⟪v t,w t⟫_ℂ) x := by
  obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
  obtain ⟨κ,hk,b,e,hb,he,hw⟩ := hw
  let := hi
  let := hk
  simp_rw [hv,hw]
  exact analyticAt_inner_spinPacket a b d e ha hb
    (fun i => hD _ _ (hd i) (hd i)) (fun j => hD _ _ (he j) (he j))
    (fun i j => hD _ _ (hd i) (he j))

theorem zero : PacketForm x D (fun _ => 0) := by
  refine ⟨Fin 0,inferInstance,fun _ i => Fin.elim0 i,fun _ i => Fin.elim0 i,?_,?_,?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro t; simp [spinPacket]

theorem add {v w : X → SpinSpace E} (hv : PacketForm x D v) (hw : PacketForm x D w) :
    PacketForm x D (fun t => v t+w t) := by
  obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
  obtain ⟨κ,hk,b,e,hb,he,hw⟩ := hw
  let := hi
  let := hk
  refine ⟨Sum ι κ,inferInstance,fun t => Sum.elim (a t) (b t),
    fun t => Sum.elim (d t) (e t),?_,?_,?_⟩
  · intro i q; cases i with
    | inl i => exact ha i q
    | inr j => exact hb j q
  · intro i; cases i with
    | inl i => exact hd i
    | inr j => exact he j
  · intro t; dsimp only; rw [hv,hw,spinPacket_sum]

theorem smul {v : X → SpinSpace E} {z : X → ℂ}
    (hz : AnalyticAt ℝ z x) (hv : PacketForm x D v) :
    PacketForm x D (fun t => z t • v t) := by
  obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
  let := hi
  refine ⟨ι,hi,fun t i q => z t*a t i q,d,fun i q => hz.mul (ha i q),hd,?_⟩
  intro t
  dsimp only
  rw [hv,spinPacket_smul]

theorem neg {v : X → SpinSpace E} (hv : PacketForm x D v) :
    PacketForm x D (fun t => -v t) := by
  simpa using smul (show AnalyticAt ℝ (fun _ : X => (-1:ℂ)) x from analyticAt_const) hv

theorem vacuum (h0 : D (fun _ => 0)) : PacketForm x D (fun _ => PointedTree.vacuum E) := by
  refine ⟨Unit,inferInstance,fun _ _ _ => spinCoefficient,fun _ _ => 0,
    fun _ _ => analyticAt_const,fun _ => h0,?_⟩
  intro t
  ext q
  simp only [spinPacket_apply,Fintype.sum_unique]
  rfl

theorem root {v : X → SpinSpace E} {A : X → Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀i j, AnalyticAt ℝ (fun t => A t i j) x) (hv : PacketForm x D v) :
    PacketForm x D (fun t => SpinOperators.act (A t) (v t)) := by
  obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
  let := hi
  refine ⟨ι,hi,fun t i q => ∑j, A t q j * a t i j,d,?_,hd,?_⟩
  · intro i q
    apply Finset.analyticAt_fun_sum
    intro j hj
    exact (hA q j).mul (ha i j)
  · intro t
    dsimp only
    rw [hv,act_spinPacket]

theorem pulse
    (hD : ∀d e, D d → D e → AnalyticAt ℝ (fun t => ⟪d t,e t⟫_ℂ) x)
    (hadd : ∀d e, D d → D e → D (fun t => d t+e t))
    (hneg : ∀d, D d → D (fun t => -d t))
    {v : X → SpinSpace E} {h : X → E} (hh : D h) (hv : PacketForm x D v) :
    PacketForm x D (fun t => WZ (h t) (v t)) := by
  classical
  obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
  let := hi
  refine ⟨ι×Fin 2,inferInstance,
    fun t p q => if q=p.2 then phase (if p.2=0 then h t else -h t) (d t p.1)*a t p.1 q else 0,
    fun t p => (if p.2=0 then h t else -h t)+d t p.1,?_,?_,?_⟩
  · intro p q
    by_cases hqp : q=p.2
    · simp only [hqp,ite_true]
      apply AnalyticAt.mul _ (ha p.1 p.2)
      apply analyticAt_phase_of_gram
      have hgram := hD _ _ hh (hd p.1)
      by_cases hp : p.2=0
      · simpa only [hp,ite_true] using hgram
      · simpa only [hp,ite_false,inner_neg_left] using hgram.fun_neg
    · simp only [hqp,ite_false]
      exact analyticAt_const
  · intro p
    by_cases hp : p.2=0
    · simpa only [hp,ite_true] using hadd _ _ hh (hd p.1)
    · simpa only [hp,ite_false] using hadd _ _ (hneg _ hh) (hd p.1)
  · intro t
    dsimp only
    rw [hv,WZ_spinPacket]

end PacketForm
end CoherentFock

namespace SeededTree
open CoherentFock Complex RootSpin PointedTree
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

 

def TopRegular (x : X) : (n : ℕ) → (X → TopMode n) → Prop
  | 0,d => ∀q, AnalyticAt ℝ (fun t => d t q) x
  | n+1,d => (∀q, AnalyticAt ℝ (fun t => (d t).fst q) x) ∧
      PacketForm x (TopRegular x n) (fun t => ((d t).snd : Level n))

def PacketRegular (x : X) (n : ℕ) (v : X → Level n) : Prop := PacketForm x (TopRegular x n) v

namespace TopRegular
variable {x : X}

theorem inner : ∀ (n : ℕ) {d e : X → TopMode n},
    TopRegular x n d → TopRegular x n e →
    AnalyticAt ℝ (fun t => ⟪d t,e t⟫_ℂ) x := by
  intro n
  induction n with
  | zero =>
    intro d e hd he
    change AnalyticAt ℝ (fun t => ∑q : Fin 2, ⟪d t q,e t q⟫_ℂ) x
    apply Finset.analyticAt_fun_sum
    intro q hq
    simp only [RCLike.inner_apply]
    exact (he q).mul ((Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (hd q))
  | succ n ih =>
    intro d e hd he
    change AnalyticAt ℝ (fun t => ⟪(d t).fst,(e t).fst⟫_ℂ+⟪(d t).snd,(e t).snd⟫_ℂ) x
    apply AnalyticAt.add
    · change AnalyticAt ℝ (fun t => ∑q : Fin 2, ⟪(d t).fst q,(e t).fst q⟫_ℂ) x
      apply Finset.analyticAt_fun_sum
      intro q hq
      simp only [RCLike.inner_apply]
      exact (he.1 q).mul ((Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (hd.1 q))
    · exact PacketForm.inner (fun _ _ => ih) hd.2 he.2

theorem zero (n : ℕ) : TopRegular x n (fun _ => 0) := by
  cases n with
  | zero => exact fun _ => analyticAt_const
  | succ n => exact ⟨fun _ => analyticAt_const,PacketForm.zero⟩

theorem add (n : ℕ) {d e : X → TopMode n} (hd : TopRegular x n d) (he : TopRegular x n e) :
    TopRegular x n (fun t => d t+e t) := by
  cases n with
  | zero => exact fun q => (hd q).add (he q)
  | succ n => exact ⟨fun q => (hd.1 q).add (he.1 q),PacketForm.add hd.2 he.2⟩

theorem smul (n : ℕ) {d : X → TopMode n} {z : X → ℂ}
    (hz : AnalyticAt ℝ z x) (hd : TopRegular x n d) :
    TopRegular x n (fun t => z t • d t) := by
  cases n with
  | zero => exact fun q => hz.mul (hd q)
  | succ n => exact ⟨fun q => hz.mul (hd.1 q),PacketForm.smul hz hd.2⟩

theorem neg (n : ℕ) {d : X → TopMode n} (hd : TopRegular x n d) :
    TopRegular x n (fun t => -d t) := by
  simpa using smul n (show AnalyticAt ℝ (fun _ : X => (-1:ℂ)) x from analyticAt_const) hd

theorem external (n : ℕ) (e : X → External) (he : ∀q, AnalyticAt ℝ (fun t => e t q) x) :
    TopRegular x n (fun t => SeededTree.external n (e t)) := by
  cases n with
  | zero => exact he
  | succ n => exact ⟨he,PacketForm.zero⟩

theorem endogenous (n : ℕ) (d : X → Mode n)
    (hd : PacketRegular x n (fun t => (d t:Level n))) :
    TopRegular x (n+1) (fun t => SeededTree.endogenous n (d t)) :=
  ⟨fun _ => analyticAt_const,hd⟩

end TopRegular

namespace PacketRegular
variable {x : X}

theorem inner (n : ℕ) {v w : X → Level n}
    (hv : PacketRegular x n v) (hw : PacketRegular x n w) :
    AnalyticAt ℝ (fun t => ⟪v t,w t⟫_ℂ) x :=
  PacketForm.inner (fun _ _ => TopRegular.inner n) hv hw

theorem zero (n : ℕ) : PacketRegular x n (fun _ => 0) := PacketForm.zero

theorem add (n : ℕ) {v w : X → Level n} (hv : PacketRegular x n v) (hw : PacketRegular x n w) :
    PacketRegular x n (fun t => v t+w t) := PacketForm.add hv hw

theorem smul (n : ℕ) {v : X → Level n} {z : X → ℂ}
    (hz : AnalyticAt ℝ z x) (hv : PacketRegular x n v) :
    PacketRegular x n (fun t => z t • v t) := PacketForm.smul hz hv

theorem neg (n : ℕ) {v : X → Level n} (hv : PacketRegular x n v) :
    PacketRegular x n (fun t => -v t) := PacketForm.neg hv

theorem vac (n : ℕ) : PacketRegular x n (fun _ => SeededTree.vac n) :=
  PacketForm.vacuum (TopRegular.zero n)

theorem root (n : ℕ) {v : X → Level n} {A : X → Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀i j, AnalyticAt ℝ (fun t => A t i j) x) (hv : PacketRegular x n v) :
    PacketRegular x n (fun t => SeededTree.root n (A t) (v t)) := PacketForm.root hA hv

theorem pulse (n : ℕ) {v : X → Level n} {h : X → TopMode n}
    (hh : TopRegular x n h) (hv : PacketRegular x n v) :
    PacketRegular x n (fun t => WZ (h t) (v t)) :=
  PacketForm.pulse (fun _ _ => TopRegular.inner n) (fun _ _ => TopRegular.add n)
    (fun _ => TopRegular.neg n) hh hv

end PacketRegular
end SeededTree

end

end OAI
