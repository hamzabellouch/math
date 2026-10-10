import Mathlib
import OAI.GroupTheory.FiniteType.LoopPath

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace BasedHorn
open Set Topology DuffySimplex SimplexBoundary DuffyTriangle SimplexAddition
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

lemma face_compatible (i : Fin (n+3)) (f : SimplexHorn.Faces i → BasedSimplex.Space (n+1) X x) :
    ∀ (j k : SimplexHorn.Faces i) (a b : Std (n+1)),
      face j.1 a = face k.1 b → (f j).1 a = (f k).1 b := by
  intro j k a b hab
  by_cases hjk : j = k
  · subst k
    exact congrArg (f j).1 (face_injective j.1 hab)
  have hv : j.1 ≠ k.1 := fun h => hjk (Subtype.ext h)
  obtain ⟨l,s,_,rfl,rfl⟩ := face_overlap hv hab
  exact ((f j).2 _ ⟨l,face_zero l s⟩).trans ((f k).2 _ ⟨_,face_zero _ s⟩).symm

def fill (i : Fin (n+3)) (f : SimplexHorn.Faces i → BasedSimplex.Space (n+1) X x) :
    C(Std (n+2),X) := SimplexHorn.fill i (fun j => (f j).1) (face_compatible i f)

lemma fill_face (i : Fin (n+3)) (f : SimplexHorn.Faces i → BasedSimplex.Space (n+1) X x)
    (j : SimplexHorn.Faces i) : (fill i f).comp (face j.1) = (f j).1 :=
  SimplexHorn.fill_face i (fun j => (f j).1) (face_compatible i f) j

lemma fill_doubleBoundary (i : Fin (n+3)) (f : SimplexHorn.Faces i → BasedSimplex.Space (n+1) X x) :
    ∀ s ∈ DoubleBoundary (n+2), fill i f s = x := by
  rintro s ⟨j,k,hjk,hj,hk⟩
  have swap : ∀ (j k : Fin (n+3)), j ≠ k → s.1 j = 0 → s.1 k = 0 → j ≠ i → fill i f s = x := by
    intro j k hjk hj hk hji
    let a := drop j s hj
    have ha : a ∈ BasedSimplex.Boundary (n+1) := by
      obtain ⟨l,hl⟩ := Fin.exists_succAbove_eq hjk.symm
      exact ⟨l,by change s.1 (j.succAbove l) = 0; rw [hl,hk]⟩
    rw [← face_drop j s hj]
    exact (DFunLike.congr_fun (fill_face i f ⟨j,hji⟩) a).trans ((f ⟨j,hji⟩).2 a ha)
  by_cases hji : j = i
  · exact swap k j hjk.symm hk hj (by intro hki; exact hjk (hji.trans hki.symm))
  · exact swap j k hjk hj hk hji

lemma lastFace_injective (n : ℕ) : Function.Injective (lastFace n) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [lastFace_val] at hv
  omega

def pairFaces (f g : BasedSimplex.Space (n+1) X x) :
    SimplexHorn.Faces (lastFace n 1) → BasedSimplex.Space (n+1) X x := fun j =>
  if j.1 = lastFace n 0 then f else if j.1 = lastFace n 2 then g else BasedSimplex.const (n+1) x

def pairFill (f g : BasedSimplex.Space (n+1) X x) : C(Std (n+2),X) :=
  fill (lastFace n 1) (pairFaces f g)

lemma pairFill_doubleBoundary (f g : BasedSimplex.Space (n+1) X x) :
    ∀ s ∈ DoubleBoundary (n+2), pairFill f g s = x := fill_doubleBoundary _ _

lemma pairFill_early (f g : BasedSimplex.Space (n+1) X x) :
    ∀ i : Fin (n+3), i.val < n → (pairFill f g).comp (face i) = ContinuousMap.const _ x := by
  intro i hi
  have hne (j : Fin 3) : i ≠ lastFace n j := by
    intro h
    have hv := congrArg Fin.val h
    rw [lastFace_val] at hv
    omega
  change (fill _ _).comp (face i) = _
  rw [fill_face _ _ ⟨i,hne 1⟩]
  simp [pairFaces,hne,BasedSimplex.const]

lemma pairFill_left (f g : BasedSimplex.Space (n+1) X x) :
    basedFace (pairFill f g) (pairFill_doubleBoundary f g) (lastFace n 0) = f := by
  apply Subtype.ext
  change (fill _ _).comp (face _) = _
  rw [fill_face _ _ ⟨lastFace n 0,fun h => by have := lastFace_injective n h; contradiction⟩]
  simp [pairFaces]

lemma pairFill_right (f g : BasedSimplex.Space (n+1) X x) :
    basedFace (pairFill f g) (pairFill_doubleBoundary f g) (lastFace n 2) = g := by
  apply Subtype.ext
  change (fill _ _).comp (face _) = _
  rw [fill_face _ _ ⟨lastFace n 2,fun h => by have := lastFace_injective n h; contradiction⟩]
  have hne : lastFace n 2 ≠ lastFace n 0 := fun h => by have := lastFace_injective n h; contradiction
  simp [pairFaces,hne]

def product (f g : BasedSimplex.Space (n+1) X x) : BasedSimplex.Space (n+1) X x :=
  basedFace (pairFill g f) (pairFill_doubleBoundary g f) (lastFace n 1)

lemma product_class (f g : BasedSimplex.Space (n+1) X x) :
    DuffyBased.homotopyClass (product f g) = DuffyBased.homotopyClass f * DuffyBased.homotopyClass g := by
  exact (three_face _ (pairFill_doubleBoundary g f) (pairFill_early g f)).trans
    (by rw [pairFill_right,pairFill_left])

end BasedHorn

namespace HurewiczAddition
open Set Topology CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains HurewiczNormalized DuffyTriangle SimplexAddition
variable {X : Type} [TopologicalSpace X] {n : ℕ} {x : X}

lemma alternating_cycle_boundary (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x) :
    (generator F - generator (ContinuousMap.const _ x)) ≫ (chains X).d (n+2) (n+1) =
      ∑ i : Fin (n+3), (-1:ℤ)^i.val • cycle (basedFace F h₂ i) := by
  rw [Preadditive.sub_comp,generator_boundary,generator_boundary,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_sub]
  rfl

lemma cycleClassHom_sum {ι : Type} [Fintype ι]
    (c : ι → (ModuleCat.of ℤ ℤ ⟶ (chains X).X n))
    (hc : ∀ i, c i ≫ (chains X).d n (n-1) = 0) (a : ι → ℤ) :
    cycleClassHom (∑ i, a i • c i) (by simp [Preadditive.sum_comp,hc]) =
      ∑ i, a i • cycleClassHom (c i) (hc i) := by
  have hl : (chains X).liftCycles (∑ i, a i • c i) (n-1)
      (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ])
      (by simp [Preadditive.sum_comp,hc]) =
      ∑ i, a i • (chains X).liftCycles (c i) (n-1)
        (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]) (hc i) := by
    apply (cancel_mono ((chains X).iCycles n)).mp
    simp only [liftCycles_i,Preadditive.sum_comp,Linear.smul_comp]
  exact (congrArg (fun t => t ≫ (chains X).homologyπ n) hl).trans
    (by simp only [Preadditive.sum_comp,Linear.smul_comp,cycleClassHom])

lemma alternating_class_zero (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x) :
    (∑ i : Fin (n+3), (-1:ℤ)^i.val • homologyClass (basedFace F h₂ i)) = 0 := by
  have hb := (chains X).liftCycles_homologyπ_eq_zero_of_boundary
    (∑ i : Fin (n+3), (-1:ℤ)^i.val • cycle (basedFace F h₂ i)) n
    (by simp [ChainComplex.next_nat_succ])
    (generator F - generator (ContinuousMap.const _ x)) (alternating_cycle_boundary F h₂).symm
  change cycleClassHom _ _ = 0 at hb
  rw [cycleClassHom_sum (fun i => cycle (basedFace F h₂ i)) (fun i => cycle_d _) (fun i : Fin (n+3) => (-1:ℤ)^i.val)] at hb
  have hv := congrArg (fun t => t 1) hb
  simpa only [ModuleCat.hom_sum,ModuleCat.hom_smul,ModuleCat.hom_zero,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.zero_apply,homologyClass] using hv

@[simp] lemma homologyClass_const (x : X) (n : ℕ) : homologyClass (BasedSimplex.const n x) = 0 := by
  have hc : cycle (BasedSimplex.const n x) = 0 := sub_self _
  have hh : cycleClassHom (cycle (BasedSimplex.const n x)) (cycle_d _) = 0 := by
    unfold cycleClassHom
    have hl : (chains X).liftCycles (cycle (BasedSimplex.const n x)) (n-1)
        (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]) (cycle_d _) = 0 := by
      apply (cancel_mono ((chains X).iCycles n)).mp
      rw [liftCycles_i,zero_comp,hc]
    rw [hl,zero_comp]
  exact congrArg (fun t => t 1) hh

lemma alternating_three {A : Type*} [AddCommGroup A] (n : ℕ) (f : Fin (n+3) → A)
    (he : ∀ i, i.val < n → f i = 0) :
    (∑ i, (-1:ℤ)^i.val • f i) = (-1:ℤ)^n •
      (f (lastFace n 0) - f (lastFace n 1) + f (lastFace n 2)) := by
  induction n with
  | zero => simp [lastFace,Fin.sum_univ_succ]; abel
  | succ n ih =>
    rw [Fin.sum_univ_succ,he 0 (by simp),smul_zero,zero_add]
    have hs : (∑ i : Fin (n+3), (-1:ℤ)^(i.val+1) • f i.succ) =
        - ∑ i : Fin (n+3), (-1:ℤ)^i.val • f i.succ := by
      simp only [pow_succ,mul_neg_one,neg_smul,Finset.sum_neg_distrib]
    simp only [Fin.val_succ]
    rw [hs,ih (fun i => f i.succ) (fun i hi => he i.succ (by simpa only [Fin.val_succ] using Nat.succ_lt_succ hi))]
    simp only [lastFace,pow_succ,mul_neg_one,neg_smul]

lemma homologyClass_product (f g : BasedSimplex.Space (n+1) X x) :
    homologyClass (BasedHorn.product f g) = homologyClass f + homologyClass g := by
  have h := alternating_class_zero (BasedHorn.pairFill g f) (BasedHorn.pairFill_doubleBoundary g f)
  rw [alternating_three n _ (by
    intro i hi
    have hface : basedFace (BasedHorn.pairFill g f) (BasedHorn.pairFill_doubleBoundary g f) i =
        BasedSimplex.const (n+1) x := Subtype.ext (BasedHorn.pairFill_early g f i hi)
    rw [hface,homologyClass_const])] at h
  rw [BasedHorn.pairFill_left,BasedHorn.pairFill_right] at h
  change (-1:ℤ)^n • (homologyClass g - homologyClass (BasedHorn.product f g) + homologyClass f) = 0 at h
  have hz : homologyClass g - homologyClass (BasedHorn.product f g) + homologyClass f = 0 := by
    have h' := congrArg (fun z => (-1:ℤ)^n • z) h
    have hz₀ : (-1:ℤ)^n • (0 : (chains X).homology (n+1)) = 0 := zsmul_zero _
    have heq : homologyClass g - homologyClass (BasedHorn.product f g) + homologyClass f =
        (-1:ℤ)^n • (0 : (chains X).homology (n+1)) := by
      simpa only [smul_smul,← mul_pow,neg_one_mul,neg_neg,one_pow,one_smul] using h'
    exact heq.trans hz₀
  have he : homologyClass g + homologyClass f = homologyClass (BasedHorn.product f g) :=
    sub_eq_zero.mp (by convert hz using 1; abel)
  exact he.symm.trans (add_comm _ _)

end HurewiczAddition

namespace DuffyHurewicz
open Set Topology CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains HurewiczNormalized DuffyBased
variable {X : Type} [TopologicalSpace X] {n : ℕ} {x : X}

lemma homologyClass_homotopic {f g : BasedSimplex.Space n X x}
    (H : f.1.HomotopyRel g.1 (BasedSimplex.Boundary n)) :
    homologyClass f = homologyClass g := by
  rw [← canonical_simplex,← canonical_simplex,BasedSimplex.class_homotopic H]

def value (p : HomotopyGroup.Pi n X x) : (chains X).homology n :=
  Quotient.lift (fun p => homologyClass (ofLoop p)) (by
    intro p q hpq
    apply homologyClass_homotopic
    apply Classical.choice
    apply (class_eq_iff _ _).mp
    change Quotient.mk _ (loop (ofLoop p)) = Quotient.mk _ (loop (ofLoop q))
    simpa only [loop_ofLoop] using Quotient.sound hpq) p

@[simp] lemma value_class (f : BasedSimplex.Space n X x) :
    value (homotopyClass f) = homologyClass f := by
  change homologyClass (ofLoop (loop f)) = _
  rw [ofLoop_loop]

lemma value_mul (p q : HomotopyGroup.Pi (n+1) X x) :
    value (p*q) = value p + value q := by
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      have hp : homotopyClass (ofLoop p) = Quotient.mk _ p := congrArg (Quotient.mk _) (loop_ofLoop p)
      have hq : homotopyClass (ofLoop q) = Quotient.mk _ q := congrArg (Quotient.mk _) (loop_ofLoop q)
      rw [← hp,← hq,← BasedHorn.product_class,value_class,value_class,value_class]
      exact HurewiczAddition.homologyClass_product _ _

def hom (n : ℕ) (x : X) : Additive (HomotopyGroup.Pi (n+1) X x) →+ (chains X).homology (n+1) :=
  AddMonoidHom.mk' (fun p => value p.toMul) (fun p q => value_mul p.toMul q.toMul)

@[simp] lemma hom_class (f : BasedSimplex.Space (n+1) X x) :
    hom n x (Additive.ofMul (homotopyClass f)) = homologyClass f := value_class f

lemma range_canonical_le_range (x : X) :
    Set.range (HurewiczConstruction.canonical (n+1) (X:=X) (x:=x)) ⊆
      Set.range (hom n x) := by
  rintro z ⟨p,rfl⟩
  induction p using Quotient.inductionOn with
  | h p =>
    let f := BasedSimplex.ofLoop p
    have hf : BasedSimplex.homotopyClass f = Quotient.mk _ p :=
      congrArg (Quotient.mk _) (BasedSimplex.loop_ofLoop p)
    refine ⟨Additive.ofMul (homotopyClass f),?_⟩
    rw [hom_class,← canonical_simplex,hf]

theorem surjective
    (hπ : ∀ p < n+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X) :
    Function.Surjective (hom n x) := by
  let P : Submodule ℤ ((chains X).homology (n+1)) :=
    { (hom n x).range with
      smul_mem' := fun c y hy => by
        change ((chains X).homology (n+1)).isModule.smul c y ∈ (hom n x).range
        rw [int_smul_eq_zsmul]
        exact AddSubgroup.zsmul_mem (hom n x).range hy c }
  have hP : Submodule.span ℤ (Set.range (HurewiczConstruction.canonical (n+1) (X:=X) (x:=x))) ≤ P :=
    Submodule.span_le.mpr (range_canonical_le_range x)
  rw [HurewiczNormalized.canonical_span hπ x] at hP
  intro z
  exact hP (Submodule.mem_top) 

end DuffyHurewicz

end

end OAI
