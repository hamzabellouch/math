import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights
import OAI.Analysis.JiangSu.Nonunital.Hereditary

namespace OAI


noncomputable section
namespace NonunitalGamma
open Filter Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def closedTwoSidedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (closure (I : Set A))
    (subset_closure I.zero_mem)
    (by
      intro x y hx hy
      exact map_mem_closure₂ continuous_add hx hy fun _ hleft _ hright =>
        I.add_mem hleft hright)
    (by
      intro x hx
      exact map_mem_closure continuous_neg hx fun _ member => I.neg_mem member)
    (by
      intro x y hy
      exact map_mem_closure (continuous_const.mul continuous_id) hy fun value member =>
        I.mul_mem_left x value member)
    (by
      intro left right hleft
      exact map_mem_closure (f := fun value : A => value * right)
        (continuous_id.mul continuous_const) hleft fun value member =>
          I.mul_mem_right value right member)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem coe_closedTwoSidedIdeal (I : TwoSidedIdeal A) :
    (closedTwoSidedIdeal I : Set A) = closure (I : Set A) := by
  simp [closedTwoSidedIdeal]

def finiteIdealSum (h : A) (l : List (A × A)) : A :=
  (l.map fun p => p.1*h*p.2).sum

def finiteSandwichIdeal (h : A) : TwoSidedIdeal A := .mk' (Set.range (finiteIdealSum h))
  ⟨[],rfl⟩
  (by
    rintro x y ⟨l,rfl⟩ ⟨m,rfl⟩
    exact ⟨l++m,by simp [finiteIdealSum]⟩)
  (by
    rintro x ⟨l,rfl⟩
    refine ⟨l.map (fun p => (-p.1,p.2)),?_⟩
    induction l with
    | nil => simp [finiteIdealSum]
    | cons p l ih => simp_all [finiteIdealSum,List.map_map,Function.comp_def,neg_add_rev,add_comm])
  (by
    rintro a x ⟨l,rfl⟩
    refine ⟨l.map (fun p => (a*p.1,p.2)),?_⟩
    simp [finiteIdealSum,List.map_map,Function.comp_def,mul_assoc,List.sum_map_mul_left])
  (by
    rintro x b ⟨l,rfl⟩
    refine ⟨l.map (fun p => (p.1,p.2*b)),?_⟩
    simp only [finiteIdealSum,List.map_map,Function.comp_def]
    simpa only [mul_assoc] using
      (List.sum_map_mul_right (l := l) (f := fun p => p.1*h*p.2) (r := b)))

lemma finiteIdealSum_dense (hsimple : TopologicallySimple A) {h : A}
    (hh : 0 ≤ h) (hh0 : h ≠ 0) : closure (Set.range (finiteIdealSum h))=Set.univ := by
  have h3 : h*h*h ≠ 0 := by
    intro hz
    have h4 : star (h*h)*(h*h)=0 := by
      simp only [star_mul,hh.star_eq]
      rw [←mul_assoc,hz,zero_mul]
    have h2 := (CStarRing.star_mul_self_eq_zero_iff (h*h)).mp h4
    exact hh0 ((CStarRing.star_mul_self_eq_zero_iff h).mp (by simpa only [hh.star_eq] using h2))
  let I := finiteSandwichIdeal h
  have hmem : h*h*h ∈ closedTwoSidedIdeal I := by
    rw [←SetLike.mem_coe,coe_closedTwoSidedIdeal]
    apply subset_closure
    simp only [I,finiteSandwichIdeal]
    exact ⟨[(h,h)],by simp [finiteIdealSum]⟩
  have hcl : IsClosed (closedTwoSidedIdeal I : Set A) := by
    rw [coe_closedTwoSidedIdeal];exact isClosed_closure
  rcases hsimple (closedTwoSidedIdeal I) hcl with hb|ht
  · rw [hb,TwoSidedIdeal.mem_bot] at hmem
    exact (h3 hmem).elim
  · have ht' := congrArg (fun J : TwoSidedIdeal A => (J : Set A)) ht
    rw [coe_closedTwoSidedIdeal,TwoSidedIdeal.coe_top] at ht'
    have hcoe : (I : Set A)=Set.range (finiteIdealSum h) := by
      ext x
      change x-0 ∈ Set.range (finiteIdealSum h) ↔ x ∈ Set.range (finiteIdealSum h)
      rw [sub_zero]
    rw [hcoe] at ht'
    exact ht'

theorem exists_square_finiteIdealSum (hsimple : TopologicallySimple A) {h g : A}
    (hh : 0 ≤ h) (hh0 : h ≠ 0) (hg : 0 ≤ g) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (A × A), ‖star (finiteIdealSum h l)*finiteIdealSum h l-g‖ < ε := by
  have hc : Continuous (fun x : A => star x*x) := continuous_star.mul continuous_id
  obtain ⟨δ,hδ,hδp⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := CFC.sqrt g)) ε hε
  have hm : CFC.sqrt g ∈ closure (Set.range (finiteIdealSum h)) := by
    rw [finiteIdealSum_dense hsimple hh hh0];exact Set.mem_univ _
  obtain ⟨x,⟨l,hl⟩,hx⟩ := Metric.mem_closure_iff.mp hm δ hδ
  refine ⟨l,?_⟩
  have ht := hδp (by simpa only [dist_comm] using hx)
  rw [(CFC.sqrt_nonneg g).star_eq,CFC.sqrt_mul_sqrt_self g hg,dist_eq_norm,←hl] at ht
  exact ht

end NonunitalGamma



namespace NonunitalGamma
open Filter Topology
open scoped CStarAlgebra ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem cfc_mem_real_subalgebra (S : NonUnitalStarSubalgebra ℝ A)
    [IsClosed (S : Set A)] (f : ℝ → ℝ) {a : A} (ha : a ∈ S) : cfcₙ f a ∈ S :=
  cfcₙ_mem f ha

local instance (priority := 2000) realModuleMatrix : Module ℝ (CStarMatrix ι ι A) :=
  Module.compHom (CStarMatrix ι ι A) Complex.ofRealHom

def hereditaryMatrix (h : A) (hh : 0 ≤ h) :
    NonUnitalStarSubalgebra ℝ (CStarMatrix ι ι A) where
  carrier := {M | ∀ i j, M i j ∈ hereditarySubalgebra h hh}
  zero_mem' := fun i j => (hereditarySubalgebra h hh).zero_mem
  add_mem' := fun hx hy i j => (hereditarySubalgebra h hh).add_mem (hx i j) (hy i j)
  mul_mem' := by
    intro M N hM hN i j
    rw [CStarMatrix.mul_apply]
    exact sum_mem fun k _ => (hereditarySubalgebra h hh).mul_mem (hM i k) (hN k j)
  smul_mem' := fun r M hM i j => (hereditarySubalgebra h hh).smul_mem r (hM i j)
  star_mem' := by
    intro M hM i j
    rw [CStarMatrix.star_apply]
    exact star_mem (hM j i)

instance hereditaryMatrix_closed (h : A) (hh : 0 ≤ h) :
    IsClosed (hereditaryMatrix (ι := ι) h hh : Set (CStarMatrix ι ι A)) := by
  change IsClosed {M : CStarMatrix ι ι A | ∀ i j, M i j ∈ hereditarySubalgebra h hh}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter fun i => isClosed_iInter fun j => ?_
  exact (hereditarySubalgebra_closed h hh).preimage
    (((continuous_apply j).comp (continuous_apply i)).comp CStarMatrix.ofMatrixL.symm.continuous)

lemma matrix_sqrt_hereditary {h : A} (hh : 0 ≤ h) (M : CStarMatrix ι ι A)
    (hM : 0 ≤ M) (hm : ∀ i j, M i j ∈ hereditaryCarrier h) :
    ∀ i j, CFC.sqrt M i j ∈ hereditaryCarrier h := by
  have hm' : M ∈ hereditaryMatrix h hh := hm
  have hs : CFC.sqrt M ∈ hereditaryMatrix h hh := by
    rw [CFC.sqrt_eq_real_sqrt M hM]
    simpa only using! cfc_mem_real_subalgebra (A := CStarMatrix ι ι A)
      (hereditaryMatrix h hh) Real.sqrt (a := M) hm'
  exact hs

omit [PartialOrder A] [StarOrderedRing A] in
lemma sum_star_matrix_vector (C : CStarMatrix ι ι A) (t : ι → A) :
    (∑ i, star (∑ j, C i j*t j)*(∑ k,C i k*t k)) =
      ∑ j, ∑ k, star (t j)*(star C*C) j k*t k := by
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum,
    CStarMatrix.mul_apply,CStarMatrix.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc]

lemma hereditary_matrix_vector_mulStar {h : A} (hh : 0 ≤ h)
    (C : CStarMatrix ι ι A) (hc : ∀ i j,C i j ∈ hereditaryCarrier h) (t : ι → A) (i : ι) :
    (∑ j,C i j*t j)*star (∑ k,C i k*t k) ∈ hereditaryCarrier h := by
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  apply (hereditarySubalgebra h hh).sum_mem
  intro j _
  apply (hereditarySubalgebra h hh).sum_mem
  intro k _
  have hk : star (C i j) ∈ hereditaryCarrier h :=
    star_mem (s := hereditarySubalgebra h hh) (hc i j)
  change C i k*t k*(star (t j)*star (C i j)) ∈ hereditaryCarrier h
  simpa only [mul_assoc] using hereditary_sandwich_mem (t k*star (t j)) (hc i k) hk

theorem finite_trace_transfer [Nonempty ι] (h : A) (hh : 0 ≤ h) (r t : ι → A) :
    ∃ c : A, 0 ≤ c ∧ c ∈ hereditaryCarrier h ∧
      ∀ τ : NormalizedTrace A,
        τ.functional c=τ.functional (star (∑ j,r j*h*t j)*(∑ j,r j*h*t j)) := by
  classical
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let R : CStarMatrix ι ι A := CStarMatrix.ofMatrix (fun i j => if i=i₀ then r j*h else 0)
  let M := star R*R
  have hM : 0 ≤ M := star_mul_self_nonneg R
  have hMe (j k : ι) : M j k=h*star (r j)*r k*h := by
    change (∑ x,star (if x=i₀ then r j*h else 0)*(if x=i₀ then r k*h else 0))=_
    simp [hh.star_eq,mul_assoc]
  have hMm : ∀ j k, M j k ∈ hereditaryCarrier h := by
    intro j k
    rw [hMe]
    exact subset_closure ⟨star (r j)*r k,by simp only [mul_assoc]⟩
  let C := CFC.sqrt M
  have hC : ∀ i j, C i j ∈ hereditaryCarrier h := matrix_sqrt_hereditary hh M hM hMm
  have hCC : star C*C=M := by
    rw [(CFC.sqrt_nonneg M).star_eq,CFC.sqrt_mul_sqrt_self M hM]
  let v : ι → A := fun i => ∑ j,C i j*t j
  let c := ∑ i,v i*star (v i)
  refine ⟨c,Finset.sum_nonneg (fun i _ => mul_star_self_nonneg (v i)),?_,?_⟩
  · exact (hereditarySubalgebra h hh).sum_mem fun i _ =>
      hereditary_matrix_vector_mulStar hh C hC t i
  · intro τ
    calc
      τ.functional c = ∑ i,τ.functional (star (v i)*v i) := by
        simp only [c,map_sum,τ.tracial]
      _ = τ.functional (∑ i,star (v i)*v i) := (map_sum _ _ _).symm
      _ = τ.functional (star (∑ j,r j*h*t j)*(∑ j,r j*h*t j)) := by
        congr 1
        change (∑ i,star (∑ j,C i j*t j)*(∑ k,C i k*t k))=_
        rw [sum_star_matrix_vector,hCC]
        simp only [hMe,star_sum,star_mul,hh.star_eq,Finset.sum_mul,Finset.mul_sum,mul_assoc]
        exact Finset.sum_comm

end NonunitalGamma

end

end OAI
