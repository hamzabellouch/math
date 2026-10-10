import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice19
import OAI.Combinatorics.SumProduct.Alignment.RoughKernel01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators
end
 
end

end

section

noncomputable section
namespace RoughArrayFace
open RationalLattice MalcevCharacters
open scoped BigOperators
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)

abbrev Component (i : ι) := PolynomialArrays.group (q:=q) (c i) (hsk i) (A i) (w i) (hA i)
abbrev Carrier := ∀ i,Component G n q c hsk A w hA i
abbrev Index := Σ i,PolynomialArrays.Index (w i) q

 
def lattice (Γ : ∀ i,Subgroup (G i)) : Subgroup (Carrier G n q c hsk A w hA) where
  carrier:=fun f=>∀ i,f i∈PolynomialArrays.lattice (c i) (hsk i) (A i) (w i) (hA i) (Γ i)
  one_mem':=fun i=>(PolynomialArrays.lattice (c i) (hsk i) (A i) (w i) (hA i) (Γ i)).one_mem
  mul_mem':=fun hf hg i=>(PolynomialArrays.lattice (c i) (hsk i) (A i) (w i) (hA i) (Γ i)).mul_mem (hf i) (hg i)
  inv_mem':=fun hf i=>(PolynomialArrays.lattice (c i) (hsk i) (A i) (w i) (hA i) (Γ i)).inv_mem (hf i)

 

def sourceState {m v : ℕ} (pattern : ι→Fin v→ℤ) (g x : ∀ i,G i)
    (b0 b1 : ι→ℝ) (a0 a1 : Fin q→ℝ) (y : Fin (m+v)→ℝ) :
    Carrier G n q c hsk A w hA :=
  fun i=>PolynomialArrays.sourceElement (c i) (hsk i) (A i) (w i) (hA i) (hw i)
    (g i) (x i)
    (b0 i+b1 i*(∏ k : Fin m,y (k.castAdd v))+∑ j,(pattern i j:ℝ)*y (j.natAdd m))
    (fun e=>a0 e+a1 e*(∏ k : Fin m,y (k.castAdd v)))

def inputShift {v : ℕ} (pattern : ι→Fin v→ℤ) (e : Fin q) (j : Fin v)
    (i : ι) : Fin q→ℤ := Pi.single e (pattern i j)

def faceMap {v : ℕ} (pattern : ι→Fin v→ℤ) (e : Fin q) (j : Fin v) :
    Carrier G n q c hsk A w hA →* Carrier G n q c hsk A w hA where
  toFun f i:=PolynomialArrays.shift (c i) (hsk i) (A i) (w i) (hA i)
    (fun k=>(inputShift q pattern e j i k:ℝ)) (f i)
  map_one':=by funext i;exact map_one _
  map_mul' f g:=by funext i;exact map_mul _ _ _

omit [Fintype ι] in
lemma faceMap_continuous {v : ℕ} (pattern : ι→Fin v→ℤ) (e : Fin q) (j : Fin v) :
    Continuous (faceMap G n q c hsk A w hA pattern e j) :=
  continuous_pi (fun i=>(PolynomialArrays.shift_continuous (c i) (hsk i) (A i) (w i) (hA i) _).comp
    (continuous_apply i))

variable (Γ : ∀ i,Subgroup (G i))
 
def faceAction {v : ℕ} (pattern : ι→Fin v→ℤ) (e : Fin q) (j : Fin v) :
    C((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ,
      (Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ) where
  toFun:=Quotient.map (faceMap G n q c hsk A w hA pattern e j) (by
    intro f g hfg
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv,← map_mul]
    intro i
    exact (PolynomialArrays.shift_lattice (c i) (hsk i) (A i) (w i) (hA i) (Γ i)
      (inputShift q pattern e j i) _).mpr ((QuotientGroup.leftRel_apply.mp hfg) i))
  continuous_toFun:=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp (faceMap_continuous G n q c hsk A w hA pattern e j))

end RoughArrayFace
end

end

noncomputable section
namespace RoughArrayFace
open RationalLattice MalcevCharacters
open scoped BigOperators
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)

open WeightedPolynomial

 

def coefficientsHomeomorph : Carrier G n q c hsk A w hA ≃ₜ (Index n q w→ℝ) where
  toFun f a:=PolynomialArrays.coefficients (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1) (f a.1) a.2
  invFun y i:=(PolynomialArrays.coefficientHomeomorph (c i) (hsk i) (A i) (w i) (hA i)).symm
    (fun a=>y ⟨i,a⟩)
  left_inv f:=by
    funext i
    exact (PolynomialArrays.coefficientHomeomorph (c i) (hsk i) (A i) (w i) (hA i)).symm_apply_apply (f i)
  right_inv y:=by
    funext a
    exact congrFun ((PolynomialArrays.coefficientHomeomorph (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1)).apply_symm_apply
      (fun k=>y ⟨a.1,k⟩)) a.2
  continuous_toFun:=continuous_pi (fun a=>(continuous_apply a.2).comp
    ((PolynomialArrays.coefficients_continuous (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1)).comp
      (continuous_apply a.1)))
  continuous_invFun:=continuous_pi (fun i=>(PolynomialArrays.coefficientHomeomorph (c i) (hsk i) (A i) (w i) (hA i)).symm.continuous.comp
    (continuous_pi (fun a=>continuous_apply (⟨i,a⟩ : Index n q w))))

def jointWeight (a : Index n q w) : ℕ:=w a.1 a.2.1

omit [Fintype ι] in
lemma coefficientsHomeomorph_one : coefficientsHomeomorph G n q c hsk A w hA 1=0 := by
  funext a
  exact congrFun (PolynomialArrays.coefficientHomeomorph_one (q:=q) (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1)) a.2

omit [Fintype ι] in
lemma joint_law (y : (Index n q w ⊕ Index n q w)→ℝ) (a : Index n q w) :
    FiniteWeightedLawChart.law (coefficientsHomeomorph G n q c hsk A w hA) y a=
      PolynomialArrays.multiply (c a.1) (w a.1)
        (Sum.elim (fun b=>y (Sum.inl ⟨a.1,b⟩)) (fun b=>y (Sum.inr ⟨a.1,b⟩))) a.2 := by
  change (PolynomialArrays.coefficientHomeomorph (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1))
    ((PolynomialArrays.coefficientHomeomorph (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1)).symm
      (fun b=>y (Sum.inl ⟨a.1,b⟩)) *
    (PolynomialArrays.coefficientHomeomorph (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1)).symm
      (fun b=>y (Sum.inr ⟨a.1,b⟩))) a.2=_
  rw [PolynomialArrays.coefficientHomeomorph_mul]
  simp only [Homeomorph.apply_symm_apply]

omit [Fintype ι] in
lemma joint_law_polynomial (a : Index n q w) : RationalPolynomialMap.IsPolynomial
    (fun y=>FiniteWeightedLawChart.law (coefficientsHomeomorph G n q c hsk A w hA) y a) := by
  have hp:=RationalPolynomialMap.comp (PolynomialArrays.multiply_polynomial (c a.1) (w a.1) a.2)
    (g:=fun y=>Sum.elim (fun b=>y (Sum.inl (⟨a.1,b⟩ : Index n q w)))
      (fun b=>y (Sum.inr (⟨a.1,b⟩ : Index n q w)))) (by
        intro j
        cases j with
        | inl j=>exact RationalPolynomialMap.coordinate _
        | inr j=>exact RationalPolynomialMap.coordinate _)
  simpa only [joint_law] using hp

omit [Fintype ι] in
lemma joint_law_weighted (a : Index n q w) :
    IsWeighted (Sum.elim (jointWeight n q w) (jointWeight n q w)) (jointWeight n q w a)
      (fun y=>FiniteWeightedLawChart.law (coefficientsHomeomorph G n q c hsk A w hA) y a) := by
  have hp:=(PolynomialArrays.multiply_weighted (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1) a.2).comp
    (g:=fun y=>Sum.elim (fun b=>y (Sum.inl (⟨a.1,b⟩ : Index n q w)))
      (fun b=>y (Sum.inr (⟨a.1,b⟩ : Index n q w)))) (by
        intro j
        cases j with
        | inl j=>exact IsWeighted.coordinate (Sum.elim (jointWeight n q w) (jointWeight n q w)) (Sum.inl ⟨a.1,j⟩)
        | inr j=>exact IsWeighted.coordinate (Sum.elim (jointWeight n q w) (jointWeight n q w)) (Sum.inr ⟨a.1,j⟩))
  simpa only [joint_law,jointWeight,PolynomialArrays.weight] using hp

def jointChart : RealCoordinates (Carrier G n q c hsk A w hA) (Fintype.card (Index n q w)) :=
  FiniteWeightedLawChart.chart (coefficientsHomeomorph G n q c hsk A w hA)
    (coefficientsHomeomorph_one G n q c hsk A w hA) (jointWeight n q w) (fun a=>hw a.1 a.2.1)
    (joint_law_polynomial G n q c hsk A w hA) (joint_law_weighted G n q c hsk A w hA)

lemma jointChart_at (f : Carrier G n q c hsk A w hA) (a : Index n q w) :
    (jointChart G n q c hsk A w hA hw).coord f ((SortedFiniteWeights.indexing (jointWeight n q w)).symm a)=
      PolynomialArrays.coefficients (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1) (f a.1) a.2 := by
  change (coefficientsHomeomorph G n q c hsk A w hA) f
    (SortedFiniteWeights.indexing (jointWeight n q w) ((SortedFiniteWeights.indexing (jointWeight n q w)).symm a))=_
  rw [Equiv.apply_symm_apply]
  rfl

lemma jointChart_natpow (f : Carrier G n q c hsk A w hA) (b : ℕ)
    (k : Fin (Fintype.card (Index n q w))) :
    (jointChart G n q c hsk A w hA hw).coord (f^b) k=
      (b:ℝ)*(jointChart G n q c hsk A w hA hw).coord f k :=
  PolynomialArrays.coefficients_natpow (c _) (hsk _) (A _) (w _) (hA _) (f _) b _

lemma jointChart_canonicalLog (f : Carrier G n q c hsk A w hA) :
    canonicalLog (jointChart G n q c hsk A w hA hw) f=
      (jointChart G n q c hsk A w hA hw).coord f := by
  funext k
  let e:=jointChart G n q c hsk A w hA hw
  have hp : powerPolynomial e f k=Polynomial.X*Polynomial.C (e.coord f k) := by
    apply Polynomial.eq_of_eval_nat_eq
    intro b
    simp only [powerPolynomial_nat,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]
    exact jointChart_natpow G n q c hsk A w hA hw f b k
  rw [canonicalLog,hp]
  simp [e]

variable (Γ : ∀ i,Subgroup (G i))
lemma jointChart_grid (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z) :
    ∃ grid : ℕ,0<grid ∧ ∀ f,(∀ j,∃ z : ℤ,
      (jointChart G n q c hsk A w hA hw).coord f j=(grid:ℝ)*z) →
      f∈lattice G n q c hsk A w hA Γ := by
  classical
  have hi (i : ι):=PolynomialArrays.chart_grid_lattice (q:=q) (c i) (hsk i) (A i) (w i) (hA i) (hw i) (Γ i) (hΓ i)
  choose D hD hgrid using hi
  refine ⟨∏ i,D i,Finset.prod_pos (fun i _=>hD i),?_⟩
  intro f hf i
  apply hgrid i (f i)
  intro k
  let a : Index n q w:=⟨i,SortedFiniteWeights.indexing (PolynomialArrays.weight (w i)) k⟩
  obtain ⟨z,hz⟩:=hf ((SortedFiniteWeights.indexing (jointWeight n q w)).symm a)
  rw [jointChart_at] at hz
  obtain ⟨b,hb⟩:=Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  refine ⟨(b:ℤ)*z,?_⟩
  change PolynomialArrays.coefficients (c i) (hsk i) (A i) (w i) (hA i) (f i)
    (SortedFiniteWeights.indexing (PolynomialArrays.weight (w i)) k)=_
  rw [show PolynomialArrays.coefficients (c i) (hsk i) (A i) (w i) (hA i) (f i)
    (SortedFiniteWeights.indexing (PolynomialArrays.weight (w i)) k)=(∏ i,D i:ℕ)*z from hz,hb]
  push_cast
  ring

end RoughArrayFace
end
noncomputable section
open scoped BigOperators
namespace RoughArrayFace
open RationalLattice MalcevCharacters WeightedPolynomial

lemma oneWeight_degree {σ : Type*} {f : (σ→ℝ)→ℝ} {D : ℕ}
    (hf : IsWeighted (fun _=>1) D f) : RealPolynomialDegree.HasDegree f D := by
  obtain ⟨p,hp,he⟩:=hf
  refine ⟨p,Finset.sup_le ?_,he⟩
  intro a ha
  have H:=hp a (MvPolynomial.mem_support_iff.mp ha)
  simpa only [Finsupp.weight_apply,smul_eq_mul,mul_one] using H

lemma oneWeight_mul {σ : Type*} {f g : (σ→ℝ)→ℝ} {D E : ℕ}
    (hf : IsWeighted (fun _=>1) D f) (hg : IsWeighted (fun _=>1) E g) :
    IsWeighted (fun _=>1) (D+E) (fun y=>f y*g y) := by
  obtain ⟨p,hp,he⟩:=hf
  obtain ⟨r,hr,hre⟩:=hg
  exact ⟨p*r,hp.mul hr,by simp [he,hre]⟩

lemma oneWeight_prod {σ κ : Type*} (s : Finset κ) (f : κ→σ) :
    IsWeighted (fun _=>1) s.card (fun y : σ→ℝ=>∏ k∈s,y (f k)) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using IsWeighted.const (σ:=σ) (fun _=>1) 0 1
  | @insert i s hi ih=>
    simpa only [Finset.card_insert_of_notMem hi,Finset.prod_insert hi,Nat.add_comm]
      using oneWeight_mul (IsWeighted.coordinate (fun _ : σ=>1) (f i)) ih

variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j)

omit [Fintype ι] in
lemma source_coefficients_weighted {m v : ℕ} (pattern : ι→Fin v→ℤ) (g x : ∀ i,G i)
    (b0 b1 : ι→ℝ) (a0 a1 : Fin q→ℝ) (a : Index n q w) :
    IsWeighted (fun _ : Fin (m+v)=>1) ((m+1)*jointWeight n q w a)
      (fun y=>coefficientsHomeomorph G n q c hsk A w hA
        (sourceState G n q c hsk A w hA hw pattern g x b0 b1 a0 a1 y) a) := by
  have hprod : IsWeighted (fun _ : Fin (m+v)=>1) (m+1)
      (fun y=>∏ k : Fin m,y (k.castAdd v)) := by
    have H:=oneWeight_prod Finset.univ (fun k : Fin m=>k.castAdd v)
    simp only [Fintype.card_fin,Finset.card_univ] at H
    exact H.mono (Nat.le_succ _)
  have hb : IsWeighted (fun _ : Fin (m+v)=>1) (m+1)
      (fun y=>b0 a.1+b1 a.1*(∏ k : Fin m,y (k.castAdd v))+
        ∑ j,(pattern a.1 j:ℝ)*y (j.natAdd m)) := by
    apply ((IsWeighted.const _ _ _).add (hprod.smul _)).add
    apply IsWeighted.sum
    intro j hj
    exact ((IsWeighted.coordinate (fun _ : Fin (m+v)=>1) (j.natAdd m)).mono (by omega)).smul _
  have hv (e : Fin q) : IsWeighted (fun _ : Fin (m+v)=>1) (m+1)
      (fun y=>a0 e+a1 e*(∏ k : Fin m,y (k.castAdd v))) :=
    (IsWeighted.const _ _ _).add (hprod.smul _)
  let k:=(SortedFiniteWeights.indexing (PolynomialArrays.weight (w a.1))).symm a.2
  have H:=PolynomialArrays.source_joint_log_weighted (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1) (hw a.1)
    hb hv (g a.1) (x a.1) k
  simp only [PolynomialArrays.chart_canonicalLog] at H
  change IsWeighted _ ((m+1)*PolynomialArrays.weight (w a.1)
      (SortedFiniteWeights.indexing (PolynomialArrays.weight (w a.1)) k))
    (fun y=>PolynomialArrays.coefficients (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1)
      (sourceState G n q c hsk A w hA hw pattern g x b0 b1 a0 a1 y a.1)
      (SortedFiniteWeights.indexing (PolynomialArrays.weight (w a.1)) k)) at H
  simp only [k,Equiv.apply_symm_apply] at H
  change IsWeighted _ ((m+1)*w a.1 a.2.1)
    (fun y=>PolynomialArrays.coefficients (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1)
      (sourceState G n q c hsk A w hA hw pattern g x b0 b1 a0 a1 y a.1) a.2)
  exact H

variable (Γ : ∀ i,Subgroup (G i))
 

theorem source_joint_geometry
    (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z) :
    ∃ e : RealCoordinates (Carrier G n q c hsk A w hA) (Fintype.card (Index n q w)),
    ∃ grid : ℕ,0<grid ∧
      (∀ f,(∀ j,∃ z : ℤ,e.coord f j=(grid:ℝ)*z) → f∈lattice G n q c hsk A w hA Γ) ∧
    ∃ J : ℕ,0<J ∧ ∀ (m v : ℕ) (pattern : ι→Fin v→ℤ) (g x : ∀ i,G i)
      (b0 b1 : ι→ℝ) (a0 a1 : Fin q→ℝ) (k : Fin (Fintype.card (Index n q w))),
      RealPolynomialDegree.HasDegree (fun y=>canonicalLog e
        (sourceState G n q c hsk A w hA hw (m:=m) pattern g x b0 b1 a0 a1 y) k)
        (J*(m+1))
 := by
  classical
  obtain ⟨grid,hgridpos,hgrid⟩:=jointChart_grid G n q c hsk A w hA hw Γ hΓ
  refine ⟨jointChart G n q c hsk A w hA hw,grid,hgridpos,hgrid,
    1+∑ a : Index n q w,jointWeight n q w a,by omega,?_⟩
  intro m v pattern g x b0 b1 a0 a1 k
  let a:=SortedFiniteWeights.indexing (jointWeight n q w) k
  have H:=oneWeight_degree (source_coefficients_weighted G n q c hsk A w hA hw (m:=m) pattern g x b0 b1 a0 a1 a)
  have ha : jointWeight n q w a≤1+∑ b : Index n q w,jointWeight n q w b := by
    have HH:=Finset.single_le_sum (f:=jointWeight n q w) (fun b _=>Nat.zero_le _) (Finset.mem_univ a)
    omega
  have H' := RealPolynomialDegree.mono H (Nat.mul_le_mul_left (m+1) ha)
  simp only [jointChart_canonicalLog]
  change RealPolynomialDegree.HasDegree
    (fun y=>coefficientsHomeomorph G n q c hsk A w hA
      (sourceState G n q c hsk A w hA hw pattern g x b0 b1 a0 a1 y) a)
    ((1+∑ b : Index n q w,jointWeight n q w b)*(m+1))
  simpa only [Nat.mul_comm] using H' 

end RoughArrayFace

end

end OAI
