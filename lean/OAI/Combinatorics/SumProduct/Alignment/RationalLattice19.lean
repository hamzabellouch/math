import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice18
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
end
 
end

section
 

 

noncomputable section
namespace RationalLattice.FiniteProducts
open MalcevCharacters MalcevWeightedCoordinates WeightedPolynomial
variable {ι : Type} [Fintype ι] (G : ι → Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι → ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i) → ℕ) (hw : ∀ i j,0<w i j) (hmono : ∀ i,Monotone (w i))
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)

abbrev Index :=Σ i,Fin (n i)
def weight (a : Index n) : ℕ:=w a.1 a.2

def logCoordinates : (∀ i,G i) ≃ₜ (Index n → ℝ) where
  toFun g a:=canonicalLog (c a.1) (g a.1) a.2
  invFun x i:=canonicalExp (c i) (fun j=>x ⟨i,j⟩)
  left_inv g:=by funext i; exact canonicalExp_log (c i) (g i)
  right_inv x:=by funext a; exact congrFun (canonicalLog_exp (c a.1) (fun j=>x ⟨a.1,j⟩)) a.2
  continuous_toFun:=continuous_pi (fun a=>(continuous_apply a.2).comp
    ((canonicalLog_continuous (c a.1)).comp (continuous_apply a.1)))
  continuous_invFun:=continuous_pi (fun i=>(logHomeomorph (c i)).symm.continuous.comp
    (continuous_pi (fun j : Fin (n i)=>continuous_apply (⟨i,j⟩ : Index n))))
omit [Fintype ι] [∀ index,IsTopologicalGroup (G index)] in
lemma logCoordinates_one : logCoordinates G n c 1=0 := by
  funext a
  exact congrFun (canonicalLog_one (c a.1)) a.2

omit [Fintype ι] [∀ index,IsTopologicalGroup (G index)] in
lemma law_polynomial (a : Index n) : RationalPolynomialMap.IsPolynomial
    (fun x=>FiniteWeightedLawChart.law (logCoordinates G n c) x a) := by
  have hl (j : Fin (n a.1)):=RationalPolynomialMap.comp (canonicalExp_polynomial (c a.1) j)
    (fun k=>RationalPolynomialMap.coordinate (Sum.inl (⟨a.1,k⟩ : Index n) : Index n ⊕ Index n))
  have hr (j : Fin (n a.1)):=RationalPolynomialMap.comp (canonicalExp_polynomial (c a.1) j)
    (fun k=>RationalPolynomialMap.coordinate (Sum.inr (⟨a.1,k⟩ : Index n) : Index n ⊕ Index n))
  have hm:=polynomialMap_mul (c a.1) hl hr
  have hh:=RationalPolynomialMap.comp (canonicalLog_polynomial (c a.1) a.2) hm
  simp only [Homeomorph.symm_apply_apply] at hh
  exact hh

include hsk hA in
omit [Fintype ι] in
lemma law_weighted (a : Index n) : IsWeighted (Sum.elim (weight n w) (weight n w)) (weight n w a)
    (fun x=>FiniteWeightedLawChart.law (logCoordinates G n c) x a) := by
  have hi (j : Fin (n a.1) ⊕ Fin (n a.1)) :
      IsWeighted (Sum.elim (weight n w) (weight n w)) (Sum.elim (w a.1) (w a.1) j)
        (fun x : (Index n ⊕ Index n) → ℝ=>Sum.elim
          (fun k=>x (Sum.inl ⟨a.1,k⟩)) (fun k=>x (Sum.inr ⟨a.1,k⟩)) j) := by
    cases j with
    | inl j=>exact IsWeighted.coordinate (Sum.elim (weight n w) (weight n w)) (Sum.inl (⟨a.1,j⟩ : Index n))
    | inr j=>exact IsWeighted.coordinate (Sum.elim (weight n w) (weight n w)) (Sum.inr (⟨a.1,j⟩ : Index n))
  have hh:=(log_multiplication_weighted (c a.1) (hsk a.1) (A a.1) (w a.1) (hA a.1) a.2).comp hi
  exact hh

def chart : RealCoordinates (∀ i,G i) (Fintype.card (Index n)) :=
  FiniteWeightedLawChart.chart (logCoordinates G n c) (logCoordinates_one G n c)
    (weight n w) (fun a=>hw a.1 a.2) (law_polynomial G n c) (law_weighted G n c hsk A w hA)
def orderedWeight (i : Fin (Fintype.card (Index n))) : ℕ:=
  weight n w (SortedFiniteWeights.indexing (weight n w) i)
include hw in
lemma orderedWeight_positive (i : Fin (Fintype.card (Index n))) : 0<orderedWeight n w i:=hw _ _
lemma orderedWeight_monotone : Monotone (orderedWeight n w):=SortedFiniteWeights.indexing_monotone _

def level (k : ℕ) : Subgroup (∀ i,G i) where
  carrier:=fun g=>∀ i,g i∈(A i).level k
  one_mem':=fun i=>(A i).level k |>.one_mem
  mul_mem':=fun hg hh i=>((A i).level k).mul_mem (hg i) (hh i)
  inv_mem':=fun hg i=>((A i).level k).inv_mem (hg i)
def filtration : CubeFaces.Filtration (∀ i,G i) where
  level:=level G A
  antitone:=fun _ _ hjk _ hg i=>(A i).antitone hjk (hg i)
  commutator_le j k:=Subgroup.commutator_le.mpr (fun g hg h hh i=>
    Subgroup.commutator_le.mp ((A i).commutator_le j k) (g i) (hg i) (h i) (hh i))

include hmono in
lemma chart_adapted (k : ℕ) (g : ∀ i,G i) :
    g∈(filtration G A).level k ↔ ∀ j,orderedWeight n w j<k → (chart G n c hsk A w hw hA).coord g j=0 := by
  change (∀ i,g i∈(A i).level k) ↔ ∀ j,weight n w (SortedFiniteWeights.indexing (weight n w) j)<k →
    canonicalLog (c (SortedFiniteWeights.indexing (weight n w) j).1)
      (g (SortedFiniteWeights.indexing (weight n w) j).1) (SortedFiniteWeights.indexing (weight n w) j).2=0
  constructor
  · intro hg j
    exact (mem_level_iff_log (c _) (A _) (w _) (hmono _) (hA _) k _).mp (hg _) _
  · intro hg i
    apply (mem_level_iff_log (c i) (A i) (w i) (hmono i) (hA i) k _).mpr
    intro j hj
    obtain ⟨l,hl⟩:=(SortedFiniteWeights.indexing (weight n w)).surjective ⟨i,j⟩
    have hh:=hg l
    rw [hl] at hh
    exact hh hj

lemma chart_projection_polynomial (i : ι) (j : Fin (n i)) : RationalPolynomialMap.IsPolynomial
    (fun x : Fin (Fintype.card (Index n)) → ℝ=>
      (c i).coord (((chart G n c hsk A w hw hA).coord.symm x) i) j) := by
  have hh:=RationalPolynomialMap.comp (canonicalExp_polynomial (c i) j)
    (fun k=>RationalPolynomialMap.coordinate ((SortedFiniteWeights.indexing (weight n w)).symm ⟨i,k⟩))
  exact hh

lemma projection_rational (g : ∀ i,G i) (hg : IsRational (chart G n c hsk A w hw hA) g) (i : ι) :
    IsRational (c i) (g i) := by
  let F : (∀ i,G i) →* G i:={ toFun:=fun g=>g i,map_one':=rfl,map_mul':=fun _ _=>rfl }
  exact rationalHom_rational (c i) (chart G n c hsk A w hw hA) F
    (chart_projection_polynomial G n c hsk A w hw hA i) hg

end RationalLattice.FiniteProducts
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalLattice.PolynomialArrays
open MalcevCharacters CubePolynomials
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)
variable (hw : ∀ i,0<w i)

def constantElement (g : G) : group (q:=q) c hsk A w hA :=⟨fun _=>g,constant c w g⟩
def sourceElement (g x : G) (b : ℝ) (v : Fin q → ℝ) : group (q:=q) c hsk A w hA :=
  ⟨fun u=>realPower c g (b+∑ j,v j*u j)*x,source_array c hsk A w hA hw g x b v⟩

def sourceOrbit (g x : G) (t : ℤ) (b : ℝ) (v : Fin q → ℝ) (z : ℤ) :
    group (q:=q) c hsk A w hA :=
  constantElement c hsk A w hA (g^t)^z * sourceElement c hsk A w hA hw g x b v

lemma sourceOrbit_apply (g x : G) (t : ℤ) (b : ℝ) (v u : Fin q → ℝ) (z : ℤ) :
    (sourceOrbit c hsk A w hA hw g x t b v z).val u=
      realPower c g (b+(t:ℝ)*z+∑ j,v j*u j)*x := by
  change evaluate c hsk A w hA u (_^z * _)=_
  rw [map_mul,map_zpow]
  change (g^t)^z*(realPower c g (b+∑ j,v j*u j)*x)=_
  rw [← zpow_mul,← realPower_int c g,← mul_assoc,← realPower_add]
  congr 2
  push_cast
  ring

end RationalLattice.PolynomialArrays
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace WeightedPolynomial
open MvPolynomial
variable {σ : Type*}
lemma IsWeighted.scale {w : σ → ℕ} {d : ℕ} {f : (σ → ℝ) → ℝ}
    (hf : IsWeighted w d f) (D : ℕ) :
    IsWeighted (fun j=>D*w j) (D*d) f := by
  obtain ⟨p,hp,he⟩:=hf
  refine ⟨p,?_,he⟩
  intro m hm
  have H:=Nat.mul_le_mul_left D (hp m hm)
  have heq : Finsupp.weight (fun j=>D*w j) m=D*Finsupp.weight w m := by
    simp only [Finsupp.weight_apply,smul_eq_mul,Finsupp.sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simpa only [heq] using H
end WeightedPolynomial

namespace RationalLattice
open WeightedPolynomial MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
omit [IsTopologicalGroup G] in
lemma canonicalLog_natpow (g : G) (m : ℕ) :
    canonicalLog c (g^m)=(m:ℝ) • canonicalLog c g := by
  have H:=canonicalLog_realPower c g (m:ℝ)
  simpa only [realPower_nat] using H

variable (hsk : SecondKind c) (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i,w i<k → c.coord g i=0)
variable (hw : ∀ i,0<w i)
include hsk hA hw in
lemma power_translate_log_weighted {σ : Type*} {D : ℕ} {a : (σ → ℝ) → ℝ}
    (ha : IsWeighted (fun _ : σ=>1) D a) (g x : G) (i : Fin n) :
    IsWeighted (fun _ : σ=>1) (D*w i)
      (fun z=>canonicalLog c (realPower c g (a z)*x) i) := by
  have hs (j : Fin n ⊕ Fin n) : IsWeighted (fun _ : σ=>1) (D*Sum.elim w w j)
      (fun z=>Sum.elim (canonicalLog c (realPower c g (a z))) (canonicalLog c x) j) := by
    cases j with
    | inl j =>
      have hh:=(ha.mono (Nat.le_mul_of_pos_right D (hw j))).smul (canonicalLog c g j)
      simpa only [Sum.elim_inl,canonicalLog_realPower,Pi.smul_apply,smul_eq_mul,mul_comm] using hh
    | inr j => exact IsWeighted.const _ _ _
  have H:=((log_multiplication_weighted c hsk A w hA i).scale D).comp hs
  simpa only [Sum.elim_inl,Sum.elim_inr,canonicalExp_log] using H
end RationalLattice

namespace RationalLattice.PolynomialArrays
open WeightedPolynomial MalcevCharacters PolynomialArrayInterpolation
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i,w i<k → c.coord g i=0)
variable (hw : ∀ i,0<w i)

lemma coefficients_natpow (f : group (q:=q) c hsk A w hA) (m : ℕ) (a : Index w q) :
    coefficients c hsk A w hA (f^m) a=(m:ℝ)*coefficients c hsk A w hA f a := by
  change (∑ v : Grid q (w a.1), _ * canonicalLog c (f.val _ ^ m) a.1)=
    (m:ℝ)*∑ v : Grid q (w a.1),_ * canonicalLog c (f.val _) a.1
  simp only [canonicalLog_natpow,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

lemma chart_natpow (f : group (q:=q) c hsk A w hA) (m : ℕ)
    (i : Fin (Fintype.card (Index w q))) :
    (chart c hsk A w hA hw).coord (f^m) i=(m:ℝ)*(chart c hsk A w hA hw).coord f i :=
  coefficients_natpow c hsk A w hA f m _

 

lemma chart_canonicalLog (f : group (q:=q) c hsk A w hA) :
    canonicalLog (chart c hsk A w hA hw) f=(chart c hsk A w hA hw).coord f := by
  funext i
  have hp : powerPolynomial (chart c hsk A w hA hw) f i=
      Polynomial.X*Polynomial.C ((chart c hsk A w hA hw).coord f i) := by
    apply Polynomial.eq_of_eval_nat_eq
    intro m
    simp only [powerPolynomial_nat,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]
    exact chart_natpow c hsk A w hA hw f m i
  rw [canonicalLog,hp]
  simp

 

lemma source_joint_log_weighted {σ : Type*} {D : ℕ}
    {b : (σ → ℝ) → ℝ} {v : (σ → ℝ) → Fin q → ℝ}
    (hb : IsWeighted (fun _ : σ=>1) D b)
    (hv : ∀ j,IsWeighted (fun _ : σ=>1) D (fun z=>v z j))
    (g x : G) (i : Fin (Fintype.card (Index w q))) :
    IsWeighted (fun _ : σ=>1) (D*orderedWeight (q:=q) w i)
      (fun z=>canonicalLog (chart c hsk A w hA hw)
        (sourceElement c hsk A w hA hw g x (b z) (v z)) i) := by
  simp only [chart_canonicalLog]
  let a : Index w q:=SortedFiniteWeights.indexing (weight w) i
  change IsWeighted (fun _ : σ=>1) (D*w a.1)
    (fun z=>∑ u : Grid q (w a.1),(IntegerGridInterpolation.tensorWeight q (w a.1) a.2.val u:ℝ)*
      canonicalLog c (realPower c g (b z+∑ j,v z j*((u j).val:ℝ))*x) a.1)
  apply IsWeighted.sum
  intro u hu
  apply IsWeighted.smul
  apply power_translate_log_weighted c hsk A w hA hw
  apply hb.add
  apply IsWeighted.sum
  intro j hj
  simpa only [mul_comm] using (hv j).smul ((u j).val:ℝ)

end RationalLattice.PolynomialArrays

end
end
end

end OAI
