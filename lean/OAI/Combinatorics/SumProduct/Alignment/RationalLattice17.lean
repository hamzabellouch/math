import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice16
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators commutatorElement
end
 
end

section
 

 

noncomputable section
namespace TriangularDenominators
open MvPolynomial
lemma polynomial_partial_origin_grid {σ τ : Type*} (P : MvPolynomial (σ ⊕ τ) ℚ) :
    ∃ D : ℕ,0<D ∧ ∀ T : ℕ,∀ x : σ → ℤ,∀ y : τ → ℤ,∃ z : ℤ,
      eval (Sum.elim (fun i=>(D:ℚ)*(T:ℚ)*(x i:ℚ)) (fun j=>(y j:ℚ))) P-
        eval (Sum.elim (fun _=>0) (fun j=>(y j:ℚ))) P=(T:ℚ)*(z:ℚ) := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨1,by norm_num,fun T x y=>⟨0,by simp⟩⟩
  | add P Q hP hQ =>
    obtain ⟨D,hD,hP⟩:=hP
    obtain ⟨E,hE,hQ⟩:=hQ
    refine ⟨D*E,Nat.mul_pos hD hE,?_⟩
    intro T x y
    obtain ⟨a,ha⟩:=hP T (fun i=>(E:ℤ)*x i) y
    obtain ⟨b,hb⟩:=hQ T (fun i=>(D:ℤ)*x i) y
    have hDE : (fun i=>(D:ℚ)*(T:ℚ)*(((E:ℤ)*x i):ℚ))=
        (fun i=>((D*E:ℕ):ℚ)*(T:ℚ)*(x i:ℚ)) := by funext i; push_cast; ring
    have hED : (fun i=>(E:ℚ)*(T:ℚ)*(((D:ℤ)*x i):ℚ))=
        (fun i=>((D*E:ℕ):ℚ)*(T:ℚ)*(x i:ℚ)) := by funext i; push_cast; ring
    simp only [Int.cast_mul] at ha hb
    rw [hDE] at ha
    rw [hED] at hb
    refine ⟨a+b,?_⟩
    simp only [map_add,Int.cast_add]
    linarith
  | mul_X P a hP =>
    cases a with
    | inl i =>
      obtain ⟨D,hD,hgrid⟩:=polynomial_grid P 1 (by norm_num)
      refine ⟨D,hD,?_⟩
      intro T x y
      obtain ⟨a,ha⟩:=hgrid
        (Sum.elim (fun i=>(D:ℚ)*(T:ℚ)*(x i:ℚ)) (fun j=>(y j:ℚ))) (by
          intro j
          cases j with
          | inl j => exact ⟨(D:ℤ)*(T:ℤ)*x j,by simp⟩
          | inr j => exact ⟨y j,by simp⟩)
      refine ⟨a*x i,?_⟩
      simp only [map_mul,eval_X,Sum.elim_inl,mul_zero,sub_zero,Int.cast_mul]
      calc
        _=(T:ℚ)*((D:ℚ)*eval
          (Sum.elim (fun i=>(D:ℚ)*(T:ℚ)*(x i:ℚ)) (fun j=>(y j:ℚ))) P)*(x i:ℚ) := by ring
        _=_ := by rw [ha]; ring
    | inr j =>
      obtain ⟨D,hD,hP⟩:=hP
      refine ⟨D,hD,?_⟩
      intro T x y
      obtain ⟨a,ha⟩:=hP T x y
      refine ⟨a*y j,?_⟩
      simp only [map_mul,eval_X,Sum.elim_inr,Int.cast_mul]
      rw [← sub_mul,ha]
      ring

lemma polynomial_partial_origin_grid_real {σ τ : Type*} (P : MvPolynomial (σ ⊕ τ) ℚ) :
    ∃ D : ℕ,0<D ∧ ∀ T : ℕ,∀ x : σ → ℝ,∀ y : τ → ℤ,
      (∀ i,∃ z : ℤ,x i=((D*T:ℕ):ℝ)*(z:ℝ)) → ∃ z : ℤ,
      eval₂ (algebraMap ℚ ℝ) (Sum.elim x (fun j=>(y j:ℝ))) P-
        eval₂ (algebraMap ℚ ℝ) (Sum.elim (fun _=>0) (fun j=>(y j:ℝ))) P=(T:ℝ)*(z:ℝ) := by
  obtain ⟨D,hD,hP⟩:=polynomial_partial_origin_grid P
  refine ⟨D,hD,?_⟩
  intro T x y hx
  choose a ha using hx
  obtain ⟨z,hz⟩:=hP T a y
  refine ⟨z,?_⟩
  have he (v : (σ ⊕ τ) → ℚ) : ((eval v P:ℚ):ℝ)=
      eval₂ (algebraMap ℚ ℝ) (fun j=>(v j:ℝ)) P :=
    eval₂_comp_left (algebraMap ℚ ℝ) (RingHom.id ℚ) v P
  have hh:=congrArg (fun q : ℚ=>(q:ℝ)) hz
  simp only [Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast] at hh
  rw [he,he] at hh
  have hx' : (fun j=>((Sum.elim (fun i=>(D:ℚ)*(T:ℚ)*(a i:ℚ))
      (fun j=>(y j:ℚ)) j:ℚ):ℝ))=Sum.elim x (fun j=>(y j:ℝ)) := by
    funext j
    cases j with
    | inl i => simpa only [Sum.elim_inl,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast,Nat.cast_mul] using (ha i).symm
    | inr j => simp
  have hz' : (fun j=>((Sum.elim (fun _ : σ=>0) (fun j=>(y j:ℚ)) j:ℚ):ℝ))=
      Sum.elim (fun _ : σ=>0) (fun j=>(y j:ℝ)) := by funext j; cases j <;> simp
  rw [hx',hz'] at hh
  exact hh

end TriangularDenominators
end
 
end

section
 

 
noncomputable section
open scoped BigOperators
namespace RationalPolynomialMap
lemma power {σ : Type*} {f : (σ → ℝ) → ℝ} (hf : IsPolynomial f) (k : ℕ) :
    IsPolynomial (fun x=>f x^k) := by
  induction k with
  | zero => simpa using (const (σ:=σ) 1)
  | succ k ih => simpa only [pow_succ] using mul ih hf
lemma finset_prod {σ ι : Type*} (s : Finset ι) {f : ι → (σ → ℝ) → ℝ}
    (hf : ∀ i∈s,IsPolynomial (f i)) : IsPolynomial (fun x=>∏ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (σ:=σ) 1)
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))
end RationalPolynomialMap
namespace RationalLattice.PolynomialArrays
open PolynomialArrayInterpolation MalcevCharacters
open CorrectedBoxLeibman (gridEval)
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)
variable (hw : ∀ i,0<w i)

lemma toLog_joint_polynomial (i : Fin n) :
    RationalPolynomialMap.IsPolynomial (fun x : (Index w q ⊕ Fin q) → ℝ=>
      toLog w (fun a=>x (Sum.inl a)) (fun j=>x (Sum.inr j)) i) := by
  apply RationalPolynomialMap.finset_sum
  intro e he
  unfold fullCoeff
  split_ifs with hd
  · apply RationalPolynomialMap.mul (RationalPolynomialMap.coordinate _)
    apply RationalPolynomialMap.finset_prod
    intro j hj
    exact RationalPolynomialMap.power (RationalPolynomialMap.coordinate _) _
  · simpa only [zero_mul] using (RationalPolynomialMap.zero)

lemma toLog_zero (u : Fin q → ℝ) : toLog w 0 u=0 := by
  funext i
  unfold toLog gridEval
  apply Finset.sum_eq_zero
  intro e he
  simp only [fullCoeff,Pi.zero_apply,dite_eq_ite,ite_self,zero_mul]

omit [IsTopologicalGroup G] in
lemma joint_coordinates_polynomial (i : Fin n) :
    RationalPolynomialMap.IsPolynomial (fun x : (Index w q ⊕ Fin q) → ℝ=>
      c.coord (canonicalExp c (toLog w (fun a=>x (Sum.inl a)) (fun j=>x (Sum.inr j)))) i) := by
  have hh:=RationalPolynomialMap.comp (canonicalExp_polynomial c i) (toLog_joint_polynomial (q:=q) w)
  simpa only [Homeomorph.symm_apply_apply] using hh

omit [IsTopologicalGroup G] in
lemma coefficient_grid_lattice (Γ : Subgroup G)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z) :
    ∃ D : ℕ,0<D ∧ ∀ x : Index w q → ℝ,
      (∀ a,∃ z : ℤ,x a=(D:ℝ)*z) →
      ∀ u : Fin q → ℤ,canonicalExp c (toLog w x (fun j=>(u j:ℝ)))∈Γ := by
  classical
  have hi (i : Fin n) : ∃ D : ℕ,0<D ∧ ∀ x : Index w q → ℝ,
      (∀ a,∃ z : ℤ,x a=(D:ℝ)*z) → ∀ u : Fin q → ℤ,
      ∃ z : ℤ,c.coord (canonicalExp c (toLog w x (fun j=>(u j:ℝ)))) i=z := by
    obtain ⟨P,hP⟩:=joint_coordinates_polynomial c w (q:=q) i
    obtain ⟨D,hD,hgrid⟩:=TriangularDenominators.polynomial_partial_origin_grid_real P
    refine ⟨D,hD,?_⟩
    intro x hx u
    obtain ⟨z,hz⟩:=hgrid 1 x u (by simpa using hx)
    refine ⟨z,?_⟩
    rw [← hP,← hP] at hz
    have hzero : toLog w (fun _ : Index w q=>0) (fun j=>(u j:ℝ))=0 := toLog_zero w _
    simpa only [Sum.elim_inl,Sum.elim_inr,hzero,canonicalExp_zero,c.one_coord,sub_zero,
      Nat.cast_one,one_mul] using hz
  choose D hD hgrid using hi
  refine ⟨∏ i,D i,Finset.prod_pos (fun i _=>hD i),?_⟩
  intro x hx u
  apply (hΓ _).mpr
  intro i
  apply hgrid i x _ u
  intro a
  obtain ⟨z,hz⟩:=hx a
  obtain ⟨b,hb⟩:=Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  refine ⟨(b:ℤ)*z,?_⟩
  rw [hz,hb]
  push_cast
  ring

lemma chart_grid_lattice (Γ : Subgroup G)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z) :
    ∃ D : ℕ,0<D ∧ ∀ f : group (q:=q) c hsk A w hA,
      (∀ i,∃ z : ℤ,(chart c hsk A w hA hw).coord f i=(D:ℝ)*z) →
      f∈lattice c hsk A w hA Γ := by
  obtain ⟨D,hD,hgrid⟩:=coefficient_grid_lattice c w (q:=q) Γ hΓ
  refine ⟨D,hD,?_⟩
  intro f hf u
  have hg : ∀ a : Index w q,∃ z : ℤ,coefficients c hsk A w hA f a=(D:ℝ)*z := by
    intro a
    have hh:=hf ((SortedFiniteWeights.indexing (weight w)).symm a)
    change ∃ z : ℤ,coefficients c hsk A w hA f
      (SortedFiniteWeights.indexing (weight w) ((SortedFiniteWeights.indexing (weight w)).symm a))=(D:ℝ)*z at hh
    simpa only [Equiv.apply_symm_apply] using hh
  have hh:=hgrid (coefficients c hsk A w hA f) hg u
  simpa only [toLog_coefficients,canonicalExp_log] using hh

end RationalLattice.PolynomialArrays
end
 
end

section
 

 

noncomputable section
namespace RationalLattice.PolynomialArrays
open PolynomialArrayInterpolation MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)
variable (Γ : Subgroup G) [DiscreteTopology Γ]

lemma sampled_injective (d : ℕ) (hd : ∀ i,w i≤d) :
    Function.Injective (fun f : group (q:=q) c hsk A w hA=>
      fun v : Grid q d=>f.val (fun i=>((v i).val:ℝ))) := by
  intro f g hfg
  apply Subtype.ext
  funext u
  have he : canonicalLog c (f.val u)=canonicalLog c (g.val u) := by
    funext i
    have hh:=grid_injective ((f.property i).mono (hd i)) ((g.property i).mono (hd i))
      (fun v=>congrArg (fun a : G=>canonicalLog c a i) (congrFun hfg v))
    exact congrFun hh u
  calc f.val u = canonicalExp c (canonicalLog c (f.val u)) := (canonicalExp_log c _).symm
       _ = canonicalExp c (canonicalLog c (g.val u)) := congrArg (canonicalExp c) he
       _ = g.val u := canonicalExp_log c _

def latticeSample (d : ℕ) (f : lattice (q:=q) c hsk A w hA Γ) (v : Grid q d) : Γ:=
  ⟨f.val.val (fun i=>((v i).val:ℝ)),by
    simpa only [Int.cast_natCast] using f.property (fun i=>((v i).val:ℤ))⟩

omit [DiscreteTopology Γ] in
lemma latticeSample_continuous (d : ℕ) : Continuous (latticeSample (q:=q) c hsk A w hA Γ d) := by
  apply continuous_pi
  intro v
  apply Continuous.subtype_mk
  exact (continuous_apply _).comp (continuous_subtype_val.comp continuous_subtype_val)

lemma lattice_discrete : DiscreteTopology (lattice (q:=q) c hsk A w hA Γ) := by
  classical
  let d:=Finset.univ.sup w
  have hd (i : Fin n) : w i≤d:=Finset.le_sup (Finset.mem_univ i)
  apply DiscreteTopology.of_continuous_injective (latticeSample_continuous c hsk A w hA Γ d)
  intro f g hfg
  apply Subtype.ext
  apply sampled_injective c hsk A w hA d hd
  funext v
  exact congrArg Subtype.val (congrFun hfg v)

end RationalLattice.PolynomialArrays

end
end
end

end OAI
