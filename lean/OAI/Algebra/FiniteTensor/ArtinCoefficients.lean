import Mathlib

namespace OAI

/-! Finite coefficient equations and exact polynomial remainder reconstruction. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable {B R ι κ : Type*} [CommRing B] [CommRing R]

 
abbrev CoefficientVariables (p : ι → Polynomial R) :=
  (i : ι) × Fin ((p i).natDegree+1)

instance [Fintype ι] (p : ι → Polynomial R) : Fintype (CoefficientVariables p) := by
  unfold CoefficientVariables
  infer_instance

instance [DecidableEq ι] (p : ι → Polynomial R) : DecidableEq (CoefficientVariables p) := by
  unfold CoefficientVariables
  infer_instance

 
def coefficientPolynomial (p : ι → Polynomial R) (i : ι) :
    Polynomial (MvPolynomial (CoefficientVariables p) B) :=
  ∑ j : Fin ((p i).natDegree+1),
    Polynomial.C (MvPolynomial.X (⟨i,j⟩ : CoefficientVariables p))*Polynomial.X^j.val

 
def coefficientPoint (p : ι → Polynomial R) : CoefficientVariables p → R :=
  fun ij => (p ij.1).coeff ij.2

 
def realizeCoefficients (p : ι → Polynomial R) (x : CoefficientVariables p → R) (i : ι) :
    Polynomial R :=
  ∑ j : Fin ((p i).natDegree+1),Polynomial.C (x ⟨i,j⟩)*Polynomial.X^j.val

 theorem realizeCoefficients_original (p : ι → Polynomial R) (i : ι) :
    realizeCoefficients p (coefficientPoint p) i=p i := by
  simp only [realizeCoefficients,coefficientPoint]
  exact (Fin.sum_univ_eq_sum_range (fun j=>Polynomial.C ((p i).coeff j)*Polynomial.X^j)
    ((p i).natDegree+1)).trans (p i).as_sum_range_C_mul_X_pow.symm

 theorem map_coefficientPolynomial (φ : B →+* R) (p : ι → Polynomial R)
    (x : CoefficientVariables p → R) (i : ι) :
    (coefficientPolynomial (B:=B) p i).map (MvPolynomial.eval₂Hom φ x) =
      realizeCoefficients p x i := by
  unfold coefficientPolynomial realizeCoefficients
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (Polynomial.mapRingHom (MvPolynomial.eval₂Hom φ x))
    (Polynomial.C (MvPolynomial.X (⟨i,j⟩ : CoefficientVariables p))*Polynomial.X^j.val) = _
  rw [map_mul]
  simp only [Polynomial.coe_mapRingHom,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,
    MvPolynomial.eval₂Hom_X']

 
def coefficientRelation (p : ι → Polynomial R) (F : MvPolynomial ι (Polynomial B)) :
    Polynomial (MvPolynomial (CoefficientVariables p) B) :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom MvPolynomial.C)
    (coefficientPolynomial p) F

 theorem map_coefficientRelation (φ : B →+* R) (p : ι → Polynomial R)
    (x : CoefficientVariables p → R) (F : MvPolynomial ι (Polynomial B)) :
    (coefficientRelation p F).map (MvPolynomial.eval₂Hom φ x) =
      MvPolynomial.eval₂ (Polynomial.mapRingHom φ) (realizeCoefficients p x) F := by
  let e := MvPolynomial.eval₂Hom φ x
  have he : (Polynomial.mapRingHom e).comp
      (MvPolynomial.eval₂Hom (Polynomial.mapRingHom MvPolynomial.C) (coefficientPolynomial p)) =
      MvPolynomial.eval₂Hom (Polynomial.mapRingHom φ) (realizeCoefficients p x) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_C,Polynomial.coe_mapRingHom,
        Polynomial.map_map]
      congr 1
      ext b
      simp [e]
    · intro i
      simp only [RingHom.comp_apply,MvPolynomial.eval₂Hom_X',Polynomial.coe_mapRingHom]
      exact map_coefficientPolynomial φ p x i
  exact RingHom.congr_fun he F

 
abbrev CoefficientEquations (p : ι → Polynomial R) (F : κ → MvPolynomial ι (Polynomial B)) :=
  (k : κ) × Fin ((coefficientRelation p (F k)).natDegree+1)

instance [Fintype κ] (p : ι → Polynomial R) (F : κ → MvPolynomial ι (Polynomial B)) :
    Fintype (CoefficientEquations p F) := by unfold CoefficientEquations; infer_instance

instance [DecidableEq κ] (p : ι → Polynomial R) (F : κ → MvPolynomial ι (Polynomial B)) :
    DecidableEq (CoefficientEquations p F) := by unfold CoefficientEquations; infer_instance

 def coefficientEquation (p : ι → Polynomial R) (F : κ → MvPolynomial ι (Polynomial B))
    (kn : CoefficientEquations p F) : MvPolynomial (CoefficientVariables p) B :=
   (coefficientRelation p (F kn.1)).coeff kn.2

 

 theorem coefficient_equations_iff (φ : B →+* R) (p : ι → Polynomial R)
    (F : κ → MvPolynomial ι (Polynomial B)) (x : CoefficientVariables p → R) :
    (∀ kn,MvPolynomial.eval₂ φ x (coefficientEquation p F kn)=0) ↔
      ∀ k,MvPolynomial.eval₂ (Polynomial.mapRingHom φ) (realizeCoefficients p x) (F k)=0 := by
  constructor
  · intro hx k
    rw [←map_coefficientRelation]
    ext j
    rw [Polynomial.coeff_map,Polynomial.coeff_zero]
    by_cases hj : j<(coefficientRelation p (F k)).natDegree+1
    · exact hx ⟨k,⟨j,hj⟩⟩
    · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (p:=coefficientRelation p (F k))
        (show (coefficientRelation p (F k)).natDegree<j by omega)
      simp [hz]
  · intro hx kn
    have he := congrArg (Polynomial.coeff · kn.2) (hx kn.1)
    rw [←map_coefficientRelation φ p x] at he
    simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,coefficientEquation,MvPolynomial.coe_eval₂Hom] using he

 theorem coefficient_equations_original (φ : B →+* R) (p : ι → Polynomial R)
    (F : κ → MvPolynomial ι (Polynomial B))
    (hp : ∀ k,MvPolynomial.eval₂ (Polynomial.mapRingHom φ) p (F k)=0) :
    ∀ kn,MvPolynomial.eval₂ φ (coefficientPoint p) (coefficientEquation p F kn)=0 := by
  apply (coefficient_equations_iff φ p F (coefficientPoint p)).mpr
  have he : realizeCoefficients p (coefficientPoint p)=p := funext (realizeCoefficients_original p)
  rwa [he]

 theorem realizeCoefficients_degree (p : ι → Polynomial R)
    (x : CoefficientVariables p → R) (i : ι) :
    (realizeCoefficients p x i).degree ≤ (p i).natDegree := by
  unfold realizeCoefficients
  apply (Polynomial.degree_sum_le _ _).trans
  apply Finset.sup_le
  intro j hj
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  exact (Polynomial.degree_monomial_le _ _).trans
    (WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ j.isLt))

 theorem realizeCoefficients_coeff (p : ι → Polynomial R)
    (x : CoefficientVariables p → R) (i : ι) (j : Fin ((p i).natDegree+1)) :
    (realizeCoefficients p x i).coeff j.val=x ⟨i,j⟩ := by
  simp only [realizeCoefficients,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    have h : j.val≠b.val := fun h=>hbj (Fin.ext h.symm)
    simp [h]
  · simp

 

 theorem realizeCoefficients_close (p : ι → Polynomial R)
    (x : CoefficientVariables p → R) (I : Ideal R)
    (hx : ∀ v,x v-coefficientPoint p v∈I) (i : ι) (j : ℕ) :
    (realizeCoefficients p x i).coeff j-(p i).coeff j∈I := by
  by_cases hj : j<(p i).natDegree+1
  · exact (realizeCoefficients_coeff p x i ⟨j,hj⟩) ▸ hx ⟨i,⟨j,hj⟩⟩
  · have hlt : (p i).natDegree<j := by omega
    have hd := realizeCoefficients_degree p x i
    have hz : (realizeCoefficients p x i).coeff j=0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (hd.trans_lt (WithBot.coe_lt_coe.mpr hlt))
    simp only [hz,Polynomial.coeff_eq_zero_of_natDegree_lt hlt,sub_self]
    exact I.zero_mem

end
end PD4Tensor.Spreading

 

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable {B A : Type*} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]

omit [IsDomain B] in
 theorem algebraic_coefficient_series {a : A} (ha : IsAlgebraic B a) :
    IsAlgebraic (Polynomial B) (PowerSeries.C a) := by
  apply ha.ringHom_of_comp_eq (Polynomial.C : B →+* Polynomial B)
    (PowerSeries.C : A →+* PowerSeries A) Polynomial.C_injective
  ext b
  simp [PowerSeries.algebraMap_apply']

 theorem polynomial_series_algebraic_coefficients (p : Polynomial A)
    (hp : ∀ n,IsAlgebraic B (p.coeff n)) :
    IsAlgebraic (Polynomial B) (p : PowerSeries A) := by
  let C := Subalgebra.algebraicClosure (Polynomial B) (PowerSeries A)
  change (p : PowerSeries A)∈C
  rw [p.as_sum_range_C_mul_X_pow]
  rw [←Polynomial.coeToPowerSeries.ringHom_apply,map_sum]
  simp only [map_mul,map_pow,Polynomial.coeToPowerSeries.ringHom_apply,Polynomial.coe_C,Polynomial.coe_X]
  apply C.sum_mem
  intro i hi
  apply C.mul_mem
  · exact algebraic_coefficient_series (hp i)
  · apply C.pow_mem
    have hx : (PowerSeries.X : PowerSeries A)=
        algebraMap (Polynomial B) (PowerSeries A) Polynomial.X := by
      simp [PowerSeries.algebraMap_apply']
    rw [hx]
    exact C.algebraMap_mem _

 
 theorem polynomial_coefficient_close (p q : Polynomial A) (I : Ideal A)
    (h : ∀ j,p.coeff j-q.coeff j∈I) :
    p-q∈I.map (Polynomial.C : A →+* Polynomial A) := by
  rw [Ideal.mem_map_C_iff]
  intro j
  simpa only [Polynomial.coeff_sub] using h j

 

 theorem polynomial_series_close (p q : Polynomial A) (I : Ideal A)
    (h : ∀ j,p.coeff j-q.coeff j∈I) :
    (p : PowerSeries A)-(q : PowerSeries A)∈I.map (PowerSeries.C : A →+* PowerSeries A) := by
  have hm := Ideal.mem_map_of_mem Polynomial.coeToPowerSeries.ringHom (polynomial_coefficient_close p q I h)
  rw [Ideal.map_map] at hm
  have he : Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.C : A →+* Polynomial A)=PowerSeries.C := by
    ext a; simp
  rw [he] at hm
  simpa only [Polynomial.coeToPowerSeries.ringHom_apply,Polynomial.coe_sub] using hm

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {B A ι : Type*} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]

 theorem realizeCoefficients_algebraic (p : ι → Polynomial A)
    (x : CoefficientVariables p → A) (hx : ∀ v,IsAlgebraic B (x v))
    (i : ι) (j : ℕ) : IsAlgebraic B ((realizeCoefficients p x i).coeff j) := by
  by_cases hj : j<(p i).natDegree+1
  · rw [realizeCoefficients_coeff p x i ⟨j,hj⟩]
    exact hx ⟨i,⟨j,hj⟩⟩
  · have hd := realizeCoefficients_degree p x i
    rw [Polynomial.coeff_eq_zero_of_degree_lt
      (hd.trans_lt (WithBot.coe_lt_coe.mpr (by omega : (p i).natDegree<j)))]
    exact isAlgebraic_zero

 theorem realizeCoefficients_series_algebraic (p : ι → Polynomial A)
    (x : CoefficientVariables p → A) (hx : ∀ v,IsAlgebraic B (x v)) (i : ι) :
    IsAlgebraic (Polynomial B) (realizeCoefficients p x i : PowerSeries A) :=
  polynomial_series_algebraic_coefficients _ (realizeCoefficients_algebraic p x hx i)

 theorem realizeCoefficients_series_close (p : ι → Polynomial A)
    (x : CoefficientVariables p → A) (I : Ideal A)
    (hx : ∀ v,x v-coefficientPoint p v∈I) (i : ι) :
    (realizeCoefficients p x i : PowerSeries A)-(p i : PowerSeries A)∈
      I.map (PowerSeries.C : A →+* PowerSeries A) :=
  polynomial_series_close _ _ I (realizeCoefficients_close p x I hx i)

end
section
variable {A : Type*} [CommRing A] [Nontrivial A]

 

theorem monic_coefficient_close_ne_zero (I : Ideal A) (hI : I≤Ideal.jacobson (⊥ : Ideal A))
    (p q : Polynomial A) (hp : p.Monic)
    (hq : ∀ j,q.coeff j-p.coeff j∈I) : q≠0 := by
  have hc := hI (hq p.natDegree)
  rw [hp.coeff_natDegree] at hc
  have hu := Ideal.isUnit_of_sub_one_mem_jacobson_bot (q.coeff p.natDegree) hc
  intro hz
  simp [hz] at hu

end
end PD4Tensor.Spreading
end

end OAI
