import OAI.Combinatorics.PolynomialVacuum.Algebra.BasePolynomials

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical
theorem basePolyThree_bound_0_0 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .zero .zero .zero).degreeOf 0 ≤ 2 := by
  have h0 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤1 := by simp
  have h1 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).degreeOf (0:Fin 3)≤2 := dpow h0 2
  have h2 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h3 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤2 := dmul h1 h2
  have h4 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h5 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤2 := dmul h1 h4
  have h6 : (((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤2 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).degreeOf (0:Fin 3)≤0 := dpow h2 2
  have h8 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h7 h0
  have h9 : ((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤2 := dadd (h6.trans (by omega)) (h8.trans (by omega))
  have h10 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h7 h4
  have h11 : (((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤2 := dadd (h9.trans (by omega)) (h10.trans (by omega))
  have h12 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).degreeOf (0:Fin 3)≤0 := dpow h4 2
  have h13 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h12 h0
  have h14 : ((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤2 := dadd (h11.trans (by omega)) (h13.trans (by omega))
  have h15 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h12 h2
  have h16 : (((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤2 := dadd (h14.trans (by omega)) (h15.trans (by omega))
  have h17 : ((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h18 : (((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h17 h0
  have h19 : ((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h18 h2
  have h20 : (((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h19 h4
  have h21 : ((((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))+((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤2 := dadd (h16.trans (by omega)) (h20.trans (by omega))
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h21

theorem basePolyThree_bound_0_1 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .zero .zero .zero).degreeOf 1 ≤ 2 := by
  have h0 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h1 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).degreeOf (1:Fin 3)≤0 := dpow h0 2
  have h2 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤1 := by simp
  have h3 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h1 h2
  have h4 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h5 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h1 h4
  have h6 : (((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤1 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).degreeOf (1:Fin 3)≤2 := dpow h2 2
  have h8 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤2 := dmul h7 h0
  have h9 : ((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤2 := dadd (h6.trans (by omega)) (h8.trans (by omega))
  have h10 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤2 := dmul h7 h4
  have h11 : (((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤2 := dadd (h9.trans (by omega)) (h10.trans (by omega))
  have h12 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).degreeOf (1:Fin 3)≤0 := dpow h4 2
  have h13 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h12 h0
  have h14 : ((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤2 := dadd (h11.trans (by omega)) (h13.trans (by omega))
  have h15 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h12 h2
  have h16 : (((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤2 := dadd (h14.trans (by omega)) (h15.trans (by omega))
  have h17 : ((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h18 : (((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h17 h0
  have h19 : ((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h18 h2
  have h20 : (((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h19 h4
  have h21 : ((((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))+((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤2 := dadd (h16.trans (by omega)) (h20.trans (by omega))
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h21

theorem basePolyThree_bound_0_2 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .zero .zero .zero).degreeOf 2 ≤ 2 := by
  have h0 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h1 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).degreeOf (2:Fin 3)≤0 := dpow h0 2
  have h2 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h3 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h1 h2
  have h4 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤1 := by simp
  have h5 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h1 h4
  have h6 : (((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).degreeOf (2:Fin 3)≤0 := dpow h2 2
  have h8 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h7 h0
  have h9 : ((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := dadd (h6.trans (by omega)) (h8.trans (by omega))
  have h10 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h7 h4
  have h11 : (((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := dadd (h9.trans (by omega)) (h10.trans (by omega))
  have h12 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).degreeOf (2:Fin 3)≤2 := dpow h4 2
  have h13 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤2 := dmul h12 h0
  have h14 : ((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤2 := dadd (h11.trans (by omega)) (h13.trans (by omega))
  have h15 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤2 := dmul h12 h2
  have h16 : (((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤2 := dadd (h14.trans (by omega)) (h15.trans (by omega))
  have h17 : ((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h18 : (((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h17 h0
  have h19 : ((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h18 h2
  have h20 : (((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h19 h4
  have h21 : ((((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))+((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤2 := dadd (h16.trans (by omega)) (h20.trans (by omega))
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h21

theorem basePolyThree_bound_1_0 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .plus .minus .zero).degreeOf 0 ≤ 1 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤1 := by simp
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h4 h5
  have h7 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤1 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h8 h1
  have h10 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤0 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (0:Fin 3)≤1 := dmul h7 h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (0:Fin 3)≤1 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_1_1 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .plus .minus .zero).degreeOf 1 ≤ 2 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤1 := by simp
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h0 h1
  have h3 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h4 h5
  have h7 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤0 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h8 h1
  have h10 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (1:Fin 3)≤1 := dmul h7 h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (1:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_1_2 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .plus .minus .zero).degreeOf 2 ≤ 2 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤1 := by simp
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h4 h5
  have h7 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h8 h1
  have h10 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (2:Fin 3)≤2 := dmul h7 h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (2:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_2_0 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .minus .plus .zero).degreeOf 0 ≤ 2 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤1 := by simp
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h0 h1
  have h3 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h4 h1
  have h6 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤1 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h8 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h7 h8
  have h10 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤0 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (0:Fin 3)≤1 := dmul h6 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (0:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_2_1 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .minus .plus .zero).degreeOf 1 ≤ 1 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h4 h1
  have h6 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤0 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h8 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤1 := by simp
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h7 h8
  have h10 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (1:Fin 3)≤1 := dmul h6 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (1:Fin 3)≤1 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_2_2 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .minus .plus .zero).degreeOf 2 ≤ 2 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤1 := by simp
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h4 h1
  have h6 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h8 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h7 h8
  have h10 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (2:Fin 3)≤2 := dmul h6 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (2:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_3_0 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .zero .plus .minus).degreeOf 0 ≤ 2 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤1 := by simp
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h4 h5
  have h7 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤1 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h8 h1
  have h10 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (0:Fin 3)≤2 := dmul h7 h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (0:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_3_1 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .zero .plus .minus).degreeOf 1 ≤ 1 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤1 := by simp
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h4 h5
  have h7 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤1 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h8 h1
  have h10 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤0 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (1:Fin 3)≤1 := dmul h7 h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (1:Fin 3)≤1 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_3_2 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .zero .plus .minus).degreeOf 2 ≤ 2 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤1 := by simp
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h0 h1
  have h3 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h4 h5
  have h7 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤0 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h8 h1
  have h10 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (2:Fin 3)≤1 := dmul h7 h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (2:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_4_0 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .zero .minus .plus).degreeOf 0 ≤ 2 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤1 := by simp
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h4 h1
  have h6 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤1 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h8 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h7 h8
  have h10 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (0:Fin 3)≤2 := dmul h6 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (0:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_4_1 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .zero .minus .plus).degreeOf 1 ≤ 2 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤1 := by simp
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h0 h1
  have h3 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤1 := dmul h4 h1
  have h6 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤1 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h8 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h7 h8
  have h10 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤0 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (1:Fin 3)≤1 := dmul h6 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (1:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_4_2 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .zero .minus .plus).degreeOf 2 ≤ 1 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h4 h1
  have h6 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤0 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h8 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤1 := by simp
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h7 h8
  have h10 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (2:Fin 3)≤1 := dmul h6 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (2:Fin 3)≤1 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_5_0 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .plus .zero .minus).degreeOf 0 ≤ 1 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h4 h1
  have h6 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤0 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h8 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤1 := by simp
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h7 h8
  have h10 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (0:Fin 3)≤1 := dmul h6 h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (0:Fin 3)≤1 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_5_1 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .plus .zero .minus).degreeOf 1 ≤ 2 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤1 := by simp
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h4 h1
  have h6 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤1 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h8 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h7 h8
  have h10 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (1:Fin 3)≤2 := dmul h6 h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (1:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_5_2 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .plus .zero .minus).degreeOf 2 ≤ 2 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤1 := by simp
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h0 h1
  have h3 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h4 h1
  have h6 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := dadd (h3.trans (by omega)) (h5.trans (by omega))
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h8 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h7 h8
  have h10 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤0 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (2:Fin 3)≤1 := dmul h6 h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (2:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_6_0 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .minus .zero .plus).degreeOf 0 ≤ 2 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤1 := by simp
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h0 h1
  have h3 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := by simp [degreeOf_X]
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤0 := dmul h4 h5
  have h7 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤0 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (0:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (0:Fin 3)≤1 := dmul h8 h1
  have h10 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (0:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (0:Fin 3)≤1 := dmul h7 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (0:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_6_1 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .minus .zero .plus).degreeOf 1 ≤ 2 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤1 := by simp
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := by simp [degreeOf_X]
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h4 h5
  have h7 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤1 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (1:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (1:Fin 3)≤0 := dmul h8 h1
  have h10 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (1:Fin 3)≤1 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (1:Fin 3)≤2 := dmul h7 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (1:Fin 3)≤2 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_bound_6_2 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .minus .zero .plus).degreeOf 2 ≤ 1 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤1 := by simp
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h4 h5
  have h7 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h8 h1
  have h10 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤0 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (2:Fin 3)≤1 := dmul h7 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (2:Fin 3)≤1 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyTwo_bound_0_0 :
    (basePolyTwo (X (0:Fin 2)) (X 1) .zero .zero).degreeOf 0 ≤ 1 := by
  have h0 : ((X (0:Fin 2) : MvPolynomial (Fin 2) ℂ)).degreeOf (0:Fin 2)≤1 := by simp
  have h1 : ((X (1:Fin 2) : MvPolynomial (Fin 2) ℂ)).degreeOf (0:Fin 2)≤0 := by simp [degreeOf_X]
  have h2 : (((X (0:Fin 2) : MvPolynomial (Fin 2) ℂ)+(X (1:Fin 2) : MvPolynomial (Fin 2) ℂ))).degreeOf (0:Fin 2)≤1 := dadd (h0.trans (by omega)) (h1.trans (by omega))
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h2

theorem basePolyTwo_bound_0_1 :
    (basePolyTwo (X (0:Fin 2)) (X 1) .zero .zero).degreeOf 1 ≤ 1 := by
  have h0 : ((X (0:Fin 2) : MvPolynomial (Fin 2) ℂ)).degreeOf (1:Fin 2)≤0 := by simp [degreeOf_X]
  have h1 : ((X (1:Fin 2) : MvPolynomial (Fin 2) ℂ)).degreeOf (1:Fin 2)≤1 := by simp
  have h2 : (((X (0:Fin 2) : MvPolynomial (Fin 2) ℂ)+(X (1:Fin 2) : MvPolynomial (Fin 2) ℂ))).degreeOf (1:Fin 2)≤1 := dadd (h0.trans (by omega)) (h1.trans (by omega))
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h2

theorem basePolyTwo_bound_1_0 :
    (basePolyTwo (X (0:Fin 2)) (X 1) .plus .minus).degreeOf 0 ≤ 0 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 2) ℂ)).degreeOf (0:Fin 2)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (1:Fin 2) : MvPolynomial (Fin 2) ℂ)).degreeOf (0:Fin 2)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 2) ℂ)*(X (1:Fin 2) : MvPolynomial (Fin 2) ℂ))).degreeOf (0:Fin 2)≤0 := dmul h0 h1
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h2

theorem basePolyTwo_bound_1_1 :
    (basePolyTwo (X (0:Fin 2)) (X 1) .plus .minus).degreeOf 1 ≤ 1 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 2) ℂ)).degreeOf (1:Fin 2)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (1:Fin 2) : MvPolynomial (Fin 2) ℂ)).degreeOf (1:Fin 2)≤1 := by simp
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 2) ℂ)*(X (1:Fin 2) : MvPolynomial (Fin 2) ℂ))).degreeOf (1:Fin 2)≤1 := dmul h0 h1
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h2

theorem basePolyTwo_bound_2_0 :
    (basePolyTwo (X (0:Fin 2)) (X 1) .minus .plus).degreeOf 0 ≤ 1 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 2) ℂ)).degreeOf (0:Fin 2)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (0:Fin 2) : MvPolynomial (Fin 2) ℂ)).degreeOf (0:Fin 2)≤1 := by simp
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 2) ℂ)*(X (0:Fin 2) : MvPolynomial (Fin 2) ℂ))).degreeOf (0:Fin 2)≤1 := dmul h0 h1
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h2

theorem basePolyTwo_bound_2_1 :
    (basePolyTwo (X (0:Fin 2)) (X 1) .minus .plus).degreeOf 1 ≤ 0 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 2) ℂ)).degreeOf (1:Fin 2)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (0:Fin 2) : MvPolynomial (Fin 2) ℂ)).degreeOf (1:Fin 2)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 2) ℂ)*(X (0:Fin 2) : MvPolynomial (Fin 2) ℂ))).degreeOf (1:Fin 2)≤0 := dmul h0 h1
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h2

theorem vacuumThree_degrees (s : Fin 3 → Spin) (j : Fin 3) :
    (vacuumThree s).degreeOf j≤2 ∧ (s j=Spin.plus → (vacuumThree s).degreeOf j≤1) := by
  fin_cases j
  · change (vacuumThree s).degreeOf (0:Fin 3)≤2 ∧ (s 0=Spin.plus → (vacuumThree s).degreeOf 0≤1)
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
    · have hb := basePolyThree_bound_0_0
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_3_0
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_4_0
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_5_0
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro _; exact hb.trans (by omega)
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_1_0
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro _; exact hb.trans (by omega)
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_6_0
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_2_0
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
  · change (vacuumThree s).degreeOf (1:Fin 3)≤2 ∧ (s 1=Spin.plus → (vacuumThree s).degreeOf 1≤1)
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
    · have hb := basePolyThree_bound_0_1
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_3_1
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro _; exact hb.trans (by omega)
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_4_1
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_5_1
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_1_1
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_6_1
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_2_1
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro _; exact hb.trans (by omega)
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
  · change (vacuumThree s).degreeOf (2:Fin 3)≤2 ∧ (s 2=Spin.plus → (vacuumThree s).degreeOf 2≤1)
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
    · have hb := basePolyThree_bound_0_2
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_3_2
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_4_2
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro _; exact hb.trans (by omega)
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_5_2
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_1_2
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_6_2
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro _; exact hb.trans (by omega)
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · have hb := basePolyThree_bound_2_2
      simp only [vacuumThree,h0,h1,h2]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
    · simp [vacuumThree,h0,h1,h2,basePolyThree]
theorem vacuumThree_minusZero : MinusZero vacuumThree := by
  intro s j h
  fin_cases j
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
    simp_all [vacuumThree,basePolyThree,basePolyThreeFactor,killSite_X,killSite_C]

theorem vacuumTwo_degrees (s : Fin 2 → Spin) (j : Fin 2) :
    (vacuumTwo s).degreeOf j≤1 ∧ (s j=Spin.plus → (vacuumTwo s).degreeOf j≤0) := by
  fin_cases j
  · change (vacuumTwo s).degreeOf (0:Fin 2)≤1 ∧ (s 0=Spin.plus → (vacuumTwo s).degreeOf 0≤0)
    cases h0 : s 0 <;> cases h1 : s 1
    · have hb := basePolyTwo_bound_0_0
      simp only [vacuumTwo,h0,h1]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · have hb := basePolyTwo_bound_1_0
      simp only [vacuumTwo,h0,h1]
      constructor
      · exact hb.trans (by omega)
      · intro _; exact hb.trans (by omega)
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · have hb := basePolyTwo_bound_2_0
      simp only [vacuumTwo,h0,h1]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumTwo,h0,h1,basePolyTwo]
  · change (vacuumTwo s).degreeOf (1:Fin 2)≤1 ∧ (s 1=Spin.plus → (vacuumTwo s).degreeOf 1≤0)
    cases h0 : s 0 <;> cases h1 : s 1
    · have hb := basePolyTwo_bound_0_1
      simp only [vacuumTwo,h0,h1]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · have hb := basePolyTwo_bound_1_1
      simp only [vacuumTwo,h0,h1]
      constructor
      · exact hb.trans (by omega)
      · intro h; cases h
    · simp [vacuumTwo,h0,h1,basePolyTwo]
    · have hb := basePolyTwo_bound_2_1
      simp only [vacuumTwo,h0,h1]
      constructor
      · exact hb.trans (by omega)
      · intro _; exact hb.trans (by omega)
    · simp [vacuumTwo,h0,h1,basePolyTwo]
theorem vacuumTwo_minusZero : MinusZero vacuumTwo := by
  intro s j h
  fin_cases j
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    simp_all [vacuumTwo,basePolyTwo,killSite_X,killSite_C]

end PolynomialVacuumAlgebra

end OAI
