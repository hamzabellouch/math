import OAI.Combinatorics.PolynomialVacuum.Algebra.BasePolynomials

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical
theorem basePolyTwo_homogeneous_0 :
    (basePolyTwo (X (0:Fin 2)) (X (1:Fin 2)) .zero .zero).IsHomogeneous 1 := by
  have h0 : ((X (0:Fin 2) : MvPolynomial (Fin 2) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h1 : ((X (1:Fin 2) : MvPolynomial (Fin 2) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h2 : (((X (0:Fin 2) : MvPolynomial (Fin 2) ℂ)+(X (1:Fin 2) : MvPolynomial (Fin 2) ℂ))).IsHomogeneous 1 := h0.add h1
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h2

theorem basePolyTwo_homogeneous_1 :
    (basePolyTwo (X (0:Fin 2)) (X (1:Fin 2)) .plus .minus).IsHomogeneous 1 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 2) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h1 : ((X (1:Fin 2) : MvPolynomial (Fin 2) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 2) ℂ)*(X (1:Fin 2) : MvPolynomial (Fin 2) ℂ))).IsHomogeneous 1 := h0.mul h1
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h2

theorem basePolyTwo_homogeneous_2 :
    (basePolyTwo (X (0:Fin 2)) (X (1:Fin 2)) .minus .plus).IsHomogeneous 1 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 2) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h1 : ((X (0:Fin 2) : MvPolynomial (Fin 2) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 2) ℂ)*(X (0:Fin 2) : MvPolynomial (Fin 2) ℂ))).IsHomogeneous 1 := h0.mul h1
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h2

theorem vacuumTwo_homogeneous (s : Fin 2 → Spin) :
    (vacuumTwo s).IsHomogeneous ((2:ℕ).choose 2) := by
  rw [show (2:ℕ).choose 2=1 from by decide]
  cases h0 : s 0 <;> cases h1 : s 1
  · simpa only [vacuumTwo,h0,h1] using basePolyTwo_homogeneous_0
  · simp only [vacuumTwo,h0,h1,basePolyTwo]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumTwo,h0,h1,basePolyTwo]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumTwo,h0,h1,basePolyTwo]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumTwo,h0,h1,basePolyTwo]; exact isHomogeneous_zero _ _ _
  · simpa only [vacuumTwo,h0,h1] using basePolyTwo_homogeneous_1
  · simp only [vacuumTwo,h0,h1,basePolyTwo]; exact isHomogeneous_zero _ _ _
  · simpa only [vacuumTwo,h0,h1] using basePolyTwo_homogeneous_2
  · simp only [vacuumTwo,h0,h1,basePolyTwo]; exact isHomogeneous_zero _ _ _
theorem vacuumTwo_charge (s : Fin 2 → Spin) (h : (∑ j, charge (s j))≠0) :
    vacuumTwo s=0 := by
  cases h0 : s 0 <;> cases h1 : s 1 <;>
    simp_all [vacuumTwo,basePolyTwo,Fin.sum_univ_succ,charge]

theorem basePolyThree_homogeneous_0 :
    (basePolyThree (X (0:Fin 3)) (X (1:Fin 3)) (X (2:Fin 3)) .zero .zero .zero).IsHomogeneous 3 := by
  have h0 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h1 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).IsHomogeneous 2 := h0.pow 2
  have h2 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h3 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 3 := h1.mul h2
  have h4 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h5 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 3 := h1.mul h4
  have h6 : (((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 3 := h3.add h5
  have h7 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).IsHomogeneous 2 := h2.pow 2
  have h8 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 3 := h7.mul h0
  have h9 : ((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 3 := h6.add h8
  have h10 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 3 := h7.mul h4
  have h11 : (((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 3 := h9.add h10
  have h12 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)).IsHomogeneous 2 := h4.pow 2
  have h13 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 3 := h12.mul h0
  have h14 : ((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 3 := h11.add h13
  have h15 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 3 := h12.mul h2
  have h16 : (((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 3 := h14.add h15
  have h17 : ((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h18 : (((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h17.mul h0
  have h19 : ((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 2 := h18.mul h2
  have h20 : (((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 3 := h19.mul h4
  have h21 : ((((((((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))+(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))+(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)^2)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))+((((C (2*(q^2-q^6)) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 3 := h16.add h20
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h21

theorem basePolyThree_homogeneous_1 :
    (basePolyThree (X (0:Fin 3)) (X (1:Fin 3)) (X (2:Fin 3)) .plus .minus .zero).IsHomogeneous 3 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h1 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h0.mul h1
  have h3 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h5 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h4.mul h5
  have h7 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.add h6
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h8.mul h1
  have h10 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.sub h9
  have h11 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))))).IsHomogeneous 2 := h7.mul h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).IsHomogeneous 3 := h2.mul h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_homogeneous_2 :
    (basePolyThree (X (0:Fin 3)) (X (1:Fin 3)) (X (2:Fin 3)) .minus .plus .zero).IsHomogeneous 3 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h1 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h0.mul h1
  have h3 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h4.mul h1
  have h6 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.add h5
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h8 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h7.mul h8
  have h10 : (((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.sub h9
  have h11 : ((((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))))).IsHomogeneous 2 := h6.mul h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).IsHomogeneous 3 := h2.mul h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_homogeneous_3 :
    (basePolyThree (X (0:Fin 3)) (X (1:Fin 3)) (X (2:Fin 3)) .zero .plus .minus).IsHomogeneous 3 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h1 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h0.mul h1
  have h3 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h5 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h4.mul h5
  have h7 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.add h6
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h8.mul h1
  have h10 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.sub h9
  have h11 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))))).IsHomogeneous 2 := h7.mul h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).IsHomogeneous 3 := h2.mul h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_homogeneous_4 :
    (basePolyThree (X (0:Fin 3)) (X (1:Fin 3)) (X (2:Fin 3)) .zero .minus .plus).IsHomogeneous 3 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h1 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h0.mul h1
  have h3 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h4.mul h1
  have h6 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.add h5
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h8 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h7.mul h8
  have h10 : (((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.sub h9
  have h11 : ((((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))))).IsHomogeneous 2 := h6.mul h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).IsHomogeneous 3 := h2.mul h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_homogeneous_5 :
    (basePolyThree (X (0:Fin 3)) (X (1:Fin 3)) (X (2:Fin 3)) .plus .zero .minus).IsHomogeneous 3 := by
  have h0 : ((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h1 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h2 : (((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h0.mul h1
  have h3 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h5 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h4.mul h1
  have h6 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.add h5
  have h7 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h8 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h7.mul h8
  have h10 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.sub h9
  have h11 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))))).IsHomogeneous 2 := h6.mul h10
  have h12 : ((((C (q^5-q^7) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).IsHomogeneous 3 := h2.mul h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem basePolyThree_homogeneous_6 :
    (basePolyThree (X (0:Fin 3)) (X (1:Fin 3)) (X (2:Fin 3)) .minus .zero .plus).IsHomogeneous 3 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h1 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h0.mul h1
  have h3 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h5 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 1 := isHomogeneous_X _ _
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h4.mul h5
  have h7 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.add h6
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).IsHomogeneous 0 := isHomogeneous_C _ _
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).IsHomogeneous 1 := h8.mul h1
  have h10 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).IsHomogeneous 1 := h3.sub h9
  have h11 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))))).IsHomogeneous 2 := h7.mul h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).IsHomogeneous 3 := h2.mul h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

theorem vacuumThree_homogeneous (s : Fin 3 → Spin) :
    (vacuumThree s).IsHomogeneous ((3:ℕ).choose 2) := by
  rw [show (3:ℕ).choose 2=3 from by decide]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  · simpa only [vacuumThree,h0,h1,h2] using basePolyThree_homogeneous_0
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simpa only [vacuumThree,h0,h1,h2] using basePolyThree_homogeneous_3
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simpa only [vacuumThree,h0,h1,h2] using basePolyThree_homogeneous_4
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simpa only [vacuumThree,h0,h1,h2] using basePolyThree_homogeneous_5
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simpa only [vacuumThree,h0,h1,h2] using basePolyThree_homogeneous_1
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simpa only [vacuumThree,h0,h1,h2] using basePolyThree_homogeneous_6
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simpa only [vacuumThree,h0,h1,h2] using basePolyThree_homogeneous_2
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
  · simp only [vacuumThree,h0,h1,h2,basePolyThree]; exact isHomogeneous_zero _ _ _
theorem vacuumThree_charge (s : Fin 3 → Spin) (h : (∑ j, charge (s j))≠0) :
    vacuumThree s=0 := by
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
    simp_all [vacuumThree,basePolyThree,Fin.sum_univ_succ,charge]

end PolynomialVacuumAlgebra

end OAI
