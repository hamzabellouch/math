import Mathlib

namespace OAI

namespace PolynomialVacuumCylinder
open Matrix

 
theorem normalized_gram_trace {n : ℕ} (A C V : Matrix (Fin n) (Fin n) ℝ)
    (hV : IsUnit V) (hn : star V*A*V=1) :
    (star V*C*V).trace=(A⁻¹*C).trace := by
  have hs : IsUnit (star V).det := (Matrix.isUnit_iff_isUnit_det _).mp hV.star
  have hi := Matrix.nonsing_inv_mul (star V) hs
  have hh := congrArg (fun X : Matrix (Fin n) (Fin n) ℝ=>(star V)⁻¹*X*star V) hn
  have he : A*(V*star V)=1 := by
    simpa only [←mul_assoc,hi,one_mul,mul_one] using hh
  have hv : V*star V=A⁻¹ := (Matrix.inv_eq_right_inv he).symm
  rw [Matrix.trace_mul_cycle, hv]

 

theorem normalized_gram_logdet {n : ℕ} (A B V : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (hA : 0<A.det) (hB : 0<B.det) (hd : ∀ i, 0<d i)
    (hn : star V*A*V=1) (he : star V*B*V=diagonal d) :
    Real.log B.det-Real.log A.det=∑ i,Real.log (d i) := by
  have hn' := congrArg Matrix.det hn
  have he' := congrArg Matrix.det he
  simp only [det_mul,star_eq_conjTranspose,det_conjTranspose,star_trivial,det_one] at hn'
  simp only [det_mul,star_eq_conjTranspose,det_conjTranspose,star_trivial,det_diagonal] at he'
  have hr : B.det/A.det=∏ i,d i := by
    calc
      _ = (V.det*A.det*V.det)*(B.det/A.det) := by rw [hn',one_mul]
      _ = V.det*B.det*V.det := by field_simp [hA.ne']
      _ = _ := he'
  rw [←Real.log_div hB.ne' hA.ne',hr]
  exact Real.log_prod fun i _=>(hd i).ne'

end PolynomialVacuumCylinder

end OAI
