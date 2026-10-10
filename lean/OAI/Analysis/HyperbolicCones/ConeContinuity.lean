import OAI.Analysis.HyperbolicCones.ConeMatrix

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem continuous_qMatrix : Continuous (qMatrix : (Fin 3 → ℝ) → Mat 3 ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : i = j
  · simp only [qMatrix, ite_eq_left h]
    fun_prop
  · simp only [qMatrix, ite_eq_right h]
    fun_prop

theorem continuous_phi :
    Continuous (fun z : (Fin 3 → ℝ) × Mat 4 ℝ => phi z.1 z.2) := by
  have hq : Continuous (fun z : (Fin 3 → ℝ) × Mat 4 ℝ => qMatrix z.1) :=
    continuous_qMatrix.comp continuous_fst
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [phi, Fin.cases_zero, Fin.cases_succ, Matrix.trace,
      Matrix.submatrix] <;> fun_prop

theorem continuous_phiSym_joint :
    Continuous (fun z : (Fin 3 → ℝ) × Sym 4 => phiSym z.1 z.2) := by
  let f : (Fin 3 → ℝ) × Sym 4 → (Fin 3 → ℝ) × Mat 4 ℝ :=
    fun z => (z.1, (z.2 : Mat 4 ℝ))
  have hf : Continuous f := continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun z : (Fin 3 → ℝ) × Sym 4 => phi z.1 (z.2 : Mat 4 ℝ)) :=
    continuous_phi.comp (f := f) hf
  exact hc.subtype_mk (fun z => phi_isHermitian z.1 (z.2 : Mat 4 ℝ) z.2.property)

end Paper256

end

end OAI
