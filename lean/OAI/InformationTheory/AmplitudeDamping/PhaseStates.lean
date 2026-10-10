import OAI.InformationTheory.AmplitudeDamping.EnsembleBounds

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

/-- Entropy of any Hermitian trace-one two-level matrix, expressed through its determinant. -/
theorem entropy_qubit {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.IsHermitian)
    (htr : P.trace=1) : entropy P = g P.det.re := by
  let a := hP.eigenvalues 0
  let b := hP.eigenvalues 1
  have hab : a+b=1 := by
    have h := congrArg Complex.re (hP.trace_eq_sum_eigenvalues.symm.trans htr)
    simpa [Fin.sum_univ_two,a,b] using h
  have hd : P.det.re=a*b := by
    rw [hP.det_eq_prod_eigenvalues,Fin.prod_univ_two]
    simp [a,b]
  have he : entropy P=Real.negMulLog a+Real.negMulLog b := by
    rw [entropy_eq_sum hP,Fin.sum_univ_two]
  have hdisc : 1-4*P.det.re=(a-b)^2 := by rw [hd]; nlinarith only [hab]
  rw [he,g,hdisc,Real.sqrt_sq_eq_abs]
  by_cases h : b ≤ a
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have ht : (1+(a-b))/2=a := by linarith
    rw [ht,Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    congr 1
    congr 1
    linarith
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
    have ht : (1+ -(a-b))/2=b := by linarith
    rw [ht,Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    have ht' : 1-b=a := by linarith
    rw [ht']; ring

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

def phaseOutput (γ ν p : ℝ) (s : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  applyKraus (kraus γ ν) (pure (phaseSignal p s))

theorem phaseSignal_mass {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    vecMass (phaseSignal p s) = 1 := by
  simp only [vecMass,Fin.sum_univ_two,phaseSignal,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false]
  split_ifs <;> simp [Complex.normSq_ofReal,Real.mul_self_sqrt hp.1,
    Real.mul_self_sqrt (sub_nonneg.mpr hp.2)]

theorem phaseOutput_state (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    IsState (phaseOutput γ ν p s) := by
  refine ⟨applyKraus_posSemidef _ (pure_posSemidef _), ?_⟩
  exact (applyKraus_trace _ (kraus_complete γ ν hγ hν) _).trans (pure_state (phaseSignal_mass hp s)).2

theorem phaseOutput_formula (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    phaseOutput γ ν p s =
      !![((1-((1-γ)*p+γ*ν) : ℝ):ℂ),
          ((if s=0 then 1 else -1 : ℝ)*Real.sqrt (1-γ)*Real.sqrt (1-p)*Real.sqrt p : ℂ);
         ((if s=0 then 1 else -1 : ℝ)*Real.sqrt (1-γ)*Real.sqrt (1-p)*Real.sqrt p : ℂ),
          (((1-γ)*p+γ*ν : ℝ):ℂ)] := by
  rw [phaseOutput,local_channel γ ν hγ hν]
  have hsp : (Real.sqrt p : ℂ)^2=(p:ℂ) := by exact_mod_cast Real.sq_sqrt hp.1
  have hs1p : (Real.sqrt (1-p) : ℂ)^2=(1-p:ℂ) := by exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hp.2)
  ext i j
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp [pure,phaseSignal,Matrix.of_apply,Complex.ofReal_mul,Complex.ofReal_sub] <;>
    ring_nf <;> simp only [hsp,hs1p] <;> ring

theorem phaseOutput_det (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    (phaseOutput γ ν p s).det.re=v γ ν p := by
  rw [phaseOutput_formula γ ν hγ hν hp s,Matrix.det_fin_two]
  have hγ' := Real.sq_sqrt (sub_nonneg.mpr hγ.2)
  have hp' := Real.sq_sqrt (sub_nonneg.mpr hp.2)
  have hp'' := Real.sq_sqrt hp.1
  simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    ← Complex.ofReal_mul,← Complex.ofReal_sub,Complex.ofReal_re]
  split_ifs <;> dsimp only [v] <;>
    ring_nf <;> rw [hγ', hp', hp''] <;> ring

theorem phaseOutput_entropy (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    entropy (phaseOutput γ ν p s)=g (v γ ν p) := by
  rw [entropy_qubit (phaseOutput_state γ ν hγ hν hp s).1.isHermitian
    (phaseOutput_state γ ν hγ hν hp s).2,phaseOutput_det γ ν hγ hν hp s]

theorem phaseOutput_average (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (1/2:ℝ) • phaseOutput γ ν p 0+(1/2:ℝ) • phaseOutput γ ν p 1 =
      Matrix.diagonal (fun b : Fin 2 ↦ ((if b=0 then 1-((1-γ)*p+γ*ν) else (1-γ)*p+γ*ν : ℝ):ℂ)) := by
  rw [phaseOutput_formula γ ν hγ hν hp 0,phaseOutput_formula γ ν hγ hν hp 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring

theorem phaseOutput_average_entropy (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    entropy ((1/2:ℝ) • phaseOutput γ ν p 0+(1/2:ℝ) • phaseOutput γ ν p 1) =
      Real.binEntropy ((1-γ)*p+γ*ν) := by
  rw [phaseOutput_average γ ν hγ hν hp,entropy_diagonal]
  simp [Fin.sum_univ_two,Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,add_comm]

end GAD

end

end OAI
