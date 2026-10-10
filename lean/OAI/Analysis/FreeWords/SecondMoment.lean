import Mathlib
import OAI.Analysis.FreeWords.HaarMoment

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

open MeasureTheory Matrix

noncomputable section

theorem perm_two_cases (π : Equiv.Perm (Fin 2)) :
    π=Equiv.refl _ ∨ π=Equiv.swap 0 1 := by
  fin_cases π <;> decide

theorem sum_perm_two {A : Type*} [AddCommMonoid A] (f : Equiv.Perm (Fin 2) → A) :
    ∑ π,f π=f (Equiv.refl _)+f (Equiv.swap 0 1) := by
  have he : (Finset.univ : Finset (Equiv.Perm (Fin 2)))={Equiv.refl _,Equiv.swap 0 1} := by
    ext π
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    exact perm_two_cases π
  rw [he,Finset.sum_pair (by decide)]

@[simp] theorem positionMatrix_refl {r d : ℕ} :
    positionMatrix (d := d) (Equiv.refl (Fin r))=1 := by
  ext a b
  simp [positionMatrix,Matrix.one_apply,eq_comm]

@[simp] theorem pair_position_refl {d : ℕ} :
    matrixPair (positionMatrix (d := d) (Equiv.refl (Fin 2)))
      (positionMatrix (Equiv.refl (Fin 2)))=(d : ℂ)^2 := by
  simp [matrixPair,pow_two]

theorem pair_position_swap {d : ℕ} :
    matrixPair (positionMatrix (d := d) (Equiv.refl (Fin 2)))
      (positionMatrix (Equiv.swap 0 1))=(d : ℂ) := by
  simp only [positionMatrix_refl,matrixPair,star_one,one_mul,Matrix.trace,Matrix.diag,positionMatrix]
  have h (a : Fin 2 → Fin d) : a=a ∘ Equiv.swap 0 1 ↔ a 0=a 1 := by
    constructor
    · intro he; simpa using congrFun he 0
    · intro he; funext i; fin_cases i <;> simp [Function.comp_apply,he]
  simp_rw [h]
  calc
    _ = ∑ p : Fin d × Fin d, if p.1=p.2 then (1 : ℂ) else 0 :=
      Fintype.sum_equiv (finTwoArrowEquiv (Fin d)) _ _ (fun a => rfl)
    _ = _ := by rw [Fintype.sum_prod_type]; simp

@[simp] theorem pair_position_self {r d : ℕ} (π : Equiv.Perm (Fin r)) :
    matrixPair (positionMatrix (d := d) π) (positionMatrix π)=(d : ℂ)^r := by
  classical
  simp [matrixPair_apply,positionMatrix]

theorem pair_swap_refl {d : ℕ} :
    matrixPair (positionMatrix (d := d) (Equiv.swap (0 : Fin 2) 1))
      (positionMatrix (Equiv.refl (Fin 2)))=(d : ℂ) := by
  have hh : matrixPair (positionMatrix (d := d) (Equiv.swap (0 : Fin 2) 1)) 1 =
      star (matrixPair 1 (positionMatrix (d := d) (Equiv.swap (0 : Fin 2) 1))) := by
    simp [matrixPair,Matrix.trace,Matrix.diag,Matrix.star_apply]
  rw [positionMatrix_refl] at ⊢
  rw [hh]
  simpa only [positionMatrix_refl,star_natCast] using congrArg star (pair_position_swap (d := d))

theorem tensorAverage_column_pair (d : ℕ) (hd : 2 ≤ d) (z : Fin d) :
    tensorAverage (matrixHaar d) (Matrix.single (fun _ : Fin 2 => z) (fun _ => z) 1) =
      ((d : ℂ)*((d : ℂ)+1))⁻¹ •
        (1+positionMatrix (d := d) (Equiv.swap (0 : Fin 2) 1)) := by
  classical
  let b : Fin 2 → Fin d := fun _ => z
  let T : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ := Matrix.single b b 1
  obtain ⟨c,hc⟩ := tensorAverage_span 2 d hd (matrixHaar d) T
  have h0 := positionPair_average (matrixHaar d) (Equiv.refl (Fin 2)) T
  have h1 := positionPair_average (matrixHaar d) (Equiv.swap (0 : Fin 2) 1) T
  rw [hc,matrixPair_sum_smul,sum_perm_two] at h0 h1
  simp only [pair_position_swap,pair_swap_refl,pair_position_self] at h0 h1
  have hb (π : Equiv.Perm (Fin 2)) : matrixPair (positionMatrix (d := d) π) T=1 := by
    rw [matrixPair_single]
    simp [positionMatrix,b,Function.comp_def]
  rw [hb] at h0 h1
  have hn : (d : ℂ)≠0 := by exact_mod_cast (by omega : d≠0)
  have hn1 : (d : ℂ)-1≠0 := by
    have h : (1 : ℂ)≠(d : ℂ) := by exact_mod_cast (by omega : 1≠d)
    exact sub_ne_zero.mpr h.symm
  have hs : (d : ℂ)*((d : ℂ)+1)≠0 := by
    apply mul_ne_zero hn
    have h : (0 : ℝ)<(d : ℝ)+1 := by positivity
    exact_mod_cast ne_of_gt h
  have he : c (Equiv.refl (Fin 2))=c (Equiv.swap 0 1) := by
    have he : (c (Equiv.refl (Fin 2))-c (Equiv.swap 0 1))*((d : ℂ)*((d : ℂ)-1))=0 := by
      linear_combination h0-h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (mul_ne_zero hn hn1))
  have hv : c (Equiv.refl (Fin 2))=((d : ℂ)*((d : ℂ)+1))⁻¹ := by
    rw [← he] at h0
    rw [← one_div]
    apply (eq_div_iff hs).mpr
    linear_combination h0
  change tensorAverage (matrixHaar d) T=_
  rw [hc,sum_perm_two,← he,hv,positionMatrix_refl,smul_add]

theorem haar_column_fourth (d : ℕ) (hd : 2 ≤ d) (z i j k l : Fin d) :
    (∫ U : Matrix.unitaryGroup (Fin d) ℂ,
      (U : Matrix (Fin d) (Fin d) ℂ) i z * star ((U : Matrix (Fin d) (Fin d) ℂ) j z) *
      (U : Matrix (Fin d) (Fin d) ℂ) k z * star ((U : Matrix (Fin d) (Fin d) ℂ) l z)
      ∂matrixHaar d) =
    ((d : ℂ)*((d : ℂ)+1))⁻¹ *
      ((if i=j ∧ k=l then 1 else 0)+(if i=l ∧ k=j then 1 else 0)) := by
  classical
  have hh := congrArg (fun A : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ =>
    A ![i,k] ![j,l]) (tensorAverage_column_pair d hd z)
  rw [tensorAverage_single_apply] at hh
  have he : (![i,k] : Fin 2 → Fin d)=![j,l] ↔ i=j ∧ k=l := by simp [funext_iff,Fin.forall_fin_two]
  have he' : (![j,l] : Fin 2 → Fin d)=![i,k] ∘ Equiv.swap 0 1 ↔ i=l ∧ k=j := by
    simp [funext_iff,Fin.forall_fin_two,eq_comm,and_comm]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.one_apply,positionMatrix] at hh
  simp only [he,he'] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with U
  simp [tensorMatrix,Fin.prod_univ_two,star_mul]
  ring

end

end KKWeingarten
end

end OAI
