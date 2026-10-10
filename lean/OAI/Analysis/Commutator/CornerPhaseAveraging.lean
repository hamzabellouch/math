import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.CornerPhase

section Fourier

variable {N : ℕ} [NeZero N]

lemma character_sum (a : ZMod N) :
    (∑ m : ZMod N, ZMod.stdAddChar (a*m))=if a=0 then (N:ℂ) else 0 := by
  classical
  split_ifs with ha
  · simp [ha]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ha)

lemma character_orthogonality (i j : ZMod N) :
    (∑ m : ZMod N, star (ZMod.stdAddChar (i*m))*ZMod.stdAddChar (j*m))=
      if i=j then (N:ℂ) else 0 := by
  classical
  have hs (a : ZMod N) : star (ZMod.stdAddChar a)=ZMod.stdAddChar (-a) := by
    rw [AddChar.map_neg_eq_inv]
    exact ((ZMod.stdAddChar : AddChar (ZMod N) ℂ).inv_apply_eq_conj a).symm
  simp only [hs,←AddChar.map_add_eq_mul,←sub_eq_neg_add,←sub_mul]
  rw [character_sum]
  congr 1
  exact propext (sub_eq_zero.trans eq_comm)

def phaseSum (b : ZMod N → ℂ) (m : ZMod N) : ℂ :=
  ∑ j, ZMod.stdAddChar (j*m)*b j

lemma phase_parseval (b : ZMod N → ℂ) :
    (∑ m : ZMod N, ‖phaseSum b m‖^2)=(N:ℝ)*∑ j, ‖b j‖^2 := by
  classical
  have h : (∑ m : ZMod N, star (phaseSum b m)*phaseSum b m)=
      (N:ℂ)*∑ j, star (b j)*b j := by
    simp only [phaseSum,star_sum,star_mul,Finset.sum_mul_sum]
    calc
      _=∑ i : ZMod N, ∑ j : ZMod N,
          (star (b i)*b j)*(∑ m : ZMod N, star (ZMod.stdAddChar (i*m))*ZMod.stdAddChar (j*m)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _=(N:ℂ)*∑ j, star (b j)*b j := by
        simp only [character_orthogonality]
        simp [Finset.sum_ite_eq,Finset.mul_sum,mul_comm]
  have hnorm (z : ℂ) : star z*z=((‖z‖^2:ℝ):ℂ) := by
    rw [Complex.sq_norm]
    exact Complex.normSq_eq_conj_mul_self.symm
  simp only [hnorm,←Complex.ofReal_sum,←Complex.ofReal_natCast,←Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

lemma phase_parseval_mul [Fact N.Prime] (b : ZMod N → ℂ) (k : ZMod N) (hk : k≠0) :
    (∑ m : ZMod N, ‖phaseSum b (k*m)‖^2)=(N:ℝ)*∑ j, ‖b j‖^2 := by
  rw [←phase_parseval b]
  exact Fintype.sum_equiv (Equiv.mulLeft₀ k hk) _ _ (fun _ => rfl)

end Fourier

section Algebra

variable {A : Type*} [CStarAlgebra A]

variable {I : Type*} [Fintype I]

variable (e : I → A) (he : ∀ i, IsStarProjection (e i))
  (ho : ∀ i j, i≠j → e i*e j=0)

def diagonal (c : I → ℂ) : A := ∑ i,c i • e i

include he ho in
lemma diagonal_mul (c d : I → ℂ) :
    diagonal e c*diagonal e d=diagonal e (fun i => c i*d i) := by
  simp only [diagonal,Finset.sum_mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [(he i).isIdempotentElem.eq,mul_comm]
  · intro j _ hji
    rw [ho i j hji.symm,smul_zero]
  · simp

include he in
lemma diagonal_star (c : I → ℂ) : star (diagonal e c)=diagonal e (fun i => star (c i)) := by
  simp only [diagonal,star_sum,star_smul,(he _).isSelfAdjoint.star_eq]

include he ho in
lemma diagonal_pow_succ (c : I → ℂ) (k : ℕ) :
    diagonal e c^(k+1)=diagonal e (fun i => c i^(k+1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,ih,diagonal_mul e he ho]
    simp only [pow_succ]

include he ho in
lemma diagonal_support (c : I → ℂ) :
    diagonal e c*(∑ i,e i)=diagonal e c ∧ (∑ i,e i)*diagonal e c=diagonal e c := by
  have hq : (∑ i,e i)=diagonal e (fun _ => 1) := by simp [diagonal]
  rw [hq,diagonal_mul e he ho,diagonal_mul e he ho]
  simp

include he ho in
lemma diagonal_unitary (c : I → ℂ) (hc : ∀ i, ‖c i‖=1) :
    star (diagonal e c)*diagonal e c=∑ i,e i ∧
      diagonal e c*star (diagonal e c)=∑ i,e i := by
  have hc' (i : I) : star (c i)*c i=1 := by
    change (starRingEnd ℂ) (c i)*c i=1
    rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hc i]
    norm_num
  rw [diagonal_star e he,diagonal_mul e he ho,diagonal_mul e he ho]
  constructor
  · simp only [hc',diagonal,one_smul]
  · simp only [mul_comm (c _) (star (c _)),hc',diagonal,one_smul]

end Algebra

end Kadison.CornerPhase

end

end
end

end OAI
