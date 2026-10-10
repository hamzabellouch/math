import OAI.Analysis.Laughlin.Spin.Schur

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

variable {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]

noncomputable def copyMatrix (A : Matrix I I ℂ) : Matrix (C × I) (C × I) ℂ :=
  fun i j => if i.1=j.1 then A i.2 j.2 else 0

omit [DecidableEq I] in
theorem copyMatrix_mul (A B : Matrix I I ℂ) :
    copyMatrix (C := C) (A*B)=copyMatrix A*copyMatrix B := by
  ext a b
  simp only [copyMatrix,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,zero_mul,mul_ite,mul_zero,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

omit [Fintype C] [Fintype I] in
theorem copyMatrix_one : copyMatrix (C := C) (1 : Matrix I I ℂ)=1 := by
  ext a b
  simp only [copyMatrix,Matrix.one_apply]
  by_cases h : a=b
  · subst b; simp
  · have hh : ¬ (a.1=b.1 ∧ a.2=b.2) := by rintro ⟨h1,h2⟩; exact h (Prod.ext h1 h2)
    simp [h]
    tauto

noncomputable def copiedSpinRepresentation (C : Type*) [Fintype C] [DecidableEq C] (Q : ℕ) :
    SourceSU2 →* Matrix (C × Fin (Q+1)) (C × Fin (Q+1)) ℂ where
  toFun g := copyMatrix (sourceSpinRepresentation Q g)
  map_one' := by rw [map_one,copyMatrix_one]
  map_mul' g h := by rw [map_mul,copyMatrix_mul]

 theorem copied_conjugateOrbit_block (Q : ℕ)
    (M : Matrix (C × Fin (Q+1)) (C × Fin (Q+1)) ℂ) (g : SourceSU2)
    (r s : C) (p q : Fin (Q+1)) :
    conjugateOrbit (copiedSpinRepresentation C Q) M g (r,p) (s,q) =
      conjugateOrbit (sourceSpinRepresentation Q) (fun i j => M (r,i) (s,j)) g p q := by
  simp only [conjugateOrbit,Matrix.mul_apply,Fintype.sum_prod_type,copiedSpinRepresentation,
    MonoidHom.coe_mk,OneHom.coe_mk,copyMatrix,ite_mul,zero_mul,mul_ite,mul_zero,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

theorem source_spin_copy_haar_schur (Q : ℕ)
    (M : Matrix (C × Fin (Q+1)) (C × Fin (Q+1)) ℂ) (r s : C) (p q : Fin (Q+1)) :
    matrixIntegral sourceHaar (conjugateOrbit (copiedSpinRepresentation C Q) M) (r,p) (s,q) =
      ((∑ k : Fin (Q+1), M (r,k) (s,k))/(Q+1 : ℕ)) * (if p=q then 1 else 0) := by
  have h := congrFun (congrFun (source_spin_haar_schur Q (fun i j => M (r,i) (s,j))) p) q
  simpa only [matrixIntegral,copied_conjugateOrbit_block,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    Matrix.trace,Matrix.diag] using h

theorem source_highest_copy_orbit_resolution (Q : ℕ) (r s : C) (a b : C) (p q : Fin (Q+1)) :
    ((Q+1 : ℕ) : ℂ) * matrixIntegral sourceHaar
      (conjugateOrbit (copiedSpinRepresentation C Q)
        (fun i j => if i=(r,(0 : Fin (Q+1))) ∧ j=(s,(0 : Fin (Q+1))) then 1 else 0)) (a,p) (b,q) =
      if a=r ∧ b=s ∧ p=q then 1 else 0 := by
  rw [source_spin_copy_haar_schur Q
    (fun (i j : C × Fin (Q+1)) => if i=(r,0) ∧ j=(s,0) then 1 else 0) a b p q]
  have hn : ((Q+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero Q
  have hn' : (Q : ℂ)+1 ≠ 0 := by simpa only [Nat.cast_add,Nat.cast_one] using hn
  simp only [Prod.mk.injEq]
  by_cases ha : a=r <;> by_cases hb : b=s <;> by_cases hpq : p=q <;>
    simp [ha,hb,hpq,hn']

end Laughlin.Rotation

end OAI
