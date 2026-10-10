import OAI.Combinatorics.PolynomialVacuum.Algebra.TransportFiltration
import OAI.Combinatorics.PolynomialVacuum.Algebra.Candidate

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem transportCup_mul {n : ℕ} (i : Fin (n+1)) (ks : List (Fin (n+1)))
    (f : MvPolynomial (Fin (n+1)) ℂ) (W : PolynomialTensor (n+2) (Fin (n+1))) :
    transportCup i ks (fun s => f*W s)=fun s => f*transportCup i ks W s := by
  induction ks generalizing W with
  | nil => rfl
  | cons k ks ih =>
    simp only [transportCup,List.foldl_cons,tensorExchange_mul]
    exact ih _

theorem initialCup_marked_degree {n : ℕ} (ψ : State n) (i : Fin (n+1))
    (s : Fin (n+2) → Spin) : (initialCup ψ i s).degreeOf i=0 := by
  apply Nat.eq_zero_of_le_zero
  exact (degreeOf_C_mul_le _ _ _).trans (le_of_eq
    (degreeOf_rename_missing i.succAbove _ i (fun j => Fin.succAbove_ne i j)))

theorem leftFusionFactors_marked_degree {n : ℕ} (i : Fin (n+1)) :
    (leftFusionFactors i).degreeOf i ≤ 2*i.val := by
  apply (degreeOf_prod_le _ _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.univ.filter (fun k : Fin (n+1) => k < i), 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hd (c : ℂ) : (X k-C c*X i : MvPolynomial (Fin (n+1)) ℂ).degreeOf i ≤ 1 := by
        rw [sub_eq_add_neg]
        apply dadd
        · exact (by rw [degreeOf_X]; split_ifs <;> omega)
        · rw [degreeOf_neg]; exact dconst_mul _ (by simp)
      exact dmul (hd _) (hd _)
    _ = 2*i.val := by simp [leftSpectators_card,Nat.mul_comm]

theorem cup_plus_carried (s : Spin) (h : -1 < charge s) : cup (Spin.plus,s)=0 := by
  cases s <;> norm_num [charge] at h <;> norm_num [charge,cup]

 

theorem cupPrescription_marked_degrees {n : ℕ} (ψ : State n) (i : Fin (n+1))
    (s : Fin (n+2) → Spin) :
    (cupPrescription ψ i s).degreeOf i ≤ 2*n+1 ∧
    (s (pairLeft i)=Spin.plus → -1 < charge (s (Fin.last (n+1))) →
      (cupPrescription ψ i s).degreeOf i ≤ 2*n) := by
  let W : PolynomialTensor (n+2) (Fin (n+1)) := fun s => X i*initialCup ψ i s
  have hd (v) : (W v).degreeOf i ≤ 0+1 := by
    dsimp [W]
    exact (dmul (by simp : (X i : MvPolynomial (Fin (n+1)) ℂ).degreeOf i≤1)
      (le_of_eq (initialCup_marked_degree ψ i v))).trans (by omega)
  have hf (v) (hv : v (pairLeft i)=Spin.plus) (hc : -1 < charge (v (pairRight i))) :
      (W v).degreeOf i ≤ 0 := by
    simp [W,initialCup,hv,cup_plus_carried _ hc]
  have ht := transportCup_marked_filtration i (rightSpectators i) _ _ (rightSpectators_path i)
    (by intro k hk; simpa [rightSpectators] using (List.mem_filter.mp hk).2) 0 W hd hf
  have he : cupPrescription ψ i s=C (1+T)*leftFusionFactors i*transportCup i (rightSpectators i) W s := by
    simp only [W,transportCup_mul,cupPrescription]
    ring
  rw [he]
  have hi:=i.isLt
  rw [rightSpectators_length] at ht
  constructor
  · exact (dmul (dconst_mul _ (leftFusionFactors_marked_degree i)) (ht.1 s)).trans (by omega)
  · intro hs hl
    exact (dmul (dconst_mul _ (leftFusionFactors_marked_degree i)) (ht.2 s hs hl)).trans (by omega)

theorem dividedCupPrescription_marked_degree {n : ℕ} (ψ : State n) (i : Fin (n+1))
    (s : Fin (n+2) → Spin) : (dividedCupPrescription ψ i s).degreeOf i ≤ 2*n := by
  by_cases hz : dividedCupPrescription ψ i s=0
  · simp [hz]
  · have h := (cupPrescription_marked_degrees ψ i s).1
    rw [cupPrescription_factor,degreeOf_mul_eq (X_ne_zero _) hz,degreeOf_X_self] at h
    omega

end PolynomialVacuumAlgebra

end OAI
