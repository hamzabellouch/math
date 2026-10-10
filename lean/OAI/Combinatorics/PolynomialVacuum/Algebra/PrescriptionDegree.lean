import OAI.Combinatorics.PolynomialVacuum.Algebra.CupPrescriptions

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem leftSpectators_card {n : ℕ} (i : Fin (n+1)) :
    (Finset.univ.filter (fun k : Fin (n+1) => k < i)).card=i.val := by
  have h : Finset.univ.filter (fun k : Fin (n+1) => k < i)=Finset.Iio i := by ext; simp
  rw [h,Fin.card_Iio]

theorem rightSpectators_length {n : ℕ} (i : Fin (n+1)) :
    (rightSpectators i).length=n-i.val := by
  have h : (rightSpectators i).toFinset=Finset.Ioi i := by
    ext k
    simp [rightSpectators]
  have hn : (rightSpectators i).Nodup := (List.nodup_finRange (n+1)).filter _
  rw [← List.toFinset_card_of_nodup hn,h,Fin.card_Ioi]
  omega

theorem cupPrescription_totalDegree {n : ℕ} (ψ : State n)
    (hψ : ∀ s, (ψ s).IsHomogeneous (n.choose 2)) (i : Fin (n+1)) (s : Fin (n+2) → Spin) :
    (cupPrescription ψ i s).IsHomogeneous ((n+2).choose 2) := by
  have h := cupPrescription_homogeneous ψ hψ i s
  rw [leftSpectators_card,rightSpectators_length] at h
  have hdeg : 1+2*i.val+n.choose 2+2*(n-i.val)=(n+2).choose 2 := by
    have h1 := Nat.choose_succ_succ' n 1
    have h2 := Nat.choose_succ_succ' (n+1) 1
    norm_num only [Nat.add_assoc, Nat.reduceAdd, Nat.choose_one_right] at h1 h2
    have hi := i.isLt
    omega
  rw [hdeg] at h
  exact h

end PolynomialVacuumAlgebra

end OAI
