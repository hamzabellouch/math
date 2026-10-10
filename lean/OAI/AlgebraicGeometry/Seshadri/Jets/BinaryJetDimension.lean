import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.PolynomialJets

namespace OAI


                                            
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators

lemma binary_degree (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum,Fin.sum_univ_two]

def binaryJetEquiv (n : ℕ) : JetIndex (Fin 2) n ≃ (i : Fin n) × Fin (i.val+1) where
  toFun d := ⟨⟨d.val.degree,d.property⟩,⟨d.val 0,by change d.val 0 < d.val.degree+1; rw [binary_degree]; omega⟩⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm ![a.2.val,a.1.val-a.2.val],by
    rw [binary_degree]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have h := a.2.isLt
    have h' := a.1.isLt
    omega⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp
    · change d.val.degree - d.val 0 = d.val 1
      rw [binary_degree]
      omega
  right_inv a := by
    rcases a with ⟨i,j⟩
    have hd : (Finsupp.equivFunOnFinite.symm ![j.val,i.val-j.val]).degree = i.val := by
      rw [binary_degree]
      simp only [Finsupp.coe_equivFunOnFinite_symm,Matrix.cons_val_zero,Matrix.cons_val_one]
      omega
    exact Sigma.ext (Fin.ext hd) ((Fin.heq_ext_iff (congrArg (·+1) hd)).mpr rfl)

lemma card_binaryJet (n : ℕ) :
    2 * Nat.card (JetIndex (Fin 2) n) = n*(n+1) := by
  rw [Nat.card_congr (binaryJetEquiv n)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_fin]
  have h : ∀ n : ℕ, 2 * (∑ i ∈ Finset.range n, (i+1)) = n*(n+1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; nlinarith
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i+1) n]
  exact h n

end
end MaximalSeshadri.AlgebraicJets

end


end OAI
