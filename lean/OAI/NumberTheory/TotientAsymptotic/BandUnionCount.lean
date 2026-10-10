import OAI.NumberTheory.TotientAsymptotic.NormalBandErrorBound

namespace OAI

/-! Sum the actual normal-preimage count over a finite family of cutoff vectors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def NormalBandWitness (S X k : ℕ) (Y : ℕ → ℕ) (v : ℕ) : Prop :=
  ∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
    (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧
    SquarefreeAbove v S ∧ SquarefreeAbove n S ∧
    (∀ p ∈ n.primeFactors,IsNormalPrime S p) ∧
    ∀ j : Fin k,j.val+2 ≤ n.primeFactorsList.length ∧ Y j.val < fordPrime n (j.val+1)

theorem normal_band_union_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X k : ℕ) (H T : ℝ) (P : Finset (ℕ → ℕ)),
    2 ≤ S → 0 ≤ B S → 1 ≤ B X → 0 ≤ H →
    (∀ Y ∈ P,S ≤ Y 0 ∧ Y k=S ∧ Real.log (Y 0) ≤ Real.log X/(20*B X) ∧
      (∀ j < k,Y (j+1) ≤ Y j) ∧ (∀ j < k,B (Y j) ≤ H) ∧
      T ≤ ∑ j ∈ Finset.range k,a (j+1)*B (Y j)) →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,∃ Y ∈ P,NormalBandWitness S X k Y v) →
    (Q.card:ℝ) ≤ C*X*P.card*Real.exp (-T+(1-countBandWeight (k+1))*B S+
      D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*H)) := by
  classical
  obtain ⟨C,D,hC,hD,hbound⟩ := ford_normal_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X k H T P hS hBS hBX hH hP Q hQ
  let F := fun Y : ℕ → ℕ => Q.filter (NormalBandWitness S X k Y)
  have hcover : Q ⊆ P.biUnion F := by
    intro v hv
    obtain ⟨Y,hY,hvY⟩ := hQ v hv
    exact Finset.mem_biUnion.mpr ⟨Y,hY,Finset.mem_filter.mpr ⟨hv,hvY⟩⟩
  have hF (Y : ℕ → ℕ) (hY : Y ∈ P) :
      ((F Y).card:ℝ) ≤ C*X*Real.exp (-T+(1-countBandWeight (k+1))*B S+
        D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*H)) := by
    obtain ⟨hSY,hYS,hcut,hdesc,hHbound,hscore⟩ := hP Y hY
    have hc := hbound S X (Y 0) k Y hS hSY rfl hYS hBX hcut hdesc (F Y)
      (fun v hv => (Finset.mem_filter.mp hv).2)
    have herr := normal_band_error_bound hD.le hBS hH hHbound
    have hexp : -(∑ j ∈ Finset.range k,a (j+1)*B (Y j))+
        (1-countBandWeight (k+1))*B S+normalBandError S D k Y ≤
        -T+(1-countBandWeight (k+1))*B S+D*(k:ℝ)*(k+2)+
          (k:ℝ)*(k+2)^2*Real.sqrt (B S*H) := by linarith
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))
  calc
    _ ≤ ((P.biUnion F).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ Y ∈ P,((F Y).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le : (P.biUnion F).card ≤ ∑ Y ∈ P,(F Y).card)
    _ ≤ ∑ _Y ∈ P,C*X*Real.exp (-T+(1-countBandWeight (k+1))*B S+
        D*(k:ℝ)*(k+2)+(k:ℝ)*(k+2)^2*Real.sqrt (B S*H)) := Finset.sum_le_sum hF
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end TotientAsymptotic

end

end OAI
