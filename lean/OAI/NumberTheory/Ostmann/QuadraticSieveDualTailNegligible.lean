import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelations
import OAI.NumberTheory.Ostmann.QuadraticSievePoissonDecayOrder

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem dualCorrelationTail_negligible (W : 𝓢(ℝ, ℂ)) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M P K : ℝ) (Δ N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      1 ≤ M → 1 ≤ P → 0 < Δ → 0 < N → (Δ : ℝ) ≤ P → (N : ℝ) ≤ P →
      ((2*Δ : ℕ) : ℝ)*(N : ℝ)^2/M*P^η ≤ K → S ⊆ oddSquarefreeUpTo N →
      ‖dualCorrelationTail W M Δ K S a‖ ≤ C*coefficientEnergy S a := by
  obtain ⟨A,hA⟩ := exists_poisson_decay_order η 6 hη
  obtain ⟨C,hC,hbound⟩ := dualPoissonTail_bound_scaled W A
  refine ⟨4*C,by positivity,?_⟩
  intro M P K Δ N S a hM hP hΔ hN hΔP hNP hcut hS
  have hMp : 0 < M := by linarith
  have hPp : 0 < P := by linarith
  have hDp : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hT : 0 < P^η := Real.rpow_pos_of_pos hPp _
  have hK : 0 < K := (by positivity : 0 < (((2*Δ : ℕ) : ℝ)*(N : ℝ)^2/M*P^η)).trans_le hcut
  have hcard : (S.card : ℝ) ≤ P := by
    have hsn : S.card ≤ N := by
      calc
        _ ≤ (Finset.Icc 1 N).card := Finset.card_le_card (fun n hn =>
          Finset.mem_Icc.mpr ⟨(mem_oddSquarefreeUpTo.mp (hS hn)).1,(mem_oddSquarefreeUpTo.mp (hS hn)).2.1⟩)
        _ = _ := by simp
    exact (show (S.card : ℝ) ≤ N by exact_mod_cast hsn).trans hNP
  have hpoint (n : ℕ) (hn : n ∈ S) (t : ℕ) (ht : t ∈ S) (hnt : Nat.Coprime n t) :
      ‖dualCorrelationTailTerm W M Δ (n*t) K‖ ≤ 4*C*P^5/(P^η)^A := by
    obtain ⟨hnp,hnb,hno,hns⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
    obtain ⟨htp,htb,hto,hts⟩ := mem_oddSquarefreeUpTo.mp (hS ht)
    have hqpos : 0 < n*t := Nat.mul_pos hnp htp
    let : NeZero (n*t) := ⟨hqpos.ne'⟩
    have hqr : 0 < ((n*t : ℕ) : ℝ) := by exact_mod_cast hqpos
    have hqN : ((n*t : ℕ) : ℝ) ≤ (N : ℝ)^2 := by exact_mod_cast (show n*t ≤ N^2 by nlinarith)
    have hqP : ((n*t : ℕ) : ℝ) ≤ P^2 := hqN.trans (pow_le_pow_left₀ hNp.le hNP 2)
    have hsqrt : Real.sqrt ((n*t : ℕ) : ℝ) ≤ P := by
      nlinarith [Real.sq_sqrt hqr.le,Real.sqrt_nonneg (((n*t : ℕ) : ℝ))]
    have hkP : (((2*Δ : ℕ) : ℝ)) ≤ 2*P := by push_cast; nlinarith
    have hr : (((2*Δ : ℕ) : ℝ))*((n*t : ℕ) : ℝ)/M ≤ 2*P^3 := by
      calc
        _ ≤ (((2*Δ : ℕ) : ℝ))*((n*t : ℕ) : ℝ) := div_le_self (by positivity) hM
        _ ≤ (2*P)*P^2 := mul_le_mul hkP hqP hqr.le (by positivity)
        _ = _ := by ring
    have hcutq : (((2*Δ : ℕ) : ℝ))*((n*t : ℕ) : ℝ)/M*P^η ≤ K := by
      apply le_trans _ hcut
      gcongr
    rw [dualCorrelationTailTerm_eq]
    apply (hbound M (2*Δ) (n*t) K (P^η) hMp (by omega) (hno.mul hto)
      (Nat.squarefree_mul_iff.mpr ⟨hnt,hns,hts⟩) hK hT hcutq).trans
    calc
      _ ≤ C*(2*P)*P*(2*P^3)/(P^η)^A := by gcongr
      _ = _ := by ring
  unfold dualCorrelationTail
  have he := norm_complementaryPair_le S a (fun q => dualCorrelationTailTerm W M Δ q K) (4*C*P^5/(P^η)^A) (by positivity) hpoint
  apply he.trans
  have hE := coefficientEnergy_nonneg S a
  have habs : P^6/(P^η)^A ≤ 1 := by simpa only [Real.rpow_ofNat] using hA P hP
  calc
    _ ≤ P*coefficientEnergy S a*(4*C*P^5/(P^η)^A) := by gcongr
    _ = 4*C*(P^6/(P^η)^A)*coefficientEnergy S a := by ring
    _ ≤ 4*C*1*coefficientEnergy S a := by gcongr
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
