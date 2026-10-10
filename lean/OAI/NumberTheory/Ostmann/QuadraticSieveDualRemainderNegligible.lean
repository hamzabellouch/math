import OAI.NumberTheory.Ostmann.QuadraticSieveDualRemainderNegligibleBasic
import OAI.NumberTheory.Ostmann.QuadraticSievePoissonDecayOrder

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem dualCorrelationRemainder_negligible (W : 𝓢(ℝ, ℂ)) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M P H : ℝ) (Δ K N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      1 ≤ M → M ≤ P → 1 ≤ P → 0 < H → (Δ : ℝ) ≤ P → (N : ℝ) ≤ P →
      (K : ℝ) ≤ P^3 → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, 1 < n) →
      (∀ n ∈ S, H ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*H) →
      ‖dualCorrelationRemainder W M Δ K S a
        (dualWindowLower M H (P^η)) (dualWindowUpper M H (P^η))
        (fun _ _ => 16*(P^η)^2)‖ ≤ C*coefficientEnergy S a := by
  obtain ⟨A, hA⟩ := exists_poisson_decay_order η 6 hη
  obtain ⟨C, hC, hbound⟩ := dualCorrelationRemainder_bound W A
  refine ⟨2*C, by positivity, ?_⟩
  intro M P H Δ K N S a hM hMP hP hH hΔP hNP hKP hS hS1 hSH
  have hMp : 0 < M := by linarith
  have hPp : 0 < P := by linarith
  have hT : 1 ≤ P^η := Real.one_le_rpow hP hη.le
  have hTp : 0 < P^η := by positivity
  have hE := coefficientEnergy_nonneg S a
  have hcard : (S.card : ℝ) ≤ P := by
    have hSN : S.card ≤ N := by
      calc
        _ ≤ (Finset.Icc 1 N).card := Finset.card_le_card (fun n hn =>
          Finset.mem_Icc.mpr ⟨(mem_oddSquarefreeUpTo.mp (hS hn)).1,
            (mem_oddSquarefreeUpTo.mp (hS hn)).2.1⟩)
        _ = _ := by simp
    exact (show (S.card : ℝ) ≤ N by exact_mod_cast hSN).trans hNP
  have hsqrt : Real.sqrt M ≤ P := by
    have hsq := Real.sq_sqrt hMp.le
    have hnn := Real.sqrt_nonneg M
    nlinarith [sq_nonneg (P-1)]
  have hΔ : ((2*Δ : ℕ) : ℝ) ≤ 2*P := by push_cast; nlinarith
  have hpoint (n : ℕ) (hn : n ∈ S) (t : ℕ) (ht : t ∈ S) (_hcop : Nat.Coprime n t) :
      dualSecondErrorScale M Δ K (n*t) A (fun _ _ => P^η) ≤ 2*P^5/(P^η)^A := by
    have hnp := (mem_oddSquarefreeUpTo.mp (hS hn)).1
    have htp := (mem_oddSquarefreeUpTo.mp (hS ht)).1
    apply (dualSecondErrorScale_le_uniform M (P^η) Δ K (n*t) A hMp hTp
      (Nat.mul_pos hnp htp)).trans
    calc
      _ ≤ (2*P)*P^3*P/(P^η)^A := by gcongr
      _ = _ := by ring
  have hp := hbound M Δ K N hMp S a hS hS1
    (dualWindowLower M H (P^η)) (dualWindowUpper M H (P^η))
    (fun _ _ => P^η) (fun _ _ => 16*(P^η)^2)
    (fun n hn t ht _hcop e he b hb =>
      dual_dyadic_window_parameters hMp hH hT (Nat.pos_of_mem_divisors he)
        (mem_oddSquarefreeUpTo.mp hb).1 (hSH n hn).1 (hSH n hn).2
        (hSH t ht).1 (hSH t ht).2)
  have hpair := dualPairErrorScale_le_uniform S a
    (fun q => dualSecondErrorScale M Δ K q A (fun _ _ => P^η))
    (2*P^5/(P^η)^A) (by positivity) hpoint
  have habs : P^6/(P^η)^A ≤ 1 := by
    convert hA P hP using 1; norm_num
  apply hp.trans
  calc
    _ ≤ C*((S.card : ℝ)*coefficientEnergy S a*(2*P^5/(P^η)^A)) :=
      mul_le_mul_of_nonneg_left hpair hC.le
    _ ≤ C*(P*coefficientEnergy S a*(2*P^5/(P^η)^A)) := by gcongr
    _ = 2*C*(P^6/(P^η)^A)*coefficientEnergy S a := by ring
    _ ≤ 2*C*1*coefficientEnergy S a := by gcongr
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
