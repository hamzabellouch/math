import OAI.Probability.InvariantIsing.Pressure.AlmostSure

namespace OAI

/-! Eventual local exponential tails imply almost-sure convergence whenever
the localizing random bound is eventually finite. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma exponential_tail_extend_initial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ℕ → Set Ω)
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (N₀ : ℕ)
    (hE : ∀ n, N₀ ≤ n → P.real (E n) ≤ C*Real.exp (-a*(n : ℝ))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, P.real (E n) ≤ D*Real.exp (-a*(n : ℝ)) := by
  let D := C+Real.exp (a*(N₀ : ℝ))
  have hCD : C ≤ D := le_add_of_nonneg_right (Real.exp_pos _).le
  refine ⟨D,by dsimp [D]; positivity,fun n => ?_⟩
  by_cases hn : N₀ ≤ n
  · exact (hE n hn).trans (mul_le_mul_of_nonneg_right hCD (Real.exp_pos _).le)
  · have hle : (n : ℝ) ≤ N₀ := by exact_mod_cast (show n ≤ N₀ by omega)
    have he : 1 ≤ Real.exp (a*(N₀ : ℝ))*Real.exp (-a*(n : ℝ)) := by
      rw [← Real.exp_add,Real.one_le_exp_iff]
      nlinarith
    have hED : Real.exp (a*(N₀ : ℝ)) ≤ D := by dsimp [D]; linarith
    exact (measureReal_le_one : P.real (E n) ≤ 1).trans
      (he.trans (mul_le_mul_of_nonneg_right hED (Real.exp_pos _).le))

lemma ae_tendsto_zero_of_localized_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : ℕ → Ω → ℝ)
    (htail : ∀ K ε : ℝ, 0 < K → 0 < ε →
      ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∃ N₀ : ℕ,
        ∀ n, N₀ ≤ n → P.real {ω | ε ≤ |X n ω| ∧ Z n ω ≤ K} ≤ C*Real.exp (-a*(n : ℝ)))
    (hbound : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ n in atTop, Z n ω ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  let T := fun k n ω => if Z n ω ≤ (k+1 : ℝ) then X n ω else 0
  have hT (k : ℕ) : ∀ᵐ ω ∂P, Tendsto (fun n => T k n ω) atTop (𝓝 0) := by
    apply ae_tendsto_zero_of_exponential_tail
    intro ε hε
    obtain ⟨C,a,hC,ha,N₀,hN₀⟩ := htail (k+1) ε (by positivity) hε
    obtain ⟨D,hD,hDE⟩ := exponential_tail_extend_initial P
      (fun n => {ω | ε ≤ |X n ω| ∧ Z n ω ≤ (k+1 : ℝ)}) hC ha N₀ hN₀
    refine ⟨D,a,hD,ha,fun n => ?_⟩
    have he : {ω | ε ≤ |T k n ω|}={ω | ε ≤ |X n ω| ∧ Z n ω ≤ (k+1 : ℝ)} := by
      ext ω
      by_cases hh : Z n ω ≤ (k+1 : ℝ)
      · simp only [T,hh,ite_true,mem_ofPred_eq,and_true]
      · simp only [T,hh,ite_false,abs_zero,mem_ofPred_eq,and_false,not_le_of_gt hε]
    rw [he]
    exact hDE n
  filter_upwards [ae_all_iff.mpr hT,hbound] with ω hω hb
  obtain ⟨K,hK⟩ := hb
  obtain ⟨k,hk⟩ := exists_nat_gt K
  have he : (fun n => T k n ω)=ᶠ[atTop] (fun n => X n ω) := by
    filter_upwards [hK] with n hn
    have hn' : Z n ω ≤ (k+1 : ℝ) := hn.trans (by exact le_trans hk.le (by linarith))
    simp only [T,ite_eq_left hn']
  exact (hω k).congr' he

end InvariantIsing

end

end OAI
