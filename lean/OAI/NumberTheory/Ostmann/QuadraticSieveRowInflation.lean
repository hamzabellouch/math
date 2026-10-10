import OAI.NumberTheory.Ostmann.QuadraticSieveRowInflationAverage
import OAI.NumberTheory.Ostmann.QuadraticSieveRowInflationTarget

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem quadraticNorm_rowInflation_of_card {M N R : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hR : 2 ≤ R)
    (hcard : Real.log 2*(R:ℝ)/Real.log R ≤ (rowInflationPrimes R).card)
    (hsize : 6*Real.log (2*(M:ℝ)*N) ≤ Real.log 2*(R:ℝ))
    (S : Finset ℕ) (hS : S ⊆ oddSquarefreeUpTo N) :
    quadraticNorm (dyadicSquarefreeRows M) S ≤ 4*quadraticNorm (rowInflationTarget M R) S := by
  classical
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hRr : (1:ℝ) < R := by exact_mod_cast (show 1<R by omega)
  have hlogR : 0 < Real.log (R:ℝ) := Real.log_pos hRr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMN : (2:ℝ) ≤ 2*(M:ℝ)*N := by nlinarith
  have hlogMN : 0 ≤ Real.log (2*(M:ℝ)*N) := Real.log_nonneg (by linarith)
  let D : ℝ := Real.log (2*(M:ℝ)*N)/Real.log R
  have hD : 0 ≤ D := div_nonneg hlogMN hlogR.le
  have hP : 0 < (rowInflationPrimes R).card := by
    have hh : (0:ℝ) < (rowInflationPrimes R).card := lt_of_lt_of_le (by positivity) hcard
    exact_mod_cast hh
  apply quadraticNorm_le_primeDilation_average (rowInflationPrimes R)
    (dyadicSquarefreeRows M) (rowInflationTarget M R) S D D hD hD hP
    (fun p hp => (mem_rowInflationPrimes.mp hp).1)
    (fun v hv => by have hh := (mem_dyadicSquarefreeRows.mp hv).1; omega)
    (fun p hp v hv hnd => primeDilation_mem_target hM hR hp hv hnd)
  · intro v hv
    obtain ⟨hMv,hvM,hvo,hvs⟩ := mem_dyadicSquarefreeRows.mp hv
    have hvp : (0:ℝ) < v := by exact_mod_cast (show 0<v by omega)
    have hvB : (v:ℝ) ≤ 2*(M:ℝ)*N := by
      have hh : (v:ℝ) ≤ 2*M := by exact_mod_cast hvM
      nlinarith
    exact (rowInflationPrimes_divisor_card_le R v hR (by omega)).trans
      (div_le_div_of_nonneg_right (Real.log_le_log hvp hvB) hlogR.le)
  · intro n hn
    have hh := mem_oddSquarefreeUpTo.mp (hS hn)
    have hnp : (0:ℝ) < n := by exact_mod_cast hh.1
    have hnB : (n:ℝ) ≤ 2*(M:ℝ)*N := by
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast hh.2.1
      nlinarith
    exact (rowInflationPrimes_divisor_card_le R n hR hh.1).trans
      (div_le_div_of_nonneg_right (Real.log_le_log hnp hnB) hlogR.le)
  · have hh := div_le_div_of_nonneg_right hsize hlogR.le
    dsimp [D]
    calc
      _ = 6*Real.log (2*(M:ℝ)*N)/Real.log R := by ring
      _ ≤ _ := hh.trans hcard

theorem exists_quadraticNorm_rowInflation :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (M N R : ℕ), 0 < M → 0 < N →
      C*Real.log (2*(M:ℝ)*N) ≤ R → ∀ S : Finset ℕ,
      S ⊆ oddSquarefreeUpTo N →
      quadraticNorm (dyadicSquarefreeRows M) S ≤ 4*quadraticNorm (rowInflationTarget M R) S := by
  obtain ⟨R₀,hR₀⟩ := Filter.eventually_atTop.mp eventually_rowInflationPrimes_card_lower
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := max 1 (max (((max R₀ 2:ℕ):ℝ)/Real.log 2) (6/Real.log 2))
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hCsize : 6 ≤ C*Real.log 2 := (div_le_iff₀ hlog2).mp
    ((le_max_right _ _).trans (le_max_right _ _))
  have hCR : ((max R₀ 2:ℕ):ℝ) ≤ C*Real.log 2 := (div_le_iff₀ hlog2).mp
    ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨C,hC,?_⟩
  intro M N R hM hN hscale S hS
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hMN : (2:ℝ) ≤ 2*(M:ℝ)*N := by nlinarith
  have hlogs : Real.log 2 ≤ Real.log (2*(M:ℝ)*N) := Real.log_le_log (by norm_num) hMN
  have hRlarge : max R₀ 2 ≤ R := by
    have hh := hCR.trans ((mul_le_mul_of_nonneg_left hlogs hC0).trans hscale)
    exact_mod_cast hh
  have hsize : 6*Real.log (2*(M:ℝ)*N) ≤ Real.log 2*(R:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hCsize
      (show 0 ≤ Real.log (2*(M:ℝ)*N) by linarith)
    have h2 := mul_le_mul_of_nonneg_left hscale hlog2.le
    nlinarith
  exact quadraticNorm_rowInflation_of_card hM hN ((le_max_right _ _).trans hRlarge)
    (hR₀ R ((le_max_left _ _).trans hRlarge)) hsize S hS

end Ostmann.QuadraticSieve

end

end OAI
