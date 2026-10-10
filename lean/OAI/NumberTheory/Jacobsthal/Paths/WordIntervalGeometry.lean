import OAI.NumberTheory.Jacobsthal.Primes.SourcePrimeProductData

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.WordIntervalGeometry
open FinitePathGeometry PrimeHistories PrimeProductLogCoordinates RepresentativeAdmission
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def wordIntervalExponent (w : ℝ) (Y : ℕ) (ps : List ℕ) : ℝ :=
  Real.log ((Y:ℝ)/(ps.prod:ℝ))/Real.log w

theorem word_interval_gap {w a : ℝ} (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2) (ps : List ℕ) (hp : ∀ p∈ps,0 < p) :
    wordIntervalExponent w Y ps=(terminal w z ps).gap+a-2 := by
  have hh := terminal_gap_log_quotient Y hY z hroot ps hp
  unfold wordIntervalExponent
  linarith

theorem gap_prefix_mono (w : ℝ) (z : Node) (pre tail : List ℕ)
    (hp : ∀ p∈tail,0 ≤ primeExponent w p) :
    (terminal w z (pre++tail)).gap ≤ (terminal w z pre).gap := by
  rw [terminal_append,terminal_gap_sum]
  have hh : 0 ≤ (tail.map (primeExponent w)).sum := List.sum_nonneg (fun x hx => by
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hx
    exact hp p hp')
  linarith

theorem interval_exponent_step (w : ℝ) (Y : ℕ) (hY : 0 < Y) (pre : List ℕ) (u : ℕ)
    (hp : 0 < pre.prod) (hu : 0 < u) :
    wordIntervalExponent w Y (pre++[u])=wordIntervalExponent w Y pre-primeExponent w u := by
  have hYr : (Y:ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  have hpr : (pre.prod:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hur : (u:ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold wordIntervalExponent primeExponent
  rw [List.prod_append,List.prod_singleton,Nat.cast_mul,Real.log_div hYr (mul_ne_zero hpr hur),
    Real.log_div hYr hpr,Real.log_mul hpr hur]
  ring
end NumberTheoryLean.WordIntervalGeometry


end Erdos970

end OAI
