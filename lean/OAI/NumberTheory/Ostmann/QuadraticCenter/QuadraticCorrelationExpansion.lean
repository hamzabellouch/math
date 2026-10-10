import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylDifference
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationCutoffLiteral
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticCorrelationScale

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def positiveQuadraticSum (d : ℕ) (a : ℕ → ℂ) (s v : ℕ) (R α : ℝ) : ℂ :=
  normalizedSmoothQuadraticSum 1 (Real.sqrt (R / ((s : ℝ) * v / d)))
    a (α * ((s : ℝ) * v / d))

def quadraticCrossMode (d e : ℕ) (a b : ℕ → ℂ) (s v w w' : ℕ) (R α : ℝ) : ℂ :=
  (a w * conj (b w') *
    weylPhase ((s : ℝ) * (α * v * ((w : ℝ)^2 / d - (w' : ℝ)^2 / e)))) *
      quadraticCutoffWeight R d e v w w' s

theorem quadraticCorrelation_cutoff_argument {d s v R : ℝ}
    (hd : 0 < d) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (w : ℝ) :
    (w / Real.sqrt (R / (s*v/d)))^2 = s*v*w^2/(R*d) := by
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp

theorem positiveQuadraticSum_truncation {d s v W : ℕ} [NeZero d]
    (a : ℕ → ℂ) {R : ℝ} (α : ℝ) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R)
    (hW : ⌊Real.sqrt (R / ((s : ℝ)*v/d))⌋₊ ≤ W) :
    positiveQuadraticSum d a s v R α =
      (((Real.sqrt (R / ((s : ℝ)*v/d)))⁻¹ : ℝ) : ℂ) *
        ∑ w ∈ Finset.Ioc 0 W,
          a w * weylPhase (α * ((s : ℝ)*v/d) * (w : ℝ)^2) *
            cutoffFourier ((s : ℝ)*v*(w : ℝ)^2/(R*d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  unfold positiveQuadraticSum
  rw [normalizedSmoothQuadraticSum_truncation (by positivity) hW]
  simp only [one_dvd, Finset.filter_true]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  rw [quadraticCorrelation_cutoff_argument hd' hs' hv' hR]

theorem positiveQuadraticSum_cross_expansion {d e s v W V : ℕ} [NeZero d] [NeZero e]
    (a b : ℕ → ℂ) {R : ℝ} (α : ℝ) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R)
    (hW : ⌊Real.sqrt (R / ((s : ℝ)*v/d))⌋₊ ≤ W)
    (hV : ⌊Real.sqrt (R / ((s : ℝ)*v/e))⌋₊ ≤ V) :
    positiveQuadraticSum d a s v R α * conj (positiveQuadraticSum e b s v R α) /
        (s : ℂ) =
      (((v : ℝ)/(R*(Real.sqrt d*Real.sqrt e)) : ℝ) : ℂ) *
        ∑ w ∈ Finset.Ioc 0 W, ∑ w' ∈ Finset.Ioc 0 V,
          quadraticCrossMode d e a b s v w w' R α := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have he' : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_neZero e
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  rw [positiveQuadraticSum_truncation a α hs hv hR hW,
    positiveQuadraticSum_truncation b α hs hv hR hV]
  simp only [map_mul, map_sum, Complex.conj_ofReal]
  have hn := congrArg (fun x : ℝ => (x : ℂ))
    (quadraticCorrelation_normalization hd' he' hs' hv' hR)
  push_cast at hn
  have halg (x y A B : ℂ) : (x*A)*(y*B)/(s:ℂ) = (x*y/(s:ℂ))*(A*B) := by ring
  rw [halg]
  push_cast
  rw [hn, Finset.sum_mul]
  congr 1
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro w' hw'
  unfold quadraticCrossMode quadraticCutoffWeight
  simp only [weylPhase_conj]
  rw [show (s : ℝ)*(α*v*((w:ℝ)^2/d-(w':ℝ)^2/e)) =
    (α*((s:ℝ)*v/d)*(w:ℝ)^2) + -(α*((s:ℝ)*v/e)*(w':ℝ)^2) by ring,
    weylPhase_add]
  ring

end Ostmann.QuadraticCenter

end

end OAI
