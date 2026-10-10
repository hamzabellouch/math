import OAI.Geometry.HeilbronnTriangle.ParameterSampling
import OAI.Geometry.HeilbronnTriangle.IntegerPointLawPairs

namespace OAI


noncomputable section

namespace Problem355.Parameters.PrimeParameterData

variable {k r : ℕ} (D : PrimeParameterData k r)

def liftMultiplicity : ℕ := D.M ^ 9

lemma liftMultiplicity_pos : 0 < D.liftMultiplicity :=
  pow_pos D.M_pos _

lemma liftMultiplicity_mul_moduli :
    D.liftMultiplicity * (D.h * D.q) = D.N := by
  change D.M ^ 9 * D.M = D.M ^ 10
  exact (pow_succ D.M 9).symm

lemma moduli_dvd_N : D.h * D.q ∣ D.N := by
  rw [← D.liftMultiplicity_mul_moduli]
  exact dvd_mul_left _ _

lemma N_div_moduli : D.N / (D.h * D.q) = D.liftMultiplicity := by
  rw [← D.liftMultiplicity_mul_moduli]
  exact Nat.mul_div_left _ D.M_pos

lemma h_pos : 0 < D.h := lt_of_lt_of_le (by norm_num : 0 < 3) D.h_ge_three

end Problem355.Parameters.PrimeParameterData

namespace Problem355.PrimeLiftParameters

open Parameters Parameters.PrimeParameterData ParameterSampling

variable {k r : ℕ}

def pointLaw (D : PrimeParameterData k r)
    {Ω Δ : Type} [Fintype Ω] [Fintype Δ]
    (s : ℕ) (hs : 0 < s)
    (w : Ω → ℝ) (p : Δ → ℝ)
    (c : Δ → Fin 3 → ZMod D.h)
    (V : Ω → Finset (Fin 3 → ZMod D.q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ δ, 0 ≤ p δ) (hpsum : ∑ δ, p δ = 1)
    (hV : ∀ ω, (V ω).card = s) : PointLaw := by
  letI : NeZero D.h := ⟨ne_of_gt D.h_pos⟩
  letI : NeZero D.q := ⟨D.auxiliary_prime.ne_zero⟩
  exact IntegerPointLaw.ofSpecialLinear D.h D.q D.liftMultiplicity s
    D.coprime D.liftMultiplicity_pos hs w p c V hw hwsum hp hpsum hV

theorem pairProbability_le (D : PrimeParameterData k r)
    {Ω Δ : Type} [Fintype Ω] [Fintype Δ]
    (s : ℕ) (hs : 0 < s)
    (w : Ω → ℝ) (p : Δ → ℝ)
    (c : Δ → Fin 3 → ZMod D.h)
    (V : Ω → Finset (Fin 3 → ZMod D.q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ δ, 0 ≤ p δ) (hpsum : ∑ δ, p δ = 1)
    (hV : ∀ ω, (V ω).card = s) :
    (pointLaw D s hs w p c V hw hwsum hp hpsum hV).pairProbability ≤
      8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 := by
  let : NeZero D.h := ⟨ne_of_gt D.h_pos⟩
  let : NeZero D.q := ⟨D.auxiliary_prime.ne_zero⟩
  have hpair := IntegerPointLaw.ofSpecialLinear_pairProbability_le
    D.h D.q D.liftMultiplicity s D.coprime D.liftMultiplicity_pos hs
    w p c V hw hwsum hp hpsum hV
  simpa only [pointLaw, D.liftMultiplicity_mul_moduli, M] using hpair

theorem configuration_of_triple_bound (D : PrimeParameterData k r)
    {Ω Δ : Type} [Fintype Ω] [Fintype Δ]
    (s : ℕ) (hs : 0 < s)
    (w : Ω → ℝ) (p : Δ → ℝ)
    (c : Δ → Fin 3 → ZMod D.h)
    (V : Ω → Finset (Fin 3 → ZMod D.q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ δ, 0 ≤ p δ) (hpsum : ∑ δ, p δ = 1)
    (hV : ∀ ω, (V ω).card = s)
    {Ct : ℝ} (hCt : 0 ≤ Ct)
    (hlarge : 32 + 24 * Ct * (31620 * k + 1 : ℝ) ^ 2 < r)
    (htriple :
      (pointLaw D s hs w p c V hw hwsum hp hpsum hV).tripleProbability
          (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
        Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
          ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) :
    ∃ P : Finset Point, P.card = D.sampleCard ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P (D.tau / (16 * (D.N : ℝ) ^ 3)) := by
  apply configuration_of_law D
    (pointLaw D s hs w p c V hw hwsum hp hpsum hV)
    (Cp := 8) (Ct := Ct) (by norm_num) hCt
  · simpa only [show (4 : ℝ) * 8 = 32 by norm_num] using hlarge
  · exact pairProbability_le D s hs w p c V hw hwsum hp hpsum hV
  · exact htriple

end Problem355.PrimeLiftParameters

end

end OAI
