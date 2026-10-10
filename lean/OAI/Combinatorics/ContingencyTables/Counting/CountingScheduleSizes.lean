import OAI.Combinatorics.ContingencyTables.Counting.CountingPhaseSchedule

namespace OAI

/-! # Polynomial numeric bounds for the explicit counting schedules -/

namespace ContingencyTables.CountingPhaseSchedule

/-- A natural reciprocal-accuracy allowance bounds the rational inverse
tolerance; no logarithmic operation is used. -/
lemma inverse_tolerance_le (H E : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) :
    1/tolerance H epsilon ≤ (800*(H+1)*E:ℕ) := by
  have heq : 1/tolerance H epsilon=(800:ℚ)*(H+1)*(1/epsilon) := by
    unfold tolerance
    field_simp
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 800*(H+1) by positivity)
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh

def observationBound (p W H E : ℕ) : ℕ :=
  1024*(H+1)*observationCoefficient p W*(800*(H+1)*E)^2+2

lemma observations_le (p W H E : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) :
    observations p W H (tolerance H epsilon) ≤ observationBound p W H E := by
  have heta := tolerance_pos H epsilon he
  have hinv := inverse_tolerance_le H E epsilon he hE
  have hinv0 : (0:ℚ) ≤ 1/tolerance H epsilon := (one_div_pos.mpr heta).le
  have hs : (1/tolerance H epsilon)^2 ≤ ((800*(H+1)*E:ℕ):ℚ)^2 := by
    nlinarith
  have hb : (1024:ℚ)*(H+1)*observationCoefficient p W/(tolerance H epsilon)^2 ≤
      (1024*(H+1)*observationCoefficient p W*(800*(H+1)*E)^2:ℕ) := by
    calc
      _ = ((1024:ℚ)*(H+1)*observationCoefficient p W)*(1/tolerance H epsilon)^2 := by ring
      _ ≤ ((1024:ℚ)*(H+1)*observationCoefficient p W)*((800*(H+1)*E:ℕ):ℚ)^2 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by push_cast; ring
  have hc := Nat.ceil_le.mpr hb
  unfold observations observationBound
  omega

def precisionBound (p W H tau E : ℕ) : ℕ :=
  1024*(H+1)*noiseCoefficient H tau (observationBound p W H E) (returnCap p H tau)+
    800*(H+1)*E+2

lemma precision_le (p W H tau E : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) :
    precision H tau (observations p W H (tolerance H epsilon)) (returnCap p H tau)
      (tolerance H epsilon) ≤ precisionBound p W H tau E := by
  have hN := observations_le p W H E epsilon he hE
  have hceil : ⌈1/tolerance H epsilon⌉₊ ≤ 800*(H+1)*E :=
    Nat.ceil_le.mpr (inverse_tolerance_le H E epsilon he hE)
  have hcoef : noiseCoefficient H tau
      (observations p W H (tolerance H epsilon)) (returnCap p H tau) ≤
        noiseCoefficient H tau (observationBound p W H E) (returnCap p H tau) := by
    unfold noiseCoefficient
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 8 (Nat.add_le_add_right hN 1)) _
  unfold precision precisionBound
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ hcoef) hceil) 1).trans
    (by omega)

lemma returnCap_eq (p H tau : ℕ) :
    returnCap p H tau=65536*(H+1)^2*(tau+1)*(p^2+1) := rfl

lemma initialPrecision_eq (H : ℕ) : initialPrecision H=2048*(H+1) := rfl

end ContingencyTables.CountingPhaseSchedule

end OAI
