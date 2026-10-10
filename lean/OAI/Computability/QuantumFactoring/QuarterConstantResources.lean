import Mathlib
import OAI.Computability.QuantumFactoring.QuarterPreparation
import OAI.Computability.QuantumFactoring.RationalHeightResources

namespace OAI



section

namespace ExactQuantumFactoring
namespace RatHeightPoly
variable {a : ℕ→ℚ}
lemma floor (ha : RatHeightPoly a) : PolyBound (fun n=>(Int.floor (a n)).natAbs.size) := by
  apply ha.1.of_le
  intro n
  apply Nat.size_le_size
  rw [Rat.floor_def']
  exact Int.natAbs_ediv_le_natAbs _ _
end RatHeightPoly
namespace Exactness
lemma completionCoeff_height {E : ℕ→ℕ} {z A : ℕ→ℚ} (hE : PolyBound E)
    (hz : RatHeightPoly z) (hA : RatHeightPoly A) :
    RatHeightPoly (fun n=>completionCoeff (E n) (z n) (A n)) := by
  have hpow:=(RatHeightPoly.constant 2).pow hE
  exact (RatHeightPoly.intCast (hpow.mul (hz.div hA)).floor).div hpow
lemma quarterCoeff_height {J : ℕ→ℕ} {p : ℕ→ℚ} (hJ : PolyBound J) (hp : RatHeightPoly p) :
    RatHeightPoly (fun n=>quarterCoeff (J n) (p n)) :=
  completionCoeff_height (hJ.add (PolyBound.const 2)) (RatHeightPoly.constant (1/2)) hp
lemma quarterRemainder_height {J : ℕ→ℕ} {p : ℕ→ℚ} (hJ : PolyBound J) (hp : RatHeightPoly p) :
    RatHeightPoly (fun n=>quarterRemainder (J n) (p n)) :=
  (RatHeightPoly.constant (1/4)).sub ((hp.mul (quarterCoeff_height hJ hp)).div (RatHeightPoly.constant 2))
lemma knownProbability_height : RatHeightPoly knownProbability :=
  ((RatHeightPoly.constant 1).sub ((RatHeightPoly.constant 1).div
    ((RatHeightPoly.constant 2).pow PolyBound.id))).pow (PolyBound.id.pow 10)
end Exactness
namespace Quarter
lemma retention_height : RatHeightPoly retention :=
  Exactness.quarterCoeff_height (PolyBound.id.mul PolyBound.id) Exactness.knownProbability_height
lemma guessRetention_height : RatHeightPoly guessRetention :=
  ((RatHeightPoly.constant 2).pow ((PolyBound.id.mul PolyBound.id).add (PolyBound.const 1))).mul
    (Exactness.quarterRemainder_height (PolyBound.id.mul PolyBound.id) Exactness.knownProbability_height)
lemma D_poly : PolyBound D := by
  unfold D Completion.coinBits
  poly_bound
end Quarter
end ExactQuantumFactoring

end



end OAI
