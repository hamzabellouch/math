import OAI.Analysis.GroupDeterminants.LampProjections

namespace OAI

universe uH uR

noncomputable section
open scoped BigOperators Pointwise

namespace LampProjectionDraft
open LampDraft AverageDraft SupportDraft GroupRingDeterminant
variable (H : Type uH) [Group H]
local instance : DecidableEq H := Classical.decEq H

variable (R : Type uR) [CommRing R]
def baseEmbedding : MonoidAlgebra R (BaseGroup H) →+* MonoidAlgebra R (LampGroup H) :=
  MonoidAlgebra.mapDomainRingHom R (BaseGroup H).subtype

lemma baseEmbedding_injective : Function.Injective (baseEmbedding H R) := by
  exact MonoidAlgebra.mapDomain_injective (Subgroup.subtype_injective (BaseGroup H))

@[simp] lemma baseEmbedding_coeff_one (a : MonoidAlgebra R (BaseGroup H)) :
    (baseEmbedding H R a).coeff 1 = a.coeff 1 := by
  exact Finsupp.mapDomain_apply_of_injective (Subgroup.subtype_injective (BaseGroup H)) a.coeff 1

variable {R}
def fullLampSymbol (h : H) : MonoidAlgebra R (LampGroup H) := MonoidAlgebra.single (lamp H h) 1

def shiftSymbol (h : H) : MonoidAlgebra R (LampGroup H) := MonoidAlgebra.single (shift H h) 1

lemma shiftSymbol_one_lamp (s : H) :
    shiftSymbol H s * fullLampSymbol H (R := R) 1 = fullLampSymbol H s * shiftSymbol H s := by
  simp only [shiftSymbol, fullLampSymbol, MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  have he := shift_conjugate_lamp H s 1
  simpa using (mul_inv_eq_iff_eq_mul.mp (by simpa using he))

def projection (S : Finset H) : MonoidAlgebra ℚ (LampGroup H) :=
  baseEmbedding H ℚ (baseProjection H S)

def average (h : H) : MonoidAlgebra ℚ (LampGroup H) := baseEmbedding H ℚ (baseAverage H h)

lemma average_def (h : H) : average H h = thirdAverage (fullLampSymbol H h) := by
  unfold average baseAverage thirdAverage
  change _ = (1 / 3 : ℚ) • (1 + _ + _)
  rw [show (baseEmbedding H ℚ) ((1 / 3 : ℚ) • _) = (1 / 3 : ℚ) •
    (baseEmbedding H ℚ) _ from map_rat_smul _ _ _]
  simp only [map_add, map_one, map_mul]
  simp [baseEmbedding, fullLampSymbol, baseLamp]

lemma projection_idempotent (S : Finset H) : IsIdempotentElem (projection H S) :=
  (baseProjection_idempotent H S).map (baseEmbedding H ℚ)

lemma projection_selfAdjoint (S : Finset H) : IsSelfAdjoint (projection H S) := by
  change star (baseEmbedding H ℚ _) = _
  change star (MonoidAlgebra.mapDomainRingHom ℚ _ _) = _
  rw [← groupAlgebra_mapDomain_star]
  exact congrArg (baseEmbedding H ℚ) (baseProjection_selfAdjoint H S)

lemma projection_trace (S : Finset H) (hS : 1 ∉ S) :
    (projection H S).coeff 1 = (1 / 3 : ℚ) * (2 / 3 : ℚ) ^ S.card := by
  rw [projection, baseEmbedding_coeff_one, baseProjection_trace H S hS]

lemma baseAverage_one_mul_projection (S : Finset H) :
    baseAverage H 1 * baseProjection H S = baseProjection H S := by
  rw [baseProjection, ← mul_assoc, baseAverage_idempotent H 1]

lemma baseProjection_mul_average_eq_zero (S : Finset H) {s : H} (hs : s ∈ S) :
    baseProjection H S * baseAverage H s = 0 := by
  have he := Finset.mul_prod_erase S (fun t => 1 - baseAverage H t) hs
  rw [baseProjection, ← he]
  have hp := baseAverage_idempotent H s
  change _ * _ = _ at hp
  calc
    _ = baseAverage H 1 * (∏ t ∈ S.erase s, (1 - baseAverage H t)) *
          ((1 - baseAverage H s) * baseAverage H s) := by ring
    _ = 0 := by rw [sub_mul, one_mul, hp, sub_self, mul_zero]

lemma shift_average (s : H) : shiftSymbol H s * average H 1 = average H s * shiftSymbol H s := by
  have hs := shiftSymbol_one_lamp H (R := ℚ) s
  rw [average_def, average_def]
  unfold thirdAverage
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  simp only [mul_add, add_mul, mul_one, one_mul]
  rw [hs]
  congr 1
  rw [← mul_assoc, hs, mul_assoc, hs, ← mul_assoc]

lemma projection_separates (S : Finset H) {s : H} (hs : s ∈ S) :
    projection H S * shiftSymbol H s * projection H S = 0 := by
  have h1 : average H 1 * projection H S = projection H S := by
    simpa only [average, projection, ← map_mul] using
      congrArg (baseEmbedding H ℚ) (baseAverage_one_mul_projection H S)
  have h0 : projection H S * average H s = 0 := by
    simpa only [average, projection, ← map_mul, map_zero] using
      congrArg (baseEmbedding H ℚ) (baseProjection_mul_average_eq_zero H S hs)
  calc
    _ = projection H S * shiftSymbol H s * (average H 1 * projection H S) := by rw [h1]
    _ = projection H S * (shiftSymbol H s * average H 1) * projection H S := by simp only [mul_assoc]
    _ = projection H S * (average H s * shiftSymbol H s) * projection H S := by rw [shift_average]
    _ = 0 := by rw [← mul_assoc, h0, zero_mul, zero_mul]

def baseSum (h : H) : MonoidAlgebra ℤ (BaseGroup H) :=
  1 + MonoidAlgebra.single (baseLamp H h) 1 + MonoidAlgebra.single (baseLamp H h) 1 ^ 2

def baseNumerator (S : Finset H) : MonoidAlgebra ℤ (BaseGroup H) :=
  baseSum H 1 * ∏ s ∈ S, (3 - baseSum H s)

def denominator (S : Finset H) : ℕ := 3 ^ (S.card + 1)

def numerator (S : Finset H) : MonoidAlgebra ℤ (LampGroup H) :=
  baseEmbedding H ℤ (baseNumerator H S)

def intToRat : MonoidAlgebra ℤ (BaseGroup H) →+* MonoidAlgebra ℚ (BaseGroup H) :=
  MonoidAlgebra.mapRingHom _ (Int.castRingHom ℚ)

lemma intToRat_baseSum (h : H) : intToRat H (baseSum H h) = (3 : ℚ) • baseAverage H h := by
  simp [intToRat, baseSum, baseAverage, thirdAverage, smul_smul, pow_two]

lemma intToRat_baseNumerator (S : Finset H) :
    intToRat H (baseNumerator H S) = (denominator H S : ℚ) • baseProjection H S := by
  have he (s : H) : intToRat H (3 - baseSum H s) = (3 : ℚ) • (1 - baseAverage H s) := by
    rw [map_sub, map_ofNat, intToRat_baseSum, smul_sub]
    simp only [← Algebra.algebraMap_eq_smul_one, map_ofNat]
  simp only [baseNumerator, map_mul, map_prod, intToRat_baseSum, he]
  rw [Finset.prod_smul, Finset.prod_const, smul_mul_smul_comm]
  simp [denominator, baseProjection, pow_succ, mul_comm]

omit [Group H] in
lemma denominator_pos (S : Finset H) : 0 < denominator H S := by
  unfold denominator; positivity
omit [Group H] in
lemma denominator_odd (S : Finset H) : Odd (denominator H S) := by
  exact (by decide : Odd 3).pow

end LampProjectionDraft

end

end OAI
