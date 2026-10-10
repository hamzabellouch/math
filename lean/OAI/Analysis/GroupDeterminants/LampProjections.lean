import OAI.Analysis.GroupDeterminants.Lamps

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace LampProjectionDraft
open LampDraft AverageDraft SupportDraft GroupRingDeterminant
variable (H : Type uH) [Group H]
local instance : DecidableEq H := Classical.decEq H

def baseAverage (h : H) : MonoidAlgebra ℚ (BaseGroup H) :=
  thirdAverage (MonoidAlgebra.single (baseLamp H h) 1)

lemma baseAverage_idempotent (h : H) : IsIdempotentElem (baseAverage H h) := by
  apply thirdAverage_square
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  have he : baseLamp H h * baseLamp H h * baseLamp H h = 1 := by
    simpa only [pow_succ, pow_zero, one_mul] using baseLamp_cube H h
  rw [he, ← MonoidAlgebra.one_def]

lemma baseAverage_selfAdjoint (h : H) : IsSelfAdjoint (baseAverage H h) := by
  have he : (baseLamp H h)⁻¹ = baseLamp H h * baseLamp H h :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_succ, pow_zero, one_mul, mul_assoc]
      using (baseLamp_cube H h))
  have he2 : (baseLamp H h * baseLamp H h)⁻¹ = baseLamp H h := by
    rw [← he, inv_inv]
  change star (baseAverage H h) = baseAverage H h
  simp only [baseAverage, thirdAverage, MonoidAlgebra.single_mul_single, one_mul,
    star_smul, star_add, star_one, star_groupAlgebra_single, he, he2, star_trivial]
  congr 1
  abel

lemma baseAverage_supported (h : H) : SupportedOn (baseCoordinate H) {h} (baseAverage H h) := by
  have hs : SupportedOn (baseCoordinate H) {h}
      (MonoidAlgebra.single (baseLamp H h) (1 : ℚ)) :=
    supportedOn_single _ _ _ _ (by intro i hi; simp_all)
  unfold baseAverage thirdAverage
  apply supportedOn_smul
  apply supportedOn_add
  · exact supportedOn_add _ (supportedOn_one _ _) hs
  · simpa only [Set.union_self] using supportedOn_mul _ hs hs

lemma baseAverage_trace (h : H) : (baseAverage H h).coeff 1 = 1 / 3 := by
  simp [baseAverage, thirdAverage, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.coeff_single, baseLamp_ne_one, baseLamp_sq_ne_one]

def baseProjection (S : Finset H) : MonoidAlgebra ℚ (BaseGroup H) :=
  baseAverage H 1 * ∏ s ∈ S, (1 - baseAverage H s)

lemma complement_prod_idempotent (S : Finset H) :
    IsIdempotentElem (∏ s ∈ S, (1 - baseAverage H s)) := by
  induction S using Finset.induction_on with
  | empty => simp [IsIdempotentElem]
  | @insert s S hs ih =>
    rw [Finset.prod_insert hs]
    exact (baseAverage_idempotent H s).one_sub.mul ih

lemma baseProjection_idempotent (S : Finset H) : IsIdempotentElem (baseProjection H S) :=
  (baseAverage_idempotent H 1).mul (complement_prod_idempotent H S)

lemma complement_prod_selfAdjoint (S : Finset H) :
    IsSelfAdjoint (∏ s ∈ S, (1 - baseAverage H s)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert s S hs ih =>
    rw [Finset.prod_insert hs]
    exact ((IsSelfAdjoint.one _).sub (baseAverage_selfAdjoint H s)).mul ih

lemma baseProjection_selfAdjoint (S : Finset H) : IsSelfAdjoint (baseProjection H S) :=
  (baseAverage_selfAdjoint H 1).mul (complement_prod_selfAdjoint H S)

lemma baseProjection_trace (S : Finset H) (hS : 1 ∉ S) :
    (baseProjection H S).coeff 1 = (1 / 3 : ℚ) * (2 / 3 : ℚ) ^ S.card := by
  have hi (b : BaseGroup H) (hb : ∀ i, baseCoordinate H i b = 1) : b = 1 :=
    baseCoordinate_injective H (by simpa using hb)
  have hc (s : H) : SupportedOn (baseCoordinate H) {s} (1 - baseAverage H s) :=
    supportedOn_sub _ (supportedOn_one _ _) (baseAverage_supported H s)
  rw [baseProjection, coeff_one_mul_of_disjoint (baseCoordinate H) hi (by simpa using hS)
    _ _ (baseAverage_supported H 1) (supportedOn_prod _ _ _ (by intro i _; exact hc i)),
    baseAverage_trace, coeff_one_prod (baseCoordinate H) hi _ _ (by intro i _; exact hc i)]
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, baseAverage_trace]
  norm_num [div_pow]

lemma baseProjection_trace_pos (S : Finset H) (hS : 1 ∉ S) :
    0 < (baseProjection H S).coeff 1 := by
  rw [baseProjection_trace H S hS]
  positivity

end LampProjectionDraft

end

end OAI
