import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyMemo
import OAI.Combinatorics.EditApproximation.Binary.BitMemoWorkOn

namespace OAI

/-! The complete mixed memo is normalized on the physical
table grid.  Its actual ranked binary values and adaptive reference trace
agree on every coarse seed and every finite scalar draw. -/

namespace EditApproximation

private theorem familyBase_pos (ell : ℕ) (base : List Bool)
    (hbase : bitWordValue base = ell ^ 10 + 1) : 0 < bitWordValue base := by
  rw [hbase]
  omega

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)
  (initial : PhysicalEntry M J target.length → ℕ)
  (ha : ∀ pass, pass ≤ passes → (a pass).value = refinementFactor (BinaryFraction.value (A pass)) F)
  (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
  (hp : target.length ≤ 2 ^ positionBits)
  (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
  (hc : ∀ entry, (coarse entry).1.value = initial entry)
  (ell : ℕ) (hell : 0 < ell) (hdelta : delta.value = 1 / (ell : ℚ) ^ 10)
  (base : List Bool) (hbase : bitWordValue base = ell ^ 10 + 1)

local notation "raw" => queryFamilyMemoRaw source target N P F exponent H Q eM eF hP hM hF
  A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw
local notation "reference" => SourceRanked.body ChargedPhysicalRequest.rank
  (physicalFamilyProgram source target N P F exponent H Q T S passes copies
    (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial)
  (physicalFamilyAnswer target N P F exponent H Q passes copies draw)
local notation "semantic" => SourceRanked.value
  (physicalFamilyAnswer target N P F exponent H Q passes copies draw)
  (physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
    (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial hP draw)
local notation "normalized" => queryFamilyMemoNormalized source target N P F exponent H Q eM eF hP hM hF
  A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw
  base (familyBase_pos ell base hbase)

include ha hs ht hp htable hc hell hdelta in
theorem queryFamilyMemoNormalized_correct
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank) normalized key).value =
        semantic key ∧
      BitQuery.RefinesOn
        (fun child => rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
          normalized child.val)
        (fun word value => word.value = value) (normalized key) (reference key) := by
  have hraw (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
      BitQuery.Refines (fun word value => word.value = value) (raw key) (reference key) :=
    queryFamilyMemoRaw_refines source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw
      ha hs ht hp htable initial hc key
  have hbody (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
      (reference key).value (fun child => semantic child.val) = semantic key := by
    apply SourceRanked.body_value
    intro request
    exact physicalFamilyProgram_value source target N P F exponent H Q T S passes copies
      (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial hP draw request
  have hd (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
      (semantic key).den ∣ bitWordValue base ^ queryFamilyMemoRemaining (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q key := by
    cases key with
    | inl source =>
      change ((draw source).val : ℚ).den ∣ _
      rw [Rat.den_natCast]
      exact one_dvd _
    | inr request =>
      change (physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
        (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial hP draw
        request).den ∣ bitWordValue base ^ chargedPhysicalRemaining request
      unfold physicalFamilyRequestValue
      rw [hdelta, hbase]
      exact chargedRequestValue_den_dvd source target N P F exponent H Q T S (passes + 1) copies ell
        (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value _ _ initial hell request
  exact rankedNormalizeBody_correct (SourceRanked.rank ChargedPhysicalRequest.rank) raw reference
    semantic hraw hbody base (familyBase_pos ell base hbase)
    (queryFamilyMemoRemaining (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) hd key

include ha hs ht hp htable hc hell hdelta in
theorem queryFamilyMemoNormalized_width
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q)
    (B V : ℕ) (hB : base.length ≤ B) (hV : |semantic key| ≤ (V : ℚ)) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank) normalized key).width ≤
      Nat.size V + 2 * (queryFamilyMemoRemaining (M := M) (J := J) (R := R)
        (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q key * B + 1) + 1 := by
  have hraw (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
      BitQuery.Refines (fun word value => word.value = value) (raw key) (reference key) :=
    queryFamilyMemoRaw_refines source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw
      ha hs ht hp htable initial hc key
  have hbody (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
      (reference key).value (fun child => semantic child.val) = semantic key := by
    apply SourceRanked.body_value
    intro request
    exact physicalFamilyProgram_value source target N P F exponent H Q T S passes copies
      (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial hP draw request
  have hd (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
      (semantic key).den ∣ bitWordValue base ^ queryFamilyMemoRemaining (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q key := by
    cases key with
    | inl source =>
      change ((draw source).val : ℚ).den ∣ _
      rw [Rat.den_natCast]
      exact one_dvd _
    | inr request =>
      change (physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
        (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value delta.value initial hP draw
        request).den ∣ bitWordValue base ^ chargedPhysicalRemaining request
      unfold physicalFamilyRequestValue
      rw [hdelta, hbase]
      exact chargedRequestValue_den_dvd source target N P F exponent H Q T S (passes + 1) copies ell
        (fun pass => BinaryFraction.value (A pass)) multiplier tau.value eta.value kappa.value _ _ initial hell request
  exact rankedNormalizeBody_width (SourceRanked.rank ChargedPhysicalRequest.rank) raw reference
    semantic hraw hbody base (familyBase_pos ell base hbase)
    (queryFamilyMemoRemaining (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q)
    hd key B V hB hV


include ha hs ht hp htable hc hell hdelta in
theorem queryFamilyMemoNormalized_decode (bits : ℕ)
    (encode : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies)
      (T := T) (S := S) target N P F exponent H Q → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies)
      (T := T) (S := S) target N P F exponent H Q) :
    (rankedBitMemoEvaluate (SourceRanked.rank ChargedPhysicalRequest.rank) normalized bits encode key
      .empty).decode =
      rankedMemoEvaluate (SourceRanked.rank ChargedPhysicalRequest.rank) reference bits encode key .empty := by
  apply rankedBitMemoEvaluate_decode_on _ _ _ _ bits encode hinjective hbounded key .empty
    (bitMemoSound_empty _ _ _)
  intro next
  exact (queryFamilyMemoNormalized_correct source target N P F exponent H Q eM eF hP hM hF
    A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw initial
    ha hs ht hp htable hc ell hell hdelta base hbase next).2

include ha hs ht hp htable hc hell hdelta in
theorem queryFamilyMemoNormalized_work_transfer (bits : ℕ)
    (encode : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies)
      (T := T) (S := S) target N P F exponent H Q → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies)
      (T := T) (S := S) target N P F exponent H Q) :
    (rankedBitMemoEvaluate (SourceRanked.rank ChargedPhysicalRequest.rank) normalized bits encode key
      .empty).localWork =
      rankedMemoKernelWork (SourceRanked.rank ChargedPhysicalRequest.rank) reference bits encode
        (rankedBitLocalWork (SourceRanked.rank ChargedPhysicalRequest.rank) normalized) key .empty := by
  apply rankedBitMemoEvaluate_work_transfer_on _ _ _ _ bits encode hinjective hbounded key .empty
    (bitMemoSound_empty _ _ _)
  intro next
  exact (queryFamilyMemoNormalized_correct source target N P F exponent H Q eM eF hP hM hF
    A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw initial
    ha hs ht hp htable hc ell hell hdelta base hbase next).2

end Family
end EditApproximation

end OAI
