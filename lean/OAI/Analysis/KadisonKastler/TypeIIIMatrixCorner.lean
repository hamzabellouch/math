import OAI.Analysis.KadisonKastler.PublishedTypeIIIProjection
import OAI.Analysis.KadisonKastler.RegularCoreMatrixData
import OAI.Analysis.FactorGeneration.NormalDimension

namespace OAI

/-! # Countable matrix corners in type III factors

The absence of nonzero finite projections gives a proper isometry. Its
wandering projections are nonzero and orthogonal. A projection supremum
completes them to a partition of one; the published comparison theorem
then joins the pieces by partial isometries.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_proper_isometry (hM : TypeIIIFactor M) :
    ∃ w : Algebra M, star w * w = 1 ∧ w * star w ≠ 1 := by
  have hn : ¬ FiniteProjectionIn M (1 : Algebra M) := by
    intro hf
    have hz := hM.purelyInfinite 1 (IsStarProjection.one (Algebra M)) hf
    exact hM.nonzero (congrArg Subtype.val hz)
  simp only [FiniteProjectionIn, one_mul] at hn
  push Not at hn
  obtain ⟨w, hw, _, hproper⟩ := hn
  exact ⟨w, hw, hproper⟩

private theorem star_pow_mul_pow (w : Algebra M) (hw : star w * w = 1) (n : ℕ) :
    star (w ^ n) * w ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, star_mul]
    calc
      (star w * star (w ^ n)) * (w ^ n * w) =
          star w * (star (w ^ n) * w ^ n) * w := by simp only [mul_assoc]
      _ = 1 := by rw [ih, mul_one, hw]

private def wanderingProjection (w : Algebra M) (hw : star w * w = 1) :
    AlgebraProjection M :=
  ⟨1 - w * star w, (show IsStarProjection (w * star w) from ⟨by
    change (w * star w) * (w * star w) = w * star w
    calc
      _ = w * (star w * w) * star w := by simp only [mul_assoc]
      _ = _ := by rw [hw, mul_one], IsSelfAdjoint.mul_star_self w⟩).one_sub⟩

private theorem wanderingProjection_mul (w : Algebra M) (hw : star w * w = 1) :
    (wanderingProjection w hw).val * w = 0 := by
  change (1 - w * star w) * w = 0
  rw [sub_mul, one_mul, mul_assoc, hw, mul_one, sub_self]

private theorem wanderingProjection_mul_pow (w : Algebra M) (hw : star w * w = 1)
    {n : ℕ} (hn : 0 < n) : (wanderingProjection w hw).val * w ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ', ← mul_assoc, wanderingProjection_mul, zero_mul]

private def wanderingPartialIsometry (w : Algebra M) (hw : star w * w = 1) (n : ℕ) :
    PartialIsometry M where
  support := wanderingProjection w hw
  val := w ^ n * (wanderingProjection w hw).val
  initial := by
    rw [star_mul, (wanderingProjection w hw).property.isSelfAdjoint.star_eq]
    calc
      ((wanderingProjection w hw).val * star (w ^ n)) *
          (w ^ n * (wanderingProjection w hw).val) =
          (wanderingProjection w hw).val * (star (w ^ n) * w ^ n) *
            (wanderingProjection w hw).val := by simp only [mul_assoc]
      _ = (wanderingProjection w hw).val := by
        rw [star_pow_mul_pow w hw, mul_one,
          (wanderingProjection w hw).property.isIdempotentElem.eq]

private theorem wandering_cross (w : Algebra M) (hw : star w * w = 1)
    {i j : ℕ} (hij : i < j) :
    star (wanderingPartialIsometry w hw i).val *
      (wanderingPartialIsometry w hw j).val = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  change star (w ^ i * (wanderingProjection w hw).val) *
    (w ^ (i + k) * (wanderingProjection w hw).val) = 0
  rw [star_mul, (wanderingProjection w hw).property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = ((wanderingProjection w hw).val * (star (w ^ i) * w ^ i)) *
        w ^ k * (wanderingProjection w hw).val := by simp only [mul_assoc]
    _ = 0 := by
      rw [star_pow_mul_pow w hw, mul_one, wanderingProjection_mul_pow w hw hk,
        zero_mul]

private theorem wandering_targets_orthogonal (w : Algebra M) (hw : star w * w = 1) :
    Pairwise (fun i j => (wanderingPartialIsometry w hw i).target.val *
      (wanderingPartialIsometry w hw j).target.val = 0) := by
  intro i j hij
  have hforward {i j : ℕ} (hlt : i < j) :
      (wanderingPartialIsometry w hw i).target.val *
        (wanderingPartialIsometry w hw j).target.val = 0 := by
    change ((wanderingPartialIsometry w hw i).val *
      star (wanderingPartialIsometry w hw i).val) *
      ((wanderingPartialIsometry w hw j).val *
        star (wanderingPartialIsometry w hw j).val) = 0
    calc
      _ = (wanderingPartialIsometry w hw i).val *
          (star (wanderingPartialIsometry w hw i).val *
            (wanderingPartialIsometry w hw j).val) *
          star (wanderingPartialIsometry w hw j).val := by simp only [mul_assoc]
      _ = 0 := by rw [wandering_cross w hw hlt, mul_zero, zero_mul]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hforward hlt
  · exact PartialIsometry.orthogonal_reverse _ _ (hforward hgt)

/-- Every nonzero type III factor has a countably infinite orthogonal
family of nonzero projections, constructed from one proper isometry. -/
theorem TypeIIIFactor.exists_orthogonal_nonzero_projections (hM : TypeIIIFactor M) :
    ∃ p : ℕ → AlgebraProjection M,
      (∀ n, (p n).val ≠ 0) ∧ Pairwise (fun i j => (p i).val * (p j).val = 0) := by
  obtain ⟨w, hw, hproper⟩ := hM.exists_proper_isometry
  have hp : (wanderingProjection w hw).val ≠ 0 := by
    change 1 - w * star w ≠ 0
    exact sub_ne_zero.mpr hproper.symm
  refine ⟨fun n => (wanderingPartialIsometry w hw n).target, ?_,
    wandering_targets_orthogonal w hw⟩
  intro n hz
  have hv : (wanderingPartialIsometry w hw n).val = 0 :=
    (CStarRing.mul_star_self_eq_zero_iff _).mp hz
  have hi := (wanderingPartialIsometry w hw n).initial
  rw [hv, star_zero, zero_mul] at hi
  exact hp hi.symm

private def orthogonalProjectionNet (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (s : Finset ℕ) : AlgebraProjection M :=
  AlgebraProjection.finsetSum p s (fun _ _ _ _ hij => ho hij)

private theorem orthogonalProjectionNet_mono (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) :
    Monotone (orthogonalProjectionNet p ho) := by
  intro s t hst
  apply (AlgebraProjection.finsetSum_le_iff p s _ _).mpr
  intro i hi
  exact (AlgebraProjection.finsetSum_le_iff p t _ _).mp le_rfl i (hst hi)

private theorem exists_orthogonalProjection_sum (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) :
    ∃ q : AlgebraProjection M, (∀ i, p i ≤ q) ∧
      ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x)
        ((q.val : H →L[ℂ] H) x) := by
  let a := orthogonalProjectionNet p ho
  have ha : Monotone a := orthogonalProjectionNet_mono p ho
  obtain ⟨q, hq⟩ := AlgebraProjection.exists_isLUB_monotone a ha
  refine ⟨q, ?_, ?_⟩
  · intro i
    have hi : p i ≤ a {i} :=
      (AlgebraProjection.finsetSum_le_iff p {i} _ _).mp le_rfl i (by simp)
    exact hi.trans (hq.1 ⟨{i}, rfl⟩)
  · intro x
    have hv := AlgebraProjection.vectorValue_tendsto_monotone a ha q hq x
    have hs (s : Finset ℕ) :
        ‖(q.val : H →L[ℂ] H) x - ((a s).val : H →L[ℂ] H) x‖ ^ 2 =
          AlgebraProjection.vectorValue x q - AlgebraProjection.vectorValue x (a s) := by
      have hh := AlgebraProjection.vectorValue_remainder x (a s) q (hq.1 ⟨s, rfl⟩)
      rw [AlgebraProjection.vectorValue_eq_norm_sq] at hh
      exact hh
    have hc : Tendsto (fun _ : Finset ℕ => AlgebraProjection.vectorValue x q)
        atTop (𝓝 (AlgebraProjection.vectorValue x q)) := tendsto_const_nhds
    have hh := hc.sub hv
    rw [sub_self] at hh
    have hsquare := hh.congr (fun s => (hs s).symm)
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    have hnorm : Tendsto (fun s : Finset ℕ =>
        ‖((a s).val : H →L[ℂ] H) x - (q.val : H →L[ℂ] H) x‖) atTop (𝓝 0) := by
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
        Real.sqrt_zero, norm_sub_rev, Function.comp_def] using hn
    have ht := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
    have ha_apply (s : Finset ℕ) :
        ((a s).val : H →L[ℂ] H) x = ∑ i ∈ s, ((p i).val : H →L[ℂ] H) x := by
      change (M.toStarSubalgebra.subtype (∑ i ∈ s, (p i).val)) x = _
      rw [map_sum]
      simp only [sum_apply]
      rfl
    simpa only [HasSum, SummationFilter.unconditional, ha_apply] using ht

/-- An infinite nonzero orthogonal family can be completed to a nonzero
strong partition of one by adding its residual projection to its first term. -/
theorem exists_nonzero_projection_partition_of_orthogonal
    (p : ℕ → AlgebraProjection M) (hp : ∀ i, (p i).val ≠ 0)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) :
    ∃ d : ℕ → AlgebraProjection M, (∀ i, (d i).val ≠ 0) ∧
      Pairwise (fun i j => (d i).val * (d j).val = 0) ∧
      ∀ x : H, HasSum (fun i => ((d i).val : H →L[ℂ] H) x) x := by
  classical
  obtain ⟨q, hpq, hsum⟩ := exists_orthogonalProjection_sum p ho
  let r : AlgebraProjection M := ⟨1 - q.val, q.property.one_sub⟩
  have hpr (i : ℕ) : (p i).val * r.val = 0 := by
    change (p i).val * (1 - q.val) = 0
    rw [mul_sub, mul_one, projection_mul_of_le (hpq i), sub_self]
  have hrp (i : ℕ) : r.val * (p i).val = 0 :=
    PartialIsometry.orthogonal_reverse _ _ (hpr i)
  let d (i : ℕ) : AlgebraProjection M :=
    if i = 0 then orthogonalSum (p 0) r (hpr 0) else p i
  have hd (i : ℕ) : (d i).val = (p i).val + if i = 0 then r.val else 0 := by
    by_cases hi : i = 0
    · subst i; simp [d, orthogonalSum]
    · simp only [d, ite_eq_right hi, add_zero]
  refine ⟨d, ?_, ?_, ?_⟩
  · intro i hz
    by_cases hi : i = 0
    · subst i
      have hle := le_orthogonalSum_left (p 0) r (hpr 0)
      change (d 0).val * (p 0).val = (p 0).val at hle
      rw [hz, zero_mul] at hle
      exact hp 0 hle.symm
    · exact hp i (by simpa only [d, ite_eq_right hi] using hz)
  · intro i j hij
    rw [hd, hd]
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := Ne.symm hij
      simp only [ite_true, ite_eq_right hj, add_zero, add_mul, ho hij, hrp]
    · by_cases hj : j = 0
      · subst j
        simp only [ite_true, ite_eq_right hi, add_zero, mul_add, ho hij, hpr]
      · simpa only [ite_eq_right hi, ite_eq_right hj, add_zero] using ho hij
  · intro x
    have hs := (hsum x).add (hasSum_ite_eq (0 : ℕ) ((r.val : H →L[ℂ] H) x))
    have ht : (q.val : H →L[ℂ] H) x + (r.val : H →L[ℂ] H) x = x := by
      change (q.val : H →L[ℂ] H) x + ((1 : H →L[ℂ] H) - q.val) x = x
      simp only [sub_apply, one_apply_eq_self]
      abel
    rw [ht] at hs
    apply hs.congr_fun
    intro i
    rw [hd]
    by_cases hi : i = 0 <;> simp [hi]

/-- The projection partition required for countable matrix units is
constructed without any trace or extra projection-comparison assumption. -/
theorem TypeIIIFactor.exists_nonzero_projection_partition (hM : TypeIIIFactor M) :
    ∃ d : ℕ → AlgebraProjection M, (∀ i, (d i).val ≠ 0) ∧
      Pairwise (fun i j => (d i).val * (d j).val = 0) ∧
      ∀ x : H, HasSum (fun i => ((d i).val : H →L[ℂ] H) x) x := by
  obtain ⟨p, hp, ho⟩ := hM.exists_orthogonal_nonzero_projections
  exact exists_nonzero_projection_partition_of_orthogonal p hp ho

/-- The closed initial Hilbert space associated to a concrete projection. -/
def typeIIIInitialSpace (p : AlgebraProjection M) : Submodule ℂ H :=
  (p.val : H →L[ℂ] H).range

instance typeIIIInitialSpaceComplete (p : AlgebraProjection M) :
    CompleteSpace (typeIIIInitialSpace p) := by
  have hp : IsIdempotentElem (p.val : H →L[ℂ] H) := by
    change (p.val : H →L[ℂ] H) * p.val = p.val
    exact congrArg Subtype.val p.property.isIdempotentElem.eq
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp).completeSpace_coe

theorem typeIIIInitialSpace_projection (p : AlgebraProjection M) :
    (p.val : H →L[ℂ] H) = (typeIIIInitialSpace p).starProjection := by
  have hp : IsStarProjection (p.val : H →L[ℂ] H) := ⟨by
    change (p.val : H →L[ℂ] H) * p.val = p.val
    exact congrArg Subtype.val p.property.isIdempotentElem.eq,
    congrArg Subtype.val p.property.isSelfAdjoint.star_eq⟩
  obtain ⟨_, he⟩ := isStarProjection_iff_eq_starProjection_range.mp hp
  exact he

/-- Countable full matrix corners exist in every separably acting type III
factor. Only the published comparison of nonzero projections is used. -/
theorem TypeIIIFactor.exists_fullMatrixCorner [TopologicalSpace.SeparableSpace H]
    (hM : TypeIIIFactor M) (hCompare : PublishedTypeIIIProjectionComparison.{u}) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      ∃ F : FullMatrixCorner (typeIIIInitialSpace p), ∀ i j, F.entry i j ∈ M := by
  obtain ⟨d, hd, ho, hsum⟩ := hM.exists_nonzero_projection_partition
  have ha : ∀ i, ∃ a : Algebra M, star a * a = 1 ∧ a * star a = (d i).val :=
    fun i => hCompare H M hM (d i).val (d i).property (hd i)
  choose a hai haf using ha
  let v (i : ℕ) : Algebra M := a i * star (a 0)
  have hvi (i : ℕ) : star (v i) * v i = (d 0).val := by
    change star (a i * star (a 0)) * (a i * star (a 0)) = (d 0).val
    rw [star_mul, star_star]
    calc
      _ = a 0 * (star (a i) * a i) * star (a 0) := by simp only [mul_assoc]
      _ = (d 0).val := by rw [hai, mul_one, haf]
  have hvf (i : ℕ) : v i * star (v i) = (d i).val := by
    change (a i * star (a 0)) * star (a i * star (a 0)) = (d i).val
    rw [star_mul, star_star]
    calc
      _ = a i * (star (a 0) * a 0) * star (a i) := by simp only [mul_assoc]
      _ = (d i).val := by rw [hai, mul_one, haf]
  let F := FullMatrixCorner.ofEquivalentProjectionFamily (typeIIIInitialSpace (d 0))
    d v hvi hvf ho (typeIIIInitialSpace_projection (d 0)) hsum
  exact ⟨d 0, hd 0, F,
    FullMatrixCorner.ofEquivalentProjectionFamily_entry_mem _ d v hvi hvf ho
      (typeIIIInitialSpace_projection (d 0)) hsum⟩

end

end KadisonKastler

end OAI
