import OAI.MeasureTheory.Falconer.Angular.AngularGrid

namespace OAI

/-!
# Finite sampled direction families

Ball counts for the sampled direction labels control both multiplicities
and normalized ball counts of the rounded incident line families. The
estimates below retain the original labels, including repeated directions.
-/

namespace Falconer
open Set
open scoped BigOperators

noncomputable def roundedLineFamily {ι : Type*} [DecidableEq ι]
    (δ : ℝ) (x : Space 2) (m : ι → ℝ) (S : Finset ι) : Finset (Space 2) :=
  S.image (fun i => roundedIncidentLine δ x (m i))

theorem roundedLineFamily_nonempty {ι : Type*} [DecidableEq ι]
    (δ : ℝ) (x : Space 2) (m : ι → ℝ) {S : Finset ι} (hS : S.Nonempty) :
    (roundedLineFamily δ x m S).Nonempty := hS.image _

/-- The coordinate error from rounding is at most half the grid width. -/
theorem slope_close_of_roundedLine_close {δ r m : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (x l : Space 2) (hclose : dist (roundedIncidentLine δ x m) l ≤ r) :
    |m - l 0| ≤ 2 * r := by
  have herr := lineGridRound_error hδ m
  have hcoord : |lineGridRound δ m - l 0| ≤ r := by
    have h := (PiLp.dist_apply_le (roundedIncidentLine δ x m) l 0).trans hclose
    simpa only [roundedIncidentLine_fst, Real.dist_eq] using h
  have htri := abs_sub_le m (lineGridRound δ m) (l 0)
  linarith

/-- Raw ball counts for the rounded line family follow from the original
direction-label counts. -/
theorem roundedLineFamily_ball_count {ι : Type*} [DecidableEq ι]
    {δ K b : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ι → ℝ)
    (D S : Finset ι) (hSD : S ⊆ D)
    (hcount : ∀ a r : ℝ, δ ≤ r →
      ((D.filter (fun i => |m i - a| ≤ r)).card : ℝ) ≤ K * r ^ b)
    (l : Space 2) (r : ℝ) (hδr : δ ≤ r) :
    (((roundedLineFamily δ x m S).filter (fun z => dist z l ≤ r)).card : ℝ) ≤
      K * 2 ^ b * r ^ b := by
  classical
  let A := D.filter (fun i => |m i - l 0| ≤ 2 * r)
  have hsub : (roundedLineFamily δ x m S).filter (fun z => dist z l ≤ r) ⊆
      A.image (fun i => roundedIncidentLine δ x (m i)) := by
    intro z hz
    obtain ⟨hzS, hzdist⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hzS
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨hSD hi, ?_⟩, rfl⟩
    exact slope_close_of_roundedLine_close hδ hδr x l hzdist
  calc
    (((roundedLineFamily δ x m S).filter (fun z => dist z l ≤ r)).card : ℝ) ≤
        ((A.image (fun i => roundedIncidentLine δ x (m i))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_image_le
    _ ≤ K * (2 * r) ^ b := hcount _ _ (by linarith)
    _ = K * 2 ^ b * r ^ b := by
      rw [Real.mul_rpow (by norm_num) ((hδ.trans_le hδr).le)]
      ring

/-- A finite map can lose only the maximum multiplicity of its fibers. -/
theorem card_le_image_card_mul_fiber_bound {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (S : Finset ι) (F : ι → α) {L : ℝ}
    (hF : ∀ a ∈ S.image F, ((S.filter (fun i => F i = a)).card : ℝ) ≤ L) :
    (S.card : ℝ) ≤ ((S.image F).card : ℝ) * L := by
  rw [Finset.card_eq_sum_card_image F S, Nat.cast_sum]
  exact (Finset.sum_le_sum hF).trans_eq (by simp)

/-- Even repeated original direction labels give enough distinct rounded
lines: their multiplicity is controlled by one δ-ball count. -/
theorem roundedLineFamily_card_lower {ι : Type*} [DecidableEq ι]
    {δ K b : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ι → ℝ)
    (D S : Finset ι) (hSD : S ⊆ D)
    (hcount : ∀ a : ℝ,
      ((D.filter (fun i => |m i - a| ≤ δ)).card : ℝ) ≤ K * δ ^ b) :
    (S.card : ℝ) ≤ ((roundedLineFamily δ x m S).card : ℝ) * (K * δ ^ b) := by
  apply card_le_image_card_mul_fiber_bound
  intro l _
  have hsub : S.filter (fun i => roundedIncidentLine δ x (m i) = l) ⊆
      D.filter (fun i => |m i - l 0| ≤ δ) := by
    intro i hi
    obtain ⟨hiS, hiL⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hSD hiS, ?_⟩
    have herr := lineGridRound_error hδ (m i)
    have heq : lineGridRound δ (m i) = l 0 := congrArg (fun z : Space 2 => z 0) hiL
    rw [heq] at herr
    exact herr.trans (by linarith)
  exact (show ((S.filter (fun i => roundedIncidentLine δ x (m i) = l)).card : ℝ) ≤
      ((D.filter (fun i => |m i - l 0| ≤ δ)).card : ℝ) from
        Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount (l 0))

/-- The raw sampled-family bound yields exactly the normalized finite
ball bound required by the published theorem. -/
theorem roundedLineFamily_normalized_ball_bound {ι : Type*} [DecidableEq ι]
    {δ K b L : ℝ} (hδ : 0 < δ) (x : Space 2) (m : ι → ℝ)
    (D S : Finset ι) (hSD : S ⊆ D)
    (hcount : ∀ a r : ℝ, δ ≤ r →
      ((D.filter (fun i => |m i - a| ≤ r)).card : ℝ) ≤ K * r ^ b)
    (hL : K * 2 ^ b ≤ L * ((roundedLineFamily δ x m S).card : ℝ)) :
    NormalizedFiniteBallBound δ b L (roundedLineFamily δ x m S) := by
  intro l r hδr _
  calc
    (((roundedLineFamily δ x m S).filter (fun z => dist z l ≤ r)).card : ℝ) ≤
        K * 2 ^ b * r ^ b := roundedLineFamily_ball_count hδ x m D S hSD hcount l r hδr
    _ ≤ (L * ((roundedLineFamily δ x m S).card : ℝ)) * r ^ b :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (hδ.trans_le hδr).le _)
    _ = L * r ^ b * ((roundedLineFamily δ x m S).card : ℝ) := by ring

/-- If a point retains an `I` fraction of the sampled labels, the line
family has normalized loss at most `2 * 2^b * K^2 / I`. The sample-size
assumption is the one supplied by `n = ceil (δ^(-b))`. -/
theorem roundedLineFamily_normalized_of_large_sample {ι : Type*} [DecidableEq ι]
    {δ K I b : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hI : 0 < I)
    (x : Space 2) (m : ι → ℝ) (D S : Finset ι) (hD : D.Nonempty) (hSD : S ⊆ D)
    (hsize : (D.card : ℝ) * δ ^ b ≤ 2)
    (hretained : I * (D.card : ℝ) ≤ (S.card : ℝ))
    (hcount : ∀ a r : ℝ, δ ≤ r →
      ((D.filter (fun i => |m i - a| ≤ r)).card : ℝ) ≤
        (K * (D.card : ℝ)) * r ^ b) :
    NormalizedFiniteBallBound δ b (2 * 2 ^ b * K ^ 2 / I)
      (roundedLineFamily δ x m S) := by
  have hn : 0 < (D.card : ℝ) := by exact_mod_cast hD.card_pos
  have ha : 0 < δ ^ b := Real.rpow_pos_of_pos hδ _
  have hT : 0 ≤ ((roundedLineFamily δ x m S).card : ℝ) := Nat.cast_nonneg _
  have hlow := roundedLineFamily_card_lower hδ x m D S hSD (fun a => hcount a δ le_rfl)
  have hbase : I ≤ ((roundedLineFamily δ x m S).card : ℝ) * K * δ ^ b := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith [hretained.trans hlow]
  apply roundedLineFamily_normalized_ball_bound hδ x m D S hSD hcount
  have hprod : I * ((K * (D.card : ℝ)) * 2 ^ b) ≤
      (2 * 2 ^ b * K ^ 2) * ((roundedLineFamily δ x m S).card : ℝ) := by
    calc
      I * ((K * (D.card : ℝ)) * 2 ^ b) ≤
          (((roundedLineFamily δ x m S).card : ℝ) * K * δ ^ b) *
            ((K * (D.card : ℝ)) * 2 ^ b) :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = (K ^ 2 * 2 ^ b * ((roundedLineFamily δ x m S).card : ℝ)) *
          ((D.card : ℝ) * δ ^ b) := by ring
      _ ≤ (K ^ 2 * 2 ^ b * ((roundedLineFamily δ x m S).card : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = _ := by ring
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hI).2
  nlinarith

end Falconer

end OAI
