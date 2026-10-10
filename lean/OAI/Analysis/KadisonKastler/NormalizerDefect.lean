import OAI.Analysis.KadisonKastler.CommutatorRangeError
import OAI.Analysis.KadisonKastler.UnitaryExponentialBounds

namespace OAI

/-! # From a conjugation defect to an infinitesimal defect -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem commutator_exp_error (h : selfAdjoint (H →L[ℂ] H))
    (x y : H →L[ℂ] H) :
    ‖(h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H) - (-Complex.I) • (y - x)‖ ≤
      ‖unitaryConj (H := H) (selfAdjoint.expUnitary h) x - y‖ +
        ‖unitaryConj (H := H) (selfAdjoint.expUnitary h) x - x -
          Complex.I • ((h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H))‖ := by
  let c : H →L[ℂ] H := (h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H)
  let z : H →L[ℂ] H := (-Complex.I) • (y - x)
  have hIz : Complex.I • z = y - x := by
    dsimp [z]
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  have heq : Complex.I • (c - z) =
      (unitaryConj (H := H) (selfAdjoint.expUnitary h) x - y) -
      (unitaryConj (H := H) (selfAdjoint.expUnitary h) x - x - Complex.I • c) := by
    rw [smul_sub, hIz]
    abel
  change ‖c - z‖ ≤ _
  calc
    ‖c - z‖ = ‖Complex.I • (c - z)‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ _ := by rw [heq]; exact norm_sub_le _ _

private theorem infDist_commutator_le_of_exp_approx (M : VonNeumannAlgebra H)
    (h : selfAdjoint (H →L[ℂ] H)) (x : H →L[ℂ] H) (hx : x ∈ M) (hxn : ‖x‖ ≤ 1)
    {e : ℝ} (he : Metric.infDist (unitaryConj (H := H) (selfAdjoint.expUnitary h) x)
      (M : Set (H →L[ℂ] H)) ≤ e) :
    Metric.infDist ((h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H))
      (M : Set (H →L[ℂ] H)) ≤ e + 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hd : Metric.infDist (unitaryConj (H := H) (selfAdjoint.expUnitary h) x)
      (M : Set (H →L[ℂ] H)) < r - 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 :=
    he.trans_lt (by linarith)
  obtain ⟨y, hy, hnear⟩ := (Metric.infDist_lt_iff
    (show (M : Set (H →L[ℂ] H)).Nonempty from ⟨0, M.zero_mem⟩)).mp hd
  have hz : (-Complex.I) • (y - x) ∈ M := M.smul_mem (M.sub_mem hy hx) _
  have hdist := Metric.infDist_le_dist_of_mem
    (x := (h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H)) hz
  rw [dist_eq_norm] at hdist hnear
  have herror := commutator_exp_error h x y
  have hrem := norm_expUnitary_conjugation_remainder_le h x
  have hmul : 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖ ≤ 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 := by
    calc
      _ ≤ 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hxn (by positivity)
      _ = _ := mul_one _
  linarith

theorem commutatorRangeError_le_of_exp_approx (M : VonNeumannAlgebra H)
    (h : selfAdjoint (H →L[ℂ] H)) {e : ℝ}
    (he : ∀ x ∈ unitBall M,
      Metric.infDist (unitaryConj (H := H) (selfAdjoint.expUnitary h) x)
        (M : Set (H →L[ℂ] H)) ≤ e) :
    commutatorRangeError M (h : H →L[ℂ] H) ≤ e + 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 := by
  apply csSup_le
    (show ((fun x : Algebra M => Metric.infDist
      (commutatorAlong M.toStarSubalgebra.subtype (h : H →L[ℂ] H) x)
      (M : Set (H →L[ℂ] H))) '' {x | ‖x‖ ≤ 1}).Nonempty from ⟨_, 0, by simp, rfl⟩)
  rintro _ ⟨x, hx, rfl⟩
  change Metric.infDist ((h : H →L[ℂ] H) * x.val - x.val * (h : H →L[ℂ] H)) _ ≤ _
  exact infDist_commutator_le_of_exp_approx M h x.val x.property hx (he x.val ⟨x.property, hx⟩)

end

end KadisonKastler

end OAI
