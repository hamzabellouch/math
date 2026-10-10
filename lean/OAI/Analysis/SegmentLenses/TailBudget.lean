import OAI.Analysis.SegmentLenses.GateRecovery

namespace OAI

/-!
# Signed-product recovery and the finite midpoint tail bound
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section SignedRecovery
open scoped Classical
variable {V Ω : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V] [Fintype Ω]

theorem tail_expect_smul (H : Finset V) (μ : FiniteLaw Ω) (σ : Ω → ℝ) (f : Ω → FullDual V) :
    tail H (μ.expect (fun ω => σ ω • f ω)) = μ.expect (fun ω => σ ω • tail H (f ω)) := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  simpa only [map_smul, tailLinear_apply] using
    (μ.expect_map (tailLinear H) (fun ω => σ ω • f ω)).symm

theorem norm_signed_tail_expect_le {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1) (f : Ω → FullDual V) :
    ‖tail H (μ.expect (fun ω => σ ω • f ω))‖ ≤ μ.mean (fun ω => ‖f ω‖) := by
  rw [tail_expect_smul]
  apply (μ.norm_expect_le _).trans
  apply μ.mean_mono
  intro ω
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hσ ω)).trans (norm_tail_le hH (f ω))

theorem signed_replacement_recovery {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (A : Ω → Representation V)
    (hK : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K)
    (p : V →₀ ℝ) (hp : p.support ⊆ H) :
    tail H (μ.expect (fun ω => σ ω • ((A ω).family.replacement p).value)) =
      ∑ g : K.filter (Gate H), μ.expect (fun ω =>
        (σ ω * (A ω).family.boundary p g.val) • segmentFunctional ((A ω).family.gateTail H g.val)) := by
  rw [tail_expect_smul]
  calc
    μ.expect (fun ω => σ ω • tail H ((A ω).family.replacement p).value) =
        μ.expect (fun ω => ∑ g : K.filter (Gate H),
          (σ ω * (A ω).family.boundary p g.val) • segmentFunctional ((A ω).family.gateTail H g.val)) := by
      congr 1
      funext ω
      rw [(A ω).family.tail_replacement hH p hp (hK ω)]
      simp only [Finset.smul_sum, smul_smul]
    _ = _ := μ.expect_sum _

theorem norm_signed_replacement_le {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1) (A : Ω → Representation V)
    (hK : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K)
    (p : V →₀ ℝ) (hp : p.support ⊆ H) :
    ‖tail H (μ.expect (fun ω => σ ω • ((A ω).family.replacement p).value))‖ ≤
      Real.sqrt (∑ g : K.filter (Gate H), μ.mean (fun ω => |(A ω).family.boundary p g.val|) ^ 2) := by
  rw [signed_replacement_recovery hH μ σ A hK p hp]
  apply cone_reconstruction (K.filter (Gate H)) (fun g hg => (Finset.mem_filter.mp hg).2) μ σ hσ
  · intro g ω
    exact (A ω).family.gateTail_segment hH g.val
  · intro g ω v hv
    exact (A ω).family.gateTail_cone (Finset.mem_filter.mp g.property).2 hv

end SignedRecovery

section JointLawBound
open scoped Classical
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]



theorem represented_joint_bound {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (A : Ω → Representation V) (hK : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K)
    (x y : FullDual V) (hx : head H x = x)
    (hmean : μ.expect (fun ω => (A ω).value) = x)
    (hsigned : μ.expect (fun ω => σ ω • (A ω).value) = y)
    (q : Test V) (hq : q.coeff.support ⊆ H) (r R : ℝ)
    (hqr : ‖q‖ = r) (hxq : x (q : Primal V) = r ^ 2)
    (hR : ∀ ω, (A ω).energy ≤ R ^ 2) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - r ^ 2) := by
  classical
  let G := K.filter (Gate H)
  have hG : ∀ g ∈ G, Gate H g := fun g hg => (Finset.mem_filter.mp hg).2
  let err := fun ω => (A ω).error q.coeff
  let slack := fun ω => r ^ 2 - (A ω).family.seminorm q.coeff ^ 2
  let η := μ.mean (fun ω => (err ω).energy)
  let θ := μ.mean slack
  have hnormq : segmentSeminorm V q.coeff = r := hqr
  have herr : ∀ ω, 0 ≤ (err ω).energy := fun ω => (err ω).energy_nonneg
  have hslack : ∀ ω, 0 ≤ slack ω := by
    intro ω
    have hf := le_segmentSeminorm (A ω).family q.coeff
    rw [hnormq] at hf
    have hn := apply_nonneg ((A ω).family.seminorm) q.coeff
    dsimp [slack]
    nlinarith
  have hη : 0 ≤ η := μ.mean_nonneg herr
  have hθ : 0 ≤ θ := μ.mean_nonneg hslack
  have hpair : μ.mean (fun ω => ∑ S : (A ω).family.sets,
      (A ω).coeff S * (∑ v ∈ S.val, q.coeff v)) = r ^ 2 := by
    simp_rw [← Representation.apply_test]
    rw [← μ.expect_apply (fun ω => (A ω).value) (q : Primal V), hmean, hxq]
  have hidentity : η + θ = μ.mean (fun ω => (A ω).energy) - r ^ 2 := by
    change μ.mean (fun ω => (err ω).energy) + μ.mean slack = _
    rw [← μ.mean_add]
    have he : (fun ω => (err ω).energy + slack ω) = fun ω =>
        (A ω).energy - 2 * (∑ S : (A ω).family.sets, (A ω).coeff S * ∑ v ∈ S.val, q.coeff v) + r ^ 2 := by
      funext ω
      exact (A ω).error_slack_identity q.coeff r
    rw [he, μ.mean_add, μ.mean_sub, μ.mean_mul, μ.mean_const, hpair]
    ring
  have hbudget : η + θ ≤ R ^ 2 - r ^ 2 := by
    rw [hidentity]
    apply sub_le_sub_right
    exact (μ.mean_mono hR).trans_eq (μ.mean_const (R ^ 2))
  let b : Ω → G → ℝ := fun ω g => (A ω).family.boundary q.coeff g.val
  let W : Ω → G → ℝ := fun ω g => (err ω).value (unitVector g.val)
  have hzero : ∀ g, μ.mean (fun ω => b ω g + W ω g) = 0 := by
    intro g
    have he : (fun ω => b ω g + W ω g) = fun ω => (A ω).value (unitVector g.val) := by
      funext ω
      dsimp [b, W, err]
      rw [Representation.error_value, _root_.sub_apply, SegmentFamily.replacement_gate]
      ring
    rw [he, ← μ.expect_apply (fun ω => (A ω).value) (unitVector g.val), hmean]
    rw [← hx, head_unitVector, ite_eq_right (hG _ g.property).1]
  have hW : ∀ ω, (∑ g : G, W ω g ^ 2) ≤ (err ω).energy :=
    fun ω => (err ω).gate_energy_le G hG
  have hcross : ∀ ω ω', (∑ g : G, (|b ω g * b ω' g| - b ω g * b ω' g)) ≤
      slack ω + slack ω' := by
    intro ω ω'
    simpa only [b, slack, hnormq] using
      opposite_crossing (A ω).family (A ω').family hH q.coeff hq G hG
  have hmass : (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) ≤ η + 2 * θ :=
    μ.joint_mass_bound b W (fun ω => (err ω).energy) slack hzero hW hcross
  have he_bound : ‖tail H (μ.expect (fun ω => σ ω • (err ω).value))‖ ≤ Real.sqrt η := by
    calc
      ‖tail H (μ.expect (fun ω => σ ω • (err ω).value))‖ ≤
          μ.mean (fun ω => ‖(err ω).value‖) := norm_signed_tail_expect_le hH μ σ hσ _
      _ ≤ μ.mean (fun ω => Real.sqrt (err ω).energy) := μ.mean_mono (fun ω => (err ω).norm_le)
      _ ≤ Real.sqrt η := μ.mean_sqrt_le _ herr
  have hr_bound : ‖tail H (μ.expect (fun ω => σ ω • ((A ω).family.replacement q.coeff).value))‖ ≤
      Real.sqrt (η + 2 * θ) := by
    exact (norm_signed_replacement_le hH μ σ hσ A hK q.coeff hq).trans
      (Real.sqrt_le_sqrt hmass)
  have hy : y = μ.expect (fun ω => σ ω • (err ω).value) +
      μ.expect (fun ω => σ ω • ((A ω).family.replacement q.coeff).value) := by
    rw [← hsigned, ← μ.expect_add]
    congr 1
    funext ω
    rw [← smul_add]
    dsimp [err]
    rw [Representation.error_value, sub_add_cancel]
  have hytail : tail H y = tail H (μ.expect (fun ω => σ ω • (err ω).value)) +
      tail H (μ.expect (fun ω => σ ω • ((A ω).family.replacement q.coeff).value)) := by
    rw [hy]
    exact (tailLinear H).map_add _ _
  apply joint_budget_tail hη hθ hbudget
  rw [hytail]
  exact (norm_add_le _ _).trans (add_le_add he_bound hr_bound)

end JointLawBound

section HeadSupport
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

theorem dual_ext_coordinates {x y : FullDual V}
    (h : ∀ v, x (unitVector v) = y (unitVector v)) : x = y := by
  apply dual_ext_test
  intro u
  simp only [dual_apply_test, h]

theorem head_eq_iff (H : Finset V) (x : FullDual V) :
    head H x = x ↔ ∀ v ∉ H, x (unitVector v) = 0 := by
  constructor
  · intro hx v hv
    rw [← hx, head_unitVector, ite_eq_right hv]
  · intro hx
    apply dual_ext_coordinates
    intro v
    rw [head_unitVector]
    by_cases hv : v ∈ H
    · simp [hv]
    · simp [hv, hx v hv]

theorem head_eq_of_subset {H K : Finset V} (hHK : H ⊆ K)
    (x : FullDual V) (hx : head H x = x) : head K x = x := by
  apply (head_eq_iff K x).mpr
  intro v hv
  exact (head_eq_iff H x).mp hx v (fun hvH => hv (hHK hvH))

end HeadSupport


theorem norm_center_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (R : ℝ) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) : ‖x‖ ≤ R := by
  have he : x = (1 / 2 : ℝ) • ((x + y) + (x - y)) := by module
  calc
    ‖x‖ = ‖(1 / 2 : ℝ) • ((x + y) + (x - y))‖ := congrArg norm he
    _ = (1 / 2 : ℝ) * ‖(x + y) + (x - y)‖ := by rw [norm_smul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖x + y‖ + ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ R := by linarith

section FiniteMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]



theorem finite_main_tail {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (hK : Ancestral (· ≤ ·) K) (hHK : H ⊆ K)
    (x y : FullDual V) (hx : head H x = x) (hy : head K y = y)
    (R : ℝ) (hR : 0 ≤ R) (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) := by
  classical
  by_cases hx0 : x = 0
  · subst x
    simp only [zero_add] at hp
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_sq hR] using
      (norm_tail_le hH y).trans (hp.trans (by linarith : R ≤ 2 * R))
  have hc := norm_center_le x y R hp hm
  have hRp : 0 < R := (norm_pos_iff.mpr hx0).trans_le hc
  have hxK := head_eq_of_subset hHK x hx
  have hpK : head K (x + y) = x + y := by
    change headLinear K (x + y) = _
    rw [map_add, headLinear_apply, headLinear_apply, hxK, hy]
  have hmK : head K (x - y) = x - y := by
    change headLinear K (x - y) = _
    rw [map_sub, headLinear_apply, headLinear_apply, hxK, hy]
  obtain ⟨μp, Ap, hpE, hpSupp, hpMean⟩ := exists_atomic_law hK (x + y) hpK hRp hp
  obtain ⟨μm, Am, hmE, hmSupp, hmMean⟩ := exists_atomic_law hK (x - y) hmK hRp hm
  let μ := μp.pooled μm
  let A := Sum.elim Ap Am
  let σ : Option (LocalFamily K) ⊕ Option (LocalFamily K) → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
  have hσ : ∀ ω, |σ ω| ≤ 1 := by intro ω; cases ω <;> norm_num [σ]
  have henergy : ∀ ω, (A ω).energy ≤ R ^ 2 := by
    intro ω
    cases ω with
    | inl ω => exact hpE ω
    | inr ω => exact hmE ω
  have hsupp : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K := by
    intro ω
    cases ω with
    | inl ω => exact hpSupp ω
    | inr ω => exact hmSupp ω
  have hmean : μ.expect (fun ω => (A ω).value) = x := by
    have he : (fun ω => (A ω).value) = Sum.elim (fun ω => (Ap ω).value) (fun ω => (Am ω).value) := by
      funext ω; cases ω <;> rfl
    rw [he]
    change (μp.pooled μm).expect (Sum.elim (fun ω => (Ap ω).value) (fun ω => (Am ω).value)) = x
    rw [FiniteLaw.pooled_expect, hpMean, hmMean]
    module
  have hsigned : μ.expect (fun ω => σ ω • (A ω).value) = y := by
    have he : (fun ω => σ ω • (A ω).value) =
        Sum.elim (fun ω => (1 : ℝ) • (Ap ω).value) (fun ω => (-1 : ℝ) • (Am ω).value) := by
      funext ω; cases ω <;> rfl
    rw [he]
    change (μp.pooled μm).expect _ = y
    rw [FiniteLaw.pooled_expect, μp.expect_smul, μm.expect_smul, hpMean, hmMean]
    module
  obtain ⟨p, hpSupport, hpn, hpx⟩ := exists_norming_head hH x hx hx0
  let q : Test V := ‖x‖ • p
  have hqSupport : q.coeff.support ⊆ H :=
    Finsupp.support_smul.trans hpSupport
  have hqn : ‖q‖ = ‖x‖ := by
    change ‖‖x‖ • p‖ = ‖x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hpn, mul_one]
  have hxq : x (q : Primal V) = ‖x‖ ^ 2 := by
    change x ((‖x‖ • p : Test V) : Primal V) = _
    rw [UniformSpace.Completion.coe_smul, map_smul, smul_eq_mul, hpx, sq]
  exact represented_joint_bound hH μ σ hσ A hsupp x y hx hmean hsigned q hqSupport
    ‖x‖ R hqn hxq henergy

end FiniteMain


end SegmentLenses

end

end OAI
