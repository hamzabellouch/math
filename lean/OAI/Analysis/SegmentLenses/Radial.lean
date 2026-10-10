import OAI.Analysis.SegmentLenses.Coordinates

namespace OAI

/-!
# Radial midpoint estimates and endpoint asymmetry
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


namespace FiniteLaw
variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

def blend (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : FiniteLaw (Ω ⊕ Ω') where
  weight := Sum.elim (fun ω => a * μ.weight ω) (fun ω => b * ν.weight ω)
  nonneg ω := by cases ω <;> exact mul_nonneg (by assumption) (by apply FiniteLaw.nonneg)
  total := by simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    ← Finset.mul_sum, μ.total, ν.total, mul_one, hab]

theorem blend_expect (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : Ω → E) (g : Ω' → E) :
    (μ.blend ν a b ha hb hab).expect (Sum.elim f g) = a • μ.expect f + b • ν.expect g := by
  simp only [expect, blend, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.smul_sum, mul_smul]

end FiniteLaw


theorem norm_center_average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) : ‖x‖ ≤ (‖x + y‖ + ‖x - y‖) / 2 := by
  have he : (2 : ℝ) • x = (x + y) + (x - y) := by module
  have h := norm_add_le (x + y) (x - y)
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

theorem norm_displacement_average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) : ‖y‖ ≤ (‖x + y‖ + ‖x - y‖) / 2 := by
  simpa only [add_comm y x, norm_sub_rev y x] using norm_center_average y x

section UnequalRadii
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [TreeOrder V] [SegmentSystem V] [IntervalSegments V]




theorem finite_unequal_radius_tail {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (hK : Ancestral (· ≤ ·) K) (hHK : H ⊆ K)
    (x y : FullDual V) (hx : head H x = x) (hy : head K y = y)
    (Rp Rm : ℝ) (hRp : 0 < Rp) (hRm : 0 < Rm)
    (hp : ‖x + y‖ ≤ Rp) (hm : ‖x - y‖ ≤ Rm) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (((Rp + Rm) / 2) ^ 2 - ‖x‖ ^ 2) := by
  classical
  let L := (Rp + Rm) / 2
  have hL : 0 < L := by dsimp [L]; positivity
  by_cases hx0 : x = 0
  · have hn := (norm_displacement_average x y).trans (by dsimp [L]; linarith :
      (‖x + y‖ + ‖x - y‖) / 2 ≤ L)
    rw [hx0, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_sq hL.le]
    exact (norm_tail_le hH y).trans (hn.trans (by linarith))
  have hxK := head_eq_of_subset hHK x hx
  have hpK : head K (x + y) = x + y := by
    change headLinear K (x + y) = _
    simp only [map_add, headLinear_apply, hxK, hy]
  have hmK : head K (x - y) = x - y := by
    change headLinear K (x - y) = _
    simp only [map_sub, headLinear_apply, hxK, hy]
  obtain ⟨μp, Ap, hpE, hpSupp, hpMean⟩ := exists_atomic_law hK (x + y) hpK hRp hp
  obtain ⟨μm, Am, hmE, hmSupp, hmMean⟩ := exists_atomic_law hK (x - y) hmK hRm hm
  let a := Rp / (2 * L)
  let b := Rm / (2 * L)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a + b = 1 := by
    dsimp [a, b, L]
    field_simp
  let μ := μp.blend μm a b ha hb hab
  let A := Sum.elim (fun ω => (Ap ω).scale (L / Rp)) (fun ω => (Am ω).scale (L / Rm))
  let σ : Option (LocalFamily K) ⊕ Option (LocalFamily K) → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
  have hσ : ∀ ω, |σ ω| ≤ 1 := by intro ω; cases ω <;> norm_num [σ]
  have heRp : (L / Rp) ^ 2 * Rp ^ 2 = L ^ 2 := by field_simp
  have heRm : (L / Rm) ^ 2 * Rm ^ 2 = L ^ 2 := by field_simp
  have henergy : ∀ ω, (A ω).energy ≤ L ^ 2 := by
    intro ω
    cases ω with
    | inl ω => exact (by
        change ((Ap ω).scale (L / Rp)).energy ≤ _
        rw [Representation.scale_energy]
        exact (mul_le_mul_of_nonneg_left (hpE ω) (sq_nonneg _)).trans_eq heRp)
    | inr ω => exact (by
        change ((Am ω).scale (L / Rm)).energy ≤ _
        rw [Representation.scale_energy]
        exact (mul_le_mul_of_nonneg_left (hmE ω) (sq_nonneg _)).trans_eq heRm)
  have hsupp : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K := by
    intro ω
    cases ω with
    | inl ω => exact hpSupp ω
    | inr ω => exact hmSupp ω
  have hac : a * (L / Rp) = 1 / 2 := by dsimp [a]; field_simp
  have hbc : b * (L / Rm) = 1 / 2 := by dsimp [b]; field_simp
  have hmean : μ.expect (fun ω => (A ω).value) = x := by
    have hf : (fun ω => (A ω).value) = Sum.elim
        (fun ω => (L / Rp) • (Ap ω).value) (fun ω => (L / Rm) • (Am ω).value) := by
      funext ω; cases ω <;> exact Representation.scale_value _ _
    rw [hf, μp.blend_expect μm, μp.expect_smul, μm.expect_smul, hpMean, hmMean, smul_smul,
      smul_smul, hac, hbc]
    module
  have hsigned : μ.expect (fun ω => σ ω • (A ω).value) = y := by
    have hf : (fun ω => σ ω • (A ω).value) = Sum.elim
        (fun ω => (L / Rp) • (Ap ω).value) (fun ω => (-(L / Rm)) • (Am ω).value) := by
      funext ω
      cases ω with
      | inl ω => simp only [σ, A, Sum.elim_inl, Representation.scale_value, one_smul]
      | inr ω =>
          simp only [σ, A, Sum.elim_inr, Representation.scale_value, smul_smul]
          congr 1
          ring
    rw [hf, μp.blend_expect μm, μp.expect_smul, μm.expect_smul, hpMean, hmMean,
      smul_smul, smul_smul, mul_neg, hac, hbc]
    module
  obtain ⟨p, hpSupport, hpn, hpx⟩ := exists_norming_head hH x hx hx0
  let q : Test V := ‖x‖ • p
  have hqSupport : q.coeff.support ⊆ H := Finsupp.support_smul.trans hpSupport
  have hqn : ‖q‖ = ‖x‖ := by
    change ‖‖x‖ • p‖ = ‖x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hpn, mul_one]
  have hxq : x (q : Primal V) = ‖x‖ ^ 2 := by
    change x ((‖x‖ • p : Test V) : Primal V) = _
    rw [UniformSpace.Completion.coe_smul, map_smul, smul_eq_mul, hpx, sq]
  exact represented_joint_bound hH μ σ hσ A hsupp x y hx hmean hsigned q hqSupport
    ‖x‖ L hqn hxq henergy

variable [LocallyFiniteOrderBot V]

theorem completed_unequal_radius_tail {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hx : head H x = x)
    (Rp Rm : ℝ) (hRp : 0 < Rp) (hRm : 0 < Rm) (hp : ‖x + y‖ ≤ Rp) (hm : ‖x - y‖ ≤ Rm) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (((Rp + Rm) / 2) ^ 2 - ‖x‖ ^ 2) := by
  apply dual_norm_le _ (by positivity)
  intro u
  let K := ancestralHull (H ∪ u.coeff.support)
  have hK := ancestralHull_ancestral (H ∪ u.coeff.support)
  have hHK : H ⊆ K := Finset.subset_union_left.trans (subset_ancestralHull _)
  have huK : u.coeff.support ⊆ K := Finset.subset_union_right.trans (subset_ancestralHull _)
  have hxK := head_eq_of_subset hHK x hx
  have hpK : ‖x + head K y‖ ≤ Rp := by
    have he : x + head K y = head K (x + y) := by
      change x + headLinear K y = headLinear K (x + y)
      simp only [map_add, headLinear_apply, hxK]
    rw [he]
    exact (norm_head_le hK _).trans hp
  have hmK : ‖x - head K y‖ ≤ Rm := by
    have he : x - head K y = head K (x - y) := by
      change x - headLinear K y = headLinear K (x - y)
      simp only [map_sub, headLinear_apply, hxK]
    rw [he]
    exact (norm_head_le hK _).trans hm
  have hb := finite_unequal_radius_tail hH hK hHK x (head K y) hx (head_head _ _)
    Rp Rm hRp hRm hpK hmK
  rw [← tail_head_pairing H K y u huK]
  have hop := (tail H (head K y)).le_opNorm (u : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at hop
  exact hop.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg u))


theorem averaged_tail_bound {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hx : head H x = x) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (((‖x + y‖ + ‖x - y‖) / 2) ^ 2 - ‖x‖ ^ 2) := by
  by_cases hp0 : x + y = 0
  · have hy : y = -x := eq_neg_of_add_eq_zero_right hp0
    have ht : tail H y = 0 := by
      rw [hy]
      change tailLinear H (-x) = 0
      rw [map_neg, tailLinear_apply]
      simp only [tail, hx, sub_self, neg_zero]
    rw [ht, norm_zero]
    positivity
  by_cases hm0 : x - y = 0
  · have hy : y = x := (sub_eq_zero.mp hm0).symm
    have ht : tail H y = 0 := by simp only [hy, tail, hx, sub_self]
    rw [ht, norm_zero]
    positivity
  exact completed_unequal_radius_tail hH x y hx ‖x + y‖ ‖x - y‖
    (norm_pos_iff.mpr hp0) (norm_pos_iff.mpr hm0) le_rfl le_rfl

end UnequalRadii

section StrongConsequences
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem norm_center_le_average (x y : FullDual V) :
    ‖x‖ ≤ (‖x + y‖ + ‖x - y‖) / 2 := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  have h := norm_add_le (x + y) (x - y)
  have he : (x + y) + (x - y) = (2 : ℝ) • x := by module
  rw [he, norm_smul] at h
  norm_num at h
  linarith

theorem sharp_radial_comparison {R r : ℝ} (hr : 0 ≤ r) (hR : r ≤ R) :
    2 * Real.sqrt (R ^ 2 - r ^ 2) ≤
      (Real.sqrt 2 + Real.sqrt 6) * Real.sqrt (R * (R - r)) := by
  have hR0 : 0 ≤ R := hr.trans hR
  have hd : 0 ≤ R * (R - r) := mul_nonneg hR0 (sub_nonneg.mpr hR)
  have hs : R ^ 2 - r ^ 2 ≤ 2 * (R * (R - r)) := by nlinarith [sq_nonneg (R-r)]
  have h := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at h
  have hc : Real.sqrt 2 ≤ Real.sqrt 6 := Real.sqrt_le_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (R * (R-r))]


theorem radial_tail_bound {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hx : head H x = x) (R : ℝ) (hR : 0 ≤ R)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖tail H y‖ ≤ (Real.sqrt 2 + Real.sqrt 6) * Real.sqrt (R * (R - ‖x‖)) :=
  (completed_main_tail hH x y hx R hR hp hm).trans
    (sharp_radial_comparison (norm_nonneg x) (norm_center_le x y R hp hm))


theorem original_coefficient_average {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x z : FullDual V) (hx : head H x = x) (hz : head H z = 0) :
    ‖x‖ ≤ ‖x+z‖ ∧ ‖x‖ ≤ ‖x-z‖ ∧
    ‖z‖ ≤ (Real.sqrt 2 + Real.sqrt 6) *
      Real.sqrt (((‖x+z‖ + ‖x-z‖)/2) * ((‖x+z‖ + ‖x-z‖)/2 - ‖x‖)) := by
  have hp : head H (x+z) = x := by
    change headLinear H (x+z) = x
    simp only [map_add, headLinear_apply, hx, hz, add_zero]
  have hm : head H (x-z) = x := by
    change headLinear H (x-z) = x
    simp only [map_sub, headLinear_apply, hx, hz, sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hp] using norm_head_le hH (x+z)
  · simpa only [hm] using norm_head_le hH (x-z)
  · have h := averaged_tail_bound hH x z hx
    rw [tail, hz, sub_zero] at h
    exact h.trans (sharp_radial_comparison (norm_nonneg x) (norm_center_le_average x z))

theorem strong_finite_head_average {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x y : FullDual V) (hx : head H x = x) (hxn : ‖x‖ = 1)
    (hy : head H y = 0) (hyn : 1 ≤ ‖y‖) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (1 + t ^ 2 / 4) - 1 ≤
      (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 := by
  let L := (‖x+t•y‖+‖x-t•y‖)/2
  have hL : 1 ≤ L := by simpa only [hxn] using norm_center_le_average x (t•y)
  have hL0 : 0 ≤ L := by linarith
  have hty : tail H (t • y) = t • y := by
    change t • y - headLinear H (t • y) = t • y
    rw [map_smul, headLinear_apply, hy, smul_zero, sub_zero]
  have htail := averaged_tail_bound hH x (t•y) hx
  rw [hty, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hxn] at htail
  change t * ‖y‖ ≤ 2 * Real.sqrt (L^2-1^2) at htail
  have htn : t ≤ t * ‖y‖ := le_mul_of_one_le_right ht.le hyn
  have hd : 0 ≤ L^2-1^2 := by nlinarith
  have hs := Real.sq_sqrt hd
  have hroot : Real.sqrt (1+t^2/4) ≤ L := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hL0, ?_⟩
    nlinarith [Real.sqrt_nonneg (L^2-1^2)]
  exact sub_le_sub_right hroot 1

theorem strong_predual_averaged_witness (x : CoordinatePredual V) (hx : ‖x‖ = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ H : Finset V, Ancestral (· ≤ ·) H ∧
      ∀ y : CoordinatePredual V, head H y.val = 0 → 1 ≤ ‖y‖ →
        (Real.sqrt (1 + t ^ 2 / 4) - 1) - ε ≤
          (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 := by
  obtain ⟨H, hH, z, hz, hzn, he⟩ := predual_unit_approx x hx hε
  refine ⟨H, hH, ?_⟩
  intro y hy hyn
  have h := strong_finite_head_average hH z y.val hz hzn hy hyn ht
  have hp : ‖z + t • y.val‖ ≤ ‖x.val + t • y.val‖ + ‖x.val - z‖ := by
    have heq : z + t • y.val = (x.val + t • y.val) + (z - x.val) := by module
    rw [heq]
    exact (norm_add_le _ _).trans_eq (by rw [norm_sub_rev z x.val])
  have hm : ‖z - t • y.val‖ ≤ ‖x.val - t • y.val‖ + ‖x.val - z‖ := by
    have heq : z - t • y.val = (x.val - t • y.val) + (z - x.val) := by module
    rw [heq]
    exact (norm_add_le _ _).trans_eq (by rw [norm_sub_rev z x.val])
  change (Real.sqrt (1 + t ^ 2 / 4) - 1) - ε ≤
    (‖x.val + t • y.val‖ + ‖x.val - t • y.val‖) / 2 - 1
  linarith


end StrongConsequences

section StrongModulus
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V] {infiniteV : Infinite V}
include infiniteV

theorem strong_predual_all_radius_average [Infinite V] {t : ℝ} (ht : 0 < t) :
    (Real.sqrt (1 + t ^ 2 / 4) - 1) ≤ averagedModulus (CoordinatePredual V) t := by
  have _ := infiniteV
  apply averagedModulus_lower predual_not_finite ht.le
  intro x ε hε
  obtain ⟨H, hH, hw⟩ := strong_predual_averaged_witness x.val x.property ht hε
  refine ⟨CofiniteSubspace.ofMap (predualHeadValues H), ?_⟩
  intro y
  exact hw y.val (predualHeadValues_zero H y.val y.property.1) y.property.2.ge

theorem strong_fullDual_all_radius_average_of_reflexive [Infinite V] (hV : Reflexive (Primal V))
    {t : ℝ} (ht : 0 < t) :
    (Real.sqrt (1 + t ^ 2 / 4) - 1) ≤ averagedModulus (FullDual V) t := by
  have _ := infiniteV
  apply averagedModulus_lower fullDual_not_finite ht.le
  intro x ε hε
  have hx : x.val ∈ coordinateSpan V := by rw [coordinateSpan_eq_top_of_reflexive hV]; trivial
  obtain ⟨H, hH, hw⟩ := strong_predual_averaged_witness (⟨x.val, hx⟩ : CoordinatePredual V)
    x.property ht hε
  let f : FullDual V →L[ℝ] (H → ℝ) :=
    ContinuousLinearMap.pi (fun v => ContinuousLinearMap.apply ℝ ℝ (unitVector v.val))
  refine ⟨CofiniteSubspace.ofMap f, ?_⟩
  intro y
  have hy : y.val ∈ coordinateSpan V := by rw [coordinateSpan_eq_top_of_reflexive hV]; trivial
  apply hw (⟨y.val, hy⟩ : CoordinatePredual V) _ y.property.2.ge
  apply Finset.sum_eq_zero
  intro v hv
  have he := congrFun y.property.1 (⟨v, hv⟩ : H)
  change y.val (unitVector v) = 0 at he
  rw [he, zero_smul]

end StrongModulus



end SegmentLenses

end

end OAI
