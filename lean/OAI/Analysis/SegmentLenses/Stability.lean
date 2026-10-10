import OAI.Analysis.SegmentLenses.Radial

namespace OAI

/-!
# Weighted stability and original-coordinate estimates
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


section GateContraction
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]



theorem gate_coordinate_square_sum {H : Finset V} (G : Finset V)
    (hG : ∀ g ∈ G, Gate H g) (z : FullDual V) :
    ∑ g : G, z (unitVector g.val) ^ 2 ≤ ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let K := ancestralHull G
  have hK := ancestralHull_ancestral G
  obtain ⟨μ, A, hA, hAK, hmean⟩ := exists_atomic_law hK (head K z) (head_head K z)
    hr (norm_head_le hK z)
  have hc : ∀ g : G, z (unitVector g.val) = μ.mean (fun ω => (A ω).value (unitVector g.val)) := by
    intro g
    rw [← μ.expect_apply, hmean, head_unitVector,
      ite_eq_left (subset_ancestralHull G g.property)]
  calc
    (∑ g : G, z (unitVector g.val) ^ 2) =
        ∑ g : G, μ.mean (fun ω => (A ω).value (unitVector g.val)) ^ 2 := by simp_rw [hc]
    _ ≤ ∑ g : G, μ.mean (fun ω => (A ω).value (unitVector g.val) ^ 2) :=
      Finset.sum_le_sum (fun g _ => μ.sq_mean_le _)
    _ = μ.mean (fun ω => ∑ g : G, (A ω).value (unitVector g.val) ^ 2) := (μ.mean_sum _).symm
    _ ≤ μ.mean (fun ω => (A ω).energy) := μ.mean_mono (fun ω => (A ω).gate_energy_le G hG)
    _ ≤ ‖z‖ ^ 2 := (μ.mean_mono hA).trans_eq (μ.mean_const _)

end GateContraction

section LawStability
variable {V Ω : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V] [Fintype Ω]


def lawDeficit (μ : FiniteLaw Ω) (A : Ω → Representation V) (p : Test V) : ℝ :=
  1 - (μ.expect (fun ω => (A ω).value)) (p : Primal V)

def lawError (μ : FiniteLaw Ω) (A : Ω → Representation V) (p : Test V) : ℝ :=
  μ.mean (fun ω => ((A ω).error p.coeff).energy)

def lawSlack (μ : FiniteLaw Ω) (A : Ω → Representation V) (p : Test V) : ℝ :=
  μ.mean (fun ω => 1 - (A ω).family.seminorm p.coeff ^ 2)

theorem unit_law_budget (μ : FiniteLaw Ω) (A : Ω → Representation V)
    (hA : ∀ ω, (A ω).energy ≤ 1) (p : Test V) (hp : ‖p‖ ≤ 1) :
    0 ≤ lawError μ A p ∧ 0 ≤ lawSlack μ A p ∧
    lawError μ A p + lawSlack μ A p ≤ 2 * lawDeficit μ A p := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  have he : 0 ≤ lawError μ A p := μ.mean_nonneg (fun ω => (A ω).error p.coeff |>.energy_nonneg)
  have hd : ∀ ω, 0 ≤ 1 - (A ω).family.seminorm p.coeff ^ 2 := by
    intro ω
    have hf := (le_segmentSeminorm (A ω).family p.coeff).trans hp
    have hn := apply_nonneg ((A ω).family.seminorm) p.coeff
    nlinarith
  refine ⟨he, μ.mean_nonneg hd, ?_⟩
  change μ.mean _ + μ.mean _ ≤ _
  rw [← μ.mean_add]
  calc
    μ.mean (fun ω => ((A ω).error p.coeff).energy + (1 - (A ω).family.seminorm p.coeff ^ 2)) ≤
        μ.mean (fun ω => 2 * (1 - (A ω).value (p : Primal V))) := by
      apply μ.mean_mono
      intro ω
      have heq := (A ω).error_slack_identity p.coeff 1
      rw [← Representation.apply_test] at heq
      norm_num only [one_pow] at heq
      linarith [hA ω]
    _ = 2 * lawDeficit μ A p := by
      rw [μ.mean_mul, μ.mean_sub, μ.mean_const, lawDeficit, μ.expect_apply]

theorem lawDeficit_nonneg (μ : FiniteLaw Ω) (A : Ω → Representation V)
    (hA : ∀ ω, (A ω).energy ≤ 1) (p : Test V) (hp : ‖p‖ ≤ 1) :
    0 ≤ lawDeficit μ A p := by
  obtain ⟨he, hd, hb⟩ := unit_law_budget μ A hA p hp
  linarith



theorem mean_error_norm_le (μ : FiniteLaw Ω) (A : Ω → Representation V)
    (hA : ∀ ω, (A ω).energy ≤ 1) (p : Test V) (hp : ‖p‖ ≤ 1) :
    μ.mean (fun ω => ‖(A ω).value - ((A ω).family.replacement p.coeff).value‖) ≤
      Real.sqrt (2 * lawDeficit μ A p) := by
  obtain ⟨he, hd, hb⟩ := unit_law_budget μ A hA p hp
  calc
    μ.mean (fun ω => ‖(A ω).value - ((A ω).family.replacement p.coeff).value‖) =
        μ.mean (fun ω => ‖((A ω).error p.coeff).value‖) := by simp only [Representation.error_value]
    _ ≤ μ.mean (fun ω => Real.sqrt ((A ω).error p.coeff).energy) := μ.mean_mono (fun ω => ((A ω).error p.coeff).norm_le)
    _ ≤ Real.sqrt (lawError μ A p) := μ.mean_sqrt_le _ (fun ω => ((A ω).error p.coeff).energy_nonneg)
    _ ≤ Real.sqrt (2 * lawDeficit μ A p) := Real.sqrt_le_sqrt (by linarith)

theorem signed_law_error_le {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (A : Ω → Representation V) (hA : ∀ ω, (A ω).energy ≤ 1)
    (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1) (p : Test V) (hp : ‖p‖ ≤ 1) :
    ‖tail H (μ.expect (fun ω => σ ω • ((A ω).error p.coeff).value))‖ ≤
      Real.sqrt (2 * lawDeficit μ A p) := by
  apply (norm_signed_tail_expect_le hH μ σ hσ _).trans
  simpa only [Representation.error_value] using mean_error_norm_le μ A hA p hp


theorem law_absolute_mass_bound {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (G : Finset V) (hG : ∀ g ∈ G, Gate H g)
    (μ : FiniteLaw Ω) (A : Ω → Representation V) (hA : ∀ ω, (A ω).energy ≤ 1)
    (p : Test V) (hp : ‖p‖ ≤ 1) (hpH : p.coeff.support ⊆ H) :
    (∑ g : G, μ.mean (fun ω => |(A ω).family.boundary p.coeff g.val|) ^ 2) ≤
      (‖tail H (μ.expect (fun ω => (A ω).value))‖ + Real.sqrt (2 * lawDeficit μ A p)) ^ 2 +
        4 * lawDeficit μ A p := by
  let x := μ.expect (fun ω => (A ω).value)
  let z := μ.expect (fun ω => ((A ω).family.replacement p.coeff).value)
  let e := μ.expect (fun ω => ((A ω).error p.coeff).value)
  have hxe : z = x - e := by
    dsimp [z, x, e]
    simp only [Representation.error_value, μ.expect_sub]
    abel
  have he : ‖tail H e‖ ≤ Real.sqrt (2 * lawDeficit μ A p) := by
    simpa only [one_smul] using signed_law_error_le hH μ A hA (fun _ => 1) (by simp) p hp
  have hz : ‖tail H z‖ ≤ ‖tail H x‖ + Real.sqrt (2 * lawDeficit μ A p) := by
    rw [hxe]
    change ‖tailLinear H (x - e)‖ ≤ _
    rw [map_sub]
    change ‖tail H x - tail H e‖ ≤ _
    exact (norm_sub_le (tail H x) (tail H e)).trans (add_le_add (le_refl ‖tail H x‖) he)
  have hgate : ∀ g : G, μ.mean (fun ω => (A ω).family.boundary p.coeff g.val) =
      tail H z (unitVector g.val) := by
    intro g
    rw [tail_unitVector, ite_eq_right (hG g.val g.property).1]
    dsimp [z]
    rw [μ.expect_apply]
    congr 1
    funext ω
    exact ((A ω).family.replacement_gate p.coeff g.val).symm
  have hv : (∑ g : G, μ.mean (fun ω => (A ω).family.boundary p.coeff g.val) ^ 2) ≤
      (‖tail H x‖ + Real.sqrt (2 * lawDeficit μ A p)) ^ 2 := by
    simp_rw [hgate]
    apply (gate_coordinate_square_sum G hG (tail H z)).trans
    exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hz
  have hc : ∀ ω ω', (∑ g : G,
      (|(A ω).family.boundary p.coeff g.val * (A ω').family.boundary p.coeff g.val| -
        (A ω).family.boundary p.coeff g.val * (A ω').family.boundary p.coeff g.val)) ≤
      (1 - (A ω).family.seminorm p.coeff ^ 2) + (1 - (A ω').family.seminorm p.coeff ^ 2) := by
    intro ω ω'
    have hb := opposite_crossing (A ω).family (A ω').family hH p.coeff hpH G hG
    change _ ≤ (‖p‖ ^ 2 - _) + (‖p‖ ^ 2 - _) at hb
    have hn := norm_nonneg p
    nlinarith
  have hm := μ.absolute_mass_bound (fun ω (g : G) => (A ω).family.boundary p.coeff g.val)
    (fun ω => 1 - (A ω).family.seminorm p.coeff ^ 2) hc
  obtain ⟨hE, hD, hb⟩ := unit_law_budget μ A hA p hp
  change _ ≤ _ + 2 * lawSlack μ A p at hm
  change _ ≤ (‖tail H x‖ + _) ^ 2 + _
  linarith


theorem represented_bounded_multiplier {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (μ : FiniteLaw Ω) (A : Ω → Representation V) (hA : ∀ ω, (A ω).energy ≤ 1)
    (hK : ∀ ω S, S ∈ (A ω).family.sets → S ⊆ K)
    (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (p : Test V) (hp : ‖p‖ ≤ 1) (hpH : p.coeff.support ⊆ H) :
    ‖tail H (μ.expect (fun ω => σ ω • (A ω).value))‖ ≤
      Real.sqrt ((‖tail H (μ.expect (fun ω => (A ω).value))‖ + Real.sqrt (2 * lawDeficit μ A p)) ^ 2 +
        4 * lawDeficit μ A p) + Real.sqrt (2 * lawDeficit μ A p) := by
  classical
  let B := (‖tail H (μ.expect (fun ω => (A ω).value))‖ + Real.sqrt (2 * lawDeficit μ A p)) ^ 2 +
        4 * lawDeficit μ A p
  have hrep := (norm_signed_replacement_le hH μ σ hσ A hK p.coeff hpH).trans
    (Real.sqrt_le_sqrt (law_absolute_mass_bound hH (K.filter (Gate H))
      (fun g hg => (Finset.mem_filter.mp hg).2) μ A hA p hp hpH))
  have he := signed_law_error_le hH μ A hA σ hσ p hp
  have hsplit : μ.expect (fun ω => σ ω • (A ω).value) =
      μ.expect (fun ω => σ ω • ((A ω).family.replacement p.coeff).value) +
      μ.expect (fun ω => σ ω • ((A ω).error p.coeff).value) := by
    rw [← μ.expect_add]
    congr 1
    funext ω
    rw [← smul_add, Representation.error_value]
    congr 1
    abel
  rw [hsplit]
  change ‖tailLinear H (_ + _)‖ ≤ _
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add hrep he)

end LawStability



theorem stable_radical_linear {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ) :
    Real.sqrt ((η + Real.sqrt (2 * δ)) ^ 2 + 4 * δ) + Real.sqrt (2 * δ) ≤
      η + (2 + 2 * Real.sqrt 2) * Real.sqrt δ := by
  have hs : Real.sqrt (2 * δ) = Real.sqrt 2 * Real.sqrt δ := Real.sqrt_mul (by norm_num) _
  have hδs := Real.sq_sqrt hδ
  have h2s := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hb : Real.sqrt ((η + Real.sqrt (2 * δ)) ^ 2 + 4 * δ) ≤
      η + Real.sqrt (2 * δ) + 2 * Real.sqrt δ := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [mul_nonneg (Real.sqrt_nonneg δ) (show 0 ≤ η + Real.sqrt (2 * δ) by positivity)]
  rw [hs] at hb ⊢
  linarith

namespace FiniteLaw
variable {I Ω : Type*} [Fintype I] [Fintype Ω]

def mixture (w : FiniteLaw I) (μ : I → FiniteLaw Ω) : FiniteLaw (I × Ω) where
  weight iω := w.weight iω.1 * (μ iω.1).weight iω.2
  nonneg iω := mul_nonneg (w.nonneg _) ((μ _).nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, fun i => (μ i).total, mul_one, w.total]

@[simp] theorem mixture_mean (w : FiniteLaw I) (μ : I → FiniteLaw Ω) (f : I × Ω → ℝ) :
    (w.mixture μ).mean f = w.mean (fun i => (μ i).mean (fun ω => f (i, ω))) := by
  simp only [mean, mixture, Fintype.sum_prod_type, mul_assoc, Finset.mul_sum]

@[simp] theorem mixture_expect (w : FiniteLaw I) (μ : I → FiniteLaw Ω)
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : I × Ω → E) :
    (w.mixture μ).expect f = w.expect (fun i => (μ i).expect (fun ω => f (i, ω))) := by
  simp only [expect, mixture, Fintype.sum_prod_type, mul_smul, Finset.smul_sum]

theorem weight_mul_mean_le (w : FiniteLaw I) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) (i : I) :
    w.weight i * f i ≤ w.mean f := Finset.single_le_sum (fun j _ => mul_nonneg (w.nonneg j) (hf j))
      (Finset.mem_univ i)

end FiniteLaw

section ConditionalLaws
variable {V I Ω : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]
  [Fintype I] [Fintype Ω]

theorem mixture_deficit (w : FiniteLaw I) (μ : I → FiniteLaw Ω)
    (A : I → Ω → Representation V) (p : Test V) :
    lawDeficit (w.mixture μ) (fun iω => A iω.1 iω.2) p =
      w.mean (fun i => lawDeficit (μ i) (A i) p) := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  simp only [lawDeficit, FiniteLaw.mixture_expect, FiniteLaw.expect_apply,
    FiniteLaw.mean_sub, FiniteLaw.mean_const]


theorem represented_weighted_tail {H K : Finset V} (hH : Ancestral (· ≤ ·) H)
    (w : FiniteLaw I) (hw : ∀ i, 0 < w.weight i) (μ : I → FiniteLaw Ω)
    (A : I → Ω → Representation V) (hA : ∀ i ω, (A i ω).energy ≤ 1)
    (hK : ∀ i ω S, S ∈ (A i ω).family.sets → S ⊆ K)
    (p : Test V) (hp : ‖p‖ ≤ 1) (hpH : p.coeff.support ⊆ H) (i : I) :
    ‖tail H ((μ i).expect (fun ω => (A i ω).value))‖ ≤
      (w.weight i)⁻¹ * Real.sqrt
        ((‖tail H (w.expect (fun j => (μ j).expect (fun ω => (A j ω).value)))‖ +
          Real.sqrt (2 * w.mean (fun j => lawDeficit (μ j) (A j) p))) ^ 2 +
          4 * w.mean (fun j => lawDeficit (μ j) (A j) p)) +
      Real.sqrt (2 * lawDeficit (μ i) (A i) p) := by
  classical
  have hi : 0 ≤ (w.weight i)⁻¹ := inv_nonneg.mpr (hw i).le
  let ν := w.mixture μ
  let B : I × Ω → Representation V := fun iω => A iω.1 iω.2
  let G := K.filter (Gate H)
  let m : I → G → ℝ := fun j g => (μ j).mean (fun ω => |(A j ω).family.boundary p.coeff g.val|)
  let M : G → ℝ := fun g => ν.mean (fun iω => |(B iω).family.boundary p.coeff g.val|)
  let d := w.mean (fun j => lawDeficit (μ j) (A j) p)
  let η := ‖tail H (w.expect (fun j => (μ j).expect (fun ω => (A j ω).value)))‖
  let C := Real.sqrt ((η + Real.sqrt (2 * d)) ^ 2 + 4 * d)
  have hd : 0 ≤ d := w.mean_nonneg (fun j => lawDeficit_nonneg (μ j) (A j) (hA j) p hp)
  have hM : (∑ g : G, M g ^ 2) ≤ C ^ 2 := by
    have h := law_absolute_mass_bound hH G (fun g hg => (Finset.mem_filter.mp hg).2)
      ν B (fun iω => hA iω.1 iω.2) p hp hpH
    change (∑ g : G, M g ^ 2) ≤ _ at h
    have hdef : lawDeficit ν B p = d := mixture_deficit w μ A p
    have hmean : ν.expect (fun iω => (B iω).value) =
        w.expect (fun j => (μ j).expect (fun ω => (A j ω).value)) := w.mixture_expect μ _
    rw [hdef, hmean] at h
    change _ ≤ (η + Real.sqrt (2 * d)) ^ 2 + 4 * d at h
    simpa only [C, Real.sq_sqrt (show 0 ≤ (η + Real.sqrt (2 * d)) ^ 2 + 4 * d by positivity)] using h
  have hm0 : ∀ j g, 0 ≤ m j g := fun j g => (μ j).mean_nonneg (fun ω => abs_nonneg _)
  have hM0 : ∀ g, 0 ≤ M g := fun g => ν.mean_nonneg (fun ω => abs_nonneg _)
  have hmM : ∀ g, m i g ≤ (w.weight i)⁻¹ * M g := by
    intro g
    have he : M g = w.mean (fun j => m j g) := w.mixture_mean μ _
    have h := w.weight_mul_mean_le (fun j => m j g) (fun j => hm0 j g) i
    rw [← he] at h
    exact (le_inv_mul_iff₀ (hw i)).mpr h
  have hm : Real.sqrt (∑ g : G, m i g ^ 2) ≤ (w.weight i)⁻¹ * C := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (inv_nonneg.mpr (hw i).le) (Real.sqrt_nonneg _), ?_⟩
    calc
      (∑ g : G, m i g ^ 2) ≤ ∑ g : G, ((w.weight i)⁻¹ * M g) ^ 2 := by
        apply Finset.sum_le_sum
        intro g hg
        exact (sq_le_sq₀ (hm0 i g) (mul_nonneg hi (hM0 g))).mpr (hmM g)
      _ = (w.weight i)⁻¹ ^ 2 * ∑ g : G, M g ^ 2 := by simp only [mul_pow, Finset.mul_sum]
      _ ≤ (w.weight i)⁻¹ ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_left hM (sq_nonneg _)
      _ = ((w.weight i)⁻¹ * C) ^ 2 := (mul_pow _ _ _).symm
  have hrep : ‖tail H ((μ i).expect (fun ω => ((A i ω).family.replacement p.coeff).value))‖ ≤
      (w.weight i)⁻¹ * C := by
    apply (show ‖tail H ((μ i).expect (fun ω => ((A i ω).family.replacement p.coeff).value))‖ ≤
      Real.sqrt (∑ g : G, m i g ^ 2) by
        simpa only [one_smul] using norm_signed_replacement_le hH (μ i) (fun _ => 1)
          (by simp) (A i) (hK i) p.coeff hpH).trans hm
  have he : ‖tail H ((μ i).expect (fun ω => ((A i ω).error p.coeff).value))‖ ≤
      Real.sqrt (2 * lawDeficit (μ i) (A i) p) := by
    simpa only [one_smul] using signed_law_error_le hH (μ i) (A i) (hA i) (fun _ => 1) (by simp) p hp
  have hsplit : (μ i).expect (fun ω => (A i ω).value) =
      (μ i).expect (fun ω => ((A i ω).family.replacement p.coeff).value) +
      (μ i).expect (fun ω => ((A i ω).error p.coeff).value) := by
    simp only [Representation.error_value, FiniteLaw.expect_sub]
    abel
  rw [hsplit]
  change ‖tailLinear H (_ + _)‖ ≤ _
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add hrep he)

end ConditionalLaws

section WeightedCompleted
variable {V I : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V] [Fintype I]

theorem head_tail_commute (H K : Finset V) (z : FullDual V) :
    head K (tail H z) = tail H (head K z) := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  apply dual_ext_coordinates
  intro v
  simp only [head_unitVector, tail_unitVector]
  split_ifs <;> rfl




theorem weighted_tail_bound {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (w : FiniteLaw I) (hw : ∀ i, 0 < w.weight i) (z : I → FullDual V)
    (hz : ∀ i, ‖z i‖ ≤ 1) (p : Test V) (hp : ‖p‖ ≤ 1)
    (hpH : p.coeff.support ⊆ H) (i : I) :
    ‖tail H (z i)‖ ≤ (w.weight i)⁻¹ * Real.sqrt
      ((‖tail H (w.expect z)‖ + Real.sqrt (2 * (1 - (w.expect z) (p : Primal V)))) ^ 2 +
        4 * (1 - (w.expect z) (p : Primal V))) + Real.sqrt (2 * (1 - z i (p : Primal V))) := by
  classical
  have hi : 0 ≤ (w.weight i)⁻¹ := inv_nonneg.mpr (hw i).le
  apply dual_norm_le _ (by positivity)
  intro u
  let K := ancestralHull (H ∪ u.coeff.support)
  have hK := ancestralHull_ancestral (H ∪ u.coeff.support)
  have hHK : H ⊆ K := Finset.subset_union_left.trans (subset_ancestralHull _)
  have huK : u.coeff.support ⊆ K := Finset.subset_union_right.trans (subset_ancestralHull _)
  have hzi : ∀ j, ∃ μ : FiniteLaw (Option (LocalFamily K)), ∃ A : Option (LocalFamily K) → Representation V,
      (∀ ω, (A ω).energy ≤ 1) ∧ (∀ ω S, S ∈ (A ω).family.sets → S ⊆ K) ∧
        μ.expect (fun ω => (A ω).value) = head K (z j) := by
    intro j
    simpa only [one_pow] using exists_atomic_law hK (head K (z j)) (head_head _ _)
      (by norm_num : (0 : ℝ) < 1) ((norm_head_le hK _).trans (hz j))
  choose μ A hA hAK hmean using hzi
  have hd : ∀ j, lawDeficit (μ j) (A j) p = 1 - z j (p : Primal V) := by
    intro j
    rw [lawDeficit, hmean, head_pairing_of_support K (z j) p (hpH.trans hHK)]
  have hdmean : w.mean (fun j => lawDeficit (μ j) (A j) p) =
      1 - (w.expect z) (p : Primal V) := by
    simp_rw [hd]
    rw [w.mean_sub, w.mean_const, w.expect_apply]
  have hmeanK : w.expect (fun j => (μ j).expect (fun ω => (A j ω).value)) = head K (w.expect z) := by
    simp_rw [hmean]
    exact w.expect_map (headLinear K) z
  have hη : ‖tail H (head K (w.expect z))‖ ≤ ‖tail H (w.expect z)‖ := by
    rw [← head_tail_commute]
    exact norm_head_le hK _
  have hc := represented_weighted_tail hH w hw μ A hA hAK p hp hpH i
  rw [hmean, hmeanK, hdmean, hd] at hc
  have hc' : ‖tail H (head K (z i))‖ ≤ (w.weight i)⁻¹ * Real.sqrt
      ((‖tail H (w.expect z)‖ + Real.sqrt (2 * (1 - (w.expect z) (p : Primal V)))) ^ 2 +
        4 * (1 - (w.expect z) (p : Primal V))) + Real.sqrt (2 * (1 - z i (p : Primal V))) := by
    apply hc.trans
    gcongr
  rw [← tail_head_pairing H K (z i) u huK]
  have hop := (tail H (head K (z i))).le_opNorm (u : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at hop
  exact hop.trans (mul_le_mul_of_nonneg_right hc' (norm_nonneg _))

theorem weighted_deficits {H : Finset V} (w : FiniteLaw I) (hw : ∀ i, 0 < w.weight i)
    (z : I → FullDual V) (hz : ∀ i, ‖z i‖ ≤ 1) (p : Test V) (hp : ‖p‖ ≤ 1) :
    (∀ i, 0 ≤ 1 - z i (p : Primal V)) ∧
      1 - (w.expect z) (p : Primal V) = w.mean (fun i => 1 - z i (p : Primal V)) ∧
      ∀ i, 1 - z i (p : Primal V) ≤ (1 - (w.expect z) (p : Primal V)) / w.weight i := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := locallyFiniteOrderBotV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  have _ := H
  have hδ : ∀ i, 0 ≤ 1 - z i (p : Primal V) := by
    intro i
    have hn := (z i).le_opNorm (p : Primal V)
    rw [UniformSpace.Completion.norm_coe] at hn
    have he : z i (p : Primal V) ≤ 1 := (le_abs_self _).trans (hn.trans
      ((mul_le_of_le_one_left (norm_nonneg p) (hz i)).trans hp))
    linarith
  have he : 1 - (w.expect z) (p : Primal V) = w.mean (fun i => 1 - z i (p : Primal V)) := by
    rw [w.mean_sub, w.mean_const, w.expect_apply]
  refine ⟨hδ, he, fun i => ?_⟩
  rw [he]
  apply (le_div_iff₀ (hw i)).mpr
  simpa only [mul_comm] using w.weight_mul_mean_le _ hδ i

end WeightedCompleted


end SegmentLenses

end

end OAI
