import Mathlib
import OAI.Probability.SKFluctuations.ScalarFlattenedContinuity

namespace OAI

/-! Scalar Slope Invariant. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open Set Scalar
open scoped NNReal

noncomputable def scalarSlopeJ (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (b : ℝ) : ℝ :=
  -α.mass l-scalarSlopeCurvature₂ α l t b/2

noncomputable def scalarSlopeJ₁ (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (b : ℝ) : ℝ :=
  invariantQ (scalarSlopeCurvature α l t b)
    (scalarProfileJet α l t 3 (scalarSlopeInverse α l t b))
    (scalarProfileJet α l t 4 (scalarSlopeInverse α l t b))
    (scalarProfileJet α l t 5 (scalarSlopeInverse α l t b))/(scalarSlopeCurvature α l t b)^5

noncomputable def scalarSlopeZ (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (b : ℝ) : ℝ :=
  -scalarSlopeCurvature₁ α l t b/2

theorem scalarSlopeJ_eq_quotient (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (b : ℝ) :
    scalarSlopeJ α l t b = invariantP (α.mass l) (scalarSlopeCurvature α l t b)
      (scalarProfileJet α l t 3 (scalarSlopeInverse α l t b))
      (scalarProfileJet α l t 4 (scalarSlopeInverse α l t b))/(scalarSlopeCurvature α l t b)^3 := by
  have hp := (scalarSlopeCurvature_pos α hα l t b).ne'
  dsimp only [scalarSlopeJ,scalarSlopeCurvature₂,invariantP]
  field_simp; ring

theorem scalarSlopeJ_hasDerivAt (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    HasDerivAt (scalarSlopeJ α l t) (scalarSlopeJ₁ α l t b) b := by
  have hj (k : ℕ) := (scalarProfileJet_hasDerivAt α hα l t k (scalarSlopeInverse α l t b)).comp b
    (scalarSlopeInverse_hasDerivAt α hα l t hb)
  have hd := (hasDerivAt_invariantP (α.mass l) (hj 2) (hj 3) (hj 4)).div ((hj 2).pow 3)
    (pow_ne_zero 3 (scalarSlopeCurvature_pos α hα l t b).ne')
  have he : (fun y => invariantP (α.mass l) (scalarProfileJet α l t 2 (scalarSlopeInverse α l t y))
      (scalarProfileJet α l t 3 (scalarSlopeInverse α l t y))
      (scalarProfileJet α l t 4 (scalarSlopeInverse α l t y))/
      (scalarProfileJet α l t 2 (scalarSlopeInverse α l t y))^3) = scalarSlopeJ α l t :=
    funext (fun y => (scalarSlopeJ_eq_quotient α hα l t y).symm)
  change HasDerivAt (fun y => invariantP (α.mass l) (scalarProfileJet α l t 2 (scalarSlopeInverse α l t y))
      (scalarProfileJet α l t 3 (scalarSlopeInverse α l t y))
      (scalarProfileJet α l t 4 (scalarSlopeInverse α l t y))/
      (scalarProfileJet α l t 2 (scalarSlopeInverse α l t y))^3) _ b at hd
  rw [he] at hd
  apply hd.congr_deriv
  dsimp only [scalarSlopeJ₁,invariantPD,invariantP,invariantQ,scalarSlopeCurvature,Function.comp_apply,Pi.pow_apply]
  have hp := (scalarSlopeCurvature_pos α hα l t b).ne'
  change scalarProfileJet α l t 2 (scalarSlopeInverse α l t b) ≠ 0 at hp
  norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.cast_ofNat]
  field_simp; ring

theorem scalarSlopeZ_hasDerivAt (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) :
    HasDerivAt (scalarSlopeZ α l t) (α.mass l+scalarSlopeJ α l t b) b := by
  have hd := (scalarSlopeCurvature₁_hasDerivAt α hα l t hb).neg.div_const 2
  convert hd using 1 <;> first | rfl | (dsimp only [scalarSlopeJ]; ring)

theorem scalarSlopeInverse_nonneg (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) (hb0 : 0 ≤ b) :
    0 ≤ scalarSlopeInverse α l t b := by
  apply (scalarProfileJet_gradient_strictMono α hα l t).le_iff_le.mp
  rw [scalarSlopeInverse_right α hα l t hb,scalarProfileJet_gradient_zero α hα l t]
  exact hb0

theorem scalarSlopeJ_nonneg (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) (b : ℝ) : 0 ≤ scalarSlopeJ α l t b := by
  rw [scalarSlopeJ_eq_quotient α hα l t]
  exact div_nonneg ((scalarProfileJet_polynomialSigns α hα l t).P _) (pow_nonneg (scalarSlopeCurvature_pos α hα l t b).le _)

theorem scalarSlopeJ₁_nonneg (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) (hb0 : 0 ≤ b) :
    0 ≤ scalarSlopeJ₁ α l t b := by
  exact div_nonneg ((scalarProfileJet_polynomialSigns α hα l t).Q _
    (scalarSlopeInverse_nonneg α hα l t hb hb0)) (pow_nonneg (scalarSlopeCurvature_pos α hα l t b).le _)

theorem scalarSlopeJ₁_upper (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo (-1) 1) (hb0 : 0 ≤ b) :
    scalarSlopeCurvature α l t b*scalarSlopeJ₁ α l t b ≤
      3*scalarSlopeZ α l t b*scalarSlopeJ α l t b := by
  have hR := (scalarProfileJet_polynomialSigns α hα l t).R _
    (scalarSlopeInverse_nonneg α hα l t hb hb0)
  have hp := scalarSlopeCurvature_pos α hα l t b
  have he : scalarSlopeCurvature α l t b*scalarSlopeJ₁ α l t b-
      3*scalarSlopeZ α l t b*scalarSlopeJ α l t b =
      invariantR (α.mass l) (scalarSlopeCurvature α l t b)
      (scalarProfileJet α l t 3 (scalarSlopeInverse α l t b))
      (scalarProfileJet α l t 4 (scalarSlopeInverse α l t b))
      (scalarProfileJet α l t 5 (scalarSlopeInverse α l t b))/(scalarSlopeCurvature α l t b)^4 := by
    rw [scalarSlopeJ_eq_quotient α hα l t]
    dsimp only [scalarSlopeJ₁,scalarSlopeZ,scalarSlopeCurvature₁,invariantR]
    field_simp; ring
  apply sub_nonpos.mp
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg hR (pow_nonneg hp.le _)

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open Set Scalar
open scoped NNReal

noncomputable def scalarSlopeK (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (b : ℝ) : ℝ :=
  if b = 0 then scalarSlopeJ α l t 0 else scalarSlopeZ α l t b / b - α.mass l

theorem scalarSlopeZ_zero (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) : scalarSlopeZ α l t 0 = 0 := by
  simp only [scalarSlopeZ,scalarSlopeCurvature₁_zero α hα l t,neg_zero,zero_div]

theorem scalarSlopeJ_monotoneOn (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) : MonotoneOn (scalarSlopeJ α l t) (Ico 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
  · intro b hb
    exact (scalarSlopeJ_hasDerivAt α hα l t ⟨by linarith [hb.1],hb.2⟩).continuousAt.continuousWithinAt
  · intro b hb
    rw [interior_Ico] at hb
    exact (scalarSlopeJ_hasDerivAt α hα l t ⟨by linarith [hb.1],hb.2⟩).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [interior_Ico] at hb
    rw [(scalarSlopeJ_hasDerivAt α hα l t ⟨by linarith [hb.1],hb.2⟩).deriv]
    exact scalarSlopeJ₁_nonneg α hα l t ⟨by linarith [hb.1],hb.2⟩ hb.1.le

theorem scalarSlopeK_eq_intermediate_J (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    ∃ c ∈ Ioo 0 b, scalarSlopeK α l t b = scalarSlopeJ α l t c := by
  have hc : ContinuousOn (scalarSlopeZ α l t) (Icc 0 b) := by
    intro c hc
    exact (scalarSlopeZ_hasDerivAt α hα l t ⟨by linarith [hc.1],by linarith [hc.2,hb.2]⟩).continuousAt.continuousWithinAt
  have hd : ∀ c ∈ Ioo 0 b, HasDerivAt (scalarSlopeZ α l t) (α.mass l+scalarSlopeJ α l t c) c := by
    intro c hc
    exact scalarSlopeZ_hasDerivAt α hα l t ⟨by linarith [hc.1],by linarith [hc.2,hb.2]⟩
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope (scalarSlopeZ α l t)
    (fun c => α.mass l+scalarSlopeJ α l t c) hb.1 hc hd
  refine ⟨c,hc,?_⟩
  rw [scalarSlopeZ_zero α hα l t,sub_zero,sub_zero] at he
  rw [scalarSlopeK,ite_eq_right hb.1.ne']
  linarith

theorem scalarSlopeK_bounds (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ico 0 1) :
    0 ≤ scalarSlopeK α l t b ∧ scalarSlopeK α l t b ≤ scalarSlopeJ α l t b := by
  by_cases hb0 : b = 0
  · simp only [hb0,scalarSlopeK]
    exact ⟨scalarSlopeJ_nonneg α hα l t 0,le_rfl⟩
  · obtain ⟨c,hc,he⟩ := scalarSlopeK_eq_intermediate_J α hα l t ⟨lt_of_le_of_ne hb.1 (Ne.symm hb0),hb.2⟩
    rw [he]
    exact ⟨scalarSlopeJ_nonneg α hα l t c,
      scalarSlopeJ_monotoneOn α hα l t ⟨hc.1.le,lt_trans hc.2 hb.2⟩ hb hc.2.le⟩

theorem scalarSlopeK_hasDerivAt (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    HasDerivAt (scalarSlopeK α l t)
      ((scalarSlopeJ α l t b-scalarSlopeK α l t b)/b) b := by
  have hd := ((scalarSlopeZ_hasDerivAt α hα l t ⟨by linarith [hb.1],hb.2⟩).div
    (hasDerivAt_id b) hb.1.ne').sub_const (α.mass l)
  have hn : ∀ᶠ c in nhds b, c ≠ 0 := isOpen_ne.mem_nhds hb.1.ne'
  have he : scalarSlopeK α l t =ᶠ[nhds b] (fun c => scalarSlopeZ α l t c/c-α.mass l) := by
    filter_upwards [hn] with c hc using by simp only [scalarSlopeK,ite_eq_right hc]
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  rw [scalarSlopeK,ite_eq_right hb.1.ne']
  dsimp only [id_eq]
  field_simp [hb.1.ne']; ring

theorem scalarSlopeK_deriv_nonneg (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    0 ≤ deriv (scalarSlopeK α l t) b := by
  rw [(scalarSlopeK_hasDerivAt α hα l t hb).deriv]
  exact div_nonneg (sub_nonneg.mpr (scalarSlopeK_bounds α hα l t ⟨hb.1.le,hb.2⟩).2) hb.1.le

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem shiftedGrid_integral {q : ℝ → E} (a η : ℝ) (N : ℕ)
    (hq : ∀ j < N, IntervalIntegrable q volume (a+(j:ℝ)*η) (a+((j+1:ℕ):ℝ)*η)) :
    (∫ r in a..a+(N:ℝ)*η, q r) =
      ∫ ξ in (0:ℝ)..η, ∑ j ∈ Finset.range N, q (a+ξ+(j:ℝ)*η) := by
  have hi j (hj : j ∈ Finset.range N) :
      IntervalIntegrable (fun ξ => q (a+ξ+(j:ℝ)*η)) volume 0 η := by
    have h := (hq j (Finset.mem_range.mp hj)).comp_add_right (a+(j:ℝ)*η)
    convert h using 1
    · ext ξ
      congr 1
      ring
    · ring
    · push_cast
      ring
  rw [intervalIntegral.integral_finsetSum hi]
  calc
    _ = ∑ j ∈ Finset.range N, ∫ r in a+(j:ℝ)*η..a+((j+1:ℕ):ℝ)*η, q r := by
      simpa only [Nat.cast_zero,zero_mul,add_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals hq).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have h := intervalIntegral.integral_comp_add_right (a := 0) (b := η) q (a+(j:ℝ)*η)
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,zero_add,add_zero,
        add_comm,add_left_comm,add_assoc] using h.symm

 

 theorem shiftedGrid_integral_truncated {q : ℝ → E} (a b η : ℝ) (N : ℕ)
    (hab : a ≤ b) (hb : b ≤ a+(N:ℝ)*η)
    (hq : ∀ j < N, IntervalIntegrable q volume (a+(j:ℝ)*η) (a+((j+1:ℕ):ℝ)*η)) :
    (∫ r in a..b, q r) = ∫ ξ in (0:ℝ)..η,
      ∑ j ∈ Finset.range N, if a+ξ+(j:ℝ)*η ≤ b then q (a+ξ+(j:ℝ)*η) else 0 := by
  have hi j (hj : j < N) : IntervalIntegrable ((Iic b).indicator q) volume
      (a+(j:ℝ)*η) (a+((j+1:ℕ):ℝ)*η) :=
    ⟨(hq j hj).1.indicator measurableSet_Iic, (hq j hj).2.indicator measurableSet_Iic⟩
  have h := shiftedGrid_integral a η N hi
  have he : (Iic b : Set ℝ) = {x : ℝ | x ≤ b} := by ext x; rfl
  rw [he] at h
  rw [intervalIntegral.integral_indicator (f := q) (μ := volume) ⟨hab,hb⟩] at h
  simpa only [Set.indicator_apply,Set.mem_ofPred_eq] using h

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology ContDiff

noncomputable def slopeJet (u : ℝ × ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  spatialJet u k (inverseSlopeMap (spatialJet u 1) p)

theorem spatialJet_one_injective {u : ℝ × ℝ → ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hp : ∀ t x, 0 < t → 0 < spatialJet u 2 (t,x))
    (t : ℝ) (ht : 0 < t) : Function.Injective (fun x => spatialJet u 1 (t,x)) := by
  apply StrictMono.injective
  apply strictMono_of_deriv_pos
  intro x
  rw [(spatialJet_hasDerivAt (isOpen_lt continuous_const continuous_fst) hu 1 (x := x) ht).deriv]
  exact hp t x ht

theorem slopeJet_at_image {u : ℝ × ℝ → ℝ}
    {t : ℝ} (hi : Function.Injective (fun x => spatialJet u 1 (t,x))) (k : ℕ) (x : ℝ) :
    slopeJet u k (t,spatialJet u 1 (t,x)) = spatialJet u k (t,x) := by
  change spatialJet u k (t,inverseSlope (spatialJet u 1) (t,spatialJet u 1 (t,x))) = _
  rw [inverseSlope_left hi x]

theorem slopeJet_contDiffAt {u : ℝ × ℝ → ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hp : ∀ t x, 0 < t → 0 < spatialJet u 2 (t,x))
    {t x : ℝ} (ht : 0 < t) (r k : ℕ) :
    ContDiffAt ℝ k (slopeJet u r) (t,spatialJet u 1 (t,x)) := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hi := spatialJet_one_injective hu hp
  have hInv := inverseSlopeMap_contDiffAt (spatialJet_contDiffOn hS hu 1) hi ht (hp t x ht).ne' k
  have hJ : ContDiffAt ℝ k (spatialJet u r) (t,x) :=
    (spatialJet_contDiffOn hS hu r k (t,x) ht).contDiffAt (hS.mem_nhds ht)
  have he : inverseSlopeMap (spatialJet u 1) (t,spatialJet u 1 (t,x)) = (t,x) :=
    Prod.ext rfl (inverseSlope_left (hi t ht) x)
  rw [← he] at hJ
  exact hJ.comp _ hInv

theorem slopeJet_space_hasDerivAt {u : ℝ × ℝ → ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hp : ∀ t x, 0 < t → 0 < spatialJet u 2 (t,x))
    {t x : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt (fun b => slopeJet u k (t,b))
      (spatialJet u (k+1) (t,x)/spatialJet u 2 (t,x)) (spatialJet u 1 (t,x)) := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hi := spatialJet_one_injective hu hp
  have hInv := inverseSlope_space_hasDerivAt (spatialJet_contDiffOn hS hu 1 1)
    hi ht (hp t x ht).ne'
  have hd := spatialJet_hasDerivAt hS hu k (x := x) ht
  have hh := hd.comp_of_eq (spatialJet u 1 (t,x)) hInv (inverseSlope_left (hi t ht) x).symm
  exact hh

theorem slopeJet_time_hasDerivAt {u : ℝ × ℝ → ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hp : ∀ t x, 0 < t → 0 < spatialJet u 2 (t,x))
    {t x : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt (fun s => slopeJet u k (s,spatialJet u 1 (t,x)))
      (timePartial (spatialJet u k) (t,x)-spatialJet u (k+1) (t,x)*
        timePartial (spatialJet u 1) (t,x)/spatialJet u 2 (t,x)) t := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hi := spatialJet_one_injective hu hp
  have hInv := inverseSlope_time_hasDerivAt (spatialJet_contDiffOn hS hu 1 1)
    hi ht (hp t x ht).ne'
  have hcurve := (hasDerivAt_id t).prodMk hInv
  have hd : DifferentiableAt ℝ (spatialJet u k) (t,x) :=
    ((spatialJet_contDiffOn hS hu k 1 (t,x) ht).contDiffAt (hS.mem_nhds ht)).differentiableAt one_ne_zero
  have he : (t,x) = (t,inverseSlope (spatialJet u 1) (t,spatialJet u 1 (t,x))) :=
    Prod.ext rfl (inverseSlope_left (hi t ht) x).symm
  have hh := hd.hasFDerivAt.comp_hasDerivAt_of_eq t hcurve he
  rw [fderiv_apply_eq_partials] at hh
  convert hh using 1 <;> first | rfl | (simp only [spatialJet, mul_one]; ring)

 
noncomputable def slopeCurvatureSecond (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (slopeJet u 4 p*slopeJet u 2 p-(slopeJet u 3 p)^2)/(slopeJet u 2 p)^3

 

theorem slopeCurvature_timePDE {u : ℝ × ℝ → ℝ} {m : ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hp : ∀ t x, 0 < t → 0 < spatialJet u 2 (t,x))
    (hPDE : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x))
      ((1/2:ℝ)*(spatialJet u 2 (t,x)+m*(spatialJet u 1 (t,x))^2)) t)
    {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => slopeJet u 2 (s,spatialJet u 1 (t,x)))
      ((1/2:ℝ)*(slopeJet u 2 (t,spatialJet u 1 (t,x)))^2*
        (slopeCurvatureSecond u (t,spatialJet u 1 (t,x))+2*m)) t := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have htime (k) := hasDerivAt_timePartial
    (((spatialJet_contDiffOn hS hu k 1 (t,x) ht).contDiffAt (hS.mem_nhds ht)).differentiableAt one_ne_zero)
  have h1 := (htime 1).unique (spatialJet_one_timePDE hu hPDE (x := x) ht)
  have h2 := (htime 2).unique (spatialJet_two_timePDE hu hPDE (x := x) ht)
  have hh := slopeJet_time_hasDerivAt hu hp (x := x) ht 2
  rw [h1,h2] at hh
  convert hh using 1
  dsimp only [slopeCurvatureSecond]
  simp only [slopeJet_at_image (spatialJet_one_injective hu hp t ht)]
  field_simp [(hp t x ht).ne']
  ring

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

section
variable (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0)
    {m : ℝ} (hm : 0 < m) (hmα : m ≤ α.mass l) (r : ℝ≥0)

include hm hmα

theorem scalarClockProfileSlice_residual_uniform_root {R : GaussianResidual}
    (hR : R.residual.Cone) (hgrad : ∀ x, |R.residual.jet 1 x| ≤ 1)
    (hn : (∫ x, R.plantedDensity (scalarClockProfileJet α hα l t m r 0) m x)=1)
    {a : ℝ} (ha : 0 ≤ a) (hz : (scalarClockProfileSlice α hα l t hm hmα r).Φ a=0)
    (hcenter : ∫ x in Ioi 0,
      R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
      (scalarClockProfileSlice α hα l t hm hmα r).Φ x = 0) :
    (1/R.variance)^2*rootCovarianceFloor (scalarClockProfileSlice α hα l t hm hmα r)
      R.variance a ≤ ∫ x in Ioi 0,
      R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
      (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x := by
  let S := scalarClockProfileSlice α hα l t hm hmα r
  let U := scalarClockProfileJet α hα l t m r 0
  let w := R.rootWeight S U
  have hU : LipschitzWith 1 U :=
    scalar_restrict_lipschitz ((scalarProfileHeatJet α hα l t).evolve hm r).lipschitz
  have hlo (x : ℝ) : gaussianDensityFloor R.variance x*(S.C x)^2 ≤ w x := by
    have hh := R.plantedDensity_envelope hgrad hU
      (by rw [abs_of_pos hm]; exact hmα.trans (hα l)) hn x
    dsimp only [w]
    rw [R.rootWeight_eq]
    exact mul_le_mul_of_nonneg_right hh.1 (sq_nonneg _)
  obtain ⟨_,hC,hzpoly,_,_⟩ := scalarClockProfileSlice_polyBounded α hα l t hm hmα r
  have hΦ : PolyBounded S.Φ := ((hzpoly.pow 2).const_mul 2).sub (hC.const_mul m)
  have hGauss : GaussianDominated w := GaussianResidual.rootWeight_dominated hR S hm.le
    (scalarClockProfileJet_zero_upper α hα l t hm r)
    (scalarClockProfileJet_absBounded α hα l t hm r 1)
  have hw : Continuous w := continuous_iff_continuousAt.mpr fun x =>
    (R.rootWeight_deriv S (scalarClockProfileJet_deriv α hα l t hm r 0) x).continuousAt
  have hi := (hGauss.mul_poly_integrable hΦ (hw.mul S.continuous_Φ).aestronglyMeasurable).integrableOn (s := Ioi 0)
  have hiQ : IntegrableOn (fun x => w x*S.Φ x*x^2) (Ioi 0) := by
    have hh := hGauss.mul_poly_integrable (hΦ.mul (PolyBounded.id.pow 2))
      (hw.mul (S.continuous_Φ.mul (continuous_id.pow 2))).aestronglyMeasurable
    simpa only [mul_assoc] using hh.integrableOn (s := Ioi 0)
  have hfloor : rootCovarianceFloor S R.variance a ≤ ∫ x in Ioi 0, w x*S.Φ x*x^2 :=
    centered_weight_mul_lower (fun x _ => hlo x) (S.Φ_strictMono hm).monotoneOn
      (by intro x hx y hy hxy; change 0 ≤ x at hx; change 0 ≤ y at hy; change x^2 ≤ y^2; nlinarith)
      ha hz hi hiQ (rootCovarianceFloor_integrable S R.positive a hC hzpoly) hcenter
  exact (mul_le_mul_of_nonneg_left hfloor (sq_nonneg _)).trans
    (scalarClockProfileSlice_residual_root_lower α hα l t hm hmα r hR hcenter)

 

theorem scalarClockProfileSlice_exists_uniform_root_bound {s a : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hz : (scalarClockProfileSlice α hα l t hm hmα r).Φ a=0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : GaussianResidual), R.variance=s → R.residual.Cone →
      (∀ x, |R.residual.jet 1 x| ≤ 1) →
      (∫ x, R.plantedDensity (scalarClockProfileJet α hα l t m r 0) m x)=1 →
      (∫ x in Ioi 0, R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
        (scalarClockProfileSlice α hα l t hm hmα r).Φ x)=0 →
      δ ≤ ∫ x in Ioi 0, R.rootWeight (scalarClockProfileSlice α hα l t hm hmα r)
        (scalarClockProfileJet α hα l t m r 0) x*
        (scalarClockProfileSlice α hα l t hm hmα r).thirdTest x := by
  let S := scalarClockProfileSlice α hα l t hm hmα r
  obtain ⟨_,hC,hzpoly,_,_⟩ := scalarClockProfileSlice_polyBounded α hα l t hm hmα r
  refine ⟨(1/s)^2*rootCovarianceFloor S s a,
    mul_pos (sq_pos_of_pos (one_div_pos.mpr hs)) (rootCovarianceFloor_pos S hm hs ha hz hC hzpoly),?_⟩
  intro R hvar hR hg hn hc
  have hh := scalarClockProfileSlice_residual_uniform_root α hα l t hm hmα r hR hg hn ha hz hc
  simpa only [hvar] using hh

end
end SKFluctuations.Hierarchy

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

namespace SKFluctuations.Hierarchy

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

 
noncomputable def terminalSpinKernel (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) : Kernel (ι → ℝ) S :=
  (Kernel.const _ Measure.count).withDensity
    (fun x σ => ENNReal.ofReal (spinWeight w φ x σ))

 theorem terminalSpinDensity_measurable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    Measurable (Function.uncurry fun x σ => ENNReal.ofReal (spinWeight w φ x σ)) :=
  measurable_from_prod_countable_left fun σ =>
    (continuous_spinWeight hw φ σ).measurable.ennreal_ofReal

 theorem terminalSpinKernel_apply {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    terminalSpinKernel w φ x = Measure.count.withDensity
      (fun σ => ENNReal.ofReal (spinWeight w φ x σ)) := by
  rw [terminalSpinKernel, Kernel.withDensity_apply _ (terminalSpinDensity_measurable hw φ)]
  rfl

 theorem terminalSpinKernel_markov {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) : IsMarkovKernel (terminalSpinKernel w φ) := by
  constructor
  intro x
  constructor
  rw [terminalSpinKernel_apply hw φ, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [lintegral_count, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
    (fun σ _ => spinWeight_nonneg hw φ x σ), sum_spinWeight hw φ]
  exact ENNReal.ofReal_one

 

noncomputable def plantedStepKernel (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (m : ℝ) (q : ι → ℝ≥0)
    (tail : List (GaussianStep ι)) : Kernel (ι → ℝ) (ι → ℝ) :=
  (Kernel.const _ (Measure.pi fun i => gaussianReal 0 (q i))).withDensity
    (fun x z => ENNReal.ofReal (plantedTransitionDensity
      (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail) x z))

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
 theorem plantedStepDensity_measurable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (m : ℝ) (q : ι → ℝ≥0)
    (tail : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a ((m,q)::tail)) :
    Measurable (Function.uncurry (fun x z => ENNReal.ofReal (plantedTransitionDensity
      (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail) x z))) := by
  apply Measurable.ennreal_ofReal
  apply Continuous.measurable
  change Continuous (fun p : (ι → ℝ) × (ι → ℝ) => Real.exp
    (m * (gaussianHierarchy w φ tail (p.1+p.2)-gaussianHierarchy w φ ((m,q)::tail) p.1)))
  apply Real.continuous_exp.comp
  apply Continuous.const_mul
  exact ((gaussianHierarchy_continuous hw φ tail ha.2.2.2).comp
    (continuous_fst.add continuous_snd)).sub
    ((gaussianHierarchy_continuous hw φ ((m,q)::tail) ha).comp continuous_fst)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
 theorem plantedStepKernel_eq_tilted {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (m : ℝ) (q : ι → ℝ≥0)
    (tail : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a ((m,q)::tail))
    (x : ι → ℝ) : plantedStepKernel w φ m q tail x =
      tiltedLaw (Measure.pi fun i => gaussianReal 0 (q i)) m
        (fun z => gaussianHierarchy w φ tail (x+z)) := by
  rw [plantedStepKernel, Kernel.withDensity_apply _
    (plantedStepDensity_measurable hw φ m q tail ha), Kernel.const_apply]
  exact plantedTransitionLaw_eq ha.2.2.1.ne' x
    (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
 theorem plantedStepKernel_markov {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (m : ℝ) (q : ι → ℝ≥0)
    (tail : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a ((m,q)::tail)) :
    IsMarkovKernel (plantedStepKernel w φ m q tail) := by
  constructor
  intro x
  rw [plantedStepKernel_eq_tilted hw φ m q tail ha x]
  exact tiltedLaw_isProbability (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x)

 

def ForwardPath (E S : Type) : ℕ → Type
  | 0 => S
  | n+1 => E × ForwardPath E S n

instance forwardPathMeasurableSpace {E S : Type} [MeasurableSpace E] [MeasurableSpace S] :
    (n : ℕ) → MeasurableSpace (ForwardPath E S n)
  | 0 => inferInstanceAs (MeasurableSpace S)
  | n+1 => @Prod.instMeasurableSpace E (ForwardPath E S n) _ (forwardPathMeasurableSpace n)

noncomputable def hierarchyPathKernel (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) : (steps : List (GaussianStep ι)) →
      Kernel (ι → ℝ) (ForwardPath (ι → ℝ) S steps.length)
  | [] => terminalSpinKernel (S := S) w φ
  | (m,q)::tail => plantedStepKernel w φ m q tail ⊗ₖ
      (hierarchyPathKernel w φ tail).comap (fun p => p.1+p.2)
        (measurable_fst.add measurable_snd)

 theorem hierarchyPathKernel_markov {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) : IsMarkovKernel (hierarchyPathKernel w φ steps) := by
  induction steps generalizing a with
  | nil => exact terminalSpinKernel_markov hw φ
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have hstep := plantedStepKernel_markov hw φ m q tail ha
    have htail := ih ha.2.2.2
    change IsMarkovKernel (plantedStepKernel w φ m q tail ⊗ₖ
      (hierarchyPathKernel w φ tail).comap (fun p => p.1+p.2)
        (measurable_fst.add measurable_snd))
    infer_instance

 def ForwardPath.spin {E S : Type} : (n : ℕ) → ForwardPath E S n → S
  | 0 => id
  | n+1 => fun p => ForwardPath.spin n p.2

 theorem ForwardPath.spin_measurable {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    (n : ℕ) : Measurable (@ForwardPath.spin E S n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.comp measurable_snd

 

theorem ForwardPath.integrable_spin {E S F : Type} [MeasurableSpace E]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (n : ℕ) (μ : Measure (ForwardPath E S n))
    [IsFiniteMeasure μ] (A : S → F) :
    Integrable (fun p => A (ForwardPath.spin n p)) μ := by
  classical
  apply (integrable_const (∑ s, ‖A s‖)).mono'
    (((measurable_of_countable A).comp (ForwardPath.spin_measurable n)).stronglyMeasurable.aestronglyMeasurable)
  exact Eventually.of_forall (fun p => Finset.single_le_sum
    (fun s _ => norm_nonneg (A s)) (Finset.mem_univ (ForwardPath.spin n p)))

theorem integral_terminalSpinKernel {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (x : ι → ℝ) :
    (∫ σ, A σ ∂terminalSpinKernel w φ x) = ∑ σ, spinWeight w φ x σ * A σ := by
  rw [terminalSpinKernel_apply hw φ,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_of_countable _) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (spinWeight_nonneg hw φ x _), smul_eq_mul]
  exact integral_count _

 

theorem integral_hierarchyPathKernel {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (x : ι → ℝ) :
    (∫ p, A (ForwardPath.spin steps.length p) ∂hierarchyPathKernel w φ steps x) =
      gaussianHierarchyMean w φ A steps x := by
  induction steps generalizing a x with
  | nil => exact integral_terminalSpinKernel hw φ A x
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have hstep := plantedStepKernel_markov hw φ m q tail ha
    have htail := hierarchyPathKernel_markov hw φ tail ha.2.2.2
    have hwhole := hierarchyPathKernel_markov hw φ ((m,q)::tail) ha
    have hf := ForwardPath.integrable_spin (tail.length+1)
      (hierarchyPathKernel w φ ((m,q)::tail) x) A
    change Integrable (fun p : (ι → ℝ) × ForwardPath (ι → ℝ) S tail.length =>
      A (ForwardPath.spin tail.length p.2))
      ((plantedStepKernel w φ m q tail ⊗ₖ
        (hierarchyPathKernel w φ tail).comap (fun p => p.1+p.2)
          (measurable_fst.add measurable_snd)) x) at hf
    change (∫ p : (ι → ℝ) × ForwardPath (ι → ℝ) S tail.length,
      A (ForwardPath.spin tail.length p.2) ∂
      ((plantedStepKernel w φ m q tail ⊗ₖ
        (hierarchyPathKernel w φ tail).comap (fun p => p.1+p.2)
          (measurable_fst.add measurable_snd)) x)) = _
    rw [ProbabilityTheory.integral_compProd hf]
    simp only [Kernel.comap_apply]
    simp_rw [ih ha.2.2.2]
    rw [plantedStepKernel_eq_tilted hw φ m q tail ha x,
      integral_tiltedLaw (F := fun z => gaussianHierarchy w φ tail (x+z))
        ((gaussianHierarchy_continuous hw φ tail ha.2.2.2).comp
          (continuous_const.add continuous_id)).measurable
        (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x)]
    rfl

end SKFluctuations.Hierarchy

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SKFluctuations.Hierarchy

 

theorem condExp_compProd_first
    {A B F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure A) [IsFiniteMeasure μ] (κ : Kernel A B) [IsMarkovKernel κ]
    (f : A × B → F) (hf : Integrable f (μ ⊗ₘ κ)) :
    (μ ⊗ₘ κ)[f | (inferInstance : MeasurableSpace A).comap Prod.fst] =ᵐ[μ ⊗ₘ κ]
      fun p => ∫ b, f (p.1,b) ∂κ p.1 := by
  let η : Kernel A B := ProbabilityTheory.condDistrib
    (Prod.snd : A × B → B) Prod.fst (μ ⊗ₘ κ)
  have hc : η =ᵐ[μ] κ := by
    apply Kernel.ae_eq_of_compProd_eq
    have h := compProd_map_condDistrib (μ := μ ⊗ₘ κ)
      (X := (Prod.fst : A × B → A)) (mβ := inferInstance)
      measurable_fst.aemeasurable measurable_snd.aemeasurable
    simpa only [show Measure.map (Prod.fst : A × B → A) (μ ⊗ₘ κ) = μ from Measure.fst_compProd μ κ,
      show (fun p : A × B => (p.1,p.2)) = id from rfl, Measure.map_id] using h
  have hc' : ∀ᵐ p ∂μ ⊗ₘ κ, η p.1 = κ p.1 := by
    have hm : Measure.map (Prod.fst : A × B → A) (μ ⊗ₘ κ) = μ :=
      Measure.fst_compProd μ κ
    have hh : ∀ᵐ a ∂Measure.map (Prod.fst : A × B → A) (μ ⊗ₘ κ), η a = κ a := by
      rw [hm]
      exact hc
    exact ae_of_ae_map measurable_fst.aemeasurable hh
  have h := condExp_prod_ae_eq_integral_condDistrib'
    (μ := μ ⊗ₘ κ) (X := (Prod.fst : A × B → A)) (Y := Prod.snd)
    measurable_fst measurable_snd.aemeasurable
    (show Integrable f ((μ ⊗ₘ κ).map fun p : A × B => (p.1,p.2)) by
      simpa only [show (fun p : A × B => (p.1,p.2)) = id from rfl, Measure.map_id] using hf)
  exact h.trans (hc'.mono fun p hp => by
    change (∫ b, f (p.1,b) ∂η p.1) = _
    rw [hp])

end SKFluctuations.Hierarchy

end

end OAI
