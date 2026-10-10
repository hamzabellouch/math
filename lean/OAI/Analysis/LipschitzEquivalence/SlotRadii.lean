import OAI.Analysis.LipschitzEquivalence.InverseTails

namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample

namespace HilbertSlots
open scoped ENNReal NNReal
open Filter Topology
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

theorem hasSum_parent {b : ℕ → ℝ} {B : ℝ} (hb : HasSum b B) :
    HasSum (fun n => b (n / 2)) (2 * B) := by
  rw [two_mul]
  apply Equiv.natSumNatEquivNat.hasSum_iff.1
  apply HasSum.sum
  · simpa [Function.comp_def, Nat.mul_add_div] using hb
  · simpa [Function.comp_def, Nat.mul_add_div] using hb

abbrev SlotDomain (E : ℕ → Type uE) [∀ i, NormedAddCommGroup (E i)] :=
  WithLp 2 (HilbertSum E × RealL2)
abbrev RadiusBlock (E : ℕ → Type uE) [∀ i, NormedAddCommGroup (E i)] (n : ℕ) :=
  WithLp 2 (E n × WithLp 2 (E (n/2) × ℝ))

def aSq (x : SlotDomain E) (n : ℕ) : ℝ :=
  ‖x.fst n‖^2 + ‖x.fst (n/2)‖^2 + ‖x.snd (n/2)‖^2

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem aSq_nonneg (x : SlotDomain E) (n : ℕ) : 0 ≤ aSq x n := by
  unfold aSq
  positivity

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem hasSum_aSq (x : SlotDomain E) :
    HasSum (aSq x) (3 * ‖x.fst‖^2 + 2 * ‖x.snd‖^2) := by
  have hu : HasSum (fun n => ‖x.fst n‖^2) (‖x.fst‖^2) := by
    simpa using lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x.fst
  have hv : HasSum (fun n => ‖x.snd n‖^2) (‖x.snd‖^2) := by
    simpa using lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x.snd
  convert (hu.add (hasSum_parent hu)).add (hasSum_parent hv) using 1
  · rfl
  · ring

def radiusBlock (x : SlotDomain E) (n : ℕ) : RadiusBlock E n :=
  WithLp.toLp 2 (x.fst n, WithLp.toLp 2 (x.fst (n/2), x.snd (n/2)))

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem radiusBlock_norm_sq (x : SlotDomain E) (n : ℕ) :
    ‖radiusBlock x n‖^2 = aSq x n := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  simp only [radiusBlock, WithLp.toLp_fst, WithLp.toLp_snd, aSq]
  ring

def radiusSeq (x : SlotDomain E) : HilbertSum (RadiusBlock E) :=
  ⟨radiusBlock x, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, radiusBlock_norm_sq] using
      (hasSum_aSq x).summable)⟩

omit [∀ i, InnerProductSpace ℝ (E i)] in
@[simp] theorem radiusSeq_apply (x : SlotDomain E) (n : ℕ) : radiusSeq x n = radiusBlock x n := rfl

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem radiusSeq_norm_sq (x : SlotDomain E) :
    ‖radiusSeq x‖^2 = 3 * ‖x.fst‖^2 + 2 * ‖x.snd‖^2 := by
  rw [norm_sq_tsum]
  simp only [radiusSeq_apply, radiusBlock_norm_sq]
  exact (hasSum_aSq x).tsum_eq

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem radiusSeq_norm_le (x : SlotDomain E) : ‖radiusSeq x‖ ≤ Real.sqrt 3 * ‖x‖ := by
  have h := radiusSeq_norm_sq x
  have hx := WithLp.prod_norm_sq_eq_of_L2 x
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).1
  rw [mul_pow, hs]
  nlinarith [sq_nonneg ‖x.snd‖]

def radiusCLM : SlotDomain E →L[ℝ] HilbertSum (RadiusBlock E) :=
  ({ toFun := radiusSeq
     map_add' := by
       intro x y
       apply lp.ext
       funext n
       apply (WithLp.equiv 2 (E n × WithLp 2 (E (n/2) × ℝ))).injective
       simp [radiusSeq, radiusBlock]
       rfl
     map_smul' := by
       intro c x
       apply lp.ext
       funext n
       apply (WithLp.equiv 2 (E n × WithLp 2 (E (n/2) × ℝ))).injective
       simp [radiusSeq, radiusBlock]
       rfl } : SlotDomain E →ₗ[ℝ] HilbertSum (RadiusBlock E)).mkContinuous
    (Real.sqrt 3) radiusSeq_norm_le

def tailCLM (N : ℕ) : HilbertSum E →L[ℝ] HilbertSum E :=
  ContinuousLinearMap.id ℝ (HilbertSum E) -
    ∑ i ∈ Finset.range N, (lp.singleContinuousLinearMap ℝ E 2 i).comp (lp.evalCLM ℝ E 2 i)

@[simp] theorem tailCLM_apply (N : ℕ) (x : HilbertSum E) : tailCLM N x = x - cutHead N x := by
  simp only [tailCLM, sub_apply, ContinuousLinearMap.id_apply,
    sum_apply, ContinuousLinearMap.comp_apply, cutHead,
    lp.singleContinuousLinearMap_apply]
  rfl

theorem tail_norm_le (N : ℕ) (x : HilbertSum E) : ‖tailCLM N x‖ ≤ ‖x‖ := by
  have hh := norm_sub_prefix_sq x N
  have hn : 0 ≤ ∑ i ∈ Finset.range N, ‖x i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [tailCLM_apply]
  nlinarith [norm_nonneg (x-cutHead N x), norm_nonneg x]

def radius (N : ℕ) (x : SlotDomain E) : ℝ := ‖tailCLM N (radiusCLM x)‖

theorem radius_nonneg (N : ℕ) (x : SlotDomain E) : 0 ≤ radius N x := norm_nonneg _

theorem radius_sq (N : ℕ) (x : SlotDomain E) :
    radius N x ^ 2 = ‖radiusSeq x‖^2 - ∑ i ∈ Finset.range N, aSq x i := by
  simpa [radius, radiusCLM, radiusSeq_apply, radiusBlock_norm_sq] using norm_sub_prefix_sq (radiusSeq x) N

theorem radius_zero_sq (x : SlotDomain E) : radius 0 x ^ 2 = 3*‖x.fst‖^2+2*‖x.snd‖^2 := by
  rw [radius_sq, Finset.range_zero, Finset.sum_empty, sub_zero, radiusSeq_norm_sq]

theorem radius_step (N : ℕ) (x : SlotDomain E) :
    aSq x N = radius N x ^ 2 - radius (N+1) x ^ 2 := by
  rw [radius_sq, radius_sq, Finset.sum_range_succ]
  ring

theorem radius_antitone (x : SlotDomain E) : Antitone (fun N => radius N x) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := radius_step n x
  nlinarith [aSq_nonneg x n, radius_nonneg n x, radius_nonneg (n+1) x]

theorem radius_tendsto (x : SlotDomain E) : Tendsto (fun N => radius N x) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := radiusSeq x)).sub (prefix_tendsto (radiusSeq x))).norm
  simpa [radius, radiusCLM] using h

theorem radius_lipschitz (N : ℕ) : LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg _⟩ (radius (E := E) N) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro x y
  change ‖‖tailCLM N (radiusCLM x)‖ - ‖tailCLM N (radiusCLM y)‖‖ ≤ _
  rw [Real.norm_eq_abs]
  apply (abs_norm_sub_norm_le _ _).trans
  rw [← map_sub, ← map_sub]
  exact (tail_norm_le N _).trans (radiusSeq_norm_le (x-y))

end HilbertSlots

end LipschitzCounterexample
end

end OAI
