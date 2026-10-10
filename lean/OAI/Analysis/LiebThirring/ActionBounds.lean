import OAI.Analysis.LiebThirring.BoundaryValues

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma trace_square_real {H : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) :
    trace (H * H) = ∑ i, ∑ j, H i j ^ 2 := by
  simp only [trace, diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : H j i = H i j := by simpa only [conjTranspose_apply, star_trivial] using congrFun (congrFun hH i) j
  rw [he, pow_two]

lemma quadratic_swap {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    (a b : Fin N → ℝ) :
    (∑ i, a i * (B *ᵥ b) i) = ∑ i, b i * (B *ᵥ a) i := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : B j i = B i j := by simpa only [conjTranspose_apply, star_trivial] using congrFun (congrFun hB i) j
  rw [he]
  ring

lemma trace_rankone_mul (a : Fin N → ℝ) (H : Matrix (Fin N) (Fin N) ℝ) :
    trace (vecMulVec a a * H) = ∑ i, a i * (H *ᵥ a) i := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic_hasDerivAt {a a' : ℝ → Fin N → ℝ}
    {B B' : ℝ → Matrix (Fin N) (Fin N) ℝ} {x : ℝ}
    (ha : ∀ i, HasDerivAt (fun t ↦ a t i) (a' x i) x)
    (hB : ∀ i j, HasDerivAt (fun t ↦ B t i j) (B' x i j) x)
    (hBx : (B x).IsHermitian) :
    HasDerivAt (fun t ↦ ∑ i, a t i * (B t *ᵥ a t) i)
      (2 * (∑ i, a' x i * (B x *ᵥ a x) i) +
        trace (vecMulVec (a x) (a x) * B' x)) x := by
  have hh := HasDerivAt.sum (u := Finset.univ) (fun i _ ↦
    (ha i).mul (HasDerivAt.sum (u := Finset.univ) (fun j _ ↦ (hB i j).mul (ha j))))
  simp only [Finset.sum_apply, Pi.mul_apply] at hh
  convert! hh using 1
  · funext t
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply]
  · rw [trace_rankone_mul]
    have hs := quadratic_swap hBx (a x) (a' x)
    change 2 * (∑ i, a' x i * (∑ j, B x i j * a x j)) +
        (∑ i, a x i * (∑ j, B' x i j * a x j)) =
      ∑ i, (a' x i * (∑ j, B x i j * a x j) +
        a x i * ∑ j, (B' x i j * a x j + B x i j * a' x j))
    simp_rw [Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
    change (∑ i, a x i * (∑ j, B x i j * a' x j)) =
      (∑ i, a' x i * (∑ j, B x i j * a x j)) at hs
    linarith

end SharpLiebThirring.ActionProof
namespace SharpLiebThirring.SpectralProof
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

def actionYoungConstant (σ : ℝ) : ℝ := σ ^ σ / (1 + σ) ^ (1 + σ)

lemma sigma_holderConjugate {σ : ℝ} (hσ : 0 < σ) :
    (1 + σ).HolderConjugate (1 + 1 / σ) := by
  rw [Real.holderConjugate_iff]
  constructor
  · linarith
  · have h1 : 1 + σ ≠ 0 := by positivity
    have h2 : 1 + 1 / σ ≠ 0 := by positivity
    field_simp
    ring

lemma young_action_bound {σ W m : ℝ} (hσ : 0 < σ) (hW : 0 ≤ W) (hm : 0 ≤ m) :
    W * m - m ^ (1 + 1 / σ) ≤ actionYoungConstant σ * W ^ (1 + σ) := by
  let q := 1 + 1 / σ
  have hq : 0 < q := by dsimp [q]; positivity
  have hp : 0 < 1 + σ := by positivity
  have hy := Real.young_inequality_of_nonneg (div_nonneg hW hq.le) hm (sigma_holderConjugate hσ)
  change W / q * m ≤ (W / q) ^ (1 + σ) / (1 + σ) + m ^ q / q at hy
  have hc : q * ((W / q) ^ (1 + σ) / (1 + σ)) = actionYoungConstant σ * W ^ (1 + σ) := by
    rw [Real.div_rpow hW hq.le]
    have hqe : q = (1 + σ) / σ := by dsimp [q]; field_simp; ring
    have hpow : q ^ (1 + σ) = q * ((1 + σ) ^ σ / σ ^ σ) := by
      rw [Real.rpow_add hq, Real.rpow_one, hqe, Real.div_rpow hp.le hσ.le]
    rw [hpow]
    unfold actionYoungConstant
    rw [Real.rpow_add hp, Real.rpow_one]
    have hsp := Real.rpow_pos_of_pos hσ σ
    have hpp := Real.rpow_pos_of_pos hp σ
    field_simp
  have hy' := mul_le_mul_of_nonneg_left hy hq.le
  have hm' : q * (m ^ q / q) = m ^ q := by field_simp
  have hw' : q * (W / q * m) = W * m := by field_simp
  rw [mul_add, hc, hm', hw'] at hy'
  linarith

lemma triangular_diagonal_energy_nonpos {N : ℕ} (k : Fin N → ℝ)
    (hk : ∀ i, 0 ≤ k i) (hkord : Antitone k) (C : Matrix (Fin N) (Fin N) ℝ)
    (hC : ∀ i j, i < j → C i j = 0) :
    (∑ i, ∑ j, C i j ^ 2 * (k i ^ 2 - k j ^ 2)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  apply Finset.sum_nonpos
  intro j _
  by_cases hij : i < j
  · simp [hC i j hij]
  · apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    have hh := hkord (le_of_not_gt hij)
    nlinarith [hk i, hk j]

end SharpLiebThirring.SpectralProof
namespace SharpLiebThirring.PathProof
open Set Filter
open scoped Topology

/-- The endpoint barrier used to remove the field cutoff. No strict negativity
or Lipschitz property of the scalar derivative is needed. -/
lemma upper_barrier {f f' : ℝ → ℝ} {l r κ : ℝ}
    (hc : ContinuousOn f (Icc l r))
    (hd : ∀ x ∈ Icc l r, HasDerivAt f (f' x) x)
    (hl : f l ≤ κ)
    (hb : ∀ x ∈ Icc l r, κ < f x → f' x ≤ 0) :
    ∀ x ∈ Icc l r, f x ≤ κ := by
  intro x hx
  have he (η : ℝ) (hη : 0 < η) : f x ≤ κ + η + η * (x - l) := by
    apply image_le_of_deriv_right_lt_deriv_boundary hc
      (fun t ht ↦ (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
      (B := fun t ↦ κ + η + η * (t - l)) (B' := fun _ ↦ η)
    · simpa using (hl.trans (le_add_of_nonneg_right hη.le))
    · intro t
      convert! ((hasDerivAt_id t).sub_const l).const_mul η |>.const_add (κ + η) using 1
      simp
    · intro t ht hft
      have hgt : κ < f t := by
        rw [hft]
        nlinarith [mul_nonneg hη.le (sub_nonneg.2 ht.1)]
      exact lt_of_le_of_lt (hb t ⟨ht.1, ht.2.le⟩ hgt) hη
    · exact hx
  have ht : Tendsto (fun η : ℝ ↦ κ + η + η * (x - l)) (𝓝[>] 0) (𝓝 κ) := by
    have hh : Continuous (fun η : ℝ ↦ κ + η + η * (x - l)) := by fun_prop
    simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with η hη using he η hη)

lemma two_endpoint_barrier {f f' : ℝ → ℝ} {l r κ : ℝ}
    (hc : ContinuousOn f (Icc l r))
    (hd : ∀ x ∈ Icc l r, HasDerivAt f (f' x) x)
    (hl : f l ≤ κ) (hr : -κ ≤ f r)
    (hb : ∀ x ∈ Icc l r, κ < |f x| → f' x ≤ 0) :
    ∀ x ∈ Icc l r, |f x| ≤ κ := by
  have hup := upper_barrier hc hd hl (fun x hx hh ↦ hb x hx (hh.trans_le (le_abs_self _)))
  let g := fun t : ℝ ↦ -f (l + r - t)
  have hmap : MapsTo (fun t : ℝ ↦ l + r - t) (Icc l r) (Icc l r) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hgc : ContinuousOn g (Icc l r) := hc.comp (by fun_prop) hmap |>.neg
  have hgd (t : ℝ) (ht : t ∈ Icc l r) : HasDerivAt g (f' (l + r - t)) t := by
    convert! ((hd (l + r - t) (hmap ht)).comp t ((hasDerivAt_id t).const_sub (l + r))).neg using 1
    ring
  have hgl : g l ≤ κ := by simpa [g] using (neg_le_neg hr)
  have hgb (t : ℝ) (ht : t ∈ Icc l r) (hh : κ < g t) : f' (l + r - t) ≤ 0 := by
    exact hb _ (hmap ht) (hh.trans_le (neg_le_abs _))
  have hlow := upper_barrier hgc hgd hgl hgb
  intro x hx
  apply abs_le.2
  constructor
  · have hh := hlow (l + r - x) (hmap hx)
    have he : l + r - (l + r - x) = x := by ring
    simpa [g, he] using (neg_le_neg hh)
  · exact hup x hx

end SharpLiebThirring.PathProof

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

/-- Real entry evaluation on the actual symmetric-matrix normed space. -/
def realSelfAdjointEntryCLM (i j : Fin N) :
    selfAdjoint (Matrix (Fin N) (Fin N) ℝ) →L[ℝ] ℝ :=
  { toFun := fun B ↦ (B : Matrix (Fin N) (Fin N) ℝ) i j
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    cont := by
      have hc : Continuous (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A i j) :=
        (({ toFun := fun A : Matrix (Fin N) (Fin N) ℝ ↦ A i j
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl } : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap).continuous
      exact hc.comp continuous_subtype_val }

lemma realSelfAdjoint_entry_derivative
    {B : ℝ → selfAdjoint (Matrix (Fin N) (Fin N) ℝ)}
    {B' : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)} {x : ℝ}
    (hB : HasDerivAt B B' x) (i j : Fin N) :
    HasDerivAt (fun t ↦ (B t : Matrix (Fin N) (Fin N) ℝ) i j)
      ((B' : Matrix (Fin N) (Fin N) ℝ) i j) x :=
  (realSelfAdjointEntryCLM i j).hasFDerivAt.comp_hasDerivAt x hB

lemma real_rankone_isHermitian (a : Fin N → ℝ) : (vecMulVec a a).IsHermitian := by
  ext i j
  simp [vecMulVec, conjTranspose_apply, mul_comm]

/-- The exact penalized action identity, pointwise wherever the amplitude is
  differentiable. Hence it applies to the a.e. derivative of H¹ amplitudes. -/
lemma action_ode_identity {σ δ ε : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (hε : 0 < ε)
    (k : Fin N → ℝ) {a a' : ℝ → Fin N → ℝ}
    {B : ℝ → selfAdjoint (Matrix (Fin N) (Fin N) ℝ)}
    {B' : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)} {x : ℝ}
    (ha : ∀ i, HasDerivAt (fun t ↦ a t i) (a' x i) x)
    (hB : HasDerivAt B B' x)
    (hode : ε • (B' : Matrix (Fin N) (Fin N) ℝ) =
      matrixField σ δ k (B x) - vecMulVec (a x) (a x)) :
    HasDerivAt (fun t ↦ fieldPrimitive σ δ k (B t) +
      ∑ i, a t i * ((B t : Matrix (Fin N) (Fin N) ℝ) *ᵥ a t) i)
      (2 * (∑ i, a' x i * ((B x : Matrix (Fin N) (Fin N) ℝ) *ᵥ a x) i) -
        constraintDefect σ δ k (B x, a x) / ε) x := by
  let D := matrixField σ δ k (B x) - vecMulVec (a x) (a x)
  have hD : D.IsHermitian :=
    (matrixField_isHermitian hσ hδ k (B x).prop).sub (real_rankone_isHermitian _)
  have hb' : (B' : Matrix (Fin N) (Fin N) ℝ) = ε⁻¹ • D := by
    rw [show D = ε • (B' : Matrix (Fin N) (Fin N) ℝ) from hode.symm,
      smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have ht : trace (D * (B' : Matrix (Fin N) (Fin N) ℝ)) =
      constraintDefect σ δ k (B x, a x) / ε := by
    rw [hb', Matrix.mul_smul, trace_smul, trace_square_real hD]
    simp only [smul_eq_mul, constraintDefect, D, Matrix.sub_apply, vecMulVec_apply,
      div_eq_mul_inv, mul_comm]
  have hq := quadratic_hasDerivAt (B := fun t ↦ (B t : Matrix (Fin N) (Fin N) ℝ))
    (B' := fun _ ↦ (B' : Matrix (Fin N) (Fin N) ℝ)) ha
    (fun i j ↦ realSelfAdjoint_entry_derivative hB i j) (B x).prop
  have hj := fieldPrimitive_path_derivative hσ hδ k hB
  convert! hj.add hq using 1
  dsimp only [D] at ht
  rw [Matrix.sub_mul, trace_sub] at ht
  linarith

lemma quadratic_square_real {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    (a : Fin N → ℝ) :
    (∑ i, a i * (B ^ 2 *ᵥ a) i) = ∑ i, (B *ᵥ a) i ^ 2 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, quadratic_swap hB]
  simp [pow_two]

lemma action_pointwise_square_bound {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    (a v : Fin N → ℝ) :
    2 * (∑ i, v i * (B *ᵥ a) i) ≤
      (∑ i, v i ^ 2) + ∑ i, a i * (B ^ 2 *ᵥ a) i := by
  rw [quadratic_square_real hB]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (v i - (B *ᵥ a) i)]

lemma action_penalty_pointwise {σ δ ε : ℝ} (k : Fin N → ℝ)
    (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) (a v : Fin N → ℝ) :
    2 * (∑ i, v i * ((B : Matrix (Fin N) (Fin N) ℝ) *ᵥ a) i) -
        constraintDefect σ δ k (B, a) / ε ≤
      (∑ i, v i ^ 2) + (∑ i, k i ^ 2 * a i ^ 2) - (∑ i, a i ^ 2) ^ (1 + 1 / σ) +
        (actionDefect σ k (B, a) - constraintDefect σ δ k (B, a) / ε) := by
  have hh := action_pointwise_square_bound B.prop a v
  have hK : (∑ i, a i * ((diagonal (fun i ↦ k i ^ 2) -
      (B : Matrix (Fin N) (Fin N) ℝ) ^ 2) *ᵥ a) i) =
      (∑ i, k i ^ 2 * a i ^ 2) - ∑ i, a i * ((B : Matrix (Fin N) (Fin N) ℝ) ^ 2 *ᵥ a) i := by
    rw [sub_mulVec]
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, mulVec_diagonal]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold actionDefect
  dsimp only
  rw [hK]
  linarith

end SharpLiebThirring.ActionProof

end
end
end

end OAI
