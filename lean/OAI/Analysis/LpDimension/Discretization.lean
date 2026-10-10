import OAI.Analysis.LpDimension.ConvexRepresentation
import OAI.Analysis.LpDimension.GridObstruction

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uE uI uΩ

namespace SubpolynomialLp

def PairIndex (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
instance (n : ℕ) : Fintype (PairIndex n) := inferInstanceAs (Fintype {ij : Fin n × Fin n // ij.1 < ij.2})

lemma pairIndex_card (n : ℕ) : Fintype.card (PairIndex n) = n.choose 2 := by
  classical
  change Fintype.card {ij : Fin n × Fin n // ij.1 < ij.2} = _
  rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt]
  simp

def pairPower (p : ℝ) {n : ℕ} (z : Fin n → ℝ) : PairIndex n → ℝ :=
  fun e => |z e.val.1 - z e.val.2| ^ p

lemma pairPower_nonneg (p : ℝ) {n : ℕ} (z : Fin n → ℝ) (e : PairIndex n) :
    0 ≤ pairPower p z e := Real.rpow_nonneg (abs_nonneg _) _

lemma pairPower_continuous (p : ℝ) (hp : 0 < p) (n : ℕ) : Continuous (pairPower (n := n) p) := by
  apply continuous_pi
  intro e
  unfold pairPower
  exact ((continuous_apply e.val.1).sub (continuous_apply e.val.2)).abs.rpow_const
    (fun _ => Or.inr hp.le)

lemma pairPower_pair_le_sum (p : ℝ) {n : ℕ} (z : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    |z i-z j|^p ≤ ∑ e, pairPower p z e := by
  classical
  rcases lt_or_gt_of_ne hij with h | h
  · exact Finset.single_le_sum (fun e _ => pairPower_nonneg p z e) (Finset.mem_univ ⟨(i,j),h⟩)
  · rw [abs_sub_comm]
    exact Finset.single_le_sum (fun e _ => pairPower_nonneg p z e) (Finset.mem_univ ⟨(j,i),h⟩)

lemma pairPower_sum_bound (p : ℝ) (hp : 0 < p) {n : ℕ} (z : Fin n → ℝ)
    (i₀ : Fin n) (hz : z i₀ = 0) (hs : ∑ e, pairPower p z e = 1) :
    ∀ i, |z i| ≤ 1 := by
  intro i
  by_cases hi : i = i₀
  · simp [hi,hz]
  have h := pairPower_pair_le_sum p z i i₀ hi
  rw [hs, hz, sub_zero] at h
  apply (Real.rpow_le_rpow_iff (abs_nonneg _) zero_le_one hp).mp
  simpa using h

def normalizedLabels (p : ℝ) {n : ℕ} (i₀ : Fin n) : Set (Fin n → ℝ) :=
  {z | z i₀ = 0 ∧ ∑ e, pairPower p z e = 1}

def normalizedPowers (p : ℝ) {n : ℕ} (i₀ : Fin n) : Set (PairIndex n → ℝ) :=
  pairPower p '' normalizedLabels p i₀

lemma normalizedLabels_compact (p : ℝ) (hp : 0 < p) {n : ℕ} (i₀ : Fin n) :
    IsCompact (normalizedLabels p i₀) := by
  have hc : IsClosed (normalizedLabels p i₀) :=
    (isClosed_eq (continuous_apply i₀) continuous_const).inter
      (isClosed_eq (continuous_finsetSum _ (fun e _ =>
        (continuous_apply e).comp (pairPower_continuous p hp n))) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro z hz
  have h := pairPower_sum_bound p hp z i₀ hz.1 hz.2
  exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩

lemma normalizedPowers_compact (p : ℝ) (hp : 0 < p) {n : ℕ} (i₀ : Fin n) :
    IsCompact (normalizedPowers p i₀) :=
  (normalizedLabels_compact p hp i₀).image (pairPower_continuous p hp n)

lemma normalizedPowers_sum (p : ℝ) {n : ℕ} (i₀ : Fin n) {v : PairIndex n → ℝ}
    (hv : v ∈ normalizedPowers p i₀) : ∑ e, v e = 1 := by
  obtain ⟨z, hz, rfl⟩ := hv
  exact hz.2

lemma pairPower_smul_sub (p : ℝ) {n : ℕ} (z : Fin n → ℝ) (a b : ℝ) :
    pairPower p (fun i => a * (z i-b)) = |a|^p • pairPower p z := by
  ext e
  simp only [pairPower, Pi.smul_apply, smul_eq_mul]
  rw [show a*(z e.val.1-b)-a*(z e.val.2-b) = a*(z e.val.1-z e.val.2) by ring,
    abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

lemma pairPower_normalize (p : ℝ) (hp : 0 < p) {n : ℕ} (i₀ : Fin n) (z : Fin n → ℝ)
    (hs : 0 < ∑ e, pairPower p z e) :
    (∑ e, pairPower p z e)⁻¹ • pairPower p z ∈ normalizedPowers p i₀ := by
  let s := ∑ e, pairPower p z e
  let a := (s⁻¹)^(1/p)
  have ha : 0 < a := Real.rpow_pos_of_pos (inv_pos.mpr hs) _
  have hap : |a|^p = s⁻¹ := by
    rw [abs_of_pos ha]
    dsimp [a]
    rw [one_div]
    exact (Real.rpow_inv_rpow (inv_nonneg.mpr hs.le) hp.ne' :
      (s⁻¹^p⁻¹)^p = s⁻¹)
  refine ⟨(fun i => a*(z i-z i₀)), ⟨by simp, ?_⟩, ?_⟩
  · rw [pairPower_smul_sub, hap]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · rw [pairPower_smul_sub, hap]


lemma lp_norm_rpow_integral (p : ℝ) (hp : 0 < p) {Ω : Type uΩ} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Lp ℝ (ENNReal.ofReal p) μ) :
    ‖f‖^p = ∫ t, |f t|^p ∂μ := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top (Lp.memLp f).aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  simp only [Real.norm_eq_abs]
  exact Real.rpow_inv_rpow (integral_nonneg (fun t => Real.rpow_nonneg (abs_nonneg _) _)) hp.ne'

lemma lpDifference_integrable (p : ℝ) (hp : 0 < p) {Ω : Type uΩ} [MeasurableSpace Ω]
    {μ : Measure Ω} (f g : Lp ℝ (ENNReal.ofReal p) μ) :
    Integrable (fun t => |f t-g t|^p) μ := by
  have h := ((Lp.memLp f).sub (Lp.memLp g)).norm_rpow
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  rw [memLp_one_iff_integrable] at h
  simpa only [Real.norm_eq_abs, Pi.sub_apply, ENNReal.toReal_ofReal hp.le] using h

lemma lpDifference_integral (p : ℝ) (hp : 0 < p) {Ω : Type uΩ} [MeasurableSpace Ω]
    {μ : Measure Ω} (f g : Lp ℝ (ENNReal.ofReal p) μ) :
    (∫ t, |f t-g t|^p ∂μ) = ‖f-g‖^p := by
  rw [lp_norm_rpow_integral p hp]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with t ht
  rw [ht]
  rfl


lemma pad_coordinates {I : Type uI} (p : ℝ) (hp : 0 < p) {k d : ℕ} (hk : k ≤ d)
    (y : I → Fin k → ℝ) : ∃ Y : I → Fin d → ℝ, ∀ i j,
      (∑ a, |Y i a-Y j a|^p) = ∑ a, |y i a-y j a|^p := by
  induction d, hk using Nat.le_induction with
  | base => exact ⟨y, fun _ _ => rfl⟩
  | succ d hd ih =>
    obtain ⟨Y,hY⟩ := ih
    refine ⟨fun i => Fin.snoc (Y i) 0, ?_⟩
    intro i j
    simpa [Fin.sum_univ_castSucc, Real.zero_rpow hp.ne'] using hY i j

/-- Ball's finite-coordinate isometry, obtained by applying Carathéodory's theorem
to the normalized pairwise `p`th powers. -/
lemma exact_discretization_ge_one (p : ℝ) (hp : 1 ≤ p) (n : ℕ) (hn : 2 ≤ n)
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Fin n → Lp ℝ (ENNReal.ofReal p) μ) (hx : Function.Injective x) :
    ∃ y : Fin n → Fin (n.choose 2) → ℝ, ∀ i j,
      coordinateDistance p (y i) (y j) = ‖x i-x j‖ := by
  classical
  have hp0 : 0 < p := by linarith
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let i₀ : Fin n := ⟨0, by omega⟩
  let j₀ : Fin n := ⟨1, by omega⟩
  let e₀ : PairIndex n := ⟨(i₀,j₀), by change (0:ℕ) < 1; omega⟩
  let q : Ω → PairIndex n → ℝ := fun t => pairPower p (fun i => x i t)
  have hqi : Integrable q μ := integrable_pi_iff.mpr (fun e =>
    lpDifference_integrable p hp0 (x e.val.1) (x e.val.2))
  have hqe (e : PairIndex n) : (∫ t, q t e ∂μ) = ‖x e.val.1-x e.val.2‖^p :=
    lpDifference_integral p hp0 _ _
  let S := ∫ t, ∑ e, q t e ∂μ
  have hsum : S = ∑ e : PairIndex n, ‖x e.val.1-x e.val.2‖^p := by
    rw [show S = ∫ t, ∑ e, q t e ∂μ from rfl, integral_finsetSum]
    · exact Finset.sum_congr rfl (fun e _ => hqe e)
    · intro e _; exact integrable_pi_iff.mp hqi e
  have hS : 0 < S := by
    rw [hsum]
    apply Finset.sum_pos'
    · intro e _; positivity
    · refine ⟨e₀, Finset.mem_univ _, Real.rpow_pos_of_pos (norm_pos_iff.mpr ?_) p⟩
      apply sub_ne_zero.mpr
      apply hx.ne
      intro he; have := congrArg Fin.val he; change (0:ℕ) = 1 at this; omega
  have hq : ∀ᵐ t ∂μ, q t = 0 ∨ (0 < ∑ e, q t e ∧ (∑ e, q t e)⁻¹ • q t ∈ normalizedPowers p i₀) := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : ∑ e, q t e = 0
    · left
      ext e
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => pairPower_nonneg p _ e)).mp ht e (Finset.mem_univ e)
    · right
      have htpos : 0 < ∑ e, q t e := lt_of_le_of_ne
        (Finset.sum_nonneg (fun e _ => pairPower_nonneg p _ e)) (Ne.symm ht)
      exact ⟨htpos, pairPower_normalize p hp0 i₀ _ htpos⟩
  have hmem := normalized_integral_mem μ (normalizedPowers_compact p hp0 i₀)
    (fun z hz => normalizedPowers_sum p i₀ hz) q hqi hq hS
  obtain ⟨k,hk,v,w,hv,hw,hws,hvw⟩ := hyperplane_convex_representation
    (fun z hz => normalizedPowers_sum p i₀ hz) hmem
  choose z hz hpz using hv
  let y : Fin n → Fin k → ℝ := fun i a => (S*w a)^(1/p)*z a i
  have hyp (e : PairIndex n) : (∑ a, |y e.val.1 a-y e.val.2 a|^p) = ‖x e.val.1-x e.val.2‖^p := by
    have hwe (a : Fin k) : |y e.val.1 a-y e.val.2 a|^p = S*w a*v a e := by
      have hsw : 0 ≤ S*w a := mul_nonneg hS.le (hw a)
      have ha : 0 ≤ (S*w a)^(1/p) := Real.rpow_nonneg hsw _
      dsimp [y]
      rw [← mul_sub, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), abs_of_nonneg ha,
        one_div, Real.rpow_inv_rpow hsw hp0.ne']
      rw [← hpz a]
      rfl
    simp_rw [hwe]
    have he := congrFun hvw e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
    have hei : (∫ t, q t ∂μ) e = ∫ t, q t e ∂μ :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PairIndex n => ℝ) e).integral_comp_comm hqi).symm
    rw [hei] at he
    rw [hqe] at he
    calc
      ∑ a, S*w a*v a e = S*∑ a, w a*v a e := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ = S*(S⁻¹*‖x e.val.1-x e.val.2‖^p) := by rw [he]
      _ = _ := by rw [mul_inv_cancel_left₀ hS.ne']
  have hyy (i j : Fin n) : (∑ a, |y i a-y j a|^p) = ‖x i-x j‖^p := by
    rcases lt_trichotomy i j with h | h | h
    · exact hyp ⟨(i,j),h⟩
    · subst j; simp [Real.zero_rpow hp0.ne']
    · simpa only [abs_sub_comm, norm_sub_rev] using hyp ⟨(j,i),h⟩
  rw [pairIndex_card] at hk
  obtain ⟨Y,hY⟩ := pad_coordinates p hp0 hk y
  refine ⟨Y, ?_⟩
  intro i j
  unfold coordinateDistance
  rw [hY, hyy, one_div, Real.rpow_rpow_inv (norm_nonneg _) hp0.ne']

lemma exact_discretization (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n)
    {Ω : Type uΩ} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Fin n → Lp ℝ (ENNReal.ofReal p) μ) (hx : Function.Injective x) :
    ∃ y : Fin n → Fin (n.choose 2) → ℝ, ∀ i j,
      coordinateDistance p (y i) (y j) = ‖x i-x j‖ :=
  exact_discretization_ge_one p hp.le n hn μ x hx

end SubpolynomialLp

end

end OAI
