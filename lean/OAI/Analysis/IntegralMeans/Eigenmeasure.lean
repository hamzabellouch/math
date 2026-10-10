import OAI.Analysis.IntegralMeans.TransferOperator

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

lemma positive_operator_mono.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) : Monotone L := by
  intro f g h
  have := hp (g-f) (sub_nonneg.mpr h)
  simpa only [map_sub,sub_nonneg] using this

lemma positive_operator_abs_bound.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) (f : C(X,ℝ)) (x : X) :
    |L f x| ≤ ‖f‖ * L 1 x := by
  have hlo : (-‖f‖) • (1 : C(X,ℝ)) ≤ f := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).1
  have hhi : f ≤ ‖f‖ • (1 : C(X,ℝ)) := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).2
  have h1 := positive_operator_mono L hp hlo x
  have h2 := positive_operator_mono L hp hhi x
  simp only [map_smul,ContinuousMap.toFun_eq_coe,ContinuousMap.smul_apply,smul_eq_mul,neg_mul] at h1 h2
  exact abs_le.mpr ⟨h1,h2⟩

lemma positive_operator_norm.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) : ‖L‖ = ‖L 1‖ := by
  apply le_antisymm
  · apply L.opNorm_le_bound (norm_nonneg _)
    intro f
    apply (ContinuousMap.norm_le (L f) (by positivity)).mpr
    intro x
    calc
      ‖L f x‖ = |L f x| := Real.norm_eq_abs _
      _ ≤ ‖f‖ * L 1 x := positive_operator_abs_bound L hp f x
      _ ≤ ‖f‖ * ‖L 1‖ := mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self _) (ContinuousMap.norm_coe_le_norm (L 1) x)) (norm_nonneg _)
      _ = ‖L 1‖ * ‖f‖ := mul_comm _ _
  · simpa using L.le_opNorm (1 : C(X,ℝ))

lemma positive_operator_pow.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) (n : ℕ) :
    ∀ f, 0 ≤ f → 0 ≤ (L^n) f := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro f hf
    simpa only [pow_succ',mul_apply_eq_comp] using hp ((L^n) f) (ih f hf)

lemma log_norm_pow_subadditive.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : Subadditive (fun n => Real.log ‖a^n‖) := by
  intro m n
  change Real.log ‖a^(m+n)‖ ≤ _
  rw [pow_add]
  calc
    Real.log ‖a^m*a^n‖ ≤ Real.log (‖a^m‖*‖a^n‖) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (by simpa [pow_add] using h (m+n))) (norm_mul_le _ _)
    _ = Real.log ‖a^m‖ + Real.log ‖a^n‖ := Real.log_mul (by linarith [h m]) (by linarith [h n])

lemma log_norm_pow_bddBelow.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : BddBelow (range (fun n : ℕ => Real.log ‖a^n‖/n)) := by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  exact div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n)

def growthLog.{u_1} {A : Type u_1} [NormedRing A] (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : ℝ :=
  (log_norm_pow_subadditive a h).lim

def growthRate.{u_1} {A : Type u_1} [NormedRing A] (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : ℝ :=
  Real.exp (growthLog a h)

lemma tendsto_log_norm_pow.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) :
    Tendsto (fun n : ℕ => Real.log ‖a^n‖/n) atTop (𝓝 (growthLog a h)) :=
  (log_norm_pow_subadditive a h).tendsto_lim (log_norm_pow_bddBelow a h)

lemma growthLog_nonneg.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : 0 ≤ growthLog a h :=
  ge_of_tendsto (tendsto_log_norm_pow a h)
    (Eventually.of_forall (fun n => div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n)))

lemma growthRate_ge_one.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : 1 ≤ growthRate a h :=
  Real.one_le_exp_iff.mpr (growthLog_nonneg a h)

lemma norm_pow_eventually_le.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) {r : ℝ} (hr : growthRate a h < r) :
    ∀ᶠ n : ℕ in atTop, ‖a^n‖ ≤ r^n := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one a h).trans hr.le)
  have hlog : growthLog a h < Real.log r := by
    rwa [← Real.exp_lt_exp,Real.exp_log hr0]
  filter_upwards [(tendsto_log_norm_pow a h).eventually (gt_mem_nhds hlog),
    eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have he : Real.log ‖a^n‖ ≤ (n : ℝ)*Real.log r := by
    have := (div_lt_iff₀ hnR).mp hn
    linarith
  have := Real.exp_le_exp.mpr he
  simpa only [Real.exp_log (lt_of_lt_of_le zero_lt_one (h n)),Real.exp_nat_mul,
    Real.exp_log hr0] using this

lemma summable_scaled_pow.{u_1} {A : Type u_1} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) {τ : ℝ} (hτ : growthRate a h < τ) :
    Summable (fun n : ℕ => (τ⁻¹)^n • a^n) := by
  obtain ⟨r,hr,hrτ⟩ := exists_between hτ
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one a h).trans hr.le)
  have hτ0 : 0 < τ := hr0.trans hrτ
  apply Summable.of_norm_bounded_eventually (g := fun n : ℕ => (r/τ)^n)
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hτ0).mpr hrτ))
  have he := norm_pow_eventually_le a h hr
  rw [← Nat.cofinite_eq_atTop] at he
  filter_upwards [he] with n hn
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (τ⁻¹)^n)]
  calc
    (τ⁻¹)^n * ‖a^n‖ ≤ (τ⁻¹)^n*r^n := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (r/τ)^n := by rw [← mul_pow]; congr 1; ring

lemma growthRate_le_of_pow_bound.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) {M c : ℝ} (hM : 0 < M) (_hc : 0 ≤ c)
    (hb : ∀ n : ℕ, ‖a^n‖ ≤ M*c^n) : growthRate a h ≤ c := by
  have hc0 : 0 < c := by
    have := hb 1
    have := h 1
    simp only [pow_one] at *
    nlinarith
  have ht : Tendsto (fun n : ℕ => Real.log M/(n : ℝ)+Real.log c) atTop (𝓝 (Real.log c)) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const (Real.log c)
  have hl : growthLog a h ≤ Real.log c := by
    apply le_of_tendsto_of_tendsto (tendsto_log_norm_pow a h) ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one (h n)) (hb n)
    rw [Real.log_mul hM.ne' (pow_pos hc0 n).ne',Real.log_pow] at hlog
    calc
      Real.log ‖a^n‖/(n : ℝ) ≤ (Real.log M+(n : ℝ)*Real.log c)/(n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnR.le
      _ = Real.log M/(n : ℝ)+Real.log c := by field_simp
  simpa [growthRate,Real.exp_log hc0] using Real.exp_le_exp.mpr hl

def positiveResolvent.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (τ : ℝ) : C(X,ℝ) →L[ℝ] C(X,ℝ) :=
  ∑' n : ℕ, (τ⁻¹)^n • L^n

lemma positiveResolvent_apply.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (h : ∀ n : ℕ, 1 ≤ ‖L^n‖)
    {τ : ℝ} (hτ : growthRate L h < τ) (f : C(X,ℝ)) :
    positiveResolvent L τ f = ∑' n : ℕ, (τ⁻¹)^n • (L^n) f := by
  exact (ContinuousLinearMap.apply ℝ C(X,ℝ) f).map_tsum (summable_scaled_pow L h hτ)

lemma summable_resolvent_eval.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (h : ∀ n : ℕ, 1 ≤ ‖L^n‖)
    {τ : ℝ} (hτ : growthRate L h < τ) (f : C(X,ℝ)) (x : X) :
    Summable (fun n : ℕ => (τ⁻¹)^n * (L^n) f x) := by
  let e : (C(X,ℝ) →L[ℝ] C(X,ℝ)) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R := ℝ) x).comp (ContinuousLinearMap.apply ℝ C(X,ℝ) f)
  have hs := e.summable (summable_scaled_pow L h hτ)
  simpa only [e,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    smul_apply,ContinuousMap.evalCLM_apply,ContinuousMap.smul_apply,smul_eq_mul] using hs

lemma positiveResolvent_eval.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (h : ∀ n : ℕ, 1 ≤ ‖L^n‖)
    {τ : ℝ} (hτ : growthRate L h < τ) (f : C(X,ℝ)) (x : X) :
    positiveResolvent L τ f x = ∑' n : ℕ, (τ⁻¹)^n * (L^n) f x := by
  let e : (C(X,ℝ) →L[ℝ] C(X,ℝ)) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R := ℝ) x).comp (ContinuousLinearMap.apply ℝ C(X,ℝ) f)
  exact e.map_tsum (summable_scaled_pow L h hτ)

lemma positiveResolvent_nonneg.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) {τ : ℝ} (hτ : growthRate L h < τ) :
    ∀ f, 0 ≤ f → 0 ≤ positiveResolvent L τ f := by
  have ht : 0 < τ := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le)
  intro f hf x
  change 0 ≤ positiveResolvent L τ f x
  rw [positiveResolvent_eval L h hτ]
  exact tsum_nonneg (fun n => mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) n)
    (positive_operator_pow L hp n f hf x))

lemma positiveResolvent_ge_one.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) {τ : ℝ} (hτ : growthRate L h < τ) :
    1 ≤ positiveResolvent L τ 1 := by
  have ht : 0 < τ := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le)
  intro x
  change 1 ≤ positiveResolvent L τ 1 x
  rw [positiveResolvent_eval L h hτ]
  have hn (n : ℕ) : 0 ≤ (τ⁻¹)^n * (L^n) (1 : C(X,ℝ)) x :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) n) (positive_operator_pow L hp n 1 (by intro; simp) x)
  simpa using (summable_resolvent_eval L h hτ 1 x).le_tsum 0 (fun n _ => hn n)

lemma positiveResolvent_mul.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (h : ∀ n : ℕ, 1 ≤ ‖L^n‖)
    {τ : ℝ} (hτ : growthRate L h < τ) :
    positiveResolvent L τ * L = τ • (positiveResolvent L τ-1) ∧
    L * positiveResolvent L τ = τ • (positiveResolvent L τ-1) := by
  have ht : τ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le))
  have hs := summable_scaled_pow L h hτ
  have htail : ∑' n : ℕ, (τ⁻¹)^(n+1) • L^(n+1) = positiveResolvent L τ-1 := by
    have he := hs.sum_add_tsum_nat_add 1
    simpa [positiveResolvent] using eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he)
  have he (n : ℕ) : τ • ((τ⁻¹)^(n+1) • L^(n+1)) = (τ⁻¹)^n • (L^n*L) := by
    rw [smul_smul,pow_succ,pow_succ]
    congr 1
    field_simp
  constructor
  · change (∑' n : ℕ, (τ⁻¹)^n • L^n)*L = _
    rw [show (∑' n : ℕ, (τ⁻¹)^n • L^n)*L =
      ∑' n : ℕ, ((τ⁻¹)^n • L^n)*L from
      ((ContinuousLinearMap.compL ℝ C(X,ℝ) C(X,ℝ) C(X,ℝ)).flip L).map_tsum hs,
      ← htail,← tsum_const_smul'']
    exact tsum_congr (fun n => by
      rw [he]; change ((τ⁻¹)^n • L^n).comp L = (τ⁻¹)^n • ((L^n).comp L)
      exact ContinuousLinearMap.smul_comp _ _ _)
  · change L*(∑' n : ℕ, (τ⁻¹)^n • L^n) = _
    rw [show L*(∑' n : ℕ, (τ⁻¹)^n • L^n) =
      ∑' n : ℕ, L*((τ⁻¹)^n • L^n) from
      ((ContinuousLinearMap.compL ℝ C(X,ℝ) C(X,ℝ) C(X,ℝ)) L).map_tsum hs,
      ← htail,← tsum_const_smul'']
    apply tsum_congr
    intro n
    rw [he]
    change L.comp ((τ⁻¹)^n • L^n) = (τ⁻¹)^n • ((L^n).comp L)
    rw [ContinuousLinearMap.comp_smul]
    congr 1
    change L * L^n = L^n * L
    rw [← pow_succ',← pow_succ]

lemma positive_operator_pow_bound.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    {g : C(X,ℝ)} (hg : 1 ≤ g) {c : ℝ} (hc : 0 ≤ c) (hLg : L g ≤ c • g) (n : ℕ) :
    ‖L^n‖ ≤ ‖g‖*c^n := by
  have hiter : ∀ n : ℕ, (L^n) g ≤ c^n • g := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := positive_operator_mono L hp ih
      have h2 : c^n • L g ≤ c^n • (c • g) := smul_le_smul_of_nonneg_left hLg (pow_nonneg hc n)
      rw [map_smul] at h1
      have h3 := h1.trans h2
      simpa only [pow_succ',mul_apply_eq_comp,smul_smul,mul_comm] using h3
  rw [positive_operator_norm (L^n) (positive_operator_pow L hp n)]
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (pow_nonneg hc n))).mpr
  intro x
  have hn := positive_operator_pow L hp n 1 (by intro; simp) x
  have h1 := positive_operator_mono (L^n) (positive_operator_pow L hp n) hg x
  have h2 := hiter n x
  change (L^n) g x ≤ c^n*g x at h2
  calc
    ‖(L^n) 1 x‖ = (L^n) 1 x := Real.norm_of_nonneg hn
    _ ≤ c^n*g x := h1.trans h2
    _ ≤ c^n*‖g‖ := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x)) (pow_nonneg hc n)
    _ = ‖g‖*c^n := mul_comm _ _

lemma positiveResolvent_norm_bound.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) {τ : ℝ} (hτ : growthRate L h < τ) :
    1 ≤ ‖positiveResolvent L τ 1‖ ∧
    τ / ‖positiveResolvent L τ 1‖ ≤ τ - growthRate L h := by
  let g := positiveResolvent L τ 1
  have hg : 1 ≤ g := positiveResolvent_ge_one L hp h hτ
  have hM : 1 ≤ ‖g‖ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (hg x).trans ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x))
  have hM0 : 0 < ‖g‖ := zero_lt_one.trans_le hM
  have ht : 0 < τ := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le)
  let c := τ*(1-1/‖g‖)
  have hc : 0 ≤ c := mul_nonneg ht.le (sub_nonneg.mpr ((div_le_one hM0).mpr hM))
  have he : L g = τ • (g-1) := by
    have hv := congrArg (fun A : C(X,ℝ) →L[ℝ] C(X,ℝ) => A 1) (positiveResolvent_mul L h hτ).2
    simpa only [mul_apply_eq_comp,smul_apply,
      sub_apply,one_apply_eq_self] using hv
  have hLg : L g ≤ c • g := by
    rw [he]
    intro x
    change τ*(g x-1) ≤ c*g x
    have hgx : g x ≤ ‖g‖ := (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x)
    have hdiv : g x / ‖g‖ ≤ 1 := (div_le_one hM0).mpr hgx
    dsimp [c]
    have hh := mul_le_mul_of_nonneg_left hdiv ht.le
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    nlinarith
  have hr := growthRate_le_of_pow_bound L h hM0 hc (positive_operator_pow_bound L hp hg hc hLg)
  refine ⟨hM,?_⟩
  dsimp [c] at hr
  change τ/‖g‖ ≤ τ-growthRate L h
  simp only [div_eq_mul_inv,one_mul] at hr ⊢
  nlinarith

lemma probability_of_positive_functional.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (h1 : Λ 1 = 1) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X,ℝ), ∫ x, f x ∂(μ : Measure X) = Λ f := by
  let Λ' : C_c(X,ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => Λ f.toContinuousMap
      map_add' := fun f g => map_add Λ f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => map_smul Λ c f.toContinuousMap
      monotone' := by
        intro f g hfg
        have hn : 0 ≤ Λ (g.toContinuousMap-f.toContinuousMap) := hp _ (sub_nonneg.mpr hfg)
        simpa only [map_sub,sub_nonneg] using hn }
  let μ := RealRMK.rieszMeasure Λ'
  have hi (f : C(X,ℝ)) : ∫ x, f x ∂μ = Λ f := by
    let f' : C_c(X,ℝ) := ⟨f,HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure Λ' f'
  have hμ : IsProbabilityMeasure μ := isProbabilityMeasure_iff_real.mpr (by
    have hh := hi 1
    simpa [h1] using hh)
  exact ⟨⟨μ,hμ⟩,hi⟩

lemma exists_max_of_nonneg_continuous.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (f : C(X,ℝ)) (hf : 0 ≤ f) : ∃ x : X, f x = ‖f‖ := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.continuousOn
  refine ⟨x,le_antisymm ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm f x)) ?_⟩
  apply (ContinuousMap.norm_le f (hf x)).mpr
  intro y
  calc
    ‖f y‖ = f y := Real.norm_of_nonneg (hf y)
    _ ≤ f x := hx (mem_univ y)

lemma exists_resolvent_probability.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) {τ : ℝ} (hτ : growthRate L h < τ) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X,ℝ),
      |(∫ x, L f x ∂(μ : Measure X))-τ*(∫ x, f x ∂(μ : Measure X))| ≤
      (τ-growthRate L h)*‖f‖ := by
  let R := positiveResolvent L τ
  let g := R 1
  have hg : 1 ≤ g := positiveResolvent_ge_one L hp h hτ
  have hg0 : 0 ≤ g := le_trans (by intro; simp) hg
  obtain ⟨x,hx⟩ := exists_max_of_nonneg_continuous g hg0
  have hM := positiveResolvent_norm_bound L hp h hτ
  have hM0 : 0 < ‖g‖ := zero_lt_one.trans_le hM.1
  let Λ : C(X,ℝ) →L[ℝ] ℝ := (‖g‖⁻¹ • ContinuousMap.evalCLM (R := ℝ) x).comp R
  have hΛ (f : C(X,ℝ)) : Λ f = R f x / ‖g‖ := by change ‖g‖⁻¹ * R f x = R f x / ‖g‖; ring
  have hpΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f := by
    intro f hf
    rw [hΛ]
    exact div_nonneg (positiveResolvent_nonneg L hp h hτ f hf x) hM0.le
  have h1 : Λ 1 = 1 := by rw [hΛ]; change g x / ‖g‖ = 1; rw [hx,div_self hM0.ne']
  obtain ⟨μ,hμ⟩ := probability_of_positive_functional Λ hpΛ h1
  refine ⟨μ,fun f => ?_⟩
  rw [hμ (L f),hμ f,hΛ,hΛ]
  have he : R (L f) x = τ*(R f x-f x) := by
    have hv := congrArg (fun A : C(X,ℝ) →L[ℝ] C(X,ℝ) => A f x) (positiveResolvent_mul L h hτ).1
    exact hv
  rw [he]
  have hτ0 : 0 ≤ τ := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le) |>.le
  calc
    |τ*(R f x-f x)/‖g‖-τ*(R f x/‖g‖)| = (τ/‖g‖)*|f x| := by
      rw [show τ*(R f x-f x)/‖g‖-τ*(R f x/‖g‖) = -(τ/‖g‖)*f x by ring,
        abs_mul,abs_neg,abs_of_nonneg (div_nonneg hτ0 hM0.le)]
    _ ≤ (τ/‖g‖)*‖f‖ := mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f x)
      (div_nonneg hτ0 hM0.le)
    _ ≤ (τ-growthRate L h)*‖f‖ := mul_le_mul_of_nonneg_right hM.2 (norm_nonneg f)

lemma exists_growth_eigenmeasure.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X,ℝ),
      (∫ x, L f x ∂(μ : Measure X)) = growthRate L h*(∫ x, f x ∂(μ : Measure X)) := by
  let ρ := growthRate L h
  let τ : ℕ → ℝ := fun n => ρ+1/((n : ℝ)+1)
  have hτ (n : ℕ) : growthRate L h < τ n := by
    dsimp [τ,ρ]
    exact lt_add_of_pos_right _ (by positivity)
  choose μ hμ using fun n : ℕ => exists_resolvent_probability L hp h (hτ n)
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let V := U.map μ
  let ν := V.lim
  have hν : Tendsto μ (U : Filter ℕ) (𝓝 ν) := V.le_nhds_lim
  have ht : Tendsto τ (U : Filter ℕ) (𝓝 ρ) := by
    have hh : Tendsto τ atTop (𝓝 ρ) := by
      simpa [τ] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add ρ
    exact hh.mono_left (Ultrafilter.of_le atTop)
  refine ⟨ν,fun f => ?_⟩
  have hi := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto ν |>.comp hν
  have hLi := (ProbabilityMeasure.continuous_integral_continuousMap (L f)).tendsto ν |>.comp hν
  have hb := le_of_tendsto_of_tendsto ((hLi.sub (ht.mul hi)).abs)
    ((ht.sub_const ρ).mul_const ‖f‖) (Eventually.of_forall (hμ · f))
  simp only [sub_self,zero_mul] at hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)

lemma positive_functional_bound.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (Λ : C(X,ℝ) →ₗ[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(X,ℝ)) :
    ‖Λ f‖ ≤ Λ 1 * ‖f‖ := by
  have hlo : (-‖f‖) • (1 : C(X,ℝ)) ≤ f := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).1
  have hhi : f ≤ ‖f‖ • (1 : C(X,ℝ)) := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).2
  have h1 := hp (f-(-‖f‖) • 1) (sub_nonneg.mpr hlo)
  have h2 := hp (‖f‖ • 1-f) (sub_nonneg.mpr hhi)
  simp only [map_sub,map_smul,smul_eq_mul,neg_mul] at h1 h2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith

end Brennan

end

end OAI
