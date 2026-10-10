import Mathlib
import OAI.Analysis.MumfordShah.Poincare
import OAI.Analysis.MumfordShah.GradientProjection

namespace OAI

/-! MumfordShah local potential. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff
open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff

lemma lp_norm_sq_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    (v : Lp E 2 μ) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

def unitMean (u : ℂ → ℝ) : ℝ := (∫ x in complexSquare 1, u x) / 4

def normalizedPotential (u : ℂ → ℝ) (x : ℂ) : ℝ := u x - unitMean u

lemma memLp_normalizedPotential {u : ℂ → ℝ} (hu : Continuous u) (R : ℝ) :
    MemLp (normalizedPotential u) 2 (volume.restrict (complexSquare R)) := by
  have h : Continuous (normalizedPotential u) := hu.sub continuous_const
  exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mpr
    ((h.pow 2).continuousOn.integrableOn_compact (isCompact_complexSquare R))

def smoothPotentialLp {u : ℂ → ℝ} (hu : Continuous u) (R : ℝ) :
    Lp ℝ 2 (volume.restrict (complexSquare R)) :=
  (memLp_normalizedPotential hu R).toLp (normalizedPotential u)

lemma normalizedPotential_sub {u v : ℂ → ℝ} (hu : Continuous u) (hv : Continuous v) :
    normalizedPotential (u - v) = normalizedPotential u - normalizedPotential v := by
  funext x
  dsimp [normalizedPotential, unitMean]
  rw [integral_sub (hu.continuousOn.integrableOn_compact (isCompact_complexSquare 1))
    (hv.continuousOn.integrableOn_compact (isCompact_complexSquare 1))]
  ring

lemma smoothPotentialLp_sub {u v : ℂ → ℝ} (hu : Continuous u) (hv : Continuous v) (R : ℝ) :
    smoothPotentialLp (hu.sub hv) R = smoothPotentialLp hu R - smoothPotentialLp hv R := by
  apply Lp.ext
  filter_upwards [(memLp_normalizedPotential (hu.sub hv) R).coeFn_toLp,
    (memLp_normalizedPotential hu R).coeFn_toLp,
    (memLp_normalizedPotential hv R).coeFn_toLp,
    Lp.coeFn_sub (smoothPotentialLp hu R) (smoothPotentialLp hv R)] with x hx hux hvx hsub
  change smoothPotentialLp (hu.sub hv) R x = _ at hx
  change smoothPotentialLp hu R x = _ at hux
  change smoothPotentialLp hv R x = _ at hvx
  rw [hx, hsub, Pi.sub_apply, hux, hvx, normalizedPotential_sub hu hv]
  rfl

lemma smoothPotentialLp_sq_bound {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u)
    {v : PlaneL2} (hv : (v : ℂ → ℂ) =ᵐ[volume] gradient u)
    {R : ℝ} (hR : 1 ≤ R) :
    ‖smoothPotentialLp hu.continuous R‖ ^ 2 ≤ (32 * R ^ 2 + 32 * R ^ 3) * ‖v‖ ^ 2 := by
  rw [lp_norm_sq_integral]
  have hleft : (∫ x in complexSquare R, ‖smoothPotentialLp hu.continuous R x‖ ^ 2) =
      ∫ x in complexSquare R, (normalizedPotential u x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [(memLp_normalizedPotential hu.continuous R).coeFn_toLp] with x hx
    change smoothPotentialLp hu.continuous R x = _ at hx
    rw [hx, Real.norm_eq_abs, sq_abs]
  rw [hleft]
  have hP := unitmean_poincare_complexSquare (hu.of_le (by simp)) hR
  change (∫ x in complexSquare R, normalizedPotential u x ^ 2) ≤ _ at hP
  refine hP.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [lp_norm_sq_integral]
  have hgrad : (∫ x in complexSquare R, ‖gradient u x‖ ^ 2) =
      ∫ x in complexSquare R, ‖v x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hv] with x hx
    rw [hx]
  rw [hgrad]
  exact setIntegral_le_integral ((Lp.memLp v).integrable_norm_pow (by norm_num)) (Filter.Eventually.of_forall (fun x => sq_nonneg _)) 

lemma smoothPotentialLp_bound {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u)
    {v : PlaneL2} (hv : (v : ℂ → ℂ) =ᵐ[volume] gradient u)
    {R : ℝ} (hR : 1 ≤ R) :
    ‖smoothPotentialLp hu.continuous R‖ ≤ (32 * R ^ 2 + 32 * R ^ 3) * ‖v‖ := by
  have h := smoothPotentialLp_sq_bound hu hv hR
  have hc : 1 ≤ 32 * R ^ 2 + 32 * R ^ 3 := by nlinarith [sq_nonneg (R - 1)]
  set C := 32 * R ^ 2 + 32 * R ^ 3
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith : 0 ≤ C) (norm_nonneg _))).mp
  calc
    ‖smoothPotentialLp hu.continuous R‖ ^ 2 ≤ C * ‖v‖ ^ 2 := h
    _ ≤ C ^ 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    _ = (C * ‖v‖) ^ 2 := by ring

lemma gradient_sub_smooth {u v : ℂ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    gradient (u - v) = gradient u - gradient v := by
  funext x
  simp only [gradient, fderiv_sub (hu.differentiable (by norm_num) x)
    (hv.differentiable (by norm_num) x), map_sub, Pi.sub_apply]

lemma smoothPotentialLp_dist_bound {u v : ℂ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    {q r : PlaneL2} (hq : (q : ℂ → ℂ) =ᵐ[volume] gradient u)
    (hr : (r : ℂ → ℂ) =ᵐ[volume] gradient v)
    {R : ℝ} (hR : 1 ≤ R) :
    dist (smoothPotentialLp hu.continuous R) (smoothPotentialLp hv.continuous R) ≤
      (32 * R ^ 2 + 32 * R ^ 3) * dist q r := by
  rw [dist_eq_norm, ← smoothPotentialLp_sub hu.continuous hv.continuous R, dist_eq_norm]
  apply smoothPotentialLp_bound (hu.sub hv) _ hR
  filter_upwards [Lp.coeFn_sub q r, hq, hr] with x hsub hqx hrx
  rw [hsub, Pi.sub_apply, hqx, hrx]
  change _ = gradient (u - v) x
  rw [gradient_sub_smooth hu hv]
  rfl

lemma cauchySeq_smoothPotentialLp {u : ℕ → ℂ → ℝ}
    (hu : ∀ k, ContDiff ℝ ∞ (u k))
    {q : ℕ → PlaneL2} (hq : ∀ k, (q k : ℂ → ℂ) =ᵐ[volume] gradient (u k))
    (hc : CauchySeq q) {R : ℝ} (hR : 1 ≤ R) :
    CauchySeq (fun k => smoothPotentialLp (hu k).continuous R) := by
  have hC : 0 < 32 * R ^ 2 + 32 * R ^ 3 := by positivity
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε / (32 * R ^ 2 + 32 * R ^ 3))
    (div_pos hε hC)
  refine ⟨N, fun i hi j hj => ?_⟩
  have hb := smoothPotentialLp_dist_bound (hu i) (hu j) (hq i) (hq j) hR
  exact hb.trans_lt ((mul_lt_mul_of_pos_left (hN i hi j hj) hC).trans_eq
    (mul_div_cancel₀ ε (ne_of_gt hC)))

lemma gradient_closure_approximation {w : PlaneL2} (hw : w ∈ compactGradientClosure) :
    ∃ (u : ℕ → ℂ → ℝ) (q : ℕ → PlaneL2),
      (∀ k, ContDiff ℝ ∞ (u k)) ∧ (∀ k, HasCompactSupport (u k)) ∧
      (∀ k, (q k : ℂ → ℂ) =ᵐ[volume] gradient (u k)) ∧ Tendsto q atTop (𝓝 w) := by
  change w ∈ closure (smoothGradientSpace : Set PlaneL2) at hw
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp hw
  change ∀ k, ∃ u : ℂ → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
    (q k : ℂ → ℂ) =ᵐ[volume] gradient u at hq
  choose u hu huc hgrad using hq
  exact ⟨u, q, hu, huc, hgrad, hlim⟩

lemma exists_localLp_limit_of_gradient_limit {u : ℕ → ℂ → ℝ}
    (hu : ∀ k, ContDiff ℝ ∞ (u k))
    {q : ℕ → PlaneL2} (hq : ∀ k, (q k : ℂ → ℂ) =ᵐ[volume] gradient (u k))
    {w : PlaneL2} (hlim : Tendsto q atTop (𝓝 w)) {R : ℝ} (hR : 1 ≤ R) :
    ∃ U : Lp ℝ 2 (volume.restrict (complexSquare R)),
      Tendsto (fun k => smoothPotentialLp (hu k).continuous R) atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete (cauchySeq_smoothPotentialLp hu hq hlim.cauchySeq hR)

def restrictLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S T : Set ℂ} (hST : S ⊆ T) :
    Lp E 2 (volume.restrict T) →L[ℝ] Lp E 2 (volume.restrict S) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_mono hST (le_refl volume))

lemma restrictLp_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S T : Set ℂ} (hST : S ⊆ T) (U : Lp E 2 (volume.restrict T)) :
    (restrictLp hST U : ℂ → E) =ᵐ[volume.restrict S] U :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

lemma complexSquare_mono {R S : ℝ} (hRS : R ≤ S) : complexSquare R ⊆ complexSquare S :=
  preimage_mono (Set.prod_mono (Icc_subset_Icc (neg_le_neg hRS) hRS)
    (Icc_subset_Icc (neg_le_neg hRS) hRS))

lemma restrict_smoothPotentialLp {u : ℂ → ℝ} (hu : Continuous u)
    {R S : ℝ} (hRS : R ≤ S) :
    restrictLp (complexSquare_mono hRS) (smoothPotentialLp hu S) = smoothPotentialLp hu R := by
  apply Lp.ext
  have hle := Measure.restrict_mono (complexSquare_mono hRS) (le_refl volume)
  filter_upwards [restrictLp_ae (complexSquare_mono hRS) (smoothPotentialLp hu S),
    ae_mono hle (memLp_normalizedPotential hu S).coeFn_toLp,
    (memLp_normalizedPotential hu R).coeFn_toLp] with x hx hS hR
  exact hx.trans (hS.trans hR.symm)

lemma localLp_limits_compatible {u : ℕ → ℂ → ℝ} (hu : ∀ k, Continuous (u k))
    {R S : ℝ} (hRS : R ≤ S)
    {U : Lp ℝ 2 (volume.restrict (complexSquare R))}
    {V : Lp ℝ 2 (volume.restrict (complexSquare S))}
    (hU : Tendsto (fun k => smoothPotentialLp (hu k) R) atTop (𝓝 U))
    (hV : Tendsto (fun k => smoothPotentialLp (hu k) S) atTop (𝓝 V)) :
    restrictLp (complexSquare_mono hRS) V = U := by
  have hlim := ((restrictLp (complexSquare_mono hRS)).continuous.tendsto V).comp hV
  have heq : (fun k => restrictLp (complexSquare_mono hRS) (smoothPotentialLp (hu k) S)) =
      (fun k => smoothPotentialLp (hu k) R) := by
    funext k
    exact restrict_smoothPotentialLp (hu k) hRS
  change Tendsto (fun k => restrictLp (complexSquare_mono hRS) (smoothPotentialLp (hu k) S)) atTop _ at hlim
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim hU

lemma mem_complexSquare_of_norm_le {z : ℂ} {R : ℝ} (h : ‖z‖ ≤ R) :
    z ∈ complexSquare R := by
  change z.re ∈ Icc (-R) R ∧ z.im ∈ Icc (-R) R
  exact ⟨abs_le.mp (z.abs_re_le_norm.trans h), abs_le.mp (z.abs_im_le_norm.trans h)⟩

lemma complexSquare_nat_cover (z : ℂ) : ∃ n : ℕ, z ∈ complexSquare (n + 1 : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  exact ⟨n, mem_complexSquare_of_norm_le (by linarith)⟩

lemma bounded_subset_complexSquare {S : Set ℂ} (hS : Bornology.IsBounded S) :
    ∃ n : ℕ, S ⊆ complexSquare (n + 1 : ℝ) := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt R
  refine ⟨n, fun z hz => mem_complexSquare_of_norm_le ?_⟩
  have hg := hR hz
  rw [mem_closedBall, dist_zero_right] at hg
  linarith

lemma glue_localLp
    (U : ∀ n : ℕ, Lp ℝ 2 (volume.restrict (complexSquare (n + 1 : ℝ))))
    (hU : ∀ n m (h : n ≤ m),
      restrictLp (complexSquare_mono (by exact_mod_cast Nat.add_le_add_right h 1)) (U m) = U n) :
    ∃ φ : ℂ → ℝ, ∀ n : ℕ,
      φ =ᵐ[volume.restrict (complexSquare (n + 1 : ℝ))] U n := by
  classical
  let k : ℂ → ℕ := fun z => Nat.find (complexSquare_nat_cover z)
  have hk (z : ℂ) : z ∈ complexSquare (k z + 1 : ℝ) := Nat.find_spec (complexSquare_nat_cover z)
  let φ : ℂ → ℝ := fun z => U (k z) z
  have hc : ∀ n m : ℕ, ∀ᵐ z ∂volume,
      z ∈ complexSquare (n + 1 : ℝ) → n ≤ m → U m z = U n z := by
    intro n m
    by_cases hnm : n ≤ m
    · have hae := restrictLp_ae
        (complexSquare_mono (R := (n : ℝ) + 1) (S := (m : ℝ) + 1)
          (by exact_mod_cast Nat.add_le_add_right hnm 1)) (U m)
      rw [hU n m hnm] at hae
      have hh := (ae_restrict_iff' (isCompact_complexSquare (n + 1 : ℝ)).measurableSet).mp hae.symm
      filter_upwards [hh] with z hz
      exact fun hzn _ => hz hzn
    · exact Eventually.of_forall (fun _ _ h => False.elim (hnm h))
  have hall : ∀ᵐ z ∂volume, ∀ n m : ℕ,
      z ∈ complexSquare (n + 1 : ℝ) → n ≤ m → U m z = U n z :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (hc n))
  refine ⟨φ, fun n => ?_⟩
  filter_upwards [ae_restrict_of_ae hall,
    ae_restrict_mem (isCompact_complexSquare (n + 1 : ℝ)).measurableSet] with z hz hzn
  change U (k z) z = U n z
  rcases le_total (k z) n with hkn | hnk
  · exact (hz (k z) n (hk z) hkn).symm
  · exact hz n (k z) hzn hnk

lemma continuous_test_deriv {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (a : ℂ) :
    Continuous (fun x => fderiv ℝ ψ x a) :=
  (hψ.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)

lemma smooth_normalized_ibp {u ψ : ℂ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {S : Set ℂ} (hS : tsupport ψ ⊆ S) (a : ℂ) :
    (∫ x in S, normalizedPotential u x * fderiv ℝ ψ x a) =
      -(∫ x : ℂ, inner ℝ (gradient u x) a * ψ x) := by
  have hun : ContDiff ℝ ∞ (normalizedPotential u) := hu.sub contDiff_const
  have hdun : Continuous (fun x => fderiv ℝ (normalizedPotential u) x a) :=
    continuous_test_deriv hun a
  have hdψ := continuous_test_deriv hψ a
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hn : x ∉ tsupport ψ := fun hc => hx (hS hc)
    rw [fderiv_of_notMem_tsupport ℝ hn]
    simp)]
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := normalizedPotential u) (g := ψ) (v := a)
    ((hdun.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
    ((hun.continuous.mul hdψ).integrable_of_hasCompactSupport (hψc.fderiv_apply ℝ a).mul_left)
    ((hun.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left)
    (fun x _ => hun.differentiable (by norm_num) x)
    (fun x _ => hψ.differentiable (by norm_num) x)
  rw [hi]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [inner_gradient_left]
  have hd : fderiv ℝ (normalizedPotential u) x = fderiv ℝ u x := by
    change fderiv ℝ (fun z => u z - unitMean u) x = _
    exact fderiv_sub_const (unitMean u)
  rw [hd]

lemma memLp_test_deriv {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (a : ℂ) :
    MemLp (fun x => fderiv ℝ ψ x a) 2 (volume : Measure ℂ) :=
  (continuous_test_deriv hψ a).memLp_of_hasCompactSupport (hψc.fderiv_apply ℝ a)

lemma memLp_test_vector {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (a : ℂ) :
    MemLp (fun x => ψ x • a) 2 (volume : Measure ℂ) :=
  (hψ.smul continuous_const).memLp_of_hasCompactSupport hψc.smul_right

lemma lp_inner_real_test {μ : Measure ℂ} (U : Lp ℝ 2 μ) {d : ℂ → ℝ}
    (hd : MemLp d 2 μ) :
    inner ℝ U (hd.toLp d) = ∫ x, U x * d x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hd.coeFn_toLp] with x hx
  rw [hx]
  simp [mul_comm]

lemma lp_inner_vector_test (q : PlaneL2) {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (a : ℂ) :
    inner ℝ q ((memLp_test_vector hψ hψc a).toLp (fun x => ψ x • a)) =
      ∫ x : ℂ, inner ℝ (q x) a * ψ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_test_vector hψ hψc a).coeFn_toLp] with x hx
  rw [hx, inner_smul_right]
  simp [mul_comm]

lemma localLp_limit_weak_gradient {u : ℕ → ℂ → ℝ}
    (hu : ∀ k, ContDiff ℝ ∞ (u k))
    {q : ℕ → PlaneL2} (hq : ∀ k, (q k : ℂ → ℂ) =ᵐ[volume] gradient (u k))
    {w : PlaneL2} (hw : Tendsto q atTop (𝓝 w)) {R : ℝ}
    {U : Lp ℝ 2 (volume.restrict (complexSquare R))}
    (hU : Tendsto (fun k => smoothPotentialLp (hu k).continuous R) atTop (𝓝 U))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψR : tsupport ψ ⊆ complexSquare R) (a : ℂ) :
    (∫ x in complexSquare R, U x * fderiv ℝ ψ x a) =
      -(∫ x : ℂ, inner ℝ (w x) a * ψ x) := by
  let d := fun x => fderiv ℝ ψ x a
  have hd : MemLp d 2 (volume.restrict (complexSquare R)) :=
    (memLp_test_deriv hψ hψc a).restrict _
  let D := hd.toLp d
  let T := (memLp_test_vector hψ.continuous hψc a).toLp (fun x => ψ x • a)
  have hleft : Tendsto (fun k => inner ℝ (smoothPotentialLp (hu k).continuous R) D)
      atTop (𝓝 (inner ℝ U D)) := hU.inner tendsto_const_nhds
  have hright : Tendsto (fun k => -(inner ℝ (q k) T)) atTop (𝓝 (-(inner ℝ w T))) :=
    (hw.inner tendsto_const_nhds).neg
  have hid : (fun k => inner ℝ (smoothPotentialLp (hu k).continuous R) D) =
      (fun k => -(inner ℝ (q k) T)) := by
    funext k
    rw [lp_inner_real_test, lp_inner_vector_test _ hψ.continuous hψc a]
    have hqk : (∫ x : ℂ, inner ℝ (q k x) a * ψ x) =
        ∫ x : ℂ, inner ℝ (gradient (u k) x) a * ψ x :=
      by
        apply integral_congr_ae
        filter_upwards [hq k] with x hx
        rw [hx]
    rw [hqk]
    have hp : (∫ x in complexSquare R, smoothPotentialLp (hu k).continuous R x * d x) =
        ∫ x in complexSquare R, normalizedPotential (u k) x * d x := by
      apply integral_congr_ae
      filter_upwards [(memLp_normalizedPotential (hu k).continuous R).coeFn_toLp] with x hx
      change smoothPotentialLp (hu k).continuous R x = _ at hx
      rw [hx]
    rw [hp]
    exact smooth_normalized_ibp (hu k) hψ hψc hψR a
  rw [hid] at hleft
  have heq := tendsto_nhds_unique hleft hright
  rw [lp_inner_real_test, lp_inner_vector_test _ hψ.continuous hψc a] at heq
  exact heq

theorem gradient_closure_has_local_potential {w : PlaneL2}
    (hw : w ∈ compactGradientClosure) :
    ∃ φ : ℂ → ℝ, ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
      SobolevOn φ w S := by
  obtain ⟨u, q, hu, _huc, hq, hlim⟩ := gradient_closure_approximation hw
  have hex : ∀ n : ℕ, ∃ U : Lp ℝ 2 (volume.restrict (complexSquare (n + 1 : ℝ))),
      Tendsto (fun k => smoothPotentialLp (hu k).continuous (n + 1 : ℝ)) atTop (𝓝 U) :=
    fun n => exists_localLp_limit_of_gradient_limit hu hq hlim (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  choose U hU using hex
  have hcompat : ∀ n m (h : n ≤ m),
      restrictLp (complexSquare_mono (by exact_mod_cast Nat.add_le_add_right h 1)) (U m) = U n := by
    intro n m hnm
    exact localLp_limits_compatible (fun k => (hu k).continuous)
      (by exact_mod_cast Nat.add_le_add_right hnm 1) (hU n) (hU m)
  obtain ⟨φ, hφ⟩ := glue_localLp U hcompat
  refine ⟨φ, fun S _hSo hSb => ?_⟩
  obtain ⟨n, hn⟩ := bounded_subset_complexSquare hSb
  have hφLp : MemLp φ 2 (volume.restrict (complexSquare (n + 1 : ℝ))) :=
    (memLp_congr_ae (hφ n)).mpr (Lp.memLp (U n))
  refine ⟨hφLp.mono_measure (Measure.restrict_mono hn (le_refl volume)),
    (Lp.memLp w).restrict S, ?_⟩
  intro ψ hψ hψc hψS a
  have hψR : tsupport ψ ⊆ complexSquare (n + 1 : ℝ) := hψS.trans hn
  have hd0 (T : Set ℂ) (hT : tsupport ψ ⊆ T) :
      ∀ x, x ∉ T → φ x * fderiv ℝ ψ x a = 0 := by
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hT h))]
    simp
  calc
    (∫ x in S, φ x * fderiv ℝ ψ x a) = ∫ x : ℂ, φ x * fderiv ℝ ψ x a :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (hd0 S hψS)
    _ = ∫ x in complexSquare (n + 1 : ℝ), φ x * fderiv ℝ ψ x a :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (hd0 _ hψR)).symm
    _ = ∫ x in complexSquare (n + 1 : ℝ), U n x * fderiv ℝ ψ x a := by
      apply integral_congr_ae
      filter_upwards [hφ n] with x hx
      rw [hx]
    _ = -(∫ x : ℂ, inner ℝ (w x) a * ψ x) :=
      localLp_limit_weak_gradient hu hq hlim (hU n) hψ hψc hψR a
    _ = -(∫ x in S, inner ℝ (w x) a * ψ x) := by
      congr 1
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψS h)), mul_zero]

end MumfordShah
end

end OAI
