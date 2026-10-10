import Mathlib

namespace OAI

noncomputable section
namespace DeGiorgi
open MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def potential (t : ℝ) : ℝ := (1 - t ^ 2) ^ 2 / 4

def profile (s : ℝ) : ℝ := Real.tanh (s / Real.sqrt 2)

def surfaceTension : ℝ := 2 * Real.sqrt 2 / 3

def AllenCahn {n : ℕ} (v : Space n → ℝ) : Prop :=
  ∀ x, Laplacian.laplacian v x = v x ^ 3 - v x

def SecondVariation {n : ℕ} (v φ : Space n → ℝ) : ℝ :=
  ∫ x, (‖gradient φ x‖ ^ 2 + (3 * v x ^ 2 - 1) * φ x ^ 2)

def Stable {n : ℕ} (v : Space n → ℝ) : Prop :=
  ∀ φ : Space n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    0 ≤ SecondVariation v φ

def Energy {n : ℕ} (v : Space n → ℝ) (Ω : Set (Space n)) : ℝ :=
  ∫ x in Ω, (‖gradient v x‖ ^ 2 / 2 + potential (v x))

def unitBallVolume (m : ℕ) : ℝ :=
  volume.real (Metric.ball (0 : Space m) 1)

def density {n : ℕ} (v : Space n → ℝ) (R : ℝ) (y : Space n) : ℝ :=
  Energy v (Metric.ball y R) / (surfaceTension * unitBallVolume (n - 1) * R ^ (n - 1))

def densityAtInfinity {n : ℕ} (v : Space n → ℝ) : ℝ≥0∞ :=
  ⨆ R : { R : ℝ // 0 < R }, ENNReal.ofReal (density v R.val 0)

def Classified {n : ℕ} (v : Space n → ℝ) : Prop :=
  (∀ x, v x = 1) ∨ (∀ x, v x = -1) ∨
    ∃ (a : Space n) (b : ℝ), ‖a‖ = 1 ∧ ∀ x, v x = profile (inner ℝ a x - b)

def StableRigiditySeven : Prop :=
  ∀ v : Space 7 → ℝ, ContDiff ℝ 2 v →
    (∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) → AllenCahn v → Stable v → Classified v

def MonotoneRigidityEight : Prop :=
  ∀ u : Space 8 → ℝ, ContDiff ℝ 2 u →
    (∀ x, u x ∈ Set.Ioo (-1 : ℝ) 1) → AllenCahn u →
    (∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single (7 : Fin 8) 1)) →
    ∃ (e : Space 8) (c : ℝ), ‖e‖ = 1 ∧ 0 < e 7 ∧
      ∀ x, u x = profile (inner ℝ e x - c)

def FiniteDensityRigidity : Prop :=
  ∀ (n : ℕ), 4 ≤ n → n ≤ 7 →
    ∀ v : Space n → ℝ, ContDiff ℝ 2 v →
      (∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) → AllenCahn v → Stable v →
      densityAtInfinity v < ⊤ → Classified v

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open MeasureTheory
open scoped ENNReal
open Filter Topology

lemma second_deriv_nonneg_of_local_min {f : ℝ → ℝ} {x : ℝ}
    (hf : ContinuousAt f x) (hm : IsLocalMin f x) : 0 ≤ deriv (deriv f) x := by
  by_contra h
  have hn : deriv (deriv f) x < 0 := lt_of_not_ge h
  have hmax := isLocalMax_of_deriv_deriv_neg hn hm.deriv_eq_zero hf
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hm, hmax] with y hy hz using le_antisymm hz hy
  have hz := he.deriv.deriv_eq
  have hz0 : deriv (deriv f) x = 0 := by
    calc deriv (deriv f) x = deriv (deriv (fun _ : ℝ => f x)) x := hz
         _ = 0 := by simp
  linarith

def basis (n : ℕ) := EuclideanSpace.basisFun (Fin n) ℝ

def coordDeriv {n : ℕ} (f : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  fderiv ℝ f x (basis n i)

lemma coordDeriv_contDiff {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (i : Fin n) : ContDiff ℝ 1 (coordDeriv f i) := by
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma laplacian_eq_sum_coordDeriv {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Space n) :
    Laplacian.laplacian f x = ∑ i : Fin n, coordDeriv (coordDeriv f i) i x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (basis n)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDeriv_two_apply]
  change _ = fderiv ℝ (fun y => fderiv ℝ f y (basis n i)) x (basis n i)
  simp [fderiv_clm_apply
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
    (differentiableAt_const (c := basis n i))]

lemma deriv_line {n : ℕ} {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (x e : Space n) (t : ℝ) :
    deriv (fun s : ℝ => f (x + s • e)) t = fderiv ℝ f (x + t • e) e := by
  have hd : HasDerivAt (fun s : ℝ => x + s • e) e t := by
    simpa using (hasDerivAt_const t x).fun_add ((hasDerivAt_id t).smul_const e)
  exact ((hf _).hasFDerivAt.comp_hasDerivAt t hd).deriv

lemma laplacian_nonneg_of_local_min {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) {x : Space n} (hm : IsLocalMin f x) :
    0 ≤ Laplacian.laplacian f x := by
  rw [laplacian_eq_sum_coordDeriv hf]
  apply Finset.sum_nonneg
  intro i _
  let g : ℝ → ℝ := fun s => f (x + s • basis n i)
  have hg : ContinuousAt g 0 := hf.continuous.continuousAt.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hmin : IsLocalMin g 0 := by
    have ht : Tendsto (fun s : ℝ => x + s • basis n i) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun s : ℝ => x + s • basis n i) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa only [ContinuousAt, zero_smul, add_zero] using hc.continuousAt (x := 0)
    change ∀ᶠ s in 𝓝 (0 : ℝ), g 0 ≤ g s
    simpa [g] using ht.eventually hm
  have hder : deriv g = fun s => coordDeriv f i (x + s • basis n i) := by
    funext s
    exact deriv_line (hf.differentiable (by norm_num)) x (basis n i) s
  have hh := second_deriv_nonneg_of_local_min hg hmin
  rw [hder, deriv_line ((coordDeriv_contDiff hf i).differentiable (by norm_num))] at hh
  simpa [coordDeriv] using hh

lemma laplacian_nonpos_of_local_max {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) {x : Space n} (hm : IsLocalMax f x) :
    Laplacian.laplacian f x ≤ 0 := by
  have h := laplacian_nonneg_of_local_min hf.neg hm.neg
  change 0 ≤ Laplacian.laplacian (-f) x at h
  rw [InnerProductSpace.laplacian_neg] at h
  simpa using h

lemma coordDeriv_translate {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (a : Space n) (i : Fin n) (x : Space n) :
    coordDeriv (fun z => f (a + z)) i x = coordDeriv f i (a + x) := by
  dsimp [coordDeriv]
  have hd : HasFDerivAt (fun z => f (a + z)) (fderiv ℝ f (a + x)) x := by
    simpa only [Function.comp_def, zero_add, ContinuousLinearMap.comp_id, id_eq] using (hf (a + x)).hasFDerivAt.comp x
      ((hasFDerivAt_const a x).fun_add (hasFDerivAt_id x))
  rw [hd.fderiv]

lemma laplacian_translate {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (a x : Space n) :
    Laplacian.laplacian (fun z => f (a + z)) x = Laplacian.laplacian f (a + x) := by
  have hs : ContDiff ℝ 2 (fun z => f (a + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [laplacian_eq_sum_coordDeriv hs,
    laplacian_eq_sum_coordDeriv hf]
  apply Finset.sum_congr rfl
  intro i _
  have hfun : coordDeriv (fun z => f (a + z)) i = fun z => coordDeriv f i (a + z) :=
    funext (coordDeriv_translate (hf.differentiable (by norm_num)) a i)
  rw [hfun, coordDeriv_translate ((coordDeriv_contDiff hf i).differentiable (by norm_num))]

lemma laplacian_norm_sq {n : ℕ} (x : Space n) :
    Laplacian.laplacian (fun z : Space n => ‖z‖ ^ 2) x = 2 * n := by
  have hs : ContDiff ℝ 2 (fun z : Space n => ‖z‖ ^ 2) := contDiff_id.norm_sq ℝ
  rw [laplacian_eq_sum_coordDeriv hs]
  have hfirst (i : Fin n) : coordDeriv (fun z : Space n => ‖z‖ ^ 2) i =
      fun z => 2 * inner ℝ z (basis n i) := by
    funext z
    simp [coordDeriv]
  simp_rw [hfirst]
  have hsecond (i : Fin n) : coordDeriv (fun z => 2 * inner ℝ z (basis n i)) i x = 2 := by
    dsimp [coordDeriv]
    have hd : HasFDerivAt (fun z : Space n => 2 * inner ℝ z (basis n i))
        ((2 : ℝ) • innerSL ℝ (basis n i)) x := by
      simpa [real_inner_comm] using
        ((innerSL ℝ (basis n i)).hasFDerivAt (x := x)).const_mul 2
    rw [hd.fderiv]
    simp [basis]
  simp_rw [hsecond]
  simp [mul_comm]

lemma hasFDerivAt_norm_nonzero {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (fun z : Space n => ‖z‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  have he : (1 / (2 * ‖x‖) : ℝ) * 2 = ‖x‖⁻¹ := by field_simp
  rw [← Nat.cast_smul_eq_nsmul ℝ 2, smul_smul, Nat.cast_ofNat, he] at h
  exact h

lemma two_point_maximum {n : ℕ} {f : Space n → ℝ} (hf : Continuous f)
    {M L ε : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |f x| ≤ M)
    (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ x y : Space n, ∀ a b : Space n,
      f b - f a - L * ‖b - a‖ - ε * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      f y - f x - L * ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  let H : Space n × Space n → ℝ := fun z =>
    f z.2 - f z.1 - L * ‖z.2 - z.1‖ - ε * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
  have hc : Continuous H := by fun_prop
  let R := Real.sqrt (2 * M / ε + 1)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 2 * M / ε + 1 := Real.sq_sqrt (by positivity)
  have hevent : ∀ᶠ z in cocompact (Space n × Space n), H z ≤ H (0, 0) := by
    filter_upwards [((isCompact_closedBall (0 : Space n) R).prod
      (isCompact_closedBall (0 : Space n) R)).compl_mem_cocompact] with z hz
    have hz' : R < ‖z.1‖ ∨ R < ‖z.2‖ := by
      simpa only [Set.mem_compl_iff, Set.mem_prod, Metric.mem_closedBall, dist_zero_right,
        not_and_or, not_le] using hz
    have hsq : R ^ 2 < ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
      rcases hz' with hz' | hz'
      · nlinarith [sq_nonneg ‖z.2‖, norm_nonneg z.1]
      · nlinarith [sq_nonneg ‖z.1‖, norm_nonneg z.2]
    have heq : ε * (2 * M / ε + 1) = 2 * M + ε := by field_simp
    have hh := mul_lt_mul_of_pos_left hsq hε
    have hb1 := (abs_le.mp (hbound z.1)).1
    have hb2 := (abs_le.mp (hbound z.2)).2
    have hcost := mul_nonneg hL (norm_nonneg (z.2 - z.1))
    dsimp [H]
    simp only [sub_self, norm_zero, mul_zero, zero_pow two_ne_zero, add_zero]
    rw [hR2, heq] at hh
    linarith
  obtain ⟨⟨x, y⟩, hmax⟩ := hc.exists_forall_ge' (0, 0) hevent
  exact ⟨x, y, fun a b => hmax (a, b)⟩

lemma gradient_at_two_point_max_y {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (L ε : ℝ) {x y : Space n} (hxy : y ≠ x)
    (hm : ∀ b : Space n,
      f b - f x - L * ‖b - x‖ - ε * (‖x‖ ^ 2 + ‖b‖ ^ 2) ≤
      f y - f x - L * ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    gradient f y = (L / ‖y - x‖) • (y - x) + (2 * ε) • y := by
  have hn : HasFDerivAt (fun b : Space n => ‖b - x‖)
      (‖y - x‖⁻¹ • innerSL ℝ (y - x)) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using
      (hasFDerivAt_norm_nonzero (sub_ne_zero.mpr hxy)).comp y
        ((hasFDerivAt_id y).sub_const x)
  have hq : HasFDerivAt (fun b : Space n => ‖x‖ ^ 2 + ‖b‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ y) y := by
    have hh := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_add (‖x‖ ^ 2)
    rw [← Nat.cast_smul_eq_nsmul ℝ 2, Nat.cast_ofNat] at hh
    exact hh
  have hd := (((hf y).hasFDerivAt.sub_const (f x)).fun_sub
    (hn.const_mul L)).fun_sub (hq.const_mul ε)
  have hz := (show IsLocalMax
      (fun b => f b - f x - L * ‖b - x‖ - ε * (‖x‖ ^ 2 + ‖b‖ ^ 2)) y from
    Filter.Eventually.of_forall hm).hasFDerivAt_eq_zero hd
  apply (InnerProductSpace.toDual ℝ (Space n)).injective
  ext z
  have he := congrArg (fun A : Space n →L[ℝ] ℝ => A z) hz
  simp only [sub_apply, smul_apply, smul_eq_mul, zero_apply] at he
  change (fderiv ℝ f y) z - L * (‖y - x‖⁻¹ * inner ℝ (y - x) z) -
    ε * (2 * inner ℝ y z) = 0 at he
  simp only [toDual_gradient, map_add, map_smul, add_apply, smul_apply,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  rw [div_eq_mul_inv]
  linarith

lemma laplacian_fun_sub {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) :
    Laplacian.laplacian (fun z => f z - g z) x =
      Laplacian.laplacian f x - Laplacian.laplacian g x := by
  change Laplacian.laplacian (f - g) x = _
  exact hf.contDiffAt.laplacian_sub hg.contDiffAt

lemma laplacian_fun_add {n : ℕ} {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) :
    Laplacian.laplacian (fun z => f z + g z) x =
      Laplacian.laplacian f x + Laplacian.laplacian g x := by
  change Laplacian.laplacian (f + g) x = _
  exact hf.contDiffAt.laplacian_add hg.contDiffAt

lemma laplacian_fun_const_mul {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (c : ℝ) (x : Space n) :
    Laplacian.laplacian (fun z => c * f z) x = c * Laplacian.laplacian f x := by
  change Laplacian.laplacian (c • f) x = _
  exact InnerProductSpace.laplacian_smul c hf.contDiffAt

lemma laplacian_at_two_point_max {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (L ε : ℝ) {x y : Space n}
    (hm : ∀ a b : Space n,
      f b - f a - L * ‖b - a‖ - ε * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      f y - f x - L * ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2)) :
    Laplacian.laplacian f y - Laplacian.laplacian f x ≤ 4 * n * ε := by
  let F : Space n → ℝ := fun z =>
    f (y + z) - f (x + z) - L * ‖y - x‖ - ε * (‖x + z‖ ^ 2 + ‖y + z‖ ^ 2)
  have hF : ContDiff ℝ 2 F := by
    dsimp [F]
    exact (((hf.comp (contDiff_const.add contDiff_id)).sub
      (hf.comp (contDiff_const.add contDiff_id))).sub contDiff_const).sub
      ((((contDiff_const.add contDiff_id).norm_sq ℝ).add
        ((contDiff_const.add contDiff_id).norm_sq ℝ)).const_smul ε)
  have hmF : IsLocalMax F 0 := Filter.Eventually.of_forall (fun z => by
    simpa [F, add_sub_add_right_eq_sub] using hm (x + z) (y + z))
  have hl := laplacian_nonpos_of_local_max hF hmF
  have hj : Laplacian.laplacian F 0 =
      Laplacian.laplacian f y - Laplacian.laplacian f x - ε * (2 * n + 2 * n) := by
    have hfx : ContDiff ℝ 2 (fun z => f (x + z)) := hf.comp (contDiff_const.add contDiff_id)
    have hfy : ContDiff ℝ 2 (fun z => f (y + z)) := hf.comp (contDiff_const.add contDiff_id)
    have hnx : ContDiff ℝ 2 (fun z : Space n => ‖x + z‖ ^ 2) :=
      (contDiff_const.add contDiff_id).norm_sq ℝ
    have hny : ContDiff ℝ 2 (fun z : Space n => ‖y + z‖ ^ 2) :=
      (contDiff_const.add contDiff_id).norm_sq ℝ
    have hA : ContDiff ℝ 2 (fun z => f (y + z) - f (x + z) - L * ‖y - x‖) :=
      (hfy.sub hfx).sub contDiff_const
    have hB : ContDiff ℝ 2 (fun z => ε * (‖x + z‖ ^ 2 + ‖y + z‖ ^ 2)) :=
      contDiff_const.mul (hnx.add hny)
    have hC : ContDiff ℝ 2 (fun _ : Space n => L * ‖y - x‖) := contDiff_const
    dsimp only [F]
    rw [laplacian_fun_sub hA hB,
      laplacian_fun_sub (hfy.sub hfx) hC,
      laplacian_fun_sub hfy hfx,
      laplacian_fun_const_mul (hnx.add hny) ε,
      laplacian_fun_add hnx hny]
    simp only [laplacian_translate hf, add_zero, InnerProductSpace.laplacian_const,
      Pi.zero_apply, sub_zero]
    have hns : ContDiff ℝ 2 (fun z : Space n => ‖z‖ ^ 2) := contDiff_id.norm_sq ℝ
    rw [laplacian_translate hns, laplacian_translate hns]
    simp [laplacian_norm_sq]
  rw [hj] at hl
  linarith

lemma sq_norm_error {n : ℕ} {u p : Space n} {L E : ℝ}
    (hL : 0 ≤ L) (hE : 0 ≤ E) (hp : ‖p‖ = L) (hu : ‖u - p‖ ≤ E) :
    |‖u‖ ^ 2 - L ^ 2| ≤ E * (2 * L + E) := by
  have h1 : |‖u‖ - L| ≤ E := by rw [← hp]; exact (abs_norm_sub_norm_le u p).trans hu
  have h2 : ‖u‖ + L ≤ 2 * L + E := by have := (abs_le.mp h1).2; linarith
  calc
    |‖u‖ ^ 2 - L ^ 2| = |‖u‖ - L| * (‖u‖ + L) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg u) hL), ← abs_mul]
      congr 1
      ring
    _ ≤ E * (2 * L + E) := mul_le_mul h1 h2 (add_nonneg (norm_nonneg u) hL) hE

end DeGiorgi
end

end OAI
