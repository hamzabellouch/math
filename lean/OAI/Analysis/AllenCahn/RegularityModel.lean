import OAI.Analysis.AllenCahn.JetProducts

namespace OAI

noncomputable section
namespace RegularitySupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
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

end RegularitySupport.DeGiorgi
end

noncomputable section
namespace RegularitySupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

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

private def basis (n : ℕ) := EuclideanSpace.basisFun (Fin n) ℝ

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

lemma laplacian_comp_isometry {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (J : Space n ≃ₗᵢ[ℝ] Space n) (x : Space n) :
    Laplacian.laplacian (fun z => f (J z)) x = Laplacian.laplacian f (J x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (basis n),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ ((basis n).map J)]
  apply Finset.sum_congr rfl
  intro i _
  change iteratedFDeriv ℝ 2 (f ∘ J.toContinuousLinearMap) x _ = _
  rw [J.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by norm_num)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply]
  congr 1
  ext j
  fin_cases j <;> simp

def reflect {n : ℕ} (e : Space n) : Space n ≃ₗᵢ[ℝ] Space n :=
  (Submodule.span ℝ {e})ᗮ.reflection

lemma reflect_apply {n : ℕ} {e : Space n} (he : ‖e‖ = 1) (z : Space n) :
    reflect e z = z - (2 * inner ℝ e z) • e := by
  simp only [reflect, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, he]
  norm_num only [RCLike.ofReal_real_eq_id, id_eq, one_pow, div_one] 
  rw [neg_sub, ← smul_assoc]
  simp only [two_smul, two_mul]

def poissonPenalty (A t : ℝ) : ℝ := A * (1 - (max (1 - t) 0) ^ 2)

lemma poissonPenalty_of_le (A : ℝ) {t : ℝ} (ht : t ≤ 1) :
    poissonPenalty A t = A * (2 * t - t ^ 2) := by
  rw [poissonPenalty, max_eq_left (by linarith)]
  ring

lemma poissonPenalty_of_ge (A : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    poissonPenalty A t = A := by
  simp [poissonPenalty, max_eq_right (show 1 - t ≤ 0 by linarith)]

lemma poissonPenalty_nonneg {A t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t) :
    0 ≤ poissonPenalty A t := by
  by_cases h : t ≤ 1
  · rw [poissonPenalty_of_le A h]
    apply mul_nonneg hA
    nlinarith
  · rw [poissonPenalty_of_ge A (le_of_not_ge h)]
    exact hA

lemma poissonPenalty_le_linear {A t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t) :
    poissonPenalty A t ≤ 2 * A * t := by
  by_cases h : t ≤ 1
  · rw [poissonPenalty_of_le A h]
    nlinarith [mul_nonneg hA (sq_nonneg t)]
  · rw [poissonPenalty_of_ge A (le_of_not_ge h)]
    nlinarith

lemma poisson_maximum {n : ℕ} {f : Space n → ℝ} (hf : Continuous f)
    {M A ε : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, |f x| ≤ M)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ x y : Space n, ∀ a b : Space n,
      f b - f a - poissonPenalty A ‖b - a‖ - ε * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤
      f y - f x - poissonPenalty A ‖y - x‖ - ε * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  let H : Space n × Space n → ℝ := fun z =>
    f z.2 - f z.1 - poissonPenalty A ‖z.2 - z.1‖ - ε * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
  have hc : Continuous H := by dsimp [H, poissonPenalty]; fun_prop
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
    have hcost := poissonPenalty_nonneg hA (norm_nonneg (z.2 - z.1))
    dsimp [H]
    simp only [sub_self, norm_zero, poissonPenalty, sub_zero, max_eq_left zero_le_one,
      one_pow, mul_zero, zero_pow two_ne_zero, add_zero]
    rw [hR2, heq] at hh
    dsimp [poissonPenalty] at hcost
    linarith
  obtain ⟨⟨x, y⟩, hmax⟩ := hc.exists_forall_ge' (0, 0) hevent
  exact ⟨x, y, fun a b => hmax (a, b)⟩

lemma coordDeriv_affine {n : ℕ} (a : Space n) (c : ℝ) (i : Fin n) (x : Space n) :
    coordDeriv (fun z => c + inner ℝ a z) i x = inner ℝ a (basis n i) := by
  have hd : HasFDerivAt (fun z => c + inner ℝ a z) (innerSL ℝ a) x :=
    (innerSL ℝ a).hasFDerivAt.const_add c
  simp [coordDeriv, hd.fderiv]

lemma laplacian_affine {n : ℕ} (a : Space n) (c : ℝ) (x : Space n) :
    Laplacian.laplacian (fun z => c + inner ℝ a z) x = 0 := by
  have hc : ContDiff ℝ 2 (fun z : Space n => c + inner ℝ a z)  := contDiff_const.add ((innerSL ℝ a).contDiff)
  rw [laplacian_eq_sum_coordDeriv hc]
  have he (i : Fin n) : coordDeriv (fun z : Space n => c + inner ℝ a z) i =
      fun _ => inner ℝ a (basis n i) := funext (coordDeriv_affine a c i)
  simp_rw [he]
  simp [coordDeriv]

lemma laplacian_affine_sq {n : ℕ} (a : Space n) (c : ℝ) (x : Space n) :
    Laplacian.laplacian (fun z => (c + inner ℝ a z) ^ 2) x = 2 * ‖a‖ ^ 2 := by
  have hc : ContDiff ℝ 2 (fun z : Space n => (c + inner ℝ a z) ^ 2) :=
    (contDiff_const.add ((innerSL ℝ a).contDiff)).pow 2
  rw [laplacian_eq_sum_coordDeriv hc]
  have hfirst (i : Fin n) : coordDeriv (fun z : Space n => (c + inner ℝ a z) ^ 2) i =
      fun z => 2 * (c + inner ℝ a z) * inner ℝ a (basis n i) := by
    funext z
    have hd := ((innerSL ℝ a).hasFDerivAt (x := z)).const_add c
    have hd2 := hd.pow 2
    dsimp only [coordDeriv]
    change (fderiv ℝ (fun z => (c + (innerSL ℝ a) z) ^ 2) z) _ = _
    rw [hd2.fderiv]
    simp only [smul_apply, smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one, innerSL_apply_apply, nsmul_eq_mul]
  simp_rw [hfirst]
  have hsecond (i : Fin n) : coordDeriv
      (fun z => 2 * (c + inner ℝ a z) * inner ℝ a (basis n i)) i x =
      2 * (inner ℝ a (basis n i)) ^ 2 := by
    have hd := ((((innerSL ℝ a).hasFDerivAt (x := x)).const_add c).const_mul 2).mul_const
      (inner ℝ a (basis n i))
    dsimp only [coordDeriv]
    change (fderiv ℝ (fun z => 2 * (c + (innerSL ℝ a) z) * inner ℝ a ((basis n) i)) x) _ = _
    rw [hd.fderiv]
    simp [pow_two, mul_left_comm]
  simp_rw [hsecond]
  rw [← Finset.mul_sum]
  congr 1
  have hb := (basis n).sum_inner_mul_inner a a
  simpa only [real_inner_comm, ← pow_two, real_inner_self_eq_norm_sq] using hb

end RegularitySupport.DeGiorgi
end

end OAI
