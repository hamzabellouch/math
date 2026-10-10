import OAI.Analysis.AllenCahn.JetProducts

namespace OAI

noncomputable section
namespace PositiveMaximum
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

end PositiveMaximum
end

noncomputable section
namespace PositiveMaximum
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
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

lemma compact_minimum_principle {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) {K : Set (Space n)} (hK : IsCompact K)
    (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    (hineq : ∀ x ∈ interior K, Laplacian.laplacian f x ≤ 2 * f x) :
    ∀ x ∈ K, 0 ≤ f x := by
  intro x hx
  by_contra hn
  have hneg : f x < 0 := lt_of_not_ge hn
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hf.continuous.continuousOn
  have hyneg : f y < 0 := lt_of_le_of_lt (hmin hx) hneg
  have hyint : y ∈ interior K := by
    by_contra hh
    exact (not_le_of_gt hyneg) (hboundary y hy hh)
  have hlap := laplacian_nonneg_of_local_min hf
    (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hyint))
  have hle := hineq y hyint
  linarith

private def gaussian {n : ℕ} (a : ℝ) (y : Space n) (x : Space n) : ℝ :=
  Real.exp (-a * ‖x - y‖ ^ 2)

private lemma gaussian_contDiff {n : ℕ} (a : ℝ) (y : Space n) :
    ContDiff ℝ 2 (gaussian a y) := by
  exact ((contDiff_const.mul ((contDiff_norm_sq ℝ).comp
    (contDiff_id.sub contDiff_const)))).exp

private lemma fderiv_gaussian {n : ℕ} (a : ℝ) (y x e : Space n) :
    fderiv ℝ (gaussian a y) x e =
      gaussian a y x * (-2 * a * inner ℝ (x - y) e) := by
  have h := (((hasFDerivAt_id x).sub (hasFDerivAt_const y x)).norm_sq.const_mul (-a)).exp
  rw [show fderiv ℝ (gaussian a y) x = _ from h.fderiv]
  simp [gaussian, inner_sub_left]
  ring

private lemma second_coord_gaussian {n : ℕ} (a : ℝ) (y x : Space n) (i : Fin n) :
    coordDeriv (coordDeriv (gaussian a y) i) i x =
      gaussian a y x * (4 * a ^ 2 * (inner ℝ (x - y) (basis n i)) ^ 2 - 2 * a) := by
  have hfun : coordDeriv (gaussian a y) i = fun z =>
      gaussian a y z * (-2 * a * inner ℝ (z - y) (basis n i)) := by
    funext z
    exact fderiv_gaussian a y z (basis n i)
  rw [hfun]
  unfold coordDeriv
  have hg := (gaussian_contDiff a y).differentiable (by norm_num)
  have hl : Differentiable ℝ (fun z : Space n => inner ℝ (z - y) (basis n i)) :=
    (differentiable_id.sub (differentiable_const y)).inner ℝ (differentiable_const _)
  rw [fderiv_fun_mul (hg x) ((hl.const_mul (-2 * a)) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_gaussian]
  have hi : fderiv ℝ (fun z : Space n => -2 * a * inner ℝ (z - y) (basis n i)) x
      (basis n i) = -2 * a := by
    rw [fderiv_const_mul (hl x) (-2 * a)]
    simp only [smul_apply, smul_eq_mul]
    have hs : DifferentiableAt ℝ (fun z : Space n => z - y) x :=
      differentiableAt_id.sub (differentiableAt_const y)
    rw [fderiv_inner_apply ℝ hs (differentiableAt_const (c := basis n i))]
    simp [basis, fderiv_fun_sub]
  rw [hi]
  ring

private lemma laplacian_gaussian {n : ℕ} (a : ℝ) (y x : Space n) :
    Laplacian.laplacian (gaussian a y) x =
      gaussian a y x * (4 * a ^ 2 * ‖x - y‖ ^ 2 - 2 * a * n) := by
  rw [laplacian_eq_sum_coordDeriv (gaussian_contDiff a y)]
  simp_rw [second_coord_gaussian]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
    (basis n).sum_sq_inner_left]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private def barrier {n : ℕ} (a r : ℝ) (y : Space n) (x : Space n) : ℝ :=
  gaussian a y x - Real.exp (-a * r ^ 2)

private lemma barrier_contDiff {n : ℕ} (a r : ℝ) (y : Space n) :
    ContDiff ℝ 2 (barrier a r y) := (gaussian_contDiff a y).sub contDiff_const

private lemma laplacian_barrier {n : ℕ} (a r : ℝ) (y x : Space n) :
    Laplacian.laplacian (barrier a r y) x =
      gaussian a y x * (4 * a ^ 2 * ‖x - y‖ ^ 2 - 2 * a * n) := by
  change Laplacian.laplacian ((gaussian a y) - (fun _ : Space n => Real.exp (-a * r ^ 2))) x = _
  rw [(gaussian_contDiff a y).contDiffAt.laplacian_sub contDiff_const.contDiffAt,
    InnerProductSpace.laplacian_const]
  simpa using laplacian_gaussian a y x

private lemma barrier_le_one {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (r : ℝ) (y x : Space n) :
    barrier a r y x ≤ 1 := by
  have he : gaussian a y x ≤ 1 := by
    rw [gaussian, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _)
  have hh := Real.exp_pos (-a * r ^ 2)
  dsimp [barrier]
  linarith

private lemma barrier_subsolution {n : ℕ} {a r : ℝ} (ha : 1 ≤ a) (hr : 0 < r)
    (hscale : 2 * (n : ℝ) + 2 ≤ a * r ^ 2) (y x : Space n)
    (hx : r / 2 ≤ ‖x - y‖) :
    2 * barrier a r y x ≤ Laplacian.laplacian (barrier a r y) x := by
  have han : 0 ≤ a := le_trans (by norm_num) ha
  have hs : r ^ 2 ≤ 4 * ‖x - y‖ ^ 2 := by nlinarith [norm_nonneg (x - y)]
  have h1 := mul_le_mul_of_nonneg_left hscale han
  have h2 := mul_le_mul_of_nonneg_left hs (sq_nonneg a)
  have hcoeff : 0 ≤ 4 * a ^ 2 * ‖x - y‖ ^ 2 - 2 * a * n - 2 := by
    nlinarith
  have hp : 0 ≤ gaussian a y x := le_of_lt (Real.exp_pos _)
  have hm := mul_nonneg hp hcoeff
  have he := Real.exp_pos (-a * r ^ 2)
  rw [laplacian_barrier]
  dsimp only [barrier]
  nlinarith

private lemma laplacian_sub_const_mul {n : ℕ} {w b : Space n → ℝ}
    (hw : ContDiff ℝ 2 w) (hb : ContDiff ℝ 2 b) (ε : ℝ) (x : Space n) :
    Laplacian.laplacian (fun z => w z - ε * b z) x =
      Laplacian.laplacian w x - ε * Laplacian.laplacian b x := by
  change Laplacian.laplacian (w - ε • b) x = _
  have hs : ContDiff ℝ 2 (ε • b) := hb.const_smul ε
  rw [hw.contDiffAt.laplacian_sub hs.contDiffAt,
    InnerProductSpace.laplacian_smul ε hb.contDiffAt]
  rfl

private lemma annulus_comparison {n : ℕ} {w : Space n → ℝ}
    (hw : ContDiff ℝ 2 w) (hw0 : ∀ x, 0 ≤ w x)
    (hineq : ∀ x, Laplacian.laplacian w x ≤ 2 * w x)
    {a r ε : ℝ} (ha : 1 ≤ a) (hr : 0 < r) (hε : 0 ≤ ε)
    (hscale : 2 * (n : ℝ) + 2 ≤ a * r ^ 2) (y : Space n)
    (hinner : ∀ x, ‖x - y‖ = r / 2 → ε ≤ w x) :
    ∀ x, r / 2 ≤ ‖x - y‖ → ‖x - y‖ ≤ r → ε * barrier a r y x ≤ w x := by
  let K : Set (Space n) := {x | r / 2 ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ r}
  have hn : Continuous (fun x : Space n => ‖x - y‖) :=
    (continuous_id.sub continuous_const).norm
  have hclosed : IsClosed K :=
    (isClosed_le continuous_const hn).inter (isClosed_le hn continuous_const)
  have hK : IsCompact K := (isCompact_closedBall y r).of_isClosed_subset hclosed (by
    intro x hx
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx.2)
  have hF : ContDiff ℝ 2 (fun x => w x - ε * barrier a r y x) :=
    hw.sub (contDiff_const.mul (barrier_contDiff a r y))
  have hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ w x - ε * barrier a r y x := by
    intro x hx hxout
    by_cases hilow : ‖x - y‖ = r / 2
    · have hb := mul_le_mul_of_nonneg_left (barrier_le_one (le_trans (by norm_num) ha) r y x) hε
      have hi := hinner x hilow
      linarith
    by_cases hihigh : ‖x - y‖ = r
    · simpa [barrier, gaussian, hihigh] using hw0 x
    exfalso
    apply hxout
    rw [mem_interior_iff_mem_nhds]
    have ho : IsOpen {z : Space n | r / 2 < ‖z - y‖ ∧ ‖z - y‖ < r} :=
      (isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_const)
    have hxstrict : x ∈ {z : Space n | r / 2 < ‖z - y‖ ∧ ‖z - y‖ < r} :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hilow), lt_of_le_of_ne hx.2 hihigh⟩
    exact Filter.mem_of_superset (ho.mem_nhds hxstrict) (fun z hz => ⟨hz.1.le, hz.2.le⟩)
  have hFineq : ∀ x ∈ interior K,
      Laplacian.laplacian (fun x => w x - ε * barrier a r y x) x ≤
        2 * (w x - ε * barrier a r y x) := by
    intro x hx
    have hxb : x ∈ K := interior_subset hx
    rw [laplacian_sub_const_mul hw (barrier_contDiff a r y)]
    have h1 := hineq x
    have h2 := mul_le_mul_of_nonneg_left (barrier_subsolution ha hr hscale y x hxb.1) hε
    linarith
  have H := compact_minimum_principle hF hK hboundary hFineq
  intro x hxlo hxhi
  have hh := H x ⟨hxlo, hxhi⟩
  linarith

private lemma fderiv_barrier {n : ℕ} (a r : ℝ) (y x e : Space n) :
    fderiv ℝ (barrier a r y) x e =
      gaussian a y x * (-2 * a * inner ℝ (x - y) e) := by
  unfold barrier
  rw [fderiv_fun_sub ((gaussian_contDiff a y).differentiable (by norm_num) x)
    (differentiableAt_const _)]
  simpa using fderiv_gaussian a y x e

private lemma nonneg_right_derivative {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (h0 : f 0 = 0)
    (hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin, hpos] with t ht hp
  simpa [h0] using mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) hp

private lemma no_tangent_zero {n : ℕ} {w : Space n → ℝ}
    (hw : ContDiff ℝ 2 w) (hw0 : ∀ x, 0 ≤ w x)
    (hineq : ∀ x, Laplacian.laplacian w x ≤ 2 * w x)
    {r : ℝ} (hr : 0 < r) (y z : Space n) (hz : ‖z - y‖ = r)
    (hwz : w z = 0) (hball : ∀ x, ‖x - y‖ < r → 0 < w x) : False := by
  obtain ⟨p, hp, hpmin⟩ := (isCompact_closedBall y (r / 2)).exists_isMinOn
    ⟨y, by simp only [Metric.mem_closedBall, dist_self]; positivity⟩ hw.continuous.continuousOn
  have hppos : 0 < w p := hball p (by
    have hnorm : ‖p - y‖ ≤ r / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hp
    linarith)
  let a : ℝ := 1 + (2 * (n : ℝ) + 2) / r ^ 2
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have ha : 1 ≤ a := by
    have hq : 0 ≤ (2 * (n : ℝ) + 2) / r ^ 2 := by positivity
    dsimp [a]
    linarith
  have hscale : 2 * (n : ℝ) + 2 ≤ a * r ^ 2 := by
    dsimp [a]
    field_simp
    nlinarith
  have hcomp := annulus_comparison hw hw0 hineq ha hr hppos.le hscale y
    (fun x hx => hpmin (by simp [Metric.mem_closedBall, dist_eq_norm, hx]))
  let F : Space n → ℝ := fun x => w x - w p * barrier a r y x
  let e : Space n := y - z
  let f : ℝ → ℝ := fun t => F (z + t • e)
  have hF : ContDiff ℝ 2 F := hw.sub (contDiff_const.mul (barrier_contDiff a r y))
  have hdline : HasDerivAt (fun t : ℝ => z + t • e) e 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) z).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const e)
  have hd : HasDerivAt f (fderiv ℝ F z e) 0 := by
    simpa [f, Function.comp_def] using ((hF.differentiable (by norm_num) (z + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt 0 hdline)
  have hf0 : f 0 = 0 := by simp [f, F, barrier, gaussian, hz, hwz]
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ f t := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with t ht ht2
    change 0 < t at ht
    change t < 1 / 2 at ht2
    have hnorm : ‖z + t • e - y‖ = (1 - t) * r := by
      have heq : z + t • e - y = (1 - t) • (z - y) := by dsimp [e]; module
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - t), hz]
    have hlow : r / 2 ≤ ‖z + t • e - y‖ := by rw [hnorm]; nlinarith
    have hhigh : ‖z + t • e - y‖ ≤ r := by rw [hnorm]; nlinarith
    have hh := hcomp (z + t • e) hlow hhigh
    dsimp [f, F]
    linarith
  have hnonneg := nonneg_right_derivative hd hf0 hpos
  have hmin : IsLocalMin w z := Filter.Eventually.of_forall (fun x => by simpa [hwz] using hw0 x)
  have hwder := hmin.fderiv_eq_zero
  have hi : inner ℝ (z - y) e = -r ^ 2 := by
    have heq : e = -(z - y) := by dsimp [e]; abel
    rw [heq, inner_neg_right, real_inner_self_eq_norm_sq, hz]
  have hcalc : fderiv ℝ F z e =
      -(w p * gaussian a y z * (2 * a * r ^ 2)) := by
    dsimp only [F]
    rw [fderiv_fun_sub (hw.differentiable (by norm_num) z)
      (((barrier_contDiff a r y).differentiable (by norm_num)).const_mul _ z)]
    simp only [sub_apply, hwder, zero_apply]
    rw [fderiv_const_mul ((barrier_contDiff a r y).differentiable (by norm_num) z)]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_barrier, hi]
    ring
  have hnegative : fderiv ℝ F z e < 0 := by
    rw [hcalc]
    have hg : 0 < gaussian a y z := Real.exp_pos _
    have hap : 0 < a := lt_of_lt_of_le (by norm_num) ha
    exact neg_neg_of_pos (mul_pos (mul_pos hppos hg) (mul_pos (mul_pos (by norm_num) hap) hr2))
  exact not_le_of_gt hnegative hnonneg

lemma nonnegative_supersolution_eq_zero {n : ℕ} {w : Space n → ℝ}
    (hw : ContDiff ℝ 2 w) (hw0 : ∀ x, 0 ≤ w x)
    (hineq : ∀ x, Laplacian.laplacian w x ≤ 2 * w x)
    {z : Space n} (hwz : w z = 0) : ∀ x, w x = 0 := by
  intro y
  by_contra hy
  have hypos : 0 < w y := lt_of_le_of_ne (hw0 y) (Ne.symm hy)
  let Z : Set (Space n) := {x | w x = 0}
  have hZ : IsClosed Z := isClosed_eq hw.continuous continuous_const
  obtain ⟨p, hp, hdist⟩ := hZ.exists_infDist_eq_dist ⟨z, hwz⟩ y
  have hne : y ≠ p := by
    intro heq
    have hpzero : w p = 0 := hp
    rw [heq, hpzero] at hypos
    exact lt_irrefl _ hypos
  have hr : 0 < dist y p := dist_pos.mpr hne
  have hball : ∀ x, ‖x - y‖ < dist y p → 0 < w x := by
    intro x hx
    by_contra hnot
    have hwx : w x = 0 := le_antisymm (le_of_not_gt hnot) (hw0 x)
    have hd := Metric.infDist_le_dist_of_mem (x := y) (show x ∈ Z from hwx)
    rw [hdist] at hd
    have he : dist y x = ‖x - y‖ := by rw [dist_comm, dist_eq_norm]
    rw [he] at hd
    exact not_le_of_gt hx hd
  exact no_tangent_zero hw hw0 hineq hr y p (by rw [← dist_eq_norm, dist_comm]) hp hball

end PositiveMaximum
end

end OAI
