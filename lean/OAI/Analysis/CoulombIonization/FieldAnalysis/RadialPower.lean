import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
namespace CoulombPDE

lemma second_deriv_nonpos_of_localMax {f : ℝ → ℝ} {x : ℝ}
    (h : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra! hp
  have hmin := isLocalMin_of_deriv_deriv_pos hp h.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [h, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hz := he.deriv.deriv_eq
  change deriv (deriv f) x = deriv (deriv (fun _ : ℝ => f x)) x at hz
  simp only [deriv_const, deriv_const'] at hz
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma second_deriv_line {f : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      (fderiv ℝ (fderiv ℝ f) x) v v := by
  let g : ℝ → E := fun t => x + t • v
  have hg (t : ℝ) : HasDerivAt g v t := by
    simpa [g] using ((hasDerivAt_id t).smul_const v).const_add x
  have hg0 : g 0 = x := by simp [g]
  have hc : ContinuousAt g 0 := (hg 0).continuousAt
  have he : deriv (fun t : ℝ => f (g t)) =ᶠ[𝓝 0]
      fun t => fderiv ℝ f (g t) v := by
    have hev := hc.eventually (hg0 ▸ h.eventually (by norm_num))
    filter_upwards [hev] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hg t)).deriv
  rw [he.deriv_eq]
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) (g 0) := by
    rw [hg0]
    exact (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (hf'.hasFDerivAt.comp_hasDerivAt 0 (hg 0)).clm_apply (hasDerivAt_const 0 v)
  simpa only [Function.comp_def, hg0, map_zero, add_zero] using hd.deriv

lemma second_fderiv_nonpos_of_localMax {f : E → ℝ} {x : E}
    (h : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) (v : E) :
    (fderiv ℝ (fderiv ℝ f) x) v v ≤ 0 := by
  rw [← second_deriv_line h v]
  have hg : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hm' : IsLocalMax (fun t : ℝ => f (x + t • v)) 0 := by
    simpa only [Function.comp_def] using
      (show IsLocalMax f ((fun t : ℝ => x + t • v) 0) by simpa using hm).comp_continuous (g := fun t : ℝ => x + t • v) hg
  exact second_deriv_nonpos_of_localMax hm'
    ((show ContinuousAt f (x + (0 : ℝ) • v) by simpa using h.continuousAt).comp (f := fun t : ℝ => x + t • v) hg)

variable [FiniteDimensional ℝ E]

lemma laplacian_nonpos_of_localMax {f : E → ℝ} {x : E}
    (h : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) : Δ f x ≤ 0 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_nonpos
  intro i _
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using second_fderiv_nonpos_of_localMax h hm ((stdOrthonormalBasis ℝ E) i)

lemma laplacian_norm_sq (x : E) :
    Δ (fun y : E => ‖y‖ ^ 2) x = 2 * (Module.finrank ℝ E : ℝ) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, fderiv_norm_sq]
  rw [fderiv_const_smul (innerSL ℝ (E := E)).differentiableAt]
  simp only [ContinuousLinearMap.fderiv, smul_apply, nsmul_eq_mul]
  change (∑ i, 2 * @inner ℝ E _ ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i)) = _
  simp [mul_comm]

theorem compact_maximum_principle [Nontrivial E] {K : Set E} (hK : IsCompact K)
    {u : E → ℝ} (hc : ContinuousOn u K)
    (hd : ∀ x ∈ interior K, ContDiffAt ℝ 2 u x)
    (hl : ∀ x ∈ interior K, 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x ∈ K, x ∉ interior K → u x ≤ 0) : ∀ x ∈ K, u x ≤ 0 := by
  intro x hx
  by_contra! hp
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let ε : ℝ := u x / (2 * (R ^ 2 + 1))
  have he : 0 < ε := div_pos hp (by positivity)
  have heq : ε * (2 * (R ^ 2 + 1)) = u x := by
    exact div_mul_cancel₀ _ (by positivity)
  let w : E → ℝ := fun y => u y + ε * (‖y‖ ^ 2 - R ^ 2)
  have hwu (y : E) (hy : y ∈ K) : w y ≤ u y := by
    have ht : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg y) (hbound y hy) 2
    dsimp [w]
    nlinarith
  have hpx : 0 < w x := by
    dsimp [w]
    nlinarith [mul_nonneg he.le (sq_nonneg ‖x‖)]
  have hwc : ContinuousOn w K := hc.add (by fun_prop)
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hwc
  have hpy : 0 < w y := hpx.trans_le (hmax hx)
  have hiy : y ∈ interior K := by
    by_contra hi
    exact (not_lt_of_ge ((hwu y hy).trans (hb y hy hi))) hpy
  have hdy := hd y hiy
  have hn : ContDiffAt ℝ 2 (fun z : E => ‖z‖ ^ 2) y := (contDiff_norm_sq ℝ).contDiffAt
  have hpert : ContDiffAt ℝ 2 (fun z : E => ε * (‖z‖ ^ 2 - R ^ 2)) y :=
    contDiffAt_const.mul (hn.sub contDiffAt_const)
  change ContDiffAt ℝ 2 (ε • ((fun z : E => ‖z‖ ^ 2) - fun _ => R ^ 2)) y at hpert
  have hs : ContDiffAt ℝ 2 ((fun z : E => ‖z‖ ^ 2) - fun _ => R ^ 2) y :=
    hn.sub contDiffAt_const
  have hwlap : Δ w y = Δ u y + ε * (2 * (Module.finrank ℝ E : ℝ)) := by
    change (Δ (u + ε • ((fun z : E => ‖z‖ ^ 2) - fun _ => R ^ 2)) : E → ℝ) y = _
    rw [hdy.laplacian_add hpert, laplacian_smul ε hs,
      hn.laplacian_sub (show ContDiffAt ℝ 2 (fun _ : E => R ^ 2) y from contDiffAt_const), laplacian_const, laplacian_norm_sq]
    simp
  have hnonpos := laplacian_nonpos_of_localMax (hdy.add hpert)
    (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hiy))
  change Δ w y ≤ 0 at hnonpos
  rw [hwlap] at hnonpos
  have hdim : 0 < (Module.finrank ℝ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hnonneg := hl y hiy (hpy.trans_le (hwu y hy))
  nlinarith [mul_pos he (mul_pos (by norm_num : (0 : ℝ) < 2) hdim)]

theorem semilinear_comparison [Nontrivial E] {K : Set E} (hK : IsCompact K)
    {u v : E → ℝ} {g : ℝ → ℝ} (hg : Monotone g)
    (huc : ContinuousOn u K) (hvc : ContinuousOn v K)
    (hud : ∀ x ∈ interior K, ContDiffAt ℝ 2 u x)
    (hvd : ∀ x ∈ interior K, ContDiffAt ℝ 2 v x)
    (hu : ∀ x ∈ interior K, g (u x) ≤ Δ u x)
    (hv : ∀ x ∈ interior K, Δ v x ≤ g (v x))
    (hb : ∀ x ∈ K, x ∉ interior K → u x ≤ v x) : ∀ x ∈ K, u x ≤ v x := by
  have hw := compact_maximum_principle hK (huc.sub hvc)
    (fun x hx => (hud x hx).sub (hvd x hx)) (fun x hx hp => ?_) (fun x hx hi => ?_)
  · intro x hx
    exact sub_nonpos.mp (hw x hx)
  · rw [(hud x hx).laplacian_sub (hvd x hx)]
    have h := hg (le_of_lt (sub_pos.mp hp))
    linarith [hu x hx, hv x hx]
  · exact sub_nonpos.mpr (hb x hx hi)

lemma differentiableAt_deriv_of_contDiffAt {g : ℝ → ℝ} {r : ℝ}
    (h : ContDiffAt ℝ 2 g r) : DifferentiableAt ℝ (deriv g) r := by
  have hc : ContDiffAt ℝ 1 (deriv g) r :=
    (h.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const
  exact hc.differentiableAt (by norm_num)

omit [FiniteDimensional ℝ E] in
lemma second_deriv_norm_sq_comp {g : ℝ → ℝ} {x : E}
    (h : ContDiffAt ℝ 2 g (‖x‖ ^ 2)) (v : E) :
    (fderiv ℝ (fderiv ℝ (fun y : E => g (‖y‖ ^ 2))) x) v v =
      deriv (deriv g) (‖x‖ ^ 2) * (2 * inner ℝ x v) ^ 2 +
        deriv g (‖x‖ ^ 2) * (2 * ‖v‖ ^ 2) := by
  have hf : ContDiffAt ℝ 2 (fun y : E => g (‖y‖ ^ 2)) x :=
    h.comp x ((contDiff_norm_sq ℝ).contDiffAt)
  rw [← second_deriv_line hf v]
  let l : ℝ → E := fun t => x + t • v
  have hl (t : ℝ) : HasDerivAt l v t := by
    simpa [l] using ((hasDerivAt_id t).smul_const v).const_add x
  have hl0 : l 0 = x := by simp [l]
  have hq (t : ℝ) : HasDerivAt (fun t => ‖l t‖ ^ 2) (2 * inner ℝ (l t) v) t :=
    (hl t).norm_sq
  have hq0 : ‖l 0‖ ^ 2 = ‖x‖ ^ 2 := by rw [hl0]
  have he : deriv (fun t => g (‖l t‖ ^ 2)) =ᶠ[𝓝 0]
      fun t => deriv g (‖l t‖ ^ 2) * (2 * inner ℝ (l t) v) := by
    have hev := (hq 0).continuousAt.eventually (hq0 ▸ h.eventually (by norm_num))
    filter_upwards [hev] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasDerivAt.comp t (hq t)).deriv
  rw [he.deriv_eq]
  have hgd : HasDerivAt (deriv g) (deriv (deriv g) (‖x‖ ^ 2)) (‖l 0‖ ^ 2) := by
    simpa only [hl0] using (differentiableAt_deriv_of_contDiffAt h).hasDerivAt
  have hdg : HasDerivAt (fun t => deriv g (‖l t‖ ^ 2))
      (deriv (deriv g) (‖x‖ ^ 2) * (2 * inner ℝ x v)) 0 := by
    simpa only [Function.comp_def, hl0] using hgd.comp 0 (hq 0)
  have hdi : HasDerivAt (fun t => 2 * inner ℝ (l t) v) (2 * ‖v‖ ^ 2) 0 := by
    simpa only [inner_zero_right, zero_add, real_inner_self_eq_norm_sq] using
      ((hl 0).inner ℝ (hasDerivAt_const 0 v)).const_mul 2
  calc
    _ = (deriv (deriv g) (‖x‖ ^ 2) * (2 * inner ℝ x v)) * (2 * inner ℝ (l 0) v) +
        deriv g (‖l 0‖ ^ 2) * (2 * ‖v‖ ^ 2) := (hdg.mul hdi).deriv
    _ = _ := by rw [hl0]; ring

lemma laplacian_norm_sq_comp {g : ℝ → ℝ} {x : E}
    (h : ContDiffAt ℝ 2 g (‖x‖ ^ 2)) :
    Δ (fun y : E => g (‖y‖ ^ 2)) x =
      4 * ‖x‖ ^ 2 * deriv (deriv g) (‖x‖ ^ 2) +
        2 * (Module.finrank ℝ E : ℝ) * deriv g (‖x‖ ^ 2) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  simp_rw [second_deriv_norm_sq_comp h, (stdOrthonormalBasis ℝ E).norm_eq_one]
  simp only [one_pow, mul_one, mul_pow, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← mul_assoc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [(stdOrthonormalBasis ℝ E).sum_sq_inner_left]
  ring

def radialPower (a : ℝ) (x : E) : ℝ := (‖x‖ ^ 2) ^ a

omit [FiniteDimensional ℝ E] in
lemma radialPower_contDiffAt (a : ℝ) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (radialPower a) x :=
  (contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))

lemma laplacian_radialPower (a : ℝ) {x : E} (hx : x ≠ 0) :
    (Δ (radialPower a : E → ℝ) : E → ℝ) x =
      (4 * a * (a - 1) + 2 * (Module.finrank ℝ E : ℝ) * a) * radialPower (a - 1) x := by
  have ht : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hc : ContDiffAt ℝ 2 (fun t : ℝ => t ^ a) (‖x‖ ^ 2) :=
    contDiffAt_id.rpow_const_of_ne ht.ne'
  have hd : deriv (fun t : ℝ => t ^ a) = fun t => a * t ^ (a - 1) :=
    funext (fun t => Real.deriv_rpow_const t a)
  have hdd : deriv (deriv (fun t : ℝ => t ^ a)) (‖x‖ ^ 2) =
      a * (a - 1) * (‖x‖ ^ 2) ^ (a - 2) := by
    rw [hd]
    calc
      _ = a * ((a - 1) * (‖x‖ ^ 2) ^ ((a - 1) - 1)) :=
        ((Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl ht.ne')).const_mul a).deriv
      _ = _ := by rw [show a - 1 - 1 = a - 2 by ring]; ring
  have hmul : ‖x‖ ^ 2 * (‖x‖ ^ 2) ^ (a - 2) = (‖x‖ ^ 2) ^ (a - 1) := by
    rw [Real.rpow_sub ht a 2, Real.rpow_sub ht a 1, Real.rpow_two, Real.rpow_one]
    field_simp
  unfold radialPower
  rw [laplacian_norm_sq_comp hc, hdd, Real.deriv_rpow_const]
  calc
    _ = 4 * a * (a - 1) * (‖x‖ ^ 2 * (‖x‖ ^ 2) ^ (a - 2)) +
        2 * (Module.finrank ℝ E : ℝ) * a * (‖x‖ ^ 2) ^ (a - 1) := by ring
    _ = _ := by rw [hmul]; ring

theorem annular_maximum_principle [Nontrivial E] {a R : ℝ} (ha : 0 < a)
    {u : E → ℝ} (hd : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, x ≠ 0 → ‖x‖ ≤ R → 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x, ‖x‖ = a ∨ ‖x‖ = R → u x ≤ 0) :
    ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → u x ≤ 0 := by
  let K : Set E := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ R}
  have hk : IsCompact K := by
    have he : K = Metric.closedBall (0 : E) R ∩ {x | a ≤ ‖x‖} := by
      ext x
      simp only [K, mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      exact and_comm
    rw [he]
    exact (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hn (x : E) (hx : x ∈ K) : x ≠ 0 := by
    have hp : 0 < ‖x‖ := ha.trans_le hx.1
    exact norm_pos_iff.mp hp
  have hb' (x : E) (hx : x ∈ K) (hi : x ∉ interior K) : u x ≤ 0 := by
    apply hb
    by_contra! h
    have ha' : a < ‖x‖ := lt_of_le_of_ne hx.1 h.1.symm
    have hr' : ‖x‖ < R := lt_of_le_of_ne hx.2 h.2
    apply hi
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨ha', hr'⟩)
    exact fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hm := compact_maximum_principle hk
    (fun x hx => (hd x (hn x hx) hx.2).continuousAt.continuousWithinAt)
    (fun x hx => hd x (hn x (interior_subset hx)) (interior_subset hx).2)
    (fun x hx hp => hl x (hn x (interior_subset hx)) (interior_subset hx).2 hp) hb'
  exact fun x hx hr => hm x ⟨hx, hr⟩

theorem punctured_ball_maximum_principle [Nontrivial E] {R : ℝ}
    {u : E → ℝ} (hd : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, x ≠ 0 → ‖x‖ ≤ R → 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x, ‖x‖ = R → u x ≤ 0)
    (hz : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → u x ≤ 0) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R → u x ≤ 0 := by
  obtain ⟨a, ha, hz⟩ := hz
  intro x hx hr
  by_cases hxa : ‖x‖ ≤ a
  · exact hz x hx hxa
  · apply annular_maximum_principle ha hd hl (fun y hy => ?_) x (le_of_not_ge hxa) hr
    rcases hy with hy | hy
    · exact hz y (norm_pos_iff.mp (hy ▸ ha)) hy.le
    · exact hb y hy

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma radialPower_add (a b : ℝ) {x : E} (hx : x ≠ 0) :
    radialPower (a + b) x = radialPower a x * radialPower b x :=
  Real.rpow_add (sq_pos_of_pos (norm_pos_iff.mpr hx)) a b

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma radialPower_pos (a : ℝ) {x : E} (hx : x ≠ 0) : 0 < radialPower a x :=
  Real.rpow_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)) a

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma radialPower_rpow (a b : ℝ) (x : E) :
    (radialPower a x) ^ b = radialPower (a * b) x :=
  (Real.rpow_mul (sq_nonneg ‖x‖) a b).symm

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma radialPower_nonneg (a : ℝ) (x : E) : 0 ≤ radialPower a x :=
  Real.rpow_nonneg (sq_nonneg ‖x‖) a

lemma exists_small_rpow_bound {s : ℝ} (hs : 0 < s) (M : ℝ) :
    ∃ a > 0, ∀ t : ℝ, 0 < t → t ≤ a → M ≤ t ^ (-s) := by
  have he := (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hs)).eventually (eventually_ge_atTop M)
  obtain ⟨b, hb, hsub⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨b / 2, by positivity, ?_⟩
  intro t ht htb
  apply hsub
  exact ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using
    (show t < b by linarith), ht⟩

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma exists_small_radialPower_bound {s : ℝ} (hs : 0 < s) (M : ℝ) :
    ∃ a > 0, ∀ x : E, x ≠ 0 → ‖x‖ ≤ a → M ≤ radialPower (-s) x := by
  obtain ⟨b, hb, hbound⟩ := exists_small_rpow_bound hs M
  refine ⟨min 1 b, lt_min (by norm_num) hb, ?_⟩
  intro x hx ha
  have h1 : ‖x‖ ≤ 1 := ha.trans (min_le_left _ _)
  have hb' : ‖x‖ ≤ b := ha.trans (min_le_right _ _)
  apply hbound _ (sq_pos_of_pos (norm_pos_iff.mpr hx))
  nlinarith [norm_nonneg x]

lemma exists_small_exponent {q : ℝ} (hq : 12 < q) :
    ∃ s > 0, 12 + 14 * s + 4 * s ^ 2 ≤ q := by
  let s := min 1 ((q - 12) / 36)
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have h1 : s ≤ 1 := min_le_left _ _
  have hq' : s ≤ (q - 12) / 36 := min_le_right _ _
  refine ⟨s, hs, ?_⟩
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr h1)]

lemma rpow_three_halves (v : ℝ) (hv : 0 ≤ v) : v ^ (3 / 2 : ℝ) = v * v ^ (1 / 2 : ℝ) := by
  by_cases h : v = 0
  · subst v; norm_num
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (lt_of_le_of_ne hv (Ne.symm h)), Real.rpow_one]

lemma rpow_three_halves_lower {B v : ℝ} (hB : 0 ≤ B) (hv : B ≤ v) :
    B ^ (1 / 2 : ℝ) * v ≤ v ^ (3 / 2 : ℝ) := by
  rw [rpow_three_halves v (hB.trans hv)]
  have h := Real.rpow_le_rpow hB hv (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith [mul_nonneg (hB.trans hv) (sub_nonneg.mpr h)]

lemma rpow_three_halves_upper {B v : ℝ} (hv : 0 ≤ v) (hB : v ≤ B) :
    v ^ (3 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) * v := by
  rw [rpow_three_halves v hv]
  have h := Real.rpow_le_rpow hv hB (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith [mul_nonneg hv (sub_nonneg.mpr h)]

abbrev Space := EuclideanSpace ℝ (Fin 3)

lemma radial_laplacian_three (a : ℝ) {x : Space} (hx : x ≠ 0) :
    (Δ (radialPower a : Space → ℝ) : Space → ℝ) x =
      (4 * a ^ 2 + 2 * a) * radialPower (a - 1) x := by
  rw [laplacian_radialPower a hx]
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hdim]
  change (4 * a * (a - 1) + 2 * (3 : ℝ) * a) * radialPower (a - 1) x = _
  ring

def radialCombination (B e s c : ℝ) (x : Space) : ℝ :=
  B * radialPower (-2) x + e * radialPower (-2 - s) x + c

lemma radialCombination_contDiffAt (B e s c : ℝ) {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (radialCombination B e s c) x :=
  ((contDiffAt_const.mul (radialPower_contDiffAt _ hx)).add
    (contDiffAt_const.mul (radialPower_contDiffAt _ hx))).add contDiffAt_const

lemma radialCombination_laplacian (B e s c : ℝ) {x : Space} (hx : x ≠ 0) :
    Δ (radialCombination B e s c) x =
      radialPower (-3) x * (12 * B + (12 + 14 * s + 4 * s ^ 2) * e * radialPower (-s) x) := by
  have h1 := radialPower_contDiffAt (-2) hx
  have h2 := radialPower_contDiffAt (-2 - s) hx
  have hb : ContDiffAt ℝ 2 (B • (radialPower (-2) : Space → ℝ)) x :=
    contDiffAt_const.smul h1
  have he : ContDiffAt ℝ 2 (e • (radialPower (-2 - s) : Space → ℝ)) x :=
    contDiffAt_const.smul h2
  have hsum : ContDiffAt ℝ 2 (B • (radialPower (-2) : Space → ℝ) + e • radialPower (-2 - s)) x := hb.add he
  change (Δ ((B • radialPower (-2) + e • radialPower (-2 - s)) + fun _ => c) : Space → ℝ) x = _
  rw [hsum.laplacian_add (show ContDiffAt ℝ 2 (fun _ : Space => c) x from contDiffAt_const), hb.laplacian_add he,
    laplacian_smul B h1, laplacian_smul e h2, laplacian_const,
    radial_laplacian_three _ hx, radial_laplacian_three _ hx]
  norm_num only
  rw [show -2 - s - 1 = -3 + -s by ring, radialPower_add _ _ hx]
  simp only [Pi.zero_apply, add_zero]
  ring

def reaction (d v : ℝ) : ℝ := d * (max (v - 1) 0) ^ (3 / 2 : ℝ)

lemma reaction_monotone {d : ℝ} (hd : 0 ≤ d) : Monotone (reaction d) := by
  intro u v huv
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_right _ _)
    (max_le_max (sub_le_sub_right huv 1) le_rfl) (by norm_num)) hd

lemma radialCombination_factor (B e s c : ℝ) {x : Space} (hx : x ≠ 0) :
    radialCombination B e s c x =
      radialPower (-2) x * (B + e * radialPower (-s) x) + c := by
  rw [radialCombination, show -2 - s = -2 + -s by ring, radialPower_add _ _ hx]
  ring

lemma radial_scaled_reaction {v : ℝ} (hv : 0 ≤ v) (x : Space) :
    (radialPower (-2) x * v) ^ (3 / 2 : ℝ) = radialPower (-3) x * v ^ (3 / 2 : ℝ) := by
  rw [Real.mul_rpow (radialPower_nonneg _ _) hv, radialPower_rpow]
  norm_num

lemma upper_barrier_laplacian {d B e s c : ℝ} (hd : 0 ≤ d) (hB : 0 < B)
    (he : 0 ≤ e) (hc : 1 ≤ c) (hq : 12 ≤ d * B ^ (1 / 2 : ℝ))
    (hκ : 12 + 14 * s + 4 * s ^ 2 ≤ d * B ^ (1 / 2 : ℝ))
    {x : Space} (hx : x ≠ 0) :
    Δ (radialCombination B e s c) x ≤ reaction d (radialCombination B e s c x) := by
  let z := e * radialPower (-s) x
  have hz : 0 ≤ z := mul_nonneg he (radialPower_nonneg _ _)
  have hv : 0 < B + z := by positivity
  have hf : radialPower (-2) x * (B + z) ≤ max (radialCombination B e s c x - 1) 0 := by
    apply le_trans _ (le_max_left _ _)
    rw [radialCombination_factor _ _ _ _ hx]
    dsimp [z]
    linarith
  calc
    Δ (radialCombination B e s c) x
        = radialPower (-3) x * (12 * B + (12 + 14 * s + 4 * s ^ 2) * z) := by
          rw [radialCombination_laplacian _ _ _ _ hx]; dsimp [z]; ring
    _ ≤ radialPower (-3) x * (d * B ^ (1 / 2 : ℝ) * (B + z)) := by
      apply mul_le_mul_of_nonneg_left _ (radialPower_nonneg _ _)
      nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hq), mul_nonneg hz (sub_nonneg.mpr hκ)]
    _ ≤ radialPower (-3) x * (d * (B + z) ^ (3 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (radialPower_nonneg _ _)
      calc
        _ = d * (B ^ (1 / 2 : ℝ) * (B + z)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_three_halves_lower hB.le (by linarith)) hd
    _ = d * (radialPower (-2) x * (B + z)) ^ (3 / 2 : ℝ) := by
      rw [radial_scaled_reaction hv.le]; ring
    _ ≤ reaction d (radialCombination B e s c x) := by
      apply mul_le_mul_of_nonneg_left _ hd
      exact Real.rpow_le_rpow (mul_nonneg (radialPower_nonneg _ _) hv.le) hf (by norm_num)

end CoulombPDE

end

end OAI
