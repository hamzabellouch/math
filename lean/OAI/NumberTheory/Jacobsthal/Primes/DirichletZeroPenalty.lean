import OAI.NumberTheory.Jacobsthal.Analysis.LocalZeroLogDerivative

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

noncomputable def dirichletCenter (t : ℝ) : ℂ := 3 + (t : ℂ) * Complex.I
noncomputable def dirichletDiskPoint (t : ℝ) (w : ℂ) : ℂ := dirichletCenter t + (5/2 : ℂ)*w
noncomputable def normalizedDirichlet {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) (w : ℂ) : ℂ :=
  DirichletCharacter.LFunction chi (dirichletDiskPoint t w) /
    DirichletCharacter.LFunction chi (dirichletCenter t)
noncomputable def dirichletDiskEnvelope (q : ℕ) (t : ℝ) : ℝ :=
  4 * absoluteZetaTwo * (|t|+6) * (q : ℝ)^(1/2:ℝ)

@[simp] theorem dirichletCenter_re (t : ℝ) : (dirichletCenter t).re = 3 := by
  simp [dirichletCenter]
@[simp] theorem dirichletDiskPoint_re (t : ℝ) (w : ℂ) :
    (dirichletDiskPoint t w).re = 3 + (5/2:ℝ)*w.re := by
  simp [dirichletDiskPoint]

theorem dirichletDiskPoint_half_strip (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    1/2 ≤ (dirichletDiskPoint t w).re := by
  have h := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
  rw [dirichletDiskPoint_re]
  linarith

theorem dirichletDiskPoint_norm (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖dirichletDiskPoint t w‖ ≤ |t|+6 := by
  have hc : ‖dirichletCenter t‖ ≤ 3+|t| := by
    simpa [dirichletCenter, norm_mul] using
      (norm_add_le (3 : ℂ) ((t : ℂ)*Complex.I))
  have h := norm_add_le (dirichletCenter t) ((5/2 : ℂ)*w)
  have hn : ‖(5/2:ℂ)*w‖ = (5/2:ℝ)*‖w‖ := by rw [norm_mul]; norm_num
  rw [hn] at h
  change ‖dirichletDiskPoint t w‖ ≤ _ at h
  linarith

theorem normalizedDirichlet_zero {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : normalizedDirichlet chi t 0 = 1 := by
  unfold normalizedDirichlet dirichletDiskPoint
  simp only [mul_zero, add_zero]
  exact div_self (LFunction_ne_zero_right chi (by simp))

theorem normalizedDirichlet_analytic {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) (w : ℂ) :
    AnalyticAt ℂ (normalizedDirichlet chi t) w := by
  have hL := DirichletCharacter.differentiable_LFunction hchi
  have hd : Differentiable ℂ (normalizedDirichlet chi t) := by
    unfold normalizedDirichlet dirichletDiskPoint
    fun_prop
  exact hd.analyticAt w

theorem normalizedDirichlet_bound {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖normalizedDirichlet chi t w‖ ≤ dirichletDiskEnvelope q t := by
  have hu := norm_LFunction_half_strip chi hchi (dirichletDiskPoint_half_strip t hw)
  have hi := norm_inv_LFunction_le_absoluteZetaTwo chi (s := dirichletCenter t) (by norm_num)
  have hZ : 0 ≤ absoluteZetaTwo := zero_le_one.trans one_le_absoluteZetaTwo
  unfold normalizedDirichlet
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (4 * ‖dirichletDiskPoint t w‖ * (q : ℝ)^(1/2:ℝ)) * absoluteZetaTwo :=
      mul_le_mul hu hi (norm_nonneg _) (by positivity)
    _ ≤ (4 * (|t|+6) * (q : ℝ)^(1/2:ℝ)) * absoluteZetaTwo := by
      gcongr
      exact dirichletDiskPoint_norm t hw
    _ = dirichletDiskEnvelope q t := by unfold dirichletDiskEnvelope; ring

theorem dirichletDiskEnvelope_gt_one (q : ℕ) [NeZero q] (t : ℝ) :
    1 < dirichletDiskEnvelope q t := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hp : (1 : ℝ) ≤ (q : ℝ)^(1/2:ℝ) := Real.one_le_rpow hq (by norm_num)
  have hZ := one_le_absoluteZetaTwo
  have ht := abs_nonneg t
  unfold dirichletDiskEnvelope
  have h1 : 24 ≤ 4 * absoluteZetaTwo * (|t|+6) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4 * absoluteZetaTwo * (|t|+6))
  nlinarith

theorem normalizedDirichlet_zero_re_lt {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) {w : ℂ}
    (hw : normalizedDirichlet chi t w = 0) : w.re < -4/5 := by
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by simp)
  have hz : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) = 0 :=
    (div_eq_zero_iff.mp hw).resolve_right hn
  by_contra! h
  have hr : 1 ≤ (dirichletDiskPoint t w).re := by rw [dirichletDiskPoint_re]; linarith
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) hr hz

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

theorem log_dirichletDiskEnvelope_bound (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (dirichletDiskEnvelope q t) ≤
      (Real.log (4 * absoluteZetaTwo)+1) * (Real.log (q : ℝ)+Real.log (|t|+6)) := by
  have hZ := one_le_absoluteZetaTwo
  have hZp : 0 < 4 * absoluteZetaTwo := by linarith
  have ht := abs_nonneg t
  have htp : 0 < |t|+6 := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqp : (0 : ℝ) < q := by linarith
  have hlogq := Real.log_nonneg hq
  have hlogZ : 0 ≤ Real.log (4 * absoluteZetaTwo) := Real.log_nonneg (by linarith)
  have hlogt : 1 ≤ Real.log (|t|+6) :=
    ((Real.lt_log_iff_exp_lt htp).mpr (Real.exp_one_lt_three.trans (by linarith))).le
  have heq : Real.log (dirichletDiskEnvelope q t) =
      Real.log (4 * absoluteZetaTwo)+Real.log (|t|+6)+(1/2)*Real.log (q : ℝ) := by
    unfold dirichletDiskEnvelope
    rw [Real.log_mul (mul_pos hZp htp).ne' (Real.rpow_pos_of_pos hqp _).ne',
      Real.log_mul hZp.ne' htp.ne', Real.log_rpow hqp]
  rw [heq]
  nlinarith [mul_nonneg hlogZ hlogq, mul_le_mul_of_nonneg_left hlogt hlogZ]

theorem normalizedDirichlet_log_derivative {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) (w : ℂ)
    (hw : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0) :
    deriv (normalizedDirichlet chi t) w / normalizedDirichlet chi t w =
      (5/2:ℂ) * (deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
        DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) := by
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by simp)
  have hp : HasDerivAt (dirichletDiskPoint t) (5/2:ℂ) w := by
    simpa only [dirichletDiskPoint, id_eq, mul_one] using! (((hasDerivAt_id w).const_mul (5/2:ℂ)).const_add (dirichletCenter t))
  have hd := (((DirichletCharacter.differentiable_LFunction hchi).differentiableAt.hasDerivAt).comp w hp).div_const
    (DirichletCharacter.LFunction chi (dirichletCenter t))
  change HasDerivAt (normalizedDirichlet chi t)
    ((deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) * (5/2:ℂ)) /
      DirichletCharacter.LFunction chi (dirichletCenter t)) w at hd
  rw [hd.deriv]
  unfold normalizedDirichlet
  field_simp

theorem uniform_dirichlet_local_log_derivative :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ t : ℝ, ∃ S : Finset ℂ,
        (∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 19/20 ∧
          DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0) ∧
        (∀ rho ∈ S, rho.re < -4/5) ∧
        ∀ w : ℂ, ‖w‖ ≤ 17/20 →
          DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 →
          ‖(5/2:ℂ) * (deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
            DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) -
            ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho)‖ ≤
            C * (Real.log (q : ℝ)+Real.log (|t|+6)) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := exists_local_zero_log_derivative_constant
  have hZ := one_le_absoluteZetaTwo
  have hlogZ : 0 ≤ Real.log (4 * absoluteZetaTwo) := Real.log_nonneg (by linarith)
  refine ⟨C * (Real.log (4 * absoluteZetaTwo)+1), mul_pos hC (by linarith), ?_⟩
  intro q _ chi hchi t
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by simp)
  obtain ⟨S, hS, hb⟩ := hlocal (dirichletDiskEnvelope q t) (dirichletDiskEnvelope_gt_one q t)
    (normalizedDirichlet chi t) (fun w _ => normalizedDirichlet_analytic chi hchi t w)
    (normalizedDirichlet_zero chi t) (fun w hw => normalizedDirichlet_bound chi hchi t
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw))
  have hzeros (rho : ℂ) : normalizedDirichlet chi t rho = 0 ↔
      DirichletCharacter.LFunction chi (dirichletDiskPoint t rho) = 0 := by
    unfold normalizedDirichlet
    exact div_eq_zero_iff.trans (or_iff_left hn)
  refine ⟨S, fun rho => (hS rho).trans (and_congr_right fun _ => hzeros rho), ?_, ?_⟩
  · intro rho hr
    exact normalizedDirichlet_zero_re_lt chi hchi t ((hS rho).mp hr).2
  · intro w hw hne
    have h := hb w hw (fun hz => hne ((hzeros w).mp hz))
    rw [normalizedDirichlet_log_derivative chi hchi t w hne] at h
    apply h.trans
    calc
      _ ≤ C * ((Real.log (4 * absoluteZetaTwo)+1) * (Real.log (q : ℝ)+Real.log (|t|+6))) :=
        mul_le_mul_of_nonneg_left (log_dirichletDiskEnvelope_bound q t) hC.le
      _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

@[simp] theorem dirichletDiskPoint_ofReal (sigma t : ℝ) :
    dirichletDiskPoint t ((2/5*(sigma-3):ℝ):ℂ) = (sigma:ℂ)+(t:ℂ)*Complex.I := by
  unfold dirichletDiskPoint dirichletCenter
  push_cast
  ring

lemma real_zero_term_nonneg {w rho : ℂ} (m : ℕ)
    (h : rho.re ≤ w.re) : 0 ≤ (((m : ℂ) / (w-rho)).re) := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero,
    Complex.sub_re]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h)) (Complex.normSq_nonneg _)

theorem uniform_neg_real_log_derivative :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ sigma t : ℝ, 1 < sigma → sigma ≤ 2 →
      (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
        DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)).re ≤
        C * (Real.log (q:ℝ)+Real.log (|t|+6)) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := uniform_dirichlet_local_log_derivative
  refine ⟨C, hC, ?_⟩
  intro q _ chi hchi sigma t hs hs2
  obtain ⟨S, _, hSre, hb⟩ := hlocal q chi hchi t
  let w : ℂ := ((2/5*(sigma-3):ℝ):ℂ)
  have hw : ‖w‖ ≤ 17/20 := by
    change ‖((2/5*(sigma-3):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwre : -4/5 < w.re := by
    dsimp only [w]
    simp only [Complex.ofReal_re]
    linarith
  have hnonzero : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 := by
    rw [dirichletDiskPoint_ofReal]
    exact LFunction_ne_zero_right chi (by simpa using hs)
  have h := hb w hw hnonzero
  have hsum : 0 ≤ (∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho) : ℂ).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg (fun rho hr => real_zero_term_nonneg _ ((hSre rho hr).le.trans hwre.le))
  have herror := (Complex.re_le_norm (-(
    (5/2:ℂ) * (deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
      DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) -
      ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho)))).trans
    (by simpa only [norm_neg] using h)
  have hscale (a : ℂ) : ((5/2:ℂ)*a).re = (5/2:ℝ)*a.re := by
    norm_num [Complex.mul_re]
  rw [Complex.neg_re, Complex.sub_re, hscale] at herror
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpos : 0 ≤ C * (Real.log (q:ℝ)+Real.log (|t|+6)) :=
    mul_nonneg hC.le (add_nonneg (Real.log_nonneg hq) (Real.log_nonneg (by have := abs_nonneg t; linarith)))
  rw [show (sigma:ℂ)+(t:ℂ)*Complex.I = dirichletDiskPoint t w from (dirichletDiskPoint_ofReal sigma t).symm]
  rw [neg_div, Complex.neg_re]
  nlinarith

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

lemma normalizedDirichlet_zero_order_pos {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) {rho : ℂ}
    (hr : ‖rho‖ ≤ 19/20) (hz : normalizedDirichlet chi t rho = 0) :
    1 ≤ (analyticOrderAt (normalizedDirichlet chi t) rho).toNat := by
  have hf : ∀ w ∈ Metric.closedBall (0:ℂ) 1, AnalyticAt ℂ (normalizedDirichlet chi t) w :=
    fun w _ => normalizedDirichlet_analytic chi hchi t w
  have hfne : normalizedDirichlet chi t 0 ≠ 0 := by rw [normalizedDirichlet_zero]; norm_num
  have hmem : rho ∈ _root_.Erdos970.zerosetKfR (19/20) (by norm_num) (normalizedDirichlet chi t) :=
    ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hr, hz⟩
  have ht := _root_.Erdos970.lem_m_rho_is_nat (39/40) (19/20) (by norm_num) (by norm_num)
    (normalizedDirichlet chi t) hf hfne (by norm_num) rho hmem
  have hge := _root_.Erdos970.lem_m_rho_ge_1 (39/40) (19/20) (by norm_num) (by norm_num)
    (normalizedDirichlet chi t) hf hfne (by norm_num) rho hmem
  simpa using ENat.toNat_le_toNat hge ht

theorem uniform_zero_penalty :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ sigma beta t : ℝ,
      1 < sigma → sigma ≤ 2 → 3/4 ≤ beta → beta < 1 →
      DirichletCharacter.LFunction chi ((beta:ℂ)+(t:ℂ)*Complex.I) = 0 →
      (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
        DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)).re ≤
        C * (Real.log (q:ℝ)+Real.log (|t|+6)) - 1/(sigma-beta) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := uniform_dirichlet_local_log_derivative
  refine ⟨C, hC, ?_⟩
  intro q _ chi hchi sigma beta t hs hs2 hb34 hb1 hzero
  obtain ⟨S, hS, hSre, hbound⟩ := hlocal q chi hchi t
  let w : ℂ := ((2/5*(sigma-3):ℝ):ℂ)
  let rho0 : ℂ := ((2/5*(beta-3):ℝ):ℂ)
  have hw : ‖w‖ ≤ 17/20 := by
    change ‖((2/5*(sigma-3):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hr : ‖rho0‖ ≤ 19/20 := by
    change ‖((2/5*(beta-3):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwre : -4/5 < w.re := by
    dsimp only [w]
    simp only [Complex.ofReal_re]
    linarith
  have hrL : DirichletCharacter.LFunction chi (dirichletDiskPoint t rho0) = 0 := by
    rw [dirichletDiskPoint_ofReal]
    exact hzero
  have hrmem : rho0 ∈ S := (hS rho0).mpr ⟨hr, hrL⟩
  have hrNorm : normalizedDirichlet chi t rho0 = 0 := by
    unfold normalizedDirichlet
    rw [hrL, zero_div]
  have hm := normalizedDirichlet_zero_order_pos chi hchi t hr hrNorm
  have hden : 0 < sigma-beta := by linarith
  have hsub : w-rho0 = ((2/5*(sigma-beta):ℝ):ℂ) := by
    dsimp only [w, rho0]
    push_cast
    ring
  have hterm : (5/2:ℝ)/(sigma-beta) ≤
      (((analyticOrderAt (normalizedDirichlet chi t) rho0).toNat:ℂ)/(w-rho0)).re := by
    rw [hsub]
    rw [show ((analyticOrderAt (normalizedDirichlet chi t) rho0).toNat:ℂ) =
      (((analyticOrderAt (normalizedDirichlet chi t) rho0).toNat:ℝ):ℂ) by simp]
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    calc
      _ = 1/(2/5*(sigma-beta)) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hm) (by positivity)
  have hsum : (5/2:ℝ)/(sigma-beta) ≤
      (∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho):ℂ).re := by
    rw [Complex.re_sum]
    apply hterm.trans
    exact Finset.single_le_sum (fun rho hr => real_zero_term_nonneg (analyticOrderAt (normalizedDirichlet chi t) rho).toNat ((hSre rho hr).le.trans hwre.le)) hrmem
  have hn : DirichletCharacter.LFunction chi (dirichletDiskPoint t w) ≠ 0 := by
    rw [dirichletDiskPoint_ofReal]
    exact LFunction_ne_zero_right chi (by simpa using hs)
  have h := hbound w hw hn
  have herror := (Complex.re_le_norm (-(
    (5/2:ℂ) * (deriv (DirichletCharacter.LFunction chi) (dirichletDiskPoint t w) /
      DirichletCharacter.LFunction chi (dirichletDiskPoint t w)) -
      ∑ rho ∈ S, (analyticOrderAt (normalizedDirichlet chi t) rho).toNat / (w-rho)))).trans
    (by simpa only [norm_neg] using h)
  have hscale (a:ℂ) : ((5/2:ℂ)*a).re = (5/2:ℝ)*a.re := by norm_num [Complex.mul_re]
  rw [Complex.neg_re, Complex.sub_re, hscale] at herror
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpos : 0 ≤ C*(Real.log (q:ℝ)+Real.log (|t|+6)) :=
    mul_nonneg hC.le (add_nonneg (Real.log_nonneg hq) (Real.log_nonneg (by have := abs_nonneg t; linarith)))
  rw [show (sigma:ℂ)+(t:ℂ)*Complex.I = dirichletDiskPoint t w from (dirichletDiskPoint_ofReal sigma t).symm,
    neg_div, Complex.neg_re]
  rw [div_eq_mul_inv] at hsum
  rw [one_div]
  nlinarith only [herror, hsum, hpos]

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
