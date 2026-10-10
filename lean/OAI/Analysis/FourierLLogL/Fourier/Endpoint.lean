import OAI.Analysis.Fourier.HeightLayers

/-! # Deduction of the L log L theorem from a good set estimate -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace OAI

namespace FourierLLogL

def symmetricMaximal (f : Torus → ℂ) (x : Torus) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal ‖symmetricPartialSum f N x‖

theorem measurable_symmetricMaximal (f : Torus → ℂ) : Measurable (symmetricMaximal f) :=
  Measurable.iSup (fun N => (measurable_symmetricPartialSum f N).norm.ennreal_ofReal)

theorem symmetricMaximal_mul (f : Torus → ℂ) (c : ℂ) (x : Torus) :
    symmetricMaximal (fun y => c * f y) x = ENNReal.ofReal ‖c‖ * symmetricMaximal f x := by
  simp only [symmetricMaximal, symmetricPartialSum_const_mul, norm_mul,
    ENNReal.ofReal_mul (norm_nonneg c), ENNReal.mul_iSup]

/-- Good-set estimate. We state it at exponential heights exp d with d = 2^j. -/
def GoodBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop, ∀ (f : Torus → ℂ),
    Integrable f circleMeasure → (∫ x, ‖f x‖ ∂circleMeasure) ≤ 1 →
    (∀ᵐ x ∂circleMeasure, ‖f x‖ ≤ Real.exp ((2 : ℝ)^j)) →
    ∃ G : Set Torus, MeasurableSet G ∧
      circleMeasure Gᶜ ≤ ENNReal.ofReal (C / ((j:ℝ) + 1)^2) ∧
      (∫⁻ x in G, symmetricMaximal f x ∂circleMeasure) ≤ ENNReal.ofReal (C * (2:ℝ)^j)

/-- Transfer the good-set estimates to summable pointwise majorants for a sequence.
Finitely many terms per point may not have been bounded. We include the untransformed term
for use with approximations. -/
theorem GoodBound.ae_tail_majorant
    (hgb : GoodBound) (F : ℕ → Torus → ℂ) (w : ℕ → ℝ) (L : ℕ)
    (hF : ∀ j, Integrable (F j) circleMeasure)
    (hw : ∀ j, 0 < w j)
    (hsum : Summable (fun j => (2:ℝ)^j * w j))
    (hm : ∀ j, (∫ x, ‖F j x‖ ∂circleMeasure) ≤ w j)
    (hh : ∀ j, ∀ᵐ x ∂circleMeasure, ‖F j x‖ ≤ w j * Real.exp ((2:ℝ)^(j+L))) :
    ∀ᵐ x ∂circleMeasure, ∃ b : ℕ → ℝ, Summable b ∧ ∀ᶠ j : ℕ in atTop,
      ∀ N, ‖symmetricPartialSum (F j) N x‖ + ‖F j x‖ ≤ b j := by
  classical
  obtain ⟨C, hC, hG⟩ := hgb
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hG
  let D := L + j₀
  have hg (j : ℕ) : ∃ G : Set Torus, MeasurableSet G ∧
      circleMeasure Gᶜ ≤ ENNReal.ofReal (C / ((j:ℝ) + 1)^2) ∧
      (∫⁻ x in G, symmetricMaximal (F j) x ∂circleMeasure)
        ≤ ENNReal.ofReal (w j * (C * (2:ℝ)^(j+D))) := by
    let f (x : Torus) : ℂ := (((w j)⁻¹ : ℝ) : ℂ) * F j x
    have winv : 0 < (w j)⁻¹ := inv_pos.mpr (hw j)
    have hf (x : Torus) : ‖f x‖ = (w j)⁻¹ * ‖F j x‖ := by
      simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos winv]
    have hnorm : (∫ x, ‖f x‖ ∂circleMeasure) ≤ 1 := by
      simp_rw [hf]
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left (hm j) winv.le).trans (le_of_eq (inv_mul_cancel₀ (hw j).ne'))
    have hheight : ∀ᵐ x ∂circleMeasure, ‖f x‖ ≤ Real.exp ((2:ℝ)^(j+D)) := by
      filter_upwards [hh j] with x hx
      calc
        ‖f x‖ = (w j)⁻¹ * ‖F j x‖ := hf x
        _ ≤ (w j)⁻¹ * (w j * Real.exp ((2:ℝ)^(j+L))) :=
          mul_le_mul_of_nonneg_left hx winv.le
        _ = Real.exp ((2:ℝ)^(j+L)) := by field_simp [(hw j).ne']
        _ ≤ Real.exp ((2:ℝ)^(j+D)) := Real.exp_monotone
          (pow_le_pow_right₀ (by norm_num) (by dsimp [D]; omega))
    obtain ⟨G, hs, hsize, hi⟩ := hj₀ (j+D) (by dsimp [D]; omega) f ((hF j).const_mul _) hnorm
      hheight
    refine ⟨G, hs, hsize.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
    · apply div_le_div_of_nonneg_left hC (by positivity)
      gcongr
      simp
    have heq : F j = (fun x => ((w j : ℝ) : ℂ) * f x) := by
      ext1 x
      dsimp [f]
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hw j).ne',
        Complex.ofReal_one, one_mul]
    rw [heq]
    simp_rw [symmetricMaximal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw j)]
    rw [lintegral_const_mul _ (measurable_symmetricMaximal f), ENNReal.ofReal_mul (hw j).le]
    exact mul_le_mul_right hi _
  choose G hGm hGsize hGi using hg
  have hCs : Summable (fun j : ℕ => C / ((j:ℝ)+1)^2) := by
    have hh : Summable (fun n : ℕ => 1 / ((n+1:ℕ):ℝ)^2) :=
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
    simpa [div_eq_mul_inv] using hh.mul_left C
  have hcompl : (∑' j, circleMeasure (G j)ᶜ) ≠ ∞ := by
    apply ne_of_lt
    refine (ENNReal.tsum_le_tsum hGsize).trans_lt ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg _ hCs]
    · exact ENNReal.ofReal_lt_top
    · intro n; positivity
  let M (j : ℕ) (x : Torus) :=
    (G j).indicator (symmetricMaximal (F j)) x + ENNReal.ofReal ‖F j x‖
  have hM (j : ℕ) : AEMeasurable (M j) circleMeasure :=
    (((measurable_symmetricMaximal _).indicator (hGm _)).aemeasurable).add
      ((hF j).norm.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have ht : ∫⁻ x, (∑' j, M j x) ∂circleMeasure ≠ ∞ := by
    have hhM (j : ℕ) : (∫⁻ x, M j x ∂circleMeasure)
          ≤ ENNReal.ofReal (w j * (C * (2:ℝ)^(j+D)) + w j) := by
      dsimp only [M]
      rw [lintegral_add_left ((measurable_symmetricMaximal _).indicator (hGm _)),
        lintegral_indicator (hGm j),
        ← ofReal_integral_eq_lintegral_ofReal (hF j).norm
          (ae_of_all _ fun x => norm_nonneg _),
        ENNReal.ofReal_add (by have := hw j; positivity) (hw j).le]
      exact add_le_add (hGi j) (ENNReal.ofReal_le_ofReal (hm j))
    rw [lintegral_tsum hM]
    apply ne_of_lt
    refine (ENNReal.tsum_le_tsum hhM).trans_lt ?_
    have hwS : Summable w := hsum.of_nonneg_of_le (fun n => (hw n).le) (fun n =>
      le_mul_of_one_le_left (hw n).le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)))
    have hfull : Summable (fun j => w j * (C * (2:ℝ)^(j+D)) + w j) :=
      ((hsum.mul_left (C*(2:ℝ)^D)).add hwS).congr fun n => by
        simp only [pow_add]
        ring
    rw [← ENNReal.ofReal_tsum_of_nonneg _ hfull]
    · exact ENNReal.ofReal_lt_top
    · intro n; have := hw n; positivity
  filter_upwards [ae_eventually_notMem hcompl, ae_lt_top' (AEMeasurable.tsum hM) ht] with x hx hx'
  refine ⟨fun n => (M n x).toReal, ENNReal.summable_toReal hx'.ne, ?_⟩
  filter_upwards [hx] with j hj
  intro N
  have hmn := ENNReal.ne_top_of_tsum_ne_top hx'.ne j
  rw [← ENNReal.toReal_ofReal
    (add_nonneg (norm_nonneg (symmetricPartialSum _ _ _)) (norm_nonneg _))]
  apply ENNReal.toReal_mono hmn
  simp only [M, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  have : x ∈ G j := by simpa using hj
  rw [Set.indicator_of_mem this]
  exact add_le_add_left (le_iSup (fun N => ENNReal.ofReal ‖symmetricPartialSum (F j) N x‖) N) _

/-- Trigonometric polynomials, as a subspace of continuous functions. -/
def trigPolys : Submodule ℂ C(Torus, ℂ) := Submodule.span ℂ (Set.range fourier)

lemma integrable_continuous {f : Torus → ℂ} (hf : Continuous f) :
    Integrable f circleMeasure := by
  apply hf.integrable_of_hasCompactSupport
  exact IsClosed.isCompact (isClosed_tsupport f)

theorem eventually_partialSum_trigPoly {p : C(Torus, ℂ)} (h : p ∈ trigPolys) :
    ∀ᶠ N : ℕ in atTop, ∀ x, symmetricPartialSum p N x = p x := by
  induction h using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k, rfl⟩ := hp
    filter_upwards [eventually_ge_atTop k.natAbs] with N hN
    intro x
    simp only [symmetricPartialSum, fourierCoeff_fourier]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hk
      exfalso
      apply hk
      simp only [Finset.mem_Icc]
      omega
  | zero => filter_upwards with N x using symmetricPartialSum_zero N x
  | add p q _ _ hp hq =>
    filter_upwards [hp, hq] with N hpN hqN
    intro x
    change symmetricPartialSum ((p : Torus → ℂ) + (q : Torus → ℂ)) N x = p x + q x
    rw [symmetricPartialSum_add (integrable_continuous p.continuous)
      (integrable_continuous q.continuous), hpN x, hqN x]
  | smul c p _ hp =>
    filter_upwards [hp] with N hpN
    intro x
    change symmetricPartialSum (fun y => c * p y) N x = c * p x
    rw [symmetricPartialSum_const_mul, hpN x]

lemma exists_bounded_trigPoly_approx (f : Torus → ℂ)
    (hf : Integrable f circleMeasure)
    (B : ℝ) (hB : 0 < B) (hb : ∀ᵐ x ∂circleMeasure, ‖f x‖ ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : C(Torus, ℂ), p ∈ trigPolys ∧
      (∫ x, ‖f x - p x‖ ∂circleMeasure) ≤ ε ∧ ∀ x, ‖p x‖ ≤ B + 1 := by
  obtain ⟨g, hg, hgi⟩ :=
    hf.exists_boundedContinuous_integral_sub_le (show 0 < ε/4 by linarith)
  let k (x : Torus) : ℂ := (B / max B ‖g x‖) • g x
  have hk : Continuous k := by
    have h1 : Continuous fun x => max B ‖g x‖ := continuous_const.max g.continuous.norm
    exact (continuous_const.div h1 (fun x => ne_of_gt (lt_max_of_lt_left hB))).smul g.continuous
  let k' : C(Torus, ℂ) := ⟨k, hk⟩
  have hkB (x : Torus) : ‖k x‖ ≤ B := by
    have hm : 0 < max B ‖g x‖ := lt_max_of_lt_left hB
    simp only [k, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hB hm)]
    exact (mul_le_mul_of_nonneg_left (le_max_right B ‖g x‖) (div_pos hB hm).le).trans
      (div_mul_cancel₀ B hm.ne').le
  have hdk (x : Torus) (hx : ‖f x‖ ≤ B) : ‖f x - k x‖ ≤ 2 * ‖f x - g x‖ := by
    suffices H : ‖g x - k x‖ ≤ ‖f x - g x‖ by
      have hi := dist_triangle (f x) (g x) (k x)
      simp only [dist_eq_norm] at hi
      linarith
    rcases le_total ‖g x‖ B with hxg | hxg
    · simp [k, max_eq_left hxg, hB.ne']
    have hp : 0 < ‖g x‖ := hB.trans_le hxg
    have hxone : (0:ℝ) ≤ 1 - B/‖g x‖ := sub_nonneg.mpr ((div_le_one hp).mpr hxg)
    calc
      ‖g x - k x‖ = ‖((1:ℝ)-B/‖g x‖) • g x‖ := by
        rw [sub_smul, one_smul]; simp only [k, max_eq_right hxg]
      _ = ‖g x‖ - B := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hxone, sub_mul, one_mul,
          div_mul_cancel₀ B hp.ne']
      _ ≤ ‖g x‖ - ‖f x‖ := sub_le_sub_left hx _
      _ ≤ ‖f x - g x‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  have hkc : k' ∈ closure (trigPolys : Set _) := by
    change k' ∈ trigPolys.topologicalClosure
    rw [trigPolys, span_fourier_closure_eq_top]; trivial
  obtain ⟨p, hps, hp⟩ := Metric.mem_closure_iff.mp hkc (min 1 (ε / 2)) (by positivity)
  have hp' (x : Torus) : ‖k x - p x‖ < min 1 (ε / 2) := by
    change ‖k' x - p x‖ < _
    rw [← dist_eq_norm]
    exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist _) hp
  refine ⟨p, hps, ?_, fun x => ?_⟩
  · calc
      _ ≤ ∫ x, (2 * ‖f x - g x‖ + (ε / 2)) ∂circleMeasure := by
        apply integral_mono_ae (hf.sub (integrable_continuous p.continuous)).norm
          (((hf.sub hgi).norm.const_mul _).add (integrable_const _))
        filter_upwards [hb] with x hx
        have h1 := dist_triangle (f x) (k x) (p x)
        simp only [dist_eq_norm] at h1
        exact h1.trans (add_le_add (hdk x hx)
          ((hp' x).le.trans (min_le_right _ _)))
      _ = 2 * (∫ x, ‖f x - g x‖ ∂circleMeasure) + (ε/2) := by
        rw [integral_add (show Integrable (fun x => 2 * ‖f x - g x‖) _ from ((hf.sub hgi).norm.const_mul _)) (integrable_const _),
          integral_const_mul]; simp
      _ ≤ ε := by linarith
  · have h1 := norm_sub_norm_le (p x) (k x)
    rw [norm_sub_rev] at h1
    have h2 := ((hp' x).le.trans (min_le_left _ _))
    linarith [hkB x]


private def pad (j : ℕ) : ℝ := ((1/4:ℝ))^j

private lemma pad_pos (j) : 0 < pad j := by unfold pad; positivity

private lemma summable_pad : Summable (fun j => (2:ℝ)^j * pad j) := by
  simp only [pad, ← mul_pow]
  exact summable_geometric_of_norm_lt_one (by norm_num)


private lemma pad_height (j : ℕ) :
    Real.exp ((2:ℝ)^(j+2)) ≤ pad j * Real.exp ((2:ℝ)^(j+4)) := by
  have hj : (j:ℝ) ≤ (2:ℝ)^j := by exact_mod_cast (Nat.lt_two_pow_self (n:=j)).le
  have hex : (4:ℝ)^j ≤ Real.exp ((3:ℝ) * j) := by
    have h3 := Real.add_one_le_exp 3
    rw [mul_comm 3, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num at h3; linarith) _
  have Hmul : (4:ℝ)^j * Real.exp ((2:ℝ)^(j+2)) ≤ Real.exp ((2:ℝ)^(j+4)) := by
    refine (mul_le_mul_of_nonneg_right hex (Real.exp_nonneg _)).trans ?_
    rw [← Real.exp_add]
    apply Real.exp_monotone
    simp only [pow_add]
    linarith
  simp only [pad, one_div, inv_pow, ← div_eq_inv_mul]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<4^j)).mpr
  rw [mul_comm]
  exact Hmul

theorem GoodBound.ae_convergence_bounded (hgb : GoodBound) (f : Torus → ℂ)
    (hf : Integrable f circleMeasure) (B : ℝ) (hB : 0 < B)
    (hb : ∀ᵐ x ∂circleMeasure, ‖f x‖ ≤ B) :
    ∀ᵐ x ∂circleMeasure, Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x)) := by
  choose p hp hm hpB using
    (fun j => exists_bounded_trigPoly_approx f hf B hB hb (pad j) (pad_pos j))
  let F (j : ℕ) (x : Torus) : ℂ := f x - p j x
  have hFi (j) : Integrable (F j) circleMeasure :=
    hf.sub (integrable_continuous (p j).continuous)
  let w (j : ℕ) : ℝ := (2*B+1) * pad j
  have hw (j) : 0 < w j := mul_pos (by linarith) (pad_pos _)
  have hs : Summable fun j => (2:ℝ)^j * w j :=
    (summable_pad.mul_left (2*B+1)).congr fun j => by dsimp only [w]; ring
  have hmw (j) : (∫ x, ‖F j x‖ ∂circleMeasure) ≤ w j :=
    (hm j).trans (le_mul_of_one_le_left (pad_pos j).le (by linarith))
  have hheight (j) : ∀ᵐ x ∂circleMeasure, ‖F j x‖ ≤ w j * Real.exp ((2:ℝ)^(j+4)) := by
    filter_upwards [hb] with x hx
    calc
      ‖F j x‖ ≤ ‖f x‖ + ‖p j x‖ := norm_sub_le _ _
      _ ≤ (2*B+1)*Real.exp ((2:ℝ)^(j+2)) := by
        have := hpB j x
        have : 1 ≤ Real.exp ((2:ℝ)^(j+2)) := Real.one_le_exp (by positivity)
        nlinarith
      _ ≤ w j * Real.exp ((2:ℝ)^(j+4)) := by
        dsimp only [w]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (pad_height j) (by linarith)
  filter_upwards [hgb.ae_tail_majorant F w 4 hFi hw hs hmw hheight] with x hx
  obtain ⟨b, hsum, hmaj⟩ := hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj, hj'⟩ :=
    (hmaj.and (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds hε))).exists
  filter_upwards [eventually_partialSum_trigPoly (hp j)] with N hN
  have hfdecomp : f = F j + (p j : Torus → ℂ) := by ext; simp [F]
  calc
    dist (symmetricPartialSum f N x) (f x)
        = ‖symmetricPartialSum (F j) N x - F j x‖ := by
          nth_rw 1 2 [hfdecomp]
          rw [symmetricPartialSum_add (hFi j) (integrable_continuous (p j).continuous),
            hN x, dist_eq_norm]
          simp only [Pi.add_apply, add_sub_add_right_eq_sub]
    _ ≤ ‖symmetricPartialSum (F j) N x‖ + ‖F j x‖ := norm_sub_le _ _
    _ ≤ b j := hj N
    _ < ε := hj'

theorem GoodBound.main_bound_consequence (hgb : GoodBound)
    {f : Torus → ℂ} (hf : MemLLogL f) :
    ∃ E : Set Torus, MeasurableSet E ∧ circleMeasure E = 0 ∧ ∀ x ∉ E,
      Tendsto (fun N : ℕ ↦ symmetricPartialSum f N x) atTop (𝓝 (f x)) := by
  classical
  let w (j : ℕ) := heightLayerMass f j + pad j
  have hw (j : ℕ) : 0 < w j :=
    add_pos_of_nonneg_of_pos (heightLayerMass_nonneg f _) (pad_pos _)
  have hs : Summable (fun j => (2:ℝ)^j * w j) := by
    have hs' := hf.summable_weighted_heightLayerMass.mul_left ((1:ℝ)/2)
    refine (hs'.add summable_pad).congr ?_
    intro j
    dsimp only [w]
    rw [pow_succ]; ring
  have hm (j) : (∫ x, ‖heightLayer f j x‖ ∂circleMeasure) ≤ w j := by
    rw [← heightLayerMass_eq_integral_norm hf]
    apply le_add_of_nonneg_right
    exact (pad_pos j).le
  have hh (j) : ∀ᵐ x ∂circleMeasure,
      ‖heightLayer f j x‖ ≤ w j * Real.exp ((2:ℝ)^(j+4)) := by
    refine ae_of_all _ fun x => ((norm_heightLayer_le f j x).trans (pad_height j)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (heightLayerMass_nonneg _ _)) (Real.exp_nonneg _)
  have hbConv := hgb.ae_convergence_bounded _ hf.boundedPart_integrable _
    (Real.exp_pos _) (ae_of_all _ (norm_boundedPart_le f))
  have hConv (j) := hgb.ae_convergence_bounded _ (hf.heightLayer_integrable j) _
    (Real.exp_pos _) (ae_of_all _ (norm_heightLayer_le f j))
  apply exists_measurable_null_of_ae
  filter_upwards [hbConv, ae_all_iff.mpr hConv,
    hgb.ae_tail_majorant _ w 4 hf.heightLayer_integrable hw hs hm hh] with x hb hc hx
  obtain ⟨b, hsum, hmaj⟩ := hx
  obtain ⟨k, hk⟩ := eventually_atTop.1 hmaj
  have hbd (j : ℕ) : BddAbove (Set.range
      (fun N : ℕ => ‖symmetricPartialSum (heightLayer f j) N x‖)) :=
    ((hc j).norm).bddAbove_range
  choose r hr using hbd
  let b' (j : ℕ) := if j < k then r j else b j
  have hs' : Summable b' := by
    apply (summable_nat_add_iff k).mp
    have hh := (summable_nat_add_iff k).mpr hsum
    simpa [b'] using hh
  have hmaj' (j N) : ‖symmetricPartialSum (heightLayer f j) N x‖ ≤ b' j := by
    dsimp [b']
    split_ifs with H
    · exact hr j (Set.mem_range_self N)
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hk j (by omega) N)
  have ht := tendsto_tsum_of_dominated_convergence hs' hc
    (Eventually.of_forall fun N j => hmaj' j N)
  have h := hb.add ht

  simpa only [hf.symmetricPartialSum_heightDecomposition, boundedPart_add_tsum_heightLayer] using h

end FourierLLogL

end OAI
