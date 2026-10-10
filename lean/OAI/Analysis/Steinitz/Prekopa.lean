import OAI.Analysis.Steinitz.HeatEnergy

namespace OAI

/-! Prékopa inequalities and Gaussian log-concavity. -/

section

open MeasureTheory Set Filter
open scoped Topology

namespace Prekopa

lemma continuousAt_invFun_strictMono {F : ℝ → ℝ} (hF : Continuous F)
    (hmono : StrictMono F) (x : ℝ) : ContinuousAt (Function.invFun F) (F x) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hl : F (x - ε) < F x := hmono (by linarith)
  have hr : F x < F (x + ε) := hmono (by linarith)
  refine ⟨min (F x - F (x - ε)) (F (x + ε) - F x), lt_min (by linarith) (by linarith), ?_⟩
  intro y hy
  obtain ⟨hy₁, hy₂⟩ := abs_lt.mp (show |y - F x| < _ from hy)
  have hyI : y ∈ Icc (F (x - ε)) (F (x + ε)) := by
    constructor
    · have := min_le_left (F x - F (x - ε)) (F (x + ε) - F x); linarith
    · have := min_le_right (F x - F (x - ε)) (F (x + ε) - F x); linarith
  obtain ⟨z, _, hz⟩ := intermediate_value_Icc (show x - ε ≤ x + ε by linarith)
    hF.continuousOn hyI
  have he : F (Function.invFun F y) = y := by rw [← hz]; exact Function.apply_invFun_apply
  rw [Function.leftInverse_invFun hmono.injective x]
  change |Function.invFun F y - x| < ε
  rw [abs_lt]
  constructor
  · have : F (x - ε) < y := by
      have := min_le_left (F x - F (x - ε)) (F (x + ε) - F x); linarith
    have : x - ε < Function.invFun F y := hmono.lt_iff_lt.mp (he.symm ▸ this)
    linarith
  · have : y < F (x + ε) := by
      have := min_le_right (F x - F (x - ε)) (F (x + ε) - F x); linarith
    have : Function.invFun F y < x + ε := hmono.lt_iff_lt.mp (he.symm ▸ this)
    linarith

lemma invFun_hasDerivAt {F : ℝ → ℝ} (hF : Continuous F) (hmono : StrictMono F)
    (x d : ℝ) (hd : d ≠ 0) (hder : HasDerivAt F d x) :
    HasDerivAt (Function.invFun F) d⁻¹ (F x) := by
  apply HasDerivAt.of_local_left_inverse (continuousAt_invFun_strictMono hF hmono x)
    (by simpa [Function.leftInverse_invFun hmono.injective x] using hder) hd
  have hl : F (x - 1) < F x := hmono (by linarith)
  have hr : F x < F (x + 1) := hmono (by linarith)
  filter_upwards [Ioo_mem_nhds hl hr] with y hy
  obtain ⟨z, _, hz⟩ := intermediate_value_Icc (show x - 1 ≤ x + 1 by linarith)
    hF.continuousOn ⟨hy.1.le, hy.2.le⟩
  exact by rw [← hz]; exact Function.apply_invFun_apply

noncomputable def primitive (f : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ := ∫ t in a..x, f t

lemma primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (primitive f a) (f x) x := by
  exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt

lemma primitive_continuous {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Continuous (primitive f a) :=
  continuous_iff_continuousAt.mpr fun x => (primitive_hasDerivAt hf a x).continuousAt

lemma primitive_strictMono {f : ℝ → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (a : ℝ) : StrictMono (primitive f a) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(primitive_hasDerivAt hf a x).deriv]
  exact hpos x

lemma normalized_interval {f g h : ℝ → ℝ} {a b α : ℝ}
    (hab : a < b) (hα : α ∈ Icc (0 : ℝ) 1)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfpos : ∀ x, 0 < f x) (hgpos : ∀ x, 0 < g x)
    (hfi : ∫ x in a..b, f x = 1) (hgi : ∫ x in a..b, g x = 1)
    (hfg : ∀ x y, f x ^ (1-α) * g y ^ α ≤ h ((1-α)*x+α*y)) :
    1 ≤ ∫ x in a..b, h x := by
  let F := primitive f a
  let G := primitive g a
  let T (x : ℝ) := Function.invFun G (F x)
  have hFc : Continuous F := primitive_continuous hf a
  have hGc : Continuous G := primitive_continuous hg a
  have hFm : StrictMono F := primitive_strictMono hf hfpos a
  have hGm : StrictMono G := primitive_strictMono hg hgpos a
  have hFa : F a = 0 := by simp [F, primitive]
  have hGa : G a = 0 := by simp [G, primitive]
  have hFb : F b = 1 := hfi
  have hGb : G b = 1 := hgi
  have hGT (x : ℝ) (hx : x ∈ Icc a b) : G (T x) = F x := by
    have hFx : F x ∈ Icc (G a) (G b) := by
      rw [hGa, hGb, ← hFa, ← hFb]
      exact ⟨hFm.monotone hx.1, hFm.monotone hx.2⟩
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc hab.le hGc.continuousOn hFx
    dsimp [T]
    rw [← hz]
    exact Function.apply_invFun_apply
  have hTi (x : ℝ) (hx : x ∈ Icc a b) : T x ∈ Icc a b := by
    have he := hGT x hx
    constructor
    · apply hGm.le_iff_le.mp
      rw [he, hGa, ← hFa]
      exact hFm.monotone hx.1
    · apply hGm.le_iff_le.mp
      rw [he, hGb, ← hFb]
      exact hFm.monotone hx.2
  have hTd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt T (f x / g (T x)) x := by
    have hi := invFun_hasDerivAt hGc hGm (T x) (g (T x))
      (ne_of_gt (hgpos _)) (primitive_hasDerivAt hg a (T x))
    rw [hGT x hx] at hi
    convert! hi.comp x (primitive_hasDerivAt hf a x) using 1;
      simp [T, div_eq_mul_inv, mul_comm]
  have hTc : ContinuousOn T (Icc a b) := fun x hx => (hTd x hx).continuousAt.continuousWithinAt
  have hTa : T a = a := by apply hGm.injective; rw [hGT a ⟨le_rfl, hab.le⟩, hFa, hGa]
  have hTb : T b = b := by apply hGm.injective; rw [hGT b ⟨hab.le, le_rfl⟩, hFb, hGb]
  let Z (x : ℝ) := (1-α)*x+α*T x
  let Z' (x : ℝ) := (1-α)+α*(f x / g (T x))
  have hZd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt Z (Z' x) x := by
    convert! ((hasDerivAt_id x).const_mul (1-α)).add ((hTd x hx).const_mul α) using 1;
      simp [Z']
  have hZc : ContinuousOn Z' (Icc a b) := by
    apply ContinuousOn.add continuousOn_const
    exact continuousOn_const.mul (hf.continuousOn.div (hg.comp_continuousOn hTc)
      (fun x _ => ne_of_gt (hgpos _)))
  have hsubst := intervalIntegral.integral_comp_mul_deriv' (a := a) (b := b) (g := h) (fun x hx =>
    hZd x (by simpa [uIcc_of_le hab.le] using hx))
    (by simpa [uIcc_of_le hab.le] using hZc) hh.continuousOn
  have hZa : Z a = a := by dsimp [Z]; rw [hTa]; ring
  have hZb : Z b = b := by dsimp [Z]; rw [hTb]; ring
  rw [hZa, hZb] at hsubst
  rw [← hsubst, ← hfi]
  apply intervalIntegral.integral_mono_on hab.le (hf.intervalIntegrable _ _)
    ((hh.comp_continuousOn (fun x hx => (hZd x hx).continuousAt.continuousWithinAt)).mul hZc
      |>.intervalIntegrable_of_Icc hab.le)
  intro x hx
  have hp : 0 < f x / g (T x) := div_pos (hfpos _) (hgpos _)
  have hmean := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ 1-α by linarith [hα.2]) hα.1 (show (0:ℝ) ≤ 1 by norm_num) hp.le
    (show (1-α)+α=1 by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at hmean
  have hZpos : 0 ≤ Z' x := le_trans (Real.rpow_nonneg hp.le _) hmean
  calc
    f x = (f x ^ (1-α) * g (T x) ^ α) * ((f x / g (T x)) ^ α) := by
      rw [Real.div_rpow (hfpos _).le (hgpos _).le]
      have hg0 : g (T x) ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (hgpos _) _)
      field_simp
      rw [← Real.rpow_add (hfpos _)]
      simp
    _ ≤ (f x ^ (1-α) * g (T x) ^ α) * Z' x :=
      mul_le_mul_of_nonneg_left hmean (mul_nonneg
        (Real.rpow_nonneg (hfpos _).le _) (Real.rpow_nonneg (hgpos _).le _))
    _ ≤ (h ∘ Z) x * Z' x := mul_le_mul_of_nonneg_right (hfg x (T x)) hZpos

lemma interval {f g h : ℝ → ℝ} {a b α : ℝ}
    (hab : a < b) (hα : α ∈ Icc (0 : ℝ) 1)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfpos : ∀ x, 0 < f x) (hgpos : ∀ x, 0 < g x)
    (hfg : ∀ x y, f x ^ (1-α) * g y ^ α ≤ h ((1-α)*x+α*y)) :
    (∫ x in a..b, f x) ^ (1-α) * (∫ x in a..b, g x) ^ α ≤ ∫ x in a..b, h x := by
  let p := ∫ x in a..b, f x
  let q := ∫ x in a..b, g x
  have hp : 0 < p := intervalIntegral.integral_pos hab hf.continuousOn
    (fun x _ => (hfpos x).le) ⟨a, ⟨le_rfl, hab.le⟩, hfpos a⟩
  have hq : 0 < q := intervalIntegral.integral_pos hab hg.continuousOn
    (fun x _ => (hgpos x).le) ⟨a, ⟨le_rfl, hab.le⟩, hgpos a⟩
  let c := p ^ (1-α) * q ^ α
  have hc : 0 < c := mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hq _)
  have he := normalized_interval hab hα (hf.div_const p) (hg.div_const q) (hh.div_const c)
    (fun x => div_pos (hfpos x) hp) (fun x => div_pos (hgpos x) hq)
    (by rw [intervalIntegral.integral_div]; exact div_self (ne_of_gt hp))
    (by rw [intervalIntegral.integral_div]; exact div_self (ne_of_gt hq))
    (fun x y => by
      rw [Real.div_rpow (hfpos x).le hp.le, Real.div_rpow (hgpos y).le hq.le]
      rw [div_mul_div_comm]
      exact div_le_div_of_nonneg_right (hfg x y) hc.le)
  rw [intervalIntegral.integral_div] at he
  have he' := (le_div_iff₀ hc).mp he
  simpa only [one_mul] using he'

lemma real {f g h : ℝ → ℝ} {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfpos : ∀ x, 0 < f x) (hgpos : ∀ x, 0 < g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hfg : ∀ x y, f x ^ (1-α) * g y ^ α ≤ h ((1-α)*x+α*y)) :
    (∫ x, f x) ^ (1-α) * (∫ x, g x) ^ α ≤ ∫ x, h x := by
  have hfl := intervalIntegral_tendsto_integral hfi tendsto_neg_atTop_atBot tendsto_id
  have hgl := intervalIntegral_tendsto_integral hgi tendsto_neg_atTop_atBot tendsto_id
  have hhl := intervalIntegral_tendsto_integral hhi tendsto_neg_atTop_atBot tendsto_id
  apply le_of_tendsto_of_tendsto
    ((hfl.rpow_const (Or.inr (by linarith [hα.2]))).mul
      (hgl.rpow_const (Or.inr hα.1))) hhl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact interval (show -R < R by linarith) hα hf hg hh hfpos hgpos hfg

end Prekopa

namespace Prekopa
open MeasureTheory Set Filter
open scoped Topology

noncomputable def gauss {n : ℕ} (c : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-c * ∑ i, (x i)^2)

lemma gauss_prod {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    gauss c x = ∏ i, Real.exp (-c * (x i)^2) := by
  rw [gauss, ← Real.exp_sum, Finset.mul_sum]

lemma gauss_cons {n : ℕ} (c t : ℝ) (x : Fin n → ℝ) :
    gauss c (Fin.cons t x) = Real.exp (-c*t^2) * gauss c x := by
  simp [gauss, Fin.sum_univ_succ, mul_add, Real.exp_add]

lemma gauss_pos {n : ℕ} (c : ℝ) (x : Fin n → ℝ) : 0 < gauss c x :=
  Real.exp_pos _

lemma gauss_le_one {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (x : Fin n → ℝ) : gauss c x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma gauss_integrable {n : ℕ} {c : ℝ} (hc : 0 < c) : Integrable (@gauss n c) := by
  simp only [funext (gauss_prod c), volume_pi]
  exact Integrable.fin_nat_prod (fun _ => integrable_exp_neg_mul_sq hc)

structure Nice {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous f
  positive : ∀ x, 0 < f x
  bound : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x, f x ≤ C * gauss c x

lemma Nice.integrable {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Nice f) : Integrable f := by
  obtain ⟨C, c, _, hc, hb⟩ := hf.bound
  apply ((gauss_integrable hc).const_mul C).mono' hf.continuous.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (hf.positive x)]
  exact hb x

lemma continuous_cons_left {n : ℕ} (x : Fin n → ℝ) :
    Continuous (fun t : ℝ => (Fin.cons t x : Fin (n+1) → ℝ)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_id
  · exact continuous_const

noncomputable def marginal {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ t : ℝ, f (Fin.cons t x)

lemma Nice.section_integrable {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ} (hf : Nice f)
    (x : Fin n → ℝ) : Integrable (fun t : ℝ => f (Fin.cons t x)) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf.bound
  apply ((integrable_exp_neg_mul_sq hc).const_mul C).mono'
    (hf.continuous.comp (continuous_cons_left x)).aestronglyMeasurable
  filter_upwards [] with t
  change ‖f (Fin.cons t x)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (hf.positive _)]
  calc
    _ ≤ C * gauss c (Fin.cons t x) := hb _
    _ = (C * Real.exp (-c*t^2)) * gauss c x := by rw [gauss_cons]; ring
    _ ≤ C * Real.exp (-c*t^2) := mul_le_of_le_one_right (by positivity) (gauss_le_one hc.le _)

lemma Nice.marginal {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ} (hf : Nice f) : Nice (marginal f) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hf.bound
  have hbd (x : Fin n → ℝ) (t : ℝ) : ‖f (Fin.cons t x)‖ ≤ C * Real.exp (-c*t^2) := by
    rw [Real.norm_eq_abs, abs_of_pos (hf.positive _)]
    calc
      _ ≤ C * gauss c (Fin.cons t x) := hb _
      _ = (C * Real.exp (-c*t^2)) * gauss c x := by rw [gauss_cons]; ring
      _ ≤ C * Real.exp (-c*t^2) := mul_le_of_le_one_right (by positivity) (gauss_le_one hc.le _)
  constructor
  · exact continuous_of_dominated
      (fun x => (hf.continuous.comp (continuous_cons_left x)).aestronglyMeasurable)
      (fun x => Filter.Eventually.of_forall (hbd x))
      ((integrable_exp_neg_mul_sq hc).const_mul C)
      (Filter.Eventually.of_forall fun t => hf.continuous.comp (continuous_const.finCons continuous_id))
  · intro x
    apply (integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun t =>
      (hf.positive (Fin.cons t x)).le) (hf.section_integrable x)).mpr
    have he : Function.support (fun t : ℝ => f (Fin.cons t x)) = Set.univ := by
      ext t
      simp [Function.mem_support, ne_of_gt (hf.positive _)]
    rw [he]
    simp
  · refine ⟨C * Real.sqrt (Real.pi/c), c, mul_pos hC (by positivity), hc, ?_⟩
    intro x
    calc
      Prekopa.marginal f x ≤ ∫ t : ℝ, C * Real.exp (-c*t^2) * gauss c x := by
        apply integral_mono (hf.section_integrable x)
          (((integrable_exp_neg_mul_sq hc).const_mul C).mul_const _)
        intro t
        simpa only [gauss_cons, mul_assoc] using hb (Fin.cons t x)
      _ = C * Real.sqrt (Real.pi/c) * gauss c x := by
        rw [integral_mul_const, integral_const_mul, integral_gaussian]

lemma integral_marginal {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ} (hf : Integrable f) :
    (∫ x, f x) = ∫ x, marginal f x := by
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) 0).symm
  have hi := hm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f)
  have he := hm.integral_comp' f
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero, Fin.zero_succAbove, volume_pi] at he hi hf ⊢
  rw [← he]
  simpa [Function.comp_apply, marginal] using integral_prod_symm _ (hi.mpr hf)

lemma fin {n : ℕ} {f g h : (Fin n → ℝ) → ℝ} {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (hf : Nice f) (hg : Nice g) (hh : Nice h)
    (hfg : ∀ x y, f x ^ (1-α) * g y ^ α ≤ h ((1-α) • x + α • y)) :
    (∫ x, f x) ^ (1-α) * (∫ x, g x) ^ α ≤ ∫ x, h x := by
  induction n with
  | zero =>
    simp only [integral_unique, measureReal_def, volume_pi, Measure.pi_univ,
      Fin.prod_univ_zero, ENNReal.toReal_one, one_smul]
    convert hfg default default using 1
    · congr 2 <;> (congr 1; exact Subsingleton.elim _ _)
    · exact congrArg h (Subsingleton.elim _ _)
  | succ n ih =>
    rw [integral_marginal hf.integrable, integral_marginal hg.integrable,
      integral_marginal hh.integrable]
    apply ih hf.marginal hg.marginal hh.marginal
    intro x y
    apply real hα
      (hf.continuous.comp (continuous_cons_left x))
      (hg.continuous.comp (continuous_cons_left y))
      (hh.continuous.comp (continuous_cons_left ((1-α) • x + α • y)))
      (fun t => hf.positive (Fin.cons t x)) (fun t => hg.positive (Fin.cons t y))
      (hf.section_integrable x) (hg.section_integrable y) (hh.section_integrable _)
    intro r s
    have he : (1-α) • Fin.cons r x + α • Fin.cons s y =
        Fin.cons ((1-α)*r+α*s) ((1-α) • x + α • y) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    simpa only [he, Function.comp_apply] using hfg (Fin.cons r x) (Fin.cons s y)

end Prekopa

namespace Prekopa
open MeasureTheory Set Filter Metric
open scoped Topology

lemma infDist_combination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {A B C : Set E} (hA : IsClosed A) (hB : IsClosed B)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) (x y : E) :
    infDist ((1-α) • x + α • y) C ≤ (1-α)*infDist x A + α*infDist y B := by
  obtain ⟨a, ha, hea⟩ := hA.exists_infDist_eq_dist hnA x
  obtain ⟨b, hb, heb⟩ := hB.exists_infDist_eq_dist hnB y
  rw [hea, heb]
  apply (infDist_le_dist_of_mem (hABC a ha b hb)).trans
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have he : (1-α) • x + α • y - ((1-α) • a + α • b) =
      (1-α) • (x-a) + α • (y-b) := by module
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hα.2), abs_of_nonneg hα.1]

lemma sum_sq_combination {n : ℕ} {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1)
    (x y : Fin n → ℝ) :
    (∑ i, (((1-α) • x + α • y) i)^2) ≤ (1-α)*(∑ i, (x i)^2) + α*(∑ i, (y i)^2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have he := mul_nonneg (mul_nonneg hα.1 (sub_nonneg.mpr hα.2)) (sq_nonneg (x i - y i))
  nlinarith

noncomputable def approx {n : ℕ} (c : ℝ) (k : ℕ) (A : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : ℝ := gauss c x * Real.exp (-(k : ℝ) * infDist x A)

lemma approx_nice {n : ℕ} {c : ℝ} (hc : 0 < c) (k : ℕ) (A : Set (Fin n → ℝ)) :
    Nice (approx c k A) := by
  constructor
  · exact (Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _
      (fun i _ => (continuous_apply i).pow 2)))).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_infDist_pt A)))
  · intro x
    exact mul_pos (gauss_pos _ _) (Real.exp_pos _)
  · refine ⟨1, c, zero_lt_one, hc, ?_⟩
    intro x
    dsimp [approx]
    rw [one_mul]
    exact mul_le_of_le_one_right (gauss_pos _ _).le
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k)) infDist_nonneg))

lemma approx_interpolate {n : ℕ} {A B C : Set (Fin n → ℝ)}
    (hA : IsClosed A) (hB : IsClosed B) (hnA : A.Nonempty) (hnB : B.Nonempty)
    {α c : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) (k : ℕ) (x y : Fin n → ℝ) :
    approx c k A x ^ (1-α) * approx c k B y ^ α ≤ approx c k C ((1-α) • x + α • y) := by
  simp only [approx, gauss, ← Real.exp_add, ← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left (sum_sq_combination hα x y) hc
  have h2 := mul_le_mul_of_nonneg_left (infDist_combination hA hB hnA hnB hα hABC x y)
    (show (0 : ℝ) ≤ (k : ℝ) by positivity)
  nlinarith

lemma approx_tendsto {n : ℕ} {A : Set (Fin n → ℝ)} (hA : IsClosed A)
    (hnA : A.Nonempty) (c : ℝ) (x : Fin n → ℝ) :
    Tendsto (fun k => approx c k A x) atTop (𝓝 (A.indicator (gauss c) x)) := by
  by_cases hx : x ∈ A
  · simp [approx, infDist_zero_of_mem hx, hx]
  · rw [indicator_of_notMem hx]
    have hd := (hA.notMem_iff_infDist_pos hnA).mp hx
    have he : Tendsto (fun k : ℕ => -(k : ℝ) * infDist x A) atTop atBot := by
      have ht : Tendsto (fun k : ℕ => (k : ℝ) * infDist x A) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hd
      have hn : Tendsto (fun k : ℕ => -((k : ℝ) * infDist x A)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp ht
      convert hn using 1; simp only [neg_mul]
    simpa only [mul_zero, approx, Function.comp_apply] using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp he)

lemma integral_approx_tendsto {n : ℕ} {A : Set (Fin n → ℝ)} (hA : IsClosed A)
    (hnA : A.Nonempty) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => ∫ x, approx c k A x) atTop (𝓝 (∫ x in A, gauss c x)) := by
  rw [← integral_indicator hA.measurableSet]
  apply tendsto_integral_of_dominated_convergence (gauss c)
    (fun k => (approx_nice hc k A).continuous.aestronglyMeasurable) (gauss_integrable hc)
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos ((approx_nice hc k A).positive x)]
    exact mul_le_of_le_one_right (gauss_pos _ _).le
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k)) infDist_nonneg))
  · exact Filter.Eventually.of_forall (approx_tendsto hA hnA c)

lemma gauss_closed_logconcave {n : ℕ} {A B C : Set (Fin n → ℝ)}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α c : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (hc : 0 < c)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (∫ x in A, gauss c x) ^ (1-α) * (∫ x in B, gauss c x) ^ α ≤ ∫ x in C, gauss c x := by
  have hnC : C.Nonempty := by
    obtain ⟨a, ha⟩ := hnA
    obtain ⟨b, hb⟩ := hnB
    exact ⟨_, hABC a ha b hb⟩
  apply le_of_tendsto_of_tendsto
    (((integral_approx_tendsto hA hnA hc).rpow_const (Or.inr (sub_nonneg.mpr hα.2))).mul
      ((integral_approx_tendsto hB hnB hc).rpow_const (Or.inr hα.1)))
    (integral_approx_tendsto hC hnC hc)
  exact Filter.Eventually.of_forall fun k => fin hα (approx_nice hc k A)
    (approx_nice hc k B) (approx_nice hc k C) (approx_interpolate hA hB hnA hnB hα hc.le hABC k)

end Prekopa

namespace Prekopa
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

noncomputable def normalConst (n : ℕ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ n

lemma normalConst_pos (n : ℕ) : 0 < normalConst n := by
  unfold normalConst
  positivity

lemma prod_pdf {n : ℕ} (x : Fin n → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (x i) = normalConst n * gauss (1/2) x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  congr 1
  unfold gauss
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma piGaussian_density (n : ℕ) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      volume.withDensity (fun x => ENNReal.ofReal (normalConst n * gauss (1/2) x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      (((gauss_integrable (n := n) (by norm_num : (0:ℝ)<1/2)).const_mul _).restrict)
      (ae_of_all _ fun x => mul_nonneg (normalConst_pos n).le (gauss_pos _ x).le)]
  simp_rw [← prod_pdf]
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal)≠0) (s i)).symm

lemma piGaussian_real (n : ℕ) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real A =
      normalConst n * ∫ x in A, gauss (1/2) x := by
  rw [Measure.real, piGaussian_density, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal
      (((gauss_integrable (n := n) (by norm_num : (0:ℝ)<1/2)).const_mul _).restrict)
      (ae_of_all _ fun x => mul_nonneg (normalConst_pos n).le (gauss_pos _ x).le),
    ENNReal.toReal_ofReal (integral_nonneg fun x =>
      mul_nonneg (normalConst_pos n).le (gauss_pos _ x).le), integral_const_mul]

lemma piGaussian_closed_logconcave {n : ℕ} {A B C : Set (Fin n → ℝ)}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ} (hα : α ∈ Icc (0:ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real A ^ (1-α) *
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).real B ^ α ≤
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).real C := by
  rw [piGaussian_real n hA.measurableSet, piGaussian_real n hB.measurableSet,
    piGaussian_real n hC.measurableSet,
    Real.mul_rpow (normalConst_pos n).le (integral_nonneg fun x => (gauss_pos _ x).le),
    Real.mul_rpow (normalConst_pos n).le (integral_nonneg fun x => (gauss_pos _ x).le)]
  have he : normalConst n ^ (1-α) * normalConst n ^ α = normalConst n := by
    rw [← Real.rpow_add (normalConst_pos n), sub_add_cancel, Real.rpow_one]
  calc
    _ = (normalConst n ^ (1-α) * normalConst n ^ α) *
      ((∫ x in A, gauss (1/2) x) ^ (1-α) * (∫ x in B, gauss (1/2) x) ^ α) := by ring
    _ ≤ normalConst n * ∫ x in C, gauss (1/2) x := by
      rw [he]
      exact mul_le_mul_of_nonneg_left
        (gauss_closed_logconcave hA hB hC hnA hnB hα (by norm_num) hABC) (normalConst_pos n).le

end Prekopa

namespace Prekopa
open MeasureTheory ProbabilityTheory Set

lemma linear_image_closed_logconcave {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : (Fin n → ℝ) →L[ℝ] F) {A B C : Set F}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    (h0A : 0 ∈ A) (h0B : 0 ∈ B) {α : ℝ} (hα : α ∈ Icc (0:ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map L).real A ^ (1-α) *
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map L).real B ^ α ≤
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map L).real C := by
  simp only [Measure.real, Measure.map_apply L.continuous.measurable hA.measurableSet,
    Measure.map_apply L.continuous.measurable hB.measurableSet,
    Measure.map_apply L.continuous.measurable hC.measurableSet]
  apply piGaussian_closed_logconcave
    (hA.preimage L.continuous) (hB.preimage L.continuous) (hC.preimage L.continuous)
    ⟨0, by simpa using h0A⟩ ⟨0, by simpa using h0B⟩ hα
  intro a ha b hb
  simpa using hABC (L a) ha (L b) hb

lemma stdGaussian_linear_image_closed_logconcave {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) {A B C : Set F}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    (h0A : 0 ∈ A) (h0B : 0 ∈ B) {α : ℝ} (hα : α ∈ Icc (0:ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    ((stdGaussian E).map L).real A ^ (1-α) *
      ((stdGaussian E).map L).real B ^ α ≤ ((stdGaussian E).map L).real C := by
  let b := stdOrthonormalBasis ℝ E
  let S : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight (b i)
  have hS (x : Fin (Module.finrank ℝ E) → ℝ) : S x = ∑ i, x i • b i := by
    simp [S]
  have hμ : (stdGaussian E).map L =
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1).map (L.comp S) := by
    rw [stdGaussian_eq_map_pi_orthonormalBasis b]
    have he : (fun x => ∑ i, x i • b i) = S := funext fun x => (hS x).symm
    rw [he, Measure.map_map L.continuous.measurable S.continuous.measurable]
    rfl
  rw [hμ]
  exact linear_image_closed_logconcave (L.comp S) hA hB hC h0A h0B hα hABC

end Prekopa

open MeasureTheory Set ProbabilityTheory
namespace Prekopa

lemma convex_closure_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {A : Set E} (hA : Convex ℝ A) : closure A =ᵐ[μ] A := by
  have hn : ∀ᵐ x ∂μ, x ∉ frontier A := by
    rw [ae_iff]
    simpa using hA.addHaar_frontier μ
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · intro hc
    by_contra ha
    exact hx ⟨hc, fun hi => ha (interior_subset hi)⟩
  · exact fun hx => subset_closure hx

lemma combination_closure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C : Set E} {α : ℝ}
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    ∀ a ∈ closure A, ∀ b ∈ closure B, (1-α) • a + α • b ∈ closure C := by
  have hm : MapsTo (fun p : E × E => (1-α) • p.1 + α • p.2) (A ×ˢ B) C :=
    fun p hp => hABC p.1 hp.1 p.2 hp.2
  have hc := hm.closure_of_continuousOn (by fun_prop)
  intro a ha b hb
  exact hc (x := (a,b)) (by simpa only [closure_prod_eq, mem_prod] using And.intro ha hb)

lemma piGaussian_convex_logconcave {n : ℕ} {A B C : Set (Fin n → ℝ)}
    (hA : Convex ℝ A) (hB : Convex ℝ B) (hC : Convex ℝ C)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ} (hα : α ∈ Icc (0:ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real A ^ (1-α) *
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).real B ^ α ≤
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).real C := by
  have hac : (Measure.pi fun _ : Fin n => gaussianReal 0 1) ≪ volume := by
    rw [piGaussian_density]
    exact withDensity_absolutelyContinuous _ _
  have he (D : Set (Fin n → ℝ)) (hD : Convex ℝ D) :
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).real (closure D) =
        (Measure.pi fun _ : Fin n => gaussianReal 0 1).real D := by
    exact congrArg ENNReal.toReal (measure_congr (hac.ae_eq (convex_closure_ae volume hD)))
  have h := piGaussian_closed_logconcave isClosed_closure isClosed_closure isClosed_closure
    hnA.closure hnB.closure hα (combination_closure hABC)
  simpa only [he A hA, he B hB, he C hC] using h

lemma linear_image_convex_logconcave {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : (Fin n → ℝ) →L[ℝ] F) {A B C : Set F}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hcA : Convex ℝ A) (hcB : Convex ℝ B) (hcC : Convex ℝ C)
    (h0A : 0 ∈ A) (h0B : 0 ∈ B) {α : ℝ} (hα : α ∈ Icc (0:ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map L).real A ^ (1-α) *
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map L).real B ^ α ≤
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map L).real C := by
  simp only [Measure.real, Measure.map_apply L.continuous.measurable hA,
    Measure.map_apply L.continuous.measurable hB, Measure.map_apply L.continuous.measurable hC]
  apply piGaussian_convex_logconcave
    (hcA.linear_preimage L.toLinearMap) (hcB.linear_preimage L.toLinearMap)
    (hcC.linear_preimage L.toLinearMap)
    ⟨0, by simpa using h0A⟩ ⟨0, by simpa using h0B⟩ hα
  intro a ha b hb
  simpa using hABC (L a) ha (L b) hb

end Prekopa
open MeasureTheory Set ProbabilityTheory
namespace Prekopa
lemma stdGaussian_linear_image_convex_logconcave {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) {A B C : Set F}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hcA : Convex ℝ A) (hcB : Convex ℝ B) (hcC : Convex ℝ C)
    (h0A : 0 ∈ A) (h0B : 0 ∈ B) {α : ℝ} (hα : α ∈ Icc (0:ℝ) 1)
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    ((stdGaussian E).map L).real A ^ (1-α) *
      ((stdGaussian E).map L).real B ^ α ≤ ((stdGaussian E).map L).real C := by
  let b := stdOrthonormalBasis ℝ E
  let S : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight (b i)
  have hS (x : Fin (Module.finrank ℝ E) → ℝ) : S x = ∑ i, x i • b i := by
    simp [S]
  have hμ : (stdGaussian E).map L =
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1).map (L.comp S) := by
    rw [stdGaussian_eq_map_pi_orthonormalBasis b]
    have he : (fun x => ∑ i, x i • b i) = S := funext fun x => (hS x).symm
    rw [he, Measure.map_map L.continuous.measurable S.continuous.measurable]
    rfl
  rw [hμ]
  exact linear_image_convex_logconcave (L.comp S) hA hB hC hcA hcB hcC h0A h0B hα hABC

end Prekopa

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace Prekopa
variable {n : ℕ}
lemma weighted_approx_nice {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {c : ℝ} (hc : 0 < c) (k : ℕ) (A : Set (Fin n → ℝ)) :
    Nice (fun x => w x * approx c k A x) := by
  constructor
  · exact hw.mul (approx_nice hc k A).continuous
  · intro x; exact mul_pos (hp x) ((approx_nice hc k A).positive x)
  · refine ⟨M,c,hM,hc,?_⟩
    intro x
    have ha : approx c k A x ≤ gauss c x := by
      unfold approx
      exact mul_le_of_le_one_right (gauss_pos _ _).le
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k)) infDist_nonneg))
    exact mul_le_mul (hb x) ha ((approx_nice hc k A).positive x).le hM.le

lemma integral_weighted_approx_tendsto {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A : Set (Fin n → ℝ)} (hA : IsClosed A)
    (hnA : A.Nonempty) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => ∫ x, w x * approx c k A x) atTop
      (𝓝 (∫ x in A, w x * gauss c x)) := by
  rw [← integral_indicator hA.measurableSet]
  apply tendsto_integral_of_dominated_convergence (fun x => M * gauss c x)
    (fun k => (weighted_approx_nice hw hp hM hb hc k A).continuous.aestronglyMeasurable)
    ((gauss_integrable hc).const_mul M)
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos ((weighted_approx_nice hw hp hM hb hc k A).positive x)]
    apply mul_le_mul (hb x) _ ((approx_nice hc k A).positive x).le hM.le
    unfold approx
    exact mul_le_of_le_one_right (gauss_pos _ _).le
      (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k)) infDist_nonneg))
  · filter_upwards [] with x
    convert (tendsto_const_nhds.mul (approx_tendsto hA hnA c x)) using 1
    by_cases hx : x ∈ A <;> simp [hx]

lemma weighted_gauss_closed {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A B C : Set (Fin n → ℝ)}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α c : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (hc : 0 < c)
    (hl : ∀ x y, w x ^ (1-α) * w y ^ α ≤ w ((1-α) • x + α • y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (∫ x in A, w x * gauss c x) ^ (1-α) *
      (∫ x in B, w x * gauss c x) ^ α ≤ ∫ x in C, w x * gauss c x := by
  have hnC : C.Nonempty := by
    obtain ⟨a,ha⟩ := hnA
    obtain ⟨b,hb'⟩ := hnB
    exact ⟨_,hABC a ha b hb'⟩
  apply le_of_tendsto_of_tendsto
    (((integral_weighted_approx_tendsto hw hp hM hb hA hnA hc).rpow_const
      (Or.inr (sub_nonneg.mpr hα.2))).mul
      ((integral_weighted_approx_tendsto hw hp hM hb hB hnB hc).rpow_const (Or.inr hα.1)))
    (integral_weighted_approx_tendsto hw hp hM hb hC hnC hc)
  apply Filter.Eventually.of_forall
  intro k
  apply fin hα (weighted_approx_nice hw hp hM hb hc k A)
    (weighted_approx_nice hw hp hM hb hc k B) (weighted_approx_nice hw hp hM hb hc k C)
  intro x y
  rw [Real.mul_rpow (hp x).le ((approx_nice hc k A).positive x).le,
    Real.mul_rpow (hp y).le ((approx_nice hc k B).positive y).le]
  calc
    _ = (w x ^ (1-α) * w y ^ α) * (approx c k A x ^ (1-α) * approx c k B y ^ α) := by ring
    _ ≤ w ((1-α) • x + α • y) * approx c k C ((1-α) • x + α • y) :=
      mul_le_mul (hl x y) (approx_interpolate hA hB hnA hnB hα hc.le hABC k x y)
        (mul_nonneg (Real.rpow_nonneg ((approx_nice hc k A).positive x).le _)
          (Real.rpow_nonneg ((approx_nice hc k B).positive y).le _)) (hp _).le

lemma integral_weighted_gauss_tendsto {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (_hM : 0 < M)
    (hb : ∀ x, w x ≤ M) (A : Set (Fin n → ℝ)) [IsFiniteMeasure (volume.restrict A)] :
    Tendsto (fun k : ℕ => ∫ x in A, w x * gauss (1/((k:ℝ)+1)) x) atTop
      (𝓝 (∫ x in A, w x)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun k => hw.aestronglyMeasurable.mul
      ((Real.continuous_exp.comp (continuous_const.mul
        (continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)))).aestronglyMeasurable))
    (integrable_const M)
  · intro k
    filter_upwards [] with x
    change ‖w x * gauss (1/((k:ℝ)+1)) x‖ ≤ M
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hp x) (gauss_pos _ _))]
    exact (mul_le_of_le_one_right (hp x).le (gauss_le_one (by positivity) x)).trans (hb x)
  · filter_upwards [] with x
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg.mul_const (∑ i, (x i)^2)
    have he := Real.continuous_exp.continuousAt.tendsto.comp ht
    simpa [gauss] using tendsto_const_nhds.mul he

lemma bounded_weight_closed {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A B C : Set (Fin n → ℝ)}
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C)
    [IsFiniteMeasure (volume.restrict A)] [IsFiniteMeasure (volume.restrict B)]
    [IsFiniteMeasure (volume.restrict C)]
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1)
    (hl : ∀ x y, w x ^ (1-α) * w y ^ α ≤ w ((1-α) • x + α • y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (∫ x in A, w x) ^ (1-α) * (∫ x in B, w x) ^ α ≤ ∫ x in C, w x := by
  apply le_of_tendsto_of_tendsto
    (((integral_weighted_gauss_tendsto hw hp hM hb A).rpow_const
      (Or.inr (sub_nonneg.mpr hα.2))).mul
      ((integral_weighted_gauss_tendsto hw hp hM hb B).rpow_const (Or.inr hα.1)))
    (integral_weighted_gauss_tendsto hw hp hM hb C)
  exact Filter.Eventually.of_forall fun k =>
    weighted_gauss_closed hw hp hM hb hA hB hC hnA hnB hα (by positivity) hl hABC

end Prekopa

namespace Prekopa
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

lemma bounded_weight_compact_haar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {w : E → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A B C : Set E}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1)
    (hl : ∀ x y, w x ^ (1-α) * w y ^ α ≤ w ((1-α) • x + α • y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (∫ x in A, w x ∂μ) ^ (1-α) * (∫ x in B, w x ∂μ) ^ α ≤ ∫ x in C, w x ∂μ := by
  let e := (Module.finBasis ℝ E).equivFunL.symm
  let ν : Measure E := volume.map e
  let : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  let c : ℝ≥0 := Measure.addHaarScalarFactor ν μ
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  have heμ : volume.map e = (c : ℝ≥0∞) • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hpre (D : Set E) (hD : IsCompact D) : IsCompact (e ⁻¹' D) := by
    exact e.toHomeomorph.isCompact_preimage.mpr hD
  have : IsFiniteMeasure (volume.restrict (e ⁻¹' A)) := ⟨by simpa using (hpre A hA).measure_lt_top⟩
  have : IsFiniteMeasure (volume.restrict (e ⁻¹' B)) := ⟨by simpa using (hpre B hB).measure_lt_top⟩
  have : IsFiniteMeasure (volume.restrict (e ⁻¹' C)) := ⟨by simpa using (hpre C hC).measure_lt_top⟩
  have hi (D : Set E) (hD : IsCompact D) :
      (∫ x in e ⁻¹' D, w (e x)) = (c:ℝ) * ∫ x in D, w x ∂μ := by
    rw [← setIntegral_map hD.isClosed.measurableSet hw.aestronglyMeasurable
      e.continuous.measurable.aemeasurable, heμ, Measure.restrict_smul, integral_smul_measure]
    simp

  have hl' : ∀ x y, w (e x) ^ (1-α) * w (e y) ^ α ≤ w (e ((1-α) • x + α • y)) := by
    intro x y
    simpa only [map_add,map_smul] using hl (e x) (e y)
  have hcomb : ∀ a ∈ e ⁻¹' A, ∀ b ∈ e ⁻¹' B, (1-α) • a + α • b ∈ e ⁻¹' C := by
    intro a ha b hb'
    change e ((1-α) • a + α • b) ∈ C
    simpa only [map_add,map_smul] using hABC (e a) ha (e b) hb'
  have hnA' : (e ⁻¹' A).Nonempty := hnA.preimage e.surjective
  have hnB' : (e ⁻¹' B).Nonempty := hnB.preimage e.surjective
  have hh := bounded_weight_closed (hw.comp e.continuous) (fun x => hp (e x)) hM
    (fun x => hb (e x)) (hpre A hA).isClosed (hpre B hB).isClosed (hpre C hC).isClosed
    hnA' hnB' hα hl' hcomb
  simp only [Function.comp_apply] at hh
  rw [hi A hA, hi B hB, hi C hC,
    Real.mul_rpow (by positivity) (integral_nonneg (fun x => (hp x).le)),
    Real.mul_rpow (by positivity) (integral_nonneg (fun x => (hp x).le))] at hh
  have hcp : (0:ℝ)<c := hc
  have hcPow : (c:ℝ)^(1-α) * (c:ℝ)^α = (c:ℝ) := by
    rw [← Real.rpow_add hcp, sub_add_cancel, Real.rpow_one]
  have heq : (c:ℝ)^(1-α) * (∫ x in A, w x ∂μ)^(1-α) *
      ((c:ℝ)^α * (∫ x in B, w x ∂μ)^α) =
      (c:ℝ) * ((∫ x in A, w x ∂μ)^(1-α) * (∫ x in B, w x ∂μ)^α) := by
    calc
      _ = ((c:ℝ)^(1-α) * (c:ℝ)^α) *
          ((∫ x in A, w x ∂μ)^(1-α) * (∫ x in B, w x ∂μ)^α) := by ring
      _ = _ := by rw [hcPow]
  rw [heq] at hh
  exact (mul_le_mul_iff_right₀ hcp).mp hh

lemma bounded_weight_convex_haar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {w : E → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 < w x) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x, w x ≤ M) {A B C : Set E}
    (ha : Bornology.IsBounded A) (hb' : Bornology.IsBounded B) (hc : Bornology.IsBounded C)
    (hcA : Convex ℝ A) (hcB : Convex ℝ B) (hcC : Convex ℝ C)
    (hnA : A.Nonempty) (hnB : B.Nonempty) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1)
    (hl : ∀ x y, w x ^ (1-α) * w y ^ α ≤ w ((1-α) • x + α • y))
    (hABC : ∀ a ∈ A, ∀ b ∈ B, (1-α) • a + α • b ∈ C) :
    (∫ x in A, w x ∂μ) ^ (1-α) * (∫ x in B, w x ∂μ) ^ α ≤ ∫ x in C, w x ∂μ := by
  have hh := bounded_weight_compact_haar μ hw hp hM hb ha.isCompact_closure
    hb'.isCompact_closure hc.isCompact_closure hnA.closure hnB.closure hα hl
    (combination_closure hABC)
  rwa [setIntegral_congr_set (convex_closure_ae μ hcA),
    setIntegral_congr_set (convex_closure_ae μ hcB),
    setIntegral_congr_set (convex_closure_ae μ hcC)] at hh

end Prekopa

end

end OAI
