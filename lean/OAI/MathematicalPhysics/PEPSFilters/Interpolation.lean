import Mathlib

namespace OAI

/-! Three-lines interpolation and entropy tangent bounds for ordered operators. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix

open Set Filter
open scoped Topology
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic

lemma tangent_le {g h : ℝ → ℝ} {g' h' : ℝ}
    (hg : HasDerivAt g g' 0) (hh : HasDerivAt h h' 0)
    (hzero : g 0 = h 0) (hle : ∀ t ∈ Ioo (0 : ℝ) 1, g t ≤ h t) :
    g' ≤ h' := by
  apply le_of_tendsto_of_tendsto hg.tendsto_slope_zero_right
    hh.tendsto_slope_zero_right
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  simp only [zero_add, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [hzero] using hle t ht)
    (le_of_lt (inv_pos.mpr ht.1))

open Complex.HadamardThreeLines

theorem threeLines_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hzero : ‖f 0‖ = a)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' {0}, ‖f z‖ ≤ a)
    (hright : ∀ z ∈ Complex.re ⁻¹' {1}, ‖f z‖ ≤ b)
    (hderiv : HasDerivAt (fun t : ℝ => ‖f (t : ℂ)‖ ^ 2) d 0) :
    d ≤ 2 * a ^ 2 * (Real.log b - Real.log a) := by
  let h : ℝ → ℝ := fun t => a ^ 2 * Real.exp (2 * t * (Real.log b - Real.log a))
  have hh : HasDerivAt h (2 * a ^ 2 * (Real.log b - Real.log a)) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
      (Real.log b - Real.log a)).exp.const_mul (a ^ 2) using 1 <;>
      simp [h]
    ring
  apply tangent_le hderiv hh
  · simp [h, hzero]
  · intro t ht
    have hstrip : (t : ℂ) ∈ verticalClosedStrip 0 1 := by
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hi := norm_le_interp_of_mem_verticalClosedStrip₀₁' f hstrip hd hB hleft hright
    simp only [Complex.ofReal_re] at hi
    have hs := pow_le_pow_left₀ (norm_nonneg (f (t : ℂ))) hi 2
    apply hs.trans_eq
    dsimp [h]
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb,
      ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_log ha]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [Real.log_exp]
    ring

theorem threeLines_entropy_tangent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hzero : ‖f 0‖ = a)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' {0}, ‖f z‖ ≤ a)
    (hright : ∀ z ∈ Complex.re ⁻¹' {1}, ‖f z‖ ≤ b)
    (hderiv : HasDerivAt (fun t : ℝ => ‖f (t : ℂ)‖ ^ 2) d 0) :
    Real.log (a ^ 2) + d / a ^ 2 ≤ Real.log (b ^ 2) := by
  have hh := threeLines_tangent f ha hb hzero hd hB hleft hright hderiv
  rw [Real.log_pow, Real.log_pow]
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hd' : d / a ^ 2 ≤ 2 * (Real.log b - Real.log a) :=
    (div_le_iff₀ ha2).mpr (by nlinarith [hh])
  nlinarith

end PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic

open scoped BigOperators
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def chain {m : ℕ} (T : Fin m → E →L[ℂ] E) (v : E) : E :=
  (List.ofFn T).foldl (fun w A => A w) v

@[simp] lemma chain_zero (T : Fin 0 → E →L[ℂ] E) (v : E) : chain T v = v := by
  simp [chain]

lemma chain_succ {m : ℕ} (T : Fin (m+1) → E →L[ℂ] E) (v : E) :
    chain T v = chain (fun j => T j.succ) (T 0 v) := by
  simp only [chain, List.ofFn_succ, List.foldl_cons]

lemma chain_differentiable {m : ℕ} (T : Fin m → ℂ → E →L[ℂ] E)
    (hT : ∀ j, Differentiable ℂ (T j)) {f : ℂ → E} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => chain (fun j => T j z) (f z)) := by
  induction m generalizing f with
  | zero => simpa only [chain_zero] using hf
  | succ m ih =>
    simp only [chain_succ]
    exact ih (fun j => T j.succ) (fun j => hT j.succ) ((hT 0).clm_apply hf)

lemma chain_norm_le {m : ℕ} (T : Fin m → E →L[ℂ] E)
    (hT : ∀ j, ‖T j‖ ≤ 1) (v : E) : ‖chain T v‖ ≤ ‖v‖ := by
  induction m generalizing v with
  | zero => simp only [chain_zero, le_refl]
  | succ m ih =>
    rw [chain_succ]
    apply (ih (fun j => T j.succ) (fun j => hT j.succ) (T 0 v)).trans
    exact (T 0).le_of_opNorm_le (hT 0) v |>.trans_eq (one_mul _)

lemma chain_fix {m : ℕ} (T : Fin m → E →L[ℂ] E) {v : E}
    (hT : ∀ j, T j v = v) : chain T v = v := by
  induction m with
  | zero => exact chain_zero T v
  | succ m ih => rw [chain_succ, hT 0]; exact ih _ (fun j => hT j.succ)

lemma chain_inner_deriv {m : ℕ} (T : Fin m → ℂ → E →L[ℂ] E)
    (D : Fin m → E →L[ℂ] E) (hT : ∀ j, HasDerivAt (T j) (D j) 0)
    {v : E} (hfix : ∀ j, T j 0 v = v)
    (hstrip : ∀ j w, inner ℂ v (T j 0 w) = inner ℂ v w)
    {f : ℂ → E} {d : E} (hf : HasDerivAt f d 0) (hf0 : f 0 = v) :
    ∃ d', HasDerivAt (fun z => chain (fun j => T j z) (f z)) d' 0 ∧
      inner ℂ v d' = inner ℂ v d + ∑ j, inner ℂ v (D j v) := by
  induction m generalizing f d with
  | zero =>
    refine ⟨d, ?_, ?_⟩
    · simpa only [chain_zero] using hf
    · simp
  | succ m ih =>
    have hd := (hT 0).clm_apply hf
    rw [hf0] at hd
    obtain ⟨d', hd', hvd'⟩ := ih (fun j => T j.succ) (fun j => D j.succ)
      (fun j => hT j.succ) (fun j => hfix j.succ) (fun j => hstrip j.succ)
      hd (by rw [hf0, hfix 0])
    refine ⟨d', ?_, ?_⟩
    · simpa only [chain_succ] using hd'
    · rw [hvd', inner_add_right, hstrip 0, Fin.sum_univ_succ]
      abel

lemma complex_deriv_real_norm_sq {f : ℂ → E} {d : E} (hf : HasDerivAt f d 0) :
    HasDerivAt (fun t : ℝ => ‖f (t : ℂ)‖ ^ 2)
      (2 * (inner ℂ (f 0) d).re) 0 := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hr := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (f := fun t : ℝ => (t : ℂ)) 0
    (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  have ht : HasDerivAt (fun t : ℝ => f (t : ℂ)) d 0 := by
    change HasDerivAt (fun t : ℝ => f (t : ℂ)) ((1 : ℂ) • d) 0 at hr
    simpa only [one_smul] using hr
  exact ht.norm_sq

end PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic
open Complex.HadamardThreeLines
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma chain_entropy_tangent {m : ℕ} (T : Fin m → ℂ → E →L[ℂ] E)
    (D : Fin m → E →L[ℂ] E) {v : E}
    (hv : v ≠ (0 : E)) {b : ℝ} (hb : 0 < b)
    (hentire : ∀ j, Differentiable ℂ (T j))
    (hderiv : ∀ j, HasDerivAt (T j) (D j) 0)
    (hfix : ∀ j, T j 0 v = v)
    (hstrip : ∀ j w, inner ℂ v (T j 0 w) = inner ℂ v w)
    (hnorm : ∀ j z, 0 ≤ z.re → ‖T j z‖ ≤ 1)
    (hright : ∀ z, z.re = 1 → ‖chain (fun j => T j z) v‖ ≤ b) :
    Real.log (‖v‖ ^ 2) + (2 * (∑ j, inner ℂ v (D j v)).re) / ‖v‖ ^ 2 ≤
      Real.log (b ^ 2) := by
  obtain ⟨d, hd, hdi⟩ := chain_inner_deriv T D hderiv hfix hstrip
    (hasDerivAt_const (0 : ℂ) v) rfl
  have hzero : chain (fun j => T j 0) v = v := chain_fix _ hfix
  have hdiff : Differentiable ℂ (fun z => chain (fun j => T j z) v) :=
    chain_differentiable T hentire (differentiable_const v)
  have hbound (z : ℂ) (hz : 0 ≤ z.re) : ‖chain (fun j => T j z) v‖ ≤ ‖v‖ :=
    chain_norm_le _ (fun j => hnorm j z hz) v
  apply threeLines_entropy_tangent (fun z => chain (fun j => T j z) v)
    (norm_pos_iff.mpr hv) hb (by rw [hzero]) hdiff.diffContOnCl
  · refine ⟨‖v‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hbound z hz.1
  · intro z hz
    exact hbound z (le_of_eq (show z.re = 0 from hz).symm)
  · intro z hz
    exact hright z hz
  · have hn := complex_deriv_real_norm_sq hd
    simpa only [hzero, hdi, inner_zero_right, zero_add] using hn

end PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic
open Complex.HadamardThreeLines

lemma threeLines_right_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) {a b : ℝ} (hb : 0 ≤ b) (hf0 : f 0 ≠ 0)
    (hdiff : Differentiable ℂ f)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ Complex.re ⁻¹' {0}, ‖f z‖ ≤ a)
    (hright : ∀ z ∈ Complex.re ⁻¹' {1}, ‖f z‖ ≤ b) : 0 < b := by
  by_contra hnb
  have hb0 : b = 0 := le_antisymm (le_of_not_gt hnb) hb
  have hzero (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) : ‖f (t : ℂ)‖ = 0 := by
    have hi := norm_le_interp_of_mem_verticalClosedStrip₀₁' f
      (show (t : ℂ) ∈ verticalClosedStrip 0 1 from ⟨ht.1.le, ht.2.le⟩)
      hdiff.diffContOnCl hB hleft hright
    apply le_antisymm _ (norm_nonneg _)
    simpa only [Complex.ofReal_re, hb0, Real.zero_rpow (ne_of_gt ht.1), mul_zero] using hi
  have he : Filter.Tendsto (fun t : ℝ => ‖f (t : ℂ)‖) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact (hzero t ht).symm
  have hc := ((hdiff.continuous.comp Complex.continuous_ofReal).norm.tendsto 0).mono_left
    (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hz : ‖f 0‖ = 0 := by simpa only [Function.comp_def, Complex.ofReal_zero] using tendsto_nhds_unique hc he
  exact hf0 (norm_eq_zero.mp hz)

end PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic
open Complex.HadamardThreeLines
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma chain_entropy_tangent_nonneg {m : ℕ} (T : Fin m → ℂ → E →L[ℂ] E)
    (D : Fin m → E →L[ℂ] E) {v : E}
    (hv : v ≠ (0 : E)) {b : ℝ} (hb : 0 ≤ b)
    (hentire : ∀ j, Differentiable ℂ (T j))
    (hderiv : ∀ j, HasDerivAt (T j) (D j) 0)
    (hfix : ∀ j, T j 0 v = v)
    (hstrip : ∀ j w, inner ℂ v (T j 0 w) = inner ℂ v w)
    (hnorm : ∀ j z, 0 ≤ z.re → ‖T j z‖ ≤ 1)
    (hright : ∀ z, z.re = 1 → ‖chain (fun j => T j z) v‖ ≤ b) :
    Real.log (‖v‖ ^ 2) + (2 * (∑ j, inner ℂ v (D j v)).re) / ‖v‖ ^ 2 ≤
      Real.log (b ^ 2) := by
  have hzero : chain (fun j => T j 0) v = v := chain_fix _ hfix
  have hdiff : Differentiable ℂ (fun z => chain (fun j => T j z) v) :=
    chain_differentiable T hentire (differentiable_const v)
  have hbound (z : ℂ) (hz : 0 ≤ z.re) : ‖chain (fun j => T j z) v‖ ≤ ‖v‖ :=
    chain_norm_le _ (fun j => hnorm j z hz) v
  have hp : 0 < b := by
    apply threeLines_right_pos (fun z => chain (fun j => T j z) v) hb
      (by rwa [hzero]) hdiff
    · refine ⟨‖v‖, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hbound z hz.1
    · intro z hz
      exact hbound z (le_of_eq (show z.re = 0 from hz).symm)
    · intro z hz
      exact hright z hz
  exact chain_entropy_tangent T D hv hp hentire hderiv hfix hstrip hnorm hright

end PolynomialPEPS.PinnedEntropy.NestedFilter.Analytic

end

end OAI
