import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective
import OAI.Analysis.SymmetricDomains.AnalyticMulZeroGerm

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric NNReal
open scoped Topology

theorem scaled_polynomial_root_bound (P : Polynomial ℂ) (hP : P ≠ 0) (a q : ℂ)
    (ha : P.IsRoot a) (C : ℝ≥0)
    (hC : ∀ j ∈ Finset.range P.natDegree,
      ‖q‖₊ * ‖P.coeff j‖₊ ≤ C * ‖P.leadingCoeff‖₊) :
    ‖q * a‖₊ ≤ C + ‖q‖₊ := by
  have hl : ‖P.leadingCoeff‖₊ ≠ 0 := by simpa using hP
  calc
    ‖q * a‖₊ = ‖q‖₊ * ‖a‖₊ := nnnorm_mul _ _
    _ ≤ ‖q‖₊ * P.cauchyBound := mul_le_mul_of_nonneg_left (ha.norm_lt_cauchyBound hP).le (show 0 ≤ ‖q‖₊ from zero_le)
    _ = (‖q‖₊ * (Finset.range P.natDegree).sup (fun j => ‖P.coeff j‖₊)) / ‖P.leadingCoeff‖₊ + ‖q‖₊ := by
      rw [Polynomial.cauchyBound,mul_add,mul_one,mul_div_assoc]
    _ ≤ C + ‖q‖₊ := by
      apply add_le_add _ le_rfl
      apply (div_le_iff₀ (pos_iff_ne_zero.mpr hl)).mpr
      rw [mul_finset_sup]
      exact Finset.sup_le hC

theorem meromorphicAt_polynomial_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : ℂ → (Fin d → ℂ))
    (hA : AnalyticAt ℂ A 0) (f : ℂ → ℂ)
    (hf : ∀ᶠ z in 𝓝[≠] 0, AnalyticAt ℂ f z)
    (hroot : ∀ᶠ z in 𝓝[≠] 0, Polynomial.eval₂ (MvPolynomial.eval (A z)) (f z) P = 0)
    (hlead : ¬∀ᶠ z in 𝓝 0, MvPolynomial.eval (A z) P.leadingCoeff = 0) :
    MeromorphicAt f 0 := by
  have hpa (p : MvPolynomial (Fin d) ℂ) :
      AnalyticAt ℂ (fun z => MvPolynomial.eval (A z) p) 0 :=
    (AnalyticOnNhd.eval_mvPolynomial p (A 0) (mem_univ _)).comp hA
  obtain ⟨M,g,hga,hg0,hfac⟩ := (hpa P.leadingCoeff).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hlead
  simp only [sub_zero,smul_eq_mul] at hfac
  have hgne : ∀ᶠ z in 𝓝 (0 : ℂ), g z ≠ 0 :=
    (hga.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg0
  let J := Finset.range P.natDegree
  let B : ℝ := ∑ j : J, (‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ + 1)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hbj (j : J) : ‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ + 1 ≤ B :=
    Finset.single_le_sum (f := fun j : J => (‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ j)
  have hce : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ j : J,
      ‖MvPolynomial.eval (A z) (P.coeff j.val) / g z‖ ≤ B := by
    apply Filter.eventually_all.mpr
    intro j
    have hc := ((hpa (P.coeff j.val)).continuousAt.div hga.continuousAt hg0).norm
    exact (hc.tendsto.eventually_le_const (by linarith :
      ‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ <
        ‖MvPolynomial.eval (A 0) (P.coeff j.val) / g 0‖ + 1)).mono (fun _ h => h.trans (hbj j))
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ ≤ 1 := by
    exact continuousAt_id.norm.tendsto.eventually_le_const (by simp)
  have hbound : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z^M * f z‖ ≤ B + 1 := by
    filter_upwards [hroot,self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hfac.and (hgne.and (hce.and hn)))] with z hz hz0 hzz
    rcases hzz with ⟨hfac,hgz,hcz,hnz⟩
    have hz0 : z ≠ 0 := hz0
    have hleadne : MvPolynomial.eval (A z) P.leadingCoeff ≠ 0 := by
      rw [hfac]
      exact mul_ne_zero (pow_ne_zero M hz0) hgz
    let Q := P.map (MvPolynomial.eval (A z))
    have hQl : Q.leadingCoeff = MvPolynomial.eval (A z) P.leadingCoeff :=
      Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hleadne
    have hQ : Q ≠ 0 := by
      intro h
      have hzero : Q.leadingCoeff = 0 := h ▸ Polynomial.leadingCoeff_zero
      exact hleadne (hQl.symm.trans hzero)
    have hQr : Q.IsRoot (f z) := by
      simpa only [Q,Polynomial.IsRoot.def,Polynomial.eval_map] using hz
    have he := scaled_polynomial_root_bound Q hQ (f z) (z^M) hQr ⟨B,hB⟩ (by
      intro j hj
      have hjJ : j ∈ J := Finset.mem_range.mpr
        ((Finset.mem_range.mp hj).trans_le Polynomial.natDegree_map_le)
      have hc : ‖MvPolynomial.eval (A z) (P.coeff j)‖ ≤ B * ‖g z‖ := by
        have hh := hcz ⟨j,hjJ⟩
        rw [norm_div] at hh
        exact (div_le_iff₀ (norm_pos_iff.mpr hgz)).mp hh
      apply NNReal.coe_le_coe.mp
      change ‖z^M‖ * ‖Q.coeff j‖ ≤ B * ‖Q.leadingCoeff‖
      rw [hQl,hfac,norm_mul]
      rw [show Q.coeff j = MvPolynomial.eval (A z) (P.coeff j) from by simp only [Q,Polynomial.coeff_map]]
      nlinarith [mul_le_mul_of_nonneg_left hc (norm_nonneg (z^M))])
    have he' : ‖z^M * f z‖ ≤ B + ‖z^M‖ := by exact_mod_cast he
    apply he'.trans
    gcongr
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hnz
  have hall : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → AnalyticAt ℂ f z ∧ ‖z^M*f z‖ ≤ B+1 := by
    simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using hf.and hbound
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hall
  apply meromorphicAt_of_power_bound hr (fun z hz => (hball hz.1 hz.2).1) M
  intro z hz
  exact (hball hz.1 hz.2).2

end Release061

end

end OAI
