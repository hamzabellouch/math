import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace WeakHessianFunctional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ClosedQuadraticEnergy (Q : E → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous Q
  zero : Q 0 = 0
  smul : ∀ (c : ℝ) (f : E), Q (c • f) = ENNReal.ofReal (c^2) * Q f
  parallelogram : ∀ f g, Q f < ∞ → Q g < ∞ →
    Q (f+g) + Q (f-g) = 2 * Q f + 2 * Q g

variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)
include hQ

lemma ClosedQuadraticEnergy.add_lt_top {f g : E} (hf : Q f < ∞) (hg : Q g < ∞) :
    Q (f+g) < ∞ := by
  have H := hQ.parallelogram f g hf hg
  have ht : 2 * Q f + 2 * Q g < ∞ := by finiteness
  exact (le_add_right le_rfl).trans_lt (H ▸ ht)

lemma ClosedQuadraticEnergy.sub_lt_top {f g : E} (hf : Q f < ∞) (hg : Q g < ∞) :
    Q (f-g) < ∞ := by
  have H := hQ.parallelogram f g hf hg
  have ht : 2 * Q f + 2 * Q g < ∞ := by finiteness
  exact (le_add_left le_rfl).trans_lt (H ▸ ht)

lemma ClosedQuadraticEnergy.midpoint_lt_top {f g : E} (hf : Q f < ∞) (hg : Q g < ∞) :
    Q ((1/2 : ℝ) • (f+g)) < ∞ := by
  rw [hQ.smul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hQ.add_lt_top hf hg)

lemma ClosedQuadraticEnergy.midpoint_le {f g : E} (hf : Q f < ∞) (hg : Q g < ∞) :
    (Q ((1/2 : ℝ) • (f+g))).toReal ≤ (Q f).toReal / 2 + (Q g).toReal / 2 := by
  have H := congrArg ENNReal.toReal (hQ.parallelogram f g hf hg)
  rw [ENNReal.toReal_add (hQ.add_lt_top hf hg).ne (hQ.sub_lt_top hf hg).ne,
    ENNReal.toReal_add (by finiteness) (by finiteness)] at H
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at H
  rw [hQ.smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  have := ENNReal.toReal_nonneg (a := Q (f-g))
  norm_num
  nlinarith

def proximalFunctional (Q : E → ℝ≥0∞) (u f : E) : ℝ≥0∞ :=
  Q f + ENNReal.ofReal (‖f-u‖^2/2)

omit hQ [InnerProductSpace ℝ E] in
lemma proximalFunctional_lt_top {u f : E} (hf : Q f < ∞) :
    proximalFunctional Q u f < ∞ := by
  unfold proximalFunctional
  finiteness

omit hQ [InnerProductSpace ℝ E] in
lemma proximalFunctional_toReal {u f : E} (hf : Q f < ∞) :
    (proximalFunctional Q u f).toReal = (Q f).toReal + ‖f-u‖^2/2 := by
  rw [proximalFunctional, ENNReal.toReal_add hf.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)]

lemma ClosedQuadraticEnergy.proximal_midpoint {u f g : E}
    (hf : Q f < ∞) (hg : Q g < ∞) :
    (proximalFunctional Q u ((1/2:ℝ) • (f+g))).toReal + ‖f-g‖^2/8 ≤
      ((proximalFunctional Q u f).toReal + (proximalFunctional Q u g).toReal)/2 := by
  rw [proximalFunctional_toReal (hQ.midpoint_lt_top hf hg),
    proximalFunctional_toReal hf, proximalFunctional_toReal hg]
  have H := hQ.midpoint_le hf hg
  have hn := parallelogram_law_with_norm_mul ℝ (f-u) (g-u)
  simp only [← pow_two] at hn
  have e1 : f-u + (g-u) = (2:ℝ) • ((1/2:ℝ) • (f+g)-u) := by module
  have e2 : f-u - (g-u) = f-g := by abel
  rw [e1, e2, norm_smul] at hn
  norm_num at hn
  simp only [smul_add] at H ⊢
  nlinarith

lemma ClosedQuadraticEnergy.lowerSemicontinuous_proximal (u : E) :
    LowerSemicontinuous (proximalFunctional Q u) := by
  exact hQ.lowerSemicontinuous.add
    (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous (fun f : E => ‖f-u‖^2/2))).lowerSemicontinuous

lemma ClosedQuadraticEnergy.exists_minimizer [CompleteSpace E] (u : E) :
    ∃ f : E, ∀ g : E, proximalFunctional Q u f ≤ proximalFunctional Q u g := by
  let J := proximalFunctional Q u
  let a : ℝ≥0∞ := ⨅ f : E, J f
  have hJ0 : J 0 < ∞ := proximalFunctional_lt_top (by rw [hQ.zero]; simp)
  have ha : a < ∞ := (iInf_le J 0).trans_lt hJ0
  let δ : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
  have hδpos : ∀ n, 0 < δ n := fun n => by dsimp [δ]; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex : ∀ n, ∃ f, J f < ENNReal.ofReal (a.toReal + δ n) := by
    intro n
    apply iInf_lt_iff.mp
    change a < ENNReal.ofReal (a.toReal + δ n)
    apply (ENNReal.toReal_lt_toReal ha.ne ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith [hδpos n]
  choose fs hs using hex
  have hJfin : ∀ n, J (fs n) < ∞ := fun n => (hs n).trans ENNReal.ofReal_lt_top
  have hQfin : ∀ n, Q (fs n) < ∞ := fun n => (le_add_right le_rfl).trans_lt (hJfin n)
  have hsmall : ∀ n, (J (fs n)).toReal < a.toReal + δ n := by
    intro n
    have H := (ENNReal.toReal_lt_toReal (hJfin n).ne ENNReal.ofReal_ne_top).mpr (hs n)
    rwa [ENNReal.toReal_ofReal (by positivity)] at H
  have hsq : ∀ n k, ‖fs n - fs k‖^2 ≤ 4 * (δ n + δ k) := by
    intro n k
    have H := hQ.proximal_midpoint (u := u) (hQfin n) (hQfin k)
    have hmid := hQ.midpoint_lt_top (hQfin n) (hQfin k)
    have hlo : a.toReal ≤ (J ((1/2:ℝ) • (fs n + fs k))).toReal :=
      (ENNReal.toReal_le_toReal ha.ne (proximalFunctional_lt_top hmid).ne).mpr (iInf_le J _)
    change (J _).toReal + _ ≤ ((J _).toReal + (J _).toReal)/2 at H
    linarith [hsmall n, hsmall k]
  have hC : CauchySeq fs := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hsmallδ : ∀ᶠ n in atTop, δ n < ε^2/16 :=
      hδ.eventually_lt_const (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmallδ
    refine ⟨N, fun n hn k hk => ?_⟩
    rw [dist_eq_norm]
    have := hsq n k
    have := hN n hn
    have := hN k hk
    nlinarith [norm_nonneg (fs n-fs k)]
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hC
  have hr : Tendsto (fun n => ENNReal.ofReal (a.toReal + δ n)) atTop (𝓝 a) := by
    have H := (ENNReal.continuous_ofReal.tendsto (a.toReal + 0)).comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a.toReal) atTop (𝓝 a.toReal)).add hδ)
    simpa only [add_zero, ENNReal.ofReal_toReal ha.ne, Function.comp_def] using H
  have hmin : (f, a) ∈ {p : E × ℝ≥0∞ | J p.1 ≤ p.2} :=
    (hQ.lowerSemicontinuous_proximal u).isClosed_epigraph.mem_of_tendsto
      (f := fun n => (fs n, ENNReal.ofReal (a.toReal + δ n)))
      (by simpa only [nhds_prod_eq] using hf.prodMk hr) (Eventually.of_forall fun n => (hs n).le)
  exact ⟨f, fun g => hmin.trans (iInf_le J g)⟩

lemma ClosedQuadraticEnergy.minimizer_unique {u f g : E}
    (hf : ∀ v, proximalFunctional Q u f ≤ proximalFunctional Q u v)
    (hg : ∀ v, proximalFunctional Q u g ≤ proximalFunctional Q u v) : f = g := by
  let J := proximalFunctional Q u
  have hJ0 : J 0 < ∞ := proximalFunctional_lt_top (by rw [hQ.zero]; simp)
  have hJf : J f < ∞ := (hf 0).trans_lt hJ0
  have hJg : J g < ∞ := (hg 0).trans_lt hJ0
  have hQf : Q f < ∞ := (le_add_right le_rfl).trans_lt hJf
  have hQg : Q g < ∞ := (le_add_right le_rfl).trans_lt hJg
  have H := hQ.proximal_midpoint (u := u) hQf hQg
  have hm := hQ.midpoint_lt_top hQf hQg
  have hfm : (J f).toReal ≤ (J ((1/2:ℝ) • (f+g))).toReal :=
    (ENNReal.toReal_le_toReal hJf.ne (proximalFunctional_lt_top hm).ne).mpr (hf _)
  have hgf : (J g).toReal ≤ (J f).toReal :=
    (ENNReal.toReal_le_toReal hJg.ne hJf.ne).mpr (hg f)
  change (J _).toReal + _ ≤ ((J _).toReal + (J _).toReal)/2 at H
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (f-g)]

lemma ClosedQuadraticEnergy.existsUnique_minimizer [CompleteSpace E] (u : E) :
    ∃! f : E, ∀ g : E, proximalFunctional Q u f ≤ proximalFunctional Q u g := by
  obtain ⟨f, hf⟩ := hQ.exists_minimizer u
  exact ⟨f, hf, fun g hg => hQ.minimizer_unique hg hf⟩

end WeakHessianFunctional

open Set Filter Bornology
open scoped Topology

end
end InlinedFile0

end OAI
