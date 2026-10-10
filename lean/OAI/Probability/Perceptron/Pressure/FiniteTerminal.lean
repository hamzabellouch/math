import Mathlib
import OAI.Probability.Perceptron.Variational.HeatLogBCF
import OAI.Probability.Perceptron.Variational.CovarianceMatrix

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial

lemma le_terminalTrial (m : Trial) (r t : Time) : m t ≤ terminalTrial m r t := by
  change m t ≤ if r ≤ t then 1 else m t
  split_ifs; exact m.le_one t; exact le_rfl

lemma terminalTrial_finite_range (m : Trial) (r : Time) (h : (Set.range m).Finite) :
    (Set.range (terminalTrial m r)).Finite := by
  apply (h.insert 1).subset
  rintro _ ⟨t,rfl⟩
  change (if r ≤ t then 1 else m t) ∈ _
  split_ifs
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ (mem_range_self t)

lemma terminalTrial_tail (m : Trial) {r t : Time} (hrt : r ≤ t) :
    tailIntegral (terminalTrial m r) t = 1 - (t : ℝ) := by
  have he : (fun s : Time => terminalTrial m r s) =ᵐ[timeLaw.restrict (Ici t)] (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    simp only [terminalTrial, ite_eq_left (hrt.trans hs)]
  rw [tailIntegral,integral_congr_ae he]
  simp [Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr t.property.2]

lemma tailIntegral_antitone (m : Trial) : Antitone (tailIntegral m) := by
  intro s t hst
  apply setIntegral_mono_set (trial_integrable m).integrableOn
    (Eventually.of_forall fun x => m.nonneg x)
  exact Filter.Eventually.of_forall (fun x hx => hst.trans hx)

lemma terminalTrial_entropy_finite (m : Trial) {r : Time} (hr : (r : ℝ) < 1) :
    entropy (terminalTrial m r) < ∞ := by
  have hbound : (∫⁻ t, (ENNReal.ofReal (tailIntegral (terminalTrial m r) t))⁻¹ -
      (ENNReal.ofReal (1-(t : ℝ)))⁻¹ ∂timeLaw) ≤ (ENNReal.ofReal (1-(r : ℝ)))⁻¹ := by
    calc
      _ ≤ ∫⁻ _t : Time, (ENNReal.ofReal (1-(r : ℝ)))⁻¹ ∂timeLaw := by
        apply lintegral_mono
        intro t
        dsimp only
        by_cases ht : r ≤ t
        · rw [terminalTrial_tail m ht,tsub_self]
          exact bot_le
        · have htr : t ≤ r := le_of_not_ge ht
          have hd := tailIntegral_antitone (terminalTrial m r) htr
          rw [terminalTrial_tail m le_rfl] at hd
          exact (tsub_le_self).trans (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hd))
      _ = _ := by simp
  unfold entropy
  apply ENNReal.div_lt_top _ (by norm_num)
  exact (hbound.trans_lt (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hr)))).ne

lemma terminalTrial_L1_le (m : Trial) (r : Time) :
    (∫ t, |terminalTrial m r t - m t| ∂timeLaw) ≤ 1-(r : ℝ) := by
  calc
    _ ≤ ∫ t, (Ici r).indicator (fun _ => (1 : ℝ)) t ∂timeLaw := by
      apply integral_mono ((trial_integrable _).sub (trial_integrable _)).abs
        ((integrable_const (1 : ℝ)).indicator measurableSet_Ici)
      intro t
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_terminalTrial m r t))]
      by_cases ht : r ≤ t
      · simp only [terminalTrial,ite_eq_left ht,Set.indicator_of_mem (show t ∈ Ici r from ht)]
        linarith [m.nonneg t]
      · simp only [terminalTrial,ite_eq_right ht,Set.indicator_of_notMem (show t ∉ Ici r from ht),sub_self]
        exact le_rfl
    _ = 1-(r : ℝ) := by
      rw [integral_indicator measurableSet_Ici]
      simp [Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr r.property.2]

lemma upperRoundedTrial_L1_le (m : Trial) (n : ℕ) :
    (∫ t, |upperRoundedTrial m n t - m t| ∂timeLaw) ≤ 1/((n+1 : ℕ) : ℝ) := by
  calc
    _ ≤ ∫ _t : Time, (1 : ℝ)/((n+1 : ℕ) : ℝ) ∂timeLaw := by
      apply integral_mono ((trial_integrable _).sub (trial_integrable _)).abs (integrable_const _)
      intro t
      dsimp only [Pi.sub_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr (le_upperRoundedTrial m n t))]
      exact upperRoundedTrial_sub_le m n t
    _ = _ := by simp

lemma exists_finite_terminal_trial_approx (m : Trial) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Trial, (Set.range q).Finite ∧ (∃ r : Time, (r : ℝ) < 1 ∧ ∀ t, r ≤ t → q t = 1) ∧
      (∀ t, m t ≤ q t) ∧ entropy q ≤ entropy m ∧ entropy q < ∞ ∧
      (∫ t, |q t-m t| ∂timeLaw) < ε := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (half_pos hε)
  let r : Time := ⟨1-min (ε/2) (1/2),by constructor <;> linarith [min_le_left (ε/2) (1/2),min_le_right (ε/2) (1/2),lt_min (half_pos hε) (by norm_num : (0:ℝ)<1/2)]⟩
  have hr : (r : ℝ) < 1 := by dsimp [r]; exact sub_lt_self _ (lt_min (half_pos hε) (by norm_num))
  let q := terminalTrial (upperRoundedTrial m n) r
  have hmq (t : Time) : m t ≤ q t := (le_upperRoundedTrial m n t).trans (le_terminalTrial _ r t)
  refine ⟨q,terminalTrial_finite_range _ r (upperRoundedTrial_finite_range m n),
    ⟨r,hr,fun t ht => by simp [q,terminalTrial,ht]⟩,hmq,entropy_antitone hmq,
    terminalTrial_entropy_finite _ hr,?_⟩
  calc
    _ ≤ (∫ t, |q t-upperRoundedTrial m n t| + |upperRoundedTrial m n t-m t| ∂timeLaw) :=
      integral_mono ((trial_integrable _).sub (trial_integrable _)).abs
        (((trial_integrable _).sub (trial_integrable _)).abs.add
          ((trial_integrable _).sub (trial_integrable _)).abs) (fun t => abs_sub_le _ _ _)
    _ = (∫ t, |q t-upperRoundedTrial m n t| ∂timeLaw) +
        ∫ t, |upperRoundedTrial m n t-m t| ∂timeLaw :=
      integral_add ((trial_integrable _).sub (trial_integrable _)).abs ((trial_integrable _).sub (trial_integrable _)).abs
    _ ≤ 1-(r : ℝ)+1/((n+1 : ℕ) : ℝ) := add_le_add (terminalTrial_L1_le _ r) (upperRoundedTrial_L1_le m n)
    _ < ε := by
      have hn' : 1/((n+1 : ℕ) : ℝ) < ε/2 := by simpa only [Nat.cast_add,Nat.cast_one] using hn
      dsimp [r]
      linarith [min_le_left (ε/2) (1/2)]

def FiniteTerminal (m : Trial) : Prop :=
  (Set.range m).Finite ∧ ∃ r : Time, (r : ℝ) < 1 ∧ ∀ t, r ≤ t → m t = 1

def finiteTerminalVariational (P : Measure BrownianPath) (α : ℝ) (f : ℝ →ᵇ ℝ) : EReal :=
  ⨅ m : {m : Trial // FiniteTerminal m},
    ((α * controlValue P f m.val : ℝ) : EReal) + (entropy m.val).toEReal

lemma finiteTerminal_one : FiniteTerminal oneTrial := by
  constructor
  · change (Set.range (fun _ : Time => (1 : ℝ))).Finite
    simpa only [Set.range_const] using Set.finite_singleton (1 : ℝ)
  · exact ⟨0,by norm_num,fun _ _ => rfl⟩

lemma finiteTerminalVariational_bounds (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((-α*‖f‖ : ℝ) : EReal) ≤ finiteTerminalVariational P α f ∧
      finiteTerminalVariational P α f ≤ ((α*‖f‖ : ℝ) : EReal) := by
  constructor
  · apply (terminalVariational_bounds P α hα f).1.trans
    apply le_iInf
    intro m
    exact iInf_le _ m.val
  · calc
      _ ≤ ((α*controlValue P f oneTrial : ℝ) : EReal) + (entropy oneTrial).toEReal :=
        iInf_le (fun m : {m : Trial // FiniteTerminal m} =>
          ((α*controlValue P f m.val : ℝ) : EReal)+(entropy m.val).toEReal) ⟨oneTrial,finiteTerminal_one⟩
      _ ≤ ((α*‖f‖ : ℝ) : EReal) := by
        simp only [entropy_oneTrial,EReal.coe_ennreal_zero,add_zero]
        exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left (controlValue_le_norm P f _) hα)

lemma finiteTerminalVariational_coe_toReal (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((finiteTerminalVariational P α f).toReal : EReal) = finiteTerminalVariational P α f := by
  obtain ⟨hlo,hhi⟩ := finiteTerminalVariational_bounds P α hα f
  exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)

lemma terminalVariational_eq_finiteTerminal (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) :
    terminalVariational P α f = finiteTerminalVariational P α f := by
  apply le_antisymm
  · apply le_iInf
    intro m
    exact iInf_le _ m.val
  · apply le_iInf
    intro m
    by_cases hm : entropy m = ∞
    · simp only [hm,EReal.coe_ennreal_top,EReal.coe_add_top,le_top]
    · rw [← EReal.coe_ennreal_toReal hm,← EReal.coe_add,
        ← finiteTerminalVariational_coe_toReal P α hα f,EReal.coe_le_coe_iff]
      apply le_of_forall_pos_le_add
      intro ε hε
      let C : ℝ := α*(3/2)*(L : ℝ)^2
      have hC : 0 ≤ C := by dsimp [C]; positivity
      obtain ⟨q,hqfin,hqterm,_,hS,hSf,hL1⟩ :=
        exists_finite_terminal_trial_approx m (div_pos hε (by positivity : 0 < C+1))
      have hi : finiteTerminalVariational P α f ≤
          ((α*controlValue P f q : ℝ) : EReal) + (entropy q).toEReal :=
        iInf_le (fun m : {m : Trial // FiniteTerminal m} =>
            ((α*controlValue P f m.val : ℝ) : EReal)+(entropy m.val).toEReal) ⟨q,hqfin,hqterm⟩
      rw [← EReal.coe_ennreal_toReal hSf.ne,← EReal.coe_add,
        ← finiteTerminalVariational_coe_toReal P α hα f,EReal.coe_le_coe_iff] at hi
      have hc := (abs_le.mp (controlValue_trial_abs_sub_le P f q m L hf)).2
      have hS' := ENNReal.toReal_mono hm hS
      have herror : C*(∫ t, |q t-m t| ∂timeLaw) ≤ ε := by
        have h := mul_le_mul_of_nonneg_left hL1.le hC
        have he : C*(ε/(C+1)) ≤ ε := by
          rw [← mul_div_assoc]
          apply (div_le_iff₀ (by positivity : 0 < C+1)).mpr
          nlinarith
        exact h.trans he
      have hc' := mul_le_mul_of_nonneg_left hc hα
      change (α*(3/2)*(L : ℝ)^2)*(∫ t, |q t-m t| ∂timeLaw) ≤ ε at herror
      nlinarith

open scoped ContDiff

def Jet3.ofCompactSmooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) : Jet3 := by
  have h1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp h1).2
  have h3 : ContDiff ℝ ∞ (deriv (deriv (deriv f))) := (contDiff_infty_iff_deriv.mp h2).2
  exact {
    f := ofCompactSupport f hf.continuous hs
    d1 := ofCompactSupport (deriv f) h1.continuous hs.deriv
    d2 := ofCompactSupport (deriv (deriv f)) h2.continuous hs.deriv.deriv
    d3 := ofCompactSupport (deriv (deriv (deriv f))) h3.continuous hs.deriv.deriv.deriv
    has1 := fun x => (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
    has2 := fun x => (h1.differentiable (by norm_num)).differentiableAt.hasDerivAt
    has3 := fun x => (h2.differentiable (by norm_num)).differentiableAt.hasDerivAt }

@[simp] lemma Jet3.ofCompactSmooth_apply (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (x : ℝ) : (Jet3.ofCompactSmooth f hf hs).f x = f x := rfl

lemma exists_bounded_smooth_terminal (f : ℝ →ᵇ ℝ) {R ε : ℝ} (hR : 0 < R)
    (hε : 0 < ε) : ∃ g : Jet3, ‖g.f‖ ≤ ‖f‖+ε ∧
      ∀ x : ℝ, |x| ≤ R → |g.f x-f x| < ε := by
  let ψ : ContDiffBump (0 : ℝ) := ⟨R,R+1,hR,by linarith⟩
  let F : ℝ → ℝ := fun x => ψ x*f x
  have hF : Continuous F := ψ.continuous.mul f.continuous
  have hFs : HasCompactSupport F := ψ.hasCompactSupport.mul_right
  obtain ⟨g,hg,hgf,hgs⟩ := hF.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => ε) continuous_const (fun _ => hε)
  have hg' : ContDiff ℝ ∞ g := hg
  have hgs' : HasCompactSupport g := hFs.mono hgs
  refine ⟨Jet3.ofCompactSmooth g hg' hgs',?_,?_⟩
  · rw [BoundedContinuousFunction.norm_le (by positivity : 0 ≤ ‖f‖+ε)]
    intro x
    change |g x| ≤ ‖f‖+ε
    have hFbound : |F x| ≤ ‖f‖ := by
      dsimp [F]
      rw [abs_mul,abs_of_nonneg ψ.nonneg]
      exact (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) ψ.nonneg).trans
        (mul_le_of_le_one_left (norm_nonneg f) ψ.le_one)
    have h := hgf x
    rw [Real.dist_eq] at h
    calc
      |g x| = |(g x-F x)+F x| := by congr 1; ring
      _ ≤ |g x-F x|+|F x| := abs_add_le _ _
      _ ≤ ‖f‖+ε := by linarith
  · intro x hx
    have he : ψ x = 1 := ψ.one_of_mem_closedBall (by simpa [Real.dist_eq] using hx)
    simpa only [Jet3.ofCompactSmooth_apply,F,he,one_mul,Real.dist_eq] using hgf x

lemma exists_bounded_smooth_terminal_sequence (f : ℝ →ᵇ ℝ) :
    ∃ g : ℕ → Jet3, (∀ n, ‖(g n).f‖ ≤ ‖f‖+1) ∧
      ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, |x| ≤ R → |(g n).f x-f x| ≤ ε := by
  have h (n : ℕ) := exists_bounded_smooth_terminal f
    (by positivity : 0 < (n : ℝ)+1) (by positivity : 0 < 1/((n : ℝ)+1))
  choose g hg hcomp using h
  refine ⟨g,?_,?_⟩
  · intro n
    apply (hg n).trans
    have h : 1/((n : ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  · intro R _ ε hε
    obtain ⟨N₁,hR⟩ := exists_nat_ge R
    obtain ⟨N₂,hε'⟩ := exists_nat_one_div_lt hε
    refine ⟨max N₁ N₂,fun n hn x hx => ?_⟩
    have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
    have hn2 : N₂ ≤ n := (le_max_right _ _).trans hn
    have hx' : |x| ≤ (n : ℝ)+1 := by
      have hc : (N₁ : ℝ) ≤ n := Nat.cast_le.mpr hn1
      linarith
    apply (hcomp n x hx').le.trans
    apply le_trans _ hε'.le
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn2 1)

lemma finiteTerminalVariational_toReal_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f g : ℝ →ᵇ ℝ) (δ : ℝ)
    (hfg : ∀ m : Trial, controlValue P f m - controlValue P g m ≤ δ) :
    (finiteTerminalVariational P α f).toReal - (finiteTerminalVariational P α g).toReal ≤ α*δ := by
  have hbound : (((finiteTerminalVariational P α f).toReal - α*δ : ℝ) : EReal) ≤
      finiteTerminalVariational P α g := by
    apply le_iInf
    intro m
    have h : finiteTerminalVariational P α f ≤
        ((α*controlValue P f m : ℝ) : EReal) + (entropy m).toEReal := iInf_le (fun m : {m : Trial // FiniteTerminal m} =>
          ((α*controlValue P f m.val : ℝ) : EReal)+(entropy m.val).toEReal) m
    have hh : (((finiteTerminalVariational P α f).toReal - α*δ : ℝ) : EReal) ≤
        ((α*controlValue P f m - α*δ : ℝ) : EReal) + (entropy m).toEReal := by
      have hs := add_le_add_right h ((-α*δ : ℝ) : EReal)
      rw [← finiteTerminalVariational_coe_toReal P α hα f] at hs
      convert hs using 1 <;> simp only [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] <;>
        push_cast <;> simp only [neg_mul, add_assoc, add_comm]
    apply hh.trans
    apply add_le_add_left
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hfg m) hα]
  rw [← finiteTerminalVariational_coe_toReal P α hα g, EReal.coe_le_coe_iff] at hbound
  linarith

lemma finiteTerminalVariational_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f g : ℝ →ᵇ ℝ) (δ : ℝ)
    (hfg : ∀ m : Trial, |controlValue P f m - controlValue P g m| ≤ δ) :
    |(finiteTerminalVariational P α f).toReal - (finiteTerminalVariational P α g).toReal| ≤ α*δ := by
  have h₁ := finiteTerminalVariational_toReal_sub_le P α hα f g δ
    (fun m => (abs_le.mp (hfg m)).2)
  have h₂ := finiteTerminalVariational_toReal_sub_le P α hα g f δ
    (fun m => by have hh := (abs_le.mp (hfg m)).1; linarith)
  exact abs_le.mpr ⟨by linarith, h₁⟩

lemma terminalVariational_eq_finiteTerminal_continuous
    (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    terminalVariational P α f = finiteTerminalVariational P α f := by
  rw [← terminalVariational_coe_toReal P α hα f,
    ← finiteTerminalVariational_coe_toReal P α hα f]
  congr 1
  apply le_antisymm
  · apply EReal.coe_le_coe_iff.mp
    rw [terminalVariational_coe_toReal P α hα f,
      finiteTerminalVariational_coe_toReal P α hα f]
    exact le_iInf fun m => iInf_le _ m.val
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g,hg,hcomp⟩ := exists_bounded_smooth_terminal_sequence f
    let δ := ε/(2*(α+1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨N,hN⟩ := controlValue_uniform_of_compact P hB f (fun n => (g n).f)
      (‖f‖+1) (by positivity) (by linarith) hg hcomp δ hδ
    have hclose : ∀ m : Trial,
        |controlValue P (g N).f m - controlValue P f m| ≤ δ := fun m => (hN N le_rfl m).le
    have h₁ := (abs_le.mp (finiteTerminalVariational_abs_sub_le P α hα (g N).f f δ hclose)).1
    have h₂ := (abs_le.mp (terminalVariational_abs_sub_le P α hα (g N).f f δ hclose)).2
    have hlipschitz : LipschitzWith ‖(g N).d1‖₊ (g N).f := by
      apply lipschitzWith_of_nnnorm_deriv_le (fun point => ((g N).has1 point).differentiableAt)
      intro point
      rw [(g N).deriv_eq]
      exact_mod_cast (g N).d1.norm_coe_le_norm point
    have he := terminalVariational_eq_finiteTerminal P α hα (g N).f ‖(g N).d1‖₊ hlipschitz
    have he' := congrArg EReal.toReal he
    have herr : 2*α*δ ≤ ε := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 2*(α+1))).mpr
      nlinarith
    linarith

abbrev RadialSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n+1))

def radialNormalizer (n : ℕ) : ℝ := ((2*Real.pi)^(((n+1 : ℕ) : ℝ)/2))⁻¹

def canonicalRadialDensity (n : ℕ) (b : ℝ) (x : RadialSpace n) : ℝ :=
  radialNormalizer n * Real.exp (-(b/2)*‖x‖^2)

def canonicalRadialMass (n : ℕ) (b : ℝ) : Measure (RadialSpace n) :=
  volume.withDensity (fun x => ENNReal.ofReal (canonicalRadialDensity n b x))

lemma radialNormalizer_pos (n : ℕ) : 0 < radialNormalizer n := by
  unfold radialNormalizer
  positivity

lemma canonicalRadialDensity_pos (n : ℕ) (b : ℝ) (x : RadialSpace n) :
    0 < canonicalRadialDensity n b x := mul_pos (radialNormalizer_pos n) (Real.exp_pos _)

lemma canonicalRadialDensity_continuous (n : ℕ) (b : ℝ) :
    Continuous (canonicalRadialDensity n b) := by unfold canonicalRadialDensity; fun_prop

lemma integrable_exp_neg_norm_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : RadialSpace n => Real.exp (-(b/2)*‖x‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := ((b/2 : ℝ) : ℂ)) (by simpa using half_pos hb) 0 (0 : RadialSpace n)).re
  convert h using 1
  ext x
  simp only [zero_mul,add_zero,← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_neg,
    ]
  exact (Complex.exp_ofReal_re _).symm

lemma canonicalRadialDensity_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (canonicalRadialDensity n b) :=
  (integrable_exp_neg_norm_sq n hb).const_mul _

lemma canonicalRadialDensity_integral (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x, canonicalRadialDensity n b x) = b ^ (-((n+1 : ℕ) : ℝ)/2) := by
  simp only [canonicalRadialDensity]
  rw [integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (half_pos hb)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [show Real.pi/(b/2) = (2*Real.pi)/b by ring,Real.div_rpow (by positivity) hb.le]
  unfold radialNormalizer
  rw [show -((n+1 : ℕ) : ℝ)/2 = -(((n+1 : ℕ) : ℝ)/2) by ring, Real.rpow_neg hb.le]
  field_simp

instance (n : ℕ) : IsProbabilityMeasure (canonicalRadialMass n 1) := by
  constructor
  rw [canonicalRadialMass,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal
      (canonicalRadialDensity_integrable n (by norm_num : (0:ℝ)<1))
      (Eventually.of_forall fun x => (canonicalRadialDensity_pos n 1 x).le),
    canonicalRadialDensity_integral n (by norm_num : (0:ℝ)<1)]
  simp

lemma canonicalRadialMass_apply {n : ℕ} {b : ℝ} (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) :
    canonicalRadialMass n b A = ENNReal.ofReal (∫ x in A, canonicalRadialDensity n b x) := by
  rw [canonicalRadialMass,withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal (canonicalRadialDensity_integrable n hb).integrableOn
    (Eventually.of_forall fun x => (canonicalRadialDensity_pos n b x).le)).symm

lemma canonicalRadial_mass_le {n : ℕ} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A)
    (hc : ∀ x ∈ A, -(a/2)*‖x‖^2 ≤ c-(b/2)*‖x‖^2) :
    canonicalRadialMass n a A ≤ ENNReal.ofReal (Real.exp c * b ^ (-((n+1 : ℕ) : ℝ)/2)) := by
  rw [canonicalRadialMass_apply ha hA]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ x in A, Real.exp c * canonicalRadialDensity n b x := by
      apply setIntegral_mono_on (canonicalRadialDensity_integrable n ha).integrableOn
        ((canonicalRadialDensity_integrable n hb).const_mul _).integrableOn hA
      intro x hx
      unfold canonicalRadialDensity
      calc
        _ ≤ radialNormalizer n * Real.exp (c-(b/2)*‖x‖^2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hc x hx)) (radialNormalizer_pos n).le
        _ = _ := by rw [Real.exp_sub,neg_mul,Real.exp_neg]; ring
    _ ≤ ∫ x, Real.exp c * canonicalRadialDensity n b x := by
      apply setIntegral_le_integral ((canonicalRadialDensity_integrable n hb).const_mul _)
      exact Eventually.of_forall fun x => (mul_pos (Real.exp_pos c) (canonicalRadialDensity_pos n b x)).le
    _ = _ := by rw [integral_const_mul,canonicalRadialDensity_integral n hb]

end SphericalPerceptronFreeEnergy

end

end OAI
