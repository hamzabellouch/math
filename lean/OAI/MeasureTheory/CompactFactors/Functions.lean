import OAI.MeasureTheory.CompactFactors.Kernels

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.CompactFunctions
open MeasureTheory
open scoped BigOperators
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

def At (μ : Measure X) (q : X → Y) (H : X → ℂ) (ε : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → X → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ x, ∑ i, ‖Hf i x‖ ≤ C) ∧
    ∀ k : K, ∃ a : Y → Fin r → ℂ, Measurable a ∧ (∀ y, ‖a y‖ ≤ B) ∧
      Integrable (fun x => dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2) μ ∧
      (∫ x, dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2 ∂μ) < ε^2

def Compact (μ : Measure X) (q : X → Y) (H : X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → At (K := K) μ q H ε

lemma at_of_finite {μ : Measure X} {q : X → Y} {H : X → ℂ} {ε : ℝ}
    {I : Type*} [Fintype I] (B C : ℝ) (Hf : I → X → ℂ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hm : ∀ i, Measurable (Hf i))
    (hb : ∀ x, ∑ i, ‖Hf i x‖ ≤ C)
    (ha : ∀ k : K, ∃ a : Y → I → ℂ, Measurable a ∧ (∀ y, ‖a y‖ ≤ B) ∧
      Integrable (fun x => dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2) μ ∧
      (∫ x, dist (H (k • x)) (∑ i, a (q x) i * Hf i x)^2 ∂μ) < ε^2) :
    At (K := K) μ q H ε := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨_, B, C, fun i => Hf (e i), hB, hC, fun i => hm (e i), ?_, ?_⟩
  · intro x
    rw [e.sum_comp (fun i => ‖Hf i x‖)]
    exact hb x
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    have hs (x : X) : (∑ i, a (q x) (e i) * Hf (e i) x) = ∑ i, a (q x) i * Hf i x := e.sum_comp (fun i => a (q x) i * Hf i x)
    refine ⟨fun y i => a y (e i), Measurable.of_eval (fun i => (measurable_pi_iff.mp ham) (e i)), ?_, ?_, ?_⟩
    · intro y
      rw [pi_norm_le_iff_of_nonneg hB]
      exact fun i => (norm_le_pi_norm (a y) (e i)).trans (hab y)
    · simpa only [hs] using hai
    · simpa only [hs] using hae

lemma module_bound {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℂ)
    {B C : ℝ} (hB : 0 ≤ B) (ha : ‖a‖ ≤ B) (hH : ∑ i, ‖H i‖ ≤ C) :
    ‖∑ i, a i * H i‖ ≤ B*C := by
  calc
    ‖∑ i, a i * H i‖ ≤ ∑ i, ‖a i * H i‖ := norm_sum_le _ _
    _ ≤ ∑ i, B*‖H i‖ := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm a i).trans ha) (norm_nonneg _)
    _ = B * ∑ i, ‖H i‖ := by rw [Finset.mul_sum]
    _ ≤ B*C := mul_le_mul_of_nonneg_left hH hB

lemma dist_sq_add (a b c d : ℂ) :
    dist (a+b) (c+d)^2 ≤ 2*(dist a c^2 + dist b d^2) := by
  have h := dist_add_add_le a b c d
  nlinarith [dist_nonneg (x := a+b) (y := c+d), dist_nonneg (x := a) (y := c),
    dist_nonneg (x := b) (y := d), sq_nonneg (dist a c - dist b d)]

lemma dist_sq_chain (a b c : ℂ) :
    dist a c^2 ≤ 2*(dist a b^2 + dist b c^2) := by
  have h := dist_triangle a b c
  nlinarith [dist_nonneg (x := a) (y := c), dist_nonneg (x := a) (y := b),
    dist_nonneg (x := b) (y := c), sq_nonneg (dist a b - dist b c)]

lemma compact_const (μ : Measure X) (q : X → Y) (c : ℂ) :
    Compact (K := K) μ q (fun _ => c) := by
  intro ε hε
  apply at_of_finite (I := Unit) 1 ‖c‖ (fun _ _ => c) (by norm_num) (norm_nonneg _) (fun _ => measurable_const)
  · intro x; simp
  · intro k
    refine ⟨fun _ _ => 1, measurable_const, fun _ => by simp, ?_, ?_⟩
    · simp
    · simpa using sq_pos_of_pos hε

lemma compact_conj {μ : Measure X} {q : X → Y} {H : X → ℂ}
    (hH : Compact (K := K) μ q H) : Compact (K := K) μ q (fun x => star (H x)) := by
  intro ε hε
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH ε hε
  refine ⟨r, B, C, fun i x => star (F i x), hB, hC,
    fun i => Complex.continuous_conj.measurable.comp (hm i), ?_, ?_⟩
  · intro x; simpa using hb x
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    refine ⟨fun y i => star (a y i), (Measurable.of_eval (fun i => Complex.continuous_conj.measurable.comp ((measurable_pi_iff.mp ham) i))), ?_, ?_, ?_⟩
    · intro y
      rw [pi_norm_le_iff_of_nonneg hB]
      intro i
      simpa using (norm_le_pi_norm (a y) i).trans (hab y)
    · have hs (x : X) : (∑ i, star (a (q x) i) * star (F i x)) = star (∑ i, a (q x) i * F i x) := by
        simp only [star_sum, star_mul, mul_comm]
      simpa only [hs, dist_star_star] using hai
    · have hs (x : X) : (∑ i, star (a (q x) i) * star (F i x)) = star (∑ i, a (q x) i * F i x) := by
        simp only [star_sum, star_mul, mul_comm]
      simpa only [hs, dist_star_star] using hae

lemma compact_add {μ : Measure X} {q : X → Y} {H G : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H) (hGm : Measurable G)
    (hH : Compact (K := K) μ q H) (hG : Compact (K := K) μ q G) :
    Compact (K := K) μ q (fun x => H x + G x) := by
  intro ε hε
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH (ε/2) (by positivity)
  obtain ⟨s, D, E, J, hD, hE, hjm, hjb, hd⟩ := hG (ε/2) (by positivity)
  classical
  apply at_of_finite (I := Fin r ⊕ Fin s) (max B D) (C+E) (Sum.elim F J)
    (hB.trans (le_max_left _ _)) (add_nonneg hC hE)
  · intro i; cases i with
    | inl i => exact hm i
    | inr i => exact hjm i
  · intro x
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using add_le_add (hb x) (hjb x)
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    obtain ⟨b, hbm, hbb, hbi, hbe⟩ := hd k
    let A : Y → Fin r ⊕ Fin s → ℂ := fun y => Sum.elim (a y) (b y)
    have hAm : Measurable A := by
      apply Measurable.of_eval
      intro i
      cases i with
      | inl i => exact (measurable_pi_iff.mp ham) i
      | inr i => exact (measurable_pi_iff.mp hbm) i
    have hAb (y : Y) : ‖A y‖ ≤ max B D := by
      rw [pi_norm_le_iff_of_nonneg (hB.trans (le_max_left _ _))]
      intro i
      cases i with
      | inl i => exact ((norm_le_pi_norm (a y) i).trans (hab y)).trans (le_max_left _ _)
      | inr i => exact ((norm_le_pi_norm (b y) i).trans (hbb y)).trans (le_max_right _ _)
    let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
    let G₀ : X → ℂ := fun x => ∑ i, b (q x) i * J i x
    have hFm : Measurable F₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp hq).mul (hm i))
    have hGm₀ : Measurable G₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp hbm) i).comp hq).mul (hjm i))
    have hiM : Integrable (fun x => 2*(dist (H (k • x)) (F₀ x)^2 +
        dist (G (k • x)) (G₀ x)^2)) μ := (hai.add hbi).const_mul 2
    have hmajor (x : X) := dist_sq_add (H (k • x)) (G (k • x)) (F₀ x) (G₀ x)
    have hi : Integrable (fun x => dist (H (k • x)+G (k • x)) (F₀ x+G₀ x)^2) μ :=
      hiM.mono' ((((hHm.comp (measurable_const_smul k)).add (hGm.comp (measurable_const_smul k))).dist
        (hFm.add hGm₀)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
    have he : (∫ x, dist (H (k • x)+G (k • x)) (F₀ x+G₀ x)^2 ∂μ) < ε^2 := by
      calc
        _ ≤ ∫ x, 2*(dist (H (k • x)) (F₀ x)^2 + dist (G (k • x)) (G₀ x)^2) ∂μ :=
          integral_mono hi hiM hmajor
        _ = 2*((∫ x, dist (H (k • x)) (F₀ x)^2 ∂μ) + ∫ x, dist (G (k • x)) (G₀ x)^2 ∂μ) := by
          rw [integral_const_mul, integral_add hai hbi]
        _ < ε^2 := by dsimp [F₀, G₀]; nlinarith
    refine ⟨A, hAm, hAb, ?_, ?_⟩
    · simpa only [Fintype.sum_sum_type, A, Sum.elim_inl, Sum.elim_inr] using hi
    · simpa only [Fintype.sum_sum_type, A, Sum.elim_inl, Sum.elim_inr] using he

lemma compact_mul {μ : Measure X} {q : X → Y} {H G : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H) (hGm : Measurable G)
    (RG : ℝ) (hRG : 0 ≤ RG) (hGb : ∀ x, ‖G x‖ ≤ RG)
    (hH : Compact (K := K) μ q H) (hG : Compact (K := K) μ q G) :
    Compact (K := K) μ q (fun x => H x * G x) := by
  intro ε hε
  let δ := ε/(2*(RG+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH δ hδ
  let γ := ε/(2*(B*C+1))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨s, D, E, J, hD, hE, hjm, hjb, hd⟩ := hG γ hγ
  classical
  apply at_of_finite (I := Fin r × Fin s) (B*D) (C*E) (fun i x => F i.1 x * J i.2 x)
    (mul_nonneg hB hD) (mul_nonneg hC hE) (fun i => (hm i.1).mul (hjm i.2))
  · intro x
    calc
      (∑ i : Fin r × Fin s, ‖F i.1 x * J i.2 x‖) = (∑ i, ‖F i x‖) * ∑ j, ‖J j x‖ := by
        simp only [Fintype.sum_prod_type, norm_mul, Finset.sum_mul_sum]
      _ ≤ C*E := mul_le_mul (hb x) (hjb x) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hC
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    obtain ⟨b, hbm, hbb, hbi, hbe⟩ := hd k
    let A : Y → Fin r × Fin s → ℂ := fun y i => a y i.1 * b y i.2
    have hAm : Measurable A := Measurable.of_eval (fun i =>
      ((measurable_pi_iff.mp ham) i.1).mul ((measurable_pi_iff.mp hbm) i.2))
    have hAb (y : Y) : ‖A y‖ ≤ B*D := by
      rw [pi_norm_le_iff_of_nonneg (mul_nonneg hB hD)]
      intro i
      change ‖a y i.1 * b y i.2‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (a y) i.1).trans (hab y))
        ((norm_le_pi_norm (b y) i.2).trans (hbb y)) (norm_nonneg _) hB
    let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
    let G₀ : X → ℂ := fun x => ∑ i, b (q x) i * J i x
    have hFm : Measurable F₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp hq).mul (hm i))
    have hGm₀ : Measurable G₀ := Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp hbm) i).comp hq).mul (hjm i))
    have hFbound (x : X) : ‖F₀ x‖ ≤ B*C := module_bound _ _ hB (hab _) (hb _)
    have hmajor (x : X) : dist (H (k • x)*G (k • x)) (F₀ x*G₀ x)^2 ≤
        2*(RG^2*dist (H (k • x)) (F₀ x)^2 + (B*C)^2*dist (G (k • x)) (G₀ x)^2) := by
      have heq : H (k • x)*G (k • x)-F₀ x*G₀ x =
          (H (k • x)-F₀ x)*G (k • x)+F₀ x*(G (k • x)-G₀ x) := by ring
      have hn : dist (H (k • x)*G (k • x)) (F₀ x*G₀ x) ≤
          RG*dist (H (k • x)) (F₀ x) + (B*C)*dist (G (k • x)) (G₀ x) := by
        rw [dist_eq_norm, heq]
        refine (norm_add_le _ _).trans ?_
        simp only [norm_mul, ← dist_eq_norm]
        exact add_le_add (by nlinarith [hGb (k • x), dist_nonneg (x := H (k • x)) (y := F₀ x)])
          (mul_le_mul_of_nonneg_right (hFbound x) dist_nonneg)
      have h₁ : 0 ≤ RG*dist (H (k • x)) (F₀ x) := mul_nonneg hRG dist_nonneg
      have h₂ : 0 ≤ (B*C)*dist (G (k • x)) (G₀ x) := mul_nonneg (mul_nonneg hB hC) dist_nonneg
      nlinarith [dist_nonneg (x := H (k • x)*G (k • x)) (y := F₀ x*G₀ x),
        sq_nonneg (RG*dist (H (k • x)) (F₀ x) - (B*C)*dist (G (k • x)) (G₀ x))]
    have hiM : Integrable (fun x => 2*(RG^2*dist (H (k • x)) (F₀ x)^2 +
        (B*C)^2*dist (G (k • x)) (G₀ x)^2)) μ :=
      ((hai.const_mul (RG^2)).add (hbi.const_mul ((B*C)^2))).const_mul 2
    have hi : Integrable (fun x => dist (H (k • x)*G (k • x)) (F₀ x*G₀ x)^2) μ :=
      hiM.mono' ((((hHm.comp (measurable_const_smul k)).mul (hGm.comp (measurable_const_smul k))).dist
        (hFm.mul hGm₀)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
    have hδB : RG*δ < ε/2 := by
      dsimp [δ]
      have hh : 0 < 2*(RG+1) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hh]
      nlinarith
    have hγB : (B*C)*γ < ε/2 := by
      dsimp [γ]
      have hh : 0 < 2*(B*C+1) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hh]
      nlinarith
    have he : (∫ x, dist (H (k • x)*G (k • x)) (F₀ x*G₀ x)^2 ∂μ) < ε^2 := by
      calc
        _ ≤ ∫ x, 2*(RG^2*dist (H (k • x)) (F₀ x)^2 +
            (B*C)^2*dist (G (k • x)) (G₀ x)^2) ∂μ := integral_mono hi hiM hmajor
        _ = 2*(RG^2*(∫ x, dist (H (k • x)) (F₀ x)^2 ∂μ) +
            (B*C)^2*∫ x, dist (G (k • x)) (G₀ x)^2 ∂μ) := by
          rw [integral_const_mul, integral_add (hai.const_mul _) (hbi.const_mul _),
            integral_const_mul, integral_const_mul]
        _ ≤ 2*((RG*δ)^2 + ((B*C)*γ)^2) := by
          have h₁ := mul_le_mul_of_nonneg_left hae.le (sq_nonneg RG)
          have h₂ := mul_le_mul_of_nonneg_left hbe.le (sq_nonneg (B*C))
          dsimp [F₀, G₀]
          nlinarith
        _ < ε^2 := by
          have h₁ := sq_lt_sq₀ (mul_nonneg hRG hδ.le) (by positivity : 0 ≤ ε/2) |>.mpr hδB
          have h₂ := sq_lt_sq₀ (mul_nonneg (mul_nonneg hB hC) hγ.le) (by positivity : 0 ≤ ε/2) |>.mpr hγB
          nlinarith
    have hs (x : X) : (∑ i : Fin r × Fin s, A (q x) i * (F i.1 x * J i.2 x)) = F₀ x*G₀ x := by
      simp only [Fintype.sum_prod_type, A, F₀, G₀, Finset.sum_mul_sum]
      congr 1
      funext i
      congr 1
      funext j
      ring
    refine ⟨A, hAm, hAb, ?_, ?_⟩
    · simpa only [hs] using hi
    · simpa only [hs] using he

lemma compact_of_l2_approximation {μ : Measure X} {q : X → Y} {H : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (happ : ∀ δ : ℝ, 0 < δ → ∃ G : X → ℂ, Measurable G ∧ Compact (K := K) μ q G ∧
      Integrable (fun x => dist (H x) (G x)^2) μ ∧ (∫ x, dist (H x) (G x)^2 ∂μ) < δ^2) :
    Compact (K := K) μ q H := by
  intro ε hε
  obtain ⟨G, hGm, hG, hi₀, he₀⟩ := happ (ε/2) (by positivity)
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hG (ε/2) (by positivity)
  refine ⟨r, B, C, F, hB, hC, hm, hb, ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha k
  let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
  have hFm : Measurable F₀ := Finset.measurable_sum _ (fun i _ =>
    (((measurable_pi_iff.mp ham) i).comp hq).mul (hm i))
  have hi₁ : Integrable (fun x => dist (H (k • x)) (G (k • x))^2) μ :=
    (hpres k).integrable_comp hi₀.aestronglyMeasurable |>.mpr hi₀
  have he₁ : (∫ x, dist (H (k • x)) (G (k • x))^2 ∂μ) < (ε/2)^2 := by
    have hm₀ : AEStronglyMeasurable (fun x => dist (H x) (G x)^2) (μ.map (fun x : X => k • x)) := by
      rw [(hpres k).map_eq]
      exact hi₀.aestronglyMeasurable
    rw [← integral_map (hpres k).measurable.aemeasurable hm₀, (hpres k).map_eq]
    exact he₀
  have hiM : Integrable (fun x => 2*(dist (H (k • x)) (G (k • x))^2 +
      dist (G (k • x)) (F₀ x)^2)) μ := (hi₁.add hai).const_mul 2
  have hmajor (x : X) := dist_sq_chain (H (k • x)) (G (k • x)) (F₀ x)
  have hi : Integrable (fun x => dist (H (k • x)) (F₀ x)^2) μ :=
    hiM.mono' (((hHm.comp (measurable_const_smul k)).dist hFm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
  refine ⟨a, ham, hab, hi, ?_⟩
  calc
    _ ≤ ∫ x, 2*(dist (H (k • x)) (G (k • x))^2 + dist (G (k • x)) (F₀ x)^2) ∂μ :=
      integral_mono hi hiM hmajor
    _ = 2*((∫ x, dist (H (k • x)) (G (k • x))^2 ∂μ) + ∫ x, dist (G (k • x)) (F₀ x)^2 ∂μ) := by
      rw [integral_const_mul, integral_add hi₁ hai]
    _ < ε^2 := by dsimp [F₀]; nlinarith

end EuclideanFiveColor.CompactFunctions

namespace EuclideanFiveColor.Quantize
open MeasureTheory
variable {A Y : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [MeasurableSpace Y]

lemma finite_measurable_choice {n : ℕ} (P : Y → Fin n → Prop)
    (hm : ∀ i, MeasurableSet {y | P y i}) (he : ∀ y, ∃ i, P y i) :
    ∃ f : Y → Fin n, Measurable f ∧ ∀ y, P y (f y) := by
  classical
  let Q : Y → ℕ → Prop := fun y k => ∃ i : Fin n, i.val = k ∧ P y i
  have hQ (y : Y) : ∃ k, Q y k := by
    obtain ⟨i, hi⟩ := he y
    exact ⟨i.val, i, rfl, hi⟩
  have hmQ (k : ℕ) : MeasurableSet {y | Q y k} := by
    have heq : {y | Q y k} = ⋃ i : Fin n, {y | i.val = k} ∩ {y | P y i} := by
      ext y
      simp only [Q, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [heq]
    apply MeasurableSet.iUnion
    intro i
    exact (MeasurableSet.const _).inter (hm i)
  let f₀ : Y → ℕ := fun y => Nat.find (hQ y)
  have hf₀ : Measurable f₀ := measurable_find hQ hmQ
  have hf₀B (y : Y) : f₀ y < n := by
    obtain ⟨i, hi, _⟩ := Nat.find_spec (hQ y)
    change Nat.find (hQ y) < n
    rw [← hi]
    exact i.isLt
  have hmF : Measurable (fun y => (⟨f₀ y, hf₀B y⟩ : Fin n)) := by
    apply measurable_to_countable'
    intro i
    convert hf₀ (measurableSet_singleton i.val) using 1
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
  refine ⟨fun y => ⟨f₀ y, hf₀B y⟩, hmF, ?_⟩
  intro y
  obtain ⟨i, hi, hp⟩ := Nat.find_spec (hQ y)
  have heq : i = ⟨f₀ y, hf₀B y⟩ := Fin.ext hi
  simpa only [heq] using hp

/-- A common finite net allows measurable nearest-bin selection for every
measurable map into the compact set. -/
lemma compact_quantization {s : Set A} (hs : IsCompact s) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (n : ℕ) (c : Fin n → A), (∀ i, c i ∈ s) ∧
      ∀ a : Y → A, Measurable a → (∀ y, a y ∈ s) →
        ∃ f : Y → Fin n, Measurable f ∧ ∀ y, dist (a y) (c (f y)) < ρ := by
  classical
  obtain ⟨u, hus, hu, hcover⟩ := hs.finite_cover_balls hρ
  let t := hu.toFinset
  let e : Fin t.card ≃ t := t.equivFin.symm
  let c : Fin t.card → A := fun i => (e i).val
  have hc (i : Fin t.card) : c i ∈ s := hus (by simpa only [t, hu.mem_toFinset] using (e i).property)
  refine ⟨t.card, c, hc, ?_⟩
  intro a ham has
  have he (y : Y) : ∃ i, dist (a y) (c i) < ρ := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (hcover (has y))
    obtain ⟨hvu, hv⟩ := Set.mem_iUnion.mp hv
    have hvt : v ∈ t := by simpa only [t, hu.mem_toFinset] using hvu
    refine ⟨e.symm ⟨v, hvt⟩, ?_⟩
    simpa only [c, Equiv.apply_symm_apply, Metric.mem_ball] using hv
  exact finite_measurable_choice (fun y i => dist (a y) (c i) < ρ)
    (fun _ => measurableSet_lt (ham.dist measurable_const) measurable_const) he
end EuclideanFiveColor.Quantize

namespace EuclideanFiveColor.CompactFunctions

section
open MeasureTheory
open scoped BigOperators
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma combination_dist {r : ℕ} (F : Fin r → ℂ) (a b : Fin r → ℂ) :
    dist (∑ i, a i * F i) (∑ i, b i * F i) ≤ dist a b * ∑ i, ‖F i‖ := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖a i * F i - b i * F i‖ := norm_sum_le _ _
    _ ≤ ∑ i, dist a b * ‖F i‖ := Finset.sum_le_sum fun i _ => by
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using dist_le_pi_dist a b i) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- Functional calculus for an individual compact function. Quantizing the
bounded coefficient arrays proves this directly, without a spectral theorem. -/
lemma compact_lipschitz {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} {H : X → ℂ}
    [MeasurableConstSMul K X] (hq : Measurable q) (hHm : Measurable H)
    (hH : Compact (K := K) μ q H) (f : ℂ → ℂ) (L : NNReal) (hLip : LipschitzWith L f) :
    Compact (K := K) μ q (fun x => f (H x)) := by
  intro ε hε
  let τ := ε/(4*((L : ℝ)+1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨r, B, C, F, hB, hC, hm, hb, ha⟩ := hH τ hτ
  let η := τ/(C+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηC : η*C ≤ τ := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < C+1)]
    nlinarith
  have hs : IsCompact {a : Fin r → ℂ | ‖a‖ ≤ B} := by
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : Fin r → ℂ) B
  obtain ⟨n, c, hc, hquant⟩ := Quantize.compact_quantization (Y := Y) hs hη
  let J : Fin n → X → ℂ := fun i x => f (∑ j, c i j * F j x)
  have hjm (i : Fin n) : Measurable (J i) := hLip.continuous.measurable.comp
    (Finset.measurable_sum _ (fun j _ => measurable_const.mul (hm j)))
  let R := ‖f 0‖ + (L : ℝ)*(B*C)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hJb (i : Fin n) (x : X) : ‖J i x‖ ≤ R := by
    have hnorm : ‖∑ j, c i j * F j x‖ ≤ B*C := module_bound _ _ hB (hc i) (hb x)
    have hl := hLip.dist_le_mul (∑ j, c i j * F j x) 0
    rw [dist_zero_right] at hl
    have ht : ‖J i x‖ ≤ dist (J i x) (f 0) + ‖f 0‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (J i x - f 0) (f 0)
    dsimp [J, R] at *
    nlinarith [mul_le_mul_of_nonneg_left hnorm L.coe_nonneg]
  refine ⟨n, 1, n*R, J, by norm_num, mul_nonneg (Nat.cast_nonneg _) hR, hjm, ?_, ?_⟩
  · intro x
    simpa using (Finset.sum_le_sum (s := Finset.univ) fun i _ => hJb i x)
  · intro k
    obtain ⟨a, ham, hab, hai, hae⟩ := ha k
    obtain ⟨b, hbm, hbd⟩ := hquant a ham hab
    let A : Y → Fin n → ℂ := fun y i => if b y = i then 1 else 0
    have hAm : Measurable A := Measurable.of_eval (fun i =>
      measurable_const.piecewise (hbm (measurableSet_singleton i)) measurable_const)
    have hAb (y : Y) : ‖A y‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i
      dsimp [A]
      split_ifs <;> norm_num
    let F₀ : X → ℂ := fun x => ∑ i, a (q x) i * F i x
    let F₁ : X → ℂ := fun x => ∑ i, c (b (q x)) i * F i x
    have hF₁ : Measurable F₁ := Finset.measurable_sum _ (fun i _ =>
      ((measurable_of_countable (fun j => c j i)).comp (hbm.comp hq)).mul (hm i))
    have hsel (x : X) : (∑ i, A (q x) i * J i x) = f (F₁ x) := by
      rw [Finset.sum_eq_single (b (q x))]
      · simp [A, J, F₁]
      · intro i _ hi
        simp [A, Ne.symm hi]
      · simp
    have hdist (x : X) : dist (F₀ x) (F₁ x) ≤ τ := by
      calc
        _ ≤ dist (a (q x)) (c (b (q x))) * ∑ i, ‖F i x‖ := combination_dist _ _ _
        _ ≤ η*C := mul_le_mul (hbd (q x)).le (hb x) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hη.le
        _ ≤ τ := hηC
    have hmajor (x : X) : dist (f (H (k • x))) (f (F₁ x))^2 ≤
        2*(L : ℝ)^2*(dist (H (k • x)) (F₀ x)^2 + τ^2) := by
      have ht := (dist_triangle (H (k • x)) (F₀ x) (F₁ x)).trans
        (add_le_add le_rfl (hdist x))
      have hl := (hLip.dist_le_mul (H (k • x)) (F₁ x)).trans
        (mul_le_mul_of_nonneg_left ht L.coe_nonneg)
      have hs₀ : dist (f (H (k • x))) (f (F₁ x))^2 ≤
          ((L : ℝ)*(dist (H (k • x)) (F₀ x)+τ))^2 :=
        pow_le_pow_left₀ dist_nonneg hl 2
      have hsq : (dist (H (k • x)) (F₀ x)+τ)^2 ≤ 2*(dist (H (k • x)) (F₀ x)^2+τ^2) := by
        nlinarith [sq_nonneg (dist (H (k • x)) (F₀ x)-τ)]
      have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (L : ℝ))
      nlinarith
    have hiM : Integrable (fun x => 2*(L : ℝ)^2*(dist (H (k • x)) (F₀ x)^2+τ^2)) μ :=
      (hai.add (integrable_const _)).const_mul _
    have hi : Integrable (fun x => dist (f (H (k • x))) (f (F₁ x))^2) μ :=
      hiM.mono' (((hLip.continuous.measurable.comp (hHm.comp (measurable_const_smul k))).dist
        (hLip.continuous.measurable.comp hF₁)).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor x)
    have hLτ : (L : ℝ)*τ < ε/4 := by
      dsimp [τ]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 4*((L : ℝ)+1))]
      nlinarith
    have he : (∫ x, dist (f (H (k • x))) (f (F₁ x))^2 ∂μ) < ε^2 := by
      calc
        _ ≤ ∫ x, 2*(L : ℝ)^2*(dist (H (k • x)) (F₀ x)^2+τ^2) ∂μ := integral_mono hi hiM hmajor
        _ = 2*(L : ℝ)^2*((∫ x, dist (H (k • x)) (F₀ x)^2 ∂μ)+τ^2) := by
          rw [integral_const_mul, integral_add hai (integrable_const _), integral_const,
            probReal_univ, smul_eq_mul, one_mul]
        _ ≤ 4*((L : ℝ)*τ)^2 := by
          have htt := mul_le_mul_of_nonneg_left hae.le (by positivity : 0 ≤ 2*(L : ℝ)^2)
          dsimp [F₀]
          nlinarith
        _ < ε^2 := by
          have hsq := (sq_lt_sq₀ (mul_nonneg L.coe_nonneg hτ.le) (by positivity : 0 ≤ ε/4)).mpr hLτ
          nlinarith [sq_pos_of_pos hε]
    refine ⟨A, hAm, hAb, ?_, ?_⟩
    · simpa only [hsel] using hi
    · simpa only [hsel] using he
end
section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma compact_of_bounded_pointwise_limit {μ : Measure X} [IsProbabilityMeasure μ]
    {q : X → Y} {H : X → ℂ} {Hn : ℕ → X → ℂ} [MeasurableConstSMul K X]
    (hq : Measurable q) (hHm : Measurable H) (hHnm : ∀ n, Measurable (Hn n))
    (hHnc : ∀ n, Compact (K := K) μ q (Hn n))
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (C : ℝ) (hC : 0 ≤ C) (hHb : ∀ x, ‖H x‖ ≤ C) (hHnb : ∀ n x, ‖Hn n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => Hn n x) atTop (𝓝 (H x))) :
    Compact (K := K) μ q H := by
  have hdist (n : ℕ) (x : X) : dist (H x) (Hn n x)^2 ≤ (2*C)^2 :=
    (sq_le_sq₀ dist_nonneg (mul_nonneg (by norm_num) hC)).mpr
      ((dist_le_norm_add_norm _ _).trans (by linarith [hHb x, hHnb n x]))
  have hi (n : ℕ) : Integrable (fun x => dist (H x) (Hn n x)^2) μ :=
    Integrable.of_bound ((hHm.dist (hHnm n)).pow_const 2).aestronglyMeasurable ((2*C)^2)
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hdist n x)
  have hl : Tendsto (fun n => ∫ x, dist (H x) (Hn n x)^2 ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (f := fun _ : X => (0 : ℝ)) (fun _ : X => (2*C)^2)
      (fun n => (hi n).aestronglyMeasurable) (integrable_const _) (fun n =>
        Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_sq] using hdist n x)
      (hlim.mono fun x hx => by
        have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => H x) atTop (𝓝 (H x))).dist hx).pow 2
        simpa only [dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht)
  apply compact_of_l2_approximation hq hHm hpres
  intro δ hδ
  obtain ⟨n, hn⟩ := (hl.eventually (gt_mem_nhds (sq_pos_of_pos hδ))).exists
  exact ⟨Hn n, hHnm n, hHnc n, hi n, hn⟩

lemma compact_closed_preimage {μ : Measure X} [IsProbabilityMeasure μ]
    {q : X → Y} {H : X → ℂ} [MeasurableConstSMul K X]
    (hq : Measurable q) (hH : Measurable H) (hC : Compact (K := K) μ q H)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (t : Set ℂ) (ht : IsClosed t) :
    Compact (K := K) μ q ((H ⁻¹' t).indicator (fun _ => (1 : ℂ))) := by
  let δ : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  let f : ℕ → ℂ → ℂ := fun n z => ((thickenedIndicator (hδ n) t z : ℝ) : ℂ)
  have hf (n : ℕ) : LipschitzWith ((δ n).toNNReal⁻¹) (f n) := by
    have h := Complex.isometry_ofReal.lipschitzWith.comp
      (NNReal.isometry_coe.lipschitzWith.comp (lipschitzWith_thickenedIndicator (hδ n) t))
    simpa only [one_mul, Function.comp_def] using h
  have hfb (n : ℕ) (z : ℂ) : ‖f n z‖ ≤ 1 := by
    dsimp [f]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast thickenedIndicator_le_one (hδ n) t z
  have hfl (z : ℂ) : Tendsto (fun n => f n z) atTop (𝓝 (t.indicator (fun _ => (1 : ℂ)) z)) := by
    have hh := (tendsto_pi_nhds.mp (thickenedIndicator_tendsto_indicator_closure hδ
      tendsto_one_div_add_atTop_nhds_zero_nat t)) z
    rw [ht.closure_eq] at hh
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (NNReal.continuous_coe.continuousAt.tendsto.comp hh)
    have he : (((t.indicator (fun _ => (1 : NNReal)) z : NNReal) : ℝ) : ℂ) =
        t.indicator (fun _ => (1 : ℂ)) z := by
      by_cases hz : z ∈ t <;> simp [hz]
    change Tendsto (fun n => f n z) atTop (𝓝 _) at h
    rwa [he] at h
  have hiM : Measurable ((H ⁻¹' t).indicator (fun _ => (1 : ℂ))) :=
    measurable_const.indicator (hH ht.measurableSet)
  apply compact_of_bounded_pointwise_limit hq hiM
    (fun n => (hf n).continuous.measurable.comp hH)
    (fun n => compact_lipschitz hq hH hC (f n) _ (hf n)) hpres 1 (by norm_num)
  · intro x
    by_cases hx : H x ∈ t <;> simp [Set.indicator, hx]
  · intro n x
    exact hfb n (H x)
  · exact Filter.Eventually.of_forall fun x => by
      have he : (H ⁻¹' t).indicator (fun _ => (1 : ℂ)) x =
          t.indicator (fun _ => (1 : ℂ)) (H x) := by
        by_cases hx : H x ∈ t <;> simp [hx]
      simpa only [Function.comp_apply, he] using hfl (H x)

lemma compact_neg {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} {H : X → ℂ}
    [MeasurableConstSMul K X]
    (hq : Measurable q) (hm : Measurable H) (hc : Compact (K := K) μ q H) :
    Compact (K := K) μ q (fun x => -H x) := by
  have h := compact_lipschitz hq hm hc (fun z : ℂ => -z) 1 isometry_neg.lipschitzWith
  exact h

omit [MeasurableSpace X] in
lemma indicator_one_bound (s : Set X) (x : X) : ‖s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  by_cases hx : x ∈ s <;> simp [hx]

lemma compact_compl {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} [MeasurableConstSMul K X]
    (hq : Measurable q) {s : Set X} (hm : MeasurableSet s)
    (hc : Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ)))) :
    Compact (K := K) μ q (sᶜ.indicator (fun _ => (1 : ℂ))) := by
  have hn := compact_neg hq (measurable_const.indicator hm) hc
  have ha := compact_add hq measurable_const (measurable_const.indicator hm).neg
    (compact_const (K := K) μ q 1) hn
  have he : (fun x => (1 : ℂ) + -(s.indicator (fun _ => 1) x)) = sᶜ.indicator (fun _ => 1) := by
    funext x; by_cases hx : x ∈ s <;> simp [hx]
  simpa only [Pi.neg_apply, he] using ha

lemma compact_union {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y} [MeasurableConstSMul K X]
    (hq : Measurable q) {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsc : Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ))))
    (htc : Compact (K := K) μ q (t.indicator (fun _ => (1 : ℂ)))) :
    Compact (K := K) μ q ((s ∪ t).indicator (fun _ => (1 : ℂ))) := by
  have hsm : Measurable (s.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator hs
  have htm : Measurable (t.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator ht
  have ha := compact_add hq hsm htm hsc htc
  have hp := compact_mul hq hsm htm 1 (by norm_num) (indicator_one_bound t) hsc htc
  have hn := compact_neg hq (hsm.mul htm) hp
  have hh := compact_add hq (hsm.add htm) (hsm.mul htm).neg ha hn
  have he : (fun x => s.indicator (fun _ => (1 : ℂ)) x + t.indicator (fun _ => 1) x +
      -(s.indicator (fun _ => 1) x * t.indicator (fun _ => 1) x)) =
      (s ∪ t).indicator (fun _ => 1) := by
    funext x; by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt]
  simpa only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply, he] using hh

lemma compact_iUnion {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (s : ℕ → Set X) (hm : ∀ n, MeasurableSet (s n))
    (hc : ∀ n, Compact (K := K) μ q ((s n).indicator (fun _ => (1 : ℂ)))) :
    Compact (K := K) μ q ((⋃ n, s n).indicator (fun _ => (1 : ℂ))) := by
  let D : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, s i
  have hDm (n : ℕ) : MeasurableSet (D n) := MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hm i))
  have hDc (n : ℕ) : Compact (K := K) μ q ((D n).indicator (fun _ => (1 : ℂ))) := by
    induction n with
    | zero => simpa [D] using compact_const (K := K) μ q 0
    | succ n ih =>
      have he : D (n+1) = s n ∪ D n := by simp only [D, Finset.range_add_one, Finset.set_biUnion_insert]
      rw [he]
      exact compact_union hq (hm n) (hDm n) (hc n) ih
  apply compact_of_bounded_pointwise_limit hq (measurable_const.indicator (MeasurableSet.iUnion hm))
    (fun n => measurable_const.indicator (hDm n)) hDc hpres 1 (by norm_num)
    (indicator_one_bound _) (fun n => indicator_one_bound (D n))
  exact Filter.Eventually.of_forall fun x => by
    apply tendsto_const_nhds.congr'
    by_cases hx : x ∈ ⋃ n, s n
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      filter_upwards [eventually_ge_atTop (i+1)] with n hn
      have hix : x ∈ D n := Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨by simpa using hn, hi⟩⟩
      simp [hx, hix]
    · have hnx (n : ℕ) : x ∉ D n := by
        intro hh
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
        obtain ⟨_, hi⟩ := Set.mem_iUnion.mp hi
        exact hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
      exact Filter.Eventually.of_forall fun n => by simp [hx, hnx n]

@[instance_reducible] def compactSigma (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y)
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ) : MeasurableSpace X where
  MeasurableSet' s := MeasurableSet s ∧ Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ)))
  measurableSet_empty := ⟨MeasurableSet.empty, by simpa using compact_const (K := K) μ q 0⟩
  measurableSet_compl s hs := ⟨hs.1.compl, compact_compl hq hs.1 hs.2⟩
  measurableSet_iUnion s hs := ⟨MeasurableSet.iUnion (fun n => (hs n).1),
    compact_iUnion hq hpres s (fun n => (hs n).1) (fun n => (hs n).2)⟩

lemma compactSigma_le (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y)
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ) :
    compactSigma μ q hq hpres ≤ ‹MeasurableSpace X› := fun _ hs => hs.1

lemma measurable_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    {H : X → ℂ} (hm : Measurable H) (hc : Compact (K := K) μ q H) :
    @Measurable X ℂ (compactSigma μ q hq hpres) inferInstance H := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap H (borel ℂ) ≤ compactSigma μ q hq hpres
  rw [borel_eq_generateFrom_isClosed, MeasurableSpace.comap_generateFrom]
  apply MeasurableSpace.generateFrom_le
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨hm ht.measurableSet, compact_closed_preimage hq hm hc hpres t ht⟩

end
section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma compact_simple {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (f : @SimpleFunc X (compactSigma μ q hq hpres) ℂ) :
    Compact (K := K) μ q f := by
  apply @SimpleFunc.induction X ℂ (compactSigma μ q hq hpres) _
    (fun f => Compact (K := K) μ q f) ?_ ?_ f
  · intro c s hs
    have hsm : MeasurableSet s := hs.1
    have hsc : Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ))) := hs.2
    have hh := compact_mul hq measurable_const (measurable_const.indicator hsm)
      1 (by norm_num) (indicator_one_bound s) (compact_const (K := K) μ q c) hsc
    convert hh using 1
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  · intro f g _ hf hg
    exact compact_add hq ((@SimpleFunc.measurable X ℂ (compactSigma μ q hq hpres) _ f).mono (compactSigma_le μ q hq hpres) le_rfl)
      ((@SimpleFunc.measurable X ℂ (compactSigma μ q hq hpres) _ g).mono (compactSigma_le μ q hq hpres) le_rfl) hf hg

lemma compact_of_measurable_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    {H : X → ℂ} (hm : @Measurable X ℂ (compactSigma μ q hq hpres) inferInstance H)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖H x‖ ≤ C) :
    Compact (K := K) μ q H := by
  let F : ℕ → @SimpleFunc X (compactSigma μ q hq hpres) ℂ :=
    @SimpleFunc.approxOn ℂ X _ _ _ (compactSigma μ q hq hpres) H hm Set.univ 0 (Set.mem_univ 0) inferInstance
  have hHm : Measurable H := hm.mono (compactSigma_le μ q hq hpres) le_rfl
  have hFm (n : ℕ) : Measurable (F n) :=
    (@SimpleFunc.measurable X ℂ (compactSigma μ q hq hpres) _ (F n)).mono (compactSigma_le μ q hq hpres) le_rfl
  apply compact_of_bounded_pointwise_limit hq hHm hFm
    (fun n => compact_simple hq hpres (F n)) hpres (2*C) (by positivity)
  · intro x; have := hb x; linarith
  · intro n x
    exact (@SimpleFunc.norm_approxOn_zero_le X ℂ (compactSigma μ q hq hpres) _ _ _ H hm Set.univ (Set.mem_univ 0) inferInstance x n).trans (by linarith [hb x])
  · exact Filter.Eventually.of_forall fun x => @SimpleFunc.tendsto_approxOn ℂ X _ _ _ (compactSigma μ q hq hpres) H hm Set.univ 0
      (Set.mem_univ 0) inferInstance x (by simp)

lemma compact_base {μ : Measure X} {q : X → Y} [SMul K Y] [MeasurableConstSMul K Y]
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (b : Y → ℂ) (hbm : Measurable b) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, ‖b y‖ ≤ B) :
    Compact (K := K) μ q (b ∘ q) := by
  intro ε hε
  apply at_of_finite (I := Unit) B 1 (fun _ _ => 1) hB (by norm_num) (fun _ => measurable_const)
  · intro x; simp
  · intro k
    refine ⟨fun y _ => b (k • y), Measurable.of_eval (fun _ => hbm.comp (measurable_const_smul k)), ?_, ?_, ?_⟩
    · intro y; simpa using hb (k • y)
    · apply (integrable_zero X ℝ μ).congr
      filter_upwards [hqcov k] with x hx
      simp [Function.comp_apply, hx]
    · have he : (fun x => dist ((b ∘ q) (k • x)) (∑ _ : Unit, b (k • q x) * 1)^2) =ᵐ[μ]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [hqcov k] with x hx
        simp [Function.comp_apply, hx]
      rw [integral_congr_ae he, integral_zero]
      exact sq_pos_of_pos hε

end
section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [Monoid K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]

omit [MulAction K Y] in
lemma compact_shift {μ : Measure X} {q : X → Y} {H : X → ℂ}
    (hc : Compact (K := K) μ q H) (g : K) :
    Compact (K := K) μ q (fun x => H (g • x)) := by
  intro ε hε
  obtain ⟨r, B, C, Hf, hB, hC, hm, hb, ha⟩ := hc ε hε
  refine ⟨r, B, C, Hf, hB, hC, hm, hb, ?_⟩
  intro k
  simpa only [smul_smul] using ha (g*k)

omit [MulAction K Y] in
lemma measurable_shift_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ) (g : K) :
    @Measurable X X (compactSigma μ q hq hpres) (compactSigma μ q hq hpres) (fun x => g • x) := by
  intro s hs
  refine ⟨(measurable_const_smul g) hs.1, ?_⟩
  have hh := compact_shift hs.2 g
  have he : (fun x => (s.indicator (fun _ => (1 : ℂ))) (g • x)) =
      ((fun x : X => g • x) ⁻¹' s).indicator (fun _ => 1) := by
    funext x; by_cases hx : g • x ∈ s <;> simp [hx]
  rwa [he] at hh

lemma measurable_base_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] [MeasurableConstSMul K Y] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) :
    @Measurable X Y (compactSigma μ q hq hpres) inferInstance q := by
  intro s hs
  refine ⟨hq hs, ?_⟩
  have hh := compact_base hqcov (s.indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator hs) 1 (by norm_num) (indicator_one_bound s)
  have he : (s.indicator (fun _ => (1 : ℂ))) ∘ q =
      (q ⁻¹' s).indicator (fun _ => 1) := by
    funext x; by_cases hx : q x ∈ s <;> simp [Function.comp_apply, hx]
  rwa [he] at hh

end

/-! Bounded integral kernels yield finite-module orbit approximation.
This implements the compact-tower construction without spectral projections:
approximate the invariant kernel by finite rectangles first. -/
open MeasureTheory ProbabilityTheory ConditionalFiber
open scoped BigOperators
variable {K X Z Y : Type*} [SMul K X] [SMul K Z]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Z]

/-- Conditional integration projects an ambient finite module to the actual
new factor, without sacrificing its uniform coefficient or basis bounds. -/
lemma compact_descend (μ : Measure X) [IsProbabilityMeasure μ]
    (π : X → Z) (hπ : Measurable π) (p : Z → Y) (hp : Measurable p)
    (hπcov : ∀ k : K, ∀ᵐ x ∂μ, π (k • x) = k • π x)
    (H : Z → ℂ) (hH : Measurable H) (D : ℝ) (_hD : 0 ≤ D)
    (hHD : ∀ z, ‖H z‖ ≤ D)
    (hc : Compact (K := K) μ (p ∘ π) (H ∘ π)) :
    Compact (K := K) (μ.map π) p H := by
  let κ := condDistrib id π μ
  let ν := μ.map π
  let : IsProbabilityMeasure ν := inferInstance
  intro ε hε
  obtain ⟨r, B, C, F, hB, hC, hFm, hFb, ha⟩ := hc ε hε
  have hFC (i : Fin r) (x : X) : ‖F i x‖ ≤ C :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (F j x)) (Finset.mem_univ i)).trans (hFb x)
  have hFi (z : Z) (i : Fin r) : Integrable (F i) (κ z) :=
    Integrable.of_bound (hFm i).aestronglyMeasurable C (Filter.Eventually.of_forall (hFC i))
  let G : Fin r → Z → ℂ := fun i z => ∫ x, F i x ∂κ z
  have hGm (i : Fin r) : Measurable (G i) :=
    (hFm i).stronglyMeasurable.integral_kernel.measurable
  have hGb (z : Z) : ∑ i, ‖G i z‖ ≤ C := by
    calc
      ∑ i, ‖G i z‖ ≤ ∑ i, ∫ x, ‖F i x‖ ∂κ z :=
        Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
      _ = ∫ x, ∑ i, ‖F i x‖ ∂κ z :=
        (integral_finsetSum _ (fun i _ => (hFi z i).norm)).symm
      _ ≤ ∫ _x, C ∂κ z := integral_mono
        (integrable_finsetSum _ (fun i _ => (hFi z i).norm)) (integrable_const C) hFb
      _ = C := by simp
  refine ⟨r, B, C, G, hB, hC, hGm, hGb, ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha k
  let E : X → ℂ := fun x => H (π (k • x)) - ∑ i, a (p (π x)) i * F i x
  have hEm : Measurable E := ((hH.comp hπ).comp (measurable_const_smul k)).sub
    (Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp (hp.comp hπ)).mul (hFm i)))
  have hEB (x : X) : ‖E x‖ ≤ D+B*C :=
    (norm_sub_le _ _).trans (add_le_add (hHD _) (module_bound _ _ hB (hab _) (hFb x)))
  have hEi (z : Z) : Integrable E (κ z) :=
    Integrable.of_bound hEm.aestronglyMeasurable (D+B*C) (Filter.Eventually.of_forall hEB)
  have hE₂i (z : Z) : Integrable (fun x => ‖E x‖^2) (κ z) :=
    Integrable.of_bound (hEm.norm.pow_const 2).aestronglyMeasurable ((D+B*C)^2)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_sq] using
          pow_le_pow_left₀ (norm_nonneg _) (hEB x) 2)
  have hE₂μ : Integrable (fun x => ‖E x‖^2) μ := by
    simpa only [E, Function.comp_apply, dist_eq_norm] using hai
  have hEeq : ∀ᵐ z ∂ν, (∫ x, E x ∂κ z) = H (k • z) - ∑ i, a (p z) i * G i z := by
    filter_upwards [ae_in_own_fiber μ π hπ, ae_fiber_of_ae μ π hπ (hπcov k)] with z hz hc'
    have he : E =ᵐ[κ z] (fun x => H (k • z) - ∑ i, a (p z) i * F i x) := by
      filter_upwards [hz, hc'] with x hx hx'
      dsimp only [E]
      rw [hx', hx]
    rw [integral_congr_ae he, integral_sub (integrable_const _) (integrable_finsetSum _
      fun i _ => (hFi z i).const_mul _), integral_finsetSum _
      (fun i _ => (hFi z i).const_mul _)]
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul, G]
  have hdistm : Measurable (fun z => dist (H (k • z)) (∑ i, a (p z) i * G i z)^2) :=
    ((hH.comp (measurable_const_smul k)).dist
      (Finset.measurable_sum _ (fun i _ => (((measurable_pi_iff.mp ham) i).comp hp).mul (hGm i)))).pow_const 2
  have hdistB (z : Z) : dist (H (k • z)) (∑ i, a (p z) i * G i z)^2 ≤ (D+B*C)^2 := by
    apply pow_le_pow_left₀ dist_nonneg
    exact (dist_le_norm_add_norm _ _).trans
      (add_le_add (hHD _) (module_bound _ _ hB (hab _) (hGb z)))
  have hdisti : Integrable (fun z => dist (H (k • z)) (∑ i, a (p z) i * G i z)^2) ν :=
    Integrable.of_bound hdistm.aestronglyMeasurable ((D+B*C)^2)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_sq] using hdistB z)
  refine ⟨a, ham, hab, hdisti, ?_⟩
  have hle : (∫ z, dist (H (k • z)) (∑ i, a (p z) i * G i z)^2 ∂ν) ≤
      ∫ z, (∫ x, ‖E x‖^2 ∂κ z) ∂ν := by
    apply integral_mono_ae hdisti (integrable_fiber_integral μ π hπ _ hE₂μ)
    filter_upwards [hEeq] with z hz
    rw [dist_eq_norm, ← hz]
    exact KernelCompact.norm_integral_sq (κ z) E (hEi z) (hE₂i z)
  rw [integral_fiber μ π hπ _ hE₂μ] at hle
  apply hle.trans_lt
  simpa only [E, Function.comp_apply, dist_eq_norm] using hae

end EuclideanFiveColor.CompactFunctions

end

end OAI
