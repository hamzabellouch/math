import OAI.Analysis.PlaneSpectrum.PhaseCollision

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
namespace EuclideanFiveColor.GoodFiber

variable {W ι T : Type*} [MeasurableSpace W] [Fintype ι] [Nonempty ι] [Fintype T]

omit [Fintype ι] [Nonempty ι] [Fintype T] in
theorem exists_lt_on_conull (μ : Measure W) [IsProbabilityMeasure μ]
    (g : W → ℝ) (hg : Integrable g μ) (havg : ∫ w, g w ∂μ < 1)
    (P : W → Prop) (hP : ∀ᵐ w ∂μ, P w) : ∃ w, P w ∧ g w < 1 := by
  by_contra h
  push Not at h
  have hle : ∀ᵐ w ∂μ, (1 : ℝ) ≤ g w := hP.mono fun w hw => h w hw
  have hi := integral_mono_ae (integrable_const 1) hg hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  exact (not_lt_of_ge hi) havg

omit [MeasurableSpace W] [Fintype T] in
lemma fraction_lower_bound (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (τ : ℝ) (hτ : 0 < τ) :
    (1 - (∑ i, e i)/((Fintype.card ι : ℝ)*τ)) ≤
      ((Finset.univ.filter (fun i => e i < τ)).card : ℝ) / Fintype.card ι := by
  classical
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint (i) : 1-e i/τ ≤ if e i < τ then (1 : ℝ) else 0 := by
    split_ifs with h
    · have := div_nonneg (he i) hτ.le; linarith
    · have : 1 ≤ e i/τ := (le_div_iff₀ hτ).mpr (by simpa using le_of_not_gt h)
      linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Finset.sum_div] at hs
  simp only [Finset.cast_card, Finset.sum_filter]
  apply (le_div_iff₀ hn).mpr
  have heq : (1 - (∑ i, e i)/((Fintype.card ι : ℝ)*τ)) * Fintype.card ι =
      Fintype.card ι - (∑ i, e i)/τ := by field_simp
  rw [heq]
  exact hs

/-- A single explicit budget gives all small-moment tests and over 90% good
approximation indices on the same fiber, together with any conull identities. -/
theorem simultaneous_good_fiber (μ : Measure W) [IsProbabilityMeasure μ]
    (f : T → W → ℝ) (e : ι → W → ℝ) (c τ : ℝ) (hc : 0 < c) (hτ : 0 < τ)
    (hf : ∀ t, Integrable (f t) μ) (he : ∀ i, Integrable (e i) μ)
    (hf0 : ∀ᵐ w ∂μ, ∀ t, 0 ≤ f t w) (he0 : ∀ᵐ w ∂μ, ∀ i, 0 ≤ e i w)
    (hbudget : (∑ t, ∫ w, f t w ∂μ)/c +
      10*(∑ i, ∫ w, e i w ∂μ)/((Fintype.card ι : ℝ)*τ) < 1)
    (P : W → Prop) (hP : ∀ᵐ w ∂μ, P w) :
    ∃ w, P w ∧ (∀ t, f t w < c) ∧
      (9/10 : ℝ)*(Fintype.card ι) <
        (Finset.univ.filter (fun i => e i w < τ)).card := by
  classical
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  let g : W → ℝ := fun w => (∑ t, f t w)/c + 10*(∑ i, e i w)/(n*τ)
  have hig : Integrable g μ := ((integrable_finsetSum _ (fun t _ => hf t)).div_const c).add
    (((integrable_finsetSum _ (fun i _ => he i)).const_mul 10).div_const _)
  have hi : ∫ w, g w ∂μ < 1 := by
    dsimp [g]
    rw [integral_add ((integrable_finsetSum _ (fun t _ => hf t)).div_const c)
      (((integrable_finsetSum _ (fun i _ => he i)).const_mul 10).div_const _),
      integral_div, integral_div, integral_const_mul,
      integral_finsetSum _ (fun t _ => hf t), integral_finsetSum _ (fun i _ => he i)]
    exact hbudget
  obtain ⟨w, ⟨hwP, hwf, hwe⟩, hw⟩ := exists_lt_on_conull μ g hig hi
    (fun w => P w ∧ (∀ t, 0 ≤ f t w) ∧ ∀ i, 0 ≤ e i w) (hP.and (hf0.and he0))
  have hfs : 0 ≤ ∑ t, f t w := Finset.sum_nonneg (fun t _ => hwf t)
  have hes : 0 ≤ ∑ i, e i w := Finset.sum_nonneg (fun i _ => hwe i)
  refine ⟨w, hwP, ?_, ?_⟩
  · intro t
    have ht : f t w ≤ ∑ t, f t w :=
      Finset.single_le_sum (fun t _ => hwf t) (Finset.mem_univ t)
    have hb : f t w/c ≤ g w := by
      dsimp [g]
      have := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hes) (mul_pos hn hτ).le
      have := (div_le_div_iff_of_pos_right hc).mpr ht
      linarith
    exact (div_lt_one hc).mp (hb.trans_lt hw)
  · have hew : (∑ i, e i w)/(n*τ) < 1/10 := by
      dsimp [g] at hw
      have : 0 ≤ (∑ t, f t w)/c := div_nonneg hfs hc.le
      rw [mul_div_assoc] at hw
      linarith
    have hlo := fraction_lower_bound (fun i => e i w) hwe τ hτ
    have hfrac : (9/10 : ℝ) <
        ((Finset.univ.filter (fun i => e i w < τ)).card : ℝ)/n := by
      change 1 - (∑ i, e i w)/(n*τ) ≤ _ at hlo
      linarith
    exact (lt_div_iff₀ hn).mp hfrac

omit [MeasurableSpace W] [Fintype T] [Nonempty ι] in
/-- Pigeonholing happens only after the common good fiber is fixed. -/
theorem large_common_bin {L B : ℕ} (s : Finset ι) (b : ι → Fin L)
    (hs : (9/10 : ℝ)*Fintype.card ι < s.card)
    (hLB : (L : ℝ)*B < (9/10 : ℝ)*Fintype.card ι) :
    ∃ J : Finset ι, J ⊆ s ∧ B < J.card ∧ ∀ i ∈ J, ∀ j ∈ J, b i = b j := by
  classical
  have hcard : L*B < s.card := by exact_mod_cast hLB.trans hs
  obtain ⟨k, _, hk⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := s) (t := Finset.univ) (f := b) (fun _ _ => Finset.mem_univ _)
    (by simpa using hcard)
  refine ⟨s.filter (fun i => b i = k), Finset.filter_subset _ _, hk, ?_⟩
  intro i hi j hj
  exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm

end EuclideanFiveColor.GoodFiber

open MeasureTheory
namespace EuclideanFiveColor.Approximation
variable {A X : Type*} [PseudoMetricSpace A] [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma dist_sq_four_points (a b c d : A) :
    dist a d ^ 2 ≤ 3*(dist a b ^ 2 + dist b c ^ 2 + dist d c ^ 2) := by
  have ht : dist a d ≤ dist a b + dist b c + dist d c := by
    have := dist_triangle a b d
    have := dist_triangle b c d
    rw [dist_comm c d] at this
    linarith
  have ha := dist_nonneg (x := a) (y := b)
  have hb := dist_nonneg (x := b) (y := c)
  have hc := dist_nonneg (x := d) (y := c)
  have hd := dist_nonneg (x := a) (y := d)
  nlinarith [sq_nonneg (dist a b - dist b c), sq_nonneg (dist a b - dist d c),
    sq_nonneg (dist b c - dist d c)]

variable [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
/-- Closeness of approximants costs τ, and each of the two approximation
errors costs less than τ in conditional L². -/
theorem integrated_distance_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (H A' H₀ A₀ : X → A) (τ : ℝ)
    (hHm : Measurable H) (hH₀m : Measurable H₀)
    (hj : Integrable (fun x => dist (H x) (A' x)^2) μ)
    (h₀ : Integrable (fun x => dist (H₀ x) (A₀ x)^2) μ)
    (hAj : ∫ x, dist (H x) (A' x)^2 ∂μ < τ^2)
    (hA₀ : ∫ x, dist (H₀ x) (A₀ x)^2 ∂μ < τ^2)
    (hbin : ∀ᵐ x ∂μ, dist (A' x) (A₀ x) ≤ τ) :
    Integrable (fun x => dist (H x) (H₀ x)^2) μ ∧
      (∫ x, dist (H x) (H₀ x)^2 ∂μ) < 9*τ^2 := by
  have hdom : Integrable (fun x => 3*(dist (H x) (A' x)^2 + τ^2 +
      dist (H₀ x) (A₀ x)^2)) μ := ((hj.add (integrable_const _)).add h₀).const_mul 3
  have hle : ∀ᵐ x ∂μ, dist (H x) (H₀ x)^2 ≤
      3*(dist (H x) (A' x)^2 + τ^2 + dist (H₀ x) (A₀ x)^2) := by
    filter_upwards [hbin] with x hx
    have hs : dist (A' x) (A₀ x)^2 ≤ τ^2 :=
      pow_le_pow_left₀ dist_nonneg hx 2
    exact (dist_sq_four_points _ _ _ _).trans (by linarith)
  have hi : Integrable (fun x => dist (H x) (H₀ x)^2) μ := by
    apply hdom.mono' ((hHm.dist hH₀m).pow_const 2).aestronglyMeasurable
    exact hle.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_sq] using hx
  refine ⟨hi, ?_⟩
  have he := integral_mono_ae hi hdom hle
  have hc : Integrable (fun _ : X => τ^2) μ := integrable_const _
  have hjc : Integrable (fun x => dist (H x) (A' x)^2 + τ^2) μ := hj.add hc
  rw [integral_const_mul, integral_add hjc h₀,
    integral_add hj hc, integral_const, probReal_univ, smul_eq_mul, one_mul] at he
  linarith

end EuclideanFiveColor.Approximation

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.ConditionalFiber
variable {X W G V : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma comp_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) :
    (condDistrib id p μ) ∘ₘ μ.map p = μ := by
  simpa using condDistrib_comp_map hp.aemeasurable (measurable_id.aemeasurable (μ := μ))

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_fiber_of_ae (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, P x := by
  exact Measure.ae_ae_of_ae_comp (by rwa [comp_identity_fiber μ p hp])

lemma map_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : AEMeasurable p μ) (b : X → G) (hb : Measurable b) :
    ∀ᵐ w ∂μ.map p, (condDistrib id p μ w).map b = condDistrib b p μ w := by
  filter_upwards [condDistrib_comp hp
    (measurable_id.aemeasurable (μ := μ)) hb] with w hw
  simpa [Kernel.map_apply _ hb] using hw.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_in_own_fiber [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsFiniteMeasure μ] (p : X → W) (hp : Measurable p) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, p x = w := by
  filter_upwards [map_identity_fiber μ p hp.aemeasurable p hp,
    condDistrib_self hp.aemeasurable] with w hw hs
  have he : (condDistrib id p μ w).map p = Measure.dirac w := by
    rw [hw, hs]; rfl
  apply ae_of_ae_map (p := fun z : W => z = w) hp.aemeasurable
  rw [he]
  simp

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integral_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    ∫ w, (∫ x, f x ∂condDistrib id p μ w) ∂μ.map p = ∫ x, f x ∂μ := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  have he := Kernel.integral_comp hi
  simpa [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply,
    comp_identity_fiber μ p hp] using he.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] [NormedSpace ℝ V] in
lemma integrable_ae_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    ∀ᵐ w ∂μ.map p, Integrable f (condDistrib id p μ w) := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  exact ((Measure.integrable_comp_iff hi.aestronglyMeasurable).mp hi).1

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integrable_fiber_integral (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    Integrable (fun w => ∫ x, f x ∂condDistrib id p μ w) (μ.map p) := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  exact hi.integral_comp

end EuclideanFiveColor.ConditionalFiber

namespace EuclideanFiveColor.FiniteModule
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open ConditionalFiber
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
variable {X W ι T : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [Fintype ι] [Nonempty ι] [Fintype T]

/-- The actual common-fiber contradiction. The budget is global; all phase
upper bounds are required simultaneously on that fiber before a bin is chosen.
The phase lists are not assumed measurable. -/
theorem common_fiber_contradiction (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → W) (hp : Measurable p) (m : ℕ) (hm : 0 < m)
    (ρ τ c : ℝ) (hρ : 0 < ρ) (hτ : 0 < τ) (hc : 0 < c)
    (hτδ : 18*τ^2 < (ρ^m/m)^2/20)
    (Hp Hm Ap Am : ι → X → Fin m → ℂ)
    (hHp : ∀ j, Measurable (Hp j)) (hHm : ∀ j, Measurable (Hm j))
    (hIp : ∀ j, Integrable (fun x => dist (Hp j x) (Ap j x)^2) μ)
    (hIm : ∀ j, Integrable (fun x => dist (Hm j x) (Am j x)^2) μ)
    (zp zm : X → ι → Fin m → Circle) (ap am : ι → X → Circle)
    (hap : ∀ j, Measurable (ap j)) (ham : ∀ j, Measurable (am j))
    (henc : ∀ᵐ x ∂μ, ∀ j, PhaseEncoding.encoding (zp x j) = Hp j x ∧
      PhaseEncoding.encoding (zm x j) = Hm j x)
    (hmem : ∀ᵐ x ∂μ, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r))
    (f : T → W → ℝ) (hf : ∀ t, Integrable (f t) (μ.map p))
    (hf0 : ∀ᵐ w ∂μ.map p, ∀ t, 0 ≤ f t w)
    (hbudget : (∑ t, ∫ w, f t w ∂μ.map p)/c +
      10*(∑ j, ((∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
        (∫ x, dist (Hm j x) (Am j x)^2 ∂μ)))/((Fintype.card ι : ℝ)*τ^2) < 1)
    (L : ℕ) (bin : W → ι → Fin L)
    (hlarge : (L : ℝ)*(10*m^2 : ℕ) < (9/10 : ℝ)*Fintype.card ι)
    (hbin : ∀ᵐ w ∂μ.map p, ∀ i j, bin w i = bin w j →
      ∀ᵐ x ∂condDistrib id p μ w, dist (Ap i x) (Ap j x) ≤ τ ∧
        dist (Am i x) (Am j x) ≤ τ)
    (hupper : ∀ᵐ w ∂μ.map p, (∀ t, f t w < c) → ∀ i j, i ≠ j →
      (condDistrib id p μ w).real {x |
        dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ}
        < 1/(4*(m : ℝ)^2)) : False := by
  classical
  let e : ι → W → ℝ := fun j w =>
    (∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w) +
    (∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w)
  have he (j : ι) : Integrable (e j) (μ.map p) :=
    (integrable_fiber_integral μ p hp _ (hIp j)).add
      (integrable_fiber_integral μ p hp _ (hIm j))
  have hinte (j : ι) : (∫ w, e j w ∂μ.map p) =
      (∫ x, dist (Hp j x) (Ap j x)^2 ∂μ) +
      (∫ x, dist (Hm j x) (Am j x)^2 ∂μ) := by
    rw [show e j = fun w =>
      (∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w) +
      (∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w) from rfl,
      integral_add (integrable_fiber_integral μ p hp _ (hIp j))
        (integrable_fiber_integral μ p hp _ (hIm j)),
      integral_fiber μ p hp _ (hIp j), integral_fiber μ p hp _ (hIm j)]
  have he0 (w) (j) : 0 ≤ e j w :=
    add_nonneg (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  have hbudget' : (∑ t, ∫ w, f t w ∂μ.map p)/c +
      10*(∑ j, ∫ w, e j w ∂μ.map p)/((Fintype.card ι : ℝ)*τ^2) < 1 := by
    simpa only [hinte] using hbudget
  have hcondp : ∀ᵐ w ∂μ.map p, ∀ j, Integrable
      (fun x => dist (Hp j x) (Ap j x)^2) (condDistrib id p μ w) :=
    ae_all_iff.mpr fun j => integrable_ae_fiber μ p hp _ (hIp j)
  have hcondm : ∀ᵐ w ∂μ.map p, ∀ j, Integrable
      (fun x => dist (Hm j x) (Am j x)^2) (condDistrib id p μ w) :=
    ae_all_iff.mpr fun j => integrable_ae_fiber μ p hp _ (hIm j)
  let P : W → Prop := fun w =>
    (∀ᵐ x ∂condDistrib id p μ w, ∀ j, PhaseEncoding.encoding (zp x j) = Hp j x ∧
      PhaseEncoding.encoding (zm x j) = Hm j x) ∧
    (∀ᵐ x ∂condDistrib id p μ w, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r)) ∧
    (∀ j, Integrable (fun x => dist (Hp j x) (Ap j x)^2) (condDistrib id p μ w)) ∧
    (∀ j, Integrable (fun x => dist (Hm j x) (Am j x)^2) (condDistrib id p μ w)) ∧
    (∀ i j, bin w i = bin w j → ∀ᵐ x ∂condDistrib id p μ w,
      dist (Ap i x) (Ap j x) ≤ τ ∧ dist (Am i x) (Am j x) ≤ τ) ∧
    ((∀ t, f t w < c) → ∀ i j, i ≠ j →
      (condDistrib id p μ w).real {x |
        dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ}
        < 1/(4*(m : ℝ)^2))
  have hP : ∀ᵐ w ∂μ.map p, P w := by
    filter_upwards [ae_fiber_of_ae μ p hp henc, ae_fiber_of_ae μ p hp hmem,
      hcondp, hcondm, hbin, hupper] with w h₁ h₂ h₃ h₄ h₅ h₆
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  obtain ⟨w, ⟨hwenc, hwmem, hwIp, hwIm, hwbin, hwup⟩, hwf, hmany⟩ :=
    GoodFiber.simultaneous_good_fiber (μ.map p) f e c (τ^2) hc (sq_pos_of_pos hτ)
      hf he hf0 (Filter.Eventually.of_forall he0) hbudget' P hP
  let s := Finset.univ.filter (fun j => e j w < τ^2)
  obtain ⟨J, hJs, hJ, hJbin⟩ := GoodFiber.large_common_bin s (bin w) hmany hlarge
  have hJpos : 0 < J.card := lt_of_le_of_lt (Nat.zero_le _) hJ
  let : Nonempty J := Set.Nonempty.to_subtype (Finset.card_pos.mp hJpos)
  obtain ⟨j₀⟩ := (inferInstance : Nonempty J)
  have herr (j : J) :
      (∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w) < τ^2 ∧
      (∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w) < τ^2 := by
    have hj : e j w < τ^2 := (Finset.mem_filter.mp (hJs j.property)).2
    have hn1 : 0 ≤ ∫ x, dist (Hp j x) (Ap j x)^2 ∂condDistrib id p μ w :=
      integral_nonneg fun _ => sq_nonneg _
    have hn2 : 0 ≤ ∫ x, dist (Hm j x) (Am j x)^2 ∂condDistrib id p μ w :=
      integral_nonneg fun _ => sq_nonneg _
    dsimp [e] at hj
    constructor <;> linarith
  have hd (j : J) := hwbin j j₀ (hJbin j j.property j₀ j₀.property)
  have hdp (j : J) := Approximation.integrated_distance_bound
    (condDistrib id p μ w) (Hp j) (Ap j) (Hp j₀) (Ap j₀) τ
    (hHp j) (hHp j₀) (hwIp j) (hwIp j₀) (herr j).1 (herr j₀).1
    ((hd j).mono fun x hx => hx.1)
  have hdm (j : J) := Approximation.integrated_distance_bound
    (condDistrib id p μ w) (Hm j) (Am j) (Hm j₀) (Am j₀) τ
    (hHm j) (hHm j₀) (hwIm j) (hwIm j₀) (herr j).2 (herr j₀).2
    ((hd j).mono fun x hx => hx.2)
  obtain ⟨i, j, hij, hlo⟩ := EncodedCollision.collision_from_measurable_encodings
    (condDistrib id p μ w) m hm ρ hρ
    (fun x (j : J) => zp x j) (fun x (j : J) => zm x j)
    (fun j : J => ap j) (fun j : J => am j) j₀ (fun j : J => Hp j) (fun j : J => Hm j)
    (hwenc.mono fun x hx j => hx j) (fun j => hap j) (fun j => ham j)
    (fun j => (hHp j).dist (hHp j₀)) (fun j => (hHm j).dist (hHm j₀))
    (hwmem.mono fun x hx j => hx j)
    (fun j => (hdp j).1.add (hdm j).1)
    (fun j => by
      rw [integral_add (hdp j).1 (hdm j).1]
      exact (add_lt_add (hdp j).2 (hdm j).2).trans (by nlinarith [hτδ]))
    (by simpa only [Fintype.card_coe] using hJ)
  exact (not_lt_of_ge hlo) (hwup hwf i j (fun heq => hij (Subtype.ext heq)))

end EuclideanFiveColor.FiniteModule

open scoped BigOperators
namespace EuclideanFiveColor.FiniteBins

variable {A : Type*} [PseudoMetricSpace A]

theorem compact_bins {s : Set A} (hs : IsCompact s) {r : ℝ} (hr : 0 < r) :
    ∃ L : ℕ, ∃ f : s → Fin L, ∀ x y, f x = f y → dist (x : A) (y : A) < r := by
  classical
  obtain ⟨u, _, hu, hucover⟩ := hs.finite_cover_balls (half_pos hr)
  let t := hu.toFinset
  have ht : s ⊆ ⋃ a ∈ t, Metric.ball a (r/2) := by simpa only [t, hu.mem_toFinset] using hucover
  have hx (x : s) : ∃ a ∈ t, dist (x : A) a < r/2 := by
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (ht x.property)
    obtain ⟨hat, hx⟩ := Set.mem_iUnion.mp ha
    exact ⟨a, hat, hx⟩
  let c : s → t := fun x => ⟨(hx x).choose, (hx x).choose_spec.1⟩
  let e : t ≃ Fin t.card := t.equivFin
  refine ⟨t.card, fun x => e (c x), ?_⟩
  intro x y hxy
  have hc : c x = c y := e.injective hxy
  have hdx : dist (x : A) (c x : A) < r/2 := (hx x).choose_spec.2
  have hdy : dist (y : A) (c x : A) < r/2 := by rw [hc]; exact (hx y).choose_spec.2
  calc
    _ ≤ dist (x : A) (c x : A) + dist (c x : A) (y : A) := dist_triangle _ _ _
    _ < r/2+r/2 := add_lt_add hdx (by simpa only [dist_comm] using hdy)
    _ = r := by ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma linear_combination_dist_bound {q : ℕ} (H : Fin q → V)
    (b c : Fin q → ℂ) :
    dist (∑ i, b i • H i) (∑ i, c i • H i) ≤
      dist b c * ∑ i, ‖H i‖ := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖b i • H i - c i • H i‖ := norm_sum_le _ _
    _ ≤ ∑ i, dist b c * ‖H i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_smul, norm_smul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [dist_eq_norm] using dist_le_pi_dist b c i) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- A common finite partition simultaneously controls both coefficient arrays. -/
theorem bounded_coefficient_bins (q : ℕ) (B D τ : ℝ) (hD : 0 ≤ D) (hτ : 0 < τ) :
    ∃ L : ℕ, ∃ f : {b : Fin 2 → Fin q → ℂ // ‖b‖ ≤ B} → Fin L,
      ∀ b c, f b = f c → ∀ H : Fin q → V, (∑ i, ‖H i‖) ≤ D →
      ∀ j : Fin 2, dist (∑ i, b.val j i • H i) (∑ i, c.val j i • H i) < τ := by
  have hden : 0 < 1+D := by linarith
  have hs : IsCompact {b : Fin 2 → Fin q → ℂ | ‖b‖ ≤ B} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (isCompact_closedBall (0 : Fin 2 → Fin q → ℂ) B)
  obtain ⟨L, f, hf⟩ := compact_bins hs (div_pos hτ hden)
  refine ⟨L, f, ?_⟩
  intro b c hbc H hH j
  have hdist : dist (b.val j) (c.val j) < τ/(1+D) :=
    (dist_le_pi_dist b.val c.val j).trans_lt (hf b c hbc)
  calc
    _ ≤ dist (b.val j) (c.val j) * ∑ i, ‖H i‖ := linear_combination_dist_bound H _ _
    _ ≤ dist (b.val j) (c.val j) * D :=
      mul_le_mul_of_nonneg_left hH dist_nonneg
    _ ≤ dist (b.val j) (c.val j) * (1+D) :=
      mul_le_mul_of_nonneg_left (by linarith) dist_nonneg
    _ < τ := (lt_div_iff₀ hden).mp hdist

end EuclideanFiveColor.FiniteBins

end

end OAI
