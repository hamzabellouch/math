import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseDecompositionNorm
import OAI.MathematicalPhysics.Boltzmann.Branching.VaryingBoundedMultiplier
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # Domination of finite sums of cold sources by the total source -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem finite_sum_coldSource_le {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    ∑ i ∈ s, coldSource q b L F (c i) p ≤ source q b L F p := by
  have hν : frequency q b F p ≤ L := (frequency_bound hq hb hFm hF p).trans hL
  unfold coldSource source
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  exact add_le_add (finite_sum_gain_le s hcm hFm hc hF hSum b p)
    (mul_le_mul_of_nonneg_left (hSum p) (sub_nonneg.mpr hν))

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Summable cold families and the nonnegative hot remainder -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*}

theorem finite_sum_picard_le {β b L T R : ℝ} (hβ : β < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R * CutoffLipschitz.frequencyConstant β b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ} (s : Finset I)
    (hFm : Measurable F) (hc₀m : ∀ i ∈ s, Measurable (c₀ i))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hc₀ : ∀ i ∈ s, ∀ p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z)
    (n : ℕ) (z : ℝ × JetPrototype.Phase) :
    ∑ i ∈ s, coldPicard β b L T F (c₀ i) n z ≤ F z := by
  have hu (i) (hi : i ∈ s) := coldPicard_properties hβ hb hL hT hR hloss
    hFm (hc₀m i hi) hF (hc₀ i hi) hF₀ hFeq
  let S := HotApplication.realBound β * R ^ 2 + L * R
  have hfs (q) : 0 ≤ forcing β b L F q ∧ forcing β b L F q ≤ S :=
    HotRepresentative.source_bounds (f := GaussianLocal.state F) hβ hb hR hloss
      (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1, (p.1.2, p.2))) ((q.1, q.2.1), q.2.2)
  induction n generalizing z with
  | zero => simpa only [coldPicard, Finset.sum_const_zero] using (hF z).1
  | succ n ih =>
    let g (i : I) := coldForcing β b L F (coldPicard β b L T F (c₀ i) n)
    have hgm (i) (hi : i ∈ s) : Measurable (g i) :=
      measurable_coldForcing hFm (hu i hi n).1 β b L
    have hgs (i) (hi : i ∈ s) (q) : 0 ≤ g i q ∧ g i q ≤ S :=
      HotRepresentative.coldSource_bounds (F := GaussianLocal.state F)
        (c := GaussianLocal.state (coldPicard β b L T F (c₀ i) n)) hβ hb hR hloss
        (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state (hu i hi n).1)
        (fun p => hF (p.1.1, (p.1.2, p.2)))
        (fun p => ⟨((hu i hi n).2 (p.1.1, (p.1.2, p.2))).1,
          (((hu i hi n).2 (p.1.1, (p.1.2, p.2))).2).trans (hF _).2⟩)
        ((q.1, q.2.1), q.2.2)
    have hsum (q) : ∑ i ∈ s, g i q ≤ forcing β b L F q :=
      HotRepresentative.finite_sum_coldSource_le hβ hb hloss s
        (fun i hi => GaussianLocal.measurable_state (hu i hi n).1) (GaussianLocal.measurable_state hFm)
        (fun i hi p => ⟨((hu i hi n).2 (p.1.1, (p.1.2, p.2))).1,
          (((hu i hi n).2 (p.1.1, (p.1.2, p.2))).2).trans (hF _).2⟩)
        (fun p => hF (p.1.1, (p.1.2, p.2)))
        (fun p => ih (p.1.1, (p.1.2, p.2))) ((q.1, q.2.1), q.2.2)
    change (∑ i ∈ s, PositiveIntegral.value T L JetBarrier.flight (c₀ i) (g i) z) ≤ F z
    rw [PositiveIntegral.value_finsetSum hT hL GaussianLocal.measurable_flight s c₀ g hgm
      (fun i hi q => by rw [abs_of_nonneg (hgs i hi q).1]; exact (hgs i hi q).2), hFeq z]
    have hsabs (q) : |∑ i ∈ s, g i q| ≤ S := by
      rw [abs_of_nonneg (Finset.sum_nonneg (fun i hi => (hgs i hi q).1))]
      exact (hsum q).trans (hfs q).2
    have hfabs (q) : |forcing β b L F q| ≤ S := by
      rw [abs_of_nonneg (hfs q).1]
      exact (hfs q).2
    exact PositiveIntegral.value_mono hT hL GaussianLocal.measurable_flight hSum₀
      (Finset.measurable_sum s hgm) (measurable_forcing hFm β b L)
      hsabs hfabs hsum z

theorem finite_sum_coldLimit_le {β b L T R : ℝ} (hβ : β < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R * CutoffLipschitz.frequencyConstant β b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ} (s : Finset I)
    (hFm : Measurable F) (hc₀m : ∀ i ∈ s, Measurable (c₀ i))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hc₀ : ∀ i ∈ s, ∀ p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z)
    (z : ℝ × JetPrototype.Phase) : ∑ i ∈ s, coldLimit β b L T F (c₀ i) z ≤ F z := by
  have ht := tendsto_finsetSum s (fun i hi =>
    (coldLimit_solution hβ hb hL hT hR hloss hFm (hc₀m i hi) hF (hc₀ i hi) hF₀ hFeq).2.2.2 z)
  exact le_of_tendsto ht (.of_forall (fun n =>
    finite_sum_picard_le hβ hb hL hT hR hloss s hFm hc₀m hF hc₀ hF₀ hSum₀ hFeq n z))

theorem cold_family_summable {β b L T R : ℝ} (hβ : β < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R * CutoffLipschitz.frequencyConstant β b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z)
    (z : ℝ × JetPrototype.Phase) :
    Summable (fun i => coldLimit β b L T F (c₀ i) z) ∧
      (∑' i, coldLimit β b L T F (c₀ i) z) ≤ F z := by
  have hn (i) : 0 ≤ coldLimit β b L T F (c₀ i) z :=
    ((coldLimit_solution hβ hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i) hF₀ hFeq).2.1 z).1
  have hs (s : Finset I) : (∑ i ∈ s, coldLimit β b L T F (c₀ i) z) ≤ F z :=
    finite_sum_coldLimit_le hβ hb hL hT hR hloss s hFm (fun i _ => hc₀m i) hF
      (fun i _ => hc₀ i) hF₀ (hSum₀ s) hFeq z
  exact ⟨summable_of_sum_le hn hs, Real.tsum_le_of_sum_le hn hs⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Countable cold gain sums and the exact hot-source identity -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem gain_family_summable {β b R : ℝ}
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    Summable (fun i => gain β b (c i) p) ∧
      (∑' i, gain β b (c i) p) ≤ gain β b F p := by
  have hn (i) : 0 ≤ gain β b (c i) p :=
    gain_nonneg (fun q => (hc i q).1) β b p
  have hs (s : Finset I) : (∑ i ∈ s, gain β b (c i) p) ≤ gain β b F p :=
    finite_sum_gain_le s (fun i _ => hcm i) hFm
      (fun i _ q => hc i q) hF (hSum s) b p
  exact ⟨summable_of_sum_le hn hs, Real.tsum_le_of_sum_le hn hs⟩

theorem tsum_coldSource {β b R : ℝ}
    (L : ℝ) {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    (∑' i, coldSource β b L F (c i) p) =
      (∑' i, gain β b (c i) p) + (L - frequency β b F p) * (∑' i, c i p) := by
  have hg := (gain_family_summable (β := β) (b := b) hcm hFm hc hF hSum p).1
  have hcs : Summable (fun i => c i p) :=
    summable_of_sum_le (fun i => (hc i p).1) (fun s => hSum s p)
  unfold coldSource
  rw [hg.tsum_add (hcs.mul_left _), tsum_mul_left]

theorem hot_source_identity {β b R : ℝ}
    (L : ℝ) {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    source β b L F p - (∑' i, coldSource β b L F (c i) p) =
      (gain β b F p - ∑' i, gain β b (c i) p) +
      (L - frequency β b F p) * (F p - ∑' i, c i p) := by
  rw [tsum_coldSource L hcm hFm hc hF hSum]
  unfold source
  ring


/-- Dropping the common loss and all but one of the subtracted cold gains. -/
theorem hot_source_le_single {β b R : ℝ} (L : ℝ)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p)
    (i : I) (p : X × Velocity) :
    source β b L F p - (∑' j, coldSource β b L F (c j) p) -
        L * (F p - ∑' j, c j p) ≤ gain β b F p - gain β b (c i) p := by
  have hgs := (gain_family_summable (β := β) (b := b) hcm hFm hc hF hSum p).1
  have hsingle : gain β b (c i) p ≤ ∑' j, gain β b (c j) p :=
    hgs.le_tsum i (fun j _ => gain_nonneg (fun v => (hc j v).1) β b p)
  have hcs : (∑' j, c j p) ≤ F p :=
    Real.tsum_le_of_sum_le (fun j => (hc j p).1) (fun s => hSum s p)
  have hloss := mul_nonneg (frequency_nonneg (fun v => (hF v).1) β b p)
    (sub_nonneg.mpr hcs)
  rw [hot_source_identity L hcm hFm hc hF hSum]
  nlinarith

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Vanishing weighted variance gives strong L1 convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

lemma abs_le_mass_add_variance {u r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    |u| ≤ δ*r+(u^2/r)/δ := by
  have hpos : 0 < δ*r := mul_pos hδ hr
  have hnum : |u| *(δ*r) ≤ (δ*r)^2+u^2 := by
    nlinarith [sq_nonneg (|u|-δ*r),sq_abs u,sq_nonneg u]
  calc
    |u| ≤ ((δ*r)^2+u^2)/(δ*r) := (le_div_iff₀ hpos).mpr hnum
    _ = δ*r+(u^2/r)/δ := by field_simp

theorem strongL1_of_weighted_variance
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u r : ℕ → X → ℝ} {B : ℝ} (hB : 0 < B)
    (hui : ∀ n, Integrable (u n) μ) (hri : ∀ n, Integrable (r n) μ)
    (hr : ∀ n x, 0 < r n x) (hbound : ∀ n, (∫ x, r n x ∂μ) ≤ B)
    (hvi : ∀ n, Integrable (fun x => (u n x)^2/r n x) μ)
    (hv : Tendsto (fun n => ∫ x, (u n x)^2/r n x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n) 1 μ) atTop (𝓝 0) := by
  have habs : Tendsto (fun n => ∫ x, |u n x| ∂μ) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun n => ha.trans_le (integral_nonneg (fun x => abs_nonneg (u n x))))
    · intro ε hε
      let δ := ε/(2*B)
      have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hB)
      have ht : Tendsto (fun n => (∫ x, (u n x)^2/r n x ∂μ)/δ) atTop (𝓝 0) := by
        simpa only [zero_div] using hv.div_const δ
      filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))] with n hn
      have he : (∫ x, |u n x| ∂μ) ≤ δ*(∫ x, r n x ∂μ)+
          (∫ x, (u n x)^2/r n x ∂μ)/δ := by
        have hh := integral_mono (hui n).abs ((hri n).const_mul δ |>.add ((hvi n).div_const δ))
          (fun x => abs_le_mass_add_variance (hr n x) hδ)
        simp only [Pi.add_apply] at hh
        rw [integral_add ((hri n).const_mul δ) ((hvi n).div_const δ),
          integral_const_mul,integral_div] at hh
        exact hh
      have hδB : δ*B = ε/2 := by dsimp only [δ]; field_simp
      have hb := mul_le_mul_of_nonneg_left (hbound n) hδ.le
      linarith
  have he n : eLpNorm (u n) 1 μ = ENNReal.ofReal (∫ x, |u n x| ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hui n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hui n)]
    simp only [Real.norm_eq_abs]
  simpa only [he,ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal habs

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Weak first and second moments identify a vanishing weighted variance -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma weighted_variance_identity {a r b : ℝ} (hr : r ≠ 0) :
    (a-r*b)^2/r = a^2/r-2*(b*a)+(b*b)*r := by
  field_simp
  ring

theorem weighted_variance_moments
    {a r : ℕ → X → ℝ} {A R b : X → ℝ}
    (ha : Published.WeakL1Converges μ a A) (hr : Published.WeakL1Converges μ r R)
    (hai : ∀ n, Integrable (a n) μ) (hri : ∀ n, Integrable (r n) μ)
    (hrp : ∀ n x, 0 < r n x)
    (hsi : ∀ n, Integrable (fun x => (a n x)^2/r n x) μ)
    (hbm : Measurable b) (C : ℝ≥0) (hb : ∀ x, |b x| ≤ C)
    (hA : A =ᵐ[μ] fun x => R x*b x)
    (hsecond : Tendsto (fun n => ∫ x, (a n x)^2/r n x ∂μ)
      atTop (𝓝 (∫ x, (b x*b x)*R x ∂μ))) :
    (∀ n, Integrable (fun x => (a n x-r n x*b x)^2/r n x) μ) ∧
    Tendsto (fun n => ∫ x, (a n x-r n x*b x)^2/r n x ∂μ) atTop (𝓝 0) := by
  have hbb x : |b x*b x| ≤ (C:ℝ)*C := by
    rw [abs_mul]
    exact mul_le_mul (hb x) (hb x) (abs_nonneg _) C.coe_nonneg
  have hcross n : Integrable (fun x => b x*a n x) μ :=
    (hai n).bdd_mul hbm.aestronglyMeasurable (ae_of_all _ hb)
  have hlast n : Integrable (fun x => (b x*b x)*r n x) μ :=
    (hri n).bdd_mul (hbm.mul hbm).aestronglyMeasurable (ae_of_all _ hbb)
  have he n : (fun x => (a n x-r n x*b x)^2/r n x) =
      (fun x => (a n x)^2/r n x)- (fun x => 2*(b x*a n x))+
        (fun x => (b x*b x)*r n x) := by
    funext x
    exact weighted_variance_identity (hrp n x).ne'
  have hv n : Integrable (fun x => (a n x-r n x*b x)^2/r n x) μ := by
    rw [he]
    exact ((hsi n).sub ((hcross n).const_mul 2)).add (hlast n)
  have hei n : (∫ x, (a n x-r n x*b x)^2/r n x ∂μ) =
      (∫ x, (a n x)^2/r n x ∂μ)-2*(∫ x, b x*a n x ∂μ)+
        (∫ x, (b x*b x)*r n x ∂μ) := by
    rw [he]
    have heq := integral_add ((hsi n).sub ((hcross n).const_mul 2)) (hlast n)
    simp only [Pi.sub_apply] at heq
    rw [integral_sub (hsi n) ((hcross n).const_mul 2),integral_const_mul] at heq
    exact heq
  have hlim := (hsecond.sub ((ha.2.2 b hbm ⟨C,hb⟩).const_mul 2)).add
    (hr.2.2 (fun x => b x*b x) (hbm.mul hbm) ⟨(C:ℝ)*C,hbb⟩)
  have hz : (∫ x, b x*A x ∂μ) = ∫ x, (b x*b x)*R x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hA] with x hx
    rw [hx]
    ring
  rw [hz,show (∫ x, (b x*b x)*R x ∂μ)-2*(∫ x, (b x*b x)*R x ∂μ)+
    (∫ x, (b x*b x)*R x ∂μ) = 0 by ring] at hlim
  exact ⟨hv,by simpa only [hei] using hlim⟩

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The nonnegative hot remainder of the countable cold construction -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

def hotRemainder (β b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : I → JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  F z - ∑' i, coldLimit β b L T F (c₀ i) z

def hotForcing (β b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : I → JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  forcing β b L F z - ∑' i, coldForcing β b L F (coldLimit β b L T F (c₀ i)) z

private theorem value_sub {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {g h : ℝ × JetPrototype.Phase → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S)
    (f₀ k₀ : JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) :
    PositiveIntegral.value T L JetBarrier.flight f₀ g z -
      PositiveIntegral.value T L JetBarrier.flight k₀ h z =
      PositiveIntegral.value T L JetBarrier.flight (fun p => f₀ p - k₀ p) (fun q => g q - h q) z := by
  unfold PositiveIntegral.value
  have he (r : ℝ) : Real.exp (-L * (PositiveIntegral.time T z.1 - r)) *
      (g (r, JetBarrier.flight (r - PositiveIntegral.time T z.1) z.2) -
        h (r, JetBarrier.flight (r - PositiveIntegral.time T z.1) z.2)) =
      Real.exp (-L * (PositiveIntegral.time T z.1 - r)) *
        g (r, JetBarrier.flight (r - PositiveIntegral.time T z.1) z.2) -
      Real.exp (-L * (PositiveIntegral.time T z.1 - r)) *
        h (r, JetBarrier.flight (r - PositiveIntegral.time T z.1) z.2) := mul_sub _ _ _
  simp_rw [he]
  rw [intervalIntegral.integral_sub
    (PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hgm hg z)
    (PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hhm hh z)]
  ring

theorem hotRemainder_solution {β b L T R : ℝ} (hβ : β < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R * CutoffLipschitz.frequencyConstant β b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z) :
    Measurable (hotRemainder β b L T F c₀) ∧
      (∀ z, 0 ≤ hotRemainder β b L T F c₀ z ∧ hotRemainder β b L T F c₀ z ≤ F z) ∧
      (∀ z, 0 ≤ hotForcing β b L T F c₀ z ∧ hotForcing β b L T F c₀ z ≤ forcing β b L F z) ∧
      ∀ z, hotRemainder β b L T F c₀ z = PositiveIntegral.value T L JetBarrier.flight
        (fun p => F₀ p - ∑' i, c₀ i p) (hotForcing β b L T F c₀) z := by
  let c (i : I) := coldLimit β b L T F (c₀ i)
  let G (i : I) := coldForcing β b L F (c i)
  let S := HotApplication.realBound β * R ^ 2 + L * R
  have hc (i) := coldLimit_solution hβ hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i) hF₀ hFeq
  have hcf (z) := cold_family_summable hβ hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hSum₀ hFeq z
  have hcm : ∀ i, Measurable (c i) := fun i => (hc i).1
  have hcb (i) (z) : 0 ≤ c i z ∧ c i z ≤ R :=
    ⟨((hc i).2.1 z).1, ((hc i).2.1 z).2.trans (hF z).2⟩
  have hgm : ∀ i, Measurable (G i) := fun i => measurable_coldForcing hFm (hcm i) β b L
  have hgb (i) (z) : 0 ≤ G i z ∧ G i z ≤ S :=
    HotRepresentative.coldSource_bounds (F := GaussianLocal.state F) (c := GaussianLocal.state (c i)) hβ hb hR hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state (hcm i))
      (fun p => hF (p.1.1, (p.1.2, p.2))) (fun p => hcb i (p.1.1, (p.1.2, p.2))) ((z.1,z.2.1),z.2.2)
  have hfs (z) : 0 ≤ forcing β b L F z ∧ forcing β b L F z ≤ S :=
    HotRepresentative.source_bounds (f := GaussianLocal.state F) hβ hb hR hloss
      (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1, (p.1.2, p.2))) ((z.1,z.2.1),z.2.2)
  have hGfinite (s : Finset I) (z) : ∑ i ∈ s, G i z ≤ forcing β b L F z :=
    HotRepresentative.finite_sum_coldSource_le hβ hb hloss s
      (fun i _ => GaussianLocal.measurable_state (hcm i)) (GaussianLocal.measurable_state hFm)
      (fun i _ p => hcb i (p.1.1, (p.1.2, p.2)))
      (fun p => hF (p.1.1, (p.1.2, p.2)))
      (fun p => finite_sum_coldLimit_le hβ hb hL hT hR hloss s hFm (fun i _ => hc₀m i)
        hF (fun i _ => hc₀ i) hF₀ (hSum₀ s) hFeq (p.1.1, (p.1.2, p.2))) ((z.1,z.2.1),z.2.2)
  have hGs (z) : Summable (fun i => G i z) := summable_of_sum_le (fun i => (hgb i z).1) (fun s => hGfinite s z)
  have hGle (z) : (∑' i, G i z) ≤ forcing β b L F z :=
    Real.tsum_le_of_sum_le (fun i => (hgb i z).1) (fun s => hGfinite s z)
  have hSm : Measurable (fun z => ∑' i, G i z) := Measurable.tsum hgm
  have hSabs (z) : |∑' i, G i z| ≤ S := by
    rw [abs_of_nonneg (tsum_nonneg (fun i => (hgb i z).1))]
    exact (hGle z).trans (hfs z).2
  refine ⟨hFm.sub (Measurable.tsum hcm), ?_, ?_, ?_⟩
  · intro z
    exact ⟨sub_nonneg.mpr (hcf z).2, sub_le_self _ (tsum_nonneg (fun i => (hcb i z).1))⟩
  · intro z
    exact ⟨sub_nonneg.mpr (hGle z), sub_le_self _ (tsum_nonneg (fun i => (hgb i z).1))⟩
  · intro z
    have hs := PositiveIntegral.hasSum_value hT hL GaussianLocal.measurable_flight c₀
      (fun p => summable_of_sum_le (fun i => (hc₀ i p).1) (fun s => hSum₀ s p)) G hgm hgb hGs
      (fun q => (hGle q).trans (hfs q).2) z
    have he : (fun i => PositiveIntegral.value T L JetBarrier.flight (c₀ i) (G i) z) =
        (fun i => c i z) := funext (fun i => ((hc i).2.2.1 z).symm)
    rw [he] at hs
    change F z - ∑' i, c i z = _
    rw [hFeq z, hs.tsum_eq]
    exact value_sub hT hL (measurable_forcing hFm β b L) hSm
      (fun q => by rw [abs_of_nonneg (hfs q).1]; exact (hfs q).2) hSabs F₀
      (fun p => ∑' i, c₀ i p) z

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Strong first moments from matched weighted second moments -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weighted_moments_strong
    {a r : ℕ → X → ℝ} {A R b : X → ℝ}
    (ha : Published.WeakL1Converges μ a A) (hr : Published.WeakL1Converges μ r R)
    (hai : ∀ n, Integrable (a n) μ) (hri : ∀ n, Integrable (r n) μ)
    (hrp : ∀ n x, 0 < r n x) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ n, (∫ x, r n x ∂μ) ≤ B)
    (hsi : ∀ n, Integrable (fun x => (a n x)^2/r n x) μ)
    (hbm : Measurable b) (C : ℝ≥0) (hb : ∀ x, |b x| ≤ C)
    (hA : A =ᵐ[μ] fun x => R x*b x)
    (hsecond : Tendsto (fun n => ∫ x, (a n x)^2/r n x ∂μ)
      atTop (𝓝 (∫ x, (b x*b x)*R x ∂μ)))
    (hstrong : Tendsto (fun n => eLpNorm (fun x => r n x-R x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x-A x) 1 μ) atTop (𝓝 0) := by
  obtain ⟨hvi,hv⟩ := weighted_variance_moments ha hr hai hri hrp hsi hbm C hb hA hsecond
  have hmul n : Integrable (fun x => r n x*b x) μ := by
    simpa only [mul_comm] using (hri n).bdd_mul hbm.aestronglyMeasurable (ae_of_all _ hb)
  have hui n : Integrable (fun x => a n x-r n x*b x) μ := (hai n).sub (hmul n)
  have hu := strongL1_of_weighted_variance hB hui hri hrp hbound hvi hv
  have he := tendsto_L1_bounded_mul_zero
    (fun n => ((hri n).sub hr.2.1).aestronglyMeasurable)
    (fun _ => hbm.aestronglyMeasurable) hstrong C.coe_nonneg
    (Eventually.of_forall (fun _ => ae_of_all μ hb))
  have ht := hu.add he
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have hid : (fun x => a n x-A x) =ᵐ[μ]
      (fun x => (a n x-r n x*b x)+b x*(r n x-R x)) := by
    filter_upwards [hA] with x hx
    rw [hx]
    ring
  change eLpNorm (fun x => a n x-A x) 1 μ ≤
    eLpNorm (fun x => a n x-r n x*b x) 1 μ+eLpNorm (fun x => b x*(r n x-R x)) 1 μ
  rw [eLpNorm_congr_ae hid]
  exact eLpNorm_add_le (by norm_num)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Measurability and norm continuity of the constructed hot remainder -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

theorem hot_regularity {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) u) :
    Measurable (hotForcing q b L T F c₀) ∧
      (∀ u, |hotForcing q b L T F c₀ u| ≤ HotApplication.realBound q*R^2+L*R) ∧
      Continuous (fun t => PhaseEssSup.size (fun p => hotRemainder q b L T F c₀ (t,p))) := by
  have hs := hotRemainder_solution hq hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hSum₀ hFeq
  have hcm (i) := (coldLimit_solution hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i) hF₀ hFeq).1
  have hgm : Measurable (hotForcing q b L T F c₀) :=
    (measurable_forcing hFm q b L).sub
      (Measurable.tsum (fun i => measurable_coldForcing hFm (hcm i) q b L))
  have hg (u) : |hotForcing q b L T F c₀ u| ≤ HotApplication.realBound q*R^2+L*R := by
    rw [abs_of_nonneg (hs.2.2.1 u).1]
    apply (hs.2.2.1 u).2.trans
    exact (HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)).2
  have hr (u) : |hotRemainder q b L T F c₀ u| ≤ R := by
    rw [abs_of_nonneg (hs.2.1 u).1]
    exact (hs.2.1 u).2.trans (hF u).2
  refine ⟨hgm,hg,?_⟩
  apply PhaseEssSup.continuous_size hT hL _ hR hgm hs.1 hg hr hs.2.2.2
  unfold HotApplication.realBound
  positivity

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
