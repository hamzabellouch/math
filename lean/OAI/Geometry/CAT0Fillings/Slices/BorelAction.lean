import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.CanonicalMass
import OAI.Geometry.CAT0Fillings.Currents.ActionLimits

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.BorelCoefficients
open Foundations MassMeasure

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma integrable_bounded_measurable {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)

lemma borelAction_tendsto_of_bounded_pointwise {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {f : X → ℝ} {fs : ℕ → X → ℝ}
    (hf : Measurable f) (hfs : ∀ j, Measurable (fs j))
    (B : ℝ) (hB : ∀ j x, |fs j x| ≤ B)
    (hlim : ∀ x, Tendsto (fun j => fs j x) atTop (𝓝 (f x)))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Tendsto (fun j => borelAction μ hT (fs j) π) atTop (𝓝 (borelAction μ hT f π)) := by
  have hfB (x : X) : |f x| ≤ B := le_of_tendsto' (hlim x).abs (fun j => hB j x)
  have hfI := integrable_bounded_measurable μ hf hfB
  have hfsI j := integrable_bounded_measurable μ (hfs j) (hB j)
  have hL : Tendsto (fun j => ∫ x, |fs j x - f x| ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ : X => (0 : ℝ)) (fun _ : X => B+B)
      (fun j => ((hfs j).sub hf).abs.aestronglyMeasurable) (integrable_const (B+B))
      (fun j => Eventually.of_forall fun x => show ‖|fs j x - f x|‖ ≤ B+B by
        simpa only [Real.norm_eq_abs,abs_abs] using (abs_sub (fs j x) (f x)).trans
          (add_le_add (hB j x) (hfB x)))
      (Eventually.of_forall fun x => by simpa only [Pi.sub_apply, sub_self,abs_zero] using
        ((hlim x).sub_const (f x)).abs)
    simpa only [integral_zero, Pi.sub_apply] using hh
  exact borelAction_tendsto μ hT hμ hfI hfsI hL π hπ

noncomputable def currentBorelAction {k : ℕ} (T : Functional X k)
    (f : X → ℝ) (π : Fin k → X → ℝ) : ℝ :=
  if hT : IsMetricCurrent T then borelAction (currentMassMeasure hT) hT f π else 0

lemma currentBorelAction_eq {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (f : X → ℝ) (π : Fin k → X → ℝ) :
    currentBorelAction T f π = borelAction (currentMassMeasure hT) hT f π := by
  simp only [currentBorelAction,dite_eq_left hT]

lemma currentBorelAction_eq_action {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {f : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible f π) :
    currentBorelAction T f π = T f π := by
  rw [currentBorelAction_eq hT]
  exact borelAction_eq _ hT (currentMassMeasure_controls hT) h

lemma currentBorelAction_bound {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |currentBorelAction T f π| ≤ (∏ i, (K i : ℝ)) * B * mass T := by
  rw [currentBorelAction_eq hT]
  calc
    _ ≤ (∏ i, (K i : ℝ)) * ∫ x, |f x| ∂currentMassMeasure hT :=
      borelAction_bound _ hT (currentMassMeasure_controls hT)
        (integrable_bounded_measurable _ hf hB) π K hK
    _ ≤ (∏ i, (K i : ℝ)) * ∫ _ : X, B ∂currentMassMeasure hT :=
      mul_le_mul_of_nonneg_left (integral_mono
        (integrable_bounded_measurable _ hf hB).abs (integrable_const B) hB) (by positivity)
    _ = _ := by rw [integral_const,smul_eq_mul,currentMassMeasure_total hT]; ring

lemma currentBorelAction_tendsto {k : ℕ} (T : Functional X k)
    {f : X → ℝ} {fs : ℕ → X → ℝ}
    (hf : Measurable f) (hfs : ∀ j, Measurable (fs j))
    (B : ℝ) (hB : ∀ j x, |fs j x| ≤ B)
    (hlim : ∀ x, Tendsto (fun j => fs j x) atTop (𝓝 (f x)))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Tendsto (fun j => currentBorelAction T (fs j) π) atTop
      (𝓝 (currentBorelAction T f π)) := by
  by_cases hT : IsMetricCurrent T
  · simp only [currentBorelAction_eq hT]
    exact borelAction_tendsto_of_bounded_pointwise hT _ (currentMassMeasure_controls hT)
      hf hfs B hB hlim π hπ
  · simp only [currentBorelAction,dite_eq_right hT]
    exact tendsto_const_nhds

lemma currentBorelAction_add {k : ℕ} (T : Functional X k)
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    currentBorelAction T (f+g) π = currentBorelAction T f π + currentBorelAction T g π := by
  by_cases hT : IsMetricCurrent T
  · simp only [currentBorelAction_eq hT]
    exact borelAction_add _ hT (integrable_bounded_measurable _ hf hB)
      (integrable_bounded_measurable _ hg hC) π hπ
  · simp [currentBorelAction, hT]

lemma currentBorelAction_sub {k : ℕ} (T : Functional X k)
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    currentBorelAction T (f-g) π = currentBorelAction T f π - currentBorelAction T g π := by
  by_cases hT : IsMetricCurrent T
  · simp only [currentBorelAction_eq hT]
    exact borelAction_sub _ hT (integrable_bounded_measurable _ hf hB)
      (integrable_bounded_measurable _ hg hC) π hπ
  · simp [currentBorelAction, hT]

lemma currentBorelAction_smul {k : ℕ} (T : Functional X k)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (c : ℝ) (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    currentBorelAction T (c • f) π = c * currentBorelAction T f π := by
  by_cases hT : IsMetricCurrent T
  · simp only [currentBorelAction_eq hT]
    exact borelAction_smul _ hT (integrable_bounded_measurable _ hf hB) π c hπ
  · simp [currentBorelAction, hT]

lemma exists_lipschitz_closed_indicator_approximation {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] (E : Set X) (hE : IsClosed E) :
    ∃ fs : ℕ → X → ℝ, (∀ j, BoundedLip (fs j)) ∧
      (∀ j x, |fs j x| ≤ 1) ∧
      (∀ x, Tendsto (fun j => fs j x) atTop (𝓝 (E.indicator (fun _ => (1 : ℝ)) x))) := by
  classical
  by_cases hne : E.Nonempty
  · let fs (j : ℕ) (x : X) : ℝ := max 0 (1 - (j+1 : ℝ) * Metric.infDist x E)
    have hLip (j : ℕ) : LipschitzWith (j+1 : ℝ≥0) (fs j) := by
      apply LipschitzWith.const_max _ 0
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (1-(j+1 : ℝ)*Metric.infDist x E) (1-(j+1 : ℝ)*Metric.infDist y E) ≤
        ((j : ℝ)+1)*dist x y
      calc
        _ = ((j : ℝ)+1)*|Metric.infDist x E-Metric.infDist y E| := by
          rw [Real.dist_eq, show (1-(j+1 : ℝ)*Metric.infDist x E) -
            (1-(j+1 : ℝ)*Metric.infDist y E) = -((j+1 : ℝ)*(Metric.infDist x E-Metric.infDist y E)) by ring,
            abs_neg,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ j+1)]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((Metric.lipschitz_infDist_pt E).dist_le_mul x y) (by positivity) |>.trans_eq (by simp)
    have hb (j : ℕ) (x : X) : |fs j x| ≤ 1 := by
      rw [abs_of_nonneg (le_max_left _ _)]
      apply max_le (by norm_num)
      have := Metric.infDist_nonneg (s := E) (x := x)
      have : 0 ≤ (j+1 : ℝ)*Metric.infDist x E := mul_nonneg (by positivity) this
      linarith
    refine ⟨fs,fun j => ⟨⟨j+1,hLip j⟩,1,hb j⟩,hb,fun x => ?_⟩
    by_cases hx : x ∈ E
    · simp [fs,Metric.infDist_zero_of_mem hx,hx]
    · have hd : 0 < Metric.infDist x E := (hE.notMem_iff_infDist_pos hne).mp hx
      obtain ⟨N,hN⟩ := exists_nat_gt (1 / Metric.infDist x E)
      have hN' : 1 < (N : ℝ)*Metric.infDist x E := (div_lt_iff₀ hd).mp hN
      have hev : ∀ᶠ j : ℕ in atTop, fs j x = 0 := by
        filter_upwards [eventually_ge_atTop N] with j hj
        have hj' : (N : ℝ) ≤ j+1 := by exact_mod_cast (Nat.le_succ_of_le hj)
        have hd' := mul_le_mul_of_nonneg_right hj' hd.le
        exact max_eq_left (by linarith)
      simpa only [indicator_of_notMem hx] using
        (tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm) : Tendsto (fun j => fs j x) atTop (𝓝 (0 : ℝ)))
  · have he : E = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ _ => 0, fun _ => BoundedLip.const 0, fun _ _ => by norm_num, fun x => ?_⟩
    simp [he]

section Integrated
variable {A : Type*} [MeasurableSpace A] (ν : Measure A)
variable {k l : ℕ} (T : Functional X k) (ρ : Fin k → X → ℝ)
  (S : A → Functional X l) (π : Fin l → X → ℝ)

def ActionIntegralAgreement (f : X → ℝ) : Prop :=
  Integrable (fun a => currentBorelAction (S a) f π) ν ∧
    currentBorelAction T f ρ = ∫ a, currentBorelAction (S a) f π ∂ν

variable {ν T ρ S π}
lemma ActionIntegralAgreement.of_bounded_pointwise
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hS : ∀ᵐ a ∂ν, IsMetricCurrent (S a))
    {g : A → ℝ} (hg : Integrable g ν) (hg0 : ∀ᵐ a ∂ν, 0 ≤ g a)
    (hgb : ∀ᵐ a ∂ν, mass (S a) ≤ g a)
    {f : X → ℝ} {fs : ℕ → X → ℝ}
    (hf : Measurable f) (hfs : ∀ j, Measurable (fs j))
    (B : ℝ≥0) (hB : ∀ j x, |fs j x| ≤ B)
    (hlim : ∀ x, Tendsto (fun j => fs j x) atTop (𝓝 (f x)))
    (hA : ∀ j, ActionIntegralAgreement ν T ρ S π (fs j)) :
    ActionIntegralAgreement ν T ρ S π f := by
  choose K hK using hπ
  let C : ℝ := (∏ i, (K i : ℝ)) * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdom (j : ℕ) : ∀ᵐ a ∂ν, ‖currentBorelAction (S a) (fs j) π‖ ≤ C*g a := by
    filter_upwards [hS,hgb,hg0] with a ha hb hg_nonneg
    simpa only [Real.norm_eq_abs,C,mul_assoc] using
      (currentBorelAction_bound ha (hfs j) (hB j) π K hK).trans
        (mul_le_mul_of_nonneg le_rfl hb hC hg_nonneg)
  have hconv (a : A) := currentBorelAction_tendsto (S a) hf hfs B hB hlim π (fun i => ⟨K i,hK i⟩)
  have hfi : Integrable (fun a => currentBorelAction (S a) f π) ν :=
    (hg.const_mul C).mono'
      (aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hA j).1.aestronglyMeasurable)
        (Eventually.of_forall hconv)) (by
          filter_upwards [ae_all_iff.mpr hdom] with a ha
          exact le_of_tendsto' (hconv a).norm ha)
  have hright := tendsto_integral_of_dominated_convergence (fun a => C*g a)
    (fun j => (hA j).1.aestronglyMeasurable) (hg.const_mul C) hdom
    (Eventually.of_forall hconv)
  have hleft := currentBorelAction_tendsto T hf hfs B hB hlim ρ hρ
  exact ⟨hfi,tendsto_nhds_unique (hleft.congr fun j => (hA j).2) hright⟩

lemma ActionIntegralAgreement.add
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (hAf : ActionIntegralAgreement ν T ρ S π f)
    (hAg : ActionIntegralAgreement ν T ρ S π g) :
    ActionIntegralAgreement ν T ρ S π (f+g) := by
  constructor
  · exact (hAf.1.add hAg.1).congr (Eventually.of_forall fun a =>
      (currentBorelAction_add (S a) hf hg hB hC _ hπ).symm)
  · simp only [currentBorelAction_add T hf hg hB hC _ hρ,
      currentBorelAction_add _ hf hg hB hC _ hπ]
    rw [integral_add hAf.1 hAg.1,hAf.2,hAg.2]

lemma ActionIntegralAgreement.sub
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (hAf : ActionIntegralAgreement ν T ρ S π f)
    (hAg : ActionIntegralAgreement ν T ρ S π g) :
    ActionIntegralAgreement ν T ρ S π (f-g) := by
  constructor
  · exact (hAf.1.sub hAg.1).congr (Eventually.of_forall fun a =>
      (currentBorelAction_sub (S a) hf hg hB hC _ hπ).symm)
  · simp only [currentBorelAction_sub T hf hg hB hC _ hρ,
      currentBorelAction_sub _ hf hg hB hC _ hπ]
    rw [integral_sub hAf.1 hAg.1,hAf.2,hAg.2]

lemma ActionIntegralAgreement.smul
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hA : ActionIntegralAgreement ν T ρ S π f) (c : ℝ) :
    ActionIntegralAgreement ν T ρ S π (c • f) := by
  constructor
  · exact (hA.1.const_mul c).congr (Eventually.of_forall fun a =>
      (currentBorelAction_smul (S a) hf hB c _ hπ).symm)
  · simp only [currentBorelAction_smul T hf hB c _ hρ,
      currentBorelAction_smul _ hf hB c _ hπ,integral_const_mul,hA.2]

theorem ActionIntegralAgreement.indicator
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hS : ∀ᵐ a ∂ν, IsMetricCurrent (S a))
    {g : A → ℝ} (hg : Integrable g ν) (hg0 : ∀ᵐ a ∂ν, 0 ≤ g a)
    (hgb : ∀ᵐ a ∂ν, mass (S a) ≤ g a)
    (hLip : ∀ f : X → ℝ, BoundedLip f → ActionIntegralAgreement ν T ρ S π f)
    (E : Set X) (hE : MeasurableSet E) :
    ActionIntegralAgreement ν T ρ S π (E.indicator (fun _ => (1 : ℝ))) := by
  classical
  have hb (E : Set X) (x : X) : |E.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ E <;> simp [hx]
  have hcompl (E : Set X) (he : MeasurableSet E)
      (ha : ActionIntegralAgreement ν T ρ S π (E.indicator (fun _ => (1 : ℝ)))) :
      ActionIntegralAgreement ν T ρ S π (Eᶜ.indicator (fun _ => (1 : ℝ))) := by
    rw [indicator_compl]
    exact ActionIntegralAgreement.sub hρ hπ measurable_const
      (measurable_const.indicator he) (fun _ => le_rfl) (hb E)
      (hLip _ (BoundedLip.const 1)) ha
  have hclosed (F : Set X) (hF : IsClosed F) :
      ActionIntegralAgreement ν T ρ S π (F.indicator (fun _ => (1 : ℝ))) := by
    obtain ⟨fs,hf,hfb,hflim⟩ := exists_lipschitz_closed_indicator_approximation F hF
    exact ActionIntegralAgreement.of_bounded_pointwise hρ hπ hS hg hg0 hgb
      (measurable_const.indicator hF.measurableSet) (fun j => (hf j).continuous.measurable)
      1 hfb hflim (fun j => hLip _ (hf j))
  apply MeasurableSet.induction_on_open (C := fun F _ =>
    ActionIntegralAgreement ν T ρ S π (F.indicator (fun _ => (1 : ℝ)))) ?_ hcompl ?_ E hE
  · intro U hU
    simpa only [compl_compl] using hcompl Uᶜ hU.measurableSet.compl (hclosed Uᶜ hU.isClosed_compl)
  · intro f hdisj hf hA
    let F (m : ℕ) : Set X := ⋃ i ∈ (Finset.range m : Set ℕ), f i
    have hFmeas (m : ℕ) : MeasurableSet (F m) :=
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hf i
    have hmono : Monotone F := by
      intro m n hmn
      exact iUnion₂_mono' fun i hi => ⟨i, Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hmn), subset_rfl⟩
    have hFam (m : ℕ) : ActionIntegralAgreement ν T ρ S π (F m |>.indicator (fun _ => (1 : ℝ))) := by
      induction m with
      | zero => simpa [F] using hLip (fun _ => 0) (BoundedLip.const 0)
      | succ m ih =>
        have hFm : F (m+1) = f m ∪ F m := by
          simp only [F,Finset.range_add_one,Finset.coe_insert,biUnion_insert]
        have hd : Disjoint (f m) (F m) := by
          apply disjoint_iUnion_right.mpr
          intro j
          apply disjoint_iUnion_right.mpr
          intro hj
          exact hdisj (ne_of_gt (Finset.mem_range.mp hj))
        rw [hFm,indicator_union_of_disjoint hd]
        exact ActionIntegralAgreement.add hρ hπ (measurable_const.indicator (hf m))
          (measurable_const.indicator (hFmeas m)) (hb (f m)) (hb (F m)) (hA m) ih
    have hUnion : (⋃ m, F m) = ⋃ i, f i := by
      ext x
      simp only [F,mem_iUnion,Finset.mem_coe,Finset.mem_range]
      constructor
      · rintro ⟨m,i,hi,hx⟩
        exact ⟨i,hx⟩
      · rintro ⟨i,hx⟩
        exact ⟨i+1,i,Nat.lt_succ_self i,hx⟩
    apply ActionIntegralAgreement.of_bounded_pointwise hρ hπ hS hg hg0 hgb
      (measurable_const.indicator (MeasurableSet.iUnion hf))
      (fun m => measurable_const.indicator (hFmeas m)) 1 (fun m => hb (F m)) ?_ hFam
    intro x
    have hh := (hmono.tendsto_indicator F (fun _ => (1 : ℝ)) x).mono_right (pure_le_nhds _)
    simpa only [hUnion] using hh

theorem ActionIntegralAgreement.bounded_measurable
    (hρ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (ρ i))
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hS : ∀ᵐ a ∂ν, IsMetricCurrent (S a))
    {g : A → ℝ} (hg : Integrable g ν) (hg0 : ∀ᵐ a ∂ν, 0 ≤ g a)
    (hgb : ∀ᵐ a ∂ν, mass (S a) ≤ g a)
    (hLip : ∀ f : X → ℝ, BoundedLip f → ActionIntegralAgreement ν T ρ S π f)
    {f : X → ℝ} (hf : Measurable f) (B : ℝ≥0) (hB : ∀ x, |f x| ≤ B) :
    ActionIntegralAgreement ν T ρ S π f := by
  classical
  have hsimp : ∀ s : SimpleFunc X ℝ, ActionIntegralAgreement ν T ρ S π s := by
    intro s
    induction s using SimpleFunc.induction with
    | @const c E hE =>
      have hbase := ActionIntegralAgreement.indicator hρ hπ hS hg hg0 hgb hLip E hE
      have hb (x : X) : |E.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
        by_cases hx : x ∈ E <;> simp [hx]
      have hc := ActionIntegralAgreement.smul hρ hπ (measurable_const.indicator hE) hb hbase c
      convert hc using 1
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    | @add s t hd hs ht =>
      obtain ⟨C,hC⟩ := (s.finite_range.image abs).bddAbove
      obtain ⟨D,hD⟩ := (t.finite_range.image abs).bddAbove
      exact ActionIntegralAgreement.add hρ hπ s.measurable t.measurable
        (fun x => hC (mem_image_of_mem _ (mem_range_self x)))
        (fun x => hD (mem_image_of_mem _ (mem_range_self x))) hs ht
  let E : Set ℝ := Icc (-(B : ℝ)) (B : ℝ)
  have h0 : (0 : ℝ) ∈ E := ⟨neg_nonpos.mpr B.coe_nonneg,B.coe_nonneg⟩
  let fs (j : ℕ) := SimpleFunc.approxOn f hf E 0 h0 j
  have hfs (j : ℕ) (x : X) : |fs j x| ≤ B := by
    exact abs_le.mpr (SimpleFunc.approxOn_mem hf h0 j x)
  apply ActionIntegralAgreement.of_bounded_pointwise hρ hπ hS hg hg0 hgb hf
    (fun j => (fs j).measurable) B hfs ?_ (fun j => hsimp (fs j))
  intro x
  exact SimpleFunc.tendsto_approxOn hf h0 (subset_closure (abs_le.mp (hB x)))

end Integrated

end CAT0Fillings.BorelCoefficients
end

end OAI
