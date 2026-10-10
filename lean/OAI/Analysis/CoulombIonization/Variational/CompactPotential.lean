import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.Radial
import OAI.Analysis.CoulombIonization.Variational.SpinFinite

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ContDiff

lemma compact_potential_bounded {d : Space → ℝ} (hd : Continuous d) (hcd : HasCompactSupport d) :
    ∃ C : ℝ, ∀ x : Space, |CoulombAnalysis.tfPotential d x| ≤ C := by
  have h1 : Integrable d := hd.integrable_of_hasCompactSupport hcd
  have hp : MemLp d (5/3 : ENNReal) := hd.memLp_of_hasCompactSupport hcd
  obtain ⟨R,_,hR⟩ := hcd.isBounded.exists_pos_norm_le
  have hs (y : Space) (hy : d y ≠ 0) : ‖y‖ ≤ R := hR y (subset_tsupport d hy)
  obtain ⟨S,_,hS⟩ := CoulombAnalysis.tfPotential_compact_decay h1 hp hs 1 zero_lt_one
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Space) S).exists_bound_of_continuousOn
    (CoulombAnalysis.tfPotential_continuous h1 hp).continuousOn
  refine ⟨max C 1,fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ S
  · exact (hC x (by simpa using hx)).trans (le_max_left _ _)
  · exact (hS x (le_of_not_ge hx)).trans (le_max_right _ _)

lemma core_bounded_potential_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {V : Space → ℝ} (hV : Continuous V) {C : ℝ} (hC : ∀ x, |V x| ≤ C)
    (s : Spins N) (j : Fin N) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 * V (x j)) := by
  apply ((hψ.1 s).norm.integrable_sq.mul_const C).mono'
    (((hψ.1 s).aestronglyMeasurable.norm.pow 2).mul
      (hV.comp (continuous_apply j)).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖‖ψ.value s x‖^2 * V (x j)‖ ≤ _
  rw [norm_mul,Real.norm_of_nonneg (sq_nonneg _),Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC (x j)) (sq_nonneg _)

lemma core_compact_potential_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {d : Space → ℝ} (hd : Continuous d) (hcd : HasCompactSupport d) (s : Spins N) (j : Fin N) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 * CoulombAnalysis.tfPotential d (x j)) := by
  obtain ⟨C,hC⟩ := compact_potential_bounded hd hcd
  exact core_bounded_potential_integrable hψ
    (CoulombAnalysis.tfPotential_continuous (hd.integrable_of_hasCompactSupport hcd)
      (hd.memLp_of_hasCompactSupport hcd)) hC s j

def coreDensityInteraction {N : ℕ} (ψ : FormVector N) (d : Space → ℝ) : ℝ :=
  ∑ s : Spins N, ∑ j : Fin N, ∫ x : Configuration N,
    ‖ψ.value s x‖^2 * CoulombAnalysis.tfPotential d (x j)

lemma spinLift_pole (u : Space → ℂ) (σ : Fin 2) (a : Space) :
    orbitalPole (spinLift u σ) a = CoulombAnalysis.tfPotential (fun y => ‖u y‖^2) a := by
  unfold orbitalPole CoulombAnalysis.tfPotential
  simpa only [div_eq_mul_inv,mul_comm] using spinLift_weight u σ (fun x => ‖a-x‖⁻¹)

lemma spinLift_core_interaction {N : ℕ} (ψ : FormVector N) (u : Space → ℂ) (σ : Fin 2) :
    orbitalCoreInteraction ψ (spinLift u σ) = coreDensityInteraction ψ (fun y => ‖u y‖^2) := by
  simp only [orbitalCoreInteraction,coreDensityInteraction,spinLift_pole]

section Work_CompactDirect_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

lemma continuous_compact_coulomb_integrable {f g : Space → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    Integrable (fun r : Space × Space => f r.1 * g r.2 / ‖r.1-r.2‖) := by
  have hm : Measurable (fun r : Space × Space => f r.1 * g r.2 / ‖r.1-r.2‖) :=
    ((hf.measurable.comp measurable_fst).mul (hg.measurable.comp measurable_snd)).div
      ((measurable_fst.sub measurable_snd).norm)
  have hg1 : Integrable g := hg.integrable_of_hasCompactSupport hcg
  have hgp : MemLp g (5/3 : ENNReal) := hg.memLp_of_hasCompactSupport hcg (p := (5/3 : ENNReal))
  have hgn1 : Integrable (fun x => ‖g x‖) := hg.norm.integrable_of_hasCompactSupport hcg.norm
  have hgnp : MemLp (fun x => ‖g x‖) (5/3 : ENNReal) := hg.norm.memLp_of_hasCompactSupport hcg.norm (p := (5/3 : ENNReal))
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall (fun x => ?_),?_⟩
  · simpa only [mul_div_assoc] using (CoulombAnalysis.tfPotential_integrable hg1 hgp x).const_mul (f x)
  · have hi : Integrable (fun x => ‖f x‖ * CoulombAnalysis.tfPotential (fun y => ‖g y‖) x) := (hf.norm.mul (CoulombAnalysis.tfPotential_continuous hgn1 hgnp)).integrable_of_hasCompactSupport
      hcf.norm.mul_right
    apply hi.congr
    filter_upwards [] with x
    simp only [norm_div,norm_mul,norm_norm,CoulombAnalysis.tfPotential,← integral_const_mul]
    congr 1
    funext y
    ring

lemma spatialFiniteDensity_continuous {ι : Type*} [Fintype ι] (p : ι → ℝ) {u : ι → Space → ℂ}
    (hu : ∀ i, Continuous (u i)) : Continuous (spatialFiniteDensity p u) := by
  unfold spatialFiniteDensity
  fun_prop

lemma spatialFiniteDensity_compact {ι : Type*} [Fintype ι] (p : ι → ℝ) {u : ι → Space → ℂ}
    (hu : ∀ i, HasCompactSupport (u i)) : HasCompactSupport (spatialFiniteDensity p u) := by
  unfold spatialFiniteDensity
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ((compact_norm_sq (hu a)).mul_left).add ih

lemma spatialFiniteDensity_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ} {u : ι → Space → ℂ}
    (hp : ∀ i, 0 ≤ p i) (x : Space) : 0 ≤ spatialFiniteDensity p u x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))

lemma compact_direct_mono {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g)
    (hn : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ g x) :
    (∫ r : Space × Space, f r.1 * f r.2 / ‖r.1-r.2‖) ≤
      ∫ r : Space × Space, g r.1 * g r.2 / ‖r.1-r.2‖ := by
  apply integral_mono (continuous_compact_coulomb_integrable hf hf hcf hcf)
    (continuous_compact_coulomb_integrable hg hg hcg hcg)
  intro r
  exact div_le_div_of_nonneg_right (mul_le_mul (hb r.1) (hb r.2) (hn r.2)
    ((hn r.1).trans (hb r.1))) (norm_nonneg _)

end Work_CompactDirect_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma bounded_compact_memLp {f : Space → ℝ} (hf : Measurable f)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support f ⊆ J)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) (p : ENNReal) : MemLp f p := by
  have hi := memLp_indicator_const (μ := volume) p hJ.measurableSet B (Or.inr hJ.measure_lt_top.ne)
  apply hi.mono' hf.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : x ∈ J
  · simpa only [Set.indicator_of_mem hx,Real.norm_eq_abs] using hb x
  · have hz : f x = 0 := by by_contra hn; exact hx (hs hn)
    simp only [Set.indicator_of_notMem hx,hz,norm_zero,le_refl]

lemma bounded_compact_integrable {f : Space → ℝ} (hf : Measurable f)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support f ⊆ J)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) : Integrable f :=
  memLp_one_iff_integrable.mp (bounded_compact_memLp hf hJ hs hb 1)

lemma compact_support_potential_bounded {f : Space → ℝ} (h1 : Integrable f)
    (hp : MemLp f (5/3 : ENNReal)) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support f ⊆ J) :
    ∃ C : ℝ, ∀ x : Space, |CoulombAnalysis.tfPotential f x| ≤ C := by
  obtain ⟨R,_,hR⟩ := hJ.isBounded.exists_pos_norm_le
  have hr (y : Space) (hy : f y ≠ 0) : ‖y‖ ≤ R := hR y (hs hy)
  obtain ⟨S,_,hS⟩ := CoulombAnalysis.tfPotential_compact_decay h1 hp hr 1 zero_lt_one
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Space) S).exists_bound_of_continuousOn
    (CoulombAnalysis.tfPotential_continuous h1 hp).continuousOn
  refine ⟨max C 1,fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ S
  · exact (hC x (by simpa using hx)).trans (le_max_left _ _)
  · exact (hS x (le_of_not_ge hx)).trans (le_max_right _ _)

lemma compact_support_coulomb_integrable {f g : Space → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g)
    (hgp : MemLp g (5/3 : ENNReal)) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support g ⊆ J) :
    Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖) := by
  have hm : Measurable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall (fun x => ?_),?_⟩
  · simpa only [mul_div_assoc] using (CoulombAnalysis.tfPotential_integrable hg hgp x).const_mul (f x)
  · obtain ⟨C,hC⟩ := compact_support_potential_bounded hg.norm hgp.norm hJ
      (fun x hx => hs (by intro hz; exact hx (by simp [hz])))
    have hi : Integrable (fun x => ‖f x‖*CoulombAnalysis.tfPotential (fun y => ‖g y‖) x) := by
      apply (hf.norm.mul_const C).mono'
        ((hfm.norm.mul (CoulombAnalysis.tfPotential_continuous hg.norm hgp.norm).measurable).aestronglyMeasurable)
      filter_upwards [] with x
      change ‖‖f x‖*CoulombAnalysis.tfPotential (fun y => ‖g y‖) x‖ ≤ ‖f x‖*C
      rw [norm_mul,norm_norm,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)
    apply hi.congr
    filter_upwards [] with x
    simp only [norm_div,norm_mul,norm_norm,CoulombAnalysis.tfPotential,← integral_const_mul]
    congr 1
    funext y
    ring

lemma bounded_compact_coulomb_integrable {f g : Space → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    {J K : Set Space} (hJ : IsCompact J) (hK : IsCompact K)
    (hsf : Function.support f ⊆ J) (hsg : Function.support g ⊆ K)
    {B C : ℝ} (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖) :=
  compact_support_coulomb_integrable hfm hgm (bounded_compact_integrable hfm hJ hsf hb)
    (bounded_compact_integrable hgm hK hsg hc) (bounded_compact_memLp hgm hK hsg hc _) hK hsg

end CoulombAtom

end

end OAI
