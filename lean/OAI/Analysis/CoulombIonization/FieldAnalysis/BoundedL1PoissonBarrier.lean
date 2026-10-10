import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.PatchWeakPoisson
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakHarmonicL1Barrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierNuclearBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BoundedL1PotentialBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_L1_laplacian_pair_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) (volume.prod volume) := by
  have hΔ := tfLaplacian_continuous hφ
  have hΔc := tfLaplacian_compact hφ hc
  have hj : Measurable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) :=
    ((hm.comp measurable_snd).div (measurable_fst.sub measurable_snd).norm).mul (hΔ.measurable.comp measurable_fst)
  apply (integrable_prod_iff hj.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => (bounded_L1_potential_integrable hm hi hM hn hb x).mul_const (Δ φ x)),?_⟩
  have hp := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  have htest := CoulombBarrier.locallyIntegrable_mul_test hp.locallyIntegrable hΔ.norm hΔc.norm
  have he (x : TFSpace) : (∫ y, ‖ρ y/‖x-y‖*Δ φ x‖) = tfPotential ρ x*‖Δ φ x‖ := by
    simp_rw [norm_mul,Real.norm_of_nonneg (div_nonneg (hn _) (norm_nonneg _))]
    exact integral_mul_const _ _
  simpa only [he] using htest

theorem bounded_L1_weak_poisson {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, tfPotential ρ x*Δ φ x) = -(4*Real.pi)*(∫ x, ρ x*φ x) := by
  calc
    _ = ∫ x, ∫ y, ρ y/‖x-y‖*Δ φ x := by simp only [integral_mul_const,tfPotential]
    _ = ∫ y, ∫ x, ρ y/‖x-y‖*Δ φ x :=
      integral_integral_swap (bounded_L1_laplacian_pair_integrable hm hi hM hn hb hφ hc)
    _ = ∫ y, ρ y*tfPotential (Δ φ) y := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change (∫ x, ρ y/‖x-y‖*Δ φ x) = ρ y*(∫ x, Δ φ x/‖y-x‖)
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by dsimp only; rw [norm_sub_rev]; ring
    _ = _ := by
      simp_rw [tfPotential_laplacian hφ hc]
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring

end CoulombAnalysis
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

def meanFieldOffset (lam : ℝ) (ρ : TFSpace → ℝ) (x : TFSpace) : ℝ := -tfPotential ρ x-lam

lemma meanFieldOffset_weak_nuclear {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (Z lam : ℝ) :
    WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+meanFieldOffset lam ρ x)
      (fun x => 4*Real.pi*ρ x) := by
  have hp := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  apply (weakNuclearLower_add_iff Z (hp.neg.sub continuous_const).locallyIntegrable).mpr
  intro φ hφ hc _ _
  have hiΔ : Integrable (Δ φ) := (tfLaplacian_continuous hφ).integrable_of_hasCompactSupport (tfLaplacian_compact hφ hc)
  have hiq := locallyIntegrable_mul_test hp.locallyIntegrable (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)
  change (∫ x, 4*Real.pi*ρ x*φ x) ≤ ∫ x, (-tfPotential ρ x-lam)*Δ φ x
  simp_rw [sub_mul,neg_mul]
  have hneg : Integrable (fun x => -(tfPotential ρ x * Δ φ x)) := hiq.neg
  have hlam : Integrable (fun x => lam * Δ φ x) := hiΔ.const_mul lam
  rw [integral_sub hneg hlam,integral_neg,bounded_L1_weak_poisson hm hi hM hn hb hφ hc,
    integral_const_mul,compact_laplacian_mass hφ hc,mul_zero,sub_zero]
  have he : (∫ x, 4*Real.pi*ρ x*φ x) = 4*Real.pi*∫ x, ρ x*φ x := by
    simpa only [mul_assoc] using
      (integral_const_mul (4*Real.pi) (fun x : TFSpace => ρ x*φ x))
  rw [he]
  nlinarith

end CoulombBarrier

end Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma weak_poisson_plus_potential_harmonic {u ρ : Space → ℝ} {c : Space} {R M : ℝ}
    (hu : ContinuousOn u (closedBall c R))
    (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c R → (∫ x, u x*Δ g x) = 4*Real.pi*∫ x, ρ x*g x)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball c R) :
    (∫ x, (u x+tfPotential ρ x)*Δ g x) = 0 := by
  have hiu := continuousOn_mul_integrable_support (isCompact_closedBall c R) hu
    (tfLaplacian_continuous hg) (fun x hx => ball_subset_closedBall (hs (tfLaplacian_support hg hx)))
  have hvcont := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  have hiv := continuousOn_mul_integrable_support (isCompact_closedBall c R) hvcont.continuousOn
    (tfLaplacian_continuous hg) (fun x hx => ball_subset_closedBall (hs (tfLaplacian_support hg hx)))
  simp_rw [add_mul]
  rw [integral_add hiu hiv,hw g hg hcg hs,bounded_L1_weak_poisson hm hi hM hn hb hg hcg]
  ring

theorem exists_weak_poisson_L1_constants : ∃ P L : ℝ, 0 ≤ P ∧ 0 ≤ L ∧
    ∀ (u ρ : Space → ℝ) (c : Space) (R M A B : ℝ), 0 < R → 0 ≤ M →
    Measurable ρ → Integrable ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ρ z ≤ M) →
    (∫ z, ρ z) ≤ B → ContinuousOn u (closedBall c (3*R)) →
    (∫ z in closedBall c (3*R), |u z|) ≤ A →
    (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c (3*R) → (∫ z, u z*Δ g z) = 4*Real.pi*∫ z, ρ z*g z) →
    ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
      |u x| ≤ P/R^3*(A+(2*Real.pi*M+B)*(volume (closedBall c (3*R))).toReal)+(2*Real.pi*M+B) ∧
      |u x-u y| ≤ (L/R^4*(A+(2*Real.pi*M+B)*(volume (closedBall c (3*R))).toReal)+4*Real.pi*M+B)*‖x-y‖ := by
  obtain ⟨P,L,hP,hL,h⟩ := exists_weak_harmonic_L1_constants
  refine ⟨P,L,hP,hL,?_⟩
  intro u ρ c R M A B hR hM hm hi hn hb hmass hu hL1 hw x hx y hy
  let V := tfPotential ρ
  let K := closedBall c (3*R)
  let C := 2*Real.pi*M+B
  have hB : 0 ≤ B := (integral_nonneg hn).trans hmass
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hVcont : Continuous V := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  have hVnonneg (z : Space) : 0 ≤ V z := tfPotential_nonneg (ae_of_all _ hn) z
  have hVbound (z : Space) : V z ≤ C :=
    (bounded_L1_potential_le hm hi hM hn hb z).trans (add_le_add le_rfl hmass)
  have hKfin : volume K ≠ ⊤ := (isCompact_closedBall c (3*R)).measure_lt_top.ne
  have hic : IntegrableOn (fun _ : Space => C) K := integrableOn_const hKfin
  have hui : IntegrableOn (fun z => |u z|) K := hu.abs.integrableOn_compact (isCompact_closedBall c (3*R))
  have huV : ContinuousOn (fun z => u z+V z) K := hu.add hVcont.continuousOn
  have hiuV : IntegrableOn (fun z => |u z+V z|) K := huV.abs.integrableOn_compact (isCompact_closedBall c (3*R))
  have hL1' : (∫ z in K, |u z+V z|) ≤ A+C*(volume K).toReal := by
    have hh := integral_mono_ae hiuV (hui.add hic) (ae_of_all _ (fun z => by
      change |u z+V z| ≤ |u z|+C
      exact (abs_add_le _ _).trans (add_le_add le_rfl (by rw [abs_of_nonneg (hVnonneg z)]; exact hVbound z))))
    change (∫ z in K, |u z+V z|) ≤ ∫ z in K, |u z|+C at hh
    rw [integral_add hui hic] at hh
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hh
    calc
      _ ≤ (∫ z in K, |u z|)+(volume K).toReal*C := hh
      _ ≤ A+(volume K).toReal*C := add_le_add hL1 le_rfl
      _ = _ := by ring
  have hhar : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c (3*R) → (∫ z, (u z+V z)*Δ g z) = 0 :=
    fun g hg hcg hs => weak_poisson_plus_potential_harmonic hu hm hi hM hn hb hw hg hcg hs
  have hest := h (fun z => u z+V z) c R hR huV hhar x hx y hy
  have habs : |u x| ≤ |u x+V x|+C := by
    calc
      _ = |(u x+V x)-V x| := by ring_nf
      _ ≤ |u x+V x|+|V x| := abs_sub _ _
      _ ≤ _ := add_le_add le_rfl (by rw [abs_of_nonneg (hVnonneg x)]; exact hVbound x)
  have hdiff : |V x-V y| ≤ (4*Real.pi*M+B)*‖x-y‖ :=
    (bounded_L1_potential_difference hm hi hM hn hb x y).trans
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl hmass) (norm_nonneg _))
  constructor
  · exact habs.trans (add_le_add (hest.1.trans
      (mul_le_mul_of_nonneg_left hL1' (div_nonneg hP (pow_nonneg hR.le 3)))) le_rfl)
  · calc
      _ = |((u x+V x)-(u y+V y))-(V x-V y)| := by ring_nf
      _ ≤ |(u x+V x)-(u y+V y)|+|V x-V y| := abs_sub _ _
      _ ≤ L/R^4*(A+C*(volume K).toReal)*‖x-y‖+(4*Real.pi*M+B)*‖x-y‖ :=
        add_le_add (hest.2.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL1' (div_nonneg hL (pow_nonneg hR.le 4))) (norm_nonneg _))) hdiff
      _ = _ := by dsimp only [C,K]; ring

end CoulombAnalysis

end

end OAI
