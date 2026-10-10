import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTowerBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierRetainedComparisonBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric Laplacian InnerProductSpace
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

def addedError (good : Prop) [Decidable good] (R : ℝ) (μ p : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  p x+if good then 0 else if R/2 ≤ ‖x‖ ∧ ‖x‖ < R then μ x else 0

lemma addedError_nonneg (good : Prop) [Decidable good] {R : ℝ} {μ p : TFSpace → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hp : ∀ x, 0 ≤ p x) (x : TFSpace) :
    0 ≤ addedError good R μ p x := by
  unfold addedError
  split_ifs <;> linarith [hμ x,hp x]

lemma addedError_le (good : Prop) [Decidable good] {R M L : ℝ} {μ p : TFSpace → ℝ}
    (hM : 0 ≤ M) (hμ : ∀ x, μ x ≤ M) (hp : ∀ x, p x ≤ L) (x : TFSpace) :
    addedError good R μ p x ≤ L+M := by
  unfold addedError
  split_ifs <;> linarith [hμ x,hp x]

lemma addedError_support (good : Prop) [Decidable good] {R : ℝ} (hR : 0 ≤ R)
    {μ p : TFSpace → ℝ} (hp : ∀ x, R/2 < ‖x‖ → p x = 0) {x : TFSpace} (hx : R < ‖x‖) :
    addedError good R μ p x = 0 := by
  simp only [addedError,hp x (by linarith),not_lt_of_ge hx.le,and_false,ite_false,ite_self,add_zero]

lemma addedError_measurable {Ω : Type*} [MeasurableSpace Ω] (good : Ω → Prop) [DecidablePred good]
    (hg : MeasurableSet {sample | good sample}) {μ p : Ω → TFSpace → ℝ}
    (hμ : Measurable (Function.uncurry μ)) (hp : Measurable (Function.uncurry p)) (R : ℝ) :
    Measurable (fun z : Ω × TFSpace => addedError (good z.1) R (μ z.1) (p z.1) z.2) := by
  exact hp.add (Measurable.ite (measurable_fst hg) measurable_const
    (Measurable.ite ((measurableSet_le measurable_const (continuous_norm.measurable.comp measurable_snd)).inter
      (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const)) hμ measurable_const))

lemma WeakNuclearLowerOn.sub_const {U : Set TFSpace} {Z : ℝ} {u h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (hu : LocallyIntegrable u) (c : ℝ) :
    WeakNuclearLowerOn U Z (fun x => u x-c) h := by
  intro φ hφ hc hs hn
  have he := compact_laplacian_green (f := fun _ : TFSpace => c) contDiff_const hφ hc
  simp only [laplacian_const,Pi.zero_apply,zero_mul,integral_zero] at he
  have hic : Integrable (fun x : TFSpace => c*Δ φ x) :=
    (continuous_const.mul (tfLaplacian_continuous hφ)).integrable_of_hasCompactSupport
      (tfLaplacian_compact hφ hc).mul_left
  simp_rw [sub_mul]
  rw [integral_sub (locallyIntegrable_mul_test hu (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc))
    hic,he,sub_zero]
  exact hw φ hφ hc hs hn

lemma outward_old_source (good : Prop) [Decidable good] {R κ lam1 lam2 e ξ C hl hh : ℝ}
    (hR : 0 < R) (hκ : 0 ≤ κ) (hlam : 0 ≤ lam1) (hξ : 0 ≤ ξ)
    (hgap : 16*ξ+2*e < lam1-lam2) {μ p u H w : TFSpace → ℝ}
    (hinv : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < R →
      InverseComparisonAt ‖x‖ (H x) (μ x) κ hl hh ξ C)
    {x : TFSpace}
    (hheight : R/2 ≤ ‖x‖ → ‖x‖ < R → 0 ≤ u x ∧ ‖x‖^4*u x ∈ Icc hl hh)
    (hcand : good → H x-lam2/R^4 ≤ w x)
    (hnear : w x-(u x-lam1/R^4) < 2*e/R^4) :
    innerSource R μ (addedError good R μ p) x+outerCoefficient R x*reaction κ (u x-lam1/R^4) ≤
      innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (u x) := by
  have hp : ‖x‖ < R/2 → ‖x‖ < R := fun hx => by linarith
  have hreact := reaction_nonneg hκ (u x)
  by_cases hx0 : ‖x‖ < R/2
  · simp [innerSource,outerCoefficient,addedError,hx0,hp hx0,not_le_of_gt hx0,not_le_of_gt (hp hx0),ite_self]
  · have hx0' := le_of_not_gt hx0
    by_cases hx1 : ‖x‖ < R
    · by_cases hg : good
      · obtain ⟨hu,hh'⟩ := hheight hx0' hx1
        have hsrc := retained_old_source hR hx0' hξ hu hh' (hinv hg x hx0' hx1) hgap
          (by linarith [hcand hg])
        simp only [innerSource,outerCoefficient,addedError,ite_eq_left hg,add_zero,ite_eq_left hx1,
          ite_eq_right hx0,ite_eq_left hx0',ite_eq_right (not_le_of_gt hx1),zero_mul,one_mul,zero_sub,add_zero]
        linarith
      · simp only [innerSource,outerCoefficient,addedError,ite_eq_right hg,ite_eq_left (show R/2 ≤ ‖x‖ ∧ ‖x‖ < R from ⟨hx0',hx1⟩),
          ite_eq_left hx1,ite_eq_right hx0,ite_eq_left hx0',ite_eq_right (not_le_of_gt hx1),zero_mul,one_mul,
          zero_sub,add_zero]
        linarith
    · have hm := reaction_monotone hκ (show u x-lam1/R^4 ≤ u x by
        have hpos : 0 ≤ lam1/R^4 := by positivity
        linarith)
      simp only [innerSource,outerCoefficient,addedError,ite_eq_right hx1,ite_eq_right hx0,ite_eq_left hx0',
        ite_eq_left (le_of_not_gt hx1),ite_eq_right (show ¬(R/2 ≤ ‖x‖ ∧ ‖x‖ < R) from fun h => hx1 h.2),
        ite_self,add_zero,zero_sub,one_mul]
      linarith

lemma outward_field_source (good : Prop) [Decidable good] {R κ lam2 ξ C hl hh : ℝ}
    (hR : 0 < R) (hξ : 0 ≤ ξ) (hshift : ξ < lam2) {μ p H : TFSpace → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hμ : ∀ x, 0 ≤ μ x) {x : TFSpace}
    (hinv : R ≤ ‖x‖ → InverseComparisonAt ‖x‖ (H x) (μ x) κ hl hh ξ C)
    (hheight : R ≤ ‖x‖ → 0 ≤ H x-lam2/R^4 ∧ ‖x‖^4*(H x-lam2/R^4) ∈ Icc hl hh) :
    innerSource R μ (addedError good R μ p) x+outerCoefficient R x*reaction κ (H x-lam2/R^4) ≤
      4*Real.pi*μ x := by
  have hp' := addedError_nonneg (R := R) good hμ hp x
  have hπ : 0 < 4*Real.pi := by positivity
  by_cases hx : ‖x‖ < R
  · simp only [innerSource,outerCoefficient,ite_eq_left hx,ite_eq_right (not_le_of_gt hx),zero_mul,add_zero]
    nlinarith
  · have hx' := le_of_not_gt hx
    obtain ⟨hv,hh'⟩ := hheight hx'
    have hm := retained_field_source hR hx' hξ hshift hv hh' (hinv hx')
    simp only [innerSource,outerCoefficient,ite_eq_right hx,ite_eq_left hx',one_mul,zero_sub]
    nlinarith

lemma retained_field_height {B C R M e hl hh H v w d lam : ℝ}
    (hB : 0 < B) (hR : 0 < R) (he : 0 < e)
    (hd : R ≤ d) (hd' : d ≤ 2*M*R) (hhl : hl < B/4) (hhh : C < hh)
    (hsmall : 2*e*(2*M)^4 < B/4) (hlam : 0 ≤ lam)
    (hv : v = H-lam/R^4) (hlo : (7*B/8)/d^4 ≤ w)
    (hhi : d^4*H ≤ C) (hnear : w-v < 2*e/R^4) :
    0 ≤ v ∧ d^4*v ∈ Icc hl hh := by
  have hd0 := hR.trans_le hd
  have hd4 : 0 < d^4 := pow_pos hd0 4
  have hR4 : 0 < R^4 := pow_pos hR 4
  have hlo' : 7*B/8 ≤ d^4*w := by
    have h := (div_le_iff₀ hd4).mp hlo
    nlinarith
  have hnear' := mul_lt_mul_of_pos_left hnear hd4
  have hpower := pow_le_pow_left₀ hd0.le hd' 4
  rw [mul_pow] at hpower
  have hratio : d^4/R^4 ≤ (2*M)^4 := (div_le_iff₀ hR4).mpr hpower
  have hscale := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2*e)
  have hbound : hl < d^4*v := by
    have heq : d^4*(2*e/R^4) = 2*e*(d^4/R^4) := by ring
    rw [heq] at hnear'
    nlinarith
  have hvpos : 0 < v := by
    by_contra hn
    have hvn := le_of_not_gt hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hd4.le hvn
    have heq : d^4*(2*e/R^4) = 2*e*(d^4/R^4) := by ring
    rw [heq] at hnear'
    nlinarith
  refine ⟨hvpos.le,hbound.le,?_⟩
  have hsub : 0 ≤ d^4*(lam/R^4) := by positivity
  rw [hv]
  nlinarith

end CoulombBarrier

end

end OAI
