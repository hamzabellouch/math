import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoherentDensity
import OAI.Analysis.CoulombIonization.Localization.RadialPacket
import OAI.Analysis.CoulombIonization.RadialBounds.FermiMeasure

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

def smearedPacketDensity (g ρ : Space → ℝ) (x : Space) : ℝ :=
  ∫ z : Space, ρ z * (g (x-z))^2

lemma coherentDensity_fermi {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) (x : Space) :
    2*coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ) x = smearedPacketDensity g ρ x := by
  have hi := fermiMeasure_integrable_continuous hn hJ hs hb
    (show Continuous (fun q : Space × Space => (g (x-q.1))^2) by fun_prop)
  simp only [coherentDensity,coherentPacket_norm,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [← mul_assoc,fermiMeasure_integral hm hi,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_const]
  simp only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ]
  rw [← mul_assoc]
  exact congrArg (fun a : ℝ => a*(g (x-z))^2) (fermiRadius_ball_mass hn z)

lemma smearedPacketDensity_nonneg {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z) (g : Space → ℝ) (x : Space) :
    0 ≤ smearedPacketDensity g ρ x := integral_nonneg (fun z => mul_nonneg (hn z) (sq_nonneg _))

lemma smearedPacketDensity_continuous {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) : Continuous (smearedPacketDensity g ρ) := by
  let := fermiMeasure_finite hn hJ hs hb
  have he : smearedPacketDensity g ρ = fun x => 2*coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ) x :=
    funext (fun x => (coherentDensity_fermi hm hn hJ hs hb hg x).symm)
  rw [he]
  exact continuous_const.mul (coherentDensity_continuous (Complex.continuous_ofReal.comp hg)
    (fermiMeasure ρ) (hJ.prod (isCompact_closedBall _ _)) (fermiMeasure_mem hm hn hs hb))

lemma smearedPacketDensity_compact {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) (hcg : HasCompactSupport g) :
    HasCompactSupport (smearedPacketDensity g ρ) := by
  let := fermiMeasure_finite hn hJ hs hb
  have he : smearedPacketDensity g ρ = fun x => 2*coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ) x :=
    funext (fun x => (coherentDensity_fermi hm hn hJ hs hb hg x).symm)
  rw [he]
  have hcc : HasCompactSupport (fun x => (g x : ℂ)) := hcg.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hd : HasCompactSupport (coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ)) :=
    coherentDensity_compact hcc (fermiMeasure ρ) (hJ.prod (isCompact_closedBall _ _))
      (fermiMeasure_mem hm hn hs hb)
  exact hd.comp_left (g := fun t : ℝ => 2*t) (mul_zero 2)

lemma smearedPacketDensity_mass {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) : (∫ x : Space, smearedPacketDensity g ρ x) = ∫ z, ρ z := by
  let := fermiMeasure_finite hn hJ hs hb
  have he : smearedPacketDensity g ρ = fun x => 2*coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ) x :=
    funext (fun x => (coherentDensity_fermi hm hn hJ hs hb hg x).symm)
  have hgc : Continuous (fun x => (g x : ℂ)) := Complex.continuous_ofReal.comp hg
  have hcc : HasCompactSupport (fun x => (g x : ℂ)) := hcg.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  rw [he,integral_const_mul,coherentDensity_mass hgc hcc (fermiMeasure ρ)
    (hJ.prod (isCompact_closedBall _ _)) (fermiMeasure_mem hm hn hs hb)]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,hgn,mul_one,← mul_assoc]
  exact fermiMeasure_mass hm hn hJ hs hb

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma coulomb_double_eq_potential {f g : Space → ℝ}
    (hi : Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖)) :
    (∫ r : Space × Space, f r.1*g r.2/‖r.1-r.2‖) =
      ∫ x : Space, f x*CoulombAnalysis.tfPotential g x := by
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  simp only [CoulombAnalysis.tfPotential,mul_div_assoc,integral_const_mul]

lemma coulomb_potential_pair_integrable {f g : Space → ℝ}
    (hi : Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖)) :
    Integrable (fun x : Space => f x*CoulombAnalysis.tfPotential g x) := by
  simpa only [CoulombAnalysis.tfPotential,mul_div_assoc,integral_const_mul] using hi.integral_prod_left

lemma coulomb_potential_pair_comm {f g : Space → ℝ}
    (hi : Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖)) :
    (∫ x : Space, f x*CoulombAnalysis.tfPotential g x) =
      ∫ x : Space, g x*CoulombAnalysis.tfPotential f x := by
  simp only [CoulombAnalysis.tfPotential,← integral_const_mul]
  have hi' : Integrable (fun r : Space × Space => f r.1*(g r.2/‖r.1-r.2‖)) (volume.prod volume) := by
    simpa only [mul_div_assoc,Measure.volume_eq_prod] using hi
  rw [integral_integral_swap hi']
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  rw [norm_sub_rev x y]
  ring

lemma coulomb_direct_le_of_potential_le {f g : Space → ℝ}
    (hff : Integrable (fun r : Space × Space => f r.1*f r.2/‖r.1-r.2‖))
    (hfg : Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖))
    (hgg : Integrable (fun r : Space × Space => g r.1*g r.2/‖r.1-r.2‖))
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    (hp : ∀ x, CoulombAnalysis.tfPotential f x ≤ CoulombAnalysis.tfPotential g x) :
    (∫ r : Space × Space, f r.1*f r.2/‖r.1-r.2‖) ≤
      ∫ r : Space × Space, g r.1*g r.2/‖r.1-r.2‖ := by
  have hgf : Integrable (fun r : Space × Space => g r.1*f r.2/‖r.1-r.2‖) := by
    rw [Measure.volume_eq_prod] at hfg ⊢
    apply hfg.swap.congr
    filter_upwards [] with r
    change f r.2*g r.1/‖r.2-r.1‖ = g r.1*f r.2/‖r.1-r.2‖
    rw [norm_sub_rev r.1 r.2]
    ring
  rw [coulomb_double_eq_potential hff,coulomb_double_eq_potential hgg]
  calc
    _ ≤ ∫ x : Space, f x*CoulombAnalysis.tfPotential g x :=
      integral_mono (coulomb_potential_pair_integrable hff) (coulomb_potential_pair_integrable hfg)
        (fun x => mul_le_mul_of_nonneg_left (hp x) (hfn x))
    _ = ∫ x : Space, g x*CoulombAnalysis.tfPotential f x := coulomb_potential_pair_comm hfg
    _ ≤ _ := integral_mono (coulomb_potential_pair_integrable hgf) (coulomb_potential_pair_integrable hgg)
      (fun x => mul_le_mul_of_nonneg_left (hp x) (hgn x))

lemma square_compact {g : Space → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => (g x)^2) := hg.comp_left (g := fun t : ℝ => t^2) (by simp)

lemma smearedPacketDensity_direct_le {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : CoulombAnalysis.IsRadial (fun x => (g x)^2)) :
    (∫ r : Space × Space, smearedPacketDensity g ρ r.1*smearedPacketDensity g ρ r.2/‖r.1-r.2‖) ≤
      ∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖ := by
  have hab (z : Space) : |ρ z| ≤ B := by rw [abs_of_nonneg (hn z)]; exact hb z
  have h1 : Integrable ρ := bounded_compact_integrable hm hJ hs hab
  have hp : MemLp ρ (5/3 : ENNReal) := bounded_compact_memLp hm hJ hs hab _
  have hd := smearedPacketDensity_continuous hm hn hJ hs hb hg
  have hc := smearedPacketDensity_compact hm hn hJ hs hb hg hcg
  apply coulomb_direct_le_of_potential_le
    (continuous_compact_coulomb_integrable hd hd hc hc)
    (compact_support_coulomb_integrable hd.measurable hm (hd.integrable_of_hasCompactSupport hc) h1 hp hJ hs)
    (compact_support_coulomb_integrable hm hm h1 h1 hp hJ hs)
    (smearedPacketDensity_nonneg hn g) hn
  intro x
  exact spatialSmearing_potential_le (hg.pow 2) (square_compact hcg) (fun y => sq_nonneg (g y))
    hr hgn hm h1 hp hn x

end CoulombAtom

end

end OAI
