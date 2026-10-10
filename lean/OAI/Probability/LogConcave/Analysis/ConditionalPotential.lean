import Mathlib
import OAI.Probability.LogConcave.Sampling.TiltedExpectation
import OAI.Probability.LogConcave.JetEstimates.Bound

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory

lemma HasGaussianLowerTail.hasExpMoments {d : ℕ} {H : Point d → ℝ}
    (ht : HasGaussianLowerTail H) (hc : Continuous H) : Appell.HasExpMoments (gibbs H) := by
  have hi := integrable_tilted H hc continuous_const ht (growth_const (1:ℝ)) 0
  simp only [inner_zero_left,zero_sub,smul_eq_mul,mul_one] at hi
  obtain ⟨m,hm,C,ht⟩ := ht
  intro R
  apply integrable_gibbs_of_weighted hc hi
  have hct : Continuous (fun x => Real.exp (-H x)*Real.exp (R*‖x‖)) :=
    hc.neg.rexp.mul ((continuous_const.mul continuous_norm).rexp)
  apply ((integrable_gaussian_envelope d (b := m/2) (by positivity)).const_mul
    (Real.exp (C+R^2/(2*m)))).mono'
    hct.aestronglyMeasurable
  filter_upwards [] with x
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hyp : R*‖x‖ ≤ (m/2)*‖x‖^2+R^2/(2*m) := by
    have hh := sq_nonneg (m*‖x‖-R)
    have hd : R^2/(2*m)*(2*m)=R^2 := by field_simp
    nlinarith
  linarith [ht x]

lemma Primitive.hasExpMoments {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) : Appell.HasExpMoments (gibbs (primitivePotential F x r)) :=
  (hF.hasGaussianLowerTail x hr hl).hasExpMoments (hF.continuous_potential x r)

namespace Appell
lemma HasExpMoments.map_lipschitz {E F : Type} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] {μ : Measure E}
    (hμ : HasExpMoments μ) {S : E → F} {K : ℝ≥0} (hS : LipschitzWith K S) :
    HasExpMoments (μ.map S) := by
  intro R
  apply (integrable_map_measure ((continuous_const.mul continuous_norm).rexp).aestronglyMeasurable
    hS.continuous.aemeasurable).2
  apply ((hμ (|R| *K)).const_mul (Real.exp (|R| *‖S 0‖))).mono'
    ((continuous_const.mul hS.continuous.norm).rexp).aestronglyMeasurable
  filter_upwards [] with x
  change ‖Real.exp (R*‖S x‖)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb : ‖S x‖ ≤ K*‖x‖+‖S 0‖ := by
    have hh := hS.dist_le_mul x 0
    simp only [dist_eq_norm,sub_zero] at hh
    have hh' := norm_add_le (S x-S 0) (S 0)
    rw [sub_add_cancel] at hh'
    linarith
  have ht := mul_le_mul_of_nonneg_left hb (abs_nonneg R)
  have hr := mul_le_mul_of_nonneg_right (le_abs_self R) (norm_nonneg (S x))
  nlinarith
end Appell
end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped ENNReal

theorem gibbs_map_equiv {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    (e : Point d ≃ᵐ Point d) {c : ℝ≥0∞} (hc0 : c≠0) (hct : c≠⊤)
    (he : (volume : Measure (Point d)).map e=c • volume) :
    (gibbs H).map e=gibbs (fun y => H (e.symm y)) := by
  have hm : ((volume : Measure (Point d)).withDensity (gibbsDensity H)).map e =
      c • volume.withDensity (gibbsDensity (fun y => H (e.symm y))) := by
    rw [EulerDensity.map_withDensity_equiv volume e (by unfold gibbsDensity; fun_prop),
      he,withDensity_smul_measure]
    rfl
  have hp : partition H=c*partition (fun y => H (e.symm y)) := by
    have hh := congrArg (fun μ : Measure (Point d) => μ Set.univ) hm
    simpa only [Measure.map_apply e.measurable MeasurableSet.univ,Set.preimage_univ,
      Measure.smul_apply,smul_eq_mul,withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ,partition] using hh
  unfold gibbs
  rw [Measure.map_smul _ e.measurable.aemeasurable,hm,hp,smul_smul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  congr 1
  calc
    (c⁻¹*(partition (fun y => H (e.symm y)))⁻¹)*c =
        (c⁻¹*c)*(partition (fun y => H (e.symm y)))⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 hct,one_mul]

lemma gibbs_map_smul {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    {s : ℝ} (hs : s≠0) :
    (gibbs H).map (fun z => s • z)=gibbs (fun z => H (s⁻¹ • z)) := by
  let e := (Homeomorph.smulOfNeZero (α := Point d) s hs).toMeasurableEquiv
  have he : (volume : Measure (Point d)).map e =
      ENNReal.ofReal |(s^d)⁻¹| • volume := by
    convert! Measure.map_addHaar_smul (volume : Measure (Point d)) hs using 1
    simp [Point]
  have h := gibbs_map_equiv hH e
    (by positivity : ENNReal.ofReal |(s^d)⁻¹| ≠ 0)
    ENNReal.ofReal_ne_top he
  change (gibbs H).map e = _
  rw [h]
  congr 1

lemma gibbs_map_add {d : ℕ} {H : Point d → ℝ} (hH : Continuous H) (v : Point d) :
    (gibbs H).map (fun z => v+z)=gibbs (fun z => H (z-v)) := by
  let e := (Homeomorph.addLeft v).toMeasurableEquiv
  have he : (volume : Measure (Point d)).map e = (1:ℝ≥0∞) • volume := by
    change (volume : Measure (Point d)).map (fun z => v+z) = _
    simpa only [one_smul] using (measurePreserving_add_left (volume : Measure (Point d)) v).map_eq
  change (gibbs H).map e = _
  rw [gibbs_map_equiv hH e (by norm_num) (by norm_num) he]
  congr 1
  funext z
  apply congrArg H
  change -v+z=z-v
  abel

lemma gibbs_map_affine {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    (v : Point d) {s : ℝ} (hs : s≠0) :
    (gibbs H).map (fun z => v+s • z)=gibbs (fun z => H (s⁻¹ • (z-v))) := by
  change (gibbs H).map ((fun z => v+z) ∘ (fun z => s • z)) = _
  rw [← Measure.map_map (show Measurable (fun z : Point d => v+z) by fun_prop)
    (show Measurable (fun z : Point d => s • z) by fun_prop),gibbs_map_smul hH hs]
  exact gibbs_map_add (show Continuous (fun z : Point d => H (s⁻¹ • z)) by fun_prop) v

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped NNReal RealInnerProductSpace

def conditionalPotential {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) : ℝ :=
  ‖z-ρ • y‖^2/(2*(1-ρ^2)) + F (x+r • z)

lemma probability_time {ρ : ℝ} (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    0 < 1-ρ^2 ∧ 1-ρ^2 ≤ 1 := by
  constructor
  · nlinarith
  · nlinarith [sq_nonneg ρ]

lemma conditionalPotential_pullback {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) (ha : 0<1-ρ^2) :
    primitivePotential F (x+r • (ρ • y)) (r*Real.sqrt (1-ρ^2))
      ((Real.sqrt (1-ρ^2))⁻¹ • (z-ρ • y)) = conditionalPotential F x r ρ y z := by
  have hs : Real.sqrt (1-ρ^2) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hv : x+r • (ρ • y)+(r*Real.sqrt (1-ρ^2)) •
      ((Real.sqrt (1-ρ^2))⁻¹ • (z-ρ • y))=x+r • z := by
    rw [← mul_smul r ρ y,smul_smul,mul_assoc,mul_inv_cancel₀ hs,mul_one,smul_sub]
    rw [smul_smul]
    abel
  unfold primitivePotential conditionalPotential
  rw [hv,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,Real.sq_sqrt ha.le]
  congr 1
  field_simp

lemma conditionalLaw_map {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ : ℝ) (y : Point d) (ha : 0<1-ρ^2) :
    (gibbs (primitivePotential F (x+r • (ρ • y)) (r*Real.sqrt (1-ρ^2)))).map
      (fun z => ρ • y+Real.sqrt (1-ρ^2) • z) =
      gibbs (conditionalPotential F x r ρ y) := by
  rw [gibbs_map_affine (hF.continuous_potential _ _)
    _ (Real.sqrt_pos.mpr ha).ne']
  congr 1
  funext z
  exact conditionalPotential_pullback F x r ρ y z ha

lemma conditional_smallness {lam : ℝ≥0} {r ρ : ℝ}
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (ha : 0<1-ρ^2) (ha1 : 1-ρ^2≤1) :
    (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 ≤ 1/2 := by
  rw [mul_pow,Real.sq_sqrt ha.le]
  have hn : 0≤(lam:ℝ)*r^2 := mul_nonneg lam.coe_nonneg (sq_nonneg r)
  calc
    (lam:ℝ)*(r^2*(1-ρ^2))=((lam:ℝ)*r^2)*(1-ρ^2) := by ring
    _ ≤ ((lam:ℝ)*r^2)*1 := mul_le_mul_of_nonneg_left ha1 hn
    _ ≤ 1/2 := by simpa using hl

lemma conditionalLaw_probability {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    IsProbabilityMeasure (gibbs (conditionalPotential F x r ρ y)) := by
  obtain ⟨ha,ha1⟩ := probability_time hρ0 hρ1
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0≤r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  have : IsProbabilityMeasure (gibbs (primitivePotential F (x+r • (ρ • y))
      (r*Real.sqrt (1-ρ^2)))) := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential _ _)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential _ hrad hsmall))
  rw [← conditionalLaw_map hF x r ρ y ha]
  infer_instance

lemma conditionalLaw_hasPoincare {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    HasPoincare (gibbs (conditionalPotential F x r ρ y)) ((Real.pi^2/2)*(1-ρ^2)) := by
  obtain ⟨ha,ha1⟩ := probability_time hρ0 hρ1
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0≤r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  have : IsProbabilityMeasure (gibbs (primitivePotential F (x+r • (ρ • y))
      (r*Real.sqrt (1-ρ^2)))) := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential _ _)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential _ hrad hsmall))
  let K : ℝ≥0 := ⟨Real.sqrt (1-ρ^2),Real.sqrt_nonneg _⟩
  have hK : LipschitzWith K (fun z : Point d => ρ • y+Real.sqrt (1-ρ^2) • z) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    rfl
  have hB : 0≤(Real.pi^2/8)*(2/(1-(lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2)) := by positivity
  have hp := (hF.hasPoincare (x+r • (ρ • y)) hrad hsmall).map hB
    (show ContDiff ℝ 1 (fun z : Point d => ρ • y+Real.sqrt (1-ρ^2) • z) by fun_prop) hK
  rw [conditionalLaw_map hF x r ρ y ha] at hp
  apply hp.mono
  change (Real.pi^2/8)*(2/(1-(lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2)) *
    (Real.sqrt (1-ρ^2))^2 ≤ _
  rw [Real.sq_sqrt ha.le]
  apply mul_le_mul_of_nonneg_right _ ha.le
  have hd : 0<1-(lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 := sub_pos.mpr hsmall
  have hb : 2/(1-(lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2) ≤ 4 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ)≤Real.pi^2/8)]

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
