import Mathlib
import OAI.Probability.LogConcave.Sampling.ConditionalFieldMean

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
open scoped RealInnerProductSpace

lemma integral_gibbs_vector {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Point d → ℝ} (hc : Continuous H) (hi : Integrable (fun z => Real.exp (-H z)))
    (h : Point d → E) : (∫ z,h z ∂gibbs H) = (∫ z,Real.exp (-H z))⁻¹ •
      ∫ z,Real.exp (-H z) • h z := by
  rw [gibbs,integral_smul_measure,ENNReal.toReal_inv,partition_toReal hi]
  have hden : Measurable (gibbsDensity H) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hden
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) h]
  simp only [gibbsDensity,ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma integral_gibbs_add_const_vector {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Point d → ℝ} (hc : Continuous H) (hi : Integrable (fun z => Real.exp (-H z)))
    (c : ℝ) (h : Point d → E) :
    (∫ z,h z ∂gibbs (fun z => H z+c))=∫ z,h z ∂gibbs H := by
  have he : (fun z => Real.exp (-(H z+c)))=fun z => Real.exp (-c)*Real.exp (-H z) := by
    funext z; rw [←Real.exp_add]; congr 1; ring
  have hi' : Integrable (fun z => Real.exp (-(H z+c))) := by rw [he]; exact hi.const_mul _
  rw [integral_gibbs_vector (hc.add_const c) hi',integral_gibbs_vector hc hi]
  simp_rw [congrFun he,mul_smul]
  rw [integral_const_mul,integral_smul,mul_inv_rev,smul_smul]
  simp only [mul_assoc,inv_mul_cancel₀ (Real.exp_pos (-c)).ne',mul_one]

def quadraticExpectation {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Point d → ℝ) (h : Point d → E) (p : Point d × ℝ) : E :=
  (quadraticTilt H (fun _ => (1:ℝ)) p)⁻¹ • quadraticTilt H h p

lemma quadratic_partition_pos {d : ℕ} {H : Point d → ℝ} (hc : Continuous H)
    {m C : ℝ} (ht : ∀ z,m*‖z‖^2 ≤ H z+C) (p : Point d × ℝ) (hp : 0 < m+p.2) :
    0 < quadraticTilt H (fun _ => (1:ℝ)) p := by
  simp only [quadraticTilt,smul_eq_mul,mul_one]
  apply integral_exp_pos
  simpa only [smul_eq_mul,mul_one] using
    integrable_quadraticTilt hc continuous_const ht (growth_const (1:ℝ)) p hp

lemma contDiffAt_quadraticExpectation {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Point d → ℝ} {h : Point d → E} (hc : Continuous H) (hh : Continuous h)
    {m C : ℝ} (ht : ∀ z,m*‖z‖^2 ≤ H z+C) (hg : HasPolynomialGrowth h)
    (p : Point d × ℝ) (hp : 0 < m+p.2) :
    ContDiffAt ℝ (⊤:ℕ∞) (quadraticExpectation H h) p :=
  ((contDiffAt_quadraticTilt hc continuous_const ht (growth_const (1:ℝ)) p hp).inv
    (quadratic_partition_pos hc ht p hp).ne').smul
    (contDiffAt_quadraticTilt hc hh ht hg p hp)

def conditionalParameter {d : ℕ} (p : ℝ × Point d) : Point d × ℝ :=
  ((p.1/(1-p.1^2)) • p.2,p.1^2/(2*(1-p.1^2)))

lemma conditionalPotential_quadratic {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r ρ : ℝ) (y z : Point d) (hρ : ρ^2≠1) :
    conditionalPotential F x r ρ y z=
      (primitivePotential F x r z+(conditionalParameter (ρ,y)).2*‖z‖^2-
        inner ℝ (conditionalParameter (ρ,y)).1 z)+
          (ρ^2/(2*(1-ρ^2)))*‖y‖^2 := by
  have ha : 1-ρ^2≠0 := sub_ne_zero.mpr (Ne.symm hρ)
  simp only [conditionalPotential,conditionalParameter,primitivePotential,norm_sub_sq_real,
    inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    inner_smul_left,starRingEnd_apply,star_trivial]
  rw [real_inner_comm y z]
  field_simp
  ring

lemma conditional_integral_quadratic {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) (hρ : ρ^2 < 1) (y : Point d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Point d → E) :
    (∫ z,h z ∂gibbs (conditionalPotential F x r ρ y))=
      quadraticExpectation (primitivePotential F x r) h (conditionalParameter (ρ,y)) := by
  let H := primitivePotential F x r
  let p := conditionalParameter (ρ,y)
  have hc : Continuous H := (hF.continuous_potential x r)
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  have hp : 0 < m+p.2 := by dsimp [p,conditionalParameter]; positivity
  let G : Point d → ℝ := fun z => H z+p.2*‖z‖^2-inner ℝ p.1 z
  have hGc : Continuous G := by dsimp [G]; fun_prop
  have he : ∀ z,Real.exp (-G z)=Real.exp (inner ℝ p.1 z-p.2*‖z‖^2-H z) := by
    intro z; congr 1; dsimp [G]; ring
  have hGi : Integrable (fun z => Real.exp (-G z)) := by
    simp_rw [he]
    simpa only [smul_eq_mul,mul_one] using
      integrable_quadraticTilt hc continuous_const ht (growth_const (1:ℝ)) p hp
  have hpot : conditionalPotential F x r ρ y=fun z => G z+(ρ^2/(2*(1-ρ^2)))*‖y‖^2 :=
    funext fun z => conditionalPotential_quadratic F x r ρ y z hρ.ne
  rw [hpot,integral_gibbs_add_const_vector hGc hGi,integral_gibbs_vector hGc hGi]
  simp only [quadraticExpectation,quadraticTilt,smul_eq_mul,mul_one,he]
  rfl

lemma conditionalParameter_smooth {d : ℕ} {p : ℝ × Point d} (hp : p.1^2 < 1) :
    ContDiffAt ℝ (⊤:ℕ∞) (conditionalParameter (d:=d)) p := by
  have ha : 1-p.1^2≠0 := by linarith
  have hdiv : ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => q.1/(1-q.1^2)) p :=
    contDiffAt_fst.div (contDiffAt_const.sub (contDiffAt_fst.pow 2)) ha
  have hdiv' : ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => q.1^2/(2*(1-q.1^2))) p :=
    (contDiffAt_fst.pow 2).div (contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_fst.pow 2)))
      (mul_ne_zero (by norm_num) ha)
  exact (hdiv.smul contDiffAt_snd).prodMk hdiv'

theorem conditionalFieldMean_joint_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) (p : ℝ × Point d) (hp : p.1^2 < 1) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun q : ℝ × Point d => conditionalFieldMean F x r q.1 q.2) p := by
  obtain ⟨m,hm,C,ht⟩ := hF.hasGaussianLowerTail x hr hl
  have hp' : 0 < m+(conditionalParameter p).2 := by dsimp [conditionalParameter]; positivity
  have hh := (contDiffAt_quadraticExpectation (hF.continuous_potential x r)
    (primitiveField_contDiff hF x r).continuous ht (growth_of_lipschitz (primitiveField_lipschitz hF x hr))
    (conditionalParameter p) hp').comp p (conditionalParameter_smooth hp)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt (continuous_fst.pow 2) continuous_const).mem_nhds hp] with q hq
  exact conditional_integral_quadratic hF x hr hl hq q.2 (primitiveField F x r)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
