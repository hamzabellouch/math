import OAI.MathematicalPhysics.CriticalSK.CubeRestriction
import OAI.MathematicalPhysics.CriticalSK.SaddleLimit

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK



section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exp_midpoint_bound (A B : ℝ) : Real.exp ((A+B)/2) ≤ (Real.exp A+Real.exp B)/2 := by
  have he : Real.exp ((A+B)/2)*Real.cosh ((A-B)/2) = (Real.exp A+Real.exp B)/2 := by
    rw [Real.cosh_eq, ← mul_div_assoc, mul_add, ← Real.exp_add, ← Real.exp_add]
    rw [show (A+B)/2+(A-B)/2=A by ring,
      show (A+B)/2+-((A-B)/2)=B by ring]
  rw [← he]
  exact le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_cosh _)

def correlatedVector (u v : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
  t • u + Real.sqrt (1-t^2) • v

omit [DecidableEq ι] in
lemma correlatedVector_gram {u v : EuclideanSpace ℝ ι} {r t : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) (ht : |t| ≤ 1) :
    ‖correlatedVector u v t‖ = r ∧ inner ℝ u (correlatedVector u v t) = t*r^2 := by
  have ht2 : t^2 ≤ 1 := by nlinarith [(abs_le.mp ht).1,(abs_le.mp ht).2]
  have hs := Real.sq_sqrt (sub_nonneg.mpr ht2)
  have horth' : inner ℝ v u = 0 := by rw [real_inner_comm,horth]
  have huu : inner ℝ u u = r^2 := by rw [real_inner_self_eq_norm_sq,hu]
  have hvv : inner ℝ v v = r^2 := by rw [real_inner_self_eq_norm_sq,hv]
  have hr : 0 ≤ r := hu ▸ norm_nonneg u
  constructor
  · apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
    rw [← real_inner_self_eq_norm_sq]
    simp only [correlatedVector,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right,horth,horth',huu,hvv]
    nlinarith
  · simp only [correlatedVector,inner_add_right,real_inner_smul_right,horth,huu,mul_zero,add_zero]

omit [DecidableEq ι] in
lemma correlatedEnergy_sign (lam : ι → ℝ) (u v : EuclideanSpace ℝ ι) (t : ℝ) :
    diagonalEnergy lam (correlatedVector u v t)+diagonalEnergy lam (correlatedVector u (-v) t) =
      2*(t^2*diagonalEnergy lam u+(Real.sqrt (1-t^2))^2*diagonalEnergy lam v) := by
  simp only [diagonalEnergy,correlatedVector,PiLp.add_apply,PiLp.smul_apply,PiLp.neg_apply,smul_eq_mul]
  simp_rw [Finset.mul_sum,← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma correlatedMoment_sign (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι}
    (horth : inner ℝ u v = 0) (q t : ℝ) :
    pairMoment lam u (correlatedVector u (-v) t) q = pairMoment lam u (correlatedVector u v t) q := by
  have he := orthogonal_pair_integral_eq
    (fun x y => Real.exp (((1+q)*diagonalEnergy lam x+(1-q)*diagonalEnergy lam (correlatedVector x y t))/2))
    (x := u) (y := -v) (x' := u) (y' := v) rfl (norm_neg v)
    (by rw [inner_neg_right,horth,neg_zero])
  simpa only [pairMoment,pairIntegrand,correlatedVector,map_add,map_smul,map_neg] using he

lemma pairMoment_correlated_lower (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι}
    (hnorm : ‖u‖ = ‖v‖) (horth : inner ℝ u v = 0) {q t : ℝ}
    (hq : q ∈ Set.Icc 0 1) (ht : |t| ≤ 1) :
    pairMoment lam u v q ≤ pairMoment lam u (correlatedVector u v t) q := by
  let p := q+(1-q)*t^2
  have hpq : |q| ≤ |p| := (le_abs_self p).trans' (by
    rw [abs_of_nonneg hq.1]
    dsimp [p]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq.2) (sq_nonneg t)])
  apply (pairMoment_mono_abs lam hnorm hpq).trans
  have ht2 : t^2 ≤ 1 := by nlinarith [(abs_le.mp ht).1,(abs_le.mp ht).2]
  have hs := Real.sq_sqrt (sub_nonneg.mpr ht2)
  have hpt (U : Matrix.orthogonalGroup ι ℝ) : pairIntegrand lam u v p U ≤
      (pairIntegrand lam u (correlatedVector u v t) q U+
        pairIntegrand lam u (correlatedVector u (-v) t) q U)/2 := by
    have hE := correlatedEnergy_sign lam (orthogonalIsometry U u) (orthogonalIsometry U v) t
    have hmid := exp_midpoint_bound
      (((1+q)*diagonalEnergy lam (orthogonalIsometry U u)+(1-q)*diagonalEnergy lam (correlatedVector (orthogonalIsometry U u) (orthogonalIsometry U v) t))/2)
      (((1+q)*diagonalEnergy lam (orthogonalIsometry U u)+(1-q)*diagonalEnergy lam (correlatedVector (orthogonalIsometry U u) (-(orthogonalIsometry U v)) t))/2)
    convert! hmid using 1
    · unfold pairIntegrand
      congr 1
      dsimp [p]
      rw [hs] at hE
      linear_combination -(1-q)/4*hE
    · simp only [pairIntegrand,correlatedVector,map_add,map_smul,map_neg]
  have hi := integral_mono (orthogonalHaar_integrable (pairIntegrand_continuous lam u v p))
    (((orthogonalHaar_integrable (pairIntegrand_continuous lam u (correlatedVector u v t) q)).add
      (orthogonalHaar_integrable (pairIntegrand_continuous lam u (correlatedVector u (-v) t) q))).div_const 2) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_div,integral_add
    (orthogonalHaar_integrable (pairIntegrand_continuous lam u (correlatedVector u v t) q))
    (orthogonalHaar_integrable (pairIntegrand_continuous lam u (correlatedVector u (-v) t) q))] at hi
  change pairMoment lam u v p ≤ (pairMoment lam u (correlatedVector u v t) q+
    pairMoment lam u (correlatedVector u (-v) t) q)/2 at hi
  rw [correlatedMoment_sign lam horth] at hi
  linarith

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pairMoment_min_at_orthogonal (lam : ι → ℝ) {u v x y : EuclideanSpace ℝ ι} {r t q : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0)
    (hx : ‖x‖ = r) (hy : ‖y‖ = r) (ht : |t| ≤ 1)
    (hxy : inner ℝ x y = t*r^2) (hq : q ∈ Set.Icc 0 1) :
    pairMoment lam u v q ≤ pairMoment lam x y q := by
  have hg := correlatedVector_gram hu hv horth ht
  have he := orthogonal_pair_integral_eq
    (fun x y => Real.exp (((1+q)*diagonalEnergy lam x+(1-q)*diagonalEnergy lam y)/2))
    (x := u) (y := correlatedVector u v t) (x' := x) (y' := y)
    (hu.trans hx.symm) (hg.1.trans hy.symm) (hg.2.trans hxy.symm)
  change pairMoment lam u (correlatedVector u v t) q = pairMoment lam x y q at he
  exact (pairMoment_correlated_lower lam (hu.trans hv.symm) horth hq ht).trans_eq he

variable [Nonempty ι]

def sphereWeightedPair (lam : ι → ℝ) (r q : ℝ) (p : unitSphere ι × unitSphere ι) : ℝ :=
  Real.exp (((1+q)*diagonalEnergy lam (r • p.1.val)+(1-q)*diagonalEnergy lam (r • p.2.val))/2)

omit [DecidableEq ι] [Nonempty ι] in
lemma sphereWeightedPair_factor (lam : ι → ℝ) (r q : ℝ) (p : unitSphere ι × unitSphere ι) :
    sphereWeightedPair lam r q p =
      Real.exp ((1+q)/2*diagonalEnergy lam (r • p.1.val))*
        Real.exp ((1-q)/2*diagonalEnergy lam (r • p.2.val)) := by
  rw [← Real.exp_add]
  unfold sphereWeightedPair
  congr 1
  ring

omit [DecidableEq ι] [Nonempty ι] in
lemma sphereWeightedPair_continuous (lam : ι → ℝ) (r q : ℝ) : Continuous (sphereWeightedPair lam r q) := by
  change Continuous (fun p => sphereWeightedPair lam r q p)
  simp_rw [sphereWeightedPair_factor]
  exact ((sphere_energy_continuous lam (1+q) r).comp continuous_fst).mul
    ((sphere_energy_continuous lam (1-q) r).comp continuous_snd)

omit [DecidableEq ι] in
lemma sphereWeightedPair_integral (lam : ι → ℝ) (r q : ℝ) :
    (∫ p, sphereWeightedPair lam r q p ∂(sphereUniform.prod sphereUniform)) =
      spherePartition lam (1+q) r * spherePartition lam (1-q) r := by
  simp_rw [sphereWeightedPair_factor]
  rw [integral_prod_mul (fun u : unitSphere ι => Real.exp ((1+q)/2*diagonalEnergy lam (r • u.val)))
    (fun v : unitSphere ι => Real.exp ((1-q)/2*diagonalEnergy lam (r • v.val))),
    sphereUniform_integral,sphereUniform_integral]
  rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma continuous_product_swap {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {f : α × β → γ} (hf : Continuous f) :
    Continuous (fun z : β × α => f (z.2,z.1)) := hf.comp continuous_swap

omit [Nonempty ι] in
lemma spherePair_haar_continuous (f : unitSphere ι × unitSphere ι → ℝ) (hf : Continuous f) :
    Continuous (fun p : unitSphere ι × unitSphere ι =>
      ∫ U, f (orthogonalSphere U p.1,orthogonalSphere U p.2) ∂orthogonalHaar ι) := by
  have hc0 : Continuous (fun z : Matrix.orthogonalGroup ι ℝ × (unitSphere ι × unitSphere ι) =>
      f (orthogonalSphere z.1 z.2.1,orthogonalSphere z.1 z.2.2)) :=
    hf.comp spherePair_action_continuous
  have hc := continuous_product_swap hc0
  simpa only [setIntegral_univ] using
    continuous_parametric_integral_of_continuous (μ := orthogonalHaar ι)
      (f := fun (p : unitSphere ι × unitSphere ι) U => f (orthogonalSphere U p.1,orthogonalSphere U p.2)) hc (s := Set.univ) isCompact_univ

lemma pairMoment_le_partition_product (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r q : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) (hq : q ∈ Set.Icc 0 1) :
    pairMoment lam u v q ≤ spherePartition lam (1+q) r * spherePartition lam (1-q) r := by
  have hr : 0 ≤ r := hu ▸ norm_nonneg u
  have hnorm (x : unitSphere ι) : ‖r • x.val‖ = r := by
    rw [norm_smul,Real.norm_of_nonneg hr,mem_sphere_zero_iff_norm.mp x.property,mul_one]
  have hle (p : unitSphere ι × unitSphere ι) : pairMoment lam u v q ≤
      ∫ U, sphereWeightedPair lam r q (orthogonalSphere U p.1,orthogonalSphere U p.2) ∂orthogonalHaar ι := by
    have hxy : inner ℝ (r • p.1.val) (r • p.2.val) = inner ℝ p.1.val p.2.val*r^2 := by
      rw [real_inner_smul_left,real_inner_smul_right]
      ring
    have hh := pairMoment_min_at_orthogonal lam hu hv horth (hnorm p.1) (hnorm p.2)
      (sphere_inner_abs_le_one p.1 p.2) hxy hq
    simpa only [pairMoment,pairIntegrand,sphereWeightedPair,orthogonalSphere,sphereMap,map_smul] using hh
  have hc := spherePair_haar_continuous _ (sphereWeightedPair_continuous lam r q)
  have hi : Integrable (fun p : unitSphere ι × unitSphere ι =>
      ∫ U, sphereWeightedPair lam r q (orthogonalSphere U p.1,orthogonalSphere U p.2) ∂orthogonalHaar ι)
      (sphereUniform.prod sphereUniform) := by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  have hh := integral_mono (integrable_const (pairMoment lam u v q)) hi hle
  rw [integral_const,probReal_univ,one_smul,spherePair_haar_average _
    (sphereWeightedPair_continuous lam r q),sphereWeightedPair_integral] at hh
  exact hh

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma sphericalVariational_deriv_integrable (lam : ι → ℝ) {a b C : ℝ}
    (hlam : ∀ i, |lam i| ≤ C) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (deriv (sphericalVariational lam)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  apply ((continuousOn_const.integrableOn_Icc (μ := volume) (a := a) (b := b) (f := fun _ : ℝ => C/2)).mono_set Ioo_subset_Icc_self).mono'
    (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 : 0 < x := ha.trans_lt hx.1
  rw [norm_eq_abs,(sphericalVariational_hasDerivAt lam hx0).deriv]
  exact sphericalVariational_slope_bound lam hx0 hlam

lemma saddleSubcriticalError_bound (lam : ι → ℝ) {C a : ℝ} (hlam : ∀ i, |lam i| ≤ C)
    (ha : a ∈ Set.Icc 0 1) :
    |sphericalVariational lam 1-sphericalVariational lam a-(1-a^2)/4| ≤ saddleSubcriticalError lam := by
  have hpoly : IntervalIntegrable (fun x : ℝ => x/2) volume 0 1 :=
    (continuous_id.div_const 2).intervalIntegrable _ _
  have hint := (sphericalVariational_deriv_integrable lam hlam (le_refl 0) (by norm_num : (0:ℝ) ≤ 1)).sub hpoly
  have hint' := hint.mono_set (show uIcc a 1 ⊆ uIcc (0:ℝ) 1 by
    rw [uIcc_of_le ha.2,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc ha.1 (le_refl 1))
  have hc : ContinuousOn (fun x => sphericalVariational lam x-x^2/4) (Set.Icc a 1) :=
    ((sphericalVariational_continuousOn lam).mono (fun _ hx => ha.1.trans hx.1)).sub
      ((continuous_id.pow 2).div_const 4).continuousOn
  have hd (x : ℝ) (hx : x ∈ Ioo a 1) :
      HasDerivAt (fun x => sphericalVariational lam x-x^2/4)
        (deriv (sphericalVariational lam) x-x/2) x := by
    have hh := sphericalVariational_hasDerivAt lam (ha.1.trans_lt hx.1)
    convert! hh.sub (((hasDerivAt_id x).pow 2).div_const 4) using 1
    rw [hh.deriv]
    simp only [id_eq]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.2 hc hd hint'
  have hmono := intervalIntegral.integral_mono_interval ha.1 ha.2 (le_refl (1:ℝ))
    (Eventually.of_forall (fun x => abs_nonneg (deriv (sphericalVariational lam) x-x/2))) hint.abs
  have hh := (intervalIntegral.abs_integral_le_integral_abs (f := fun x => deriv (sphericalVariational lam) x-x/2) ha.2).trans hmono
  rw [hFTC] at hh
  convert hh using 1 <;> try rfl
  congr 1
  ring

lemma sphericalVariational_supercritical_bound (lam : ι → ℝ) {s₀ q : ℝ}
    (hedge : spectralTop lam < 2+s₀) (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hq : q ∈ Set.Icc 0 1) :
    sphericalVariational lam (1+q)-sphericalVariational lam 1 ≤ q/2+q^2/4-q^3/12+s₀*q/2 := by
  let g : ℝ → ℝ := fun u => u/2+u^2/4-u^3/12+s₀*u/2
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hdg (u : ℝ) : HasDerivAt g ((1+u)/2-u^2/4+s₀/2) u := by
    convert! ((((hasDerivAt_id u).div_const 2).add (((hasDerivAt_id u).pow 2).div_const 4)).sub
      (((hasDerivAt_id u).pow 3).div_const 12)).add (((hasDerivAt_id u).const_mul s₀).div_const 2) using 1
    simp only [id_eq]
    ring
  have hB (u : ℝ) (hu : 0 ≤ u) : HasDerivAt (fun u => sphericalVariational lam (1+u))
      ((saddleRadius lam (1+u)-(1+u)⁻¹)/2) u := by
    simpa only [zero_add,mul_one,Function.comp_def] using
      (sphericalVariational_hasDerivAt lam (show 0 < 1+u by linarith)).comp u
        ((hasDerivAt_const u 1).add (hasDerivAt_id u))
  have hdBound (u : ℝ) (hu : u ∈ Ioo 0 q) :
      (saddleRadius lam (1+u)-(1+u)⁻¹)/2 ≤ (1+u)/2-u^2/4+s₀/2 := by
    have hP : 0 < 1+u := by linarith [hu.1]
    have hp := (saddleRadius_le_iff lam hP hedge).mpr (show spectralStieltjes lam (2+s₀) ≤ 1+u by linarith [hu.1])
    have he : (2+s₀-(1+u)⁻¹)/2 = (1+u)/2-u^2/(2*(1+u))+s₀/2 := by field_simp; ring
    have hc : u^2/4 ≤ u^2/(2*(1+u)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 1-u by linarith [hu.2,hq.2])]
    linarith
  have hc : ContinuousOn (fun u => sphericalVariational lam (1+u)-g u) (Set.Icc 0 q) := by
    apply ContinuousOn.sub _ hg.continuousOn
    exact (sphericalVariational_continuousOn lam).comp (continuous_const.add continuous_id).continuousOn
      (fun u hu => show 0 ≤ 1+u by linarith [hu.1])
  have hd (u : ℝ) (hu : u ∈ Ioo 0 q) :
      HasDerivAt (fun u => sphericalVariational lam (1+u)-g u)
        ((saddleRadius lam (1+u)-(1+u)⁻¹)/2-((1+u)/2-u^2/4+s₀/2)) u :=
    (hB u hu.1.le).sub (hdg u)
  have hmono := antitoneOn_of_deriv_nonpos (convex_Icc 0 q) hc
    (fun u hu => (hd u (by rwa [interior_Icc] at hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [interior_Icc] at hu
      rw [(hd u hu).deriv]
      linarith [hdBound u hu])
  have hh := hmono (show (0:ℝ) ∈ Set.Icc 0 q from ⟨le_refl 0,hq.1⟩) (show q ∈ Set.Icc 0 q from ⟨hq.1,le_refl q⟩) hq.1
  dsimp [g] at hh
  simp only [add_zero,zero_div,zero_pow (by omega : 2 ≠ 0),zero_pow (by omega : 3 ≠ 0),mul_zero,sub_zero] at hh
  linarith

lemma saddlePairDeficit_macro_bound (lam : ι → ℝ) {s₀ q C : ℝ}
    (hlam : ∀ i, |lam i| ≤ C) (hs₀ : 0 ≤ s₀)
    (hedge : spectralTop lam < 2+s₀) (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hq : q ∈ Set.Icc 0 1) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/12+saddleSubcriticalError lam+s₀/2 := by
  have hsub := (abs_le.mp (saddleSubcriticalError_bound lam hlam (show 1-q ∈ Set.Icc (0:ℝ) 1 by constructor <;> linarith [hq.1,hq.2]))).1
  have hsup := sphericalVariational_supercritical_bound lam hedge hres₀ hq
  unfold saddlePairDeficit
  nlinarith [mul_le_mul_of_nonneg_left hq.2 hs₀]

lemma saddlePairDeficit_macro_cubic (lam : ι → ℝ) {s₀ q C : ℝ}
    (hlam : ∀ i, |lam i| ≤ C) (hs₀ : 0 ≤ s₀)
    (hedge : spectralTop lam < 2+s₀) (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hq : q ∈ Set.Icc (1/4) 1) (herr : saddleSubcriticalError lam+s₀/2 ≤ 1/1536) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/24 := by
  have hh := saddlePairDeficit_macro_bound lam hlam hs₀ hedge hres₀ (show q ∈ Set.Icc (0:ℝ) 1 by constructor <;> linarith [hq.1,hq.2])
  have hq3 : (1:ℝ)/64 ≤ q^3 := by
    calc (1:ℝ)/64 = (1/4)^3 := by norm_num
         _ ≤ q^3 := pow_le_pow_left₀ (by norm_num) hq.1 3
  nlinarith

end

section

open Set

variable {n : ℕ}

lemma pairMoment_abs (lam : Fin (n+2) → ℝ) {u v : EuclideanSpace ℝ (Fin (n+2))}
    (h : ‖u‖ = ‖v‖) (q : ℝ) : pairMoment lam u v q = pairMoment lam u v |q| := by
  rcases le_or_gt 0 q with hp | hp
  · rw [abs_of_nonneg hp]
  · rw [abs_of_neg hp,pairMoment_even lam h]

lemma pairMoment_variational_upper (lam : Fin (n+2) → ℝ)
    {u v : EuclideanSpace ℝ (Fin (n+2))} (hu : ‖u‖ = Real.sqrt (n+2))
    (hv : ‖v‖ = Real.sqrt (n+2)) (horth : inner ℝ u v = 0)
    (hlam : ∀ i, |lam i| ≤ 3) {q K : ℝ} (hq : |q| ≤ 1) (hK : 0 < K)
    (hlo : K*Real.exp ((n+2)*sphericalVariational lam 1) ≤
      spherePartition lam 1 (Real.sqrt (n+2))) :
    pairMoment lam u v q / spherePartition lam 1 (Real.sqrt (n+2))^2 ≤
      (26*Real.exp 1*(n+2)/K)^2 * Real.exp ((n+2)*saddlePairDeficit lam |q|) := by
  let S := spherePartition lam 1 (Real.sqrt (n+2))
  let A := 26*Real.exp 1*((n:ℝ)+2)
  have hS : 0 < S := spherePartition_pos _ _ _
  have hm := pairMoment_le_partition_product lam hu hv horth (show |q| ∈ Set.Icc (0:ℝ) 1 from ⟨abs_nonneg _,hq⟩)
  rw [← pairMoment_abs lam (hu.trans hv.symm) q] at hm
  have hup := spherePartition_upper n lam (show 1+|q| ∈ Set.Icc (0:ℝ) 2 by constructor <;> linarith [abs_nonneg q]) hlam
  have hdown := spherePartition_upper n lam (show 1-|q| ∈ Set.Icc (0:ℝ) 2 by constructor <;> linarith [abs_nonneg q]) hlam
  have hprod := mul_le_mul hup hdown (spherePartition_pos lam (1-|q|) (Real.sqrt (n+2))).le (by positivity)
  have hupper : pairMoment lam u v q ≤ A^2 * Real.exp (((n:ℝ)+2)*
      (sphericalVariational lam (1+|q|)+sphericalVariational lam (1-|q|))) := by
    calc
      _ ≤ _ := hm.trans hprod
      _ = A^2 * Real.exp (((n:ℝ)+2)*(sphericalVariational lam (1+|q|)+sphericalVariational lam (1-|q|))) := by
        rw [mul_add (((n:ℝ)+2)) (sphericalVariational lam (1+|q|)) (sphericalVariational lam (1-|q|)),Real.exp_add]
        dsimp only [A]
        ring
  have hlower : (K*Real.exp (((n:ℝ)+2)*sphericalVariational lam 1))^2 ≤ S^2 :=
    pow_le_pow_left₀ (by positivity) hlo 2
  have hpos : 0 < (K*Real.exp (((n:ℝ)+2)*sphericalVariational lam 1))^2 := by positivity
  calc
    pairMoment lam u v q / S^2 ≤
        (A^2 * Real.exp (((n:ℝ)+2)*(sphericalVariational lam (1+|q|)+sphericalVariational lam (1-|q|)))) /
          (K*Real.exp (((n:ℝ)+2)*sphericalVariational lam 1))^2 :=
      div_le_div₀ (by positivity) hupper hpos hlower
    _ = _ := by
      have he : ((n:ℝ)+2)*saddlePairDeficit lam |q| =
          ((n:ℝ)+2)*(sphericalVariational lam (1+|q|)+sphericalVariational lam (1-|q|)) -
            2*(((n:ℝ)+2)*sphericalVariational lam 1) := by unfold saddlePairDeficit; ring
      rw [he,Real.exp_sub,two_mul,Real.exp_add]
      dsimp only [A]
      field_simp

lemma weighted_overlap_tail_term {m j : ℕ} (hm : 0 < m) (hj : j ≤ m)
    {h D : ℝ → ℝ} {A c δ : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hδ : 0 ≤ δ) (htail : δ ≤ |latticeOverlap m j|)
    (hh : h (latticeOverlap m j) ≤ A*Real.exp ((m:ℝ)*D |latticeOverlap m j|))
    (hD : D |latticeOverlap m j| ≤ latticeOverlap m j^2/2-c*|latticeOverlap m j|^3) :
    cubeOverlapMass m j*h (latticeOverlap m j) ≤ A*Real.exp (-(m:ℝ)*c*δ^3) := by
  have hp := cubeOverlapMass_chernoff hm hj
  have hmul := (mul_le_mul_of_nonneg_left hh (cubeOverlapMass_nonneg m j)).trans
    (mul_le_mul_of_nonneg_right hp (show 0 ≤ A*Real.exp ((m:ℝ)*D |latticeOverlap m j|) by positivity))
  have he : Real.exp (-(m:ℝ)*latticeOverlap m j^2/2) *
      (A*Real.exp ((m:ℝ)*D |latticeOverlap m j|)) =
      A*Real.exp ((m:ℝ)*(D |latticeOverlap m j|-latticeOverlap m j^2/2)) := by
    rw [← mul_assoc,mul_comm _ A,mul_assoc,← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [he] at hmul
  apply hmul.trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.exp_le_exp.mpr
  have hcub := pow_le_pow_left₀ hδ htail 3
  have hh0 := mul_le_mul_of_nonneg_left hcub hc
  have hh1 : D |latticeOverlap m j|-latticeOverlap m j^2/2 ≤ -c*δ^3 := by linarith
  have hh2 := mul_le_mul_of_nonneg_left hh1 (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  nlinarith

lemma weighted_overlap_tail_sum {m : ℕ} (hm : 0 < m) {h D : ℝ → ℝ} {A c δ : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hh : ∀ j ≤ m, δ < |latticeOverlap m j| →
      h (latticeOverlap m j) ≤ A*Real.exp ((m:ℝ)*D |latticeOverlap m j|))
    (hD : ∀ j ≤ m, δ < |latticeOverlap m j| →
      D |latticeOverlap m j| ≤ latticeOverlap m j^2/2-c*|latticeOverlap m j|^3) :
    (∑ j ∈ (Finset.range (m+1)).filter (fun j => ¬ |latticeOverlap m j| ≤ δ),
      cubeOverlapMass m j*h (latticeOverlap m j)) ≤ (m+1)*(A*Real.exp (-(m:ℝ)*c*δ^3)) := by
  let s := (Finset.range (m+1)).filter (fun j => ¬ |latticeOverlap m j| ≤ δ)
  have hc0 : (s.card:ℝ) ≤ m+1 := by
    have h : s.card ≤ m+1 := by
      simpa only [s,Finset.card_range] using Finset.card_filter_le (s := Finset.range (m+1)) (p := fun j => ¬ |latticeOverlap m j| ≤ δ)
    exact_mod_cast h
  have hs : ∀ j ∈ s, cubeOverlapMass m j*h (latticeOverlap m j) ≤ A*Real.exp (-(m:ℝ)*c*δ^3) := by
    intro j hj
    obtain ⟨hjm,hjt⟩ := Finset.mem_filter.mp hj
    have hjm' : j ≤ m := by have := Finset.mem_range.mp hjm; omega
    have hjt' := lt_of_not_ge hjt
    exact weighted_overlap_tail_term hm hjm' hA hc hδ hjt'.le (hh j hjm' hjt') (hD j hjm' hjt')
  have hsum := Finset.sum_le_card_nsmul s _ _ hs
  rw [nsmul_eq_mul] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_right hc0 (by positivity))

lemma polynomial_stretched_exponential_tendsto (p : ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n:ℝ)^p*Real.exp (-c*(n:ℝ)^a)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hd := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p/a) c hc).comp ht
  apply hd.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul (Nat.cast_nonneg n),mul_div_cancel₀ p ha.ne']

end

open Set MeasureTheory Filter

lemma latticeOverlap_abs_le {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) : |latticeOverlap n j| ≤ 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hj' : (j:ℝ) ≤ n := by exact_mod_cast hj
  have hnon : 0 ≤ 2*(j:ℝ)/n := by positivity
  have hup : 2*(j:ℝ)/n ≤ 2 := (div_le_iff₀ hn').mpr (by linarith)
  rw [abs_le]
  unfold latticeOverlap
  constructor <;> linarith

lemma pairMoment_variational_upper_general {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n) (lam : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n)
    (hv : ‖v‖ = Real.sqrt n) (horth : inner ℝ u v = 0)
    (hlam : ∀ i, |lam i| ≤ 3) {q K : ℝ} (hq : |q| ≤ 1) (hK : 0 < K)
    (hlo : K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n)) :
    pairMoment lam u v q / spherePartition lam 1 (Real.sqrt n)^2 ≤
      (26*Real.exp 1*n/K)^2 * Real.exp ((n:ℝ)*saddlePairDeficit lam |q|) := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hm
  subst n
  simpa only [Nat.cast_add,Nat.cast_ofNat] using pairMoment_variational_upper lam (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hu) (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hv) horth hlam hq hK (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hlo)

lemma sphereOverlap_density_second_moment_general {n : ℕ} (hn : 4 ≤ n) (lam : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ q : ℝ, pairMoment lam u v q*sphereOverlapDensity n q) = spherePartition lam 1 r^2 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hm
  subst n
  exact sphereOverlap_density_second_moment m lam hu hv horth

lemma saddlePairDeficit_full_cubic {ι : Type*} [Fintype ι] [Nonempty ι] (lam : ι → ℝ)
    {s₀ δ q : ℝ} (hlam : ∀ i, |lam i| ≤ 3) (hs₀ : 0 ≤ s₀)
    (hedge : spectralTop lam < 2+s₀) (hlow : 2-s₀ ≤ spectralTop lam)
    (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hres : ∀ s ∈ Set.Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hδ : 0 ≤ δ) (hscale : 216*s₀ ≤ δ^2)
    (herr : saddleSubcriticalError lam+s₀/2 ≤ 1/1536) (hq : q ∈ Set.Icc δ 1) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/24 := by
  have hq0 : 0 ≤ q := hδ.trans hq.1
  by_cases hsmall : q ≤ 1/4
  · have hsc : 216*s₀ ≤ q^2 := hscale.trans (pow_le_pow_left₀ hδ hq.1 2)
    have hh := saddlePairDeficit_shrinking_cubic lam hs₀ hedge hlow hres₀ hres ⟨hq0,hsmall⟩ hsc
    nlinarith [pow_nonneg hq0 3]
  · exact saddlePairDeficit_macro_cubic lam hlam hs₀ hedge hres₀ ⟨(le_of_not_ge hsmall),hq.2⟩ herr

lemma orientation_normalized_variance_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ [Nonempty (Fin n)] (lam : Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n)) (K s₀ : ℝ),
      ‖u‖ = Real.sqrt n → ‖v‖ = Real.sqrt n → inner ℝ u v = 0 →
      (∀ i, |lam i| ≤ 3) → 0 < K →
      K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n) →
      0 ≤ s₀ → spectralTop lam < 2+s₀ → 2-s₀ ≤ spectralTop lam →
      spectralStieltjes lam (2+s₀) ≤ 1 →
      (∀ s ∈ Set.Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s) →
      216*s₀ ≤ overlapCentralCutoff n^2 →
      saddleSubcriticalError lam+s₀/2 ≤ 1/1536 →
      (∫ U, (rotatedCubePartition lam 1 U / spherePartition lam 1 (Real.sqrt n)-1)^2
        ∂orthogonalHaar (Fin n)) ≤
        ε+(n+1)*((26*Real.exp 1*n/K)^2 * Real.exp (-(n:ℝ)/24*overlapCentralCutoff n^3)) := by
  have hc := central_overlap_uniform_bound overlapCentralCutoff_tendsto overlapCentralCutoff_fourth
    overlapCentralCutoff_min ε hε
  filter_upwards [hc,eventually_ge_atTop 4] with n hn hfour
  intro _ lam u v K s₀ hu hv horth hlam hK hlo hs₀ hedge hlow hres₀ hres hscale herr
  let S := spherePartition lam 1 (Real.sqrt n)
  let A := (26*Real.exp 1*n/K)^2
  let M := pairMoment lam u v
  let δ := overlapCentralCutoff n
  have hδ : 0 ≤ δ := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpos : 0 < S := spherePartition_pos _ _ _
  have hM := pairMoment_continuous lam u v
  have hMpos := pairMoment_nonneg lam u v
  have hcentral := hn M hM hMpos (fun _ _ hh => pairMoment_mono_abs lam (hu.trans hv.symm) hh)
  rw [sphereOverlap_density_second_moment_general hfour lam hu hv horth] at hcentral
  have hdivcentral : (∑ j ∈ (Finset.range (n+1)).filter (fun j => |latticeOverlap n j| ≤ δ),
      cubeOverlapMass n j*(M (latticeOverlap n j)/S^2)) ≤ 1+ε := by
    simp_rw [← mul_div_assoc,← Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos hpos)).mpr
    exact hcentral
  have hpair (j : ℕ) (hj : j ≤ n) : M (latticeOverlap n j)/S^2 ≤
      A*Real.exp ((n:ℝ)*saddlePairDeficit lam |latticeOverlap n j|) :=
    pairMoment_variational_upper_general (by omega) lam hu hv horth hlam
      (latticeOverlap_abs_le (by omega) hj) hK hlo
  have hcubic (j : ℕ) (hj : j ≤ n) (ht : δ < |latticeOverlap n j|) :
      saddlePairDeficit lam |latticeOverlap n j| ≤ latticeOverlap n j^2/2-(1/24)*|latticeOverlap n j|^3 := by
    have hh := saddlePairDeficit_full_cubic lam hlam hs₀ hedge hlow hres₀ hres hδ hscale herr
      ⟨ht.le,latticeOverlap_abs_le (by omega) hj⟩
    rw [sq_abs] at hh
    linarith
  have htail := weighted_overlap_tail_sum (h := fun q => M q/S^2) (D := saddlePairDeficit lam)
    (by omega : 0 < n) (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1/24) hδ
    (fun j hj _ => hpair j hj) hcubic
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.range (n+1))
    (fun j => |latticeOverlap n j| ≤ δ) (fun j => cubeOverlapMass n j*(M (latticeOverlap n j)/S^2))
  have hwhole := add_le_add hdivcentral htail
  rw [hsum] at hwhole
  simp_rw [← mul_div_assoc,← Finset.sum_div] at hwhole
  rw [← rotatedCubePartition_second_lattice (by omega) lam hu hv horth] at hwhole
  have hvareq := normalized_integral_square (rotatedCubePartition_continuous lam 1) hpos.ne'
    (rotatedCubePartition_first_moment (by omega) lam 1)
  rw [hvareq]
  dsimp only [A,δ,S,M] at hwhole ⊢
  convert (sub_le_sub_right hwhole 1) using 1
  all_goals first | rfl | ring_nf

lemma orientation_normalized_overlap_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ [Nonempty (Fin n)] (lam : Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n)) (K s₀ : ℝ),
      ‖u‖ = Real.sqrt n → ‖v‖ = Real.sqrt n → inner ℝ u v = 0 →
      (∀ i, |lam i| ≤ 3) → 0 < K →
      K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n) →
      0 ≤ s₀ → spectralTop lam < 2+s₀ → 2-s₀ ≤ spectralTop lam →
      spectralStieltjes lam (2+s₀) ≤ 1 →
      (∀ s ∈ Set.Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s) →
      216*s₀ ≤ overlapCentralCutoff n^2 →
      saddleSubcriticalError lam+s₀/2 ≤ 1/1536 →
      (∫ U, rotatedCubePair lam (fun q => q^2) U ∂orthogonalHaar (Fin n)) /
        spherePartition lam 1 (Real.sqrt n)^2 ≤
        (1+ε)*((∫ q : ℝ, (q^2*pairMoment lam u v q)*sphereOverlapDensity n q) /
          spherePartition lam 1 (Real.sqrt n)^2)+
        (n+1)*((26*Real.exp 1*n/K)^2 * Real.exp (-(n:ℝ)/24*overlapCentralCutoff n^3)) := by
  have hc := central_overlap_uniform_bound overlapCentralCutoff_tendsto overlapCentralCutoff_fourth
    overlapCentralCutoff_min ε hε
  filter_upwards [hc,eventually_ge_atTop 4] with n hn hfour
  intro _ lam u v K s₀ hu hv horth hlam hK hlo hs₀ hedge hlow hres₀ hres hscale herr
  let S := spherePartition lam 1 (Real.sqrt n)
  let A := (26*Real.exp 1*n/K)^2
  let M := fun q => q^2*pairMoment lam u v q
  let δ := overlapCentralCutoff n
  have hδ : 0 ≤ δ := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpos : 0 < S := spherePartition_pos _ _ _
  have hM : Continuous M := (continuous_id.pow 2).mul (pairMoment_continuous lam u v)
  have hMpos (q) : 0 ≤ M q := mul_nonneg (sq_nonneg _) (pairMoment_nonneg lam u v q)
  have hcentral := hn M hM hMpos (fun _ _ hh => squaredPairMoment_mono_abs lam (hu.trans hv.symm) hh)
  have hdivcentral : (∑ j ∈ (Finset.range (n+1)).filter (fun j => |latticeOverlap n j| ≤ δ),
      cubeOverlapMass n j*(M (latticeOverlap n j)/S^2)) ≤
      (1+ε)*((∫ q : ℝ, M q*sphereOverlapDensity n q)/S^2) := by
    simp_rw [← mul_div_assoc,← Finset.sum_div]
    exact div_le_div_of_nonneg_right hcentral (sq_nonneg S)
  have hpair (j : ℕ) (hj : j ≤ n) : M (latticeOverlap n j)/S^2 ≤
      A*Real.exp ((n:ℝ)*saddlePairDeficit lam |latticeOverlap n j|) := by
    have hq := latticeOverlap_abs_le (by omega : 0 < n) hj
    have hsq : latticeOverlap n j^2 ≤ 1 := by
      simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg (latticeOverlap n j)) hq 2
    have hh : M (latticeOverlap n j) ≤ pairMoment lam u v (latticeOverlap n j) := by
      dsimp only [M]
      exact mul_le_of_le_one_left (pairMoment_nonneg lam u v _) hsq
    exact (div_le_div_of_nonneg_right hh (sq_nonneg S)).trans
      (pairMoment_variational_upper_general (by omega) lam hu hv horth hlam hq hK hlo)
  have hcubic (j : ℕ) (hj : j ≤ n) (ht : δ < |latticeOverlap n j|) :
      saddlePairDeficit lam |latticeOverlap n j| ≤ latticeOverlap n j^2/2-(1/24)*|latticeOverlap n j|^3 := by
    have hh := saddlePairDeficit_full_cubic lam hlam hs₀ hedge hlow hres₀ hres hδ hscale herr
      ⟨ht.le,latticeOverlap_abs_le (by omega) hj⟩
    rw [sq_abs] at hh
    linarith
  have htail := weighted_overlap_tail_sum (h := fun q => M q/S^2) (D := saddlePairDeficit lam)
    (by omega : 0 < n) (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1/24) hδ
    (fun j hj _ => hpair j hj) hcubic
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.range (n+1))
    (fun j => |latticeOverlap n j| ≤ δ) (fun j => cubeOverlapMass n j*(M (latticeOverlap n j)/S^2))
  have hwhole := add_le_add hdivcentral htail
  rw [hsum] at hwhole
  simp_rw [← mul_div_assoc,← Finset.sum_div] at hwhole
  rw [← rotatedCubePair_lattice (by omega) lam (fun q => q^2) hu hv horth] at hwhole
  dsimp only [S,M,δ] at hwhole ⊢
  convert hwhole using 1; first | rfl | ring_nf

end CriticalSK

end

end OAI
