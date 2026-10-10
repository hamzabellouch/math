import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicWeighted

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
def atomicFraction (e:ℝ) (x:Space):ℝ:=coulombKernel x*atomicWeight e x
lemma atomicFraction_nonneg {e:ℝ} (he:0<e) (x:Space):0≤atomicFraction e x := by
  unfold atomicFraction atomicWeight coulombKernel
  positivity
lemma atomicFraction_le_one {e:ℝ} (he:0<e) (x:Space):atomicFraction e x≤1 := by
  change ‖x‖⁻¹*(‖x‖⁻¹+e)⁻¹≤1
  rw [←div_eq_mul_inv,div_le_one (by positivity)]
  linarith
lemma atomicFraction_measurable (e:ℝ):Measurable (atomicFraction e) :=
  coulombKernel_measurable.mul (atomicWeight_measurable e)
lemma atomicWeight_eq_radius {e:ℝ} (he:0<e) {x:Space} (hx:x≠0):
    atomicWeight e x=‖x‖/(1+e*‖x‖) := by
  unfold atomicWeight coulombKernel
  have hr:=norm_pos_iff.mpr hx
  field_simp
lemma atomicFraction_eq_radius {e:ℝ} (he:0<e) {x:Space} (hx:x≠0):
    atomicFraction e x=1/(1+e*‖x‖) := by
  rw [atomicFraction,atomicWeight_eq_radius he hx]
  unfold coulombKernel
  field_simp
lemma atomic_weight_triangle {e:ℝ} (he:0<e) {x y:Space} (hx:x≠0) (hy:y≠0) (hxy:x≠y):
    atomicFraction e x*atomicFraction e y≤coulombKernel (x-y)*(atomicWeight e x+atomicWeight e y) := by
  rw [atomicFraction_eq_radius he hx,atomicFraction_eq_radius he hy,
    atomicWeight_eq_radius he hx,atomicWeight_eq_radius he hy]
  let a:=1+e*‖x‖
  let b:=1+e*‖y‖
  have ha:0<a:=by dsimp [a]; positivity
  have hb:0<b:=by dsimp [b]; positivity
  have hd:0<‖x-y‖:=norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hn:‖x-y‖≤‖x‖*b+‖y‖*a := by
    have H:=norm_sub_le x y
    have H0:0≤e*‖x‖*‖y‖:=by positivity
    dsimp [a,b]
    nlinarith
  change 1/a*(1/b)≤‖x-y‖⁻¹*(‖x‖/a+‖y‖/b)
  calc
    _=‖x-y‖/(‖x-y‖*(a*b)):=by field_simp
    _≤(‖x‖*b+‖y‖*a)/(‖x-y‖*(a*b)):=div_le_div_of_nonneg_right hn (by positivity)
    _= _:=by field_simp
lemma potentialForm_finsetSum {n:ℕ} {ι:Type*} (u:H1Vector n) (A:Finset ι)
    (f:ι → Configuration n → ℝ)
    (hi:∀ i∈A,∀ s,Integrable (fun x => f i x*‖u.value s x‖^2)):
    potentialForm (fun x => ∑ i∈A,f i x) u=∑ i∈A,potentialForm (f i) u := by
  unfold potentialForm
  simp only [Finset.sum_mul]
  simp_rw [integral_finsetSum A (fun i hi' => hi i hi' _)]
  exact Finset.sum_comm
lemma potentialForm_add {n:ℕ} (u:H1Vector n) (f g:Configuration n → ℝ)
    (hf:∀ s,Integrable (fun x => f x*‖u.value s x‖^2))
    (hg:∀ s,Integrable (fun x => g x*‖u.value s x‖^2)):
    potentialForm (fun x => f x+g x) u=potentialForm f u+potentialForm g u := by
  unfold potentialForm
  simp only [add_mul,integral_add (hf _) (hg _),Finset.sum_add_distrib]
lemma potentialForm_mono_ae {n:ℕ} (u:H1Vector n) (f g:Configuration n → ℝ)
    (hf:∀ s,Integrable (fun x => f x*‖u.value s x‖^2))
    (hg:∀ s,Integrable (fun x => g x*‖u.value s x‖^2)) (h:∀ᵐ x,f x≤g x):
    potentialForm f u≤potentialForm g u := by
  exact Finset.sum_le_sum (fun s _ => integral_mono_ae (hf s) (hg s)
    (h.mono fun x hx => mul_le_mul_of_nonneg_right hx (sq_nonneg _)))
lemma pair_weight_integrable {n:ℕ} (u:H1Vector n) (i j a:Fin n) (hij:i≠j)
    {e:ℝ} (he:0<e) (s:Spins n):
    Integrable (fun x => coulombKernel (position x i-position x j)*atomicWeight e (position x a)*‖u.value s x‖^2) :=
  potentialForm_bdd_mul_integrable u _ _ (fun s =>
    (u.pair_coulomb_integrable_bound s i j hij (by norm_num : (0:ℝ)<1)).1)
    (((atomicWeight_measurable e).comp (continuous_position a).measurable).aestronglyMeasurable)
    (Eventually.of_forall (fun x => atomicWeight_bound he (position x a))) s
lemma pair_weight_symmetry {n:ℕ} (u:H1Vector n) (ha:Antisymmetric u) (i j:Fin n) (e:ℝ):
    potentialForm (fun x => coulombKernel (position x i-position x j)*atomicWeight e (position x j)) u=
    potentialForm (fun x => coulombKernel (position x i-position x j)*atomicWeight e (position x i)) u := by
  have H:=antisymmetric_expectation_permute ha (Equiv.swap i j)
    (fun x => coulombKernel (position x i-position x j)*atomicWeight e (position x i))
  simpa only [potentialForm,position_permute,Equiv.swap_apply_left,Equiv.swap_apply_right,coulombKernel,norm_sub_rev] using H
end Coulomb
end

end

end OAI
