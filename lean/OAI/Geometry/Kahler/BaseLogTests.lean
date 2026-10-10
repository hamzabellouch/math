import OAI.Geometry.Kahler.HartogsTransferTools

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
namespace PinchedHartogs
namespace BaseConstruction

abbrev Sphere := Metric.sphere (0 : Base) 1

def bracket (z p : Base) : ℂ := inner ℂ p z

def peakPolynomial (P : Finset Sphere) (k : ℕ) (z : Base) : ℂ :=
  ∑ p ∈ P, bracket z p ^ k

def regularizedLog (a ε : ℝ) (v : ℂ) : ℝ :=
  Real.log ((‖1-(a:ℂ)*v‖^2+ε^2)/(1+ε^2))

def logarithmicTest (a ε : ℝ) (P : Finset Sphere) (k : ℕ) (z : Base) : ℝ :=
  regularizedLog a ε (peakPolynomial P k z)

def basePotential (P : ℕ → Finset Sphere) (a ε L : ℝ) (Q : ℕ) (z : Base) : ℝ :=
  psi z + L * ∑' j : ℕ, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) z

lemma bracket_analytic (p : Base) : AnalyticOnNhd ℂ (fun z => bracket z p) univ :=
  fun z _ => (innerSL ℂ p).analyticAt z

lemma peakPolynomial_analytic (P : Finset Sphere) (k : ℕ) :
    AnalyticOnNhd ℂ (peakPolynomial P k) univ := by
  intro z hz
  apply Finset.analyticAt_fun_sum
  intro p hp
  exact (bracket_analytic p z (mem_univ _)).pow k

lemma regularizedLog_eq (a ε : ℝ) (v : ℂ) (hε : ε ≠ 0) :
    regularizedLog a ε v = Real.log (‖1-(a:ℂ)*v‖^2+ε^2)-Real.log (1+ε^2) := by
  apply Real.log_div <;> positivity

@[simp] lemma regularizedLog_zero (a ε : ℝ) : regularizedLog a ε 0 = 0 := by
  simp [regularizedLog]

lemma regularizedLog_contDiff (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedLog a ε) := by
  have hn : ContDiff ℝ ∞ (fun v : ℂ => ‖1-(a:ℂ)*v‖^2+ε^2) :=
    ((contDiff_norm_sq ℂ).comp (contDiff_const.sub (contDiff_const.mul contDiff_id))).add contDiff_const
  have hh : ContDiff ℝ ∞ (fun v : ℂ => Real.log (‖1-(a:ℂ)*v‖^2+ε^2)-Real.log (1+ε^2)) :=
    (hn.log (fun v => by positivity)).sub contDiff_const
  have he : regularizedLog a ε = (fun v : ℂ => Real.log (‖1-(a:ℂ)*v‖^2+ε^2)-Real.log (1+ε^2)) :=
    funext (fun v => regularizedLog_eq a ε v hε)
  rw [he]
  exact hh

lemma logarithmicTest_contDiff (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) (P : Finset Sphere) (k : ℕ) :
    ContDiff ℝ ∞ (logarithmicTest a ε P k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (regularizedLog_contDiff a hε).contDiffAt.comp z
    (((peakPolynomial_analytic P k) z (mem_univ _)).contDiffAt.restrict_scalars ℝ)

lemma peakPolynomial_zero (P : Finset Sphere) {k : ℕ} (hk : k ≠ 0) :
    peakPolynomial P k 0 = 0 := by simp [peakPolynomial,bracket,hk]

lemma logarithmicTest_zero (a ε : ℝ) (P : Finset Sphere) {k : ℕ} (hk : k ≠ 0) :
    logarithmicTest a ε P k 0 = 0 := by simp [logarithmicTest,peakPolynomial_zero P hk]

lemma peakPolynomial_homogeneous (P : Finset Sphere) (k : ℕ) (c : ℂ) (z : Base) :
    peakPolynomial P k (c • z) = c^k * peakPolynomial P k z := by
  simp only [peakPolynomial,bracket, inner_smul_right,mul_pow,Finset.mul_sum]

lemma regularizedLog_lipschitz_bound (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, ‖v‖ ≤ A → |regularizedLog a ε v| ≤ C*‖v‖ := by
  have hs := regularizedLog_contDiff a hε
  have hc : Continuous (fderiv ℝ (regularizedLog a ε)) := hs.continuous_fderiv (by norm_num)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) A).bddAbove_image hc.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro v hv
  have hbound : ∀ x ∈ Metric.closedBall (0:ℂ) A, ‖fderiv ℝ (regularizedLog a ε) x‖ ≤ max C 0 := by
    intro x hx
    exact (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hm := (convex_closedBall (0:ℂ) A).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hs.differentiable (by norm_num) x) hbound
    (show (0:ℂ) ∈ Metric.closedBall 0 A by simpa using hA)
    (show v ∈ Metric.closedBall 0 A by simpa using hv)
  simpa [Real.norm_eq_abs] using hm

private def regularizedFiberLog (ε : ℝ) (q : Ambient) : ℝ :=
  Real.log (‖q.2‖^2+ε^2)-Real.log (1+ε^2)

private lemma regularizedFiberLog_contDiff {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedFiberLog ε) := by
  have he := sq_pos_of_ne_zero hε
  have hn : ContDiff ℝ ∞ (fun q : Ambient => ‖q.2‖^2+ε^2) :=
    ((contDiff_norm_sq ℂ).comp contDiff_snd).add contDiff_const
  exact (hn.log (fun q => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) he))).sub contDiff_const

private lemma regularizedFiberLog_hessian {ε : ℝ} (hε : ε ≠ 0) (q : Ambient) (i j : Fin 3) :
    complexHessian (regularizedFiberLog ε) q i j =
      ((ε^2/(‖q.2‖^2+ε^2)^2 : ℝ):ℂ) * (if i=2 then 1 else 0)*(if j=2 then 1 else 0) := by
  have hden : ‖q.2‖^2+ε^2 ≠ 0 := by positivity
  have hρ : ∀ᶠ y in 𝓝 (‖q.2‖^2),
      HasDerivAt (fun s => Real.log (s+ε^2)-Real.log (1+ε^2)) ((y+ε^2)⁻¹) y := by
    filter_upwards [(continuousAt_id.add continuousAt_const).eventually_ne hden] with y hy
    simpa [one_div] using (((hasDerivAt_id y).add_const (ε^2)).log hy).sub_const (Real.log (1+ε^2))
  have hρ' : HasDerivAt (fun s : ℝ => (s+ε^2)⁻¹) (-( (‖q.2‖^2+ε^2)^2)⁻¹) (‖q.2‖^2) := by
    convert ((hasDerivAt_id (‖q.2‖^2)).add_const (ε^2)).inv hden using 1 <;> try rfl
    simp [one_div, neg_div]
  have hh := complexHessian_real_comp
    (((contDiff_norm_sq ℂ).comp contDiff_snd).contDiffAt : ContDiffAt ℝ 2 (fun p : Ambient => ‖p.2‖^2) q)
    hρ hρ' i j
  dsimp only [Function.comp_def] at hh
  rw [complexHessian_fiber_norm_sq,dz_fiber_norm_sq,dbar_fiber_norm_sq] at hh
  change complexHessian (regularizedFiberLog ε) q i j = _ at hh
  rw [hh]
  have hn : star q.2 * q.2 = (‖q.2‖^2 : ℝ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  by_cases hi : i=2 <;> by_cases hj : j=2 <;> simp [hi,hj]
  rw [mul_assoc, ← Complex.star_def, hn]
  have hd : (↑‖q.2‖^2 + (ε:ℂ)^2) ≠ 0 := by exact_mod_cast hden
  field_simp
  ; push_cast; ring

lemma regularizedLog_holomorphic_psh (a : ℝ) {ε : ℝ} (he : ε ≠ 0)
    {f : Base → ℂ} {z : Base} (hf : AnalyticAt ℂ f z) (v : Base) :
    0 ≤ (∑ i, ∑ j, baseHessian (regularizedLog a ε ∘ f) z i j * v i * star (v j)).re := by
  let F : Ambient → Ambient := fun q => (q.1,1-(a:ℂ)*f q.1)
  have hF : AnalyticAt ℂ F (z,0) :=
    ((ContinuousLinearMap.fst ℂ Base ℂ).analyticAt _).prod
      (analyticAt_const.sub (analyticAt_const.mul (hf.comp ((ContinuousLinearMap.fst ℂ Base ℂ).analyticAt _))))
  have hfc : ContDiffAt ℝ 2 (regularizedLog a ε ∘ f) z :=
    ((regularizedLog_contDiff a he).contDiffAt.comp z (hf.contDiffAt.restrict_scalars ℝ)).of_le (WithTop.coe_le_coe.mpr le_top)
  have heq : regularizedFiberLog ε ∘ F = fun q : Ambient => (regularizedLog a ε ∘ f) q.1 := by
    funext q
    exact (regularizedLog_eq a ε (f q.1) he).symm
  have hh := congrArg (fun A => (hermitianValue A (v,0) (v,0)).re)
    (complexHessian_pullback ((regularizedFiberLog_contDiff he).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) hF)
  rw [heq,hermitianValue_lift_base hfc,hermitianValue_pullback] at hh
  rw [hh]
  let u := fderiv ℂ F (z,0) (v,0)
  change 0 ≤ (hermitianValue (complexHessian (regularizedFiberLog ε) (F (z,0))) u u).re
  simp only [hermitianValue,regularizedFiberLog_hessian he,Fin.sum_univ_three]
  simp only [Fin.reduceEq,ite_false,ite_true,mul_zero,zero_mul,zero_add,add_zero]
  have hu : u.2*star u.2 = (‖u.2‖^2:ℝ) := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  change 0 ≤ (((ε^2/(‖(F (z,0)).2‖^2+ε^2)^2:ℝ):ℂ)*1*1*u.2*star u.2).re
  rw [mul_one,mul_one,mul_assoc,hu]
  simp only [← Complex.ofReal_mul,Complex.ofReal_re]
  positivity

lemma logarithmicTest_psh (a : ℝ) {ε : ℝ} (he : ε ≠ 0) (P : Finset Sphere)
    (k : ℕ) (z v : Base) :
    0 ≤ (∑ i, ∑ j, baseHessian (logarithmicTest a ε P k) z i j * v i * star (v j)).re :=
  regularizedLog_holomorphic_psh a he (peakPolynomial_analytic P k z (mem_univ _)) v

end BaseConstruction
end PinchedHartogs

end

end OAI
