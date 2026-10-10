import Mathlib
import OAI.Probability.SKSupport.Density.GaussianLogDensity
import OAI.Probability.SKSupport.Density.DensityFubini

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat

lemma Heat.finiteDensity_first_formula (c : ℕ → ℝ≥0) {h : ℝ≥0}
    (hh : 0 < (h:ℝ)) (f : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    finiteDensity c h f N 1 x=heatKernel h x*
      Real.exp ((c 0:ℝ)*backwardBoundary c h f N 1 x-(c 0:ℝ)*backwardBoundary c h f N 0 0) := by
  have hn : Real.exp (-(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ)))=
      (Real.sqrt (2*Real.pi*(h:ℝ)))⁻¹ := by
    rw [show -(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))= -((1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))) by ring,
      Real.exp_neg,exp_half_log (by positivity)]
  unfold finiteDensity
  rw [forwardBoundary]
  simp only [Nat.cast_one,one_mul,ite_true,Nat.zero_add]
  rw [show (c 1:ℝ)*backwardBoundary c h f N 1 x-x^2/(2*(h:ℝ))+
      (-(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ))-(c 0:ℝ)*backwardBoundary c h f N 0 0-
      ((c 1:ℝ)-(c 0:ℝ))*backwardBoundary c h f N 1 x)=
      (-(1/2:ℝ)*Real.log (2*Real.pi*(h:ℝ)))+(-x^2/(2*(h:ℝ)))+
      ((c 0:ℝ)*backwardBoundary c h f N 1 x-(c 0:ℝ)*backwardBoundary c h f N 0 0) by ring,
    Real.exp_add,Real.exp_add,hn,heatKernel_formula hh.le]

lemma Heat.finiteDensity_first_pairing {f g : ℝ → ℝ}
    (hf : RegularDatum f) (hLip : LipschitzWith 1 f) (hg : BoundedSmooth g)
    (c : ℕ → ℝ≥0) (hc : 0 < (c 0:ℝ)) {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N : ℕ} (hN : 0 < N) :
    varianceTilted (c 0) h (backwardBoundary c h f N 1) g 0=
      ∫ x, finiteDensity c h f N 1 x*g x := by
  have hφ : LipschitzWith 1 (backwardBoundary c h f N 1) := cascade_lipschitz hLip c h _ _
  have hem := exp_varianceLogHeat hφ (ne_of_gt hc) (h:ℝ) 0
  rw [backwardBoundary_step hf hLip c h hN] at hem
  have hgm : Measurable (fun z => g z*Real.exp ((c 0:ℝ)*backwardBoundary c h f N 1 z)) :=
    hg.smooth.continuous.measurable.mul ((measurable_const.mul hφ.continuous.measurable).exp)
  unfold varianceTilted
  rw [← hem,varianceHeat_kernel hgm hh,← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [finiteDensity_first_formula c hh,Real.exp_sub]
  simp only [sub_zero]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

theorem finite_density_identity (W : BrownianSystem Ω) {f g : ℝ → ℝ}
    (hf : RegularDatum f) (hLip : LipschitzWith 1 f) (hg : BoundedSmooth g)
    (c : ℕ → ℝ≥0) (hc : ∀ i, 0 < (c i:ℝ)) {h : ℝ≥0} (hh : 0 < (h:ℝ))
    {N i : ℕ} (hi : 0 < i) (hiN : i ≤ N) :
    (∫ w, g ((finiteFeedback hf hLip c h N 0).solution W.driver ((i:ℝ≥0)*h) w) ∂W.law)=
      ∫ x, finiteDensity c h f N i x*g x := by
  let := W.isProbability
  induction i generalizing g with
  | zero => omega
  | succ i ih =>
    rw [finite_transition_tilted W hf hLip hg c h (by omega : i < N)]
    by_cases h0 : i=0
    · subst i
      simp only [Nat.cast_zero,zero_mul,BoundedLipschitzDrift.solution_zero]
      simpa using finiteDensity_first_pairing hf hLip hg c (hc 0) hh (N := N) (by omega)
    · have hip : 0 < i := Nat.pos_of_ne_zero h0
      have hφ : RegularDatum (backwardBoundary c h f N (i+1)) := cascade_regular hf hLip c h _ _
      have hφL : LipschitzWith 1 (backwardBoundary c h f N (i+1)) := cascade_lipschitz hLip c h _ _
      have hgt := (varianceTilted_family hφ hφL hg (hc i).le).regular (h:ℝ)
      rw [ih hgt hip (by omega)]
      exact finiteDensity_step_pairing hf hLip hg c hc hh hip (by omega)

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma datumScore_regular {L : ℝ → ℝ} (hL : RegularDatum L) (a : ℝ) : RegularDatum (datumScore a L) := by
  refine ⟨(contDiff_id.div_const a).sub (contDiff_infty_iff_deriv.mp hL.smooth |>.2),?_⟩
  have he : deriv (datumScore a L)=fun x => 1/a+(-1)*deriv (deriv L) x := by
    funext x
    rw [datumScore_deriv hL.smooth]
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    ring
  rw [he]
  exact (BoundedSmooth.const _).add (hL.deriv_bounded.deriv.const_mul (-1))

lemma datumScore_odd {L : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (he : Function.Even L) (a : ℝ) :
    Function.Odd (datumScore a L) := by
  have hh := even_deriv_odd (hL.differentiable (by simp)) he
  intro x
  dsimp only [datumScore]
  rw [hh x]
  ring

lemma datumScore_second {L : ℝ → ℝ} (hL : ContDiff ℝ ∞ L) (a x : ℝ) :
    iteratedDeriv 2 (datumScore a L) x= -iteratedDeriv 3 L x := by
  have he : deriv (datumScore a L)=fun y => 1/a-iteratedDeriv 2 L y := by
    funext y;exact datumScore_deriv hL a y
  simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
  rw [he]
  convert ((hasDerivAt_const x (1/a)).sub (hasDerivAt_spatialJet hL 2 x)).deriv using 1
  first | rfl | simp [iteratedDeriv_succ,iteratedDeriv_zero]

theorem finite_density_coercivity {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N i : ℕ} (hi : 0 < i) (hiN : i ≤ N) :
    let r := fun x => (c i:ℝ)*deriv (backwardBoundary c h (softAbs M) N i) x
    (1/1000:ℝ)*(∫ x, finiteDensity c h (softAbs M) N i x*quarticMoment r x) ≤
      ∫ x, finiteDensity c h (softAbs M) N i x*coercivePolynomial r x := by
  let φ := backwardBoundary c h (softAbs M) N i
  let L := forwardBoundary c h (softAbs M) N i
  let a : ℝ := (i:ℝ)*h
  let r := fun x => (c i:ℝ)*deriv φ x
  let s := datumScore a L
  let U := fun x => (c i:ℝ)*φ x+L x
  let d : ℝ := 1/(2*a)
  have ha : 0 < a := mul_pos (Nat.cast_pos.mpr hi) hh
  have hp := (hc 0).trans_le (hM 0)
  have hf := regularDatum_softAbs (ne_of_gt hp)
  have hLip := softAbs_lipschitz (ne_of_gt hp)
  have hφ : RegularDatum φ := cascade_regular hf hLip c h _ _
  have hL : RegularDatum L := forwardBoundary_regular hf hLip c hh N i
  have hLe : ForwardDatumShape L := forwardBoundary_shape c hc hmono hM hh N i
  have hr : BoundedSmooth r := hφ.deriv_bounded.const_mul _
  have hs : RegularDatum s := datumScore_regular hL a
  have hshape : BackwardShape r := backwardBoundary_shape c hc hmono hM h N i
  have hso : Function.Odd s := datumScore_odd hL.smooth hLe.even a
  have hsa (x : ℝ) : 0 ≤ deriv s x := by
    rw [datumScore_deriv hL.smooth]
    linarith [hLe.second x,one_div_pos.mpr ha]
  have hsw (x : ℝ) (hx : 0 ≤ x) : iteratedDeriv 2 s x ≤ 0 := by
    rw [datumScore_second hL.smooth]
    exact neg_nonpos.mpr (hLe.third x hx)
  have hQ (x : ℝ) (hx : 0 ≤ x) : 0 ≤ r x*deriv s x-s x*deriv r x :=
    boundaryRatio_nonneg c hc hmono hM hh N i hi hiN x hx
  have hUr : RegularDatum U := by
    convert hL.sub_mul hφ (-(c i:ℝ)) using 1
    funext x;dsimp only [U];ring
  obtain ⟨K,hU⟩ := hUr.exists_lipschitz
  have hUe : Function.Even U := by
    have heφ : Function.Even φ := cascade_even hf hLip (softAbs_even M) c h _ _
    intro x
    dsimp only [U]
    rw [heφ x,hLe.even x]
  have hUd (x : ℝ) : HasDerivAt U (r x-s x+2*d*x) x := by
    have he : r x-s x+2*d*x=(c i:ℝ)*deriv φ x+deriv L x := by
      dsimp only [r,s,datumScore,d]
      field_simp [ne_of_gt ha]
      ring
    rw [he]
    convert (((hφ.smooth.differentiable (by simp)) x).hasDerivAt.const_mul (c i:ℝ)).add
      (((hL.smooth.differentiable (by simp)) x).hasDerivAt) using 1
  have he : finiteDensity c h (softAbs M) N i=gaussianLogDensity d U := by
    funext x
    unfold finiteDensity gaussianLogDensity
    congr 1
    dsimp only [d,U,a,φ,L]
    ring
  rw [he]
  exact gaussian_shape_coercivity hr hs hshape hso hsa hsw hQ hU hUe (by dsimp [d];positivity) hUd

end Heat
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

theorem finite_feedback_coercivity (W : BrownianSystem Ω) {M : ℝ} (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hM : ∀ i, (c i:ℝ) ≤ M)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N i : ℕ} (hi : 0 < i) (hiN : i ≤ N) :
    let hMp : M ≠ 0 := ne_of_gt ((hc 0).trans_le (hM 0))
    let X := (finiteFeedback (regularDatum_softAbs hMp) (softAbs_lipschitz hMp) c h N 0).solution W.driver
    let r := fun x => (c i:ℝ)*deriv (backwardBoundary c h (softAbs M) N i) x
    (1/1000:ℝ)*(∫ w, quarticMoment r (X ((i:ℝ≥0)*h) w) ∂W.law) ≤
      ∫ w, coercivePolynomial r (X ((i:ℝ≥0)*h) w) ∂W.law := by
  dsimp only
  have hMp : M ≠ 0 := ne_of_gt ((hc 0).trans_le (hM 0))
  have hr : BoundedSmooth (fun x => (c i:ℝ)*deriv (backwardBoundary c h (softAbs M) N i) x) := (cascade_regular (regularDatum_softAbs hMp) (softAbs_lipschitz hMp) c h (N-i) i).deriv_bounded.const_mul (c i:ℝ)
  rw [finite_density_identity W (regularDatum_softAbs hMp) (softAbs_lipschitz hMp)
    (quarticMoment_boundedSmooth hr) c hc hh hi hiN,
    finite_density_identity W (regularDatum_softAbs hMp) (softAbs_lipschitz hMp)
    (coercivePolynomial_boundedSmooth hr) c hc hh hi hiN]
  exact finite_density_coercivity c hc hmono hM hh hi hiN

end ZeroTemperatureSK

end
end

end OAI
