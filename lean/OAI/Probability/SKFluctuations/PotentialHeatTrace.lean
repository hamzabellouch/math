import Mathlib
import OAI.Probability.SKFluctuations.EvalStep

namespace OAI

/-! Potential Heat Trace. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
def potentialHeatTrace {κ E : Type*} [Fintype κ] (m : ℝ) (G H : κ → E → ℝ) (x : E) : ℝ :=
  ∑ i, (m*H i x+m^2*(G i x)^2)

def testedHeatTrace {κ E : Type*} [Fintype κ] (m : ℝ) (G H : κ → E → ℝ)
    (A : E → ℝ) (A₁ A₂ : κ → E → ℝ) (x : E) : ℝ :=
  ∑ i, (A₂ i x+2*m*A₁ i x*G i x+A x*(m*H i x+m^2*(G i x)^2))

 

theorem hasDerivWithinAt_clockTest {n : ℕ}
    {F A : (Fin (n+1) → ℝ) → ℝ} {G H A₁ A₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hA₁ : ∀ i, BddSmooth 0 (A₁ i)) (hA₂ : ∀ i, BddSmooth 0 (A₂ i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hdG : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1))
      (H i (x+t • Pi.single i 1)) t)
    (hdA : ∀ x v t, HasDerivAt (fun s : ℝ => A (x+s • v))
      (∑ i, v i*A₁ i (x+t • v)) t)
    (hdA₁ : ∀ i x t, HasDerivAt (fun s : ℝ => A₁ i (x+s • Pi.single i 1))
      (A₂ i (x+t • Pi.single i 1)) t)
    (m : ℝ) (x : Fin (n+1) → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => clockTest m F A s x)
      ((1/2:ℝ)*(clockTest m F (testedHeatTrace m G H A A₁ A₂) t x-
        clockTest m F A t x*clockTest m F (potentialHeatTrace m G H) t x)) (Ici 0) t := by
  let P := fun y => Real.exp (m*F y)
  let P₁ := fun i y => (m*G i y)*P y
  let P₂ := fun i y => (m*H i y+m^2*(G i y)^2)*P y
  let W := fun y => A y*P y
  let W₁ := fun i y => (A₁ i y+m*A y*G i y)*P y
  let W₂ := fun i y => (A₂ i y+2*m*A₁ i y*G i y+A y*(m*H i y+m^2*(G i y)^2))*P y
  let ν := Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have hP : ExpNormBounded P := ExpNormBounded.exp_lipschitz hF m
  have hP₂ (i) : BddSmooth 0 (fun y => m*H i y+m^2*(G i y)^2) := by
    simpa only [pow_two] using ((hH i).const_mul m).add (((hG i).mul (hG i)).const_mul (m*m))
  have hW₁ (i) : BddSmooth 0 (fun y => A₁ i y+m*A y*G i y) :=
    (hA₁ i).add ((hA.const_mul m).mul (hG i))
  have hW₂ (i) : BddSmooth 0 (fun y => A₂ i y+2*m*A₁ i y*G i y+A y*(m*H i y+m^2*(G i y)^2)) :=
    ((hA₂ i).add (((hA₁ i).const_mul (2*m)).mul (hG i))).add (hA.mul (hP₂ i))
  have hdP (y v : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P (y+r • v)) (∑ i, v i*P₁ i (y+s • v)) s := by
    apply (((hdF y v s).const_mul m).exp).congr_deriv
    dsimp [P₁,P]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdPc (i) (y : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P (y+r • Pi.single i 1)) (P₁ i (y+s • Pi.single i 1)) s := by
    simpa only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using
      hdP y (Pi.single i 1) s
  have hdP₁ (i) (y : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P₁ i (y+r • Pi.single i 1)) (P₂ i (y+s • Pi.single i 1)) s := by
    apply (((hdG i y s).const_mul m).mul (hdPc i y s)).congr_deriv
    dsimp [P₂,P₁]
    ring
  have hdAc (i) (y : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => A (y+r • Pi.single i 1)) (A₁ i (y+s • Pi.single i 1)) s := by
    simpa only [Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using
      hdA y (Pi.single i 1) s
  have hdW (y v : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => W (y+r • v)) (∑ i, v i*W₁ i (y+s • v)) s := by
    apply ((hdA y v s).mul (hdP y v s)).congr_deriv
    dsimp [W₁,P₁]
    rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdW₁ (i) (y : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => W₁ i (y+r • Pi.single i 1)) (W₂ i (y+s • Pi.single i 1)) s := by
    apply (((hdA₁ i y s).add (((hdAc i y s).const_mul m).mul (hdG i y s))).mul (hdPc i y s)).congr_deriv
    dsimp [W₂,P₁]
    ring
  have hp := hasDerivWithinAt_gaussian_vector_variance hP (fun i => hP.bdd_mul ((hG i).const_mul m))
    (fun i => hP.bdd_mul (hP₂ i)) hdP hdP₁ x ht
  have hw := hasDerivWithinAt_gaussian_vector_variance (hP.bdd_mul hA)
    (fun i => hP.bdd_mul (hW₁ i)) (fun i => hP.bdd_mul (hW₂ i)) hdW hdW₁ x ht
  have htraceP : BddSmooth 0 (potentialHeatTrace m G H) := BddSmooth.sum Finset.univ (fun i _ => hP₂ i)
  have htraceW : BddSmooth 0 (testedHeatTrace m G H A A₁ A₂) := BddSmooth.sum Finset.univ (fun i _ => hW₂ i)
  have hdp (y) : (∑ i, P₂ i y) = potentialHeatTrace m G H y*P y := by dsimp [P₂,potentialHeatTrace]; rw [Finset.sum_mul]
  have hdw (y) : (∑ i, W₂ i y) = testedHeatTrace m G H A A₁ A₂ y*P y := by dsimp [W₂,testedHeatTrace]; rw [Finset.sum_mul]
  change HasDerivWithinAt (fun s => ∫ z, W (x+Real.sqrt s • z) ∂ν)
    ((1/2:ℝ)*∫ z, ∑ i, W₂ i (x+Real.sqrt t • z) ∂ν) (Ici 0) t at hw
  change HasDerivWithinAt (fun s => ∫ z, P (x+Real.sqrt s • z) ∂ν)
    ((1/2:ℝ)*∫ z, ∑ i, P₂ i (x+Real.sqrt t • z) ∂ν) (Ici 0) t at hp
  simp_rw [hdp] at hp
  simp_rw [hdw] at hw
  have hpos : (∫ z, P (x+Real.sqrt t • z) ∂ν) ≠ 0 := (partition_pos m (hP.affine_integrable hν x _)).ne'
  have h := hw.div hp hpos
  apply h.congr_of_eventuallyEq ?_ ?_ |>.congr_deriv ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact clockTest_eq hF.continuous hA.continuous m hs x
  · exact clockTest_eq hF.continuous hA.continuous m ht x
  · rw [clockTest_eq hF.continuous htraceW.continuous m ht x,
      clockTest_eq hF.continuous hA.continuous m ht x,
      clockTest_eq hF.continuous htraceP.continuous m ht x]
    dsimp only [tiltedMean]
    change ((_ * (∫ z, P (x+Real.sqrt t • z) ∂ν)) - _ * _) /
      (∫ z, P (x+Real.sqrt t • z) ∂ν)^2 = _
    dsimp only [W,P,ν] at *
    field_simp

end SKFluctuations.Hierarchy

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

 

theorem ExpNormBounded.continuous_integral_affine {f : E → ℝ} (hf : ExpNormBounded f)
    {ν : Measure E} (hν : ExponentialIncrement ν) :
    Continuous (fun p : ℝ × E => ∫ z, f (p.2+p.1 • z) ∂ν) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated
    (bound := fun z => C*Real.exp (c*(‖p.2‖+1))*Real.exp (c*(|p.1|+1)*‖z‖))
  · exact Eventually.of_forall fun q =>
      (hf.1.comp (continuous_const.add ((continuous_const (y := q.1)).smul continuous_id))).aestronglyMeasurable
  · filter_upwards [(prod_mem_nhds (Metric.ball_mem_nhds p.1 (by norm_num : (0:ℝ)<1))
      (Metric.ball_mem_nhds p.2 (by norm_num : (0:ℝ)<1)))] with q hq
    refine Eventually.of_forall fun z => ?_
    have hq₁ : |q.1| ≤ |p.1|+1 := by
      have h := (Metric.mem_ball.mp hq.1).le
      rw [Real.dist_eq] at h
      calc |q.1| = |(q.1-p.1)+p.1| := by congr 1; ring
        _ ≤ |q.1-p.1|+|p.1| := abs_add_le _ _
        _ ≤ |p.1|+1 := by linarith
    have hq₂ : ‖q.2‖ ≤ ‖p.2‖+1 := by
      have h := (Metric.mem_ball.mp hq.2).le
      calc ‖q.2‖ = ‖q.2-p.2+p.2‖ := by rw [sub_add_cancel]
        _ ≤ ‖q.2-p.2‖+‖p.2‖ := norm_add_le _ _
        _ ≤ ‖p.2‖+1 := by rw [← dist_eq_norm]; linarith
    change |f (q.2+q.1 • z)| ≤ _
    apply (affine_norm_exp_bound hC hc hb q.2 q.1 z).trans
    gcongr
  · exact (hν (c*(|p.1|+1))).const_mul _
  · exact Eventually.of_forall fun z =>
      (hf.1.comp (continuous_snd.add (continuous_fst.smul continuous_const))).continuousAt

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

theorem sqrt_coe_toNNReal (t : ℝ) : Real.sqrt (Real.toNNReal t : ℝ) = Real.sqrt t := by
  by_cases ht : 0 ≤ t
  · rw [Real.coe_toNNReal t ht]
  · rw [Real.toNNReal_of_nonpos (le_of_not_ge ht)]
    simp only [NNReal.coe_zero,Real.sqrt_zero,Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ht)]

theorem clockTest_eq_all {F A : (ι → ℝ) → ℝ} (hF : Continuous F) (hA : Continuous A)
    (m t : ℝ) (x : ι → ℝ) :
    clockTest m F A t x = tiltedMean (Measure.pi fun _ : ι => gaussianReal 0 1) m
      (fun z => F (x+Real.sqrt t • z)) (fun z => A (x+Real.sqrt t • z)) := by
  have hn := integral_isotropicGaussian (Real.toNNReal t)
    (f := fun z => A (x+z)*Real.exp (m*F (x+z))) (by fun_prop)
  have hd := integral_isotropicGaussian (Real.toNNReal t)
    (f := fun z => Real.exp (m*F (x+z))) (by fun_prop)
  rw [sqrt_coe_toNNReal] at hn hd
  exact congrArg₂ (· / ·) hn.symm hd.symm

 
theorem clockTest_continuous {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (m : ℝ) :
    Continuous (fun p : ℝ × (ι → ℝ) => clockTest m F A p.1 p.2) := by
  let ν := Measure.pi fun _ : ι => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have he := ExpNormBounded.exp_lipschitz hF m
  have hn := (he.bdd_mul hA).continuous_integral_affine hν
  have hd := he.continuous_integral_affine hν
  have hc : Continuous (fun p : ℝ × (ι → ℝ) =>
      tiltedMean ν m (fun z => F (p.2+Real.sqrt p.1 • z)) (fun z => A (p.2+Real.sqrt p.1 • z))) := by
    apply (hn.div hd (fun q => (partition_pos m (he.affine_integrable hν q.2 q.1)).ne')).comp
      ((Real.continuous_sqrt.comp continuous_fst).prodMk continuous_snd)
  exact hc.congr fun p => (clockTest_eq_all hF.continuous hA.continuous m p.1 p.2).symm

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 

def clockGradient (m : ℝ) (F G A A₁ : (ι → ℝ) → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  clockTest m F A₁ t x + m*(clockTest m F (fun y => A y*G y) t x-
    clockTest m F A t x*clockTest m F G t x)

 theorem hasDerivAt_clockTest_source {F G A A₁ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hA : BddSmooth 0 A)
    (hA₁ : BddSmooth 0 A₁) {v : ι → ℝ}
    (hdF : ∀ x t, HasDerivAt (fun s : ℝ => F (x+s • v)) (G (x+t • v)) t)
    (hdA : ∀ x t, HasDerivAt (fun s : ℝ => A (x+s • v)) (A₁ (x+t • v)) t)
    (m t : ℝ) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => clockTest m F A t (x+r • v))
      (clockGradient m F G A A₁ t (x+s • v)) s := by
  obtain ⟨K,hK,hbK⟩ := hG.bound
  obtain ⟨B,hB,hbB⟩ := hA.bound
  obtain ⟨B₁,hB₁,hbB₁⟩ := hA₁.bound
  exact hasDerivAt_shiftedMean hK (add_nonneg hB hB₁) hF.continuous hG.continuous
    hA.continuous hA₁.continuous hdF hdA hbK (fun y => (hbB y).trans (by linarith))
    (fun y => (hbB₁ y).trans (by linarith))
    (fun y => (exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m y) x s

 theorem clockGradient_continuous {F G A A₁ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hA : BddSmooth 0 A)
    (hA₁ : BddSmooth 0 A₁) (m : ℝ) :
    Continuous (fun p : ℝ × (ι → ℝ) => clockGradient m F G A A₁ p.1 p.2) :=
  (clockTest_continuous hF hA₁ m).add (((clockTest_continuous hF (hA.mul hG) m).sub
    ((clockTest_continuous hF hA m).mul (clockTest_continuous hF hG m))).const_mul m)

 theorem clockGradient_bddSmooth {k : ℕ} {F G A A₁ : (ι → ℝ) → ℝ}
    (hF : PotentialRegularity k F) (hG : BddSmooth k G) (hA : BddSmooth k A)
    (hA₁ : BddSmooth k A₁) (m t : ℝ) : BddSmooth k (clockGradient m F G A A₁ t) := by
  obtain ⟨C,hC⟩ := hF.1
  have hi (y) := (exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hC m y
  exact (hA₁.shiftedMean hF hi).add (((hA.mul hG).shiftedMean hF hi).sub
    ((hA.shiftedMean hF hi).mul (hG.shiftedMean hF hi)) |>.const_mul m)

 

def clockSecond (m : ℝ) (F G H A A₁ A₂ : (ι → ℝ) → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  clockGradient m F G A₁ A₂ t x + m*(
    clockGradient m F G (fun y => A y*G y) (fun y => A₁ y*G y+A y*H y) t x-
    (clockGradient m F G A A₁ t x*clockTest m F G t x+
      clockTest m F A t x*clockGradient m F G G H t x))

 theorem hasDerivAt_clockGradient_source {F G H A A₁ A₂ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hH : BddSmooth 0 H)
    (hA : BddSmooth 0 A) (hA₁ : BddSmooth 0 A₁) (hA₂ : BddSmooth 0 A₂) {v : ι → ℝ}
    (hdF : ∀ x t, HasDerivAt (fun s : ℝ => F (x+s • v)) (G (x+t • v)) t)
    (hdG : ∀ x t, HasDerivAt (fun s : ℝ => G (x+s • v)) (H (x+t • v)) t)
    (hdA : ∀ x t, HasDerivAt (fun s : ℝ => A (x+s • v)) (A₁ (x+t • v)) t)
    (hdA₁ : ∀ x t, HasDerivAt (fun s : ℝ => A₁ (x+s • v)) (A₂ (x+t • v)) t)
    (m t : ℝ) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => clockGradient m F G A A₁ t (x+r • v))
      (clockSecond m F G H A A₁ A₂ t (x+s • v)) s := by
  have h1 := hasDerivAt_clockTest_source hF hG hA₁ hA₂ hdF hdA₁ m t x s
  have h2 := hasDerivAt_clockTest_source hF hG (hA.mul hG)
    ((hA₁.mul hG).add (hA.mul hH)) hdF (fun y r => (hdA y r).mul (hdG y r)) m t x s
  have h3 := hasDerivAt_clockTest_source hF hG hA hA₁ hdF hdA m t x s
  have h4 := hasDerivAt_clockTest_source hF hG hG hH hdF hdG m t x s
  exact h1.add ((h2.sub (h3.mul h4)).const_mul m)

 theorem clockSecond_continuous {F G H A A₁ A₂ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hH : BddSmooth 0 H)
    (hA : BddSmooth 0 A) (hA₁ : BddSmooth 0 A₁) (hA₂ : BddSmooth 0 A₂) (m : ℝ) :
    Continuous (fun p : ℝ × (ι → ℝ) => clockSecond m F G H A A₁ A₂ p.1 p.2) :=
  (clockGradient_continuous hF hG hA₁ hA₂ m).add
    (((clockGradient_continuous hF hG (hA.mul hG) ((hA₁.mul hG).add (hA.mul hH)) m).sub
      (((clockGradient_continuous hF hG hA hA₁ m).mul (clockTest_continuous hF hG m)).add
        ((clockTest_continuous hF hA m).mul (clockGradient_continuous hF hG hG hH m)))).const_mul m)

 theorem clockSecond_bddSmooth {k : ℕ} {F G H A A₁ A₂ : (ι → ℝ) → ℝ}
    (hF : PotentialRegularity k F) (hG : BddSmooth k G) (hH : BddSmooth k H)
    (hA : BddSmooth k A) (hA₁ : BddSmooth k A₁) (hA₂ : BddSmooth k A₂) (m t : ℝ) :
    BddSmooth k (clockSecond m F G H A A₁ A₂ t) := by
  obtain ⟨C,hC⟩ := hF.1
  have hi (y) := (exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hC m y
  exact (clockGradient_bddSmooth hF hG hA₁ hA₂ m t).add
    (((clockGradient_bddSmooth hF hG (hA.mul hG) ((hA₁.mul hG).add (hA.mul hH)) m t).sub
      (((clockGradient_bddSmooth hF hG hA hA₁ m t).mul (hG.shiftedMean hF hi)).add
        ((hA.shiftedMean hF hi).mul (clockGradient_bddSmooth hF hG hG hH m t)))).const_mul m)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 theorem clockContinuation_eq_all {F : (ι → ℝ) → ℝ} (hF : Continuous F)
    (m t : ℝ) (x : ι → ℝ) :
    clockContinuation m F t x = Real.log (∫ z, Real.exp (m*F (x+Real.sqrt t • z))
      ∂Measure.pi fun _ : ι => gaussianReal 0 1)/m := by
  have hi := integral_isotropicGaussian (Real.toNNReal t)
    (f := fun z => Real.exp (m*F (x+z))) (by fun_prop)
  rw [sqrt_coe_toNNReal] at hi
  exact congrArg (fun z => Real.log z/m) hi.symm

 theorem clockContinuation_continuous {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) :
    Continuous (fun p : ℝ × (ι → ℝ) => clockContinuation m F p.1 p.2) := by
  have he := ExpNormBounded.exp_lipschitz hF m
  have hd := he.continuous_integral_affine (exponentialIncrement_gaussian (fun _ : ι => 1))
  have hlog := hd.log (fun q => (partition_pos m (he.affine_integrable
    (exponentialIncrement_gaussian (fun _ : ι => 1)) q.2 q.1)).ne')
  have hh := (hlog.div_const m).comp
    ((Real.continuous_sqrt.comp continuous_fst).prodMk continuous_snd)
  exact hh.congr fun p => (clockContinuation_eq_all hF.continuous m p.1 p.2).symm

 theorem hasDerivAt_clockContinuation_source {F G : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) {v : ι → ℝ}
    (hdF : ∀ x t, HasDerivAt (fun s : ℝ => F (x+s • v)) (G (x+t • v)) t)
    {m : ℝ} (hm : m ≠ 0) (t : ℝ) (x : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => clockContinuation m F t (x+r • v))
      (clockTest m F G t (x+s • v)) s := by
  obtain ⟨B,hB,hb⟩ := hG.bound
  exact hasDerivAt_continuation
    (F := fun r z => F (x+r • v+z)) (F₁ := fun r z => G (x+r • v+z)) hB hm
    (fun _ => (hF.continuous.comp (continuous_const.add continuous_id)).measurable)
    (fun _ => (hG.continuous.comp (continuous_const.add continuous_id)).measurable)
    (fun r z => by simpa only [add_assoc,add_comm z] using hdF (x+z) r)
    (fun _ _ => hb _) s ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m _)

 theorem linearGaussian_id (s : ℝ≥0) :
    linearGaussian (ContinuousLinearMap.id ℝ (ι → ℝ)) s = Measure.pi fun _ : ι => gaussianReal 0 s := by
  exact Measure.map_id

 theorem clockContinuation_add {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) {m : ℝ} (hm : m ≠ 0) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ι → ℝ) :
    clockContinuation m (clockContinuation m F t) s x = clockContinuation m F (s+t) x := by
  have h := shiftedContinuation_linearGaussian_add (ContinuousLinearMap.id ℝ (ι → ℝ))
    hF hm (Real.toNNReal s) (Real.toNNReal t) x
  rw [linearGaussian_id,linearGaussian_id,linearGaussian_id,← Real.toNNReal_add hs ht] at h
  exact h

 theorem clockTest_add {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) {m : ℝ} (hm : m ≠ 0) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ι → ℝ) :
    clockTest m (clockContinuation m F t) (clockTest m F A t) s x = clockTest m F A (s+t) x := by
  have h := shiftedMean_linearGaussian_add (ContinuousLinearMap.id ℝ (ι → ℝ))
    hF hA hm (Real.toNNReal s) (Real.toNNReal t) x
  rw [linearGaussian_id,linearGaussian_id,linearGaussian_id,← Real.toNNReal_add hs ht] at h
  exact h

 theorem isotropicGaussian_zero : (Measure.pi fun _ : ι => gaussianReal 0 0) = Measure.dirac 0 := by
  have h := (isotropicGaussian_preserving (ι := ι) 0).map_eq
  simpa only [NNReal.coe_zero,Real.sqrt_zero,zero_smul,Measure.map_const,measure_univ,one_smul] using h.symm

 theorem clockTest_zero {F A : (ι → ℝ) → ℝ} (m : ℝ) (x : ι → ℝ) : clockTest m F A 0 x = A x := by
  unfold clockTest shiftedMean tiltedMean
  rw [Real.toNNReal_zero, isotropicGaussian_zero]
  simp

 theorem clockContinuation_zero {F : (ι → ℝ) → ℝ} {m : ℝ} (hm : m ≠ 0) (x : ι → ℝ) :
    clockContinuation m F 0 x = F x := by
  unfold clockContinuation shiftedContinuation
  rw [Real.toNNReal_zero, isotropicGaussian_zero]
  simp [hm]

 theorem clockTest_add_test {F A B : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (hB : BddSmooth 0 B) (m t : ℝ) (x : ι → ℝ) :
    clockTest m F (fun y => A y+B y) t x = clockTest m F A t x+clockTest m F B t x :=
  shiftedMean_add hA hB ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x)

 theorem clockTest_const_mul {F A : (ι → ℝ) → ℝ} (c m t : ℝ) (x : ι → ℝ) :
    clockTest m F (fun y => c*A y) t x = c*clockTest m F A t x := shiftedMean_const_mul c x

 theorem clockTest_sum {κ : Type*} [Fintype κ] {F : (ι → ℝ) → ℝ} {A : κ → (ι → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : ∀ i, BddSmooth 0 (A i)) (m t : ℝ) (x : ι → ℝ) :
    clockTest m F (fun y => ∑ i, A i y) t x = ∑ i, clockTest m F (A i) t x :=
  shiftedMean_sum hA ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 theorem clockGradient_sum {F A : (ι → ℝ) → ℝ} {G A₁ : κ → (ι → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hA₁ : ∀ i, BddSmooth 0 (A₁ i))
    (v : κ → ℝ) (m t : ℝ) (x : ι → ℝ) :
    clockGradient m F (fun y => ∑ i, v i*G i y) A (fun y => ∑ i, v i*A₁ i y) t x =
      ∑ i, v i*clockGradient m F (G i) A (A₁ i) t x := by
  have he : (fun y => A y*(∑ i, v i*G i y)) = fun y => ∑ i, v i*(A y*G i y) := by
    funext y
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [clockGradient,he,clockTest_sum hF (fun i => (hA₁ i).const_mul (v i)),
    clockTest_sum hF (fun i => (hA.mul (hG i)).const_mul (v i)),
    clockTest_sum hF (fun i => (hG i).const_mul (v i)),clockTest_const_mul]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 

 theorem clockSecond_add_drift {F G H A A₁ A₂ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hH : BddSmooth 0 H)
    (hA : BddSmooth 0 A) (hA₁ : BddSmooth 0 A₁) (hA₂ : BddSmooth 0 A₂)
    (m t : ℝ) (x : ι → ℝ) :
    clockSecond m F G H A A₁ A₂ t x+
        2*m*clockGradient m F G A A₁ t x*clockTest m F G t x =
      clockTest m F (fun y => A₂ y+2*m*A₁ y*G y+A y*(m*H y+m^2*(G y)^2)) t x-
        clockTest m F A t x*clockTest m F (fun y => m*H y+m^2*(G y)^2) t x := by
  have hsG : BddSmooth 0 (fun y => (G y)^2) := by simpa only [pow_two] using hG.mul hG
  have he1 : (fun y => A₂ y+2*m*A₁ y*G y+A y*(m*H y+m^2*(G y)^2)) =
      fun y => A₂ y+(2*m)*(A₁ y*G y)+m*(A y*H y)+m^2*((A y*G y)*G y) := by
    funext y; ring
  have he2 : (fun y => G y*G y) = fun y => (G y)^2 := by funext y; ring
  rw [he1]
  simp only [clockSecond,clockGradient,he2]
  rw [clockTest_add_test hF (hA₁.mul hG) (hA.mul hH),
    clockTest_add_test hF (((hA₂.add ((hA₁.mul hG).const_mul (2*m))).add
      ((hA.mul hH).const_mul m))) (((hA.mul hG).mul hG).const_mul (m^2)),
    clockTest_add_test hF (hA₂.add ((hA₁.mul hG).const_mul (2*m))) ((hA.mul hH).const_mul m),
    clockTest_add_test hF hA₂ ((hA₁.mul hG).const_mul (2*m)),
    clockTest_add_test hF (hH.const_mul m) (hsG.const_mul (m^2))]
  simp only [clockTest_const_mul]
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.GaussianCalculus
open Filter Set
open scoped Topology

 
theorem hasDerivAt_bivariate_chain {f f₁ f₂ : ℝ → ℝ → ℝ} {u v : ℝ → ℝ}
    {u' v' t : ℝ}
    (h₁ : ∀ᶠ p in 𝓝 (u t,v t), HasDerivAt (fun r => f r p.2) (f₁ p.1 p.2) p.1)
    (h₂ : ∀ᶠ p in 𝓝 (u t,v t), HasDerivAt (fun r => f p.1 r) (f₂ p.1 p.2) p.2)
    (hc₁ : ContinuousAt (fun p : ℝ × ℝ => f₁ p.1 p.2) (u t,v t))
    (hc₂ : ContinuousAt (fun p : ℝ × ℝ => f₂ p.1 p.2) (u t,v t))
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun r => f (u r) (v r)) (f₁ (u t) (v t)*u'+f₂ (u t) (v t)*v') t := by
  have hh := hasStrictFDerivAt_uncurry_coprod
    (f := f)
    (f₁ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (f₁ a b))
    (f₂ := fun a b => ContinuousLinearMap.toSpanSingleton ℝ (f₂ a b))
    (h₁.mono fun _ h => h.hasFDerivAt) (h₂.mono fun _ h => h.hasFDerivAt)
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hc₁)
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hc₂)
  have hd := hh.hasFDerivAt.comp_hasDerivAt t (hu.prodMk hv)
  change HasDerivAt (fun r => f (u r) (v r))
    (u'*f₁ (u t) (v t)+v'*f₂ (u t) (v t)) t at hd
  simpa only [mul_comm] using hd

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 def clockTestDerivative {n : ℕ} (m : ℝ) (F : (Fin (n+1) → ℝ) → ℝ)
    (G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (A : (Fin (n+1) → ℝ) → ℝ) (A₁ A₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  (1/2:ℝ)*(clockTest m F (testedHeatTrace m G H A A₁ A₂) t x-
    clockTest m F A t x*clockTest m F (potentialHeatTrace m G H) t x)

 theorem potentialHeatTrace_bddSmooth {κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {k : ℕ} {G H : κ → E → ℝ}
    (hG : ∀ i, BddSmooth k (G i)) (hH : ∀ i, BddSmooth k (H i)) (m : ℝ) :
    BddSmooth k (potentialHeatTrace m G H) := by
  apply BddSmooth.sum Finset.univ
  intro i _
  simpa only [pow_two] using ((hH i).const_mul m).add (((hG i).mul (hG i)).const_mul (m*m))

 theorem testedHeatTrace_bddSmooth {κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {k : ℕ} {G H A₁ A₂ : κ → E → ℝ} {A : E → ℝ}
    (hG : ∀ i, BddSmooth k (G i)) (hH : ∀ i, BddSmooth k (H i))
    (hA : BddSmooth k A) (hA₁ : ∀ i, BddSmooth k (A₁ i)) (hA₂ : ∀ i, BddSmooth k (A₂ i)) (m : ℝ) :
    BddSmooth k (testedHeatTrace m G H A A₁ A₂) := by
  apply BddSmooth.sum Finset.univ
  intro i _
  have hp : BddSmooth k (fun y => m*H i y+m^2*(G i y)^2) := by
    simpa only [pow_two] using ((hH i).const_mul m).add (((hG i).mul (hG i)).const_mul (m*m))
  exact ((hA₂ i).add (((hA₁ i).const_mul (2*m)).mul (hG i))).add (hA.mul hp)

 theorem clockTestDerivative_continuous {n : ℕ}
    {F A : (Fin (n+1) → ℝ) → ℝ} {G H A₁ A₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hA₁ : ∀ i, BddSmooth 0 (A₁ i)) (hA₂ : ∀ i, BddSmooth 0 (A₂ i)) (m : ℝ) :
    Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => clockTestDerivative m F G H A A₁ A₂ p.1 p.2) :=
  ((clockTest_continuous hF (testedHeatTrace_bddSmooth hG hH hA hA₁ hA₂ m) m).sub
    ((clockTest_continuous hF hA m).mul
      (clockTest_continuous hF (potentialHeatTrace_bddSmooth hG hH m) m))).const_mul (1/2:ℝ)

 

 theorem hasDerivAt_clockTest_joint {n : ℕ}
    {F A : (Fin (n+1) → ℝ) → ℝ} {G H A₁ A₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hA₁ : ∀ i, BddSmooth 0 (A₁ i)) (hA₂ : ∀ i, BddSmooth 0 (A₂ i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hdG : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1))
      (H i (x+t • Pi.single i 1)) t)
    (hdA : ∀ x v t, HasDerivAt (fun s : ℝ => A (x+s • v))
      (∑ i, v i*A₁ i (x+t • v)) t)
    (hdA₁ : ∀ i x t, HasDerivAt (fun s : ℝ => A₁ i (x+s • Pi.single i 1))
      (A₂ i (x+t • Pi.single i 1)) t)
    (m : ℝ) (x v : Fin (n+1) → ℝ) {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ht : 0 < a t) :
    HasDerivAt (fun r => clockTest m F A (a r) (x+b r • v))
      (clockTestDerivative m F G H A A₁ A₂ (a t) (x+b t • v)*a'+
        (∑ i, v i*clockGradient m F (G i) A (A₁ i) (a t) (x+b t • v))*b') t := by
  have hsumG : BddSmooth 0 (fun y => ∑ i, v i*G i y) :=
    BddSmooth.sum Finset.univ (fun i _ => (hG i).const_mul (v i))
  have hsumA : BddSmooth 0 (fun y => ∑ i, v i*A₁ i y) :=
    BddSmooth.sum Finset.univ (fun i _ => (hA₁ i).const_mul (v i))
  apply hasDerivAt_bivariate_chain
    (f := fun q s => clockTest m F A q (x+s • v))
    (f₁ := fun q s => clockTestDerivative m F G H A A₁ A₂ q (x+s • v))
    (f₂ := fun q s => ∑ i, v i*clockGradient m F (G i) A (A₁ i) q (x+s • v))
    ?_ ?_ ?_ ?_ ha hb
  · filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds ht)] with p hp
    exact (hasDerivWithinAt_clockTest hF hA hG hH hA₁ hA₂ hdF hdG hdA hdA₁ m _ hp.le).hasDerivAt
      (Ici_mem_nhds hp)
  · exact Eventually.of_forall fun p => by
      have h := hasDerivAt_clockTest_source hF hsumG hA hsumA
        (fun y r => hdF y v r) (fun y r => hdA y v r) m p.1 x p.2
      rw [clockGradient_sum hF hA hG hA₁] at h
      exact h
  · exact ((clockTestDerivative_continuous hF hA hG hH hA₁ hA₂ m).comp
      (continuous_fst.prodMk (continuous_const.add (continuous_snd.smul continuous_const)))).continuousAt
  · exact ((continuous_finsetSum _ fun i _ =>
      (clockGradient_continuous hF (hG i) hA (hA₁ i) m).const_mul (v i)).comp
      (continuous_fst.prodMk (continuous_const.add (continuous_snd.smul continuous_const)))).continuousAt

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 

theorem clockTestDerivative_eq_generator {n : ℕ}
    {F A : (Fin (n+1) → ℝ) → ℝ} {G H A₁ A₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hA₁ : ∀ i, BddSmooth 0 (A₁ i)) (hA₂ : ∀ i, BddSmooth 0 (A₂ i)) (m t : ℝ) (x : Fin (n+1) → ℝ) :
    clockTestDerivative m F G H A A₁ A₂ t x =
      (1/2:ℝ)*∑ i, (clockSecond m F (G i) (H i) A (A₁ i) (A₂ i) t x+
        2*m*clockGradient m F (G i) A (A₁ i) t x*clockTest m F (G i) t x) := by
  have hP (i) : BddSmooth 0 (fun y => m*H i y+m^2*(G i y)^2) := by
    simpa only [pow_two] using ((hH i).const_mul m).add (((hG i).mul (hG i)).const_mul (m*m))
  have hW (i) : BddSmooth 0 (fun y => A₂ i y+2*m*A₁ i y*G i y+A y*(m*H i y+m^2*(G i y)^2)) :=
    ((hA₂ i).add (((hA₁ i).const_mul (2*m)).mul (hG i))).add (hA.mul (hP i))
  unfold clockTestDerivative testedHeatTrace potentialHeatTrace
  rw [clockTest_sum hF hW, clockTest_sum hF hP, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (clockSecond_add_drift hF (hG i) (hH i) hA (hA₁ i) (hA₂ i) m t x).symm

 theorem hasDerivAt_clockTest_source_vector {n : ℕ}
    {F A : (Fin (n+1) → ℝ) → ℝ} {G A₁ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ}
    {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hA₁ : ∀ i, BddSmooth 0 (A₁ i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hdA : ∀ x v t, HasDerivAt (fun s : ℝ => A (x+s • v))
      (∑ i, v i*A₁ i (x+t • v)) t)
    (m t : ℝ) (x v : Fin (n+1) → ℝ) (s : ℝ) :
    HasDerivAt (fun r => clockTest m F A t (x+r • v))
      (∑ i, v i*clockGradient m F (G i) A (A₁ i) t (x+s • v)) s := by
  have hsumG : BddSmooth 0 (fun y => ∑ i, v i*G i y) :=
    BddSmooth.sum Finset.univ (fun i _ => (hG i).const_mul (v i))
  have hsumA : BddSmooth 0 (fun y => ∑ i, v i*A₁ i y) :=
    BddSmooth.sum Finset.univ (fun i _ => (hA₁ i).const_mul (v i))
  have h := hasDerivAt_clockTest_source hF hsumG hA hsumA
    (fun y r => hdF y v r) (fun y r => hdA y v r) m t x s
  rw [clockGradient_sum hF hA hG hA₁] at h
  exact h

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

 
def AbsBounded {X : Type*} (f : X → ℝ) : Prop := ∃ K, 0 ≤ K ∧ ∀ x, |f x| ≤ K

 theorem AbsBounded.add {X : Type*} {f g : X → ℝ} (hf : AbsBounded f) (hg : AbsBounded g) :
    AbsBounded (fun x => f x+g x) := by
  obtain ⟨B,hB,hb⟩ := hf; obtain ⟨C,hC,hc⟩ := hg
  exact ⟨B+C,add_nonneg hB hC,fun x => (abs_add_le _ _).trans (add_le_add (hb x) (hc x))⟩
 theorem AbsBounded.neg {X : Type*} {f : X → ℝ} (hf : AbsBounded f) : AbsBounded (fun x => -f x) := by
  simpa only [AbsBounded,abs_neg] using hf
 theorem AbsBounded.sub {X : Type*} {f g : X → ℝ} (hf : AbsBounded f) (hg : AbsBounded g) :
    AbsBounded (fun x => f x-g x) := by simpa only [sub_eq_add_neg] using hf.add hg.neg
 theorem AbsBounded.mul {X : Type*} {f g : X → ℝ} (hf : AbsBounded f) (hg : AbsBounded g) :
    AbsBounded (fun x => f x*g x) := by
  obtain ⟨B,hB,hb⟩ := hf; obtain ⟨C,hC,hc⟩ := hg
  refine ⟨B*C,mul_nonneg hB hC,fun x => ?_⟩
  rw [abs_mul]; exact mul_le_mul (hb x) (hc x) (abs_nonneg _) hB
 theorem AbsBounded.const_mul {X : Type*} {f : X → ℝ} (hf : AbsBounded f) (c : ℝ) :
    AbsBounded (fun x => c*f x) := by
  exact (show AbsBounded (fun _ : X => c) from ⟨|c|,abs_nonneg _,fun _ => le_rfl⟩).mul hf
 theorem AbsBounded.sum {X κ : Type*} [Fintype κ] {f : κ → X → ℝ} (hf : ∀ i, AbsBounded (f i)) :
    AbsBounded (fun x => ∑ i, f i x) := by
  choose B hB hb using hf
  exact ⟨∑ i, B i,Finset.sum_nonneg fun i _ => hB i,fun x =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hb i x)⟩

 theorem clockTest_absBounded {ι : Type*} [Fintype ι] {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (m : ℝ) :
    AbsBounded (fun p : ℝ × (ι → ℝ) => clockTest m F A p.1 p.2) := by
  obtain ⟨B,hB,hb⟩ := hA.bound
  refine ⟨B,hB, fun p => ?_⟩
  exact abs_tiltedMean_le (hA.continuous.comp (continuous_const.add continuous_id)).measurable
    ((exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal p.1)).integrable_shift hF m p.2)
    (fun z => hb (p.2+z))

 theorem clockGradient_absBounded {ι : Type*} [Fintype ι] {F G A A₁ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hA : BddSmooth 0 A)
    (hA₁ : BddSmooth 0 A₁) (m : ℝ) :
    AbsBounded (fun p : ℝ × (ι → ℝ) => clockGradient m F G A A₁ p.1 p.2) :=
  (clockTest_absBounded hF hA₁ m).add (((clockTest_absBounded hF (hA.mul hG) m).sub
    ((clockTest_absBounded hF hA m).mul (clockTest_absBounded hF hG m))).const_mul m)

 theorem clockSecond_absBounded {ι : Type*} [Fintype ι] {F G H A A₁ A₂ : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : BddSmooth 0 G) (hH : BddSmooth 0 H)
    (hA : BddSmooth 0 A) (hA₁ : BddSmooth 0 A₁) (hA₂ : BddSmooth 0 A₂) (m : ℝ) :
    AbsBounded (fun p : ℝ × (ι → ℝ) => clockSecond m F G H A A₁ A₂ p.1 p.2) :=
  (clockGradient_absBounded hF hG hA₁ hA₂ m).add
    (((clockGradient_absBounded hF hG (hA.mul hG) ((hA₁.mul hG).add (hA.mul hH)) m).sub
      (((clockGradient_absBounded hF hG hA hA₁ m).mul (clockTest_absBounded hF hG m)).add
        ((clockTest_absBounded hF hA m).mul (clockGradient_absBounded hF hG hG hH m)))).const_mul m)

 theorem clockTestDerivative_absBounded {n : ℕ} {F A : (Fin (n+1) → ℝ) → ℝ}
    {G H A₁ A₂ : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hA₁ : ∀ i, BddSmooth 0 (A₁ i)) (hA₂ : ∀ i, BddSmooth 0 (A₂ i)) (m : ℝ) :
    AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => clockTestDerivative m F G H A A₁ A₂ p.1 p.2) :=
  ((clockTest_absBounded hF (testedHeatTrace_bddSmooth hG hH hA hA₁ hA₂ m) m).sub
    ((clockTest_absBounded hF hA m).mul
      (clockTest_absBounded hF (potentialHeatTrace_bddSmooth hG hH m) m))).const_mul (1/2:ℝ)

end SKFluctuations.Hierarchy

end

end OAI
