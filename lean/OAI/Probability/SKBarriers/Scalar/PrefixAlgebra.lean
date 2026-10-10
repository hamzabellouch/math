import Mathlib
import OAI.Probability.SKBarriers.Scalar.ThermalMoments
import OAI.Probability.SKBarriers.Gaussian.GaussianAverageProduct
import OAI.Probability.SKBarriers.Gaussian.SmoothObservables

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section TerminalMarginal
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyTerminalGibbs_eq_affineGibbs (n : ℕ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) (z : ParameterSpace n) :
    hierarchyTerminalGibbs n U s z = affineGibbs (fun _ => 0) U z s := by
  have hp : 0 < ∑ t, Real.exp (U t z) := by
    simpa only [zero_add] using affinePartition_pos (fun _ => 0) U z
  simp only [hierarchyTerminalGibbs,affineGibbs,affineLogPartition,zero_add,Real.exp_sub,
    Real.exp_log hp]

theorem hierarchyGaussian_terminal_marginal (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (h : ParameterSpace n → ℝ)
    (hh : Continuous h) (hb : HasExpGrowth h) :
    (∫ sz, c sz.1*h sz.2 ∂hierarchyGaussianLaw n m U) =
      ∫ z, affineMoment (fun _ => 0) U c z*h z
        ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0 := by
  let V := hierarchyPotential n m U
  have hV (s : S) := hierarchyPotential_boundedDerivs n m U s
  have he (s : S) : HasExpGrowth (fun z => Real.exp (V s z)) := by
    simpa only [one_mul] using ((hV s).exp_growths 1).1
  have hce (s : S) := Real.continuous_exp.comp (hV s).1.continuous
  have hi (s : S) : Integrable (fun z => c s*h z*Real.exp (V s z)) (fiberGaussian n 0) :=
    (((HasExpGrowth.const (c s)).mul hb).mul (he s)).integrable_fiberGaussian n
      ((continuous_const.mul hh).mul (hce s)) 0
  have hI : Integrable (fun sz : S × ParameterSpace n => c sz.1*h sz.2*
      Real.exp (hierarchyPotential n m U sz.1 sz.2))
      ((Measure.count : Measure S).prod (fiberGaussian n 0)) :=
    finite_fiberGaussian_integrable n (fun s z => c s*h z*Real.exp (V s z))
      (fun s => (continuous_const.mul hh).mul (hce s)) hi
  rw [hierarchyGaussianLaw_eq_spinGaussian,spinGaussianLaw,integral_tilted_real_eq_div,
    hierarchyPotential_normalized,div_one,integral_prod _ hI,integral_count]
  rw [← integral_finsetSum _ (fun s _ => hi s),hierarchyPathLaw_integral n m _
    (affineLogPartition_boundedDerivs (fun _ => 0) U)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [V,hierarchyPotential,← hierarchy_fixed_spin_density]
  change (∑ s, c s*h z*(hierarchyPathWeight n m (affineLogPartition (fun _ => 0) U) z *
    hierarchyTerminalGibbs n U s z)) = _
  simp only [hierarchyTerminalGibbs_eq_affineGibbs,affineMoment,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

end TerminalMarginal

theorem hierarchyMomentLevel_tower (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (j l : Fin (n+1)) (hjl : j ≤ l) :
    hierarchyMomentLevel n m f (hierarchyMomentLevel n m f g l) j =
      hierarchyMomentLevel n m f g j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    revert hjl
    refine Fin.lastCases (fun hjl => ?_) (fun j hjl => ?_) j
    · have hl : l = Fin.last (n+1) := le_antisymm (Fin.le_last l) hjl
      subst l
      simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · revert hjl
      refine Fin.lastCases (fun _ => ?_) (fun l hjl => ?_) l
      · simp only [hierarchyMomentLevel,Fin.lastCases_last]
      · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
        rw [gaussianAverage_const_prefix hf]
        funext z
        exact congrFun (ih (fun i => m i.castSucc) _ _ (hf.gaussianStep _) j l hjl) z.1

theorem hierarchyPathLaw_integrable (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g)
    {C : ℝ} (hb : ∀ z, ‖g z‖ ≤ C) (x : ℝ) :
    Integrable g (hierarchyPathLaw n m f x) := by
  let := hierarchyPathLaw_probability n m f hf x
  exact Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hb)

end SK.Analytic

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathLaw_moment_orthogonality (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C)
    (j l : Fin (n+1)) (hjl : j ≤ l) (x : ℝ) :
    let A := hierarchyMomentLevel n m f g j
    let B := hierarchyMomentLevel n m f g l
    (∫ z, (B z-A z)^2 ∂hierarchyPathLaw n m f x) =
      (∫ z, (B z)^2 ∂hierarchyPathLaw n m f x)-
      ∫ z, (A z)^2 ∂hierarchyPathLaw n m f x := by
  dsimp only
  let A := hierarchyMomentLevel n m f g j
  let B := hierarchyMomentLevel n m f g l
  let μ := hierarchyPathLaw n m f x
  have hA := hierarchyMomentLevel_bounded_continuous n m f g hf hg hC hb j
  have hB := hierarchyMomentLevel_bounded_continuous n m f g hf hg hC hb l
  have bounded (u v : ParameterSpace n → ℝ) (hu : ∀ z, ‖u z‖ ≤ C) (hv : ∀ z, ‖v z‖ ≤ C)
      (z) : ‖u z*v z‖ ≤ C*C := by
    rw [norm_mul]
    exact mul_le_mul (hu z) (hv z) (norm_nonneg _) hC
  have ihAA : Integrable (fun z => A z*A z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hA.1.mul hA.1) (bounded A A hA.2 hA.2) x
  have ihBB : Integrable (fun z => B z*B z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hB.1.mul hB.1) (bounded B B hB.2 hB.2) x
  have ihAB : Integrable (fun z => A z*B z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hA.1.mul hB.1) (bounded A B hA.2 hB.2) x
  have ht := hierarchyPathLaw_prefix_mul n m f B g hf hB.1 hg hC hC hB.2 hb j x
  rw [hierarchyMomentLevel_tower n m f g hf j l hjl] at ht
  change (∫ z, A z*B z ∂μ) = ∫ z, A z*A z ∂μ at ht
  change (∫ z, (B z-A z)^2 ∂μ) = (∫ z, (B z)^2 ∂μ)-∫ z, (A z)^2 ∂μ
  have he : (fun z => (B z-A z)^2) = fun z => B z*B z-(2*(A z*B z))+A z*A z := by
    funext z
    ring
  rw [he]
  have ha := integral_add (μ := μ)
    (f := fun z => B z*B z-2*(A z*B z)) (g := fun z => A z*A z)
    (ihBB.sub (ihAB.const_mul 2)) ihAA
  rw [ha]
  have hs := integral_sub (μ := μ)
    (f := fun z => B z*B z) (g := fun z => 2*(A z*B z)) ihBB (ihAB.const_mul 2)
  rw [hs,integral_const_mul,ht]
  simp only [pow_two]
  ring

theorem hierarchyPathLaw_moment_square_mono (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C)
    (j l : Fin (n+1)) (hjl : j ≤ l) (x : ℝ) :
    (∫ z, (hierarchyMomentLevel n m f g j z)^2 ∂hierarchyPathLaw n m f x) ≤
      ∫ z, (hierarchyMomentLevel n m f g l z)^2 ∂hierarchyPathLaw n m f x := by
  have H := integral_nonneg (μ := hierarchyPathLaw n m f x)
    (f := fun z : ParameterSpace n => (hierarchyMomentLevel n m f g l z-hierarchyMomentLevel n m f g j z)^2)
    (fun z => sq_nonneg (hierarchyMomentLevel n m f g l z-hierarchyMomentLevel n m f g j z))
  rw [hierarchyPathLaw_moment_orthogonality n m f g hf hg hC hb j l hjl x] at H
  exact sub_nonneg.mp H

end SK.Analytic

namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_retained (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (j l : Fin (n+1)) (hjl : j ≤ l) :
    hierarchyMomentLevel n m f (hierarchyMomentLevel n m f g j) l =
      hierarchyMomentLevel n m f g j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    revert hjl
    refine Fin.lastCases (fun _ => ?_) (fun l hjl => ?_) l
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · revert hjl
      refine Fin.lastCases (fun hjl => ?_) (fun j hjl => ?_) j
      · exact (Nat.not_le_of_gt l.isLt hjl).elim
      · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
        rw [gaussianAverage_const_prefix hf]
        funext z
        exact congrFun (ih (fun i => m i.castSucc) _ _ (hf.gaussianStep _) j l hjl) z.1

theorem hierarchyMomentLevel_family {I : Type} (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (g : I → ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (F : (I → ℝ) → ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => F (fun i => hierarchyMomentLevel n m f (g i) j z)) j =
      fun z => F (fun i => hierarchyMomentLevel n m f (g i) j z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      let G : ParameterSpace n → ℝ := fun z => F (fun i =>
        hierarchyMomentLevel n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
          (gaussianAverage (m (Fin.last n)) f (g i)) j z)
      change (fun z : ParameterSpace (n+1) => hierarchyMomentLevel n (fun i => m i.castSucc)
        (gaussianStep (m (Fin.last n)) f) (gaussianAverage (m (Fin.last n)) f (fun z => G z.1)) j z.1) =
        fun z : ParameterSpace (n+1) => G z.1
      rw [gaussianAverage_const_prefix hf]
      funext z
      exact congrFun (ih (fun i => m i.castSucc) _ (fun i => gaussianAverage (m (Fin.last n)) f (g i))
        (hf.gaussianStep _) j) z.1

theorem hierarchyPathLaw_fixed_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g) (hh : Continuous h)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hgb : ∀ z, ‖g z‖ ≤ C) (hhb : ∀ z, ‖h z‖ ≤ D)
    (j : Fin (n+1)) (hj : hierarchyMomentLevel n m f h j = h) (x : ℝ) :
    (∫ z, h z*g z ∂hierarchyPathLaw n m f x) =
      ∫ z, h z*hierarchyMomentLevel n m f g j z ∂hierarchyPathLaw n m f x := by
  have H := hierarchyPathLaw_prefix_mul n m f g h hf hg hh hC hD hgb hhb j x
  rwa [hj] at H

section SpinMeans
variable {S : Type} [Fintype S] [Nonempty S]

def hierarchySpinMean (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (c : S → ℝ) (j : Fin (n+1)) : ParameterSpace n → ℝ :=
  hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U) (affineMoment (fun _ => 0) U c) j

theorem hierarchySpinMean_regular (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ s, ‖c s‖ ≤ C) (j : Fin (n+1)) :
    Continuous (hierarchySpinMean n m U c j) ∧ ∀ z, ‖hierarchySpinMean n m U c j z‖ ≤ C :=
  hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (affineMoment_continuous (fun _ => 0) U c) hC (affineMoment_norm_le (fun _ => 0) U c hc) j

theorem hierarchyLevel_spinMean (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (j : Fin (n+1))
    (u : ParameterSpace n) (hu : TailZero n j u) (hU : ∀ s, U s u = c s) :
    directionalGradient (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) u =
      hierarchySpinMean n m U c j := by
  funext z
  rw [directionalGradient,hierarchyLevel_gradient n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) j u z hu]
  have he : directionalGradient (affineLogPartition (fun _ => 0) U) u = affineMoment (fun _ => 0) U c := by
    funext z
    simp only [directionalGradient,fderiv_affineLogPartition_apply,hU]
  rw [he]
  rfl

end SpinMeans
end SK.Analytic

end
end

end

end OAI
