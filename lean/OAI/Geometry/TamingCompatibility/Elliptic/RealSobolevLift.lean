import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.CriticalRescaleH1

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def realSobolevLift (s : ℝ) (L : G →L[ℝ] 𝓢'(E,F))
    (hL : ∀ g, MemSobolev s 2 (L g)) : G →L[ℝ] H E F s :=
  InjectiveLinearLift.continuousLift ((toDistribution E F s).restrictScalars ℝ)
    (toDistribution_injective s) L (fun g => by
      have hg : L g ∈ Set.range (toDistribution E F s) := by
        rw [range_toDistribution]; exact hL g
      exact hg)

lemma realSobolevLift_spec (s : ℝ) (L : G →L[ℝ] 𝓢'(E,F))
    (hL : ∀ g, MemSobolev s 2 (L g)) (g : G) :
    toDistribution E F s (realSobolevLift s L hL g) = L g := by
  unfold realSobolevLift
  exact InjectiveLinearLift.continuousLift_spec ((toDistribution E F s).restrictScalars ℝ)
    (toDistribution_injective s) L _ g

def realBoundedLift (s : ℝ) (hs : Module.finrank ℝ E < 2*s)
    (L : G →L[ℝ] 𝓢'(E,F)) (hL : ∀ g, MemSobolev s 2 (L g)) :
    G →L[ℝ] (E →ᵇ F) :=
  ((EuclideanSobolev.sobolevToBounded s hs).restrictScalars ℝ).comp
    (realSobolevLift s L hL)

lemma realBoundedLift_spec (s : ℝ) (hs : Module.finrank ℝ E < 2*s)
    (L : G →L[ℝ] 𝓢'(E,F)) (hL : ∀ g, MemSobolev s 2 (L g)) (g : G) :
    EuclideanSobolev.boundedDistribution (realBoundedLift s hs L hL g) = L g := by
  change EuclideanSobolev.boundedDistribution (EuclideanSobolev.sobolevToBounded s hs
    (realSobolevLift s L hL g)) = _
  rw [EuclideanSobolev.sobolevToBounded_spec,realSobolevLift_spec]
end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolev Set
open scoped SchwartzMap ENNReal LineDeriv Topology BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma schwartz_bessel_surjective (s : ℝ) : Function.Surjective
    (SchwartzMap.fourierMultiplierCLM F (fun x : E => (((1+‖x‖^2)^(s/2) : ℝ) : ℂ))) := by
  intro f
  refine ⟨SchwartzMap.fourierMultiplierCLM F (fun x : E => (((1+‖x‖^2)^(-s/2) : ℝ) : ℂ)) f,?_⟩
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  have he : ((fun x : E => (((1+‖x‖^2)^(s/2) : ℝ) : ℂ)) *
      (fun x : E => (((1+‖x‖^2)^(-s/2) : ℝ) : ℂ))) = fun _ => (1:ℂ) := by
    ext x
    simp only [Pi.mul_apply,← Complex.ofReal_mul]
    rw [← Real.rpow_add (by positivity)]
    have hz : s/2 + -s/2 = 0 := by ring
    rw [hz,Real.rpow_zero,Complex.ofReal_one]
  rw [he,SchwartzMap.fourierMultiplierCLM_const]
  simp

omit [CompleteSpace F] in
lemma schwartzLp_dense : DenseRange (fun f : 𝓢(E,F) => f.toLp 2 (volume : Measure E)) :=
  SchwartzMap.denseRange_toLpCLM (E := E) (F := F)
    (μ := (volume : Measure E)) (p := 2) (by norm_num)

omit [CompleteSpace F] in
lemma schwartzToH_coe (s : ℝ) :
    ⇑(schwartzToH (E := E) (F := F) s) =
      (fun f : 𝓢(E,F) => f.toLp 2 (volume : Measure E)) ∘
        (SchwartzMap.fourierMultiplierCLM F (fun x : E => (((1+‖x‖^2)^(s/2) : ℝ) : ℂ))) := rfl

lemma schwartzToH_dense (s : ℝ) : DenseRange (schwartzToH (E := E) (F := F) s) := by
  rw [schwartzToH_coe]
  exact schwartzLp_dense.comp (schwartz_bessel_surjective s).denseRange SchwartzMap.continuous_toLp

lemma sobolevToBounded_lipschitz_bound (s : ℝ)
    (hs : Module.finrank ℝ E < 2*(s-1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H E F s, ∀ x y : E,
      ‖sobolevToBounded s (by linarith) u x-sobolevToBounded s (by linarith) u y‖ ≤
        C*‖u‖*‖x-y‖ := by
  classical
  choose K hK hb using fun i => schwartz_first_derivative_bound (E := E) (F := F)
    s hs (stdOrthonormalBasis ℝ E i)
  let C := ∑ i, K i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hK i)
  refine ⟨C,hC,fun u x y => ?_⟩
  have hc : _root_.IsClosed {u : H E F s |
      ‖sobolevToBounded s (by linarith) u x-sobolevToBounded s (by linarith) u y‖ ≤
        C*‖u‖*‖x-y‖} := by
    apply isClosed_le
    · exact (((BoundedContinuousFunction.evalCLM ℂ x).comp
        (sobolevToBounded s (by linarith))).continuous.sub
        (((BoundedContinuousFunction.evalCLM ℂ y).comp
        (sobolevToBounded s (by linarith))).continuous)).norm
    · fun_prop
  refine (schwartzToH_dense s).induction_on u hc ?_
  intro f
  rw [sobolevToBounded_schwartz]
  change ‖f x-f y‖ ≤ C*‖schwartzToH s f‖*‖x-y‖
  apply (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => f.differentiableAt) _ (mem_univ y) (mem_univ x)
  intro z _
  calc
    ‖fderiv ℝ f z‖ ≤ ∑ i, ‖fderiv ℝ f z (stdOrthonormalBasis ℝ E i)‖ :=
      CriticalSobolev.opNorm_le_sum_basis _
    _ = ∑ i, ‖(∂_{stdOrthonormalBasis ℝ E i} f) z‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    _ ≤ ∑ i, K i*‖schwartzToH s f‖ := Finset.sum_le_sum (fun i _ => hb i f z)
    _ = C*‖schwartzToH s f‖ := (Finset.sum_mul _ _ _).symm

def sobolevEval (s : ℝ) (hs : Module.finrank ℝ E < 2*s) (x : E) :
    H E F s →L[ℂ] F :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (sobolevToBounded s hs)

lemma sobolevEval_continuous (s : ℝ) (hs : Module.finrank ℝ E < 2*(s-1)) :
    Continuous (sobolevEval (E := E) (F := F) s (by linarith)) := by
  obtain ⟨C,hC,hb⟩ := sobolevToBounded_lipschitz_bound (E := E) (F := F) s hs
  have hl : LipschitzWith ⟨C,hC⟩ (sobolevEval (E := E) (F := F) s (by linarith)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
    intro u
    change ‖sobolevToBounded s _ u x-sobolevToBounded s _ u y‖ ≤ _
    exact (hb u x y).trans_eq (by ring)
  exact hl.continuous
end TamingCompatibility.HilbertSobolev

end
end

end
end

end OAI
