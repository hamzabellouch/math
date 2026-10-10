import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedPoisson
import OAI.Geometry.PrescribedPotential.RealPoisson

namespace OAI

/-! Real Poisson Equivalence. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

local instance realPoissonEquivalenceNormedAddCommGroup (s : ℝ) :
    NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance realPoissonEquivalenceNormedSpace (s : ℝ) :
    NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance realPoissonEquivalenceIsTopologicalAddGroup (s : ℝ) :
    IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance realPoissonEquivalenceContinuousSMul (s : ℝ) :
    ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

def realAugmentedL (k : ℕ) (x₀ : X) :
    (D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) →L[ℝ]
      (D.localizers.RealSobolev (k : ℝ) × ℝ) :=
  ((D.realLOrder k ∘L ContinuousLinearMap.fst ℝ (D.localizers.RealSobolev ((k : ℝ)+2)) ℝ) -
    (D.realConstants (k : ℝ) ∘L ContinuousLinearMap.snd ℝ (D.localizers.RealSobolev ((k : ℝ)+2)) ℝ)).prod
    (D.realEvaluation ((k : ℝ)+2) x₀ ∘L ContinuousLinearMap.fst ℝ (D.localizers.RealSobolev ((k : ℝ)+2)) ℝ)

lemma realAugmentedL_bijective (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X) :
    Function.Bijective (D.realAugmentedL k x₀) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨u,c⟩ h
    have hl : D.realLOrder k u = D.realConstants (k : ℝ) c := sub_eq_zero.mp (congrArg Prod.fst h)
    have hcplx : D.completedLOrder k u.val = D.localizers.constantsOrder (k : ℝ) (c : ℂ) :=
      congrArg Subtype.val hl
    obtain ⟨a, ha, hc⟩ := D.completedLOrder_constant_kernel m hm he k u.val (c : ℂ) hcplx
    have hn : D.realEvaluation ((k : ℝ)+2) x₀ u = 0 := congrArg Prod.snd h
    change (D.pointEvaluation ((k : ℝ)+2) x₀ u.val).re = 0 at hn
    rw [ha, Localizers.constantsOrder_apply, D.pointEvaluation_embed hk] at hn
    have hi := D.localizers.real_strong hk u x₀
    rw [ha, Localizers.constantsOrder_apply, D.localizers.strong_embed _ hk] at hi
    have ha0 : a = 0 := Complex.ext hn hi
    have hu0 : u = 0 := by apply Subtype.ext; rw [ha, ha0, map_zero]; rfl
    have hc0 : c = 0 := Complex.ofReal_eq_zero.mp hc
    exact Prod.ext hu0 hc0
  · rintro ⟨f,a⟩
    refine ⟨(D.realPointPoisson m hm he P k hk x₀ f + D.realConstants ((k : ℝ)+2) a,
      D.realResidue m hm he P k f), ?_⟩
    apply Prod.ext
    · change D.realLOrder k (_ + _) - _ = f
      rw [map_add, D.realPointPoisson_equation, D.realLOrder_constants, add_zero]
      exact add_sub_cancel_right _ _
    · change D.realEvaluation ((k : ℝ)+2) x₀ (_ + _) = a
      rw [map_add, D.realPointPoisson_normalized, D.realEvaluation_constants hk, zero_add]

def realPoissonEquiv (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X) :
    (D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) ≃L[ℝ]
      (D.localizers.RealSobolev (k : ℝ) × ℝ) :=
  ContinuousLinearEquiv.ofBijective (D.realAugmentedL k x₀)
    (LinearMap.ker_eq_bot.mpr (D.realAugmentedL_bijective m hm he P k hk x₀).1)
    (LinearMap.range_eq_top.mpr (D.realAugmentedL_bijective m hm he P k hk x₀).2)

end GluingData
end GlobalElliptic

end
end

end OAI
