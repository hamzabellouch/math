import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeFormula
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFourierMode

namespace OAI

/-! The explicit cubed-prime operator and its exact action on a single
horizontal mode. The formula keeps all frequency and height dilations. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeUnitFunctionSum {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaPoint → ℂ) (x : CubicThetaPoint) : ℂ :=
  ∑' u : (Residues (p^(3-k.val)))ˣ,
    (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))))^k.val*
      F (cubicThetaPrimeCubeBranchPoint hp k
        (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))) x)

def cubicThetaPrimeCubeBottomFunctionSum {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaPoint → ℂ) (x : CubicThetaPoint) : ℂ :=
  ∑' r : Residues (p^3),F (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r) x)

def cubicThetaPrimeCubeFunctionOperator {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaPoint → ℂ) (x : CubicThetaPoint) : ℂ :=
  F (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)+
    cubicThetaPrimeCubeBottomFunctionSum hp F x+
    cubicThetaPrimeCubeUnitFunctionSum hp 1 F x+
    cubicThetaPrimeCubeUnitFunctionSum hp (⟨2,by decide⟩ : Fin 3) F x

theorem cubicThetaPrimeCubeHecke_functionOperator {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeHecke hp F).val x=cubicThetaPrimeCubeFunctionOperator hp F.val x :=
  cubicThetaPrimeCubeHecke_fourBranches hp F x

lemma cubicThetaPrimeCubeBottomFunctionSum_mode {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (f : ℝ → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeBottomFunctionSum hp (cubicThetaPrimeCubeFourierMode h f) x=
      cubicThetaPrimeCubeBottomFourier hp h*cubicThetaPrimeCubeScaledMode hp 0 h f x := by
  unfold cubicThetaPrimeCubeBottomFunctionSum cubicThetaPrimeCubeBottomFourier
  rw [←tsum_mul_right]
  apply tsum_congr
  intro r
  rw [cubicThetaPrimeCubeFourierMode_branch]
  simp only [Fin.val_zero,Nat.sub_zero,map_mul,residueRepresentative_spec]

lemma cubicThetaPrimeCubeUnitFunctionSum_mode {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) (f : ℝ → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeUnitFunctionSum hp k (cubicThetaPrimeCubeFourierMode h f) x=
      cubicThetaPrimeCubeUnitFourier hp k h*cubicThetaPrimeCubeScaledMode hp k h f x :=
  cubicThetaPrimeCubeUnitModeSum_eq hp k h f x

theorem cubicThetaPrimeCubeFunctionOperator_mode {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (f : ℝ → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeFunctionOperator hp (cubicThetaPrimeCubeFourierMode h f) x=
      cubicThetaPrimeCubeFourierMode h f (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)+
      cubicThetaPrimeCubeBottomFourier hp h*cubicThetaPrimeCubeScaledMode hp 0 h f x+
      cubicThetaPrimeCubeUnitFourier hp 1 h*cubicThetaPrimeCubeScaledMode hp 1 h f x+
      cubicThetaPrimeCubeUnitFourier hp (⟨2,by decide⟩ : Fin 3) h*
        cubicThetaPrimeCubeScaledMode hp (⟨2,by decide⟩ : Fin 3) h f x := by
  unfold cubicThetaPrimeCubeFunctionOperator
  rw [cubicThetaPrimeCubeBottomFunctionSum_mode,cubicThetaPrimeCubeUnitFunctionSum_mode,
    cubicThetaPrimeCubeUnitFunctionSum_mode]

end CubicFirstMoment

end

end OAI
