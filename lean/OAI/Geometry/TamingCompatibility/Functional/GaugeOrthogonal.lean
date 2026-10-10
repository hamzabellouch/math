import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.End
import OAI.Geometry.TamingCompatibility.Elliptic.OperatorCalculus

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus
open FlatHeat (V)
open scoped RealInnerProductSpace ContDiff
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {W Q : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]

lemma gauge_orthogonal (U : W →L[ℝ] W) (hU : ∀ u v, ⟪U u,U v⟫ = ⟪u,v⟫) :
    U.adjoint ∘L U = ContinuousLinearMap.id ℝ W := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.adjoint_inner_right] using hU v u

lemma weighted_symbol_cancel (a b : W →L[ℝ] Q) {ρ c : ℝ} (hρ : ρ ≠ 0)
    (he : (ρ • a).adjoint ∘L b + (ρ • b).adjoint ∘L a =
      (2*(ρ*c)) • ContinuousLinearMap.id ℝ W) :
    a.adjoint ∘L b + b.adjoint ∘L a = (2*c) • ContinuousLinearMap.id ℝ W := by
  apply smul_right_injective (W →L[ℝ] W) hρ
  dsimp only
  simpa only [map_smul,ContinuousLinearMap.smul_comp,←smul_add,
    ←mul_smul,show ρ*(2*c) = 2*(ρ*c) by ring] using he

omit [CompleteSpace W] in

lemma residual_secondOrder (g : Fin 4 → Fin 4 → V → ℝ)
    (b : Fin 4 → V → W →L[ℝ] W) (c : V → W →L[ℝ] W)
    {t : ℝ} (ht : 0 < t) (z : V) (u : W) :
    deriv (fun s => modelSection s u z) t +
      secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) g b c (modelSection t u) z =
      residual (fun y i j => g i j y) (fun y i => b i y) c t z u := by
  have he : secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) g b c
      (modelSection t u) z =
      applyOperator (fun y i j => g i j y) (fun y i => b i y) c (modelSection t u) z := by
    unfold secondOrder applyOperator
    rfl
  rw [he]
  exact residual_apply (fun y i j => g i j y) (fun y i => b i y) c ht z u

lemma actual_residual (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (g : Fin 4 → Fin 4 → V → ℝ) (U : V → W →L[ℝ] W)
    (hU : ContDiff ℝ ∞ U) (horth : ∀ z, (U z).adjoint ∘L U z = ContinuousLinearMap.id ℝ W)
    {z : V} (ha : ∀ i, DifferentiableAt ℝ (a i) z) (hb : DifferentiableAt ℝ b z)
    (hρ : DifferentiableAt ℝ ρ z) (hρz : ρ z ≠ 0)
    (hp : ∀ i j, (a i z).adjoint ∘L a j z + (a j z).adjoint ∘L a i z =
      (2*g i j z) • ContinuousLinearMap.id ℝ W) {t : ℝ} (ht : 0 < t) (u : W) :
    (U z).adjoint (deriv (fun s => U z (modelSection s u z)) t +
      weightedAdjoint (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ
        (differential (EuclideanSpace.basisFun (Fin 4) ℝ) a b (fun y => U y (modelSection t u y))) z) =
    residual (fun y i j => g i j y)
      (fun y j => gaugeFirst (EuclideanSpace.basisFun (Fin 4) ℝ) g
        (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U j y)
      (gaugeZero (EuclideanSpace.basisFun (Fin 4) ℝ) g
        (firstMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ)
        (zeroMatrix (EuclideanSpace.basisFun (Fin 4) ℝ) a b ρ) U) t z u := by
  let e := EuclideanSpace.basisFun (Fin 4) ℝ
  have hU2 : ContDiff ℝ 2 U := hU.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hm0 : ContDiff ℝ ∞ (fun y : V => FlatHeat.heat t y • u) :=
    (FlatHeat.heat_contDiff t).smul (contDiff_const (c := u))
  have hm : ContDiff ℝ 2 (modelSection t u) :=
    hm0.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have htime : deriv (fun s => U z (modelSection s u z)) t =
      U z (deriv (fun s => modelSection s u z) t) := by
    have hd := ((FlatHeat.heat_hasDerivAt_time ht z).smul_const u)
    exact ((U z).hasFDerivAt.comp_hasDerivAt t hd).deriv.trans
      (congrArg (U z) hd.deriv.symm)
  have hcancel (v : W) : (U z).adjoint (U z v) = v :=
    congrArg (fun C : W →L[ℝ] W => C v) (horth z)
  have htime' : (U z).adjoint (deriv (fun s => U z (modelSection s u z)) t) =
      deriv (fun s => modelSection s u z) t :=
    (congrArg (U z).adjoint htime).trans (hcancel _)
  have hspace := gauge_formal_square e a b ρ g U (modelSection t u)
    hU2 hm ha hb hρ hρz hp (horth z)
  exact (map_add (U z).adjoint _ _).trans
    ((congrArg₂ (fun v w : W => v+w) htime' hspace).trans
      (residual_secondOrder g _ _ ht z u))

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end

end OAI
