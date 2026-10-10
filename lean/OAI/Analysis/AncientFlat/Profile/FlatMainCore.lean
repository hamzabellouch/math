import OAI.Analysis.AncientFlat.Weighted.ExactSourceSpace
import OAI.Analysis.AncientFlat.Profile.ProfileData

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian ENNReal
namespace FlatMain
open FlatWeighted FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def timeDerivative (u : V × ℝ → ℂ) (t : ℝ) (x : V) : ℂ := deriv (fun r => u (x,r)) t

def flatOperator (P : ProfileData) (u : V × ℝ → ℂ) (t : ℝ) (x : V) : ℂ :=
  timeDerivative u t x+((P.G (‖x‖^2/Real.sqrt (-t)))^2/16:ℝ)*Δ (Δ (fun z => u (z,t))) x+
    (FlatRadial.originalB P.G P.h t x:ℂ)*u (x,t)

def InX {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V) (α w a : ℝ) (u : V × ℝ → ℂ) : Prop :=
  (∀ t : ℝ, t<0 → ContDiff ℝ 4 (fun x => u (x,t))) ∧
  (∀ t : ℝ, t<0 → ∀ x : V, DifferentiableAt ℝ (fun r => u (x,r)) t) ∧
  (xNorm e α w a (fun t x => u (x,t)) (timeDerivative u)≠⊤) ∧
  (∀ t : ℝ, t<0 → Radial (fun x => u (x,t))) ∧
  (∀ t : ℝ, t<0 → RealValued (fun x => u (x,t)))
def XNorm {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V) (α w a : ℝ) (u : V × ℝ → ℂ) : ℝ :=
  (xNorm e α w a (fun t x => u (x,t)) (timeDerivative u)).toReal
end FlatMain

end

end OAI
