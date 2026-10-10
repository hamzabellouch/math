import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridLocalJets
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTwiceDifferentiation

namespace OAI

/-! Actual termwise first and second differentiation of the Eisenstein
grid on its initial half-plane. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEisensteinGrid_coordinate_derivs (k : CubicThetaAxis)
    (s : ℂ) (hs : 2<s.re) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    let f := fun cd : Eisenstein × Eisenstein => fun t : ℝ =>
      cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k x y v t) s
    let t := cubicThetaCoordinateCenter k x y v
    deriv (fun w => ∑' cd, f cd w) t=(∑' cd, deriv (f cd) t) ∧
    deriv (deriv (fun w => ∑' cd, f cd w)) t=(∑' cd, deriv (deriv (f cd)) t) ∧
    Summable (fun cd => deriv (f cd) t) ∧
    Summable (fun cd => deriv (deriv (f cd)) t) := by
  obtain ⟨r,hr,u₁,u₂,hu₁,hu₂,hbound⟩ := cubicThetaCoordinate_local_jets k s hs x y hv
  dsimp only
  have hx : cubicThetaCoordinateCenter k x y v ∈
      Set.Ioo (cubicThetaCoordinateCenter k x y v-r) (cubicThetaCoordinateCenter k x y v+r) :=
    ⟨by linarith,by linarith⟩
  refine cubicTheta_twice_deriv_tsum hu₁ hu₂ hx ?_ ?_ ?_ ?_
  · intro cd t ht
    exact cubicThetaCoordinateLine_analytic k cd s x y v t (hbound cd t ht).1
  · intro cd t ht
    exact (hbound cd t ht).2.1
  · intro cd t ht
    exact (hbound cd t ht).2.2
  · simpa only [cubicThetaCoordinateLine_center] using
      (cubicThetaEisensteinGrid_summable (p:=cubicThetaCartesianPoint x y v) hv hs)

end CubicFirstMoment

end

end OAI
