import OAI.Geometry.RCD.Transport.ExactAffineGeodesic
import OAI.Geometry.RCD.Sobolev.OrthonormalHarmonicLipschitz
import Mathlib.Analysis.Normed.Affine.AddTorsor

namespace OAI

/-! # Exact horizontal speeds and vertical geodesics for orthonormal coordinates -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem coordinate_speed_of_affine {X : Type*} {n : ℕ} (v : X → Euclidean n)
    (γ : Time → X)
    (h : ∀ t : Time, v (γ t)=(1-(t:ℝ)) • v (γ 0)+(t:ℝ) • v (γ 1))
    (s t : Time) :
    dist (v (γ s)) (v (γ t))=|(s:ℝ)-(t:ℝ)| * dist (v (γ 0)) (v (γ 1)) := by
  rw [h s,h t]
  simpa only [AffineMap.lineMap_apply_module,Real.dist_eq] using
    dist_lineMap_lineMap (v (γ 0)) (v (γ 1)) (s:ℝ) (t:ℝ)

namespace NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem orthonormal_harmonic_geodesic {R : ℝ} (hR : 1≤R)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    {b : ℝ} (hb : 50*R<b)
    (hu : ∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i)
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun x => v x i)
    (hH : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) (u i))
    (hgram : ∀ i j, localGamma (hausdorff n X) hX.quadratic (u i) (u j)
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => if i=j then 1 else 0)
    (hv : ContinuousOn v (ball p b)) :
    LipschitzOnWith 1 v (ball p (4*R)) ∧
    ∀ x y : X, dist x p≤R/2 → dist y p≤R/2 →
      ∃ γ : C(Time,X), IsGeodesic γ ∧ γ 0=x ∧ γ 1=y ∧
        (∀ t : Time, dist (γ t) p≤3*R) ∧
        (∀ t : Time, v (γ t)=(1-(t:ℝ)) • v x+(t:ℝ) • v y) ∧
        (∀ s t : Time, dist (v (γ s)) (v (γ t))=|(s:ℝ)-(t:ℝ)| * dist (v x) (v y)) ∧
        (v x=v y → ∀ t : Time, v (γ t)=v x) := by
  have hsub : ball p (8*(4*R))⊆ball p b := ball_subset_ball (by linarith)
  have hLip := hX.orthonormal_coordinates_lipschitz hn p (by linarith : 0<4*R) u v
    (hv.mono hsub) (fun i => ae_restrict_of_ae_restrict_of_subset hsub (hu i))
    (fun i j => ae_restrict_of_ae_restrict_of_subset hsub (hgram i j))
  refine ⟨hLip,?_⟩
  intro x y hx hy
  have hdiag (i : Fin n) : localGamma (hausdorff n X) hX.quadratic (u i) (u i)
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => (1:ℝ) := by
    simpa only [ite_true] using hgram i i
  obtain ⟨γ,hγ,h₀,h₁,hstay,haff⟩ := hX.exists_exact_affine_geodesic hn p hR u v hb hu hH
    (fun _ => 1) (fun i => (hdiag i).mono fun _ he => by simpa only [NNReal.coe_one,one_pow] using he.le)
    (fun _ => 1) hdiag hv hx hy
  refine ⟨γ,hγ,h₀,h₁,hstay,haff,?_,?_⟩
  · intro s t
    have hh : ∀ t : Time, v (γ t)=(1-(t:ℝ)) • v (γ 0)+(t:ℝ) • v (γ 1) := by
      simpa only [h₀,h₁] using haff
    simpa only [h₀,h₁] using coordinate_speed_of_affine v γ hh s t
  · intro hxy t
    rw [haff t,← hxy,← add_smul]
    simp

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
