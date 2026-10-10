import OAI.Geometry.NodalSets.Elliptic.RealSmoothCutoffJetBound
import OAI.Geometry.NodalSets.Spectral.SphereEigenSmoothRepresentative

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry Yau.Analysis
open scoped ContDiff Topology
noncomputable section

theorem sphere_eigen_smooth_quantitative (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) :
    ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧
      ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
        ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧
          tsupport v ⊆ Yau.realCenteredCube 4 (1/8) ∧
          v =ᵐ[volume.restrict (Yau.realCenteredCube 4 (1/32))]
            (fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) ∧
          ∀ n ds, ds.length ≤ n → ∀ x,
            (partialJet v ds x)^2 ≤ C n*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  obtain ⟨eta,he,hc,hs,hb,h1⟩ := Yau.real_cube_smooth_cutoff (1/32) (3/64) (by norm_num)
  have hsQ : tsupport eta ⊆ interior (Yau.realCenteredCube 4 (1/16)) :=
    hs.trans (Yau.realCenteredCube_subset_interior (by norm_num))
  choose A hA hbound using (fun n ↦ Yau.real_smooth_cutoff_jet_bound
    (Yau.realCenteredCube_isCompact 4 (1/16)) eta he hc hsQ n)
  choose K hK hjet using (fun n ↦ sphere_eigen_all_finite_weak_jets d p hrho mu hmu (n+1))
  refine ⟨fun n ↦ A n*K n,fun n ↦ mul_pos (hA n) (hK n),fun f heigen ↦ ?_⟩
  obtain ⟨v,hv,hsv,hve⟩ := sphere_eigen_cutoff_smooth d p hrho mu hmu eta he hc hsQ f heigen
  have hvc : HasCompactSupport v :=
    (Yau.realCenteredCube_isCompact 4 (1/8)).of_isClosed_subset (isClosed_tsupport _) hsv
  refine ⟨v,hv,hsv,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hve,
      self_mem_ae_restrict (Yau.realCenteredCube_isCompact 4 (1/32)).measurableSet] with x hx hxQ
    rw [hx,(h1 x hxQ).eq_of_nhds,one_mul]
  · intro n ds hd x
    obtain ⟨U,hzero,hone,hU,hw,hpde⟩ := hjet n f heigen
    have hzeroV : v =ᵐ[volume] (fun x ↦ eta x*U [] x) := by rw [hzero]; exact hve
    have h := hbound n U (fun es hh ↦ (hU es (by omega)).1)
      (fun es hh i psi hp hc hs ↦ (hw es (by omega) i psi hp hc hs).2.2)
      (K n*(‖f‖^2+‖sphereWeakSolution d f‖^2))
      (mul_nonneg (hK n).le (by positivity))
      (fun es hh ↦ (hU es (by omega)).2) v hv hvc hzeroV ds hd x
    simpa only [mul_assoc] using h

end
end Yau.Target

end OAI
