import OAI.Geometry.NodalSets.Charts.SphereChartEnergyBounds
import OAI.Geometry.NodalSets.Charts.SphereFiniteChartL2Comparison
import OAI.Geometry.NodalSets.Elliptic.RealCubeEnergyCompactness

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem sphere_energy_subsequence (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : Continuous rho) (hrp : ∀ x, 0 < rho x)
    (W : ℕ → Base → ℝ) (hW : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (W j))
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ j, sphereWeightedPairing rho (W j) (W j)+sphereDirichletForm A (W j) (W j) ≤ C) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ eps > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      sphereWeightedPairing rho (W (nu i)-W (nu j)) (W (nu i)-W (nu j)) < eps := by
  classical
  obtain ⟨P,R,hR,hcomp⟩ := sphere_finite_chart_l2_comparison rho hr hrp
  let I := {p // p ∈ P}
  choose K hK hKb using (fun p : I ↦ sphere_chart_cube_energy_bound A hA hs hp rho hr hrp p.val)
  let F : I → ℕ → Yau.Jets.Coord → ℝ := fun p j ↦ W j ∘ sphereChartCoordMap p.val
  have hF (p : I) (j : ℕ) : ContDiff ℝ ∞ (F p j) := spherePullback_smooth (W j) (hW j) p.val
  have hb (p : I) (j : ℕ) : (∫ x in realFinCube 4, (F p j x)^2)+
      (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (F p j) x i)^2) ≤ K p*C :=
    (hKb p (W j) (hW j)).trans (mul_le_mul_of_nonneg_left (hbound j) (hK p).le)
  obtain ⟨nu,hnu,hlocal⟩ := real_countable_cube_energy_subsequence F hF (fun p ↦ K p*C)
    (fun p ↦ mul_pos (hK p) hC) hb
  refine ⟨nu,hnu,?_⟩
  intro eps heps
  let delta := eps/(R*((Fintype.card I:ℝ)+1))
  have hd : 0 < delta := div_pos heps (mul_pos hR (by positivity))
  choose Ns hNs using (fun p : I ↦ hlocal p delta hd)
  let N := Finset.univ.sup Ns
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  have hpt (p : I) : (∫ x in realFinCube 4, (F p (nu i) x-F p (nu j) x)^2) ≤ delta := by
    have hpN : Ns p ≤ N := Finset.le_sup (f := Ns) (Finset.mem_univ p)
    exact (hNs p i (hpN.trans hi) j (hpN.trans hj)).le
  have hsum : (∑ p : I, ∫ x in realFinCube 4, (F p (nu i) x-F p (nu j) x)^2) ≤
      (Fintype.card I:ℝ)*delta := by
    simpa using Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset I)) ↦ hpt p)
  have h := (hcomp (W (nu i)-W (nu j)) ((hW (nu i)).continuous.sub (hW (nu j)).continuous)).trans
    (mul_le_mul_of_nonneg_left hsum hR.le)
  apply h.trans_lt
  have heq : R*((Fintype.card I:ℝ)+1)*delta=eps := by
    dsimp [delta]
    field_simp
  nlinarith [mul_pos hR hd]

end
end Yau.Target

end OAI
