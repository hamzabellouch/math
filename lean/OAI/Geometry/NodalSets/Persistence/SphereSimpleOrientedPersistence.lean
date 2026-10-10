import OAI.Geometry.NodalSets.Charts.SpherePositiveNormalization
import OAI.Geometry.NodalSets.Persistence.SphereSimpleUniformPersistence
import OAI.Geometry.NodalSets.Spectral.SphereOrthogonalEigenfunction

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter Metric Yau.Geometry
open scoped ContDiff Topology
noncomputable section

theorem sphere_finite_norm_simple_oriented_persistence (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (he : ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
      lam*u ((extChartAt (𝓡 4) p).symm y))
    (hsimple : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) :
    ∃ N : ℕ, sphereIndexedEigenvalue d N=lam ∧
      ∃ P : Finset Base,
        (∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x) ∧
        ∀ eps > 0, ∃ eta > 0, ∀ b : SphereEnergyData,
          ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
          sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
          sphereIndexedEigenvalue b N ∈ Set.Icc (lam/2) (2*lam) ∧
          ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
            (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
              sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) ∧
            ∀ x, |v x-u x| < eps := by
  let U : SphereEnergySmooth d := (⟨u,hu⟩ : sphereSmoothFunctions)
  have hU : U ≠ 0 := fun h ↦ hu0 (congrArg (fun w : SphereEnergySmooth d ↦
    (SphereEnergySmooth.toSmooth d w : Base → ℝ)) h)
  obtain ⟨N,hN⟩ := sphere_smooth_intrinsic_eigenvalue_index d hd U hU lam he
  obtain ⟨c,hc,hcn⟩ := sphere_positive_normalization d u hu.continuous hu0
  have hS : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        sphereIndexedEigenvalue d N*v ((extChartAt (𝓡 4) p).symm y)) →
      ∃ a : ℝ, v=a • (c • u) := by
    intro v hv hve
    obtain ⟨a,ha⟩ := hsimple v hv (by simpa only [hN] using hve)
    refine ⟨a/c,?_⟩
    rw [smul_smul,div_mul_cancel₀ a hc.ne']
    exact ha
  obtain ⟨P,hP,H⟩ := sphere_finite_norm_simple_uniform_persistence d hd N (c • u) hcn hS
  have hcore : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hyx⟩ := hP x
    exact ⟨p,hp,seedCoordEquiv y,⟨y,(closedBall_subset_closedBall (by norm_num : (1:ℝ)/512 ≤ 1))
      (ball_subset_closedBall hy),rfl⟩,hyx⟩
  refine ⟨N,hN,P,hcore,?_⟩
  intro eps heps
  obtain ⟨eta₀,h₀,H₀⟩ := H (eps*c) (mul_pos heps hc)
  obtain ⟨eta₁,h₁,H₁⟩ := sphere_finite_norm_indexed_eigenvalue_continuity P hcore d hd N
    (lam/2) (by positivity)
  refine ⟨min eta₀ eta₁,lt_min h₀ h₁,?_⟩
  intro b hb hdist
  have hdist0 := (sphereCoefficientDistance_mono_order P d b hd hb 0 8 (by omega)).trans_lt
    (hdist.trans_le (min_le_right _ _))
  have hval := H₁ b hb hdist0
  rw [hN] at hval
  have hinterval : sphereIndexedEigenvalue b N ∈ Set.Icc (lam/2) (2*lam) :=
    ⟨by linarith [(abs_lt.mp hval).1],by linarith [(abs_lt.mp hval).2]⟩
  obtain ⟨v,hv,hv0,hvn,hve⟩ := sphereIndexedEigenvalue_intrinsic_realization b
    (fun p ↦ (hb.comp (sphereChartCoordMap_smooth p)).contDiff) N
  have hclose := H₀ b hb (hdist.trans_le (min_le_left _ _)) v hv hvn hve
  have hbranch : ∃ w : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w ∧ w ≠ 0 ∧
      (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density w p y =
        sphereIndexedEigenvalue b N*w ((extChartAt (𝓡 4) p).symm y)) ∧
      ∀ x, |w x-(c • u) x| < eps*c := by
    rcases hclose with hp | hm
    · exact ⟨v,hv,hv0,hve,hp⟩
    · refine ⟨-v,hv.neg,neg_ne_zero.mpr hv0,?_,?_⟩
      · simpa only [neg_one_smul] using intrinsic_eigenfunction_smul b.tensor b.smooth b.symm b.pos
          b.density v hv (sphereIndexedEigenvalue b N) (-1) hve
      · intro x
        change |-v x-(c • u) x| < eps*c
        rw [show -v x-(c • u) x=-(v x+(c • u) x) by ring,abs_neg]
        exact hm x
  obtain ⟨w,hw,hw0,hwe,hwclose⟩ := hbranch
  refine ⟨hinterval,c⁻¹ • w,(contMDiff_const (c := c⁻¹)).mul hw,
    smul_ne_zero (inv_ne_zero hc.ne') hw0,
    intrinsic_eigenfunction_smul b.tensor b.smooth b.symm b.pos b.density w hw
      (sphereIndexedEigenvalue b N) c⁻¹ hwe,?_⟩
  intro x
  have hid : (c⁻¹ • w) x-u x=c⁻¹*(w x-(c • u) x) := by
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp
  rw [hid,abs_mul,abs_of_pos (inv_pos.mpr hc)]
  calc
    c⁻¹*|w x-(c • u) x| < c⁻¹*(eps*c) := mul_lt_mul_of_pos_left (hwclose x) (inv_pos.mpr hc)
    _ = eps := by field_simp

end
end Yau.Target

end OAI
