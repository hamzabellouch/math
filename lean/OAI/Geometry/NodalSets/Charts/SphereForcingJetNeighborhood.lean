import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientDivergenceJets
import OAI.Geometry.NodalSets.Elliptic.RealFinitePositiveBounds

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Metric
open scoped ContDiff
noncomputable section

theorem sphere_weighted_density_finite_jet_bound (P : Finset Base) (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (J : ℕ) :
    ∃ B > 0, ∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) 1,
      ∀ ds : List (Fin 4), ds.length ≤ J →
        |partialJet (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) ds x| ≤ B := by
  have hr (p : Base) : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) :=
    roundCoordDensity_smooth.mul (spherePullback_smooth d.density hd p)
  choose C hC hCb using (fun p : P ↦ compact_real_derivative_bound _ (hr p)
    (isCompact_closedBall (0 : Yau.Jets.Coord) 1) J)
  obtain ⟨B,hB,hmajor⟩ := Yau.real_finite_positive_majorant C
  refine ⟨B,hB,?_⟩
  intro p hp x hx ds hds
  exact (partialJet_norm_le_iterated _ (hr p) ds x).trans
    ((hCb ⟨p,hp⟩ ds.length hds x hx).trans (hmajor ⟨p,hp⟩))

theorem sphere_finite_norm_divergence_neighborhood (P : Finset Base) (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (lam₀ : ℝ) (J : ℕ)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta > 0, ∀ (b : SphereEnergyData) (lam : ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      sphereCoefficientDistance P J d.tensor d.density b.tensor b.density < eta →
      |lam-lam₀| < eta →
      ∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) 1,
      ∀ ds : List (Fin 4), ds.length ≤ J →
        (∀ i j, |partialJet (fun y ↦ sphereChartPrincipalDensity b p y i j) ds x-
          partialJet (fun y ↦ sphereChartPrincipalDensity d p y i j) ds x| ≤ eps) ∧
        |partialJet (fun y ↦ lam*(roundCoordDensity y*b.density (sphereChartCoordMap p y))) ds x-
          partialJet (fun y ↦ lam₀*(roundCoordDensity y*d.density (sphereChartCoordMap p y))) ds x| ≤ eps ∧
        |partialJet (fun y ↦ roundCoordDensity y*b.density (sphereChartCoordMap p y)) ds x-
          partialJet (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) ds x| ≤ eps := by
  obtain ⟨C,hC,hCb⟩ := sphere_coefficient_divergence_jet_bound J
  obtain ⟨B,hB,hBb⟩ := sphere_weighted_density_finite_jet_bound P d hd J
  let K := C+(|lam₀|+1)*C+B+1
  have hK : 0 < K := by dsimp [K]; positivity
  let eta := min 1 (eps/K)
  have heta : 0 < eta := lt_min zero_lt_one (div_pos heps hK)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hbudget : K*eta ≤ eps := by
    have h : eta ≤ eps/K := min_le_right _ _
    nlinarith [(le_div_iff₀ hK).mp h]
  refine ⟨eta,heta,?_⟩
  intro b lam hb hdist hlam p hp x hx ds hds
  let D := sphereCoefficientDistance P J d.tensor d.density b.tensor b.density
  have hD : 0 ≤ D := sphereCoefficientDistance_nonneg P J d.tensor b.tensor d.density b.density
    (fun q _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd q)
    (fun q _ ↦ intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb q)
  have hCD : C*D ≤ eps := by
    have hCK : C ≤ K := by
      dsimp [K]
      nlinarith [mul_nonneg (show 0 ≤ |lam₀|+1 by positivity) hC.le]
    exact (mul_le_mul_of_nonneg_left hdist.le hC.le).trans
      ((mul_le_mul_of_nonneg_right hCK heta.le).trans hbudget)
  obtain ⟨hprincipal,hrho⟩ := hCb P d b hd hb p hp x hx ds hds
  refine ⟨fun i j ↦ (hprincipal i j).trans hCD,?_,hrho.trans hCD⟩
  have hbd : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y*b.density (sphereChartCoordMap p y)) :=
    roundCoordDensity_smooth.mul (spherePullback_smooth b.density hb p)
  have hdd : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) :=
    roundCoordDensity_smooth.mul (spherePullback_smooth d.density hd p)
  rw [partialJet_const_mul _ hbd,partialJet_const_mul _ hdd]
  let rb := partialJet (fun y ↦ roundCoordDensity y*b.density (sphereChartCoordMap p y)) ds x
  let rd := partialJet (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) ds x
  have hrd : |rd| ≤ B := hBb p hp x hx ds hds
  have hlamabs : |lam| ≤ |lam₀|+1 := by
    have hh : |lam| ≤ |lam-lam₀|+|lam₀| := by
      simpa only [sub_add_cancel] using abs_add_le (lam-lam₀) lam₀
    linarith [hlam.trans_le heta1]
  have hrb : |rb-rd| ≤ C*D := hrho
  change |lam*rb-lam₀*rd| ≤ eps
  calc
    _ = |lam*(rb-rd)+(lam-lam₀)*rd| := by congr 1; ring
    _ ≤ |lam| * |rb-rd|+|lam-lam₀| * |rd| := by simpa only [abs_mul] using abs_add_le (lam*(rb-rd)) ((lam-lam₀)*rd)
    _ ≤ (|lam₀|+1)*(C*D)+eta*B := add_le_add
      (mul_le_mul hlamabs hrb (abs_nonneg _) (by positivity))
      (mul_le_mul hlam.le hrd (abs_nonneg _) heta.le)
    _ ≤ (|lam₀|+1)*(C*eta)+eta*B := by gcongr
    _ ≤ K*eta := by dsimp [K]; nlinarith [mul_nonneg hC.le heta.le]
    _ ≤ eps := hbudget

end
end Yau.Target

end OAI
