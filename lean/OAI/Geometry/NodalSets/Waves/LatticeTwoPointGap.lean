import OAI.Geometry.NodalSets.Waves.CosineCovarianceBounds
import OAI.Geometry.NodalSets.Waves.LatticeTwoPointCovariance
import OAI.Geometry.NodalSets.Waves.PlaneWaveSecondMoment

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
noncomputable section

theorem lattice_plane_wave_two_point_gap
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ delta > 0,
      ∀ (w S : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : H ⊆ D) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∀ x ∈ Q, ∃ j : Fin 4,
            let G := fun v coeff ↦ gaussianWaveField
              (a.latticePlaneWaveCoefficient hUD n x (sourceSignScale g S x)) coeff v
            let M := Var[G 0;gaussianPairs]
            let C := cov[G 0,G (tau • Pi.single j 1);gaussianPairs]
            (1/2:ℝ) ≤ M ∧ M ≤ 1 ∧
              Var[G (tau • Pi.single j 1);gaussianPairs] = M ∧
              M/2 ≤ C ∧ C ≤ M-delta := by
  classical
  obtain ⟨κ,hκ,B,hB,hann⟩ := lattice_main_frequency_annulus g hH hg hp
  let tau : ℝ := 1/(8*(B+1))
  have ht : 0 < tau := by dsimp [tau]; positivity
  have ht4 : tau < 1/4 := by
    dsimp [tau]
    apply (div_lt_iff₀ (by positivity : 0 < 8*(B+1))).mpr
    linarith
  have hsmall : tau*B ≤ 1 := by
    dsimp [tau]
    rw [one_div,mul_comm,← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : 0 < 8*(B+1))).mpr
    linarith
  let delta : ℝ := (2/Real.pi^2)*tau^2*(κ^2/8)
  have hd : 0 < delta := by dsimp [delta]; positivity
  refine ⟨tau,ht,ht4,delta,hd,?_⟩
  intro w S D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU
  filter_upwards [hann w S D U m J K k0 a hHD hUD hUH,
    a.latticeAlpha_main_mass hUD hU hUb hQ hQU (1/2) (by norm_num)] with n hn hm
  obtain ⟨hfin,hm⟩ := hm
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx
  let F := Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
    sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ))
  let alpha := a.latticeAlpha hUD n x
  let k := fun i : SourceGrid U n × Fin 3 ↦ sourceFrequency (g (scaledLatticePoint n i.1))
    (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2) (sourceSignScale g S x)
  have hmass : (1/2:ℝ) ≤ ∑ i ∈ F, ‖alpha i‖^2 := by
    have := (hm x hx).2
    dsimp only [F,alpha]
    linarith
  have hmass1 : ∑ i ∈ F, ‖alpha i‖^2 ≤ 1 := by
    rw [← (hm x hx).1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ ↦ sq_nonneg _)
  have hb (i : SourceGrid U n × Fin 3) (hi : i ∈ F) :
      κ ≤ sourceEuclideanNorm (k i) ∧ sourceEuclideanNorm (k i) ≤ B :=
    hn x (hUH (hQU hx)) i (Finset.mem_filter.mp hi).2
  obtain ⟨j,hj⟩ := coordinate_second_moment F alpha k κ hκ.le hmass (fun i hi ↦ (hb i hi).1)
  have hcoord (i : SourceGrid U n × Fin 3) (hi : i ∈ F) : |k i j| ≤ B :=
    (norm_le_pi_norm (k i) j).trans ((norm_le_sourceEuclideanNorm _).trans (hb i hi).2)
  have hbounds := cosine_covariance_bounds F (fun i ↦ ‖alpha i‖^2) (fun i ↦ k i j)
    tau B (κ^2/8) (fun i hi ↦ sq_nonneg _) ht.le hsmall hcoord hj
  refine ⟨j,?_⟩
  dsimp only
  rw [a.lattice_plane_wave_variance,a.lattice_plane_wave_variance,a.lattice_plane_wave_covariance]
  exact ⟨hmass,hmass1,rfl,hbounds.1,hbounds.2⟩

end
end Yau.Geometry

end OAI
