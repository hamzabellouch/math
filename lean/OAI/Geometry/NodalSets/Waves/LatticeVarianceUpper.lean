import OAI.Geometry.NodalSets.Waves.LocalCompactWaves
import OAI.Geometry.NodalSets.Waves.ScaledLatticeGaussianSum

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeVariance (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)] (x : Coord) : ℝ :=
  ∑ i : SourceGrid U n × Fin 3, ‖latticeWave a.cover a.beams hUD n i.1 i.2 x‖^2

def latticeSigma (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)] (x : Coord) : ℝ :=
  Real.sqrt (a.latticeVariance hUD n x)

lemma latticeVariance_nonneg (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)] (x : Coord) :
    0 ≤ a.latticeVariance hUD n x := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma latticeSigma_sq (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)] (x : Coord) :
    (a.latticeSigma hUD n x)^2 = a.latticeVariance hUD n x :=
  Real.sq_sqrt (a.latticeVariance_nonneg hUD n x)

theorem lattice_derivative_square_sum_bound (hUD : U ⊆ D) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x : Coord,
      ∀ k : Fin (k0+1),
      ∑ i : SourceGrid U n × Fin 3,
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x) := by
  obtain ⟨B,hB,hgauss⟩ := source_lattice_gaussian_sum (show 0 < 2*a.beams.c by have := a.beams.c_pos; positivity)
  refine ⟨3*a.beams.Cw^2*B,by have := a.beams.Cw_pos; positivity,?_⟩
  filter_upwards [a.estimates,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro hfin x k
  let R := a.beams.Cw^2*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hb (i : SourceGrid U n × Fin 3) :
      ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        R*Real.exp (-(2*a.beams.c)*(n:ℝ)*(sourceEuclideanNorm (x-scaledLatticePoint n i.1))^2) := by
    have h := ((hn (latticeFrame a.cover hUD n i.1,i.2)).2.2.2.2 x).1 k
    simp only [latticeFrame_center] at h
    change ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖ ≤ _ at h
    have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
    refine hh.trans_eq ?_
    dsimp [R]
    rw [mul_pow,mul_pow,← Real.exp_nat_mul,← pow_mul]
    simp only [mul_assoc,← Real.exp_add]
    congr 2 <;> ring_nf
  calc
    _ ≤ ∑ i : SourceGrid U n × Fin 3, R*Real.exp (-(2*a.beams.c)*(n:ℝ)*
        (sourceEuclideanNorm (x-scaledLatticePoint n i.1))^2) := Finset.sum_le_sum (fun i _ ↦ hb i)
    _ = 3*R*∑ z : SourceGrid U n, Real.exp (-(2*a.beams.c)*(n:ℝ)*
        (sourceEuclideanNorm (x-scaledLatticePoint n z))^2) := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [← Finset.mul_sum,← Finset.mul_sum,mul_assoc]
      dsimp [R]
      ring
    _ ≤ 3*R*B := mul_le_mul_of_nonneg_left (hgauss U n hnpos x) (by positivity)
    _ = _ := by dsimp [R]; ring

theorem lattice_variance_upper_bound (hUD : U ⊆ D) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x : Coord,
      a.latticeVariance hUD n x ≤ C*Real.exp (2*(n:ℝ)*S x) := by
  obtain ⟨C,hC,hb⟩ := a.lattice_derivative_square_sum_bound hUD
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with n hn
  intro hfin x
  calc
    a.latticeVariance hUD n x =
        ∑ i : SourceGrid U n × Fin 3,
          ‖iteratedFDeriv ℝ 0 (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z : ℝ ↦ z^2)
        (norm_iteratedFDeriv_zero (𝕜 := ℝ)
          (f := latticeWave a.cover a.beams hUD n i.1 i.2) (x := x)).symm
    _ ≤ _ := by simpa only [Fin.val_zero,mul_zero,pow_zero,mul_one] using! hn x 0

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
