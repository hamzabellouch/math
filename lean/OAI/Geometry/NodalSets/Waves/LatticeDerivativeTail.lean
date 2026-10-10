import OAI.Geometry.NodalSets.Waves.GaussianTailBound
import OAI.Geometry.NodalSets.Waves.LatticeVarianceUpper

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_derivative_tail_bound (hUD : U ⊆ D) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x : Coord,
      ∀ k : Fin (k0+1), ∀ r : ℝ, 0 ≤ r →
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          r < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)*Real.exp (-a.beams.c*(n:ℝ)*r^2) := by
  classical
  obtain ⟨B,hB,hgauss⟩ := source_lattice_gaussian_sum a.beams.c_pos
  refine ⟨3*a.beams.Cw^2*B,by have := a.beams.Cw_pos; positivity,?_⟩
  filter_upwards [a.estimates,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro hfin x k r hr
  let d : SourceGrid U n × Fin 3 → ℝ := fun i ↦ sourceEuclideanNorm (x-scaledLatticePoint n i.1)
  let R := a.beams.Cw^2*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)
  have hb (i : SourceGrid U n × Fin 3) :
      ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        R*Real.exp (-2*(a.beams.c*(n:ℝ))*(d i)^2) := by
    have h := ((hn (latticeFrame a.cover hUD n i.1,i.2)).2.2.2.2 x).1 k
    simp only [latticeFrame_center] at h
    change ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖ ≤ _ at h
    refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq ?_
    dsimp [R,d]
    rw [mul_pow,mul_pow,← Real.exp_nat_mul,← pow_mul]
    simp only [mul_assoc,← Real.exp_add]
    congr 2 <;> ring_nf
  have hg : ∑ i : SourceGrid U n × Fin 3, Real.exp (-(a.beams.c*(n:ℝ))*(d i)^2) ≤ 3*B := by
    dsimp [d]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [← Finset.mul_sum]
    norm_num only [Nat.cast_ofNat]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [neg_mul] using hgauss U n hnpos x
  have hh := finite_gaussian_tail d
    (fun i ↦ ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2)
    (by have := a.beams.c_pos; positivity : 0 ≤ a.beams.c*(n:ℝ))
    (by dsimp [R]; positivity : 0 ≤ R) hr (fun i ↦ sourceEuclideanNorm_nonneg _) hb hg
  convert hh using 1
  dsimp [R]
  simp only [neg_mul]
  ring

theorem lattice_nonmain_derivative_bound (hUD : U ⊆ D) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x : Coord,
      ∀ k : Fin (k0+1),
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := a.lattice_derivative_tail_bound hUD
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro hfin x k
  have h := hn x k ((n:ℝ)^(-5/12:ℝ)) (by positivity)
  rwa [mul_assoc (-a.beams.c),main_center_scale _ (by exact_mod_cast hnpos)] at h

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
