import OAI.Geometry.NodalSets.Waves.LatticeEnergyLowerBound
import OAI.Geometry.NodalSets.Waves.LatticeLogJets
import OAI.Geometry.NodalSets.Waves.LatticeVarianceUpper

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_variance_lower_bound (hUD : U ⊆ D) (hU : IsOpen U)
    {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x ∈ Q,
      c*Real.exp (2*(n:ℝ)*S x) ≤ a.latticeVariance hUD n x := by
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,c,hc,C,hC,hb⟩ :=
    a.lattice_logarithmic_jet_estimates hUD 2 (by norm_num)
  obtain ⟨r,hr,hinner⟩ := compact_inner_ball hQ hU hQU
  refine ⟨c^2,pow_pos hc 2,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℕ),
    eventually_nat_frequency (half_scale_eventually 2 1 r hr)] with n hn hnpos hsmall
  intro hfin x hx
  have hd := (norm_le_sourceEuclideanNorm _).trans (rounded_lattice_distance hnpos x)
  have hmem : scaledLatticePoint n (roundedLatticeIndex n x) ∈ U :=
    hinner x hx (by simpa only [mem_closedBall,dist_eq_norm] using hd.trans hsmall.2.1)
  let z : SourceGrid U n := ⟨roundedLatticeIndex n x,hmem⟩
  have hd' : ‖x-scaledLatticePoint n z‖ ≤ 2*(n:ℝ)^(-1/2:ℝ) := by
    rw [norm_sub_rev]; exact hd
  have hl := (hn z 0 x hd').2.2.2.2.1
  have hle : c*Real.exp ((n:ℝ)*S x) ≤ ‖latticeWave a.cover a.beams hUD n z 0 x‖ := by
    have hh := mul_le_mul_of_nonneg_right hl.1 (Real.exp_nonneg ((n:ℝ)*S x))
    simpa only [mul_assoc,← Real.exp_add,neg_mul,neg_add_cancel,Real.exp_zero,mul_one] using hh
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ c*Real.exp ((n:ℝ)*S x)) hle 2
  have he : (c*Real.exp ((n:ℝ)*S x))^2 = c^2*Real.exp (2*(n:ℝ)*S x) := by
    rw [mul_pow,← Real.exp_nat_mul]
    congr 2
    ring
  rw [he] at hs
  apply hs.trans
  unfold latticeVariance
  exact Finset.single_le_sum (fun i _ ↦ sq_nonneg ‖latticeWave a.cover a.beams hUD n i.1 i.2 x‖)
    (Finset.mem_univ (z,(0:Fin 3)))

theorem lattice_sigma_comparison (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ x ∈ Q, c*Real.exp ((n:ℝ)*S x) ≤ a.latticeSigma hUD n x ∧
        a.latticeSigma hUD n x ≤ C*Real.exp ((n:ℝ)*S x) := by
  obtain ⟨c,hc,hlo⟩ := a.lattice_variance_lower_bound hUD hU hQ hQU
  obtain ⟨C,hC,hup⟩ := a.lattice_variance_upper_bound hUD
  refine ⟨Real.sqrt c,Real.sqrt_pos.mpr hc,Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  filter_upwards [hlo,hup,eventually_gt_atTop (0:ℕ)] with n hl hu hn
  have := finite_source_grid hUb hn
  let hfin := Fintype.ofFinite (SourceGrid U n)
  refine ⟨hfin,?_⟩
  intro x hx
  have hl' := hl x hx
  have hu' := hu x
  have hs := a.latticeSigma_sq hUD n x
  have hnon : 0 ≤ a.latticeSigma hUD n x := Real.sqrt_nonneg _
  have he : (Real.exp ((n:ℝ)*S x))^2 = Real.exp (2*(n:ℝ)*S x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hc2 := Real.sq_sqrt hc.le
  have hC2 := Real.sq_sqrt hC.le
  constructor
  · apply (sq_le_sq₀ (by positivity) hnon).mp
    rw [mul_pow,hc2,he,hs]
    exact hl'
  · apply (sq_le_sq₀ hnon (by positivity)).mp
    rw [mul_pow,hC2,he,hs]
    exact hu'

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
