import OAI.Geometry.NodalSets.Waves.LatticeNormalizedWeights

namespace OAI

namespace Yau.Probability
open Filter
open scoped Topology

lemma tendsto_polynomial_main_center_tail (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ (n:ℝ)^k*Real.exp (-a*(n:ℝ)^(1/6:ℝ))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n:ℝ)^(1/6:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/6)).comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6*(k:ℝ)) a ha).comp hpow
  convert ht using 1
  funext n
  simp only [Function.comp_def]
  rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ n)]
  rw [show (1/6:ℝ)*(6*(k:ℝ)) = (k:ℝ) by ring,Real.rpow_natCast]

end Yau.Probability

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_nonmain_derivatives_negligible (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ k : Fin (k0+1),
        (∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
          ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2) /
          (a.latticeSigma hUD n x)^2 ≤ ε := by
  classical
  obtain ⟨c,hc,hlo⟩ := a.lattice_variance_lower_bound hUD hU hQ hQU
  obtain ⟨C,hC,htail⟩ := a.lattice_nonmain_derivative_bound hUD
  have hlim := (tendsto_polynomial_main_center_tail (2*k0) a.beams.c a.beams.c_pos).const_mul (C/c)
  simp only [mul_zero] at hlim
  filter_upwards [hlo,htail,hlim.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)]
    with n hl ht hsmall hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  refine ⟨hfin,?_⟩
  intro x hx k
  have hv : 0 < a.latticeVariance hUD n x :=
    lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hl x hx)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hp : (n:ℝ)^(2*k.val) ≤ (n:ℝ)^(2*k0) :=
    pow_le_pow_right₀ hn1 (by have := k.isLt; omega)
  rw [a.latticeSigma_sq]
  apply le_trans _ hsmall.le
  apply (div_le_iff₀ hv).mpr
  have hh := mul_le_mul_of_nonneg_left (hl x hx)
    (by positivity : 0 ≤ (C/c)*((n:ℝ)^(2*k0)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ))))
  calc
    _ ≤ C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)) := ht x k
    _ ≤ C*(n:ℝ)^(2*k0)*Real.exp (2*(n:ℝ)*S x)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)) := by gcongr
    _ = ((C/c)*((n:ℝ)^(2*k0)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ))))*
        (c*Real.exp (2*(n:ℝ)*S x)) := by field_simp
    _ ≤ _ := hh

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
