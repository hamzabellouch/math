import OAI.Geometry.NodalSets.Elliptic.ShiftedCenterDistance
import OAI.Geometry.NodalSets.Waves.LatticeDerivativeTail
import OAI.Geometry.NodalSets.Waves.LatticeNonmainDecay
import OAI.Geometry.NodalSets.Waves.LatticeVarianceComparison

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_shifted_nonmain_bound (hUD : U ⊆ D) (hS : ContDiff ℝ ∞ S)
    {Q : Set Coord} (hQ : IsCompact Q) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)],
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : Coord, ‖v‖ ≤ R → ∀ k : Fin (k0+1),
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2)
          (x+((n:ℝ)*s)⁻¹ • v)‖^2 ≤
        C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)*
          Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ)) := by
  classical
  obtain ⟨B,hB,htail⟩ := a.lattice_derivative_tail_bound hUD
  obtain ⟨L,hL,hshift⟩ := compact_rescaled_envelope_bound S hS hQ R hR
  refine ⟨B*Real.exp (2*L),by positivity,?_⟩
  filter_upwards [htail,eventually_shifted_center_distance R,eventually_gt_atTop (0:ℕ)]
    with n hn hdist hnpos
  intro hfin x hx s hs v hv k
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  let z := x+((n:ℝ)*s)⁻¹ • v
  let r : ℝ := (n:ℝ)^(-5/12:ℝ)
  have hsub : Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
      r < sourceEuclideanNorm (x-scaledLatticePoint n i.1)) ⊆
      Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
      r/4 < sourceEuclideanNorm (z-scaledLatticePoint n i.1)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdist s hs x _ v hv (Finset.mem_filter.mp hi).2⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ ↦
    sq_nonneg ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) z‖)
  have he : -a.beams.c*(n:ℝ)*(r/4)^2 = -(a.beams.c/16)*(n:ℝ)^(1/6:ℝ) := by
    calc
      _ = -(a.beams.c/16)*((n:ℝ)*r^2) := by ring
      _ = _ := by rw [main_center_scale _ hn0]
  have hb := hn z k (r/4) (by dsimp [r]; positivity)
  rw [he] at hb
  have hexp : Real.exp (2*(n:ℝ)*S z) ≤ Real.exp (2*(n:ℝ)*S x)*Real.exp (2*L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := (le_abs_self _).trans (hshift n s hn1 hs x hx v hv)
    dsimp [z]
    nlinarith
  apply (hsum.trans hb).trans
  calc
    _ ≤ B*(n:ℝ)^(2*k.val)*(Real.exp (2*(n:ℝ)*S x)*Real.exp (2*L))*
        Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ)) := by gcongr
    _ = _ := by ring

theorem lattice_shifted_nonmain_negligible (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : Coord, ‖v‖ ≤ R → ∀ k : Fin (k0+1),
      (∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2)
          (x+((n:ℝ)*s)⁻¹ • v)‖^2) / (a.latticeSigma hUD n x)^2 ≤ ε := by
  classical
  obtain ⟨c,hc,hlo⟩ := a.lattice_variance_lower_bound hUD hU hQ hQU
  obtain ⟨C,hC,htail⟩ := a.lattice_shifted_nonmain_bound hUD hS hQ R hR
  have hlim := (tendsto_polynomial_main_center_tail (2*k0) (a.beams.c/16)
    (by have := a.beams.c_pos; positivity)).const_mul (C/c)
  simp only [mul_zero] at hlim
  filter_upwards [hlo,htail,hlim.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)]
    with n hl ht hsmall hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv k
  have hv0 : 0 < a.latticeVariance hUD n x :=
    lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hl x hx)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hp : (n:ℝ)^(2*k.val) ≤ (n:ℝ)^(2*k0) :=
    pow_le_pow_right₀ hn1 (by have := k.isLt; omega)
  rw [a.latticeSigma_sq]
  apply le_trans _ hsmall.le
  apply (div_le_iff₀ hv0).mpr
  have hh := mul_le_mul_of_nonneg_left (hl x hx)
    (by positivity : 0 ≤ (C/c)*((n:ℝ)^(2*k0)*Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ))))
  calc
    _ ≤ C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)*
        Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ)) := ht x hx s hs v hv k
    _ ≤ C*(n:ℝ)^(2*k0)*Real.exp (2*(n:ℝ)*S x)*
        Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ)) := by gcongr
    _ = ((C/c)*((n:ℝ)^(2*k0)*Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ))))*
        (c*Real.exp (2*(n:ℝ)*S x)) := by field_simp
    _ ≤ _ := hh

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
