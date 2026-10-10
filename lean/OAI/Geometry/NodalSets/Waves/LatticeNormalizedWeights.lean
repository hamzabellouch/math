import OAI.Geometry.NodalSets.Waves.LatticeDerivativeTail
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

def latticeAlpha (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x : Coord) (i : SourceGrid U n × Fin 3) : ℂ :=
  latticeWave a.cover a.beams hUD n i.1 i.2 x / (a.latticeSigma hUD n x:ℂ)

lemma latticeAlpha_sum_sq (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x : Coord) (s : Finset (SourceGrid U n × Fin 3)) :
    ∑ i ∈ s, ‖a.latticeAlpha hUD n x i‖^2 =
      (∑ i ∈ s, ‖latticeWave a.cover a.beams hUD n i.1 i.2 x‖^2) / a.latticeVariance hUD n x := by
  simp only [latticeAlpha,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ a.latticeSigma hUD n x from Real.sqrt_nonneg _),
    div_pow,a.latticeSigma_sq,Finset.sum_div]

lemma latticeAlpha_total (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x : Coord) (hv : 0 < a.latticeVariance hUD n x) :
    ∑ i, ‖a.latticeAlpha hUD n x i‖^2 = 1 := by
  rw [a.latticeAlpha_sum_sq]
  exact div_self hv.ne'

theorem latticeAlpha_nonmain_bound (hUD : U ⊆ D) (hU : IsOpen U)
    {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x ∈ Q,
      0 < a.latticeVariance hUD n x ∧
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖a.latticeAlpha hUD n x i‖^2 ≤ C*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)) := by
  classical
  obtain ⟨c,hc,hlo⟩ := a.lattice_variance_lower_bound hUD hU hQ hQU
  obtain ⟨C,hC,htail⟩ := a.lattice_nonmain_derivative_bound hUD
  refine ⟨C/c,div_pos hC hc,?_⟩
  filter_upwards [hlo,htail] with n hl ht
  intro hfin x hx
  have hv : 0 < a.latticeVariance hUD n x :=
    lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hl x hx)
  refine ⟨hv,?_⟩
  rw [a.latticeAlpha_sum_sq]
  apply (div_le_iff₀ hv).mpr
  have h := ht x (0 : Fin (k0+1))
  simp only [Fin.val_zero,mul_zero,pow_zero,mul_one] at h
  change (∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
      (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
    ‖iteratedFDeriv ℝ 0 (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2) ≤ _ at h
  simp only [norm_iteratedFDeriv_zero] at h
  refine h.trans ?_
  have hh := mul_le_mul_of_nonneg_left (hl x hx)
    (by positivity : 0 ≤ (C/c)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)))
  calc
    _ = ((C/c)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)))*(c*Real.exp (2*(n:ℝ)*S x)) := by field_simp
    _ ≤ _ := hh

theorem latticeAlpha_main_mass (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, (∑ i, ‖a.latticeAlpha hUD n x i‖^2 = 1) ∧
        1-ε ≤ ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)),
          ‖a.latticeAlpha hUD n x i‖^2 := by
  classical
  obtain ⟨C,hC,hb⟩ := a.latticeAlpha_nonmain_bound hUD hU hQ hQU
  have hlim := (tendsto_main_center_tail a.beams.c a.beams.c_pos).const_mul C
  simp only [mul_zero] at hlim
  filter_upwards [hb,hlim.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)] with n hn hsmall hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  refine ⟨hfin,?_⟩
  intro x hx
  obtain ⟨hv,ht⟩ := hn x hx
  have hall := a.latticeAlpha_total hUD n x hv
  refine ⟨hall,?_⟩
  have he := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (SourceGrid U n × Fin 3)))
    (fun i ↦ sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ))
    (fun i ↦ ‖a.latticeAlpha hUD n x i‖^2)
  simp only [not_le,hall] at he
  linarith

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
