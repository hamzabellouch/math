import OAI.Geometry.NodalSets.Elliptic.NormalizedRescaling
import OAI.Geometry.NodalSets.Waves.ShiftedLatticeTail

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem rescaled_lattice_nonmain_negligible (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : Coord, ‖v‖ ≤ R → ∀ k : Fin (k0+1),
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val
          (normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2)
            S n s (a.latticeSigma hUD n x) x) v‖^2 ≤ ε := by
  classical
  obtain ⟨A,hA,hamp⟩ := compact_smooth_derivative_bound (rescaledSeedNormalizer S) k0
    (fun j _ ↦ (smooth_spatial_iteratedFDeriv _ (rescaledSeedNormalizer_smooth S hS) j).continuous)
    (Q ×ˢ Icc (0:ℝ) 1) (hQ.prod isCompact_Icc) R
  let C : ℝ := (2^k0*A)^2
  have hC : 0 < C := by dsimp [C]; positivity
  have hkpos : (0:ℝ) < k0+1 := by positivity
  obtain ⟨c,hc,B,hB,hsigma⟩ := a.lattice_sigma_comparison hUD hU hUb hQ hQU
  have htail := a.lattice_shifted_nonmain_negligible hUD hU hUb hQ hQU hS R hR
    (ε/(C*((k0:ℝ)+1))) (by positivity)
  filter_upwards [htail,hsigma,a.estimates,eventually_gt_atTop (0:ℕ)]
    with n hn hσ hest hnpos
  obtain ⟨hfin,ht⟩ := hn
  obtain ⟨hfin',hσ⟩ := hσ
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv k
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hσ0 : 0 < a.latticeSigma hUD n x :=
    lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hσ x hx).1
  have ha := hamp (x,s⁻¹) ⟨hx,by positivity,(inv_le_one₀ hs0).mpr hs⟩ v hv
  let F := Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
    (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1))
  have hb (i : SourceGrid U n × Fin 3) := normalizedRescaling_square_bound
    (latticeWave a.cover a.beams hUD n i.1 i.2)
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
    S hS n s _ hn1 hs hσ0 x v k0 A hA.le ha k.val (by omega)
  apply (Finset.sum_le_sum (fun i (_ : i ∈ F) ↦ hb i)).trans
  calc
    _ = C*∑ j : Fin (k0+1), ((∑ i ∈ F,
        ‖iteratedFDeriv ℝ j.val (latticeWave a.cover a.beams hUD n i.1 i.2)
          (x+((n:ℝ)*s)⁻¹ • v)‖^2)/(a.latticeSigma hUD n x)^2) := by
      dsimp only [C]
      simp only [Finset.mul_sum,Finset.sum_div,mul_div_assoc]
      rw [Finset.sum_comm]
    _ ≤ C*∑ _j : Fin (k0+1), ε/(C*((k0:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ ht x hx s hs v hv j)) hC.le
    _ = ε := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      field_simp

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
