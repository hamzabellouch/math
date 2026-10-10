import OAI.Analysis.CircleDomains.Selection.FiniteLineGaps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! The actual closed gaps have disjoint interiors; positive hole widths
make the closed gaps disjoint too. Their density integrals use at most
the density integral on the whole source segment. -/
open Set Function Filter MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem closed_gaps_disjoint {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 < (H i).2) (hfirst : Monotone (fun i => (H i).1)) :
    Pairwise (Disjoint on fun i => Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm
  obtain ⟨k,rfl⟩ := Fin.eq_castSucc_of_ne_last (show i ≠ Fin.last n by
    intro he; subst i; exact (not_lt_of_ge (Fin.le_last j)) hlt)
  obtain ⟨l,rfl⟩ := Fin.eq_succ_of_ne_zero (show j ≠ 0 by
    intro he; subst j; exact (not_lt_of_ge (Fin.zero_le _)) hlt)
  have hkl : k ≤ l := Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hlt)
  apply disjoint_left.mpr
  intro x hx hy
  dsimp only at hx hy
  rw [gapsAfterHoles_castSucc_snd] at hx
  rw [gapsAfterHoles_succ_fst] at hy
  exact (not_lt_of_ge hx.2) (((hfirst hkl).trans_lt (hvalid l)).trans_le hy.1)

 theorem closed_gap_integrals_le {ι : Type*} [Fintype ι]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i))
    (hdis : Pairwise (Disjoint on A)) {B : Set ℝ} (hB : MeasurableSet B) (hsub : ∀ i, A i ⊆ B)
    {ρ : ℝ → ℝ} (hi : IntegrableOn ρ B volume) (hρ : ∀ x ∈ B, 0 ≤ ρ x) :
    (∑ i, ∫ x in A i, ρ x) ≤ ∫ x in B, ρ x := by
  rw [← integral_iUnion_fintype hA hdis (fun i => hi.mono_set (hsub i))]
  apply setIntegral_mono_set hi
  · exact (ae_restrict_mem hB).mono (fun x hx => hρ x hx)
  · exact (iUnion_subset hsub).eventuallySubset

/-- Singleton endpoints have zero length, so even zero-width holes permit
summing the closed-gap integrals without double payment. -/
 theorem closed_gap_integrals_le_of_nonstrict {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2) (hfirst : Monotone (fun i => (H i).1))
    {B V : Set ℝ} (hB : MeasurableSet B) (hV : MeasurableSet V)
    {ρ : ℝ → ℝ} (hi : IntegrableOn ρ B volume) (hρ : ∀ x ∈ B, 0 ≤ ρ x)
    (hsub : ∀ i, Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V ⊆ B) :
    (∑ i, ∫ x in Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V, ρ x) ≤
      ∫ x in B, ρ x := by
  have he (i : Fin (n+1)) :
      (∫ x in Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V, ρ x) =
      ∫ x in Ioo (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V, ρ x := by
    apply setIntegral_congr_set
    filter_upwards [Ioo_ae_eq_Icc (μ := volume)
      (a := (gapsAfterHoles a b H i).1) (b := (gapsAfterHoles a b H i).2)] with x hx
    simp only [mem_inter_iff]
    exact propext (and_congr_left (fun _ => (iff_of_eq hx).symm))
  simp_rw [he]
  apply closed_gap_integrals_le _ (fun _ => measurableSet_Ioo.inter hV)
    (fun i j hij => (gapsAfterHoles_disjoint a b H hvalid hfirst hij).mono
      inter_subset_left inter_subset_left) hB _ hi hρ
  intro i x hx
  exact hsub i ⟨Ioo_subset_Icc_self hx.1,hx.2⟩

end CircleDomainRigidity

end

end OAI
