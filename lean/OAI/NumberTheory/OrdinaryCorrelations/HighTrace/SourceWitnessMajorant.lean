import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceManyWitnessTests
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessError
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AvgFintypeChange
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NumericalLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CylinderBudget

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SourceCylinder OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter

namespace NumericalLine

noncomputable def sourceWitnessMajorant {B τ C₀ : ℝ}
    (D : (sourceSystem B).DivisorFamily B τ C₀) (h : ℕ) : ℝ :=
  cylinderBudget (sourceListSlotBudget C₀ B) *
    ∑ w : NumericalLine D h (sourceLength B),
      ∑ l ∈ boundedLists (AttachedSpec w.line D (pathLength B)) (listCutoff B),
        ∑ F : PrivateFamily w.line D (pathLength B) (listCutoff B),
          crudeListWeight w.line (l++List.ofFn F.witness)

lemma sourceWitnessError_le_majorant {B τ C₀ T : ℝ}
    (D : (sourceSystem B).DivisorFamily B τ C₀) {h : ℕ} (hh : 0 < h)
    (K₀ : ℝ) (cut : (sourceSystem B).Cutoffs T) (hB : 1 ≤ B) :
    sourceWitnessError D hh K₀ cut ≤ sourceWitnessMajorant D h := by
  apply mul_le_mul_of_nonneg_left _ (cylinderBudget_nonneg _)
  exact sum_le_sum (fun w hw => residualWitnessIntegral_le_crude_list_sum w.line w.labels cut
    (sourceRetained hh K₀ w) (listCutoff_pos hB))

theorem source_retained_allowed_with_witness_majorant (h : ℕ) (hh : 0 < h)
    (τ T C₀ K₀ : ℝ) (hτ : 1 ≤ τ) (hC₀ : 0 ≤ C₀) (hK₀ : 0 ≤ K₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      sourceAllowedRetainedSum D hh K₀ cut ≤
        B^(-(1+2*eta)*(sourceLength B:ℝ)) + sourceWitnessMajorant D h := by
  filter_upwards [source_retained_allowed_with_error h hh τ T C₀ K₀ hτ hC₀ hK₀,
    eventually_ge_atTop (1:ℝ)] with B hb hB
  intro D cut
  exact (hb D cut).trans (add_le_add le_rfl (sourceWitnessError_le_majorant D hh K₀ cut hB))

end NumericalLine

theorem source_crude_witness_tests (h : ℕ) (hh : 0 < h) (τ C₀ : ℝ) (hτ : τ < 2) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (w : ClosedLine h (sourceLength B))
      (l : List (AttachedSpec w D (pathLength B)))
      (F : PrivateFamily w D (pathLength B) (listCutoff B)),
      JointlyRealizable w (l++List.ofFn F.witness) →
      ∃ (mode : PrivateFamily.Case) (A : Finset (Fin (listCutoff B)))
        (t : ∀ j : A, F.Test j.val),
        B^(2*epsilon) ≤ (A.card:ℝ) ∧
        (∀ j, (t j).Valid) ∧
        Function.Injective (fun j : A => (t j).selected) ∧
        (∀ i j : A, mode.Precedes i.val j.val → ((t j).selected:ℕ) ∉ (t i).support) ∧
        (∀ j, if (t j).Linear then ¬(((t j).modulus:ℕ):ℤ) ∣ (t j).coefficient
          else (t j).expression ≠ 0) ∧
        (∀ j, (((t j).modulus:ℕ):ℤ) ∣ (t j).expression) := by
  filter_upwards [source_many_witness_tests,source_eventually_large h] with B hmany hB
  intro D w l F hj
  obtain ⟨r,hr⟩ := hj
  have hq (j) (p) : (F.witness j).spec.ResidueTest p (F.witness j).vertex (r p) :=
    hr (F.witness j) (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)) p
  have hpp (j) : h < ((F.witness j).spec.extra:ℕ) := by
    exact lt_of_lt_of_le (hB.2 (F.witness j).spec.extra).2 (le_refl _)
  have hpL (j) : pathLength B < ((F.witness j).spec.extra:ℕ) := by
    have hL : pathLength B ≤ ⌊B⌋₊ := Nat.floor_le_floor
      (Real.rpow_le_self_of_one_le hB.1 (by norm_num [rho]))
    have hp := (hB.2 (F.witness j).spec.extra).1
    simp only [sourceLength] at hp
    omega
  obtain ⟨mode,A,t,hcard,ht,hinj,hfuture,hnd,hholds⟩ := F.triangular_tests hh hτ hpp hpL
  refine ⟨mode,A,t,hmany.trans (by exact_mod_cast hcard),ht,hinj,hfuture,hnd,?_⟩
  intro j
  exact (t j).holds_residues (ht j) r hq

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
