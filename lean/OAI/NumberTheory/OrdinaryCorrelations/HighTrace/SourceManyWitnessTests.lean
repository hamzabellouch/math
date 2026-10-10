import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourcePolyDivTendsto
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExceptionalBudget
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ResidualRankPrivateFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Precedes

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SourceCylinder
open Finset Classical Filter

lemma source_many_witness_tests :
    ∀ᶠ B : ℝ in atTop, B^(2*epsilon) ≤ (listCutoff B/5:ℕ) := by
  filter_upwards [eventually_const_mul_rpow_le (2*epsilon) (4*epsilon) 10
    (by norm_num [epsilon]),eventually_ge_atTop (1:ℝ)] with B hbig hB
  have hx : (1:ℝ) ≤ B^(2*epsilon) := Real.one_le_rpow hB (by norm_num [epsilon])
  have hc : B^(4*epsilon) ≤ (listCutoff B:ℝ) := Nat.le_ceil _
  have hm : listCutoff B ≤ 5*(listCutoff B/5)+4 := by
    have hh := Nat.mod_lt (listCutoff B) (by norm_num : 0 < 5)
    omega
  have hm' : (listCutoff B:ℝ) ≤ 5*(listCutoff B/5:ℕ)+4 := by exact_mod_cast hm
  nlinarith

theorem source_residual_witness_certificates (h : ℕ) (hh : 0 < h) (τ C₀ : ℝ)
    (hτ : τ < 2) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (w : ClosedLine h (sourceLength B)) (a : (sourceSystem B).FixedResidues w)
      (c : Cylinder (fun p : (sourceSystem B).FreeIndex w => ZMod (p.val:ℕ)))
      (z : (sourceSystem B).FreeResidues w),
      listCutoff B ≤ Cylinder.rank (residualEvents w D (pathLength B) a) c → c.Holds z →
      ∃ (F : PrivateFamily w D (pathLength B) (listCutoff B))
        (mode : PrivateFamily.Case) (A : Finset (Fin (listCutoff B)))
        (t : ∀ j : A, F.Test j.val),
        B^(2*epsilon) ≤ (A.card:ℝ) ∧
        (∀ j, (t j).Valid) ∧
        Function.Injective (fun j : A => (t j).selected) ∧
        (∀ i j : A, mode.Precedes i.val j.val → ((t j).selected:ℕ) ∉ (t i).support) ∧
        (∀ j, if (t j).Linear then ¬(((t j).modulus:ℕ):ℤ) ∣ (t j).coefficient
          else (t j).expression ≠ 0) ∧
        (∀ j, (((t j).modulus:ℕ):ℤ) ∣ (t j).expression) := by
  filter_upwards [source_many_witness_tests,source_eventually_large h] with B hmany hB
  intro D w a c z hr hz
  have hx : (1:ℝ) ≤ B^(4*epsilon) := Real.one_le_rpow hB.1 (by norm_num [epsilon])
  have htp : 0 < listCutoff B := by
    have hh := hx.trans (Nat.le_ceil (B^(4*epsilon)))
    change (1:ℝ) ≤ (listCutoff B:ℝ) at hh
    have : 1 ≤ listCutoff B := by exact_mod_cast hh
    omega
  obtain ⟨F,hF⟩ := residual_rank_private_family w a c htp hr z hz
  have hpp (j : Fin (listCutoff B)) : h < ((F.witness j).spec.extra:ℕ) :=
    (hB.2 (F.witness j).spec.extra).2
  have hpL (j : Fin (listCutoff B)) : pathLength B < ((F.witness j).spec.extra:ℕ) := by
    have hL : pathLength B ≤ ⌊B⌋₊ := Nat.floor_le_floor
      (Real.rpow_le_self_of_one_le hB.1 (by norm_num [rho]))
    have hp := (hB.2 (F.witness j).spec.extra).1
    simp only [sourceLength] at hp
    omega
  obtain ⟨mode,A,t,hcard,ht,hinj,hfuture,hnd,hholds⟩ := F.triangular_tests hh hτ hpp hpL
  refine ⟨F,mode,A,t,hmany.trans (by exact_mod_cast hcard),ht,hinj,hfuture,hnd,?_⟩
  intro j
  exact (t j).holds_residues (ht j) (mergeResidues w a z) hF

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
