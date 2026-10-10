import OAI.Analysis.CircleDomains.Probability.CompactMeasureMajorants
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.CompactlySupported

namespace OAI

/-! The actual least L² cost of a bounded continuous majorant on a compact
family of finite measures. Feasibility follows from its positive minimum
mass; sublinearity follows from the triangle inequality in L². -/
open Set MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  (σ : Measure Z) [IsFiniteMeasure σ] (S : Set (FiniteMeasure Z))

private def majorantNorms (u : C_c(S,ℝ)) : Set ℝ :=
  {r | ∃ f : Z →ᵇ ℝ, (∀ v : S, u v ≤ compactMeasureTestOperator S f v) ∧
    ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ = r}

def compactMeasureMajorantCost (u : C_c(S,ℝ)) : ℝ := sInf (majorantNorms σ S u)

private lemma majorantNorms_bddBelow (u : C_c(S,ℝ)) : BddBelow (majorantNorms σ S u) :=
  ⟨0,fun _ ⟨_,_,he⟩ => he ▸ norm_nonneg _⟩

variable {S}

private lemma majorantNorms_nonempty (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S] (u : C_c(S,ℝ)) :
    (majorantNorms σ S u).Nonempty := by
  obtain ⟨r,_,hr⟩ := exists_compact_measure_constant_majorant hS hne hz u.toContinuousMap
  exact ⟨_,BoundedContinuousFunction.const Z r,hr,rfl⟩

lemma compactMeasureMajorantCost_nonneg (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S] (u : C_c(S,ℝ)) :
    0 ≤ compactMeasureMajorantCost σ S u :=
  le_csInf (majorantNorms_nonempty σ hS hne hz u)
    (fun _ ⟨_,_,he⟩ => he ▸ norm_nonneg _)

lemma le_compactMeasureMajorantCost (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S]
    (u : C_c(S,ℝ)) {a : ℝ}
    (ha : ∀ f : Z →ᵇ ℝ, (∀ v : S, u v ≤ compactMeasureTestOperator S f v) →
      a ≤ ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖) :
    a ≤ compactMeasureMajorantCost σ S u := by
  apply le_csInf (majorantNorms_nonempty σ hS hne hz u)
  rintro _ ⟨f,hf,rfl⟩
  exact ha f hf

lemma compactMeasureMajorantCost_le (u : C_c(S,ℝ)) (f : Z →ᵇ ℝ)
    (hf : ∀ v : S, u v ≤ compactMeasureTestOperator S f v) :
    compactMeasureMajorantCost σ S u ≤ ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ :=
  csInf_le (majorantNorms_bddBelow σ S u) ⟨f,hf,rfl⟩

lemma compactMeasureMajorantCost_nonpos (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S]
    (u : C_c(S,ℝ)) (hu : ∀ v, u v ≤ 0) : compactMeasureMajorantCost σ S u = 0 := by
  apply le_antisymm _ (compactMeasureMajorantCost_nonneg σ hS hne hz u)
  have hb := compactMeasureMajorantCost_le σ u (0 : Z →ᵇ ℝ)
    (fun v => by simpa using hu v)
  simpa using hb

lemma compactMeasureMajorantCost_smul_le (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S]
    (r : ℝ) (hr : 0 < r) (u : C_c(S,ℝ)) :
    compactMeasureMajorantCost σ S (r • u) ≤ r * compactMeasureMajorantCost σ S u := by
  have hdiv : compactMeasureMajorantCost σ S (r • u) / r ≤
      compactMeasureMajorantCost σ S u := by
    apply le_csInf (majorantNorms_nonempty σ hS hne hz u)
    rintro _ ⟨f,hf,rfl⟩
    apply (div_le_iff₀ hr).mpr
    have hb := compactMeasureMajorantCost_le σ (r • u) (r • f) (fun v => by
      simpa using mul_le_mul_of_nonneg_left (hf v) hr.le)
    simpa only [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hr,smul_eq_mul,mul_comm] using hb
  have hb := (div_le_iff₀ hr).mp hdiv
  simpa only [mul_comm] using hb

lemma compactMeasureMajorantCost_smul (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S]
    (r : ℝ) (hr : 0 < r) (u : C_c(S,ℝ)) :
    compactMeasureMajorantCost σ S (r • u) = r * compactMeasureMajorantCost σ S u := by
  apply le_antisymm (compactMeasureMajorantCost_smul_le σ hS hne hz r hr u)
  have hb := compactMeasureMajorantCost_smul_le σ hS hne hz r⁻¹ (inv_pos.mpr hr) (r • u)
  rw [inv_smul_smul₀ hr.ne'] at hb
  have hc := mul_le_mul_of_nonneg_left hb hr.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] using hc

lemma compactMeasureMajorantCost_add (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S] (u v : C_c(S,ℝ)) :
    compactMeasureMajorantCost σ S (u+v) ≤
      compactMeasureMajorantCost σ S u + compactMeasureMajorantCost σ S v := by
  have hb (f g : Z →ᵇ ℝ)
      (hf : ∀ a : S, u a ≤ compactMeasureTestOperator S f a)
      (hg : ∀ a : S, v a ≤ compactMeasureTestOperator S g a) :
      compactMeasureMajorantCost σ S (u+v) ≤
        ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ + ‖BoundedContinuousFunction.toLp 2 σ ℝ g‖ := by
    have hfg := compactMeasureMajorantCost_le σ (u+v) (f+g) (fun a => by
      simpa using add_le_add (hf a) (hg a))
    have hn := norm_add_le (BoundedContinuousFunction.toLp 2 σ ℝ f)
      (BoundedContinuousFunction.toLp 2 σ ℝ g)
    exact hfg.trans (by simpa only [map_add] using hn)
  have hu (f : Z →ᵇ ℝ) (hf : ∀ a : S, u a ≤ compactMeasureTestOperator S f a) :
      compactMeasureMajorantCost σ S (u+v) - ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ ≤
        compactMeasureMajorantCost σ S v := by
    apply le_csInf (majorantNorms_nonempty σ hS hne hz v)
    rintro _ ⟨g,hg,rfl⟩
    linarith [hb f g hf hg]
  have hv : compactMeasureMajorantCost σ S (u+v) - compactMeasureMajorantCost σ S v ≤
      compactMeasureMajorantCost σ S u := by
    apply le_csInf (majorantNorms_nonempty σ hS hne hz u)
    rintro _ ⟨f,hf,rfl⟩
    linarith [hu f hf]
  linarith

end CircleDomainRigidity

end

end OAI
