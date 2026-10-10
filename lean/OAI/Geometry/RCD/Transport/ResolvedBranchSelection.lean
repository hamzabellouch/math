import OAI.Geometry.RCD.Transport.ResolvedBranchWindow
import OAI.Geometry.RCD.Metric.RealSliceSelection

namespace OAI

/-! # Quantitative selection of two branches with a common past

The chosen pair restriction has mass at least a fixed multiple of the time
mesh, equal past marginals, and mutually singular future marginals.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem select_resolved_branches (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ]
    (hσ : σ univ ≠ 0) (T S q : Time) (hTS : T ≤ S) (hSq : S ≤ q)
    (h0 : ∀ᵐ z ∂σ, z.1 0=z.2 0)
    (hroot : ∀ᵐ z ∂σ, (T:ℝ) ≤ (lastPathAgreement q z:ℝ) ∧
      (lastPathAgreement q z:ℝ) < (S:ℝ)) {n : ℕ} (hn : 0 < n) :
    ∃ s t : Time, ∃ κ : Measure (C(Time,X)×C(Time,X)),
      T ≤ s ∧ s ≤ t ∧ t ≤ S ∧ (t:ℝ)-(s:ℝ)=((S:ℝ)-(T:ℝ))/(n:ℝ) ∧
      κ ≤ σ ∧ σ.real univ/(5*(n:ℝ)) < κ.real univ ∧
      (∀ r : Time, r ≤ s → κ.map (fun z => z.1 r)=κ.map (fun z => resolvePathBranch q z r)) ∧
      κ.map (fun z => z.1 t) ⟂ₘ κ.map (fun z => resolvePathBranch q z t) := by
  have hmeas : Measurable (fun z : C(Time,X)×C(Time,X) => (lastPathAgreement q z:ℝ)) :=
    (measurable_lastPathAgreement q).subtype_coe
  obtain ⟨k,hk,hmass⟩ := exists_large_real_slice σ hmeas (show (T:ℝ) ≤ (S:ℝ) from hTS) hroot hn
  have hmono := intervalGrid_monotone (show (T:ℝ) ≤ (S:ℝ) from hTS) hn
  have hslo : (T:ℝ) ≤ intervalGrid T S n k := by
    simpa only [intervalGrid_zero] using hmono (Nat.zero_le k)
  have hst : intervalGrid T S n k ≤ intervalGrid T S n (k+1) := hmono (Nat.le_succ k)
  have hthi : intervalGrid T S n (k+1) ≤ (S:ℝ) := by
    simpa only [intervalGrid_self _ _ hn] using hmono (Nat.succ_le_of_lt hk)
  let s : Time := ⟨intervalGrid T S n k,⟨T.property.1.trans hslo,(hst.trans hthi).trans S.property.2⟩⟩
  let t : Time := ⟨intervalGrid T S n (k+1),⟨T.property.1.trans (hslo.trans hst),hthi.trans S.property.2⟩⟩
  let F : Set (C(Time,X)×C(Time,X)) :=
    {z | (s:ℝ) ≤ (lastPathAgreement q z:ℝ) ∧ (lastPathAgreement q z:ℝ) < (t:ℝ)}
  have hF : MeasurableSet F :=
    (measurableSet_le measurable_const hmeas).inter (measurableSet_lt hmeas measurable_const)
  let ρ := σ.restrict F
  have hρmass : σ.real univ/(n:ℝ) ≤ ρ.real univ := by
    simpa only [ρ,F,s,t,Measure.real,Measure.restrict_apply_univ] using hmass
  have hσpos : 0 < σ.real univ := ENNReal.toReal_pos hσ (measure_ne_top _ _)
  have hρpos : 0 < ρ.real univ := lt_of_lt_of_le (div_pos hσpos (by positivity)) hρmass
  have hρ0 : ∀ᵐ z ∂ρ, z.1 0=z.2 0 :=
    h0.filter_mono Measure.restrict_le_self.absolutelyContinuous.ae_le
  have hne : ∀ᵐ z ∂ρ, z.1 t ≠ resolvePathBranch q z t := by
    filter_upwards [ae_restrict_mem hF,hρ0] with z hz hz0
    exact resolvePathBranch_ne_after q z hz0 hz.2 (le_trans (show t ≤ S from hthi) hSq)
  have hdiff : ρ.real {z | z.1 t ≠ resolvePathBranch q z t}=ρ.real univ := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hne] with z hz
    change (z.1 t ≠ resolvePathBranch q z t)=True
    exact propext ⟨fun _ => trivial,fun _ => hz⟩
  obtain ⟨A,hA,hcut,hsing⟩ := exists_separated_restriction ρ
    (f:=fun z => z.1 t) (g:=fun z => resolvePathBranch q z t)
    ((measurable_path_eval t).comp measurable_fst)
    ((measurable_path_eval t).comp (measurable_resolvePathBranch q))
    (by rw [hdiff]; exact hρpos)
  let κ := ρ.restrict A
  have hκρ : κ ≤ ρ := Measure.restrict_le_self
  have hκσ : κ ≤ σ := hκρ.trans Measure.restrict_le_self
  refine ⟨s,t,κ,hslo,hst,hthi,?_,hκσ,?_,?_,hsing⟩
  · change intervalGrid T S n (k+1)-intervalGrid T S n k=_
    simp only [intervalGrid,Nat.cast_add,Nat.cast_one]
    ring
  · rw [hdiff] at hcut
    have h := div_le_div_of_nonneg_right hρmass (by norm_num : (0:ℝ) ≤ 5)
    have h' : σ.real univ/(5*(n:ℝ)) ≤ ρ.real univ/5 := by
      simpa only [div_div,mul_comm] using h
    exact h'.trans_lt hcut
  · intro r hr
    apply Measure.map_congr
    filter_upwards [(ae_restrict_mem hF).filter_mono hκρ.absolutelyContinuous.ae_le,
      h0.filter_mono hκσ.absolutelyContinuous.ae_le] with z hz hz0
    rw [resolvePathBranch_apply q z hz0,
      ite_eq_left (hr.trans (show s ≤ lastPathAgreement q z from hz.1))]

end RegularPointCoordinates

end

end OAI
