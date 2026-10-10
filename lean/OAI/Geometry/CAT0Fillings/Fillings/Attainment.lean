import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.PushMajorant
import OAI.Geometry.CAT0Fillings.Reconstruction.JointCharts

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations SliceReconstruction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma NormalApprox.boundarySucc {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) : NormalApprox k (boundarySucc T) := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := h
  refine ⟨C,fun j => CAT0Fillings.boundarySucc (Ts j),fun j => (hTs j).boundarySucc,hN,?_,
    boundarySucc_weak_limit hlim⟩
  intro j
  cases k with
  | zero => simp only [boundary,mass_zero];positivity
  | succ k =>
    change mass (CAT0Fillings.boundarySucc (CAT0Fillings.boundarySucc (Ts j))) ≤ C
    rw [Foundations.boundarySucc_boundarySucc (hTs j).1,mass_zero]
    positivity

lemma NormalApprox.integerRectifiable {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X) : IntegerRectifiable T := by
  cases k with
  | zero => exact h.integral_zero.2
  | succ k => exact integerRectifiable_succ_of_normalApprox h hX

theorem NormalApprox.integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X) : IsIntegral k T := by
  cases k with
  | zero => exact h.integral_zero
  | succ k => exact ⟨h.metric,h.integerRectifiable hX,
      h.boundarySucc.metric,h.boundarySucc.integerRectifiable hX⟩

theorem integral_weak_closed {k : ℕ} {Ts : ℕ → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsIntegral k (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundary (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) : IsIntegral k T :=
  (normalApprox_of_weak_limit hTs M N hM hN hlim).integral hX

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem exists_integral_weak_subsequence {k : ℕ} {Ts : ℕ → Functional X (k+1+1)}
    (hTs : ∀ j, IsIntegral (k+1+1) (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hX : IsCAT0 X) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧ ∃ T : Functional X (k+1+1),
      IsIntegral (k+1+1) T ∧ mass T ≤ M ∧ mass (boundarySucc T) ≤ N ∧
      ∀ b π, Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (T b π)) := by
  obtain ⟨ψ,hψ,T,_,_,hTM,hTN,hlim⟩ := exists_normal_weak_subsequence_of_integral_mass_bound hTs M N hM hN
  exact ⟨ψ,hψ,T,integral_weak_closed (fun j => hTs (ψ j)) M N
    (fun j => hM (ψ j)) (fun j => hN (ψ j)) hlim hX,hTM,hTN,hlim⟩

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem mass_le_of_mass_tendsto {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {Ts : ℕ → Functional X k}
    {T : Functional X k} (hTs : ∀ j, IsMetricCurrent (Ts j)) {m : ℝ}
    (hm : Tendsto (fun j => mass (Ts j)) atTop (𝓝 m))
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    mass T ≤ m := by
  have hm0 : 0 ≤ m := ge_of_tendsto hm (Eventually.of_forall fun j => mass_nonneg (Ts j))
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.eventually (gt_mem_nhds (lt_add_of_pos_right m hε)))
  exact mass_le_of_bounded_weak_limit (⟨m+ε,by positivity⟩ : ℝ≥0)
    (fun j => hTs (j+N)) (fun j => (hN (j+N) (Nat.le_add_left N j)).le)
    (fun b π _ => (hlim b π).comp (tendsto_add_atTop_nat N))

noncomputable def fillingVolume {k : ℕ} (T : Functional X (k+1)) : ℝ :=
  sInf {r : ℝ | ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧
    boundarySucc S = T ∧ r = mass S}

lemma fillingVolume_nonneg {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ}
    (T : Functional X (k+1)) : 0 ≤ fillingVolume T := by
  apply Real.sInf_nonneg
  rintro r ⟨S,_,_,rfl⟩
  exact mass_nonneg S

lemma fillingVolume_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ}
    {T : Functional X (k+1)} {S : Functional X (k+2)}
    (hS : IsIntegral (k+2) S) (hb : boundarySucc S = T) : fillingVolume T ≤ mass S := by
  apply csInf_le
  · exact ⟨0,by rintro r ⟨U,_,_,rfl⟩; exact mass_nonneg U⟩
  · exact ⟨S,hS,hb,rfl⟩

theorem exists_filling_mass_eq (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
    (hex : ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S = fillingVolume T := by
  let A : Set ℝ := {r | ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧
    boundarySucc S = T ∧ r = mass S}
  have hA : A.Nonempty := by
    obtain ⟨S,hS,hb⟩ := hex
    exact ⟨mass S,S,hS,hb,rfl⟩
  have hAl : BddBelow A := ⟨0,by rintro r ⟨S,_,_,rfl⟩; exact mass_nonneg S⟩
  obtain ⟨u,hu,hlim,huA⟩ := exists_seq_tendsto_sInf hA hAl
  choose Ts hTs hb hm using huA
  have hu0 : 0 ≤ u 0 := by rw [hm]; exact mass_nonneg _
  obtain ⟨ψ,hψ,S,hS,_,_,hweak⟩ := exists_integral_weak_subsequence hTs
    (⟨u 0,hu0⟩ : ℝ≥0) (⟨mass T,mass_nonneg T⟩ : ℝ≥0)
    (fun j => by rw [←hm]; exact hu (Nat.zero_le j)) (fun j => by simp only [hb]; rfl) hX
  have hboundary : boundarySucc S = T := by
    funext b π
    apply tendsto_nhds_unique (boundarySucc_weak_limit hweak b π)
    simpa only [hb] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => T b π) atTop (𝓝 (T b π)))
  refine ⟨S,hS,hboundary,le_antisymm ?_ (fillingVolume_le hS hboundary)⟩
  apply mass_le_of_mass_tendsto (fun j => (hTs (ψ j)).1) _ hweak
  simpa only [Function.comp_def,hm,fillingVolume,A] using hlim.comp hψ.tendsto_atTop

 theorem IsCAT0.exists_minimal_integral_filling (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S = fillingVolume T := by
  obtain ⟨S,hS,hb,_⟩ := hX.exists_integral_filling_diam hT hz
  exact exists_filling_mass_eq hX ⟨S,hS,hb⟩

lemma IsCAT0.fillingVolume_le_linear (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    fillingVolume T ≤ (k+2:ℝ)*Metric.diam (univ : Set X)*mass T := by
  obtain ⟨S,hS,hb,hm⟩ := hX.exists_integral_filling_diam hT hz
  exact (fillingVolume_le hS hb).trans hm

end CAT0Fillings
end

end OAI
