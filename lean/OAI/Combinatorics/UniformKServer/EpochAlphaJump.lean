import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlphaSchedule
import OAI.Combinatorics.UniformKServer.EpochAlphaPieces

namespace OAI

                                     
section

/-! The actual held-size epoch jump is charged to sparse size changes, a
 side-reference refresh, or a wholesale epoch. All primitives are evaluated at
 the common-core prepared state, including the zero-input boundary. -/
noncomputable section
namespace UniformKServer.EpochAlphaJump
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

 theorem regular {a b : ι → ℝ} {A ell ct C : ℝ}
    (hp : AdaptiveAlpha.valid (EpochAlpha.regular a A ell ct C))
    (hq : AdaptiveAlpha.valid (EpochAlpha.regular b A ell ct C))
    (B v : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hpa : DomainTransport.Supported (EpochParameters.active a) B)
    (hqa : DomainTransport.Supported (EpochParameters.active b) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AdaptiveAlpha.potential (EpochAlpha.regular b A ell ct C) B v-
      AdaptiveAlpha.potential (EpochAlpha.regular a A ell ct C) B v| ≤
      8*(C*ell)*(∑ i, if a i=b i then 0 else B i) := by
  have h := AlphaParameterChanges.regular_jump hp hq rfl rfl B v hB hpa hqa hv hf
    (fun i => a i ≠ b i) (fun i hi => EpochAlphaPieces.regular_same a b A ell ct C B v hpa hqa i (not_not.mp hi))
  simpa only [AdaptiveAlpha.scale,EpochAlpha.regular,ite_not,show 4*(C*ell+C*ell)=8*(C*ell) by ring] using h

 theorem marked {a b : ι → ℝ} {A U ell ct C : ℝ}
    (oa : EpochParameters.active a) (ob : EpochParameters.active b) (ho : oa.val=ob.val)
    (hp : AdaptiveAlpha.valid (EpochAlpha.marked a A U ell ct C oa))
    (hq : AdaptiveAlpha.valid (EpochAlpha.marked b A U ell ct C ob))
    (B v : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hpa : DomainTransport.Supported (EpochParameters.active a) B)
    (hqa : DomainTransport.Supported (EpochParameters.active b) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AdaptiveAlpha.potential (EpochAlpha.marked b A U ell ct C ob) B v-
      AdaptiveAlpha.potential (EpochAlpha.marked a A U ell ct C oa) B v| ≤
      8*(C*ell)*(∑ i, if a i=b i then 0 else B i) := by
  have h := AlphaParameterChanges.marked_sparse_jump hp hq oa ob (U/A) rfl rfl ho B v hB hpa hqa hv hf
    (fun i => a i ≠ b i ∧ i ≠ oa.val) (fun i hi => EpochAlphaPieces.marked_same a b A U ell ct C oa ob ho
      B v hpa hqa i (by tauto)) (by simp)
  have hm : (∑ i, if a i ≠ b i ∧ i ≠ oa.val then B i else 0) ≤
      ∑ i, if a i=b i then 0 else B i := by
    apply sum_le_sum
    intro i _
    split_ifs <;> simp_all
  have hc : 0 ≤ 8*(C*ell) := by
    have := AdaptiveAlpha.scale_nonneg hp
    change 0 ≤ C*ell at this
    positivity
  have h' := mul_le_mul_of_nonneg_left hm hc
  change |_-_| ≤ 4*(C*ell+C*ell)*_ at h
  nlinarith

 theorem scale_bound (a : ι → ℝ) (s : EpochGeometry.State ι) (U ell ct C : ℝ)
    (hc : 0 ≤ C*ell) : AlphaEmpty.scale (EpochAlphaSchedule.config a s U ell ct C) ≤ C*ell := by
  unfold EpochAlphaSchedule.config
  split
  · split
    · exact le_rfl
    · split
      · split_ifs <;> exact le_rfl
      · exact hc
  · exact hc

 theorem total_upper {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) : EpochGeometry.total a ≤ (101/100)*EpochGeometry.total s.base := by
  have ht := EpochGeometry.total_difference s.base a
  have hc := hs.2.2.2.trans hs.2.2.1
  have := (le_abs_self _).trans (ht.trans hc)
  linarith

 theorem reference_upper {a : ι → ℝ} {o : ι} {U : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hU : EpochParameters.sideReference a o U) :
    U ≤ 2*EpochGeometry.side o a := by
  have hu := (div_le_iff₀ (by norm_num : (0:ℝ)<1001/1000)).mp hU.2.1
  linarith [EpochParameters.side_nonneg ha o]

 theorem side_input {b B : ι → ℝ} (hb : ∀ i, B i ≤ 40*b i) (o : ι) :
    (∑ i, B i)-B o ≤ 40*EpochGeometry.side o b := by
  have h := sum_le_sum (s:=univ.erase o) (fun i _ => hb i)
  rw [←mul_sum,sum_erase_eq_sub (mem_univ o)] at h
  have he : (∑ i ∈ univ.erase o, b i)=EpochGeometry.side o b := by
    rw [EpochGeometry.side]
    simp_rw [show ∀ i : ι, (if i=o then (0:ℝ) else b i)=(if i≠o then b i else 0) by intro i; split_ifs <;> simp_all]
    rw [←sum_filter]
    apply sum_congr
    · ext i; simp
    · intro i _; rfl
  rwa [he] at h

 theorem marked_sized {a b B : ι → ℝ} {s : EpochGeometry.State ι} {U ell ct C : ℝ}
    (ha : ∀ i, 0 ≤ a i)
    (hb : EpochGeometry.total b ≤ (101/100)*EpochGeometry.total s.base)
    (oa : EpochParameters.active a)
    (hA : 0 < EpochGeometry.total s.base)
    (hU : EpochParameters.sideReference a oa U) (hct : ct/ell ≤ 1)
    (hp : AdaptiveAlpha.valid (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C oa))
    (v : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hBb : ∀ i, B i ≤ 40*b i)
    (hs : DomainTransport.Supported (EpochParameters.active a) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1) (hsum : ∑ i, v i=1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AdaptiveAlpha.potential (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C oa) B v| ≤
      (C*ell)*(520*EpochGeometry.side oa.val b+246*EpochGeometry.side oa.val a) := by
  have h := AlphaParameterChanges.marked_prepared hp oa (U/EpochGeometry.total s.base) rfl B v hB hs hv hsum hf
  have hsc : 0 ≤ C*ell := AdaptiveAlpha.scale_nonneg hp
  have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
  have hSb : (∑ i, B i) ≤ 41*EpochGeometry.total s.base := by
    have hh := sum_le_sum (s:=univ) (fun i _ => hBb i)
    rw [←mul_sum] at hh
    have ht := hb
    change _ ≤ 40*EpochGeometry.total b at hh
    nlinarith [hA.le]
  have huS : (U/EpochGeometry.total s.base)*(∑ i, B i) ≤ 82*EpochGeometry.side oa.val a := by
    have h1 := mul_le_mul_of_nonneg_left hSb (div_nonneg hU.1 hA.le)
    have he : U/EpochGeometry.total s.base*(41*EpochGeometry.total s.base)=41*U := by field_simp
    rw [he] at h1
    linarith [reference_upper ha hU]
  have hc := mul_le_mul_of_nonneg_right hct (mul_nonneg (div_nonneg hU.1 hA.le) hS)
  simp only [one_mul] at hc
  have hside := side_input hBb oa.val
  have h1 := mul_le_mul_of_nonneg_left hside hsc
  have h2 := mul_le_mul_of_nonneg_left (hc.trans huS) hsc
  change |AdaptiveAlpha.potential (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C oa) B v| ≤
    13*(C*ell)*((∑ i, B i)-B oa)+3*(C*ell)*(ct/ell)*(U/EpochGeometry.total s.base)*(∑ i, B i) at h
  nlinarith

end UniformKServer.EpochAlphaJump

end


end

end OAI
