import OAI.Combinatorics.ContingencyTables.Machines.EnumerationPointBounds
import OAI.Combinatorics.ContingencyTables.Sampling.PaddedEnumerationBounds
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileMatrixProgram
import OAI.Combinatorics.ContingencyTables.Sampling.UnitMatrixProgram

namespace OAI

/-! # Bounding the nested measures of the executed profile tabulation -/

namespace ContingencyTables.MeasuredMap
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma listMeasure_le {A B : Type} [Codec A] [Codec B] (μ : A×B → ℕ)
    (a : A) (bs : List B) (M : ℕ) (h : ∀ b∈bs,μ (a,b) ≤ M) :
    listMeasure μ (a,bs) ≤ weight (a,bs)+bs.length*M := by
  have hs := ProfilePrograms.list_sum_le_length_mul
    (bs.map (fun b => μ (a,b))) M (by
      intro n hn
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hn
      exact h b hb)
  simpa only [listMeasure,List.length_map] using Nat.add_le_add_left hs (weight (a,bs))

lemma listMeasure_mono {A B : Type} [Codec A] [Codec B] (μ ν : A×B → ℕ)
    (a : A) (bs : List B) (h : ∀ b∈bs,μ (a,b) ≤ ν (a,b)) :
    listMeasure μ (a,bs) ≤ listMeasure ν (a,bs) := by
  have hs : (bs.map (fun b => μ (a,b))).sum ≤ (bs.map (fun b => ν (a,b))).sum := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add (h b (by simp))
        (ih (by intro c hc; exact h c (by simp [hc])))
  exact Nat.add_le_add_left hs _

end ContingencyTables.MeasuredMap

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma list_weight_bound {A : Type} [Codec A] (as : List A) (W : ℕ)
    (h : ∀ a∈as,weight a ≤ W) : weight as ≤ as.length*(W+1)+1 := by
  simpa only [List.map_id,id_eq] using weight_map_bound (f := id) (as := as) h

/-- The two loops over the profile box cost a polynomial in its
cardinality and the uniform measure of a single transition entry. -/
lemma profileMatrixMeasure_le (z : MatrixParameters) (W M : ℕ)
    (hz : weight z ≤ W)
    (hv : ∀ v∈profileBoxViews (matrixData z),weight v ≤ W)
    (he : ∀ u∈profileBoxViews (matrixData z),∀ v∈profileBoxViews (matrixData z),
      matrixEntryMeasure (z,(u,v)) ≤ M) :
    let N := gridStateCount (profileEnumerationData (matrixData z))
    profileMatrixMeasure z ≤ (N+1)^2*(M+3*W+7) := by
  let vs := profileBoxViews (matrixData z)
  let N := gridStateCount (profileEnumerationData (matrixData z))
  have hlen : vs.length=N := profileBoxViews_length _
  have hvs : weight vs ≤ N*(W+1)+1 := by
    simpa only [hlen] using list_weight_bound vs W hv
  have hc (v : List ℕ×List ℕ) (hv' : v∈vs) :
      matrixColumnMeasure (z,v) ≤ (N+1)*(M+2*W+4) := by
    have hpair : weight ((z,v),vs) ≤ (N+1)*(2*W+3) := by
      have hw := hv v hv'
      simp only [weight_prod]
      nlinarith
    have hsum := MeasuredMap.listMeasure_le columnEntryMeasure (z,v) vs M (by
      intro u hu
      exact he u hu v hv')
    have hh : matrixColumnMeasure (z,v) ≤ N+(N+1)*(2*W+3)+N*M := by
      unfold matrixColumnMeasure
      change N+MeasuredMap.listMeasure columnEntryMeasure ( (z,v),vs) ≤ _
      rw [hlen] at hsum
      omega
    exact hh.trans (by nlinarith)
  have hout : weight (z,vs) ≤ (N+1)*(W+2) := by
    simp only [weight_prod]
    nlinarith
  have hs := MeasuredMap.listMeasure_le matrixColumnMeasure z vs
    ((N+1)*(M+2*W+4)) hc
  rw [hlen] at hs
  have hm : profileMatrixMeasure z ≤
      N+(N+1)*(W+2)+N*((N+1)*(M+2*W+4)) := by
    unfold profileMatrixMeasure
    change N+MeasuredMap.listMeasure matrixColumnMeasure (z,vs) ≤ _
    omega
  have h1 : N ≤ (N+1)^2 := by nlinarith
  have h2 : N+1 ≤ (N+1)^2 := Nat.le_self_pow (by decide) _
  have h3 : N*(N+1) ≤ (N+1)^2 := by nlinarith
  calc
    _ ≤ N+(N+1)*(W+2)+N*((N+1)*(M+2*W+4)) := hm
    _ ≤ (N+1)^2+(N+1)^2*(W+2)+(N+1)^2*(M+2*W+4) := by
      exact Nat.add_le_add (Nat.add_le_add h1 (Nat.mul_le_mul_right _ h2))
        (by rw [←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h3)
    _ = (N+1)^2*(M+3*W+7) := by ring

lemma unitMatrixMeasure_le (z : MatrixParameters) :
    UnitCountPrograms.profileMatrixMeasure z ≤ profileMatrixMeasure z := by
  unfold UnitCountPrograms.profileMatrixMeasure profileMatrixMeasure
  apply Nat.add_le_add_left
  apply MeasuredMap.listMeasure_mono
  intro v _
  unfold UnitCountPrograms.matrixColumnMeasure matrixColumnMeasure
  apply Nat.add_le_add_left
  apply MeasuredMap.listMeasure_mono
  intro u _
  change UnitCountPrograms.entryMeasure (columnEntryInput ((z,v),u)) ≤
    matrixEntryMeasure (columnEntryInput ((z,v),u))
  unfold UnitCountPrograms.entryMeasure matrixEntryMeasure
  omega

end ContingencyTables.ProfilePrograms

end OAI
