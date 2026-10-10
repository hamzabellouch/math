import Mathlib
import OAI.Probability.SphericalField.Fields.HeightWord

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

def heightIndicator (r t : ℝ) : ℝ := if r < t then 1 else 0

lemma heightIndicator_antitone (t : ℝ) : Antitone (fun r => heightIndicator r t) := by
  intro r s hrs
  dsimp only [heightIndicator]
  split_ifs with hs hr
  · rfl
  · exact (hr (hrs.trans_lt hs)).elim
  · norm_num
  · rfl

lemma heightIndicator_weighted_sum {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (r : ℝ) (hr : r ∈ Set.range z) :
    (∑ j, heightVariances z j*heightIndicator r (z j.succ))=2*(z (Fin.last K)-r) := by
  have he (j : Fin K) : heightVariances z j*heightIndicator r (z j.succ)=
      heightVariances z j-(if z j.succ ≤ r then heightVariances z j else 0) := by
    unfold heightIndicator
    by_cases hj : z j.succ ≤ r
    · simp [hj,not_lt.mpr hj]
    · simp [hj,lt_of_not_ge hj]
  simp only [he,Finset.sum_sub_distrib,heightVariances_prefix z hz r hr,heightVariances_sum]
  ring

lemma heightIndicator_distance_sum {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (r s : ℝ) (hr : r ∈ Set.range z) (hs : s ∈ Set.range z) :
    (∑ j, heightVariances z j*|heightIndicator r (z j.succ)-heightIndicator s (z j.succ)|)=
      2*|r-s| := by
  have H (a b : ℝ) (ha : a ∈ Set.range z) (hb : b ∈ Set.range z) (hab : a ≤ b) :
      (∑ j, heightVariances z j*|heightIndicator a (z j.succ)-heightIndicator b (z j.succ)|)=
        2*|a-b| := by
    simp only [abs_of_nonneg (sub_nonneg.mpr (heightIndicator_antitone _ hab)),mul_sub,
      Finset.sum_sub_distrib,heightIndicator_weighted_sum z hz a ha,heightIndicator_weighted_sum z hz b hb]
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  rcases le_total r s with hrs | hsr
  · exact H r s hr hs hrs
  · simpa only [abs_sub_comm] using H s r hs hr hsr

lemma finiteFieldCDFLeft_coupling_sub {d e : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j) (t : ℝ) :
    finiteFieldCDFLeft w h t-finiteFieldCDFLeft v g t=
      ∑ a, c a*(heightIndicator (h a.1) t-heightIndicator (g a.2) t) := by
  simp only [mul_sub,Finset.sum_sub_distrib]
  rw [coupling_sum_fst c w (fun i => heightIndicator (h i) t) hr,
    coupling_sum_snd c v (fun j => heightIndicator (g j) t) hc]
  simp only [finiteFieldCDFLeft,heightIndicator,mul_ite,mul_one,mul_zero]

lemma finiteFieldCDFLeft_coupling_abs {d e : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hcn : ∀ a, 0 ≤ c a) (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j) (t : ℝ) :
    |finiteFieldCDFLeft w h t-finiteFieldCDFLeft v g t| ≤
      ∑ a, c a*|heightIndicator (h a.1) t-heightIndicator (g a.2) t| := by
  rw [finiteFieldCDFLeft_coupling_sub w h v g c hr hc t]
  simpa only [abs_mul,abs_of_nonneg (hcn _)] using
    Finset.abs_sum_le_sum_abs (fun a => c a*(heightIndicator (h a.1) t-heightIndicator (g a.2) t)) Finset.univ

lemma finiteFieldCDFLeft_partition_cost {d e K : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hcn : ∀ a, 0 ≤ c a) (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j)
    (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (hm : ∀ i, h i ∈ Set.range z) (gm : ∀ j, g j ∈ Set.range z) :
    (∑ j, heightVariances z j*|finiteFieldCDFLeft w h (z j.succ)-finiteFieldCDFLeft v g (z j.succ)|) ≤
      2*(∑ a, c a*|h a.1-g a.2|) := by
  calc
    _ ≤ ∑ j, heightVariances z j*(∑ a, c a*
        |heightIndicator (h a.1) (z j.succ)-heightIndicator (g a.2) (z j.succ)|) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (finiteFieldCDFLeft_coupling_abs w h v g c hcn hr hc _)
        (heightVariances_nonneg z hz j)
    _ = ∑ a, c a*(∑ j, heightVariances z j*
        |heightIndicator (h a.1) (z j.succ)-heightIndicator (g a.2) (z j.succ)|) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [heightIndicator_distance_sum z hz _ _ (hm _) (gm _),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

lemma exists_common_height_partition {I J : Type*} [Fintype I] [Fintype J]
    (h : I → ℝ) (g : J → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hh : ∀ i, h i ∈ Icc (0:ℝ) H) (hg : ∀ j, g j ∈ Icc (0:ℝ) H) :
    ∃ (K : ℕ) (z : Fin (K+1) → ℝ), Monotone z ∧ z 0=0 ∧ z (Fin.last K)=H ∧
      (∀ i, h i ∈ Set.range z) ∧ (∀ j, g j ∈ Set.range z) := by
  classical
  let S : Finset ℝ := insert 0 (insert H (Finset.univ.image h ∪ Finset.univ.image g))
  have hs0 : (0:ℝ) ∈ S := by simp [S]
  have hsH : H ∈ S := by simp [S]
  have hsb : ∀ x ∈ S, x ∈ Icc (0:ℝ) H := by
    intro x hx
    simp only [S,Finset.mem_insert,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hx
    rcases hx with rfl | rfl | ⟨i,rfl⟩ | ⟨j,rfl⟩
    · exact ⟨le_rfl,hH⟩
    · exact ⟨hH,le_rfl⟩
    · exact hh i
    · exact hg j
  obtain ⟨K,hK⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr ⟨0,hs0⟩)
  let e := S.orderIsoOfFin hK
  let z : Fin (K+1) → ℝ := fun i => e i
  have hz : Monotone z := fun i j hij => e.monotone hij
  have hm (x : ℝ) (hx : x ∈ S) : x ∈ Set.range z := by
    exact ⟨e.symm ⟨x,hx⟩,congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩
  have hz0 : z 0=0 := by
    obtain ⟨i,hi⟩ := hm 0 hs0
    apply le_antisymm
    · rw [← hi]; exact hz (Fin.zero_le i)
    · exact (hsb (z 0) (e 0).2).1
  have hzH : z (Fin.last K)=H := by
    obtain ⟨i,hi⟩ := hm H hsH
    apply le_antisymm
    · exact (hsb (z (Fin.last K)) (e (Fin.last K)).2).2
    · rw [← hi]; exact hz (Fin.le_last i)
  exact ⟨K,z,hz,hz0,hzH,(fun i => hm (h i) (by simp [S])),(fun j => hm (g j) (by simp [S]))⟩

end SphericalPerceptron
end
end

end OAI
