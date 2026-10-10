import Mathlib
import OAI.Probability.GaussianInformation.Inverse.GreedyOrder

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def dyadicRadius (l : ℤ) : ℝ := (2:ℝ)^(-l)
lemma dyadicRadius_pos (l : ℤ) : 0 < dyadicRadius l := zpow_pos (by norm_num) _
lemma dyadicRadius_antitone : Antitone dyadicRadius := by
  intro l m hlm
  exact zpow_le_zpow_right₀ (by norm_num) (neg_le_neg hlm)
lemma exists_dyadic_bin {x : ℝ} (hx : 0<x) : ∃ l : ℤ,dyadicRadius (l+1)<x ∧ x≤dyadicRadius l := by
  obtain ⟨m,hm,hM⟩ := exists_mem_Ioc_zpow hx (by norm_num : (1:ℝ)<2)
  refine ⟨-m-1,?_,?_⟩
  · simpa [dyadicRadius] using hm
  · simpa [dyadicRadius,add_comm] using hM

noncomputable def clippedLength {d k : ℕ} (ε : ℝ) (f : Fin k → Ambient d) (i : Fin k) :=
  max ‖gramSchmidt ℝ f i‖ ε

def InBins {d k : ℕ} (ε : ℝ) (f : Fin k → Ambient d) (l : Fin k → ℤ) : Prop :=
  ∀ i,dyadicRadius (l i+1)<clippedLength ε f i ∧ clippedLength ε f i≤dyadicRadius (l i)

lemma exists_bins {d k : ℕ} {ε : ℝ} (hε : 0<ε) (f : Fin k → Ambient d) :
    ∃ l : Fin k → ℤ,InBins ε f l := by
  have hi : ∀ i,∃ l : ℤ,dyadicRadius (l+1)<clippedLength ε f i ∧ clippedLength ε f i≤dyadicRadius l :=
    fun i => exists_dyadic_bin (hε.trans_le (le_max_right _ _))
  exact Classical.skolem.mp hi

lemma bins_monotone {d k : ℕ} {ε : ℝ} {f : Fin k → Ambient d} {l : Fin k → ℤ}
    (hg : Greedy residualScore f) (hl : InBins ε f l) : Monotone l := by
  intro i j hij
  by_contra hn
  have he : l j+1≤l i := by omega
  have hc : clippedLength ε f j≤clippedLength ε f i :=
    max_le_max (greedy_lengths_antitone hg hij) le_rfl
  exact (not_lt_of_ge ((hl i).2.trans (dyadicRadius_antitone he))) ((hl j).1.trans_le hc)

noncomputable def binGap {k : ℕ} (l : Fin k → ℤ) (i j : Fin k) : ℕ :=
  if j < i then (l i-l j).toNat else 0

lemma dyadicRadius_sq_gap {a b : ℤ} (hab : b≤a) :
    (dyadicRadius b)^2=(dyadicRadius a)^2*(4:ℝ)^((a-b).toNat) := by
  have hz : (((a-b).toNat:ℕ):ℤ)=a-b := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  have h4 : (4:ℝ)^((a-b).toNat)=(2:ℝ)^(2*(a-b):ℤ) := by
    rw [show (4:ℝ)=2^2 by norm_num,← pow_mul,← zpow_natCast, Nat.cast_mul,hz]
    norm_num
  rw [h4,dyadicRadius,dyadicRadius,← zpow_natCast,← zpow_natCast,← _root_.zpow_mul,← _root_.zpow_mul,
    ← zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  congr 1
  ring

lemma greedy_mem_groupedTube {d k : ℕ} {ε : ℝ} {f : Fin k → Ambient d} {l : Fin k → ℤ}
    (hg : Greedy residualScore f) (hl : InBins ε f l) (i : Fin k) :
    f i∈groupedTube (prefixAxes f i) (binGap l i) (dyadicRadius (l i)) := by
  classical
  have hmono := bins_monotone hg hl
  have he := gramSchmidtNormed_suborthonormal f
  constructor
  · rw [prefixResidual_eq,prefixResidual_self]
    exact (le_max_left _ _).trans (hl i).2
  · intro h
    let s := Finset.univ.filter (fun j => j < i ∧ binGap l i j=h)
    have hsum : ∑ j ∈ Finset.univ.filter (fun j => binGap l i j=h),
        (inner ℝ (prefixAxes f i j) (f i))^2 =
        ∑ j ∈ s,(inner ℝ (gramSchmidtNormed ℝ f j) (f i))^2 := by
      simp only [s,Finset.sum_filter,prefixAxes]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j < i <;> by_cases hh : binGap l i j=h <;> simp [hj,hh]
    rw [hsum]
    by_cases hs : s.Nonempty
    · obtain ⟨b,hbs,hmin⟩ := Finset.exists_min_image s id hs
      have hb := (Finset.mem_filter.mp hbs).2
      have hbj : ∀ j∈s,b≤j := fun j hj => hmin j hj
      have hinner : ∀ j∈s,inner ℝ (gramSchmidtNormed ℝ f j) (prefixResidual f b (f i))=
          inner ℝ (gramSchmidtNormed ℝ f j) (f i) := by
        intro j hj
        rw [prefixResidual,orthoResidual_inner he]
        simp only [Finset.mem_Iio,not_lt_of_ge (hbj j hj),ite_false]
      have hc : ∑ j ∈ s,(inner ℝ (gramSchmidtNormed ℝ f j) (f i))^2 ≤
          ‖prefixResidual f b (f i)‖^2 := by
        convert suborthonormal_bessel he s (prefixResidual f b (f i)) using 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [hinner j hj]
      have hnorm : ‖prefixResidual f b (f i)‖≤dyadicRadius (l b) := by
        calc
          _ ≤ ‖prefixResidual f b (f b)‖ := hg b i hb.1.le
          _ = ‖gramSchmidt ℝ f b‖ := by rw [prefixResidual_self]
          _ ≤ clippedLength ε f b := le_max_left _ _
          _ ≤ _ := (hl b).2
      have hgap : (l i-l b).toNat=h := by simpa only [binGap,ite_eq_left hb.1] using hb.2
      calc
        _ ≤ ‖prefixResidual f b (f i)‖^2 := hc
        _ ≤ (dyadicRadius (l b))^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm _
        _ = _ := by rw [dyadicRadius_sq_gap (hmono hb.1.le),hgap]
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.sum_empty]
      positivity

lemma measurable_snoc_const {α : Type*} [MeasurableSpace α] {k : ℕ} (a : α) :
    Measurable (fun z : Fin k → α => Fin.snoc (α := fun _ : Fin (k+1) => α) z a) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa using (measurable_pi_apply j : Measurable (fun z : Fin k → α => z j))

lemma snoc_update_last {α : Type*} {k : ℕ} (z : Fin k → α) (a x : α) :
    Function.update (Fin.snoc (α := fun _ : Fin (k+1) => α) z a) (Fin.last k) x=Fin.snoc z x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

end AllScaleInverseVolume

end OAI
