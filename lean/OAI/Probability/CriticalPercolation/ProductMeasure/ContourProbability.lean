import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.ContourWords

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

lemma measureReal_countable_union_bound {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : I → Set Ω) (b : I → ℝ)
    (hb : ∀ i, 0≤b i) (hs : Summable b) (hA : ∀ i, μ.real (A i)≤b i) :
    μ.real (⋃ i, A i)≤∑' i, b i := by
  have hh (i : I) : μ (A i)≤ENNReal.ofReal (b i) := by
    calc μ (A i)=ENNReal.ofReal (μ.real (A i)) := by simp [Measure.real]
         _ ≤ ENNReal.ofReal (b i) := ENNReal.ofReal_le_ofReal (hA i)
  have h := (measure_iUnion_le A).trans (ENNReal.tsum_le_tsum hh)
  rw [← ENNReal.ofReal_tsum_of_nonneg hb hs] at h
  have ht := ENNReal.toReal_mono (by finiteness) h
  simpa only [Measure.real,ENNReal.toReal_ofReal (tsum_nonneg hb)] using ht

namespace Boundary

def wordFailure {Ω : Type*} (B : Set Ω) (F : Grid → Set Ω)
    {n : ℕ} (w : Fin n → Dir) : Set Ω :=
  if wordValid (0,1) w then B∩⋂ z∈outsideSites (wordEdge (0,1) w) n, F z else ∅

lemma wordFailure_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Set Ω) (F : Grid → Set Ω)
    (q : ℝ) (hq₀ : 0≤q) (hq₁ : q≤1)
    (hfail : ∀ s : Finset Grid, μ.real (B∩⋂ z∈s, F z)≤μ.real B*(q^4)^s.card)
    (n : ℕ) (w : Fin n → Dir) : μ.real (wordFailure B F w)≤μ.real B*q^n := by
  by_cases hw : wordValid (0,1) w
  · rw [wordFailure,ite_eq_left hw]
    apply (hfail _).trans
    apply mul_le_mul_of_nonneg_left _ (measureReal_nonneg)
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hq₀ hq₁
      (length_le_four_outside _ _ (wordEdge_chain (0,1) w) hw.1 hw.2)
  · rw [wordFailure,ite_eq_right hw]
    simp only [measureReal_empty]
    positivity

theorem finite_good_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Set Ω)
    (S : Ω → Set Grid) (F : Grid → Set Ω)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, 0≤v.1 ∧ 0≤v.2)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F z)
    (q : ℝ) (hq₀ : 0≤q) (hq : 4*q<1)
    (hfail : ∀ s : Finset Grid, μ.real (B∩⋂ z∈s, F z)≤μ.real B*(q^4)^s.card) :
    μ.real (B∩{ω | (S ω).Finite})≤μ.real B*(4*q)/(1-4*q) := by
  have hsub : B∩{ω | (S ω).Finite}⊆
      ⋃ n : ℕ, ⋃ w : Fin (n+1) → Dir, wordFailure B F w := by
    intro ω hω
    obtain ⟨n,w,hw,hz⟩ := finite_good_contour (S ω) hω.2 (hroot ω hω.1) (hquad ω hω.1)
    refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨w,?_⟩⟩
    rw [wordFailure,ite_eq_left hw]
    refine ⟨hω.1,Set.mem_iInter.mpr fun z => Set.mem_iInter.mpr fun hs => ?_⟩
    exact hchild ω hω.1 z (hz z hs).1 (hz z hs).2
  have hq₁ : q≤1 := by linarith
  have hterm (n : ℕ) :
      μ.real (⋃ w : Fin (n+1) → Dir, wordFailure B F w)≤μ.real B*(4*q)^(n+1) := by
    apply (measureReal_iUnion_fintype_le _).trans
    calc
      (∑ w : Fin (n+1) → Dir, μ.real (wordFailure B F w))≤
          ∑ _w : Fin (n+1) → Dir, μ.real B*q^(n+1) :=
        Finset.sum_le_sum (fun w _ => wordFailure_bound μ B F q hq₀ hq₁ hfail (n+1) w)
      _ = μ.real B*(4*q)^(n+1) := by
        simp only [Finset.sum_const,Finset.card_univ,card_words,nsmul_eq_mul,
          Nat.cast_pow,Nat.cast_ofNat,mul_pow]
        ring
  have hs₀ : Summable (fun n : ℕ => (4*q)^n) :=
    summable_geometric_of_lt_one (by positivity) hq
  have hs : Summable (fun n : ℕ => μ.real B*(4*q)^(n+1)) :=
    ((summable_nat_add_iff 1).mpr hs₀).mul_left _
  have hu := measureReal_countable_union_bound μ
    (fun n => ⋃ w : Fin (n+1) → Dir, wordFailure B F w)
    (fun n => μ.real B*(4*q)^(n+1)) (fun _ => by positivity) hs hterm
  apply ((measureReal_mono hsub).trans hu).trans_eq
  simp_rw [pow_succ]
  rw [tsum_mul_left,tsum_mul_right,tsum_geometric_of_lt_one (by positivity) hq]
  ring

theorem infinite_good_positive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Set Ω)
    (S : Ω → Set Grid) (F : Grid → Set Ω)
    (hB : 0<μ.real B)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, 0≤v.1 ∧ 0≤v.2)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F z)
    (q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1)
    (hfail : ∀ s : Finset Grid, μ.real (B∩⋂ z∈s, F z)≤μ.real B*(q^4)^s.card) :
    0<μ.real (B∩{ω | (S ω).Infinite}) := by
  have hh : 4*q<1 := by linarith
  have hf := finite_good_probability_bound μ B S F hroot hquad hchild q hq₀ hh hfail
  have hratio : μ.real B*(4*q)/(1-4*q)<μ.real B := by
    apply (div_lt_iff₀ (by linarith : 0<1-4*q)).mpr
    nlinarith [mul_pos hB (by linarith : 0<1-8*q)]
  have he : B=(B∩{ω | (S ω).Finite})∪(B∩{ω | (S ω).Infinite}) := by
    ext ω
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.Infinite]
    tauto
  have hu := measureReal_union_le (μ := μ)
    (B∩{ω | (S ω).Finite}) (B∩{ω | (S ω).Infinite})
  rw [← he] at hu
  linarith

end Boundary
end CriticalPercolation
end
end
end

end OAI
