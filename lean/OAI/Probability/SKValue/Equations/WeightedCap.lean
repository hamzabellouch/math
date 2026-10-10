import Mathlib

namespace OAI

section

open Set
namespace SKValue

noncomputable def weightedCap (a b : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  sSup ((fun p : ℝ×ℝ ↦ Real.sqrt (b-p.1)*|F p.1 p.2|) '' (Icc a b ×ˢ univ))

lemma weightedCap_bddAbove {a b C : ℝ} {F : ℝ → ℝ → ℝ} (_ : a≤b)
    (_ : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) :
    BddAbove ((fun p : ℝ×ℝ ↦ Real.sqrt (b-p.1)*|F p.1 p.2|) '' (Icc a b ×ˢ univ)) := by
  refine ⟨Real.sqrt (b-a)*C,?_⟩
  rintro _ ⟨⟨t,x⟩,ht,rfl⟩
  exact mul_le_mul (Real.sqrt_le_sqrt (sub_le_sub_left ht.1.1 b)) (hF t ht.1 x)
    (abs_nonneg _) (Real.sqrt_nonneg _)

lemma le_weightedCap {a b C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) {t : ℝ} (ht : t∈Icc a b) (x : ℝ) :
    Real.sqrt (b-t)*|F t x|≤weightedCap a b F :=
  le_csSup (weightedCap_bddAbove hab hC hF) ⟨(t,x),⟨ht,mem_univ _⟩,rfl⟩

lemma weightedCap_nonneg {a b C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) : 0≤weightedCap a b F := by
  simpa only [sub_self,Real.sqrt_zero,zero_mul] using le_weightedCap hab hC hF ⟨hab,le_rfl⟩ 0

lemma abs_le_weightedCap_div {a b C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) {t : ℝ} (ht : t∈Ico a b) (x : ℝ) :
    |F t x|≤weightedCap a b F/Real.sqrt (b-t) := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (sub_pos.mpr ht.2))).mpr
  simpa only [mul_comm] using le_weightedCap hab hC hF ⟨ht.1,ht.2.le⟩ x

lemma weightedCap_le {a b A : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hF : ∀ t∈Icc a b, ∀ x, Real.sqrt (b-t)*|F t x|≤A) : weightedCap a b F≤A := by
  unfold weightedCap
  refine csSup_le ?_ ?_
  · exact ⟨Real.sqrt (b-a)*|F a 0|, ⟨(a,0),⟨⟨le_rfl,hab⟩,mem_univ _⟩,rfl⟩⟩
  · rintro _ ⟨⟨t,x⟩,ht,rfl⟩
    exact hF t ht.1 x

lemma weightedCap_absorb {a b A q C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) (hq : q≤1/2)
    (h : ∀ t∈Icc a b, ∀ x, Real.sqrt (b-t)*|F t x|≤A+q*weightedCap a b F) :
    weightedCap a b F≤2*A := by
  have hb := weightedCap_nonneg hab hC hF
  have hc := weightedCap_le hab h
  nlinarith

end SKValue

end

end OAI
