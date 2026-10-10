import Mathlib

namespace OAI

section


/-! A literal square with prescribed boundary paths, constructed from a relative
path homotopy by an explicit compact quotient. -/
noncomputable section
open scoped Topology unitInterval
open Topology
namespace HyperbolicObstruction.SquarePathFilling

def low (s : I) : ℝ := max (2 * (s : ℝ) - 1) 0
def high (s : I) : ℝ := min (2 * (s : ℝ)) 1
lemma bounds (s : I) : 0 ≤ low s ∧ low s ≤ high s ∧ high s ≤ 1 := by
  have h0 := s.property.1
  have h1 := s.property.2
  unfold low high
  constructor
  · exact le_max_right _ _
  constructor
  · apply max_le <;> apply le_min <;> linarith
  · exact min_le_right _ _
lemma sum (s : I) : high s + low s = 2 * (s : ℝ) := by
  unfold high low
  by_cases h : (s : ℝ) ≤ 1/2
  · rw [min_eq_left (by linarith),max_eq_right (by linarith)]; ring
  · rw [min_eq_right (by linarith),max_eq_left (by linarith)]; ring
lemma gap_pos {s : I} (h0 : (0 : ℝ) < s) (h1 : (s : ℝ) < 1) : low s < high s := by
  unfold high low
  apply max_lt <;> apply lt_min <;> linarith
lemma low_continuous : Continuous low := by unfold low; fun_prop
lemma high_continuous : Continuous high := by unfold high; fun_prop

/-- Horizontal parameter selects a broken boundary path; vertical parameter
runs from its common source to its common target. -/
def quotient : C(I × I,I × I) where
  toFun ts :=
    (⟨(1 - (ts.1 : ℝ)) * high ts.2 + (ts.1 : ℝ) * low ts.2, by
      have ht0 := ts.1.property.1
      have ht1 := ts.1.property.2
      have hb := bounds ts.2
      constructor <;> nlinarith⟩,
     ⟨(1 - (ts.1 : ℝ)) * low ts.2 + (ts.1 : ℝ) * high ts.2, by
      have ht0 := ts.1.property.1
      have ht1 := ts.1.property.2
      have hb := bounds ts.2
      constructor <;> nlinarith⟩)
  continuous_toFun := by
    apply Continuous.prodMk <;> apply Continuous.subtype_mk
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (high_continuous.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul (low_continuous.comp continuous_snd))
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (low_continuous.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul (high_continuous.comp continuous_snd))

lemma quotient_sum (t s : I) :
    ((quotient (t,s)).1 : ℝ) + ((quotient (t,s)).2 : ℝ) = 2 * (s : ℝ) := by
  change (1-(t:ℝ))*high s+(t:ℝ)*low s+((1-(t:ℝ))*low s+(t:ℝ)*high s) = _
  nlinarith [sum s]

lemma quotient_fiber {t s t' s' : I} (h : quotient (t,s) = quotient (t',s')) :
    s = s' ∧ (t = t' ∨ s = 0 ∨ s = 1) := by
  have hsum : 2 * (s : ℝ) = 2 * (s' : ℝ) := by
    rw [←quotient_sum t s,←quotient_sum t' s',h]
  have hs : s = s' := Subtype.ext (by linarith)
  refine ⟨hs,?_⟩
  subst s'
  by_cases h0 : s = 0
  · exact Or.inr (Or.inl h0)
  by_cases h1 : s = 1
  · exact Or.inr (Or.inr h1)
  left
  have h0' : (0 : ℝ) < s := lt_of_le_of_ne s.property.1 (by
    intro he; exact h0 (Subtype.ext he.symm))
  have h1' : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 (by
    intro he; exact h1 (Subtype.ext he))
  have ht := congrArg (fun z : I × I => (z.2 : ℝ)) h
  change (1-(t:ℝ))*low s+(t:ℝ)*high s =
    (1-(t':ℝ))*low s+(t':ℝ)*high s at ht
  have hg := gap_pos h0' h1'
  apply Subtype.ext
  nlinarith

lemma quotient_surjective : Function.Surjective quotient := by
  rintro ⟨x,y⟩
  let s : I := ⟨((x : ℝ)+(y : ℝ))/2,by constructor <;>
    linarith [x.property.1,x.property.2,y.property.1,y.property.2]⟩
  have slo : low s ≤ (y : ℝ) := by
    dsimp [low,s]
    apply max_le <;> linarith [x.property.2,y.property.1]
  have shi : (y : ℝ) ≤ high s := by
    dsimp [high,s]
    apply le_min <;> linarith [x.property.1,y.property.2]
  by_cases hz : high s = low s
  · refine ⟨(0,s),?_⟩
    have hy : (y : ℝ) = low s := by linarith
    have hx : (x : ℝ) = low s := by
      have hh := sum s
      dsimp [s] at hh
      linarith
    apply Prod.ext <;> apply Subtype.ext <;> dsimp [quotient]
    · norm_num; linarith
    · norm_num; exact hy.symm
  · have hp : 0 < high s - low s := by
      have := (bounds s).2.1
      exact sub_pos.mpr (lt_of_le_of_ne this (Ne.symm hz))
    let t : I := ⟨((y : ℝ) - low s)/(high s - low s),by
      constructor
      · exact div_nonneg (sub_nonneg.mpr slo) hp.le
      · exact (div_le_one hp).mpr (by linarith)⟩
    have he : (t : ℝ) * (high s - low s) = (y : ℝ) - low s := by
      dsimp [t]
      exact div_mul_cancel₀ _ hp.ne'
    refine ⟨(t,s),?_⟩
    apply Prod.ext <;> apply Subtype.ext <;> dsimp [quotient]
    · have hh := sum s
      dsimp [s] at hh
      nlinarith
    · nlinarith

lemma quotient_isQuotientMap : IsQuotientMap quotient :=
  quotient.continuous.isClosedMap.isQuotientMap quotient.continuous quotient_surjective

variable {X : Type*} [TopologicalSpace X] {a b c d : X}
  {p : Path a b} {q : Path a c} {r : Path b d} {s : Path c d}

lemma homotopy_fiber (H : (p.trans r).Homotopy (q.trans s))
    {z z' : I × I} (h : quotient z = quotient z') : H z = H z' := by
  rcases z with ⟨t,v⟩
  rcases z' with ⟨t',v'⟩
  obtain ⟨rfl,hh⟩ := quotient_fiber h
  rcases hh with rfl|rfl|rfl <;> simp

/-- The actual square filling, with no extension assumption. -/
def fill (H : (p.trans r).Homotopy (q.trans s)) : C(I × I,X) where
  toFun z := H (quotient_surjective z).choose
  continuous_toFun := by
    apply quotient_isQuotientMap.continuous_iff.mpr
    have he : (fun z => H (quotient_surjective z).choose) ∘ quotient = H := by
      funext z
      exact homotopy_fiber H (quotient_surjective (quotient z)).choose_spec
    rw [he]
    exact H.continuous

lemma fill_quotient (H : (p.trans r).Homotopy (q.trans s)) (z : I × I) :
    fill H (quotient z) = H z :=
  homotopy_fiber H (quotient_surjective (quotient z)).choose_spec

def half (x : I) : I := ⟨(x:ℝ)/2,by constructor <;>
  linarith [x.property.1,x.property.2]⟩
def upper (x : I) : I := ⟨((x:ℝ)+1)/2,by constructor <;>
  linarith [x.property.1,x.property.2]⟩
lemma low_half (x : I) : low (half x) = 0 := by
  dsimp [low,half]; rw [max_eq_right (by linarith [x.property.2])]
lemma high_half (x : I) : high (half x) = (x:ℝ) := by
  dsimp [high,half]; rw [min_eq_left (by linarith [x.property.2])]; ring
lemma low_upper (x : I) : low (upper x) = (x:ℝ) := by
  dsimp [low,upper]; rw [max_eq_left (by linarith [x.property.1])]; ring
lemma high_upper (x : I) : high (upper x) = 1 := by
  dsimp [high,upper]; rw [min_eq_right (by linarith [x.property.1])]

lemma quotient_bottom (x : I) : quotient (0,half x) = (x,0) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [quotient,low_half,high_half]
lemma quotient_left (x : I) : quotient (1,half x) = (0,x) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [quotient,low_half,high_half]
lemma quotient_right (x : I) : quotient (0,upper x) = (1,x) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [quotient,low_upper,high_upper]
lemma quotient_top (x : I) : quotient (1,upper x) = (x,1) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [quotient,low_upper,high_upper]

lemma trans_half (p : Path a b) (r : Path b d) (x : I) :
    p.trans r (half x) = p x := by
  rw [←Path.extend_apply,Path.extend_trans_of_le_half p r (by
    change (x:ℝ)/2 ≤ 1/2; linarith [x.property.2])]
  have he : 2 * (half x : ℝ) = (x:ℝ) := by dsimp [half]; ring
  rw [he,Path.extend_apply]
lemma trans_upper (p : Path a b) (r : Path b d) (x : I) :
    p.trans r (upper x) = r x := by
  rw [←Path.extend_apply,Path.extend_trans_of_half_le p r (by
    change 1/2 ≤ ((x:ℝ)+1)/2; linarith [x.property.1])]
  have he : 2 * (upper x : ℝ) - 1 = (x:ℝ) := by dsimp [upper]; ring
  rw [he,Path.extend_apply]

@[simp] lemma fill_bottom (H : (p.trans r).Homotopy (q.trans s)) (x : I) :
    fill H (x,0) = p x := by
  rw [←quotient_bottom x,fill_quotient]
  simpa using trans_half p r x
@[simp] lemma fill_left (H : (p.trans r).Homotopy (q.trans s)) (x : I) :
    fill H (0,x) = q x := by
  rw [←quotient_left x,fill_quotient]
  simpa using trans_half q s x
@[simp] lemma fill_right (H : (p.trans r).Homotopy (q.trans s)) (x : I) :
    fill H (1,x) = r x := by
  rw [←quotient_right x,fill_quotient]
  simpa using trans_upper p r x
@[simp] lemma fill_top (H : (p.trans r).Homotopy (q.trans s)) (x : I) :
    fill H (x,1) = s x := by
  rw [←quotient_top x,fill_quotient]
  simpa using trans_upper q s x

end HyperbolicObstruction.SquarePathFilling
end
end

section

end

end OAI
