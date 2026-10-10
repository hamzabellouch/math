import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaStability

namespace OAI

                                  
section

/-! Exact old-state affine forms for the all-step filtering leg in §04.  In
particular the marked coefficient bound is uniform as its side mass vanishes. -/
namespace UniformKServer.AlphaLinear
noncomputable section
open Set MeasureTheory Finset
open UniformKServer.LogPrimitive UniformKServer.Denominators UniformKServer.AlphaStability

theorem primitive_linear {D : ℝ → ℝ} {base a : ℝ}
    (hb : base ∈ Icc (0:ℝ) 1) (ha : a ∈ Icc (0:ℝ) 1)
    (hS : IntervalIntegrable (fun x => (1-0/x)/D x) volume 0 1)
    (hQ : IntervalIntegrable (fun x => (0-1/x)/D x) volume 0 1)
    (scale S Q : ℝ) :
    primitive D base scale S Q a =
      S*primitive D base scale 1 0 a+Q*primitive D base scale 0 1 a := by
  have hs : uIcc base a ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.uIcc_subset_Icc hb ha
  have hid : (fun x => (S-Q/x)/D x) =
      fun x => S*((1-0/x)/D x)+Q*((0-1/x)/D x) := by funext x; ring
  rw [primitive,hid,intervalIntegral.integral_add ((hS.mono_set hs).const_mul S)
    ((hQ.mono_set hs).const_mul Q),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  simp only [primitive]
  ring

variable {ι : Type*} [Fintype ι]

def potential (D : ι → ℝ → ℝ) (base η : ι → ℝ) (scale : ℝ)
    (B a : ι → ℝ) : ℝ :=
  ∑ i, primitive (D i) (base i) scale (∑ j, B j) ((1+η i)*B i) (a i)

def coefficient (D : ι → ℝ → ℝ) (base η : ι → ℝ) (scale : ℝ)
    (a : ι → ℝ) (j : ι) : ℝ :=
  (∑ i, primitive (D i) (base i) scale 1 0 (a i))+
    (1+η j)*primitive (D j) (base j) scale 0 1 (a j)

theorem potential_affine (D : ι → ℝ → ℝ) (base η : ι → ℝ) (scale : ℝ)
    (B a : ι → ℝ) (hb : ∀ i, base i ∈ Icc (0:ℝ) 1)
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1)
    (hS : ∀ i, IntervalIntegrable (fun x => (1-0/x)/D i x) volume 0 1)
    (hQ : ∀ i, IntervalIntegrable (fun x => (0-1/x)/D i x) volume 0 1) :
    potential D base η scale B a = ∑ j, coefficient D base η scale a j*B j := by
  let X (i : ι) := primitive (D i) (base i) scale 1 0 (a i)
  let Y (i : ι) := primitive (D i) (base i) scale 0 1 (a i)
  calc
    _ = ∑ i, ((∑ j, B j)*X i+((1+η i)*B i)*Y i) := by
      apply sum_congr rfl
      intro i _
      exact primitive_linear (hb i) (ha i) (hS i) (hQ i) ..
    _ = (∑ j, B j)*(∑ i, X i)+∑ i, ((1+η i)*B i)*Y i := by
      rw [sum_add_distrib,←mul_sum]
    _ = (∑ i, X i)*(∑ j, B j)+∑ i, ((1+η i)*Y i)*B i := by
      congr 1
      · ring
      · apply sum_congr rfl
        intro i _
        ring
    _ = ∑ i, ((∑ j, X j)+(1+η i)*Y i)*B i := by
      rw [mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := rfl

/-- An affine functional's coefficients inherit its exact L1 input bound. -/
theorem coefficient_of_lipschitz [DecidableEq ι] (f : (ι → ℝ) → ℝ) (c : ι → ℝ)
    (L : ℝ) (hf : ∀ B, f B=∑ i, c i*B i)
    (hLip : ∀ B B', |f B-f B'| ≤ L*(∑ i, |B i-B' i|)) (j : ι) : |c j| ≤ L := by
  have h := hLip (fun i => if i=j then 1 else 0) (fun _ => 0)
  simp only [hf,mul_zero,sum_const_zero,sub_zero] at h
  simpa [abs_ite] using h

/-- All regular old-state coefficients, independent of the active dimension. -/
theorem regular_coefficient [DecidableEq ι] (h η a : ι → ℝ) (scale E : ℝ)
    (hh : ∀ i, 1 ≤ h i) (ha : ∀ i, a i ∈ Icc (0:ℝ) 1)
    (hasum : ∑ i, a i=1) (hη : ∀ i, 0 ≤ η i) (hηE : ∀ i, η i ≤ E) (j : ι) :
    |coefficient (fun i => regular (h i)) (fun _ => 0) η scale a j| ≤ |scale| *(2+E) := by
  apply coefficient_of_lipschitz (fun B => potential (fun i => regular (h i)) (fun _ => 0) η scale B a)
    _ (|scale| *(2+E))
  · intro B
    exact potential_affine _ _ _ _ B a (by intro i; simp) ha
      (fun i => regular_integrable (hh i) 1 0) (fun i => regular_integrable (hh i) 0 1)
  · intro B B'
    exact regular_input h η a B B' scale E hh ha hasum hη hηE

/-- Marked coefficients are bounded before filtering or selecting a change
 event; no lower bound on the new or old side parameter is introduced. -/
theorem marked_coefficient [DecidableEq ι] (o : ι) (u : ℝ)
    (h η a : ι → ℝ) (scale E : ℝ) (hu : 0 < u) (hu₁ : u ≤ 1)
    (hh : ∀ i, i ≠ o → 1 ≤ h i) (ha : ∀ i, a i ∈ Icc (0:ℝ) 1)
    (hasum : ∑ i, a i=1) (hη : ∀ i, 0 ≤ η i) (hηE : ∀ i, η i ≤ E) (j : ι) :
    |coefficient (fun i => if i=o then marked u else regular (h i))
      (fun i => if i=o then 1 else 0) η scale a j| ≤ |scale| * (11+4*E) := by
  let D (i : ι) := if i=o then marked u else regular (h i)
  let base (i : ι) : ℝ := if i=o then 1 else 0
  change |coefficient D base η scale a j| ≤ _
  apply coefficient_of_lipschitz (fun B => potential D base η scale B a) _ (|scale| * (11+4*E))
  · intro B
    apply potential_affine D base η scale B a
    · intro i
      simp only [base]
      split_ifs <;> simp
    · exact ha
    · intro i
      dsimp [D]
      split_ifs with hi
      · exact marked_integrable hu hu₁ 1 0
      · exact regular_integrable (hh i hi) 1 0
    · intro i
      dsimp [D]
      split_ifs with hi
      · exact marked_integrable hu hu₁ 0 1
      · exact regular_integrable (hh i hi) 0 1
  · intro B B'
    have he (B : ι → ℝ) : potential D base η scale B a =
        ∑ i, mixedPrimitive o u h η B scale a i := by
      apply sum_congr rfl
      intro i _
      simp only [D,base,mixedPrimitive]
      split_ifs <;> rfl
    rw [he,he]
    exact marked_input o h η a B B' scale E u hu hu₁ hh ha hasum hη hηE

end
end UniformKServer.AlphaLinear

end

end OAI
