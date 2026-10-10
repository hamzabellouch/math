import Mathlib

namespace OAI

                                        
section

/-! Exact two child-output rules of companion §05.  The estimates retain one
copy of the parent variation; this coefficient must be independent of k for
the tree absorption.  Input inequalities below are the explicit rank, cap,
and proportion conditions, not an assumed output feasibility statement. -/
namespace UniformKServer.AllocationOutputs
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def lower (n B f β : ι → ℝ) (i : ι) : ℝ := n i-β i*B i+f i

def excess (d : ι → ℝ) (parent : ℝ) : ℝ := max ((∑ i, d i)-parent) 0

def ruleOne (d α : ι → ℝ) (parent : ℝ) (i : ι) : ℝ := d i-excess d parent*α i

def ruleTwo (d w : ι → ℝ) (parent D : ℝ) (o i : ι) : ℝ :=
  if i=o then min (d o) (parent-∑ j ∈ univ.erase o, (d j-D*w j)) else d i-D*w i

def variation (a b : ι → ℝ) : ℝ := ∑ i, |b i-a i|

omit [DecidableEq ι] in
theorem excess_nonneg (d : ι → ℝ) (q : ℝ) : 0 ≤ excess d q := le_max_right _ _

omit [DecidableEq ι] in
theorem required_holes (n B f b : ι → ℝ) (β q e : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hβ : 0 ≤ β) (he : 0 ≤ e)
    (hparent : (∑ i, (n i-β*B i+f i)) ≤ q)
    (hcap : (∑ i, (b i-f i)) ≤ e) :
    excess (fun i => n i+b i) q ≤ β*(∑ i, B i)+e := by
  unfold excess
  apply max_le
  · have hid : (∑ i, (n i+b i))-(∑ i, (n i-β*B i+f i)) =
        β*(∑ i, B i)+(∑ i, (b i-f i)) := by
      rw [←sum_sub_distrib,mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    linarith
  · exact add_nonneg (mul_nonneg hβ (sum_nonneg (fun i _ => hB i))) he

omit [DecidableEq ι] in
theorem rule_one_budget (d α : ι → ℝ) (q : ℝ) (hα : (∑ i, α i)=1) :
    (∑ i, ruleOne d α q i) = min (∑ i, d i) q := by
  simp only [ruleOne,sum_sub_distrib,←mul_sum,hα,mul_one,excess]
  rcases le_total (∑ i, d i) q with h|h
  · rw [max_eq_right (by linarith),min_eq_left h,sub_zero]
  · rw [max_eq_left (by linarith),min_eq_right h]
    ring

omit [DecidableEq ι] in
theorem rule_one_upper (d α : ι → ℝ) (q : ℝ) (hα : ∀ i, 0 ≤ α i) (i : ι) :
    ruleOne d α q i ≤ d i :=
  sub_le_self _ (mul_nonneg (excess_nonneg _ _) (hα i))

omit [DecidableEq ι] in
/-- Source Rule I, at regular coordinates.  The error comparison e≤εS
includes the admissible zero case S=0, so no division by S is used. -/
theorem rule_one_regular (n B f b β η α : ι → ℝ) (βv q e ε : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hα : ∀ i, 0 ≤ α i)
    (hβ : 0 ≤ βv+ε)
    (hR : excess (fun i => n i+b i) q ≤ βv*(∑ i, B i)+e)
    (he : e ≤ ε*(∑ i, B i))
    (hprop : ∀ i, (∑ j, B j)*α i ≤ (1+η i)*B i)
    (i : ι) (hgap : (βv+ε)*(1+η i) ≤ β i) (hcap : f i ≤ b i) :
    lower n B f β i ≤ ruleOne (fun i => n i+b i) α q i := by
  have hR' : excess (fun i => n i+b i) q ≤ (βv+ε)*(∑ i, B i) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hR' (hα i)
  have h2 := mul_le_mul_of_nonneg_left (hprop i) hβ
  have h3 := mul_le_mul_of_nonneg_right hgap (hB i)
  dsimp [lower,ruleOne]
  nlinarith

omit [DecidableEq ι] in
/-- Source Rule I at the marked dominant coordinate: the cap's excess e is
retained without multiplying it by a inverse core mass. -/
theorem rule_one_dominant (n B f b β η α : ι → ℝ) (βv q e : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hα : ∀ i, 0 ≤ α i) (hαsum : (∑ i, α i)=1)
    (hβ : 0 ≤ βv) (he : 0 ≤ e)
    (hR : excess (fun i => n i+b i) q ≤ βv*(∑ i, B i)+e)
    (hprop : ∀ i, (∑ j, B j)*α i ≤ (1+η i)*B i)
    (o : ι) (hgap : βv*(1+η o) ≤ β o) (hcap : f o+e ≤ b o) :
    lower n B f β o ≤ ruleOne (fun i => n i+b i) α q o := by
  have hαo : α o ≤ 1 := by
    rw [←hαsum]
    exact single_le_sum (fun i _ => hα i) (mem_univ o)
  have h1 := mul_le_mul_of_nonneg_right hR (hα o)
  have h2 := mul_le_mul_of_nonneg_left (hprop o) hβ
  have h3 := mul_le_mul_of_nonneg_right hgap (hB o)
  have h4 := mul_le_mul_of_nonneg_left hαo he
  dsimp [lower,ruleOne]
  nlinarith

theorem rule_two_side (d w : ι → ℝ) (q D : ℝ) (o i : ι) (hi : i ≠ o) :
    ruleTwo d w q D o i = d i-D*w i := ite_eq_right hi

theorem rule_two_budget (d w : ι → ℝ) (q D : ℝ) (o : ι) :
    (∑ i, ruleTwo d w q D o i) ≤ q := by
  rw [←sum_erase_add _ _ (mem_univ o)]
  have hs : (∑ i ∈ univ.erase o, ruleTwo d w q D o i) =
      ∑ i ∈ univ.erase o, (d i-D*w i) := by
    apply sum_congr rfl
    intro i hi
    exact rule_two_side d w q D o i (ne_of_mem_erase hi)
  rw [hs]
  simp only [ruleTwo,ite_true]
  linarith [min_le_right (d o) (q-∑ i ∈ univ.erase o, (d i-D*w i))]

theorem rule_two_upper (d w : ι → ℝ) (q D : ℝ) (o i : ι)
    (hD : 0 ≤ D) (hw : ∀ i, i ≠ o → 0 ≤ w i) :
    ruleTwo d w q D o i ≤ d i := by
  by_cases hi : i=o
  · subst i
    simp only [ruleTwo,ite_true]
    exact min_le_left _ _
  · rw [rule_two_side d w q D o i hi]
    exact sub_le_self _ (mul_nonneg hD (hw i hi))

/-- Exact lower bounds of Rule II, with the side lower tracker inequality
and the aggregate side slack paid from the dominant parameter gap. -/
theorem rule_two_lower (n B fp fc b β : ι → ℝ) (w θ z : ι → ℝ)
    (q D βv βplus : ℝ) (o : ι)
    (hB : ∀ i, 0 ≤ B i) (hparent : (∑ i, (n i-βv*B i+fp i)) ≤ q)
    (hparam : βv ≤ βplus)
    (hcap : ∀ i, fc i ≤ b i)
    (hsideCap : ∀ i, i ≠ o → b i ≤ fp i)
    (hupper : ∀ i, i ≠ o → D*w i ≤ β i*B i)
    (hlower : ∀ i, i ≠ o → βplus*B i-D*θ i*z i ≤ D*w i)
    (hslack : D*(∑ i ∈ univ.erase o, θ i*z i) ≤
      (n o-βv*B o+fp o)-lower n B fc β o)
    (hβo : 0 ≤ β o) :
    ∀ i, lower n B fc β i ≤ ruleTwo (fun i => n i+b i) w q D o i := by
  intro i
  by_cases hi : i=o
  · subst i
    simp only [ruleTwo,ite_true]
    apply le_min
    · dsimp [lower]
      nlinarith [hcap o,mul_nonneg hβo (hB o)]
    · have hs : (∑ i ∈ univ.erase o, (n i+b i-D*w i)) ≤
          (∑ i ∈ univ.erase o, (n i-βv*B i+fp i))+
            D*(∑ i ∈ univ.erase o, θ i*z i) := by
        rw [mul_sum,←sum_add_distrib]
        apply sum_le_sum
        intro i hi
        have hio := ne_of_mem_erase hi
        have hp := mul_le_mul_of_nonneg_right hparam (hB i)
        nlinarith [hsideCap i hio,hlower i hio]
      rw [←sum_erase_add _ _ (mem_univ o)] at hparent
      linarith
  · rw [rule_two_side _ _ _ _ _ _ hi]
    dsimp [lower]
    linarith [hupper i hi,hcap i]

end
end UniformKServer.AllocationOutputs

end

end OAI
