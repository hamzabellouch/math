import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

lemma list_prod_perturb (l : List ℝ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ x∈l,|x-1| ≤ t) :
    |l.prod| ≤ 2^l.length ∧ |l.prod-1| ≤ (2^l.length-1)*t := by
  induction l with
  | nil => simp
  | cons x l ih =>
      have hx := h x (by simp)
      have hl := ih (fun y hy=>h y (by simp [hy]))
      have hx2 : |x| ≤ 2 := by
        have hh := abs_add_le (x-1) 1
        simp only [sub_add_cancel,abs_one] at hh
        linarith
      have he : x*l.prod-1=(x-1)*l.prod+(l.prod-1) := by ring
      simp only [List.prod_cons,List.length_cons,pow_succ]
      constructor
      · rw [abs_mul]
        exact (mul_le_mul hx2 hl.1 (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      · rw [he]
        calc
          _ ≤ |x-1| * |l.prod|+|l.prod-1| := by simpa only [abs_mul] using abs_add_le ((x-1)*l.prod) (l.prod-1)
          _ ≤ t*2^l.length+(2^l.length-1)*t := add_le_add
            (mul_le_mul hx hl.1 (abs_nonneg _) ht) hl.2
          _ = _ := by ring

lemma list_prod_between (l : List ℝ) (h : ∀ x∈l,(1/2:ℝ) ≤ x ∧ x ≤ 2) :
    (1/2:ℝ)^l.length ≤ l.prod ∧ l.prod ≤ (2:ℝ)^l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
      have hx := h x (by simp)
      have hl := ih (fun y hy=>h y (by simp [hy]))
      have hl0 : 0 ≤ l.prod := (by positivity : (0:ℝ) ≤ (1/2:ℝ)^l.length).trans hl.1
      simp only [List.prod_cons,List.length_cons,pow_succ]
      constructor
      · exact (by ring : (1/2:ℝ)^l.length*(1/2)=(1/2)*(1/2)^l.length).le.trans
          (mul_le_mul hx.1 hl.1 (by positivity) (by linarith))
      · exact (mul_le_mul hx.2 hl.2 hl0 (by norm_num)).trans_eq (by ring)

lemma pair_factor_control {u z : ℝ} (hu : |u| ≤ 1/4) (hz : |z| ≤ 1) :
    (1/2:ℝ) ≤ 1+u*z ∧ 1+u*z ≤ 2 ∧ |(1+u*z)-1| ≤ |u| := by
  have hh : |u*z| ≤ |u| := by rw [abs_mul];exact (mul_le_mul_of_nonneg_left hz (abs_nonneg u)).trans_eq (mul_one _)
  have hb := abs_le.mp hh
  constructor
  · linarith
  constructor
  · linarith
  simpa only [add_sub_cancel_left] using hh

lemma pair_square_factor_control {u : ℝ} (hu : |u| ≤ 1/4) :
    (1/2:ℝ) ≤ 1-u^2 ∧ 1-u^2 ≤ 2 ∧ |(1-u^2)-1| ≤ |u| := by
  have hs : u^2 ≤ |u| := by nlinarith [sq_abs u,abs_nonneg u]
  have h0 := sq_nonneg u
  constructor
  · linarith
  constructor
  · linarith
  rw [sub_sub_cancel_left,abs_neg,abs_of_nonneg h0]
  exact hs

def pairRationalWeight (a b u x y : ℝ) : ℝ :=
  (1-u^2)^2*(1+u*x*y)/((1+u*a*b)*(1+u*a*y)^2*(1+u*b*x)^2)

lemma pairRationalWeight_bounds {a b u x y : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    1/256 ≤ pairRationalWeight a b u x y ∧
    pairRationalWeight a b u x y ≤ 256 ∧
    |pairRationalWeight a b u x y-1| ≤ 1216*|u| := by
  have hab : |a*b| ≤ 1 := by simpa only [one_mul,abs_mul] using mul_le_mul ha hb (abs_nonneg b) (by norm_num : (0:ℝ) ≤ 1)
  have hay : |a*y| ≤ 1 := by simpa only [one_mul,abs_mul] using mul_le_mul ha hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)
  have hbx : |b*x| ≤ 1 := by simpa only [one_mul,abs_mul] using mul_le_mul hb hx (abs_nonneg x) (by norm_num : (0:ℝ) ≤ 1)
  have hxy : |x*y| ≤ 1 := by simpa only [one_mul,abs_mul] using mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)
  have h₀ := pair_square_factor_control hu
  have h₁ := pair_factor_control hu hab
  have h₂ := pair_factor_control hu hay
  have h₃ := pair_factor_control hu hbx
  have h₄ := pair_factor_control hu hxy
  let ln : List ℝ := [1-u^2,1-u^2,1+u*(x*y)]
  let ld : List ℝ := [1+u*(a*b),1+u*(a*y),1+u*(a*y),1+u*(b*x),1+u*(b*x)]
  have hn : ∀ z∈ln, (1/2:ℝ) ≤ z ∧ z ≤ 2 := by
    intro z hz
    simp only [ln,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> exact ⟨by grind,by grind⟩
  have hd : ∀ z∈ld, (1/2:ℝ) ≤ z ∧ z ≤ 2 := by
    intro z hz
    simp only [ld,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> exact ⟨by grind,by grind⟩
  have hn' : ∀ z∈ln, |z-1| ≤ |u| := by
    intro z hz
    simp only [ln,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> grind
  have hd' : ∀ z∈ld, |z-1| ≤ |u| := by
    intro z hz
    simp only [ld,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> grind
  have hnb := list_prod_between ln hn
  have hdb := list_prod_between ld hd
  have hnp := (list_prod_perturb ln (abs_nonneg u) (by linarith) hn').2
  have hdp := (list_prod_perturb ld (abs_nonneg u) (by linarith) hd').2
  have hnl : ln.length=3 := rfl
  have hdl : ld.length=5 := rfl
  rw [hnl] at hnb hnp
  rw [hdl] at hdb hdp
  norm_num only at hnb hdb hnp hdp
  have hd0 : 0 < ld.prod := by linarith [hdb.1]
  have he : pairRationalWeight a b u x y=ln.prod/ld.prod := by
    unfold pairRationalWeight ln ld
    simp only [List.prod_cons,List.prod_nil,mul_one]
    congr 1 <;> ring
  rw [he]
  constructor
  · apply (le_div_iff₀ hd0).mpr
    nlinarith [hnb.1,hdb.2]
  constructor
  · apply (div_le_iff₀ hd0).mpr
    nlinarith [hnb.2,hdb.1]
  rw [div_sub_one (ne_of_gt hd0),abs_div,abs_of_pos hd0]
  apply (div_le_iff₀ hd0).mpr
  have hh : |ln.prod-ld.prod| ≤ 38*|u| := by
    have hh := abs_sub_le (ln.prod-1) 0 (ld.prod-1)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    simpa only [sub_sub_sub_cancel_right] using (hh.trans (add_le_add hnp hdp)).trans_eq (by ring)
  have hm := mul_le_mul_of_nonneg_left hdb.1 (show 0 ≤ 1216*|u| by positivity)
  nlinarith only [hh,hm]
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real

def pairK (a b u : ℝ) : ℝ :=
  (1-u^2)/((1+u*a*b)*(1-u^2*a^2)*(1-u^2*b^2))
def pairR (a b u : ℝ) : ℝ :=
  1+u*a*b+u^2*(a^2*b^2-a^2-b^2)-u^3*a*b

def pairCrossPolynomial (a b u p s r : ℝ) : ℝ :=
  pairK a b u*((-u+u^2*a*b)*p*s+u^2*b*(1-a^2)*r*p+
    u^2*a*(1-b^2)*r*s+pairR a b u*r^2)

lemma abs_mul_le_one_pair {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x*y| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) (by norm_num)).trans_eq (by ring)

lemma pairK_bounds {a b u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    |pairK a b u-1| ≤ 64*|u| ∧ 9/10 ≤ pairK a b u ∧ pairK a b u ≤ 2 := by
  have hu4 : |u| ≤ 1/4 := by linarith only [hu]
  have hua : |u| ≤ 1 := by linarith only [hu]
  have ha2 : |a^2| ≤ 1 := by simpa only [pow_two] using abs_mul_le_one_pair ha ha
  have hb2 : |b^2| ≤ 1 := by simpa only [pow_two] using abs_mul_le_one_pair hb hb
  have h₁ := pair_factor_control hu4 (abs_mul_le_one_pair ha hb)
  have h₂ := pair_factor_control hu4 (show |-u*a^2| ≤ 1 by simpa only [abs_neg,abs_mul] using abs_mul_le_one_pair hua ha2)
  have h₃ := pair_factor_control hu4 (show |-u*b^2| ≤ 1 by simpa only [abs_neg,abs_mul] using abs_mul_le_one_pair hua hb2)
  have he₂ : 1+u*(-u*a^2)=1-u^2*a^2 := by ring
  have he₃ : 1+u*(-u*b^2)=1-u^2*b^2 := by ring
  rw [he₂] at h₂
  rw [he₃] at h₃
  let l : List ℝ := [1+u*(a*b),1-u^2*a^2,1-u^2*b^2]
  have hl : ∀ z∈l,(1/2:ℝ) ≤ z ∧ z ≤ 2 := by
    intro z hz
    simp only [l,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> grind
  have hl' : ∀ z∈l,|z-1| ≤ |u| := by
    intro z hz
    simp only [l,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> grind
  have hlen : l.length=3 := rfl
  have hbounds := list_prod_between l hl
  have hperturb := (list_prod_perturb l (abs_nonneg u) hua hl').2
  rw [hlen] at hbounds hperturb
  norm_num only at hbounds hperturb
  have hd : 0 < l.prod := by linarith only [hbounds.1]
  have he : pairK a b u=(1-u^2)/l.prod := by
    unfold pairK l
    simp only [List.prod_cons,List.prod_nil,mul_one]
    congr 1; ring
  have hs : u^2 ≤ |u| := by nlinarith only [sq_abs u,abs_nonneg u,hu]
  have hp : |pairK a b u-1| ≤ 64*|u| := by
    rw [he,div_sub_one hd.ne',abs_div,abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    have hh : |1-u^2-l.prod| ≤ 8*|u| := by
      have hh := abs_add_le (-u^2) (1-l.prod)
      rw [abs_neg,abs_of_nonneg (sq_nonneg u),abs_sub_comm] at hh
      have he' : 1-u^2-l.prod= -u^2+(1-l.prod) := by ring
      rw [he']
      linarith only [hh,hs,hperturb]
    have hm := mul_le_mul_of_nonneg_left hbounds.1 (show 0 ≤ 64*|u| by positivity)
    nlinarith only [hh,hm]
  refine ⟨hp,?_,?_⟩ <;> have hh := abs_le.mp hp <;> linarith only [hu,hh.1,hh.2]

lemma pairR_bounds {a b u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    |pairR a b u-1| ≤ 5*|u| ∧ 9/10 ≤ pairR a b u := by
  have hua : |u| ≤ 1 := by linarith only [hu]
  have ha2 : |a^2| ≤ 1 := by simpa only [pow_two] using abs_mul_le_one_pair ha ha
  have hb2 : |b^2| ≤ 1 := by simpa only [pow_two] using abs_mul_le_one_pair hb hb
  have hab := abs_mul_le_one_pair ha hb
  have hab2 := abs_mul_le_one_pair ha2 hb2
  have hz : |a^2*b^2-a^2-b^2| ≤ 3 := by
    have h₁ := abs_sub_le (a^2*b^2) 0 (a^2)
    have h₂ := abs_sub_le (a^2*b^2-a^2) 0 (b^2)
    simp only [sub_zero,zero_sub,abs_neg] at h₁ h₂
    linarith only [h₁,h₂,ha2,hb2,hab2]
  have hs : u^2 ≤ |u| := by nlinarith only [sq_abs u,abs_nonneg u,hu]
  have hu3 : |u^3| ≤ |u| := by
    rw [pow_succ,abs_mul,abs_of_nonneg (sq_nonneg u)]
    have h' := mul_le_mul_of_nonneg_right hs (abs_nonneg u)
    nlinarith only [h',sq_abs u,hs]
  have h₁ : |u*a*b| ≤ |u| := by
    rw [mul_assoc,abs_mul]
    exact (mul_le_mul_of_nonneg_left hab (abs_nonneg u)).trans_eq (mul_one _)
  have h₂ : |u^2*(a^2*b^2-a^2-b^2)| ≤ 3*|u| := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg u)]
    have hh := mul_le_mul_of_nonneg_left hz (sq_nonneg u)
    nlinarith only [hh,hs]
  have h₃ : |u^3*a*b| ≤ |u| := by
    rw [mul_assoc,abs_mul]
    exact (mul_le_mul hu3 hab (abs_nonneg _) (abs_nonneg u)).trans_eq (mul_one _)
  have hp : |pairR a b u-1| ≤ 5*|u| := by
    have hh := abs_add_le (u*a*b) (u^2*(a^2*b^2-a^2-b^2))
    have hh' := abs_sub_le (u*a*b+u^2*(a^2*b^2-a^2-b^2)) 0 (u^3*a*b)
    simp only [sub_zero,zero_sub,abs_neg] at hh'
    have he : pairR a b u-1=u*a*b+u^2*(a^2*b^2-a^2-b^2)-u^3*a*b := by unfold pairR;ring
    rw [he]
    linarith only [hh,hh',h₁,h₂,h₃]
  exact ⟨hp,by have hh := (abs_le.mp hp).1;linarith only [hh,hu]⟩

lemma pairKR_lower {a b u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    1/2 ≤ pairK a b u*pairR a b u := by
  have h₁ := (pairK_bounds ha hb hu).2.1
  have h₂ := (pairR_bounds ha hb hu).2
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]
end SKGap

end
end

end OAI
