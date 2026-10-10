import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalTaperAffine

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

def candidates (g P : ℚ) (d : I → ℚ) : Finset ℚ :=
  breakpoints P d ∪ ((breakpoints P d) ×ˢ (breakpoints P d)).image
    (fun p => (A P d ((p.1+p.2)/2)-1/g)/B P d ((p.1+p.2)/2))

theorem breakpoints_card (P : ℚ) (d : I → ℚ) :
    (breakpoints P d).card ≤ 2*Fintype.card I+2 := by
  unfold breakpoints
  have h1 := card_insert_le (0:ℚ) (insert (upper d)
    ((univ.image (fun i => (1-P)/d i)) ∪ (univ.image (fun i => 1/d i))))
  have h2 := card_insert_le (upper d)
    ((univ.image (fun i => (1-P)/d i)) ∪ (univ.image (fun i => 1/d i)))
  have h3 := card_union_le (univ.image (fun i => (1-P)/d i)) (univ.image (fun i => 1/d i))
  have h4 : (univ.image (fun i => (1-P)/d i)).card ≤ Fintype.card I := card_image_le.trans_eq (card_univ)
  have h5 : (univ.image (fun i => 1/d i)).card ≤ Fintype.card I := card_image_le.trans_eq (card_univ)
  omega

theorem candidates_card (g P : ℚ) (d : I → ℚ) :
    (candidates g P d).card ≤ (2*Fintype.card I+2)+(2*Fintype.card I+2)^2 := by
  apply (card_union_le _ _).trans
  have hi : (((breakpoints P d) ×ˢ (breakpoints P d)).image
      (fun p => (A P d ((p.1+p.2)/2)-1/g)/B P d ((p.1+p.2)/2))).card ≤
      (breakpoints P d).card*(breakpoints P d).card := card_image_le.trans_eq (card_product _ _)
  exact (Nat.add_le_add (breakpoints_card P d) (hi.trans
    (Nat.mul_le_mul (breakpoints_card P d) (breakpoints_card P d)))).trans_eq (by rw [pow_two])

theorem mass_upper (g P : ℚ) (d : I → ℚ) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1)
    (hd : ∀ i, 0 ≤ d i) :
    mass g P (fun i => (d i:ℝ)) (upper d)=colocatedMass g (fun i => (d i:ℝ)) := by
  apply sum_congr rfl
  intro i _
  by_cases hi : d i=0
  · simp only [hi,Rat.cast_zero,marginal_at_zero_distance hP hP1,mul_one,ite_true]
  · have hip : 0 < d i := lt_of_le_of_ne (hd i) (Ne.symm hi)
    have hb : (d i)⁻¹ ≤ ∑ t, (d t)⁻¹ := single_le_sum
      (fun t _ => inv_nonneg.mpr (hd t)) (mem_univ i)
    have hm := mul_le_mul_of_nonneg_right hb hip.le
    rw [inv_mul_cancel₀ hi] at hm
    have hu : 1 ≤ upper d*d i := by dsimp only [upper]; nlinarith only [hm,hip]
    have hur : 1 ≤ (upper d:ℝ)*(d i:ℝ) := by exact_mod_cast hu
    have hir : (d i:ℝ) ≠ 0 := by exact_mod_cast hi
    simp only [marginal_zero hur,mul_zero,ite_eq_right hir]

theorem maximal_root_in_candidates (g P : ℚ) (d : I → ℚ)
    (hg : 0 < (g:ℝ)) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (hcol : colocatedMass g (fun i => (d i:ℝ)) < 1)
    (r : ℝ) (hr : 0 < r) (hroot : mass g P (fun i => (d i:ℝ)) r=1)
    (hmax : ∀ u, 1 ≤ mass g P (fun i => (d i:ℝ)) u → u ≤ r) :
    ∃ q ∈ candidates g P d, (q:ℝ)=r := by
  classical
  by_cases heq : ∃ q ∈ breakpoints P d, (q:ℝ)=r
  · obtain ⟨q,hq,he⟩ := heq
    exact ⟨q,mem_union_left _ hq,he⟩
  have hnot : ∀ q ∈ breakpoints P d, (q:ℝ) ≠ r := by simpa only [not_exists,not_and] using heq
  have hU : r < (upper d:ℝ) := by
    by_contra hn
    have hh := mass_antitone (d := fun i => (d i:ℝ)) hg.le hP (fun i => by exact_mod_cast hd i) (le_of_not_gt hn)
    rw [hroot,mass_upper g P d hP (by linarith) hd] at hh
    linarith
  obtain ⟨a,ha,b,hb,har,hrb,hgap⟩ := rational_bracket (breakpoints P d) r 0 (upper d)
    (mem_insert_self _ _) (mem_insert_of_mem (mem_insert_self _ _)) (by simpa only [Rat.cast_zero] using hr) hU hnot
  have hab : a < b := by exact_mod_cast har.trans hrb
  let t : ℚ := (a+b)/2
  have ht : a < t ∧ t < b := by dsimp only [t]; constructor <;> linarith
  have hPq : P < 1 := by exact_mod_cast (show (P:ℝ) < 1 by linarith)
  have hcuts := cuts_in_interval hd hPq a b t hgap ht r ⟨har,hrb⟩
  have haff := mass_affine (g := g) hP hcuts.1 hcuts.2
  rw [hroot] at haff
  have hB : B P d t ≠ 0 := by
    intro hz
    let u := (r+(b:ℝ))/2
    have hur : r < u := by dsimp only [u]; linarith
    have hu : (a:ℝ) < u ∧ u < (b:ℝ) := by dsimp only [u]; constructor <;> linarith
    have hcu := cuts_in_interval hd hPq a b t hgap ht u hu
    have hfu := mass_affine (g := g) hP hcu.1 hcu.2
    rw [hz,Rat.cast_zero,mul_zero,sub_zero] at hfu haff
    have hmass : mass g P (fun i => (d i:ℝ)) u=1 := hfu.trans haff.symm
    exact not_le_of_gt hur (hmax u hmass.ge)
  refine ⟨(A P d t-1/g)/B P d t,mem_union_right _ (mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,rfl⟩),?_⟩
  have hBR : (B P d t:ℝ) ≠ 0 := by exact_mod_cast hB
  have hgR := hg.ne'
  push_cast
  apply (div_eq_iff hBR).mpr
  have hdiv : (A P d t:ℝ)-r*(B P d t:ℝ)=1/(g:ℝ) := (eq_div_iff hgR).mpr (by nlinarith [haff])
  linarith

end MetricKMedian.Taper
end
end

end OAI
