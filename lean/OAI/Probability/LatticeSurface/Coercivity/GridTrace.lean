import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace

namespace NatGrid

abbrev Vertex := ℕ × ℕ

def rect (l u : Vertex) : Finset Vertex :=
  (Finset.Icc l.1 u.1) ×ˢ (Finset.Icc l.2 u.2)

def grad₁ (v : Vertex → ℝ) (l u : Vertex) : ℝ :=
  ∑ i ∈ Finset.Ico l.1 u.1, ∑ j ∈ Finset.Icc l.2 u.2, |v (i+1,j)-v (i,j)|

def grad₂ (v : Vertex → ℝ) (l u : Vertex) : ℝ :=
  ∑ i ∈ Finset.Icc l.1 u.1, ∑ j ∈ Finset.Ico l.2 u.2, |v (i,j+1)-v (i,j)|

def avg {ι : Type*} (S : Finset ι) (v : ι → ℝ) : ℝ := (∑ x ∈ S, v x)/(S.card:ℝ)

lemma line_bound (f : ℕ → ℝ) {l u a b : ℕ}
    (ha : a ∈ Finset.Icc l u) (hb : b ∈ Finset.Icc l u) :
    |f a-f b| ≤ ∑ i ∈ Finset.Ico l u, |f (i+1)-f i| := by
  have ordered (a b : ℕ) (ha : a ∈ Finset.Icc l u) (hb : b ∈ Finset.Icc l u)
      (hab : a ≤ b) : |f a-f b| ≤ ∑ i ∈ Finset.Ico l u, |f (i+1)-f i| := by
    rw [abs_sub_comm,← Finset.sum_Ico_sub f hab]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      have ha := Finset.mem_Icc.mp ha
      have hb := Finset.mem_Icc.mp hb
      have hi := Finset.mem_Ico.mp hi
      exact Finset.mem_Ico.mpr ⟨ha.1.trans hi.1,hi.2.trans_le hb.2⟩
    · intro i _ _;exact abs_nonneg _
  rcases le_total a b with hab | hba
  · exact ordered a b ha hb hab
  · simpa only [abs_sub_comm] using ordered b a hb ha hba

lemma rect_pointwise (v : Vertex → ℝ) (l u : Vertex)
    {a b : Vertex} (ha : a ∈ rect l u) (hb : b ∈ rect l u) :
    |v a-v b| ≤
      (∑ i ∈ Finset.Ico l.1 u.1, |v (i+1,a.2)-v (i,a.2)|) +
      (∑ j ∈ Finset.Ico l.2 u.2, |v (b.1,j+1)-v (b.1,j)|) := by
  obtain ⟨ha1,ha2⟩ := Finset.mem_product.mp ha
  obtain ⟨hb1,hb2⟩ := Finset.mem_product.mp hb
  calc
    _ ≤ |v a-v (b.1,a.2)|+|v (b.1,a.2)-v b| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (line_bound (fun i => v (i,a.2)) ha1 hb1)
      (line_bound (fun j => v (b.1,j)) ha2 hb2)

lemma rect_pair_bound (v : Vertex → ℝ) (l u : Vertex) :
    (∑ a ∈ rect l u, ∑ b ∈ rect l u, |v a-v b|) ≤
      ((Finset.Icc l.1 u.1).card:ℝ)^2 * (Finset.Icc l.2 u.2).card * grad₁ v l u +
      ((Finset.Icc l.2 u.2).card:ℝ)^2 * (Finset.Icc l.1 u.1).card * grad₂ v l u := by
  calc
    _ ≤ ∑ a ∈ rect l u, ∑ b ∈ rect l u,
      ((∑ i ∈ Finset.Ico l.1 u.1, |v (i+1,a.2)-v (i,a.2)|) +
       (∑ j ∈ Finset.Ico l.2 u.2, |v (b.1,j+1)-v (b.1,j)|)) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => rect_pointwise v l u ha hb))
    _ = _ := by
      simp only [rect]
      simp_rw [Finset.sum_product]
      simp only [Finset.sum_add_distrib,Finset.sum_const,
        nsmul_eq_mul,← Finset.mul_sum,grad₁,grad₂]
      rw [Finset.sum_comm (s := Finset.Icc l.2 u.2) (t := Finset.Ico l.1 u.1)]
      ring

lemma avg_diff_identity {ι : Type*} (A B : Finset ι) (v : ι → ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    avg A v-avg B v = (∑ a ∈ A, ∑ b ∈ B, (v a-v b))/((A.card:ℝ)*B.card) := by
  have ha : (A.card:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hA)
  have hb : (B.card:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hB)
  simp only [avg,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
  field_simp

lemma avg_subset_bound {ι : Type*} [DecidableEq ι] (A B : Finset ι) (v : ι → ℝ)
    (hA : A.Nonempty) (hAB : A ⊆ B) :
    |avg A v-avg B v| ≤
      (∑ a ∈ B, ∑ b ∈ B, |v a-v b|)/((A.card:ℝ)*B.card) := by
  have hB := hA.mono hAB
  rw [avg_diff_identity A B v hA hB,abs_div,abs_of_nonneg (by positivity : 0 ≤ (A.card:ℝ)*B.card)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ a ∈ A, |∑ b ∈ B, (v a-v b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, ∑ b ∈ B, |v a-v b| :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hAB (fun a _ _ => Finset.sum_nonneg (fun b _ => abs_nonneg _))

lemma rect_avg_bound (v : Vertex → ℝ) (l u : Vertex) (A : Finset Vertex)
    (hA : A.Nonempty) (hAB : A ⊆ rect l u) (s : ℝ)
    (hs1 : (Finset.Icc l.1 u.1).card ≤ s) (hs2 : (Finset.Icc l.2 u.2).card ≤ s) :
    |avg A v-avg (rect l u) v| ≤ s/(A.card:ℝ)*(grad₁ v l u+grad₂ v l u) := by
  have hB := hA.mono hAB
  have ha : 0 < (A.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have hb : 0 < ((rect l u).card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  have hg1 : 0 ≤ grad₁ v l u := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hg2 : 0 ≤ grad₂ v l u := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  calc
    _ ≤ (∑ a ∈ rect l u, ∑ b ∈ rect l u, |v a-v b|)/((A.card:ℝ)*(rect l u).card) := avg_subset_bound A _ v hA hAB
    _ ≤ (((Finset.Icc l.1 u.1).card:ℝ)^2*(Finset.Icc l.2 u.2).card*grad₁ v l u+
      ((Finset.Icc l.2 u.2).card:ℝ)^2*(Finset.Icc l.1 u.1).card*grad₂ v l u)/
      ((A.card:ℝ)*(rect l u).card) :=
      div_le_div_of_nonneg_right (rect_pair_bound v l u) (mul_nonneg ha.le hb.le)
    _ ≤ s/(A.card:ℝ)*(grad₁ v l u+grad₂ v l u) := by
      apply (div_le_iff₀ (mul_pos ha hb)).mpr
      rw [show s/(A.card:ℝ)*(grad₁ v l u+grad₂ v l u)*((A.card:ℝ)*(rect l u).card) =
          s*(grad₁ v l u+grad₂ v l u)*(rect l u).card by field_simp]
      have hBcard : ((rect l u).card:ℝ) = (Finset.Icc l.1 u.1).card*(Finset.Icc l.2 u.2).card := by simp [rect]
      rw [hBcard]
      nlinarith [mul_le_mul_of_nonneg_right hs1 (mul_nonneg (show (0:ℝ) ≤ (Finset.Icc l.1 u.1).card*(Finset.Icc l.2 u.2).card by positivity) hg1),
        mul_le_mul_of_nonneg_right hs2 (mul_nonneg (show (0:ℝ) ≤ (Finset.Icc l.1 u.1).card*(Finset.Icc l.2 u.2).card by positivity) hg2)]

end NatGrid

end GridTrace

end

end OAI
