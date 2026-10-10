import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridTrace

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace

namespace NatGrid

end NatGrid

end GridTrace

namespace GridTrace.NatGrid

def lo (x : Vertex) (r : ℕ) : Vertex := (x.1-r,x.2-r)

def hi (N : ℕ) (x : Vertex) (r : ℕ) : Vertex := (min N (x.1+r),min N (x.2+r))

def box (N : ℕ) (x : Vertex) (r : ℕ) : Finset Vertex := rect (lo x r) (hi N x r)

def square (N : ℕ) : Finset Vertex := rect (0,0) (N,N)

abbrev Edge := Vertex ⊕ Vertex

def edges (l u : Vertex) : Finset Edge :=
  ((Finset.Ico l.1 u.1) ×ˢ (Finset.Icc l.2 u.2)).disjSum
  ((Finset.Icc l.1 u.1) ×ˢ (Finset.Ico l.2 u.2))

def edgeGrad (v : Vertex → ℝ) : Edge → ℝ
  | .inl (i,j) => |v (i+1,j)-v (i,j)|
  | .inr (i,j) => |v (i,j+1)-v (i,j)|

def anchor : Edge → Vertex
  | .inl x => x
  | .inr x => x

lemma square_mem {N : ℕ} {x : Vertex} : x ∈ square N ↔ x.1 ≤ N ∧ x.2 ≤ N := by
  simp [square,rect]

lemma mem_box_iff {N r : ℕ} {x y : Vertex} :
    y ∈ box N x r ↔ y.1 ≤ N ∧ y.2 ≤ N ∧
      y.1 ≤ x.1+r ∧ x.1 ≤ y.1+r ∧ y.2 ≤ x.2+r ∧ x.2 ≤ y.2+r := by
  simp only [box,rect,lo,hi,Finset.mem_product,Finset.mem_Icc,le_min_iff]
  omega

lemma box_self {N : ℕ} {x : Vertex} (hx : x ∈ square N) (r : ℕ) : x ∈ box N x r := by
  rw [mem_box_iff]
  have hx := square_mem.mp hx
  omega

lemma box_subset {N r s : ℕ} {x : Vertex} (hrs : r ≤ s) : box N x r ⊆ box N x s := by
  intro y hy
  rw [mem_box_iff] at hy ⊢
  omega

lemma box_subset_square (N : ℕ) (x : Vertex) (r : ℕ) : box N x r ⊆ square N := by
  intro y hy
  exact square_mem.mpr ⟨(mem_box_iff.mp hy).1,(mem_box_iff.mp hy).2.1⟩

lemma box_zero {N : ℕ} {x : Vertex} (hx : x ∈ square N) : box N x 0 = {x} := by
  ext y
  rw [mem_box_iff,Finset.mem_singleton]
  have hx := square_mem.mp hx
  constructor
  · intro h
    exact Prod.ext (by omega) (by omega)
  · rintro rfl;omega

lemma box_full {N r : ℕ} {x : Vertex} (hx : x ∈ square N) (hr : N ≤ r) :
    box N x r = square N := by
  ext y
  rw [mem_box_iff,square_mem]
  have hx := square_mem.mp hx
  omega

lemma side_lower {N x r : ℕ} (hx : x ≤ N) (hr : r ≤ N) :
    r+1 ≤ (Finset.Icc (x-r) (min N (x+r))).card := by
  rw [Nat.card_Icc]
  omega

lemma side_upper (N x r : ℕ) :
    (Finset.Icc (x-r) (min N (x+r))).card ≤ 2*r+1 := by
  rw [Nat.card_Icc]
  omega

lemma box_card_lower {N r : ℕ} {x : Vertex} (hx : x ∈ square N) (hr : r ≤ N) :
    (r+1)^2 ≤ (box N x r).card := by
  have hx := square_mem.mp hx
  simpa [box,rect,lo,hi,pow_two] using Nat.mul_le_mul (side_lower hx.1 hr) (side_lower hx.2 hr)

lemma edges_sum (v : Vertex → ℝ) (l u : Vertex) :
    ∑ e ∈ edges l u, edgeGrad v e = grad₁ v l u+grad₂ v l u := by
  simp [edges,Finset.sum_disjSum,Finset.sum_product,edgeGrad,grad₁,grad₂]

lemma edges_subset {l u l' u' : Vertex} (hl1 : l'.1 ≤ l.1) (hl2 : l'.2 ≤ l.2)
    (hu1 : u.1 ≤ u'.1) (hu2 : u.2 ≤ u'.2) : edges l u ⊆ edges l' u' := by
  intro e he
  cases e with
  | inl e =>
      simp only [edges,Finset.inl_mem_disjSum,Finset.mem_product,Finset.mem_Ico,Finset.mem_Icc] at he ⊢
      omega
  | inr e =>
      simp only [edges,Finset.inr_mem_disjSum,Finset.mem_product,Finset.mem_Ico,Finset.mem_Icc] at he ⊢
      omega

lemma box_edges_subset (N : ℕ) (x : Vertex) (r : ℕ) :
    edges (lo x r) (hi N x r) ⊆ edges (0,0) (N,N) := by
  apply edges_subset <;> simp [lo,hi]

lemma anchor_mem_rect {l u : Vertex} {e : Edge} (he : e ∈ edges l u) : anchor e ∈ rect l u := by
  cases e with
  | inl e =>
      simp only [edges,Finset.inl_mem_disjSum,Finset.mem_product,Finset.mem_Ico,Finset.mem_Icc] at he
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨he.1.1,he.1.2.le⟩,by simpa [anchor] using he.2⟩
  | inr e =>
      simp only [edges,Finset.inr_mem_disjSum,Finset.mem_product,Finset.mem_Ico,Finset.mem_Icc] at he
      exact Finset.mem_product.mpr ⟨by simpa [anchor] using he.1,Finset.mem_Icc.mpr ⟨he.2.1,he.2.2.le⟩⟩

lemma edges_card_bound (N : ℕ) (x : Vertex) (r : ℕ) :
    (edges (lo x r) (hi N x r)).card ≤ 2*(2*r+1)^2 := by
  have hx := side_upper N x.1 r
  have hy := side_upper N x.2 r
  have hx' : (Finset.Ico (x.1-r) (min N (x.1+r))).card ≤ 2*r+1 := by
    exact (Finset.card_le_card (by intro i hi;exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hi).1,(Finset.mem_Ico.mp hi).2.le⟩)).trans hx
  have hy' : (Finset.Ico (x.2-r) (min N (x.2+r))).card ≤ 2*r+1 := by
    exact (Finset.card_le_card (by intro i hi;exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hi).1,(Finset.mem_Ico.mp hi).2.le⟩)).trans hy
  simp only [edges,lo,hi,Finset.card_disjSum,Finset.card_product]
  nlinarith [Nat.mul_le_mul hx' hy, Nat.mul_le_mul hx hy']

lemma dyadic_step (v : Vertex → ℝ) {N : ℕ} {x : Vertex} (hx : x ∈ square N)
    (s : ℕ) (hs : 1 ≤ s) (hsN : s ≤ N) :
    |avg (box N x (s-1)) v-avg (box N x (2*s-1)) v| ≤
      (4/(s:ℝ))*(∑ e ∈ edges (lo x (2*s-1)) (hi N x (2*s-1)), edgeGrad v e) := by
  have hA : (box N x (s-1)).Nonempty := ⟨x,box_self hx _⟩
  have hcard : (s:ℝ)^2 ≤ ((box N x (s-1)).card:ℝ) := by
    have h := box_card_lower hx (show s-1 ≤ N by omega)
    have he : s-1+1=s := by omega
    rw [he] at h
    exact_mod_cast h
  have hside (i : ℕ) : ((Finset.Icc (i-(2*s-1)) (min N (i+(2*s-1)))).card:ℝ) ≤ 4*s := by
    have h := side_upper N i (2*s-1)
    have hh : 2*(2*s-1)+1 ≤ 4*s := by omega
    exact_mod_cast h.trans hh
  have hsp : (0:ℝ) < s := by exact_mod_cast hs
  have hc : (0:ℝ) < (box N x (s-1)).card := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have h := rect_avg_bound v (lo x (2*s-1)) (hi N x (2*s-1))
    (box N x (s-1)) hA (box_subset (by omega)) (4*s) (hside x.1) (hside x.2)
  rw [← edges_sum] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by
    apply (div_le_div_iff₀ hc hsp).mpr
    nlinarith) (Finset.sum_nonneg (fun e _ => by cases e <;> exact abs_nonneg _)))

end GridTrace.NatGrid

end

end OAI
