import Mathlib

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Relay

def width (i : ℕ) : ℝ := max 2 (210-(i : ℝ)/2)
def selectedSign (u : ℝ) : ℝ := if 0 ≤ u then -1 else 1

def domain (J T σ : ℝ) : Set (ℝ×ℝ) :=
  {x | |x.1| ≤ J ∧ |x.2| ≤ J/4+630} ∪
  {x | |x.1-T| ≤ J ∧ |x.2-σ*T/4| ≤ J/4+630} ∪
  {x | 0 ≤ x.1 ∧ x.1 ≤ T ∧ |x.2-σ*x.1/4| ≤ 630}

lemma width_lower (i : ℕ) : 2 ≤ width i := le_max_left _ _
lemma width_upper (i : ℕ) : width i ≤ 210 := by
  apply max_le (by norm_num)
  linarith [Nat.cast_nonneg (α := ℝ) i]
lemma width_next (i : ℕ) : width i ≤ width (i+1)+1/2 := by
  have h1 := width_lower (i+1)
  have h2 : 210-((i+1 : ℕ) : ℝ)/2 ≤ width (i+1) := le_max_right _ _
  unfold width at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  exact max_le (by linarith) (by linarith)
lemma width_last (L : ℕ) (hL : 416 ≤ L) : width L=2 := by
  apply max_eq_left
  have : (416 : ℝ) ≤ L := by exact_mod_cast hL
  linarith

lemma selectedSign_cases (u : ℝ) : selectedSign u=-1 ∨ selectedSign u=1 := by
  unfold selectedSign
  split  <;>  simp

lemma selectedSign_abs (u : ℝ) : |selectedSign u|=1 := by
  rcases selectedSign_cases u with h|h  <;>  rw [h]  <;>  norm_num

lemma move_towards_axis (u b : ℝ) (hu : |u| ≤ b) :
    |u+selectedSign u| ≤ max 1 (b-1) := by
  rw [abs_le] at hu ⊢
  have h1 : 1 ≤ max 1 (b-1) := le_max_left _ _
  have h2 : b-1 ≤ max 1 (b-1) := le_max_right _ _
  unfold selectedSign
  split  <;>  constructor  <;>  linarith

lemma full_step_height (i : ℕ) (u σ d e ε : ℝ) (hσ : |σ|=1)
    (hu : |u| ≤ width i+d) (hd₀ : 0 ≤ d) (hd : d+e/4 ≤ 1/4)
    (hε : |ε| ≤ e/4) :
    |u+selectedSign u-σ/4+ε| ≤ width (i+1) := by
  have h1 := width_lower (i+1)
  have h2 := width_next i
  have hs : |σ/4|=1/4 := by rw [abs_div,hσ]; norm_num
  calc
    _  ≤  |u+selectedSign u|+|σ/4|+|ε| :=
      by linarith [abs_add_le (u+selectedSign u-σ/4) ε, abs_sub (u+selectedSign u) (σ/4)]
    _  ≤  max 1 (width i+d-1)+1/4+e/4 := by
      rw [hs]
      linarith [move_towards_axis u (width i+d) hu]
    _  ≤  width (i+1) := by
      rcases le_total 1 (width i+d-1) with hh|hh
      · rw [max_eq_right hh]; linarith
      · rw [max_eq_left hh]; linarith

lemma full_step_time (i : ℕ) (y z d e : ℝ)
    (hy : |y-(i : ℝ)| ≤ (i+1)*e+d) (hz : |z-(y+1)| ≤ e/4)
    (hde : d+e/4 ≤ e) : |z-((i+1 : ℕ) : ℝ)| ≤ (i+2)*e := by
  rw [abs_le] at hy hz ⊢
  push_cast
  constructor  <;>  nlinarith

lemma path_axis_bound (L i : ℕ) (hi : i ≤ L) (y x : ℝ×ℝ) (d e σ : ℝ)
    (hσ : |σ|=1) (he : 0 ≤ e)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    |x.2-σ*x.1/4| ≤ 210+d+100+((L+1)*e+d+100)/4 := by
  have ht : |x.1-(i : ℝ)| ≤ (L+1)*e+d+100 := by
    have hc : (i : ℝ) ≤ L := by exact_mod_cast hi
    calc
      _  ≤  |x.1-y.1|+|y.1-(i : ℝ)| := abs_sub_le _ _ _
      _  ≤  100+((i+1)*e+d) := add_le_add hxt hyt
      _  ≤  _ := by nlinarith
  have hsame : σ*(i : ℝ)/4-σ*x.1/4=σ*((i : ℝ)-x.1)/4 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(i : ℝ)/4|+|σ*(i : ℝ)/4-σ*x.1/4| := by
      linarith [abs_sub_le x.2 (σ*(i : ℝ)/4) (σ*x.1/4),
        abs_sub_le x.2 y.2 (σ*(i : ℝ)/4)]
    _  ≤  100+(width i+d)+((L+1)*e+d+100)/4 := by
      rw [hsame,abs_div,abs_mul,hσ,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4),abs_sub_comm (i : ℝ)]
      exact add_le_add (add_le_add hxz hyz) (div_le_div_of_nonneg_right ht (by norm_num))
    _  ≤  _ := by linarith [width_upper i]

lemma band_mem_domain (J T σ : ℝ) (hσ : |σ|=1)
    (x : ℝ×ℝ) (ht : -J ≤ x.1 ∧ x.1 ≤ T+J)
    (hz : |x.2-σ*x.1/4| ≤ 630) : x∈domain J T σ := by
  have ha : |σ|=1 := hσ
  by_cases h0 : x.1 < 0
  · apply Or.inl; apply Or.inl
    have hx : |x.1| ≤ J := by rw [abs_of_neg h0]; linarith [ht.1]
    refine ⟨hx,?_⟩
    calc
      |x.2|  ≤  |x.2-σ*x.1/4|+|σ*x.1/4| := by simpa using abs_sub_le x.2 (σ*x.1/4) 0
      _  ≤  630+J/4 := by
        rw [abs_div,abs_mul,ha,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4)]
        exact add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
      _ = _ := add_comm _ _
  · by_cases h1 : T < x.1
    · apply Or.inl; apply Or.inr
      have hx : |x.1-T| ≤ J := by rw [abs_of_pos (by linarith)]; linarith [ht.2]
      refine ⟨hx,?_⟩
      calc
        _  ≤  |x.2-σ*x.1/4|+|σ*x.1/4-σ*T/4| := abs_sub_le _ _ _
        _ = |x.2-σ*x.1/4|+|x.1-T|/4 := by
          rw [show σ*x.1/4-σ*T/4=σ*(x.1-T)/4 by ring,abs_div,abs_mul,ha,one_mul]
          norm_num
        _  ≤  630+J/4 := add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
        _ = _ := add_comm _ _
    · exact Or.inr ⟨by linarith,by linarith,hz⟩

lemma move_path_contained (J : ℝ) (L i : ℕ) (hi : i ≤ L) (hJ : 26200 < J)
    (y x : ℝ×ℝ) (d e σ : ℝ) (hσ : |σ|=1) (he : 0 ≤ e)
    (hsmall : (L+1)*e+d < 1)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    x∈domain J (L+1/2) σ := by
  have hi' : (i : ℝ) ≤ L := by exact_mod_cast hi
  have hi₀ : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have heL : 0 ≤ (L+1)*e := mul_nonneg (by positivity) he
  apply band_mem_domain J (L+1/2) σ hσ x
  · rw [abs_le] at hyt hxt
    constructor  <;>  nlinarith
  · exact (path_axis_bound L i hi y x d e σ hσ he hyt hyz hxt hxz).trans (by linarith)

lemma last_crossing_height (L : ℕ) (y x : ℝ×ℝ) (d σ : ℝ) (hσ : |σ|=1)
    (hy : |y.2-σ*(L : ℝ)/4| ≤ 2+d) (hx : |x.2-y.2| ≤ 100) (hd : d < 1) :
    |x.2-σ*(L+1/2)/4| < 210 := by
  have he : σ*(L : ℝ)/4-σ*(L+1/2)/4=-σ/8 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(L : ℝ)/4|+|σ*(L : ℝ)/4-σ*(L+1/2)/4| :=
      by linarith [abs_sub_le x.2 (σ*(L : ℝ)/4) (σ*(L+1/2)/4),
        abs_sub_le x.2 y.2 (σ*(L : ℝ)/4)]
    _  ≤  100+(2+d)+1/8 := by
      rw [he,abs_div,abs_neg,hσ]
      norm_num
      linarith
    _  <  _ := by linarith

end CriticalPercolation.Relay
namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk
variable {V : Type*} {H : SimpleGraph V}

lemma exists_first_crossing (f : V → ℝ) (ρ T : ℝ)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y| ≤ ρ)
    {a b : V} (w : H.Walk a b) (ha : f a < T) (hb : T ≤ f b) :
    ∃ x∈w.support, T ≤ f x ∧ f x ≤ T+ρ := by
  induction w with
  | nil =>  exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T ≤ f c
    · refine ⟨c,?_,hc,?_⟩
      · simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]
        exact Or.inr w.start_mem_support
      · have hh := hf hac
        rw [abs_le] at hh
        linarith
    · obtain ⟨x,hx,h1,h2⟩ := ih (lt_of_not_ge hc) hb
      exact ⟨x,by simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx,h1,h2⟩
end SimpleGraph.Walk
end
end
end

end OAI
