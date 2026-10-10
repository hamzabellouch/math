import OAI.Combinatorics.ThinTrees.Model

namespace OAI

universe uV uE uV2 uE2 uV3 uE3 uI uI2 uI3

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

lemma integrable_interval_indicator (a b c : ℝ) :
    Integrable ((Set.Ioc a b).indicator (fun _ : ℝ => c)) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp [Real.volume_Ioc]))

lemma integral_interval_indicator (a b c : ℝ) (hab : a ≤ b) :
    (∫ t : ℝ, (Set.Ioc a b).indicator (fun _ => c) t) = (b-a)*c := by
  rw [integral_indicator_const c measurableSet_Ioc, Real.volume_real_Ioc,
    max_eq_left (sub_nonneg.mpr hab), smul_eq_mul]

lemma threshold_interval {x y t : ℝ} :
    ((x < t ∧ ¬ y < t) ∨ (y < t ∧ ¬ x < t)) ↔ t ∈ Set.Ioc (min x y) (max x y) := by
  simp only [Set.mem_Ioc, min_lt_iff, le_max_iff, not_lt]
  constructor
  · rintro (h | h)
    · exact ⟨Or.inl h.1, Or.inr h.2⟩
    · exact ⟨Or.inr h.1, Or.inl h.2⟩
  · rintro ⟨h | h, h' | h'⟩ <;> first | (exfalso; linarith) | exact Or.inl ⟨h, h'⟩ | exact Or.inr ⟨h, h'⟩

lemma finite_coarea {V : Type uV} {E : Type uE} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) :
    (∫ t : ℝ, (((univ.filter (fun e =>
      (f (u e)<t ∧ ¬f (v e)<t) ∨ (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) =
      ∑e, |f (u e)-f (v e)| := by
  have heq (t : ℝ) :
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ)) =
      ∑e, (Set.Ioc (min (f (u e)) (f (v e)))
        (max (f (u e)) (f (v e)))).indicator (fun _ : ℝ => (1:ℝ)) t := by
    simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    apply sum_congr rfl
    intro e he
    rw [Set.indicator_apply]
    simp only [threshold_interval]
    split_ifs <;> norm_num
  simp_rw [heq]
  rw [integral_finsetSum _ (fun e _ => integrable_interval_indicator _ _ _)]
  apply sum_congr rfl
  intro e he
  rw [integral_interval_indicator _ _ _ min_le_max, mul_one]
  simpa only [abs_sub_comm] using (max_sub_min_eq_abs (f (u e)) (f (v e)))

lemma integrable_cut_card {V : Type uV2} {E : Type uE2} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) :
    Integrable (fun t : ℝ =>
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) := by
  have hi := integrable_finsetSum univ
    (fun e _ => integrable_interval_indicator (min (f (u e)) (f (v e)))
      (max (f (u e)) (f (v e))) 1)
  apply hi.congr
  filter_upwards with t
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro e he
  rw [Set.indicator_apply]
  simp only [threshold_interval]
  split_ifs <;> norm_num

lemma cut_range_bound {V : Type uV3} {E : Type uE3} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) {a b k : ℝ} (hab : a ≤ b)
    (hcut : ∀t ∈ Set.Ioc a b, k ≤
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) :
    k*(b-a) ≤ ∑e, |f (u e)-f (v e)| := by
  have hh := integral_mono (integrable_interval_indicator a b k)
    (integrable_cut_card u v f) (show (Set.Ioc a b).indicator (fun _ : ℝ => k) ≤
      (fun t : ℝ => (((univ.filter (fun e =>
        (f (u e)<t ∧ ¬f (v e)<t) ∨ (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) by
        intro t
        by_cases ht : t ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem ht]
          exact hcut t ht
        · rw [Set.indicator_of_notMem ht]
          positivity)
  rw [integral_interval_indicator a b k hab, finite_coarea] at hh
  simpa only [mul_comm] using hh

def clamp (a b x : ℝ) : ℝ := min b (max a x)

lemma clamp_eq_left {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) : clamp a b x = a := by
  simp [clamp, max_eq_left hx, min_eq_right hab]

lemma clamp_eq_right {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) : clamp a b x = b := by
  simp [clamp, max_eq_right (hab.trans hx), min_eq_left hx]

lemma clamp_bounds {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    a ≤ clamp a b x ∧ clamp a b x ≤ b := by
  exact ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩

lemma clamp_lt_iff {a b x t : ℝ} (ht : t ∈ Set.Ioc a b) :
    clamp a b x < t ↔ x < t := by
  simp only [clamp, min_lt_iff, max_lt_iff]
  constructor
  · rintro (h | h)
    · linarith [ht.2]
    · exact h.2
  · intro h
    exact Or.inr ⟨ht.1, h⟩

end
end StrongThinTree.Geometry

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m : ℕ} (G : MultiGraph n m)

lemma clamped_variation_lower {k : ℕ} (hk : G.EdgeConnected k)
    (f : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hu : ∃u, f u ≤ a) (hv : ∃v, b ≤ f v) :
    (k : ℝ)*(b-a) ≤ ∑e : Fin m,
      |clamp a b (f (G.left e))-clamp a b (f (G.right e))| := by
  classical
  apply cut_range_bound G.left G.right (fun v => clamp a b (f v)) hab
  intro t ht
  let S := univ.filter (fun v => f v < t)
  have hne : S.Nonempty := by
    obtain ⟨u, hu⟩ := hu
    exact ⟨u, mem_filter.mpr ⟨mem_univ _, lt_of_le_of_lt hu ht.1⟩⟩
  have hproper : S ≠ univ := by
    obtain ⟨v, hv⟩ := hv
    intro heq
    have hh : v ∈ S := heq.symm ▸ mem_univ v
    have := (mem_filter.mp hh).2
    linarith [ht.2]
  have hc := hk S hne hproper
  have hset : (univ.filter (fun e =>
      (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
      (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))) = G.cut univ S := by
    ext e
    simp only [S, cut, mem_filter, mem_univ, true_and, clamp_lt_iff ht]
  rw [hset]
  exact_mod_cast hc

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

lemma clamp_mono {a b x y : ℝ} (hxy : x ≤ y) : clamp a b x ≤ clamp a b y :=
  min_le_min_left _ (max_le_max_left _ hxy)

lemma clipped_affine_interval_increasing {a b x y : ℝ} (hab : a ≤ b) (hxy : x < y) :
    ∃ l r : ℝ, 0 ≤ l ∧ l ≤ r ∧ r ≤ 1 ∧
      |clamp a b x-clamp a b y| = |y-x| *(r-l) ∧
      ∀t ∈ Set.Ioo l r, a < x+t*(y-x) ∧ x+t*(y-x) < b := by
  by_cases heq : clamp a b x = clamp a b y
  · exact ⟨0,0,by norm_num,by norm_num,by norm_num,by simp [heq],by simp⟩
  have hAB := lt_of_le_of_ne (clamp_mono hxy.le) heq
  have hAx := clamp_bounds hab x
  have hBy := clamp_bounds hab y
  have hx : x < b := by
    by_contra h
    have hh := clamp_eq_right hab (not_lt.mp h)
    linarith
  have hy : a < y := by
    by_contra h
    have hh := clamp_eq_left hab (not_lt.mp h)
    linarith
  have hxA : x ≤ clamp a b x := by
    rw [clamp, min_eq_right (max_le hab hx.le)]
    exact le_max_right _ _
  have hBy' : clamp a b y ≤ y := by
    rw [clamp, max_eq_right hy.le]
    exact min_le_right _ _
  let s := y-x
  have hs : 0 < s := sub_pos.mpr hxy
  let l := (clamp a b x-x)/s
  let r := (clamp a b y-x)/s
  have hl : 0 ≤ l := div_nonneg (sub_nonneg.mpr hxA) hs.le
  have hr : r ≤ 1 := (div_le_one hs).mpr (by dsimp [s]; linarith)
  have hlr : l ≤ r := (div_le_div_iff_of_pos_right hs).mpr (by linarith)
  have hlmul : l*s = clamp a b x-x := div_mul_cancel₀ _ hs.ne'
  have hrmul : r*s = clamp a b y-x := div_mul_cancel₀ _ hs.ne'
  refine ⟨l,r,hl,hlr,hr,?_,?_⟩
  · rw [abs_of_nonpos (by linarith : clamp a b x-clamp a b y ≤ 0),
      abs_of_pos (sub_pos.mpr hxy)]
    dsimp [s] at hlmul hrmul
    nlinarith
  · intro t ht
    have hlt := mul_lt_mul_of_pos_right ht.1 hs
    have htr := mul_lt_mul_of_pos_right ht.2 hs
    dsimp [s] at hlt htr hlmul hrmul
    constructor <;> nlinarith

lemma clipped_affine_interval {a b x y : ℝ} (hab : a ≤ b) :
    ∃ l r : ℝ, 0 ≤ l ∧ l ≤ r ∧ r ≤ 1 ∧
      |clamp a b x-clamp a b y| = |y-x| *(r-l) ∧
      ∀t ∈ Set.Ioo l r, a < x+t*(y-x) ∧ x+t*(y-x) < b := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact clipped_affine_interval_increasing hab hxy
  · subst y
    exact ⟨0,0,by norm_num,by norm_num,by norm_num,by simp,by simp⟩
  · obtain ⟨l,r,hl,hlr,hr,heq,h⟩ := clipped_affine_interval_increasing hab hxy
    refine ⟨1-r,1-l,by linarith,by linarith,by linarith,?_,?_⟩
    · rw [abs_sub_comm, heq, abs_sub_comm x y]
      congr 1
      ring
    · intro t ht
      have hh := h (1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
      constructor <;> nlinarith [hh.1,hh.2]

lemma clamped_affine_disjoint_sum {I : Type uI} [Fintype I]
    (a b x y : I → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hab : ∀i, a i ≤ b i) (hslope : ∀i, |y i-x i| ≤ L)
    (hdis : ∀ i j, i ≠ j → ∀t ∈ Set.Ioo (0:ℝ) 1,
      ¬(a i < x i+t*(y i-x i) ∧ x i+t*(y i-x i)<b i ∧
        a j < x j+t*(y j-x j) ∧ x j+t*(y j-x j)<b j)) :
    ∑i, |clamp (a i) (b i) (x i)-clamp (a i) (b i) (y i)| ≤ L := by
  classical
  choose l r hl hlr hr heq hactive using fun i =>
    clipped_affine_interval (x:=x i) (y:=y i) (hab i)
  have hsub : (⋃i, Set.Ioo (l i) (r i)) ⊆ Set.Ioo (0:ℝ) 1 := by
    rintro t ⟨_,⟨i,rfl⟩,ht⟩
    exact ⟨lt_of_le_of_lt (hl i) ht.1,lt_of_lt_of_le ht.2 (hr i)⟩
  have hd : Pairwise (fun i j => Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t hti htj
    exact hdis i j hij t ⟨lt_of_le_of_lt (hl i) hti.1,
      lt_of_lt_of_le hti.2 (hr i)⟩ ⟨(hactive i t hti).1,(hactive i t hti).2,
        (hactive j t htj).1,(hactive j t htj).2⟩
  have hv := measureReal_mono (μ:=volume) hsub (by simp [Real.volume_Ioo])
  rw [measureReal_iUnion_fintype hd (fun _ => measurableSet_Ioo)
      (fun _ => by simp [Real.volume_Ioo]), Real.volume_real_Ioo] at hv
  simp only [Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr (hlr _))] at hv
  have hsum : ∑i, (r i-l i) ≤ 1 := by simpa using hv
  calc
    _ = ∑i, |y i-x i| *(r i-l i) := sum_congr rfl (fun i _ => heq i)
    _ ≤ ∑i, L*(r i-l i) := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hslope i) (sub_nonneg.mpr (hlr i)))
    _ = L*∑i, (r i-l i) := (mul_sum _ _ _).symm
    _ ≤ L*1 := mul_le_mul_of_nonneg_left hsum hL
    _ = L := mul_one L

end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry
noncomputable section
open Finset

def cube {h : ℕ} (x : Fin h → ℝ) : Prop := ∀j, 0 ≤ x j ∧ x j ≤ 1

def binary {h : ℕ} (x : Fin h → ℝ) : Prop := ∀j, x j = 0 ∨ x j = 1

def l1dist {h : ℕ} (x y : Fin h → ℝ) : ℝ := ∑j, |x j-y j|

lemma binary_cube {h : ℕ} {x : Fin h → ℝ} (hx : binary x) : cube x := by
  intro j
  rcases hx j with h | h <;> simp [h]

lemma l1dist_nonneg {h : ℕ} (x y : Fin h → ℝ) : 0 ≤ l1dist x y :=
  sum_nonneg (fun _ _ => abs_nonneg _)

lemma l1dist_comm {h : ℕ} (x y : Fin h → ℝ) : l1dist x y = l1dist y x := by
  simp only [l1dist, abs_sub_comm]

lemma l1dist_reverse {h : ℕ} (x y z : Fin h → ℝ) :
    |l1dist x z-l1dist y z| ≤ l1dist x y := by
  rw [l1dist, l1dist, ← sum_sub_distrib]
  calc
    _ ≤ ∑j, abs (abs (x j-z j) - abs (y j-z j)) := abs_sum_le_sum_abs _ _
    _ ≤ ∑j, |x j-y j| := by
      apply sum_le_sum
      intro j _
      simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le_abs_sub (x j-z j) (y j-z j)
    _ = _ := rfl

lemma cube_segment {h : ℕ} {x y : Fin h → ℝ} (hx : cube x) (hy : cube y)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : cube (fun j => x j+t*(y j-x j)) := by
  intro j
  have h1 : 0 ≤ (1-t)*x j+t*y j := add_nonneg
    (mul_nonneg (by linarith [ht.2]) (hx j).1) (mul_nonneg ht.1 (hy j).1)
  have h2 : (1-t)*x j+t*y j ≤ (1-t)*1+t*1 := add_le_add
    (mul_le_mul_of_nonneg_left (hx j).2 (by linarith [ht.2]))
    (mul_le_mul_of_nonneg_left (hy j).2 ht.1)
  constructor <;> nlinarith

lemma binary_radial_affine {h : ℕ} {x y z : Fin h → ℝ}
    (hx : cube x) (hy : cube y) (hz : binary z)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    l1dist (fun j => x j+t*(y j-x j)) z =
      l1dist x z+t*(l1dist y z-l1dist x z) := by
  have hc := cube_segment hx hy ht
  unfold l1dist
  rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rcases hz j with hzj | hzj
  · simp only [hzj, sub_zero, abs_of_nonneg (hx j).1, abs_of_nonneg (hy j).1,
      abs_of_nonneg (hc j).1]
  · rw [hzj, abs_of_nonpos (sub_nonpos.mpr (hc j).2),
      abs_of_nonpos (sub_nonpos.mpr (hx j).2), abs_of_nonpos (sub_nonpos.mpr (hy j).2)]
    ring

lemma binary_shell_edge_bound {h : ℕ} {I : Type uI2} [Fintype I]
    {x y : Fin h → ℝ} (hx : cube x) (hy : cube y)
    (z : I → Fin h → ℝ) (hz : ∀i, binary (z i)) (a b : I → ℝ)
    (hab : ∀i, a i ≤ b i)
    (hdis : ∀i j, i ≠ j → ∀w, cube w →
      ¬(a i < l1dist w (z i) ∧ l1dist w (z i)<b i ∧
        a j < l1dist w (z j) ∧ l1dist w (z j)<b j)) :
    ∑i, |clamp (a i) (b i) (l1dist x (z i))-
      clamp (a i) (b i) (l1dist y (z i))| ≤ l1dist x y := by
  apply clamped_affine_disjoint_sum a b _ _ (l1dist_nonneg x y) hab
  · intro i
    simpa only [l1dist_comm y x] using l1dist_reverse y x (z i)
  · intro i j hij t ht hbad
    have htc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    apply hdis i j hij (fun j => x j+t*(y j-x j)) (cube_segment hx hy htc)
    simpa only [binary_radial_affine hx hy (hz i) htc,
      binary_radial_affine hx hy (hz j) htc] using hbad

end
end StrongThinTree.Geometry

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry

lemma binary_shell_length_bound {n m h : ℕ} (G : MultiGraph n m) {k : ℕ}
    (hk : G.EdgeConnected k) (X : Fin n → Fin h → ℝ) (hX : ∀v, cube (X v))
    {I : Type uI3} [Fintype I] (z : I → Fin h → ℝ) (hz : ∀i, binary (z i))
    (a b : I → ℝ) (hab : ∀i, a i ≤ b i)
    (hu : ∀i, ∃u, l1dist (X u) (z i) ≤ a i)
    (hv : ∀i, ∃v, b i ≤ l1dist (X v) (z i))
    (hdis : ∀i j, i ≠ j → ∀w, cube w →
      ¬(a i < l1dist w (z i) ∧ l1dist w (z i)<b i ∧
        a j < l1dist w (z j) ∧ l1dist w (z j)<b j)) :
    (k:ℝ)*(∑i, (b i-a i)) ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  classical
  calc
    _ = ∑i, (k:ℝ)*(b i-a i) := mul_sum _ _ _
    _ ≤ ∑i, ∑e : Fin m, |clamp (a i) (b i) (l1dist (X (G.left e)) (z i))-
      clamp (a i) (b i) (l1dist (X (G.right e)) (z i))| := by
      apply sum_le_sum
      intro i _
      exact G.clamped_variation_lower hk _ (hab i) (hu i) (hv i)
    _ = ∑e : Fin m, ∑i, |clamp (a i) (b i) (l1dist (X (G.left e)) (z i))-
      clamp (a i) (b i) (l1dist (X (G.right e)) (z i))| := sum_comm
    _ ≤ _ := sum_le_sum (fun e _ => binary_shell_edge_bound (hX _) (hX _) z hz a b hab hdis)

end
end StrongThinTree.MultiGraph

end

end OAI
