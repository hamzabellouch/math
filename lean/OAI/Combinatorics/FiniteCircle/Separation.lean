import OAI.Combinatorics.FiniteCircle.Histograms

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

noncomputable def coordDist {X ι : Type*} [Fintype ι] (F : X → ι → ℝ) (x y : X) : ℝ :=
  ∑ i, |F x i - F y i|

theorem coordDist_nonneg {X ι : Type*} [Fintype ι] (F : X → ι → ℝ) (x y : X) :
    0 ≤ coordDist F x y := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem coordDist_symm {X ι : Type*} [Fintype ι] (F : X → ι → ℝ) (x y : X) :
    coordDist F x y = coordDist F y x := by simp only [coordDist, abs_sub_comm]

theorem coordDist_triangle {X ι : Type*} [Fintype ι] (F : X → ι → ℝ) (x y z : X) :
    coordDist F x z ≤ coordDist F x y + coordDist F y z := by
  unfold coordDist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_sub_le _ _ _)

def normalizeWord {α : Type*} (a : α) (m : ℕ) (x : List α) : List.Vector α m :=
  ⟨x.take m ++ List.replicate (m - x.length) a, by simp; omega⟩

theorem normalizeWord_val {α : Type*} (a : α) {m : ℕ} {x : List α} (h : x.length ≤ m) :
    (normalizeWord a m x).val = x ++ List.replicate (m-x.length) a := by
  simp only [normalizeWord, List.take_of_length_le h]

theorem normalizeWord_deficit {α : Type*} (a : α) {m : ℕ} {x y : List α}
    (hx : x.length ≤ m) (hy : x.length = y.length) :
    deficit (normalizeWord a m x).val (normalizeWord a m y).val = deficit x y := by
  rw [normalizeWord_val a hx, normalizeWord_val a (by omega), ← hy]
  simp only [deficit, List.length_append, List.length_replicate, lcs_append_common_right]
  omega

def windowWords {α : Type*} (a : α) (x : List α) (start m s : ℕ) : List (List.Vector α m) :=
  (windows x start m s).map (normalizeWord a m)

@[simp] theorem length_windowWords {α : Type*} (a : α) (x : List α) (start m s : ℕ) :
    (windowWords a x start m s).length = s := by simp [windowWords]

theorem windowWords_ofFn {α : Type*} (a : α) (x : List α) (start m s : ℕ) :
    windowWords a x start m s =
      List.ofFn (fun r : Fin s => normalizeWord a m (segment x (start+r) (m-s+1))) := by
  simp [windowWords, windows, List.map_ofFn, Function.comp_def]

theorem windows_segment {α : Type*} (x : List α) {start m s : ℕ}
    (_hs : 1 ≤ s) (hsm : s ≤ m) :
    windows (segment x start m) 0 m s = windows x start m s := by
  unfold windows
  congr 1
  funext r
  simp only [Nat.zero_add]
  exact segment_segment x start m r (m-s+1) (by have := r.isLt; omega)

theorem windowWords_segment {α : Type*} (a : α) (x : List α) {start m s : ℕ}
    (hs : 1 ≤ s) (hsm : s ≤ m) :
    windowWords a (segment x start m) 0 m s = windowWords a x start m s := by
  simp only [windowWords, windows_segment x hs hsm]

theorem cross_window_deficit {α : Type*} (a : α) {x y : List α} {m s : ℕ}
    (hx : x.length = m) (hy : y.length = m) (hs : 1 ≤ s) (hsm : s ≤ m)
    (hq : 2*s ≤ deficit x y + 1) (i j : Fin s) :
    s ≤ deficit (normalizeWord a m (segment x i (m-s+1))).val
      (normalizeWord a m (segment y j (m-s+1))).val := by
  have hxi : (segment x i (m-s+1)).length = m-s+1 :=
    length_segment (by have := i.isLt; omega)
  have hyj : (segment y j (m-s+1)).length = m-s+1 :=
    length_segment (by have := j.isLt; omega)
  rw [normalizeWord_deficit a (by omega) (by omega)]
  have hmono := lcs_mono (segment_sublist x i (m-s+1)) (segment_sublist y j (m-s+1))
  have hb := lcs_le_length_left x y
  simp only [deficit, hxi] at *
  omega

theorem exists_separating_scale {m q : ℕ} (hq : 0 < q) (hqm : q ≤ m) :
    ∃ k : Fin (Nat.log 2 m + 1), 1 ≤ 2^k.val ∧ 2^k.val ≤ m ∧
      q ≤ 4 * 2^k.val ∧ 2 * 2^k.val ≤ q+1 := by
  let n := (q+1)/2
  have hn : 0 < n := by dsimp [n]; omega
  have hnm : n ≤ m := by dsimp [n]; omega
  let k := Nat.log 2 n
  have hk : k ≤ Nat.log 2 m := Nat.log_mono_right hnm
  have hpow : 2^k ≤ n := Nat.pow_le_of_le_log hn.ne' le_rfl
  have hlt : n < 2^(k+1) := Nat.lt_pow_succ_log_self (by norm_num) n
  refine ⟨⟨k, by omega⟩, ?_, hpow.trans hnm, ?_, ?_⟩
  · change 1 ≤ 2^k
    have hp : 0 < 2^k := pow_pos (by norm_num) _
    omega
  · change q ≤ 4 * 2^k
    simp only [pow_succ] at hlt
    dsimp [n] at *
    omega
  · change 2 * 2^k ≤ q+1
    dsimp [n] at hpow
    omega

noncomputable def partitionRate (s : ℕ) : ℝ := 4 * Real.log (s+1) / s

theorem partitionRate_nonneg (s : ℕ) : 0 ≤ partitionRate s := by
  unfold partitionRate
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (Nat.cast_nonneg _)

theorem partition_collision_bound {s : ℕ} (hs : 1 ≤ s) {ρ : ℝ} (hρ : s ≤ ρ) :
    Real.exp (-partitionRate s * ρ) ≤ ((s : ℝ)+1)⁻¹ ^ 4 := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  calc
    _ ≤ Real.exp (-partitionRate s * s) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hρ (neg_nonpos.mpr (partitionRate_nonneg s)))
    _ = _ := by
      rw [show -partitionRate s * s = -(4 * Real.log ((s:ℝ)+1)) by
        unfold partitionRate; field_simp]
      rw [Real.exp_neg, show 4 * Real.log ((s:ℝ)+1) = (4:ℕ) * Real.log ((s:ℝ)+1) by norm_num,
        Real.exp_nat_mul, Real.exp_log (by positivity), inv_pow]

theorem scale_collision_union {s : ℕ} : (s : ℝ)^2 * (((s:ℝ)+1)⁻¹ ^ 4) ≤ 1/2 := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  rw [inv_pow, mul_inv_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ((s:ℝ)^2), sq_nonneg ((s:ℝ)-1)]

theorem block_histogram_lower {α Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]
    (a : α) {m s : ℕ} (F : List.Vector α m → ι → ℝ)
    (hF : ∀ u v, (deficit u.val v.val : ℝ) ≤ coordDist F u v)
    (μ : FiniteLaw Ω) (label : Ω → List.Vector α m → Y)
    (he : ∀ u v, μ.event (fun ω => label ω u = label ω v) =
      Real.exp (-partitionRate s * coordDist F u v))
    {x y : List α} (hx : x.length = m) (hy : y.length = m)
    (hs : 1 ≤ s) (hsm : s ≤ m) (hq : 2*s ≤ deficit x y + 1) :
    (s:ℝ) ≤ μ.expect (fun ω => histDist (label ω) (windowWords a x 0 m s) (windowWords a y 0 m s)) := by
  rw [windowWords_ofFn, windowWords_ofFn]
  simp only [Nat.zero_add]
  apply expect_histDist_ofFn_ge μ label _ _ (((s:ℝ)+1)⁻¹^4) _ scale_collision_union
  intro i j
  rw [he]
  apply partition_collision_bound hs
  exact (Nat.cast_le.mpr (cross_window_deficit a hx hy hs hsm hq i j)).trans (hF _ _)

theorem normalized_slide_segment {α : Type*} (a : α) {x y : List α} (h : Slide x y)
    {m len start : ℕ} (hlen : len ≤ m) :
    deficit (normalizeWord a m (segment x start len)).val
      (normalizeWord a m (segment y start len)).val ≤ 2 := by
  have hx : (segment x start len).length ≤ m := by
    simp only [segment, List.length_take, List.length_drop]
    exact (min_le_left _ _).trans hlen
  have hy : (segment x start len).length = (segment y start len).length := by
    simp only [segment, List.length_take, List.length_drop, h.length_eq]
  rw [normalizeWord_deficit a hx hy, deficit_eq_unequalDeficit hy]
  exact h.segment_deficit_le_two _ _

theorem block_histogram_pairing {α Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]
    (a : α) {m s : ℕ} (F : List.Vector α m → ι → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hF : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val)
    (μ : FiniteLaw Ω) (label : Ω → List.Vector α m → Y)
    (he : ∀ u v, μ.event (fun ω => label ω u = label ω v) =
      Real.exp (-partitionRate s * coordDist F u v))
    {x y : List α} (hxy : Slide x y) (start : ℕ) (hs : 1 ≤ s) (hsm : s ≤ m) :
    μ.expect (fun ω => histDist (label ω) (windowWords a x start m s) (windowWords a y start m s)) ≤
      16 * Real.log ((s:ℝ)+1) * Λ := by
  rw [windowWords_ofFn, windowWords_ofFn]
  calc
    _ ≤ 2 * s * (2 * partitionRate s * Λ) := by
      apply expect_histDist_ofFn_le
      intro i
      have hr := partition_separation_le μ label (coordDist F) (partitionRate s) he
        (normalizeWord a m (segment x (start+i) (m-s+1)))
        (normalizeWord a m (segment y (start+i) (m-s+1)))
      refine hr.trans ?_
      calc
        _ ≤ partitionRate s * (Λ * 2) := by
          apply mul_le_mul_of_nonneg_left _ (partitionRate_nonneg s)
          refine (hF _ _).trans ?_
          apply mul_le_mul_of_nonneg_left _ hΛ
          exact_mod_cast normalized_slide_segment a hxy (by omega : m-s+1 ≤ m)
        _ = _ := by ring
    _ = _ := by
      have hs0 : (s:ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
      unfold partitionRate
      field_simp
      ring

theorem fin_index_indicator_sum (b p : ℕ) :
    (∑ j : Fin b, if j.val = p then (1:ℝ) else 0) ≤ 1 := by
  classical
  by_cases hp : p < b
  · have he (j : Fin b) : j.val = p ↔ j = ⟨p,hp⟩ := by simp only [Fin.ext_iff]
    simp only [he]
    simp
  · have hn (j : Fin b) : j.val ≠ p := by have := j.isLt; omega
    simp [hn]

theorem histogram_forward_bound {α Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]
    (a : α) {m s : ℕ} (F : List.Vector α m → ι → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hF : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val)
    (μ : FiniteLaw Ω) (label : Ω → List.Vector α m → Y)
    (he : ∀ u v, μ.event (fun ω => label ω u = label ω v) =
      Real.exp (-partitionRate s * coordDist F u v))
    (u v t : List α) (c d : α) (b : ℕ) (hs : 1 ≤ s) (hsm : s ≤ m) :
    (∑ j : Fin b, μ.expect (fun ω => histDist (label ω)
      (windowWords a (u ++ c :: (v ++ t)) (j*m) m s)
      (windowWords a (u ++ v ++ d :: t) (j*m) m s))) ≤
      2*b + 32 * Real.log ((s:ℝ)+1) * Λ := by
  classical
  let B := 16 * Real.log ((s:ℝ)+1) * Λ
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) s; linarith))) hΛ
  let p := u.length / m
  let q := (u.length + v.length) / m
  have hb (j : Fin b) : μ.expect (fun ω => histDist (label ω)
      (windowWords a (u ++ c :: (v ++ t)) (j*m) m s)
      (windowWords a (u ++ v ++ d :: t) (j*m) m s)) ≤
      2 + B * ((if j.val = p then 1 else 0) + (if j.val = q then 1 else 0)) := by
    have hexc : μ.expect (fun ω => histDist (label ω)
        (windowWords a (u ++ c :: (v ++ t)) (j*m) m s)
        (windowWords a (u ++ v ++ d :: t) (j*m) m s)) ≤ B :=
      block_histogram_pairing a F Λ hΛ hF μ label he (.forward u v t c d) (j*m) hs hsm
    by_cases hp : j.val = p
    · refine hexc.trans ?_
      rw [ite_eq_left hp]
      split_ifs <;> linarith
    · by_cases hq : j.val = q
      · refine hexc.trans ?_
        rw [ite_eq_right hp, ite_eq_left hq]
        linarith
      · rw [ite_eq_right hp, ite_eq_right hq]
        simp only [add_zero, mul_zero]
        obtain ⟨zs, hz, hx, hy⟩ := windows_nonexceptional u v t c d hs hsm hp hq
        have hbω (ω : Ω) : histDist (label ω)
            (windowWords a (u ++ c :: (v ++ t)) (j*m) m s)
            (windowWords a (u ++ v ++ d :: t) (j*m) m s) ≤ 2 := by
          have h := histDist_common_sublist_le (label ω) (hx.map (normalizeWord a m))
            (hy.map (normalizeWord a m))
          simp only [List.length_map, length_windows] at h
          have hr : (2:ℝ) * s ≤ 2 * zs.length + 2 := by
            exact_mod_cast (by omega : 2*s ≤ 2*zs.length+2)
          exact h.trans (by linarith)
        simpa using μ.expect_mono hbω
  calc
    _ ≤ ∑ j : Fin b, (2 + B * ((if j.val = p then 1 else 0) + (if j.val = q then 1 else 0))) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = 2*b + B * ((∑ j : Fin b, if j.val=p then (1:ℝ) else 0) +
        (∑ j : Fin b, if j.val=q then (1:ℝ) else 0)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ 2*b + B * (1+1) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add (fin_index_indicator_sum b p) (fin_index_indicator_sum b q)) hB)
    _ = _ := by dsimp [B]; ring

theorem histogram_slide_bound {α Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]
    (a : α) {m s : ℕ} (F : List.Vector α m → ι → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hF : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val)
    (μ : FiniteLaw Ω) (label : Ω → List.Vector α m → Y)
    (he : ∀ u v, μ.event (fun ω => label ω u = label ω v) =
      Real.exp (-partitionRate s * coordDist F u v))
    {x y : List α} (hxy : Slide x y) (b : ℕ) (hs : 1 ≤ s) (hsm : s ≤ m) :
    (∑ j : Fin b, μ.expect (fun ω => histDist (label ω)
      (windowWords a x (j*m) m s) (windowWords a y (j*m) m s))) ≤
      2*b + 32 * Real.log ((s:ℝ)+1) * Λ := by
  cases hxy with
  | forward u v t c d => exact histogram_forward_bound a F Λ hΛ hF μ label he u v t c d b hs hsm
  | backward u v t c d =>
    simp only [histDist_symm (label _)
      (windowWords a (u ++ v ++ d :: t) _ _ _)]
    exact histogram_forward_bound a F Λ hΛ hF μ label he u v t c d b hs hsm

theorem SlidePath.coordDist_le {α ι : Type*} [Fintype ι] {x y : List α} {n : ℕ}
    (h : SlidePath n x y) (F : List α → ι → ℝ) (K : ℝ)
    (hF : ∀ u v, Slide u v → coordDist F u v ≤ K) : coordDist F x y ≤ n*K := by
  induction h with
  | nil => simp [coordDist]
  | @cons n x y z h hs ih =>
    calc
      _ ≤ coordDist F x y + coordDist F y z := coordDist_triangle F x y z
      _ ≤ K + n*K := add_le_add (hF x y h) ih
      _ = _ := by push_cast; ring

end FiniteCircle

end OAI
