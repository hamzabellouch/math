import Mathlib

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.FiniteAntiConcentration
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def subsetSum (w : ι → ℝ) (s : Finset ι) : ℝ := ∑ i ∈ s, w i

def intervalFamily (w : ι → ℝ) (L U : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter (fun s => L ≤ subsetSum w s ∧ subsetSum w s ≤ U)

omit [Fintype ι] in
theorem subsetSum_increase (w : ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i, δ ≤ w i) {s t : Finset ι} (hst : s ⊂ t) :
    subsetSum w s + δ ≤ subsetSum w t := by
  obtain ⟨i, hit, his⟩ := Finset.exists_of_ssubset hst
  have hd := Finset.single_le_sum (s := t \ s) (f := w)
    (fun j _ => hδ.trans (hw j)) (Finset.mem_sdiff.mpr ⟨hit, his⟩)
  have he := Finset.sum_sdiff (f := w) (Finset.Subset.refl s |>.trans hst.le)
  unfold subsetSum
  linarith [hw i]

theorem interval_card_le (w : ι → ℝ) (L U δ : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hw : ∀ i, δ ≤ w i) (hwide : U - L < N * δ) :
    (intervalFamily w L U).card ≤ N * (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  let bucket : Finset ι → ℕ := fun s => ⌊(subsetSum w s - L) / δ⌋₊
  have hb : ∀ s ∈ intervalFamily w L U, bucket s < N := by
    intro s hs
    have hs' := (Finset.mem_filter.mp hs).2
    apply (Nat.floor_lt (div_nonneg (sub_nonneg.mpr hs'.1) hδ.le)).mpr
    apply (div_lt_iff₀ hδ).mpr
    linarith [hs'.2]
  have hc : ∀ k, ((intervalFamily w L U).filter (fun s => bucket s = k)).card ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
    intro k
    apply IsAntichain.sperner
    intro s hs t ht hne hst
    have hs' := Finset.mem_filter.mp hs
    have ht' := Finset.mem_filter.mp ht
    have hsL := (Finset.mem_filter.mp hs'.1).2.1
    have hi := subsetSum_increase w hδ.le hw
      (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩)
    have hlo := Nat.floor_le (div_nonneg (sub_nonneg.mpr hsL) hδ.le)
    have hhi := Nat.lt_floor_add_one ((subsetSum w t - L) / δ)
    change (bucket s : ℝ) ≤ (subsetSum w s - L) / δ at hlo
    change (subsetSum w t - L) / δ < (bucket t : ℝ) + 1 at hhi
    rw [hs'.2] at hlo
    rw [ht'.2] at hhi
    have hlo' := (le_div_iff₀ hδ).mp hlo
    have hhi' := (div_lt_iff₀ hδ).mp hhi
    nlinarith
  have ht : Set.MapsTo bucket (intervalFamily w L U) (Finset.range N) := by
    intro s hs
    exact Finset.mem_range.mpr (hb s hs)
  rw [Finset.card_eq_sum_card_fiberwise ht]
  calc
    _ ≤ ∑ _k ∈ Finset.range N, (Fintype.card ι).choose (Fintype.card ι / 2) :=
      Finset.sum_le_sum (fun k _ => hc k)
    _ = _ := by simp

def choices (lo hi : ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ i, if i ∈ s then hi i else lo i

theorem choices_eq (lo hi : ι → ℝ) (s : Finset ι) :
    choices lo hi s = (∑ i, lo i) + subsetSum (fun i => hi i - lo i) s := by
  classical
  unfold choices subsetSum
  have hs : (∑ i ∈ s, (hi i - lo i)) = ∑ i, if i ∈ s then hi i - lo i else 0 := by
    symm
    simp
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi'
  by_cases h : i ∈ s <;> simp [h]

theorem choice_card_le (lo hi : ι → ℝ) (L U δ : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hdiff : ∀ i, lo i + δ ≤ hi i) (hwide : U - L < N * δ) :
    (Finset.univ.filter (fun s : Finset ι => L ≤ choices lo hi s ∧ choices lo hi s ≤ U)).card ≤
      N * (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  have he : (Finset.univ.filter (fun s : Finset ι => L ≤ choices lo hi s ∧ choices lo hi s ≤ U)) =
      intervalFamily (fun i => hi i - lo i) (L - ∑ i, lo i) (U - ∑ i, lo i) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, intervalFamily, choices_eq]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he]
  apply interval_card_le _ _ _ δ N hδ (fun i => by linarith [hdiff i])
  linarith

def toggleEquiv (mask : Finset ι) : Finset ι ≃ Finset ι where
  toFun s := symmDiff s mask
  invFun s := symmDiff s mask
  left_inv s := by
    ext i
    simp only [Finset.mem_symmDiff]
    tauto
  right_inv s := by
    ext i
    simp only [Finset.mem_symmDiff]
    tauto

variable {α : Type*} [Fintype α]

def orderedChoice (g : α → ℝ) (τ : α ≃ α) (x : ι → α) (s : Finset ι) : ℝ :=
  choices (fun i => min (g (x i)) (g (τ (x i))))
    (fun i => max (g (x i)) (g (τ (x i)))) s

def rawChoice (g : α → ℝ) (τ : α ≃ α) (x : ι → α) (s : Finset ι) : ℝ :=
  ∑ i, if i ∈ s then g (τ (x i)) else g (x i)

omit [Fintype α] in
theorem orderedChoice_eq (g : α → ℝ) (τ : α ≃ α) (x : ι → α) (s : Finset ι) :
    orderedChoice g τ x s = rawChoice g τ x
      (toggleEquiv (Finset.univ.filter (fun i => g (τ (x i)) < g (x i))) s) := by
  classical
  unfold orderedChoice rawChoice choices toggleEquiv
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : i ∈ s <;> by_cases ho : g (τ (x i)) < g (x i)
  · simp [Finset.mem_symmDiff, hm, ho, max_eq_left ho.le]
  · simp [Finset.mem_symmDiff, hm, ho, max_eq_right (le_of_not_gt ho)]
  · simp [Finset.mem_symmDiff, hm, ho, min_eq_right ho.le]
  · simp [Finset.mem_symmDiff, hm, ho, min_eq_left (le_of_not_gt ho)]

def coordinateShift (τ : α ≃ α) (s : Finset ι) : (ι → α) ≃ (ι → α) :=
  Equiv.piCongrRight (fun i => if i ∈ s then τ else Equiv.refl α)

omit [Fintype α] in
theorem rawChoice_eq (g : α → ℝ) (τ : α ≃ α) (x : ι → α) (s : Finset ι) :
    rawChoice g τ x s = ∑ i, g (coordinateShift τ s x i) := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : i ∈ s <;> simp [coordinateShift, hm]

theorem sum_orderedChoices (g : α → ℝ) (τ : α ≃ α) (f : ℝ → ℝ) :
    (∑ x : ι → α, ∑ s : Finset ι, f (orderedChoice g τ x s)) =
      (2 : ℝ) ^ Fintype.card ι * ∑ x : ι → α, f (∑ i, g (x i)) := by
  classical
  calc
    _ = ∑ x : ι → α, ∑ s : Finset ι, f (rawChoice g τ x s) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [orderedChoice_eq]
      exact (toggleEquiv (Finset.univ.filter (fun i => g (τ (x i)) < g (x i)))).sum_comp (fun s => f (rawChoice g τ x s))
    _ = ∑ s : Finset ι, ∑ x : ι → α, f (rawChoice g τ x s) := Finset.sum_comm
    _ = ∑ _s : Finset ι, ∑ x : ι → α, f (∑ i, g (x i)) := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [rawChoice_eq]
      exact (coordinateShift τ s).sum_comp (fun x => f (∑ i, g (x i)))
    _ = _ := by simp [Fintype.card_finset]

def grid (d : ℕ) (u : Fin (2*d+1)) : ℝ :=
  2 * ((u.val : ℝ) - d) / (2*d+1)

def gridShift (d : ℕ) : Fin (2*d+1) ≃ Fin (2*d+1) :=
  Equiv.addRight ⟨d, by omega⟩

theorem grid_gap (d : ℕ) (u : Fin (2*d+1)) :
    (2*d : ℝ)/(2*d+1) ≤ |grid d (gridShift d u) - grid d u| := by
  have hp : (0 : ℝ) < 2*d+1 := by positivity
  have hv : (gridShift d u).val =
      if 2*d+1 ≤ u.val+d then u.val+d-(2*d+1) else u.val+d := by
    exact Fin.val_add_eq_ite u ⟨d, by omega⟩
  unfold grid
  rw [hv]
  split_ifs with h
  · have hs : ((u.val+d-(2*d+1) : ℕ) : ℝ) = (u.val : ℝ)+d-(2*d+1) := by
      rw [Nat.cast_sub h]
      push_cast
      rfl
    rw [hs]
    have he : 2*((u.val:ℝ)+d-(2*d+1)-d)/(2*d+1) -
        2*((u.val:ℝ)-d)/(2*d+1) = -(2*(d+1)/(2*d+1)) := by ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (by linarith) hp.le
  · push_cast
    have he : 2*((u.val:ℝ)+d-d)/(2*d+1) -
        2*((u.val:ℝ)-d)/(2*d+1) = 2*d/(2*d+1) := by ring
    rw [he, abs_of_nonneg (by positivity)]

theorem grid_ordered_gap (d : ℕ) (u : Fin (2*d+1)) :
    min (grid d u) (grid d (gridShift d u)) + (2*d : ℝ)/(2*d+1) ≤
      max (grid d u) (grid d (gridShift d u)) := by
  have h := grid_gap d u
  rw [← max_sub_min_eq_abs] at h
  linarith

theorem grid_neg (d : ℕ) (u : Fin (2*d+1)) : grid d (Fin.rev u) = - grid d u := by
  unfold grid
  rw [Fin.val_rev, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem grid_interval_card (d n N : ℕ) (hd : 0 < d) (L U : ℝ)
    (hwide : U-L < N * ((2*d : ℝ)/(2*d+1))) :
    (2 : ℝ)^n *
      ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
        L ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ U)).card : ℝ) ≤
    ((2*d+1 : ℕ)^n : ℝ) * N * (n.choose (n/2)) := by
  classical
  let f : ℝ → ℝ := fun y => if L ≤ y ∧ y ≤ U then 1 else 0
  have hlaw := sum_orderedChoices (ι := Fin n) (grid d) (gridShift d) f
  have hc (x : Fin n → Fin (2*d+1)) :
      ∑ s : Finset (Fin n), f (orderedChoice (grid d) (gridShift d) x s) ≤
        (N * n.choose (n/2) : ℕ) := by
    have h := choice_card_le
      (fun i => min (grid d (x i)) (grid d (gridShift d (x i))))
      (fun i => max (grid d (x i)) (grid d (gridShift d (x i))))
      L U ((2*d : ℝ)/(2*d+1)) N
      (by positivity) (fun i => grid_ordered_gap d (x i)) hwide
    have hs : (∑ s : Finset (Fin n), f (orderedChoice (grid d) (gridShift d) x s)) =
        ((Finset.univ.filter (fun s : Finset (Fin n) =>
          L ≤ orderedChoice (grid d) (gridShift d) x s ∧
          orderedChoice (grid d) (gridShift d) x s ≤ U)).card : ℝ) := by
      exact Finset.sum_boole _ _
    rw [hs]
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hc x)
  rw [hlaw] at hs
  have hcount : (∑ x : Fin n → Fin (2*d+1), f (∑ i, grid d (x i))) =
      ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
        L ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ U)).card : ℝ) := by
    exact Finset.sum_boole _ _
  rw [hcount] at hs
  simpa [Fintype.card_fun, mul_assoc] using hs

theorem symmetric_tail_count {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (rev : Ω ≃ Ω) (hrev : ∀ x, f (rev x) = -f x) (t : ℝ) (ht : 0 ≤ t) :
    2 * ((Finset.univ.filter (fun x => t < f x)).card : ℝ) +
      ((Finset.univ.filter (fun x => -t ≤ f x ∧ f x ≤ t)).card : ℝ) = Fintype.card Ω := by
  classical
  let pos : Ω → ℝ := fun x => if t < f x then 1 else 0
  let neg : Ω → ℝ := fun x => if f x < -t then 1 else 0
  let mid : Ω → ℝ := fun x => if -t ≤ f x ∧ f x ≤ t then 1 else 0
  have he (x : Ω) : pos x + neg x + mid x = 1 := by
    dsimp [pos, neg, mid]
    split_ifs <;> simp_all <;> linarith
  have hn : (∑ x, neg x) = ∑ x, pos x := by
    have h : (∑ x, pos (rev x)) = ∑ x, neg x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [pos, neg, hrev, lt_neg]
    rw [← h]
    exact rev.sum_comp pos
  have hs : (∑ x, pos x) + (∑ x, neg x) + (∑ x, mid x) = Fintype.card Ω := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp only [he]
    simp
  rw [hn] at hs
  have hpcount : (∑ x, pos x) = ((Finset.univ.filter (fun x => t < f x)).card : ℝ) :=
    Finset.sum_boole _ _
  have hmcount : (∑ x, mid x) =
      ((Finset.univ.filter (fun x => -t ≤ f x ∧ f x ≤ t)).card : ℝ) :=
    Finset.sum_boole _ _
  rw [hpcount, hmcount] at hs
  linarith

theorem grid_tail_count (d n t : ℕ) :
    2 * ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
      (t : ℝ) < ∑ i, grid d (x i))).card : ℝ) +
    ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
      -(t : ℝ) ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ t)).card : ℝ) =
      ((2*d+1 : ℕ)^n : ℝ) := by
  classical
  have hr (x : Fin n → Fin (2*d+1)) :
      (∑ i, grid d ((Equiv.piCongrRight (fun _ : Fin n => Fin.revPerm)) x i)) =
      -(∑ i, grid d (x i)) := by
    change (∑ i, grid d (Fin.rev (x i))) = -(∑ i, grid d (x i))
    simp only [grid_neg, Finset.sum_neg_distrib]
  simpa [Fintype.card_fun] using symmetric_tail_count
    (fun x : Fin n → Fin (2*d+1) => ∑ i, grid d (x i))
    (Equiv.piCongrRight (fun _ : Fin n => Fin.revPerm)) hr (t : ℝ) (by positivity)

theorem grid_central_card (d n t : ℕ) (ht : t < d) :
    (2 : ℝ)^n *
      ((Finset.univ.filter (fun x : Fin n → Fin (2*d+1) =>
        -(t : ℝ) ≤ ∑ i, grid d (x i) ∧ (∑ i, grid d (x i)) ≤ t)).card : ℝ) ≤
    ((2*d+1 : ℕ)^n : ℝ) * (2*t+1) * (n.choose (n/2) : ℝ) := by
  have htr : (t:ℝ) < d := Nat.cast_lt.mpr ht
  have hwide : (t:ℝ)-(-t) < (2*t+1 : ℕ)*((2*d : ℝ)/(2*d+1)) := by
    push_cast
    rw [mul_div, lt_div_iff₀ (by positivity : (0:ℝ) < 2*d+1)]
    nlinarith
  simpa using grid_interval_card d n (2*t+1) (by omega) (-(t:ℝ)) (t:ℝ) hwide

end
end VertexCover.FiniteAntiConcentration


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
