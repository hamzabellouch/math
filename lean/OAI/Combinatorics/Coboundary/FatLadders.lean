import Mathlib

namespace OAI

/-!
Balanced chamber weights, fat ladders, degeneracy, and cochain counting.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.FatLadders

section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

inductive Path (F : Finset V → Prop) (s : Finset V) : Finset V → Prop
  | refl : F s → Path F s s
  | step {a : Finset V} (v : V) : Path F s a → v ∉ a → F (insert v a) →
      Path F s (insert v a)

namespace Path
variable {F : Finset V → Prop} {s a : Finset V}
lemma fat (h : Path F s a) : F a := by cases h with | refl h => exact h | step _ _ _ h => exact h
lemma subset (h : Path F s a) : s ⊆ a := by
  induction h with
  | refl _ => exact Finset.Subset.refl _
  | step v _ _ _ ih => exact ih.trans (Finset.subset_insert _ _)
lemma start (h : Path F s a) : F s := by
  induction h with | refl h => exact h | step _ _ _ _ ih => exact ih
end Path

def NoBad (F : Finset V → Prop) (T : Finset V) : Prop :=
  ∀ a ⊆ T, ∀ x ∈ a, ∀ y ∈ a, x ≠ y →
    F (a.erase x) → F (a.erase y) → F ((a.erase x).erase y)

def Minimal (F : Finset V → Prop) (s : Finset V) : Prop :=
  F s ∧ ∀ x ∈ s, ¬ F (s.erase x)

lemma Path.erase_fat {F : Finset V → Prop} {s a T : Finset V}
    (h : Path F s a) (hT : a ⊆ T) (hn : NoBad F T) (x : V) (hx : x ∈ s)
    (he : F (a.erase x)) : F (s.erase x) := by
  induction h with
  | refl _ => exact he
  | @step b v hb hv hf ih =>
    have hxb : x ∈ b := hb.subset hx
    have hvx : v ≠ x := by intro e; subst v; exact hv hxb
    have hfb : F b := hb.fat
    have hsmall : F (b.erase x) := by
      have hh := hn (insert v b) hT v (Finset.mem_insert_self _ _) x
        (Finset.mem_insert_of_mem hxb) hvx (by simpa [Finset.erase_insert hv] using hfb) he
      simpa only [Finset.erase_insert hv] using hh
    exact ih ((Finset.subset_insert v b).trans hT) hsmall

lemma Path.erase_path {F : Finset V → Prop} {s a T : Finset V}
    (h : Path F s a) (hT : a ⊆ T) (hn : NoBad F T) (x : V) (hx : x ∉ s)
    (he : F (a.erase x)) : Path F s (a.erase x) := by
  induction h with
  | refl hf => simpa [Finset.erase_eq_of_notMem hx] using Path.refl hf
  | @step b v hb hv hf ih =>
    by_cases hvx : v = x
    · subst v
      simpa only [Finset.erase_insert hv] using hb
    · by_cases hxb : x ∈ b
      · have hsmall : F (b.erase x) := by
          have hh := hn (insert v b) hT v (Finset.mem_insert_self _ _) x
            (Finset.mem_insert_of_mem hxb) hvx
            (by simpa only [Finset.erase_insert hv] using hb.fat) he
          simpa only [Finset.erase_insert hv] using hh
        have hp := ih ((Finset.subset_insert v b).trans hT) hsmall
        have hv' : v ∉ b.erase x := fun hh => hv (Finset.mem_of_mem_erase hh)
        rw [Finset.erase_insert_of_ne hvx]
        exact Path.step v hp hv' (by simpa only [Finset.erase_insert_of_ne hvx] using he)
      · have hnot : x ∉ insert v b := by simp [hxb,Ne.symm hvx]
        simpa only [Finset.erase_eq_of_notMem hnot] using Path.step v hb hv hf

theorem exchange {F : Finset V → Prop} {s T : Finset V} (hs : Minimal F s)
    (hn : NoBad F T) {x y : V} (hx : x ∈ T) (hy : y ∈ T)
    (hp : Path F s (T.erase x)) (hf : F (T.erase y)) :
    Path F s (T.erase y) := by
  by_cases hxy : x = y
  · simpa only [hxy] using hp
  have he : F ((T.erase x).erase y) := hn T (Finset.Subset.refl _) x hx y hy hxy hp.fat hf
  have hys : y ∉ s := by
    intro h
    exact hs.2 y h (hp.erase_fat (Finset.erase_subset _ _) hn y h he)
  have hr := hp.erase_path (Finset.erase_subset _ _) hn y hys he
  have hxi : x ∉ (T.erase x).erase y := by simp
  have hrep : insert x ((T.erase x).erase y) = T.erase y := by
    rw [Finset.erase_right_comm,Finset.insert_erase]
    exact Finset.mem_erase.mpr ⟨hxy,hx⟩
  rw [← hrep]
  exact Path.step x hr hxi (hrep ▸ hf)

abbrev k := ZMod 2

def indicator (F : Finset V → Prop) (s : Finset V) : k := if F s then 1 else 0

def delta (f : Finset V → k) (s : Finset V) : k := ∑ x ∈ s, f (s.erase x)

lemma path_indicator_le_support {F : Finset V → Prop} {s a : Finset V} :
    indicator (Path F s) a ≠ 0 → indicator F a ≠ 0 := by
  intro h
  simp only [indicator,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] at h ⊢
  exact h.fat

theorem localized_boundary_support {F : Finset V → Prop} {s T : Finset V}
    (hs : Minimal F s) (hn : NoBad F T)
    (hb : delta (indicator (Path F s)) T ≠ 0) :
    delta (indicator F) T ≠ 0 := by
  have hex : ∃ x ∈ T, Path F s (T.erase x) := by
    by_contra h
    push Not at h
    apply hb
    apply Finset.sum_eq_zero
    intro x hx
    simp only [indicator,ite_eq_right (h x hx)]
  obtain ⟨x,hx,hp⟩ := hex
  have he : delta (indicator (Path F s)) T = delta (indicator F) T := by
    apply Finset.sum_congr rfl
    intro y hy
    apply congrArg (fun b : Prop => if b then (1:k) else 0)
    apply propext
    exact ⟨Path.fat, fun hf => exchange hs hn hx hy hp hf⟩
  rwa [← he]

lemma indicator_vanish {F : Finset V → Prop} {s a : Finset V} (h : ¬ s ⊆ a) :
    indicator (Path F s) a = 0 := by
  exact ite_eq_right (fun hp => h hp.subset)

theorem exists_minimal_path (F : Finset V → Prop) (a : Finset V) (ha : F a) :
    ∃ s ⊆ a, Minimal F s ∧ Path F s a := by
  induction a using Finset.strongInductionOn with
  | _ a ih =>
    by_cases h : ∃ x ∈ a, F (a.erase x)
    · obtain ⟨x,hx,hf⟩ := h
      obtain ⟨s,hs,hm,hp⟩ := ih (a.erase x) (Finset.erase_ssubset hx) hf
      refine ⟨s,hs.trans (Finset.erase_subset _ _),hm,?_⟩
      have he : insert x (a.erase x) = a := Finset.insert_erase hx
      have hf' : F (insert x (a.erase x)) := by rwa [he]
      simpa only [he] using Path.step x hp (Finset.notMem_erase _ _) hf'
    · refine ⟨a,Finset.Subset.refl _,⟨ha,?_⟩,Path.refl ha⟩
      intro x hx hf
      exact h ⟨x,hx,hf⟩

lemma minimal_nonempty {F : Finset V → Prop} (hF : ¬ F ∅) {s : Finset V}
    (hs : Minimal F s) : s.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  subst s
  exact hF hs.1

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def level (r : ℕ) : Finset (Finset V) := Finset.univ.powersetCard r
omit [DecidableEq V] in
@[simp] lemma mem_level {r : ℕ} {s : Finset V} : s ∈ level (V:=V) r ↔ s.card = r := by
  simp [level]

def atom (w : Finset V → ℝ) (f : Finset V → k) (s : Finset V) : ℝ :=
  if f s = 0 then 0 else w s

def norm (w : Finset V → ℝ) (r : ℕ) (f : Finset V → k) : ℝ :=
  ∑ s ∈ level r, atom w f s

def starSum (r : ℕ) (s : Finset V) (f : Finset V → ℝ) : ℝ :=
  ∑ t ∈ level r, if s ⊆ t then f t else 0

def starNorm (w : Finset V → ℝ) (r : ℕ) (s : Finset V) (f : Finset V → k) : ℝ :=
  starSum r s (atom w f)

omit [Fintype V] [DecidableEq V] in
lemma atom_nonneg {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (f : Finset V → k) (s) :
    0 ≤ atom w f s := by unfold atom; split_ifs; exact le_rfl; exact hw s
omit [DecidableEq V] in
lemma norm_nonneg {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r) (f : Finset V → k) :
    0 ≤ norm w r f := Finset.sum_nonneg (fun s _ => atom_nonneg hw f s)
lemma starNorm_nonneg {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r s) (f : Finset V → k) :
    0 ≤ starNorm w r s f := by
  apply Finset.sum_nonneg
  intro t ht
  split_ifs
  · exact atom_nonneg hw f t
  · exact le_rfl
omit [Fintype V] [DecidableEq V] in
lemma atom_add_le {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (f g : Finset V → k) (s) :
    atom w (f+g) s ≤ atom w f s + atom w g s := by
  unfold atom
  simp only [Pi.add_apply]
  by_cases hf : f s = 0 <;> by_cases hg : g s = 0 <;> simp [hf,hg]
  split_ifs <;> linarith [hw s]

lemma starNorm_add_le {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r s) (f g : Finset V → k) :
    starNorm w r s (f+g) ≤ starNorm w r s f + starNorm w r s g := by
  rw [starNorm,starNorm,starNorm,starSum,starSum,starSum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  split_ifs
  · exact atom_add_le hw f g t
  · simp

lemma starSum_mono {r : ℕ} {s : Finset V} {f g : Finset V → ℝ}
    (h : ∀ t ∈ level r, s ⊆ t → f t ≤ g t) : starSum r s f ≤ starSum r s g := by
  apply Finset.sum_le_sum
  intro t ht
  split_ifs with hs
  · exact h t ht hs
  · rfl

omit [Fintype V] in
lemma subsets_card_le (S : Finset (Finset V)) (t : Finset V) :
    (S.filter (fun s => s ⊆ t)).card ≤ 2^t.card := by
  rw [← Finset.card_powerset]
  exact Finset.card_le_card (by intro s hs; exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hs).2)

lemma sum_star_le (S : Finset (Finset V)) (r : ℕ) (f : Finset V → ℝ)
    (hf : ∀ t, 0 ≤ f t) :
    (∑ s ∈ S, starSum r s f) ≤ (2:ℝ)^r * ∑ t ∈ level r, f t := by
  unfold starSum
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have he : (∑ s ∈ S, if s ⊆ t then f t else 0) =
      ((S.filter (fun s => s ⊆ t)).card : ℝ) * f t := by
    rw [← Finset.sum_filter]
    simp
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (hf t)
  have hh := subsets_card_le S t
  have hr := mem_level.mp ht
  rw [hr] at hh
  exact_mod_cast hh

omit [Fintype V] in
lemma ladder_difference (w : Finset V → ℝ) (F : Finset V → Prop) (s t : Finset V) :
    atom w (indicator F + indicator (Path F s)) t =
      atom w (indicator F) t - atom w (indicator (Path F s)) t := by
  by_cases hp : Path F s t
  · have hf := hp.fat
    simp [atom,indicator,hp,hf,CharTwo.add_self_eq_zero]
  · by_cases hf : F t <;> simp [atom,indicator,hp,hf]

lemma ladder_star_difference (w : Finset V → ℝ) (F : Finset V → Prop) (r) (s : Finset V) :
    starNorm w r s (indicator F + indicator (Path F s)) =
      starNorm w r s (indicator F) - starNorm w r s (indicator (Path F s)) := by
  unfold starNorm starSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs
  · exact ladder_difference w F s t
  · ring

def minimalFaces (F : Finset V → Prop) : Finset (Finset V) :=
  Finset.univ.filter (Minimal F)

lemma norm_le_ladders {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    (F : Finset V → Prop) (r : ℕ) :
    norm w r (indicator F) ≤ ∑ s ∈ minimalFaces F, starNorm w r s (indicator (Path F s)) := by
  unfold norm starNorm starSum
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hF : F t
  · obtain ⟨s,hst,hs,hp⟩ := exists_minimal_path F t hF
    have hmem : s ∈ minimalFaces F := by simp [minimalFaces,hs]
    calc
      atom w (indicator F) t =
          (if s ⊆ t then atom w (indicator (Path F s)) t else 0) := by simp [atom,indicator,hF,hp,hst]
      _ ≤ ∑ a ∈ minimalFaces F, if a ⊆ t then atom w (indicator (Path F a)) t else 0 := by
        apply Finset.single_le_sum _ hmem
        intro a ha
        split_ifs
        · exact atom_nonneg hw _ _
        · exact le_rfl
  · have hh : atom w (indicator F) t = 0 := by simp [atom,indicator,hF]
    rw [hh]
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact atom_nonneg hw _ _
    · exact le_rfl

def NearMinimal (w : Finset V → ℝ) (r : ℕ) (ε : ℝ) (f : Finset V → k) : Prop :=
  ∀ s : Finset V, s.Nonempty → s.card < r → ∀ b : Finset V → k,
    (∀ t, ¬ s ⊆ t → b t = 0) →
    (1-ε) * starNorm w r s f ≤ starNorm w r s (f + delta b)

def LinkCorrection (w : Finset V → ℝ) (r : ℕ) (C : ℝ) : Prop :=
  ∀ s : Finset V, s.Nonempty → s.card ≤ r → ∀ g : Finset V → k,
    (∀ t, ¬ s ⊆ t → g t = 0) →
    ∃ b : Finset V → k, (∀ t, ¬ s ⊆ t → b t = 0) ∧
      (s.card = r → ∀ t ∈ level r, delta b t = 0) ∧
      starNorm w r s (g + delta b) ≤ C * starNorm w (r+1) s (delta g)

lemma ladder_local_estimate {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} (hF : ¬ F ∅) {r : ℕ} {ε C : ℝ}
    (hε : 0 ≤ ε) (hmin : NearMinimal w r ε (indicator F))
    (hcor : LinkCorrection w r C) {s : Finset V} (hs : Minimal F s) (hr : s.card ≤ r) :
    starNorm w r s (indicator (Path F s)) ≤
      C * starNorm w (r+1) s (delta (indicator (Path F s))) +
        ε * starNorm w r s (indicator F) := by
  let g := indicator (Path F s)
  obtain ⟨b,hb,hbe,hcorr⟩ := hcor s (minimal_nonempty hF hs) hr g
    (fun t ht => indicator_vanish ht)
  have hnear : (1-ε) * starNorm w r s (indicator F) ≤
      starNorm w r s (indicator F + delta b) := by
    rcases lt_or_eq_of_le hr with hlt | heq
    · exact hmin s (minimal_nonempty hF hs) hlt b hb
    · have hd : starNorm w r s (indicator F + delta b) = starNorm w r s (indicator F) := by
        unfold starNorm starSum
        apply Finset.sum_congr rfl
        intro t ht
        simp only [atom,Pi.add_apply,hbe heq t ht,add_zero]
      rw [hd]
      nlinarith [starNorm_nonneg hw r s (indicator F)]
  have hid : indicator F + delta b = (g + delta b) + (indicator F + g) := by
    funext t
    change indicator F t + delta b t = (g t + delta b t) + (indicator F t + g t)
    calc
      _ = (indicator F t + delta b t) + (g t + g t) := by rw [CharTwo.add_self_eq_zero,add_zero]
      _ = _ := by abel
  rw [hid] at hnear
  have hh := starNorm_add_le hw r s (g + delta b) (indicator F + g)
  have hd := ladder_star_difference w F r s
  change starNorm w r s (indicator F + g) = _ at hd
  rw [hd] at hh
  linarith

lemma starNorm_eq_zero_of_card {w : Finset V → ℝ} {r : ℕ} {s : Finset V}
    (hr : r < s.card) (f : Finset V → k) : starNorm w r s f = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  have hn : ¬ s ⊆ t := by intro h; have := Finset.card_le_card h; have := mem_level.mp ht; omega
  exact ite_eq_right hn

lemma boundary_star_estimate {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} {s : Finset V} (hs : Minimal F s) (r : ℕ) :
    starNorm w (r+1) s (delta (indicator (Path F s))) ≤
      starNorm w (r+1) s (delta (indicator F)) +
        starNorm w (r+1) s (indicator (fun T => ¬ NoBad F T)) := by
  unfold starNorm starSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hst : s ⊆ t
  · simp only [ite_eq_left hst]
    by_cases hd : delta (indicator (Path F s)) t = 0
    · simp only [atom,hd]
      split_ifs <;> linarith [hw t]
    · by_cases hn : NoBad F t
      · have hh := localized_boundary_support hs hn hd
        simp only [atom,ite_eq_right hd,ite_eq_right hh]
        exact le_add_of_nonneg_right (by split_ifs <;> linarith [hw t])
      · simp only [atom,ite_eq_right hd,indicator,ite_eq_left hn,one_ne_zero,ite_false]
        exact le_add_of_nonneg_left (by split_ifs <;> linarith [hw t])
  · simp only [ite_eq_right hst,add_zero,le_refl]

theorem fat_ladder_inequality {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} (hF : ¬ F ∅) {r : ℕ} {ε C : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hmin : NearMinimal w r ε (indicator F))
    (hcor : LinkCorrection w r C) :
    (1 - ε*(2:ℝ)^r) * norm w r (indicator F) ≤
       C*(2:ℝ)^(r+1) * (norm w (r+1) (delta (indicator F)) +
         norm w (r+1) (indicator (fun T => ¬ NoBad F T))) := by
  let S := minimalFaces F
  have hloc (s : Finset V) (hs : s ∈ S) :
      starNorm w r s (indicator (Path F s)) ≤
        C * starNorm w (r+1) s (delta (indicator (Path F s))) +
          ε * starNorm w r s (indicator F) := by
    have hsm : Minimal F s := (Finset.mem_filter.mp hs).2
    by_cases hr : s.card ≤ r
    · exact ladder_local_estimate hw hF hε hmin hcor hsm hr
    · rw [starNorm_eq_zero_of_card (lt_of_not_ge hr)]
      exact add_nonneg (mul_nonneg hC (starNorm_nonneg hw _ _ _))
        (mul_nonneg hε (starNorm_nonneg hw _ _ _))
  have hlocsum := Finset.sum_le_sum hloc
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum] at hlocsum
  have hb : (∑ s ∈ S, starNorm w (r+1) s (delta (indicator (Path F s)))) ≤
      (2:ℝ)^(r+1) * (norm w (r+1) (delta (indicator F)) +
        norm w (r+1) (indicator (fun T => ¬ NoBad F T))) := by
    calc
      _ ≤ (∑ s ∈ S, ( starNorm w (r+1) s (delta (indicator F)) +
          starNorm w (r+1) s (indicator (fun T => ¬ NoBad F T)))) := by
        apply Finset.sum_le_sum
        intro s hs
        exact boundary_star_estimate hw (Finset.mem_filter.mp hs).2 r
      _ = (∑ s ∈ S, starNorm w (r+1) s (delta (indicator F))) +
          (∑ s ∈ S, starNorm w (r+1) s (indicator (fun T => ¬ NoBad F T))) := Finset.sum_add_distrib
      _ ≤ (2:ℝ)^(r+1) * norm w (r+1) (delta (indicator F)) +
          (2:ℝ)^(r+1) * norm w (r+1) (indicator (fun T => ¬ NoBad F T)) :=
        add_le_add (sum_star_le S (r+1) _ (atom_nonneg hw _))
          (sum_star_le S (r+1) _ (atom_nonneg hw _))
      _ = _ := by ring
  have hf : (∑ s ∈ S, starNorm w r s (indicator F)) ≤ (2:ℝ)^r * norm w r (indicator F) :=
    sum_star_le S r _ (atom_nonneg hw _)
  have hcover := norm_le_ladders hw F r
  change norm w r (indicator F) ≤ ∑ s ∈ S, starNorm w r s (indicator (Path F s)) at hcover
  have htotal := hcover.trans (hlocsum.trans
    (add_le_add (mul_le_mul_of_nonneg_left hb hC) (mul_le_mul_of_nonneg_left hf hε)))
  nlinarith

theorem small_set_expansion {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} (hF : ¬ F ∅) {r : ℕ} {ε C : ℝ}
    (hε : 0 ≤ ε) (hC : 0 < C) (hεsmall : ε*(2:ℝ)^r ≤ 1/2)
    (hmin : NearMinimal w r ε (indicator F)) (hcor : LinkCorrection w r C)
    (hbad : C*(2:ℝ)^(r+1) * norm w (r+1) (indicator (fun T => ¬ NoBad F T)) ≤
      (1/4:ℝ) * norm w r (indicator F)) :
    (1/4:ℝ) * norm w r (indicator F) ≤ C*(2:ℝ)^(r+1) *
      norm w (r+1) (delta (indicator F)) := by
  have h := fat_ladder_inequality hw hF hε hC.le hmin hcor
  have hf := norm_nonneg hw r (indicator F)
  have he := mul_le_mul_of_nonneg_right hεsmall hf
  nlinarith

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def chamberWeight {A : Type*} [Fintype A] (c : A → Finset V) (μ : A → ℝ)
    (s : Finset V) : ℝ := ∑ a, if s ⊆ c a then μ a else 0

omit [Fintype V] in
lemma chamberWeight_nonneg {A : Type*} [Fintype A] (c : A → Finset V) (μ : A → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (s) : 0 ≤ chamberWeight c μ s := by
  apply Finset.sum_nonneg
  intro a ha
  split_ifs
  · exact hμ a
  · rfl

omit [Fintype V] in
lemma chamberWeight_mono {A : Type*} [Fintype A] (c : A → Finset V) (μ : A → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) {s t : Finset V} (hst : s ⊆ t) :
    chamberWeight c μ t ≤ chamberWeight c μ s := by
  apply Finset.sum_le_sum
  intro a ha
  by_cases ht : t ⊆ c a
  · simp only [ite_eq_left ht,ite_eq_left (hst.trans ht),le_refl]
  · simp only [ite_eq_right ht]
    split_ifs
    · exact hμ a
    · rfl

lemma count_cofaces (s t : Finset V) (R : ℕ) (hsR : s.card ≤ R) :
    ∑ u ∈ level R, (if s ⊆ u ∧ u ⊆ t then (1:ℝ) else 0) =
      if s ⊆ t then (Nat.choose (t.card-s.card) (R-s.card):ℝ) else 0 := by
  by_cases hst : s ⊆ t
  · rw [ite_eq_left hst,← Finset.sum_filter]
    have he : (level R).filter (fun u => s ⊆ u ∧ u ⊆ t) =
        (t.powersetCard R).filter (s ⊆ ·) := by
      ext u
      simp only [Finset.mem_filter,mem_level,Finset.mem_powersetCard]
      tauto
    rw [he]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    exact_mod_cast Finset.card_filter_powersetCard_subset s t R hst hsR
  · rw [ite_eq_right hst]
    apply Finset.sum_eq_zero
    intro u hu
    exact ite_eq_right (fun hh => hst (hh.1.trans hh.2))

theorem chamberWeight_balance {A : Type*} [Fintype A]
    (c : A → Finset V) (μ : A → ℝ) (N : ℕ) (hc : ∀ a, (c a).card = N)
    (s : Finset V) (R : ℕ) (hsR : s.card ≤ R) :
    starSum R s (chamberWeight c μ) =
      (Nat.choose (N-s.card) (R-s.card):ℝ) * chamberWeight c μ s := by
  unfold starSum chamberWeight
  simp_rw [Finset.mul_sum]
  have he (t : Finset V) :
      (if s ⊆ t then ∑ a, if t ⊆ c a then μ a else 0 else 0) =
        ∑ a, if s ⊆ t ∧ t ⊆ c a then μ a else 0 := by
    by_cases h : s ⊆ t <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have he' : (∑ t ∈ level R, if s ⊆ t ∧ t ⊆ c a then μ a else 0) =
      (∑ t ∈ level R, if s ⊆ t ∧ t ⊆ c a then (1:ℝ) else 0) * μ a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> ring
  rw [he',count_cofaces s (c a) R hsR,hc a]
  split_ifs <;> ring

structure Balanced (w : Finset V → ℝ) (N : ℕ) : Prop where
  nonneg : ∀ s, 0 ≤ w s
  vanish : ∀ s, N < s.card → w s = 0
  balance : ∀ s R, s.card ≤ R → starSum R s w =
    (Nat.choose (N-s.card) (R-s.card):ℝ)*w s

lemma chamberWeight_balanced {A : Type*} [Fintype A]
    (c : A → Finset V) (μ : A → ℝ) (N : ℕ) (hc : ∀ a, (c a).card = N)
    (hμ : ∀ a, 0 ≤ μ a) : Balanced (chamberWeight c μ) N := by
  refine ⟨chamberWeight_nonneg c μ hμ,?_,chamberWeight_balance c μ N hc⟩
  intro s hs
  apply Finset.sum_eq_zero
  intro a ha
  exact ite_eq_right (by intro h; have := Finset.card_le_card h; rw [hc a] at this; omega)

lemma choose_le_two_pow (n k : ℕ) : (Nat.choose n k : ℝ) ≤ (2:ℝ)^n := by
  exact_mod_cast Nat.choose_le_two_pow n k

lemma Balanced.star_le {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    (s : Finset V) (R : ℕ) : starSum R s w ≤ (2:ℝ)^N * w s := by
  by_cases hs : s.card ≤ R
  · rw [hw.balance s R hs]
    apply mul_le_mul_of_nonneg_right _ (hw.nonneg s)
    exact (choose_le_two_pow _ _).trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
  · have he : starSum R s w = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      exact ite_eq_right (by intro h; have := Finset.card_le_card h; have := mem_level.mp ht; omega)
    rw [he]
    exact mul_nonneg (by positivity) (hw.nonneg s)

lemma Balanced.weight_eq_zero_of_base {w : Finset V → ℝ} {N : ℕ} (hw : Balanced w N)
    {s t : Finset V} (hst : s ⊆ t) (hs : w s = 0) : w t = 0 := by
  have hle : w t ≤ starSum t.card s w := by
    calc
      w t = (if s ⊆ t then w t else 0) := (ite_eq_left hst).symm
      _ ≤ starSum t.card s w := by
        unfold starSum
        apply Finset.single_le_sum (a := t) (f := fun u : Finset V => if s ⊆ u then w u else 0) _ (mem_level.mpr rfl)
        intro u hu
        split_ifs
        · exact hw.nonneg u
        · rfl
  rw [hw.balance s t.card (Finset.card_le_card hst),hs,mul_zero] at hle
  exact le_antisymm hle (hw.nonneg t)

lemma sum_children (f : Finset V → ℝ) (j : ℕ) :
    (∑ s ∈ level j, starSum (j+1) s f) =
      (j+1:ℝ) * ∑ t ∈ level (j+1), f t := by
  unfold starSum
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have he : (level j).filter (fun s => s ⊆ t) = t.powersetCard j := by
    ext s
    simp only [Finset.mem_filter,mem_level,Finset.mem_powersetCard]
    tauto
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,he,Finset.card_powersetCard]
  have htc := mem_level.mp ht
  rw [htc,Nat.choose_succ_self_right]
  push_cast
  rfl

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def Collision (F : Finset V → Prop) (s a : Finset V) : Prop :=
  ∃ x ∈ a, ∃ y ∈ a, x ≠ y ∧ (a.erase x).erase y = s ∧
    F (a.erase x) ∧ F (a.erase y)

omit [Fintype V] in
lemma Collision.card {F : Finset V → Prop} {s a : Finset V}
    (h : Collision F s a) : a.card = s.card+2 := by
  obtain ⟨x,hx,y,hy,hxy,he,hfx,hfy⟩ := h
  subst s
  have hye : y ∈ a.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy,hy⟩
  rw [Finset.card_erase_of_mem hye,Finset.card_erase_of_mem hx]
  have hh := Finset.one_le_card.mpr ⟨y,hye⟩
  rw [Finset.card_erase_of_mem hx] at hh
  omega

omit [Fintype V] in
lemma Collision.base_lt {F : Finset V → Prop} {r : ℕ}
    (hcap : ∀ a, F a → a.card ≤ r) {s a : Finset V}
    (h : Collision F s a) : s.card < r := by
  have hc := h.card
  obtain ⟨x,hx,y,hy,hxy,he,hfx,hfy⟩ := h
  have hf := hcap _ hfx
  rw [Finset.card_erase_of_mem hx] at hf
  omega

def collisionMass (w : Finset V → ℝ) (F : Finset V → Prop) (s : Finset V) : ℝ :=
  ∑ a ∈ level (s.card+2), if Collision F s a then w a else 0

def thinBases (F : Finset V → Prop) (r : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun s => s.card < r ∧ ¬ F s)

lemma collisionMass_nonneg {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    (F : Finset V → Prop) (s) : 0 ≤ collisionMass w F s := by
  apply Finset.sum_nonneg
  intro a ha
  split_ifs
  · exact hw a
  · rfl

lemma bad_face_cover {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    {F : Finset V → Prop} {r : ℕ} (hcap : ∀ a, F a → a.card ≤ r) (T : Finset V) :
    atom w (indicator (fun T => ¬ NoBad F T)) T ≤
      ∑ s ∈ thinBases F r, ∑ a ∈ level (s.card+2),
        if Collision F s a ∧ a ⊆ T then w T else 0 := by
  have hn (s : Finset V) : 0 ≤ ∑ a ∈ level (s.card+2),
        if Collision F s a ∧ a ⊆ T then w T else 0 := by
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact hw T
    · rfl
  by_cases hbad : ¬ NoBad F T
  · have h := hbad
    unfold NoBad at h
    push Not at h
    obtain ⟨a,ha,x,hx,y,hy,hxy,hfx,hfy,hthin⟩ := h
    let s := (a.erase x).erase y
    have hcol : Collision F s a := ⟨x,hx,y,hy,hxy,rfl,hfx,hfy⟩
    have hs : s ∈ thinBases F r := by
      simp only [thinBases,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hcol.base_lt hcap,hthin⟩
    have hle : w T ≤ ∑ b ∈ level (s.card+2),
        if Collision F s b ∧ b ⊆ T then w T else 0 := by
      calc
        w T = (if Collision F s a ∧ a ⊆ T then w T else 0) := (ite_eq_left ⟨hcol,ha⟩).symm
        _ ≤ _ := by
          apply Finset.single_le_sum (a := a) _ (mem_level.mpr hcol.card)
          intro b hb
          split_ifs
          · exact hw T
          · rfl
    simp only [atom,indicator,ite_eq_left hbad,one_ne_zero,ite_false]
    exact hle.trans (Finset.single_le_sum (fun s _ => hn s) hs)
  · simp only [atom,indicator,ite_eq_right hbad,ite_true]
    exact Finset.sum_nonneg (fun s _ => hn s)

theorem bad_mass_le {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    {F : Finset V → Prop} (hcap : ∀ a, F a → a.card ≤ r) (R : ℕ) :
    norm w R (indicator (fun T => ¬ NoBad F T)) ≤
      (2:ℝ)^N * ∑ s ∈ thinBases F r, collisionMass w F s := by
  calc
    _ ≤ ∑ T ∈ level R, ∑ s ∈ thinBases F r, ∑ a ∈ level (s.card+2),
        if Collision F s a ∧ a ⊆ T then w T else 0 :=
      Finset.sum_le_sum (fun T hT => bad_face_cover hw.nonneg hcap T)
    _ = ∑ s ∈ thinBases F r, ∑ a ∈ level (s.card+2),
        if Collision F s a then starSum R a w else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hcol : Collision F s a <;> simp [hcol,starSum]
    _ ≤ (2:ℝ)^N * ∑ s ∈ thinBases F r, collisionMass w F s := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s hs
      unfold collisionMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      by_cases hcol : Collision F s a
      · simp only [ite_eq_left hcol]
        exact hw.star_le a R
      · simp only [ite_eq_right hcol,mul_zero,le_refl]

omit [DecidableEq V] in
lemma level_eq_filter (j : ℕ) : level (V:=V) j = Finset.univ.filter (fun s => s.card = j) := by
  ext s
  simp

omit [DecidableEq V] in
lemma sum_thinBases (F : Finset V → Prop) (r : ℕ) (f : Finset V → ℝ) :
    (∑ s ∈ thinBases F r, f s) =
      ∑ j ∈ Finset.range r, ∑ s ∈ level j, if F s then 0 else f s := by
  unfold thinBases
  rw [Finset.sum_filter]
  simp_rw [level_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hf : F s
  · simp [hf]
  · simp [hf]

theorem degeneracy_estimate {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hrN : r ≤ N) {F : Finset V → Prop} (hcap : ∀ a, F a → a.card ≤ r)
    (θ : ℕ → ℝ) (lam : ℝ) (hθ : ∀ j < r, 0 ≤ θ j+lam)
    (hpair : ∀ s, s.card < r → ¬ F s →
      collisionMass w F s ≤ (θ s.card+lam)*(N:ℝ)*
        starNorm w (s.card+1) s (indicator F)) (R : ℕ) :
    norm w R (indicator (fun T => ¬NoBad F T)) ≤
      (2:ℝ)^N * (N:ℝ)^2 *
        ∑ j ∈ Finset.range r, (θ j+lam)*norm w (j+1) (indicator F) := by
  apply (bad_mass_le hw hcap R).trans
  rw [sum_thinBases]
  have hsum : (∑ j ∈ Finset.range r, ∑ s ∈ level j,
      if F s then 0 else collisionMass w F s) ≤
      (N:ℝ)^2 * ∑ j ∈ Finset.range r, (θ j+lam)*norm w (j+1) (indicator F) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjr := Finset.mem_range.mp hj
    have hc : 0 ≤ (θ j+lam)*(N:ℝ) := mul_nonneg (hθ j hjr) (Nat.cast_nonneg N)
    calc
      _ ≤ ∑ s ∈ level j, (θ j+lam)*(N:ℝ)*starNorm w (j+1) s (indicator F) := by
        apply Finset.sum_le_sum
        intro s hs
        have he := mem_level.mp hs
        by_cases hf : F s
        · rw [ite_eq_left hf]
          exact mul_nonneg hc (starNorm_nonneg hw.nonneg _ _ _)
        · rw [ite_eq_right hf]
          simpa only [he] using hpair s (by omega) hf
      _ = (θ j+lam)*(N:ℝ)*(j+1:ℝ)*norm w (j+1) (indicator F) := by
        rw [← Finset.mul_sum]
        change (θ j+lam)*(N:ℝ)*(∑ s ∈ level j, starSum (j+1) s (atom w (indicator F))) = _
        rw [sum_children]
        simp only [norm,mul_assoc]
      _ ≤ (N:ℝ)^2*((θ j+lam)*norm w (j+1) (indicator F)) := by
        have hjN : (j+1:ℝ) ≤ N := by exact_mod_cast (show j+1 ≤ N by omega)
        have hn := norm_nonneg hw.nonneg (j+1) (indicator F)
        nlinarith [mul_le_mul_of_nonneg_left hjN (mul_nonneg hc hn)]
  have h := mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ 2^N by positivity)
  simpa only [mul_assoc] using h

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq V] in
@[simp] lemma atom_indicator (w : Finset V → ℝ) (F : Finset V → Prop) (s : Finset V) :
    atom w (indicator F) s = if F s then w s else 0 := by
  by_cases h : F s <;> simp [atom,indicator,h]

def fatAt (w : Finset V → ℝ) (N : ℕ) (θ : ℕ → ℝ) (f : Finset V → k) :
    ℕ → Finset V → Prop
  | 0, s => f s ≠ 0 ∧ 0 < w s
  | k+1, s => 0 < w s ∧ θ s.card * (N-s.card:ℕ) * w s ≤
      starNorm w (s.card+1) s (indicator (fatAt w N θ f k))

def fatFamily (w : Finset V → ℝ) (N r : ℕ) (θ : ℕ → ℝ) (f : Finset V → k)
    (s : Finset V) : Prop := s.card ≤ r ∧ fatAt w N θ f (r-s.card) s

lemma fatFamily_cap (w : Finset V → ℝ) (N r : ℕ) (θ : ℕ → ℝ) (f : Finset V → k) :
    ∀ s, fatFamily w N r θ f s → s.card ≤ r := fun _ h => h.1

lemma fatFamily_recurrence (w : Finset V → ℝ) (N r : ℕ) (θ : ℕ → ℝ)
    (f : Finset V → k) (s : Finset V) (hs : s.card < r) :
    fatFamily w N r θ f s ↔ 0 < w s ∧
      θ s.card * (N-s.card:ℕ) * w s ≤
        starNorm w (s.card+1) s (indicator (fatFamily w N r θ f)) := by
  have he : r-s.card = (r-s.card-1)+1 := by omega
  have hh : starNorm w (s.card+1) s (indicator (fatAt w N θ f (r-s.card-1))) =
      starNorm w (s.card+1) s (indicator (fatFamily w N r θ f)) := by
    unfold starNorm starSum
    apply Finset.sum_congr rfl
    intro t ht
    have htc := mem_level.mp ht
    have htr : t.card ≤ r := by omega
    have hidx : r-t.card = r-s.card-1 := by omega
    simp only [atom_indicator,fatFamily,htr,true_and,hidx]
  unfold fatFamily
  rw [he]
  simp only [fatAt,show s.card ≤ r from hs.le,true_and]
  rw [hh]
  rfl

lemma fatFamily_top_norm {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s)
    (N r : ℕ) (θ : ℕ → ℝ) (f : Finset V → k) :
    norm w r (indicator (fatFamily w N r θ f)) = norm w r f := by
  apply Finset.sum_congr rfl
  intro s hs
  have hc := mem_level.mp hs
  simp only [atom_indicator,fatFamily,hc,Nat.sub_self,le_refl,true_and,fatAt]
  by_cases hf : f s = 0
  · simp [hf,atom]
  · by_cases hp : 0 < w s
    · simp [hf,hp,atom]
    · have hz : w s = 0 := le_antisymm (le_of_not_gt hp) (hw s)
      simp [hz,atom]

theorem fat_markov {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hrN : r ≤ N) (θ : ℕ → ℝ) (hθ : ∀ j < r, 0 ≤ θ j)
    (f : Finset V → k) (j : ℕ) (hj : j < r) :
    θ j * norm w j (indicator (fatFamily w N r θ f)) ≤
      (N:ℝ) * norm w (j+1) (indicator (fatFamily w N r θ f)) := by
  let F := fatFamily w N r θ f
  have hlocal (s : Finset V) (hs : s ∈ level j) :
      θ j * (N-j:ℕ) * atom w (indicator F) s ≤
        starNorm w (j+1) s (indicator F) := by
    have he := mem_level.mp hs
    by_cases hf : F s
    · have h := (fatFamily_recurrence w N r θ f s (by omega)).mp hf
      simpa only [atom_indicator,ite_eq_left hf,he] using h.2
    · simp only [atom_indicator,ite_eq_right hf,mul_zero]
      exact starNorm_nonneg hw.nonneg _ _ _
  have hsum := Finset.sum_le_sum hlocal
  simp only [← Finset.mul_sum] at hsum
  change θ j * (N-j:ℕ) * norm w j (indicator F) ≤
    ∑ s ∈ level j, starSum (j+1) s (atom w (indicator F)) at hsum
  rw [sum_children] at hsum
  change θ j * (N-j:ℕ) * norm w j (indicator F) ≤
    (j+1:ℝ)*norm w (j+1) (indicator F) at hsum
  have hn := norm_nonneg hw.nonneg j (indicator F)
  have hn' := norm_nonneg hw.nonneg (j+1) (indicator F)
  have hnj : (1:ℝ) ≤ (N-j:ℕ) := by exact_mod_cast (show 1 ≤ N-j by omega)
  have hjN : (j+1:ℝ) ≤ N := by exact_mod_cast (show j+1 ≤ N by omega)
  have hleft := mul_le_mul_of_nonneg_right hnj (mul_nonneg (hθ j hj) hn)
  have hright := mul_le_mul_of_nonneg_right hjN hn'
  change θ j * norm w j (indicator F) ≤ _
  nlinarith

def fatBudget (N : ℕ) (η : ℝ) : ℕ → ℝ
  | 0 => 1
  | k+1 => (N:ℝ) * (fatBudget N η k)^2 / η

lemma fatBudget_pos {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    0 < fatBudget N η k := by
  induction k with
  | zero => norm_num [fatBudget]
  | succ k ih => simp only [fatBudget]; positivity

def fatThreshold (N r : ℕ) (η : ℝ) (j : ℕ) : ℝ := η / fatBudget N η (r-j-1)

lemma fatThreshold_pos {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) (r j : ℕ) :
    0 < fatThreshold N r η j := div_pos hη (fatBudget_pos hN hη _)

theorem fat_mass_bound {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) {η : ℝ} (hη : 0 < η) (f : Finset V → k)
    (a : ℕ) (ha : a ≤ r) :
    norm w (r-a) (indicator (fatFamily w N r (fatThreshold N r η) f)) ≤
      fatBudget N η a * norm w r f := by
  let θ := fatThreshold N r η
  let F := fatFamily w N r θ f
  induction a with
  | zero =>
      simp only [Nat.sub_zero,fatBudget,one_mul]
      exact le_of_eq (fatFamily_top_norm hw.nonneg N r θ f)
  | succ a ih =>
      have har : a ≤ r := by omega
      have hi := ih har
      have hj : r-(a+1) < r := by omega
      have ht : θ (r-(a+1)) = η / fatBudget N η a := by
        unfold θ fatThreshold
        congr 2
        omega
      have hidx : r-(a+1)+1 = r-a := by omega
      have hm := fat_markov hw hrN θ (fun j _ => (fatThreshold_pos hN hη r j).le) f _ hj
      change θ (r-(a+1))*norm w (r-(a+1)) (indicator F) ≤
        (N:ℝ)*norm w (r-(a+1)+1) (indicator F) at hm
      rw [ht,hidx] at hm
      have hb := fatBudget_pos hN hη a
      have hh := hm.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg N))
      have hdiv : 0 < η / fatBudget N η a := div_pos hη hb
      have hh' : norm w (r-(a+1)) (indicator F) ≤
          (N:ℝ)*(fatBudget N η a*norm w r f)/(η/fatBudget N η a) :=
        (le_div_iff₀ hdiv).mpr (by simpa only [mul_comm] using hh)
      calc
        _ ≤ (N:ℝ) * (fatBudget N η a * norm w r f) / (η / fatBudget N η a) := hh'
        _ = fatBudget N η (a+1)*norm w r f := by
          simp only [fatBudget]
          field_simp

lemma fat_empty_false {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) (hw0 : w ∅ = 1) {η : ℝ} (hη : 0 < η)
    (f : Finset V → k) (hf : norm w r f < 1 / fatBudget N η r) :
    ¬ fatFamily w N r (fatThreshold N r η) f ∅ := by
  intro hF
  have hm := fat_mass_bound hw hN hrN hη f r le_rfl
  have he : norm w 0 (indicator (fatFamily w N r (fatThreshold N r η) f)) = 1 := by
    simp [norm,level,atom_indicator,hF,hw0]
  rw [Nat.sub_self,he] at hm
  have hb := fatBudget_pos hN hη r
  have hlt := (lt_div_iff₀ hb).mp hf
  nlinarith

end

variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq V] in
lemma atom_le_weight {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (f : Finset V → k) (s) :
    atom w f s ≤ w s := by unfold atom; split_ifs; exact hw s; rfl

lemma starNorm_le_starSum {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r s) (f : Finset V → k) :
    starNorm w r s f ≤ starSum r s w := starSum_mono (fun _ _ _ => atom_le_weight hw f _)

def LocalMixing (w : Finset V → ℝ) (N : ℕ) (lam : ℝ) : Prop :=
  ∀ (F : Finset V → Prop) (s : Finset V), s.card < N → ∀ t : ℝ, 0 ≤ t →
    starNorm w (s.card+1) s (indicator F) ≤ t*(N-s.card:ℕ)*w s →
    collisionMass w F s ≤ (t+lam)*(N:ℝ)*starNorm w (s.card+1) s (indicator F)

lemma fat_thin_children {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (θ : ℕ → ℝ) (f : Finset V → k) (s : Finset V) (hs : s.card < r)
    (hf : ¬ fatFamily w N r θ f s) :
    starNorm w (s.card+1) s (indicator (fatFamily w N r θ f)) ≤
      θ s.card * (N-s.card:ℕ) * w s := by
  by_cases hp : 0 < w s
  · have hn : ¬ θ s.card * (N-s.card:ℕ) * w s ≤
        starNorm w (s.card+1) s (indicator (fatFamily w N r θ f)) := by
      intro h
      exact hf ((fatFamily_recurrence w N r θ f s hs).mpr ⟨hp,h⟩)
    exact (lt_of_not_ge hn).le
  · have hz : w s = 0 := le_antisymm (le_of_not_gt hp) (hw.nonneg s)
    have hh := starNorm_le_starSum hw.nonneg (s.card+1) s
      (indicator (fatFamily w N r θ f))
    rw [hw.balance s (s.card+1) (by omega),hz,mul_zero] at hh
    simpa only [hz,mul_zero] using hh

theorem fat_degeneracy_bound {w : Finset V → ℝ} {N r : ℕ} (hw : Balanced w N)
    (hN : 0 < N) (hrN : r ≤ N) {η lam : ℝ} (hη : 0 < η) (hlam : 0 ≤ lam)
    (hbudget : ∀ a ≤ r, lam * fatBudget N η a ≤ η)
    (hmix : LocalMixing w N lam) (f : Finset V → k) (R : ℕ) :
    norm w R (indicator (fun T => ¬NoBad (fatFamily w N r (fatThreshold N r η) f) T)) ≤
      (2:ℝ)^N * (N:ℝ)^2 * (r:ℝ) * (2*η) * norm w r f := by
  let θ := fatThreshold N r η
  let F := fatFamily w N r θ f
  have hpair : ∀ s, s.card < r → ¬F s → collisionMass w F s ≤
      (θ s.card+lam)*(N:ℝ)*starNorm w (s.card+1) s (indicator F) := by
    intro s hs hf
    exact hmix F s (by omega) (θ s.card) (fatThreshold_pos hN hη r s.card).le
      (fat_thin_children hw θ f s hs hf)
  have hd := degeneracy_estimate hw hrN (fatFamily_cap w N r θ f) θ lam
    (fun j _ => add_nonneg (fatThreshold_pos hN hη r j).le hlam) hpair R
  have hs : (∑ j ∈ Finset.range r, (θ j+lam)*norm w (j+1) (indicator F)) ≤
      (r:ℝ)*(2*η)*norm w r f := by
    calc
      _ ≤ ∑ j ∈ Finset.range r, (2*η)*norm w r f := by
        apply Finset.sum_le_sum
        intro j hj
        have hjr := Finset.mem_range.mp hj
        have hidx : r-(r-j-1) = j+1 := by omega
        have hb := fatBudget_pos hN hη (r-j-1)
        have hm := fat_mass_bound hw hN hrN hη f (r-j-1) (by omega)
        rw [hidx] at hm
        have hθlam : 0 ≤ θ j+lam := add_nonneg (fatThreshold_pos hN hη r j).le hlam
        calc
          (θ j+lam)*norm w (j+1) (indicator F) ≤
              (θ j+lam)*(fatBudget N η (r-j-1)*norm w r f) :=
            mul_le_mul_of_nonneg_left hm hθlam
          _ = (η+lam*fatBudget N η (r-j-1))*norm w r f := by
            unfold θ fatThreshold
            field_simp
          _ ≤ (2*η)*norm w r f := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg hw.nonneg r f)
            linarith [hbudget (r-j-1) (by omega)]
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
  have hmult := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ 2^N*(N:ℝ)^2 by positivity)
  exact hd.trans (by simpa only [mul_assoc] using hmult)

theorem exists_mixing_tolerance (N r : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ a ≤ r, lam*fatBudget N η a ≤ η := by
  let S := ∑ a ∈ Finset.range (r+1), fatBudget N η a
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a _ => (fatBudget_pos hN hη a).le)
  have hden : 0 < 1+S := by linarith
  refine ⟨η/(1+S),div_pos hη hden,?_⟩
  intro a ha
  have hle : fatBudget N η a ≤ S := Finset.single_le_sum
    (fun b _ => (fatBudget_pos hN hη b).le) (Finset.mem_range.mpr (by omega))
  have hh : fatBudget N η a ≤ 1+S := by linarith
  calc
    η/(1+S)*fatBudget N η a ≤ η/(1+S)*(1+S) :=
      mul_le_mul_of_nonneg_left hh (div_pos hη hden).le
    _ = η := div_mul_cancel₀ η (ne_of_gt hden)

end CoboundaryExpanders.FatLadders

end

end OAI
