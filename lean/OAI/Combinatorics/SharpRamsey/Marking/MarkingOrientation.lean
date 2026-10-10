import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.LevelLosses

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Marking

section FinitePotential
variable {Y : Type*} [Fintype Y]

noncomputable def level (r : Y → ℕ) (l : ℕ) : Finset Y := {y | r y = l}
noncomputable def below (r : Y → ℕ) (l : ℕ) : Finset Y := {y | r y ≤ l}
noncomputable def potential (D : ℕ) (r : Y → ℕ) : ℝ :=
  ∑ l ∈ range (D+1), Real.log ((below r l).card + 1 : ℝ)

theorem below_antitone {r r' : Y → ℕ} (h : ∀ y, r y ≤ r' y) (l : ℕ) :
    below r' l ⊆ below r l := by
  intro y hy
  simp only [below, mem_filter, mem_univ, true_and] at *
  exact (h y).trans hy

theorem potential_nonneg (D : ℕ) (r : Y → ℕ) : 0 ≤ potential D r := by
  apply sum_nonneg
  intro l hl
  apply Real.log_nonneg
  exact le_add_of_nonneg_left (Nat.cast_nonneg _)

theorem potential_le (D : ℕ) (r : Y → ℕ) :
    potential D r ≤ (D+1)*Real.log (Fintype.card Y + 1 : ℝ) := by
  calc
    _ ≤ ∑ _l ∈ range (D+1), Real.log (Fintype.card Y + 1 : ℝ) := by
      apply sum_le_sum
      intro l hl
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.add_le_add_right (card_le_univ _) 1
    _ = _ := by simp

theorem log_drop {n m δ : ℝ} (hn : 1 ≤ n) (hm : 0 ≤ m)
    (hδ : 0 ≤ δ) (hdrop : m ≤ n - δ*n) :
    δ/2 ≤ Real.log (n+1) - Real.log (m+1) := by
  have hn0 : 0 < n+1 := by linarith
  have hm0 : 0 < m+1 := by linarith
  have hratio : 0 < (m+1)/(n+1) := div_pos hm0 hn0
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hm0.ne' hn0.ne'] at hlog
  have hfrac : (m+1)/(n+1) ≤ 1-δ/2 := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hn)]
  linarith

theorem potential_drop {D l : ℕ} {r r' : Y → ℕ} {δ : ℝ}
    (hl : l ≤ D) (hmono : ∀ y, r y ≤ r' y)
    (hn : (below r l).Nonempty) (hδ : 0 ≤ δ)
    (hdrop : ((below r' l).card : ℝ) ≤ (below r l).card - δ*(below r l).card) :
    δ/2 ≤ potential D r - potential D r' := by
  have hle i : Real.log ((below r' i).card + 1 : ℝ) ≤
      Real.log ((below r i).card + 1 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right (card_le_card (below_antitone hmono i)) 1
  rw [potential, potential, ← sum_sub_distrib]
  calc
    _ ≤ Real.log ((below r l).card + 1 : ℝ) - Real.log ((below r' l).card + 1 : ℝ) := by
      apply log_drop _ (by positivity) hδ hdrop
      exact_mod_cast (card_pos.mpr hn)
    _ ≤ ∑ i ∈ range (D+1),
        (Real.log ((below r i).card + 1 : ℝ) - Real.log ((below r' i).card + 1 : ℝ)) := by
      exact single_le_sum (fun i hi => sub_nonneg.mpr (hle i)) (mem_range.mpr (by omega))

theorem below_card_le_of_max {r : Y → ℕ} {l : ℕ}
    (hmax : ∀ j ≤ l, (level r j).card ≤ (level r l).card) :
    (below r l).card ≤ (l+1)*(level r l).card := by
  have heq : below r l = (range (l+1)).biUnion (level r) := by
    ext y
    simp [below, level]
  rw [heq]
  calc
    _ ≤ ∑ j ∈ range (l+1), (level r j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ range (l+1), (level r l).card :=
      sum_le_sum fun j hj => hmax j (by simpa using hj)
    _ = _ := by simp
end FinitePotential

section State
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
abbrev Points := Projectivization K V
abbrev State := Points (K:=K) (V:=V) → Submodule K V
noncomputable def ranks (W : State (K:=K) (V:=V)) (y : Points (K:=K) (V:=V)) : ℕ :=
  Module.finrank K (W y)

noncomputable def update (W : State (K:=K) (V:=V))
    (a : Module.Dual K V) (b : Points (K:=K) (V:=V)) : State (K:=K) (V:=V) :=
  fun y => if a y.rep = 0 then W y ⊔ b.submodule else W y

omit [FiniteDimensional K V] [Fintype (Projectivization K V)] in
theorem le_update (W : State (K:=K) (V:=V)) (a : Module.Dual K V)
    (b y : Points (K:=K) (V:=V)) : W y ≤ update W a b y := by
  unfold update
  split_ifs
  · exact le_sup_left
  · exact le_rfl

omit [Fintype (Projectivization K V)] in
theorem ranks_update_mono (W : State (K:=K) (V:=V)) (a : Module.Dual K V)
    (b y : Points (K:=K) (V:=V)) : ranks W y ≤ ranks (update W a b) y :=
  Submodule.finrank_mono (le_update W a b y)

omit [Fintype (Projectivization K V)] in
theorem ranks_lt_update (W : State (K:=K) (V:=V)) (a : Module.Dual K V)
    (b y : Points (K:=K) (V:=V)) (ha : a y.rep = 0) (hb : ¬ b.submodule ≤ W y) :
    ranks W y < ranks (update W a b) y := by
  apply Submodule.finrank_lt_finrank_of_lt
  rw [update, ite_eq_left ha]
  refine lt_of_le_of_ne le_sup_left ?_
  intro he
  apply hb
  have h : b.submodule ≤ W y ⊔ b.submodule := le_sup_right
  rwa [← he] at h

def Popular (W : State (K:=K) (V:=V)) (q : ℝ) (l : ℕ)
    (b : Points (K:=K) (V:=V)) : Prop :=
  ((level (ranks W) l).card : ℝ)/(16*q) ≤
    ((level (ranks W) l).filter (fun y => b.submodule ≤ W y)).card

def Poor (W : State (K:=K) (V:=V)) (q : ℝ) (l : ℕ)
    (a : Module.Dual K V) : Prop :=
  (((level (ranks W) l).filter (fun y => a y.rep = 0)).card : ℝ) ≤
    (level (ranks W) l).card/(8*q)

theorem expensive_drop (W : State (K:=K) (V:=V)) {q : ℝ} (hq : 0 < q)
    {l D : ℕ} (hl : l ≤ D)
    (hmax : ∀ j ≤ l, (level (ranks W) j).card ≤ (level (ranks W) l).card)
    (a : Module.Dual K V) (b : Points (K:=K) (V:=V))
    (hp : ¬ Popular W q l b) (hr : ¬ Poor W q l a) :
    (1/(32*(D+1)*q) : ℝ) ≤
      potential D (ranks W) - potential D (ranks (update W a b)) := by
  let Z := level (ranks W) l
  let H := Z.filter (fun y => a y.rep = 0)
  let B := Z.filter (fun y => b.submodule ≤ W y)
  have hp' : (B.card:ℝ) < Z.card/(16*q) := lt_of_not_ge hp
  have hr' : Z.card/(8*q) < (H.card:ℝ) := lt_of_not_ge hr
  have hZ : Z.Nonempty := by
    apply card_pos.mp
    by_contra! hz
    have hz0 : Z.card = 0 := by omega
    have hB0 : B.card = 0 := by apply Nat.eq_zero_of_le_zero; rw [← hz0]; exact card_filter_le _ _
    rw [hz0, hB0] at hp'
    simp at hp'
  have hU := below_card_le_of_max hmax
  have hUD : (below (ranks W) l).card ≤ (D+1)*Z.card :=
    hU.trans (Nat.mul_le_mul_right _ (by omega))
  have hset : below (ranks (update W a b)) l ⊆ below (ranks W) l \ (H \ B) := by
    intro y hy
    refine mem_sdiff.mpr ⟨below_antitone (ranks_update_mono W a b) l hy, ?_⟩
    intro hb
    obtain ⟨hyH, hyB⟩ := mem_sdiff.mp hb
    obtain ⟨hyZ, ha⟩ := mem_filter.mp hyH
    have ranky : ranks W y = l := by simpa [Z, level] using hyZ
    have hby : ¬ b.submodule ≤ W y := fun hb => hyB (mem_filter.mpr ⟨hyZ,hb⟩)
    have hgt := ranks_lt_update W a b y ha hby
    have hle : ranks (update W a b) y ≤ l := by simpa [below] using hy
    omega
  have hHB : H \ B ⊆ below (ranks W) l := by
    intro y hy
    have hz := (mem_filter.mp (mem_sdiff.mp hy).1).1
    simp only [Z, level, mem_filter, mem_univ, true_and] at hz
    simpa only [below, mem_filter, mem_univ, true_and] using hz.le
  have hcard : (below (ranks (update W a b)) l).card + (H \ B).card ≤
      (below (ranks W) l).card := by
    have hc := card_le_card hset
    rw [card_sdiff_of_subset hHB] at hc
    have hsmall := card_le_card hHB
    omega
  have hdiff : (H.card:ℝ) - B.card ≤ ((H \ B).card:ℝ) := by
    have hc : H.card ≤ (H \ B).card + B.card := card_le_card_sdiff_add_card
    have hc' : (H.card:ℝ) ≤ (H \ B).card + B.card := by exact_mod_cast hc
    linarith
  have hpos : (0:ℝ) < D+1 := by positivity
  have hfrac : ((below (ranks W) l).card : ℝ)/(16*(D+1)*q) ≤
      (H.card:ℝ)-B.card := by
    have hUD' : ((below (ranks W) l).card : ℝ) ≤ (D+1)*Z.card := by exact_mod_cast hUD
    have h1 : ((below (ranks W) l).card : ℝ)/(16*(D+1)*q) ≤ Z.card/(16*q) := by
      apply (div_le_iff₀ (by positivity : (0:ℝ) < 16*(D+1)*q)).mpr
      field_simp
      nlinarith
    have h2 : Z.card/(16*q) < (H.card:ℝ)-B.card := by
      have he : (Z.card:ℝ)/(8*q) = 2*(Z.card/(16*q)) := by field_simp; ring
      linarith
    exact h1.trans h2.le
  have hbelow : (below (ranks W) l).Nonempty := by
    obtain ⟨y,hy⟩ := hZ
    refine ⟨y,?_⟩
    have hz : ranks W y = l := by simpa [Z, level] using hy
    simp [below,hz]
  have Hdrop := potential_drop hl (ranks_update_mono W a b) hbelow
    (by positivity : (0:ℝ) ≤ 1/(16*(D+1)*q))
  have hc' : ((below (ranks (update W a b)) l).card : ℝ) + (H \ B).card ≤
      (below (ranks W) l).card := by exact_mod_cast hcard
  have Hdrop' := Hdrop (by
    rw [one_div_mul_eq_div]
    linarith : ((below (ranks (update W a b)) l).card : ℝ) ≤
      (below (ranks W) l).card - 1/(16*(D+1)*q)*(below (ranks W) l).card)
  convert Hdrop' using 1; field_simp; ring

noncomputable def chosenLevel (W : State (K:=K) (V:=V))
    (b : Points (K:=K) (V:=V)) : ℕ :=
  Classical.choose ((range (ranks W b + 1)).exists_max_image
    (fun l => (level (ranks W) l).card) ⟨0, by simp⟩)

omit [FiniteDimensional K V] in
theorem chosenLevel_spec (W : State (K:=K) (V:=V))
    (b : Points (K:=K) (V:=V)) :
    chosenLevel W b ≤ ranks W b ∧
    ∀ j ≤ ranks W b, (level (ranks W) j).card ≤ (level (ranks W) (chosenLevel W b)).card := by
  have h := Classical.choose_spec ((range (ranks W b + 1)).exists_max_image
    (fun l => (level (ranks W) l).card) ⟨0, by simp⟩)
  simpa only [chosenLevel, mem_range, Nat.lt_succ_iff] using h

def IsExpensive (W : State (K:=K) (V:=V)) (q : ℝ)
    (f : Module.Dual K V × Points (K:=K) (V:=V)) : Prop :=
  ¬ Popular W q (chosenLevel W f.2) f.2 ∧ ¬ Poor W q (chosenLevel W f.2) f.1

noncomputable def scan (q : ℝ) : State (K:=K) (V:=V) →
    List (Module.Dual K V × Points (K:=K) (V:=V)) → ℕ × State (K:=K) (V:=V)
  | W, [] => (0,W)
  | W, f :: fs =>
    if IsExpensive W q f then
      let p := scan q (update W f.1 f.2) fs
      (p.1+1,p.2)
    else scan q W fs

theorem scan_potential_bound (q : ℝ) (hq : 0 < q)
    (W : State (K:=K) (V:=V)) (fs : List (Module.Dual K V × Points (K:=K) (V:=V))) :
    ((scan q W fs).1:ℝ) / (32*(Module.finrank K V+1)*q) ≤
      potential (Module.finrank K V) (ranks W) -
        potential (Module.finrank K V) (ranks (scan q W fs).2) := by
  induction fs generalizing W with
  | nil => simp [scan]
  | cons f fs ih =>
    by_cases he : IsExpensive W q f
    · simp only [scan, ite_eq_left he]
      have hL := chosenLevel_spec W f.2
      have hD : chosenLevel W f.2 ≤ Module.finrank K V :=
        hL.1.trans (Submodule.finrank_le _)
      have hd := expensive_drop W hq hD
        (fun j hj => hL.2 _ (hj.trans hL.1)) f.1 f.2 he.1 he.2
      have hi := ih (update W f.1 f.2)
      push_cast
      rw [add_div]
      linarith
    · simpa only [scan, ite_eq_right he] using ih W

theorem scan_expensive_bound (q : ℝ) (hq : 0 < q)
    (W : State (K:=K) (V:=V)) (fs : List (Module.Dual K V × Points (K:=K) (V:=V))) :
    ((scan q W fs).1:ℝ) ≤
      32*(Module.finrank K V+1)^2*q*Real.log (Fintype.card (Points (K:=K) (V:=V))+1 : ℝ) := by
  have h := scan_potential_bound q hq W fs
  have hn := potential_nonneg (Module.finrank K V) (ranks (scan q W fs).2)
  have hu := potential_le (Module.finrank K V) (ranks W)
  have hden : (0:ℝ) < 32*(Module.finrank K V+1)*q := by positivity
  have h' : ((scan q W fs).1:ℝ)/(32*(Module.finrank K V+1)*q) ≤
      (Module.finrank K V+1)*Real.log (Fintype.card (Points (K:=K) (V:=V))+1 : ℝ) := by
    linarith
  have h'' := (div_le_iff₀ hden).mp h'
  convert h'' using 1
  first | rfl | ring

omit [FiniteDimensional K V] [Fintype (Projectivization K V)] in

theorem update_le_ker (W : State (K:=K) (V:=V))
    (a a' : Module.Dual K V) (b y : Points (K:=K) (V:=V))
    (hW : W y ≤ LinearMap.ker a') (hcons : a y.rep = 0 → a' b.rep = 0) :
    update W a b y ≤ LinearMap.ker a' := by
  unfold update
  split_ifs with ha
  · apply sup_le hW
    rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
    exact hcons ha
  · exact hW

noncomputable def historyState : List (Module.Dual K V × Points (K:=K) (V:=V)) → State (K:=K) (V:=V)
  | [] => fun _ => ⊥
  | f::fs => update (historyState fs) f.1 f.2

omit [FiniteDimensional K V] [Fintype (Projectivization K V)] in
theorem historyState_le_ker (fs : List (Module.Dual K V × Points (K:=K) (V:=V)))
    (a : Module.Dual K V) (y : Points (K:=K) (V:=V))
    (hcons : ∀ f ∈ fs, f.1 y.rep = 0 → a f.2.rep = 0) :
    historyState fs y ≤ LinearMap.ker a := by
  induction fs with
  | nil => exact bot_le
  | cons f fs ih =>
    apply update_le_ker
    · exact ih (fun f hf => hcons f (List.mem_cons_of_mem _ hf))
    · exact hcons f (List.mem_cons_self)

omit [Fintype (Projectivization K V)] in
theorem historyState_rank_bound (fs : List (Module.Dual K V × Points (K:=K) (V:=V)))
    (a : Module.Dual K V) (ha : a ≠ 0) (y : Points (K:=K) (V:=V))
    (hcons : ∀ f ∈ fs, f.1 y.rep = 0 → a f.2.rep = 0) :
    ranks (historyState fs) y < Module.finrank K V := by
  have hm := Submodule.finrank_mono (historyState_le_ker fs a y hcons)
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero ha
  unfold ranks
  omega

end State
end SharpLogRamsey.Marking

namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem geom_sum_le_twice {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ i ∈ range (r+1), q^i) ≤ 2*q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := pow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hq hp]

omit [Fintype (Projectivization K (Module.Dual K V))] in
omit [FiniteDimensional K V] in
theorem card_subspace_points_le (W : Submodule K V) {r : ℕ}
    (hW : Module.finrank K W = r+1) :
    ((univ.filter (fun b : Points (K:=K) (V:=V) => b.submodule ≤ W)).card:ℝ) ≤
      2*(Nat.card K:ℝ)^r := by
  have hc : (univ.filter (fun b : Points (K:=K) (V:=V) => b.submodule ≤ W)).card =
      ∑ i ∈ range (r+1), Nat.card K^i := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      ← Nat.card_congr (projectiveSubmoduleEquiv W)]
    exact Projectivization.card_of_finrank K W hW
  rw [hc, Nat.cast_sum]
  push_cast
  apply geom_sum_le_twice
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)

theorem joint_bound_of_product {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V)))
    (hprod : (S.card:ℝ)*T.card ≤ 16*(Nat.card K:ℝ)^(n+3)) :
    (incidenceCount S T:ℝ) ≤ 20*(Nat.card K:ℝ)^(n+2) := by
  let q : ℝ := Nat.card K
  let p : ℝ := (∑ i ∈ range (n+2), q^i)/(∑ i ∈ range (n+3), q^i)
  let a : ℝ := (S.card:ℝ)*T.card
  have hq : 0 < q := by
    change (0:ℝ) < Nat.card K
    have h := (Finite.one_lt_card : 1 < Nat.card K)
    exact_mod_cast (lt_trans Nat.zero_lt_one h)
  have hv : 0 < ∑ i ∈ range (n+3), q^i := by
    apply sum_pos' (fun i hi => pow_nonneg hq.le _)
    exact ⟨0, by simp, by simp⟩
  have hp : p ≤ 1/q := by
    apply (div_le_div_iff₀ hv hq).mpr
    have he : (∑ i ∈ range (n+3), q^i) = q*(∑ i ∈ range (n+2), q^i)+1 := geom_sum_succ
    linarith
  have ha : 0 ≤ a := by positivity
  have hm := mul_le_mul_of_nonneg_right hp ha
  have hcap : p*a ≤ 16*q^(n+2) := by
    have hd : a/q ≤ 16*q^(n+2) := by
      apply (div_le_iff₀ hq).mpr
      have he : q^(n+3) = q^(n+2)*q := by rw [← pow_succ]
      change a ≤ 16*q^(n+3) at hprod
      rw [he] at hprod
      nlinarith
    have he : (1/q)*a = a/q := by ring
    rw [he] at hm
    exact hm.trans hd
  have hs := projective_mixing_sq hdim S T
  change ((incidenceCount S T:ℝ)-p*S.card*T.card)^2 ≤ q^(n+1)*S.card*T.card at hs
  simp only [mul_assoc] at hs
  change ((incidenceCount S T:ℝ)-p*a)^2 ≤ q^(n+1)*a at hs
  have hmul := mul_le_mul_of_nonneg_left hprod (pow_nonneg hq.le (n+1))
  have he : q^(n+1)*(16*q^(n+3)) = (4*q^(n+2))^2 := by
    rw [mul_left_comm, ← pow_add, mul_pow, ← pow_mul]
    congr 1 <;> ring
  change q^(n+1)*a ≤ q^(n+1)*(16*q^(n+3)) at hmul
  rw [he] at hmul
  have hfour : 0 ≤ 4*q^(n+2) := by positivity
  have habs := (sq_le_sq₀ (abs_nonneg ((incidenceCount S T:ℝ)-p*a)) hfour).mp
    (by simpa using hs.trans hmul)
  have hdev := le_abs_self ((incidenceCount S T:ℝ)-p*a)
  linarith

noncomputable def poorDomain (W : State (K:=K) (V:=V)) (l : ℕ) :
    Finset (Projectivization K (Module.Dual K V)) :=
  univ.filter (fun a => Poor W (Nat.card K) l a.rep)

theorem poor_marginal_product {n : ℕ} (hdim : Module.finrank K V = n+3)
    (W : State (K:=K) (V:=V)) (l : ℕ) :
    ((level (ranks W) l).card:ℝ)*(poorDomain W l).card ≤
      16*(Nat.card K:ℝ)^(n+3) := by
  apply sparse_product_bound hdim
  have hq : (0:ℝ) < Nat.card K := by
    exact_mod_cast (Finite.card_pos : 0 < Nat.card K)
  calc
    (incidenceCount (level (ranks W) l) (poorDomain W l):ℝ) ≤
        ∑ _a ∈ poorDomain W l, ((level (ranks W) l).card:ℝ)/(8*Nat.card K) := by
      rw [incidenceCount, Nat.cast_sum]
      apply sum_le_sum
      intro a ha
      have h := (mem_filter.mp ha).2
      exact h
    _ = ((level (ranks W) l).card:ℝ)*(poorDomain W l).card/(8*Nat.card K) := by
      simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((level (ranks W) l).card:ℝ)*(poorDomain W l).card/(4*Nat.card K) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith

theorem poor_joint_domain_bound {n : ℕ} (hdim : Module.finrank K V = n+3)
    (W : State (K:=K) (V:=V)) {l r : ℕ}
    (hmax : (level (ranks W) r).card ≤ (level (ranks W) l).card) :
    (incidenceCount (level (ranks W) r) (poorDomain W l):ℝ) ≤
      20*(Nat.card K:ℝ)^(n+2) := by
  apply joint_bound_of_product hdim
  calc
    _ ≤ ((level (ranks W) l).card:ℝ)*(poorDomain W l).card :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmax) (by positivity)
    _ ≤ _ := poor_marginal_product hdim W l

end SharpLogRamsey.Marking

namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

noncomputable def popularDomain (W : State (K:=K) (V:=V)) (l : ℕ) : Finset (Points (K:=K) (V:=V)) :=
  univ.filter (Popular W (Nat.card K) l)

end SharpLogRamsey.Marking
end

end OAI
