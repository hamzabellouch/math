import OAI.Combinatorics.FiniteCircle.BitCounting

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

open Classical

abbrev SmallHoles (w : ℕ) := {S : Finset (Fin w) // (S.card : ℝ) ≤ (w : ℝ)/1048576}
abbrev DenseParameters (w : ℕ) := Fin w × Fin w × SmallHoles w

noncomputable instance (w : ℕ) : Fintype (SmallHoles w) := Fintype.ofFinite _

def denseList {w : ℕ} (P : DenseParameters w) : List (Fin w) :=
  (Finset.Icc P.1 P.2.1 \ P.2.2.val).sort (· ≤ ·)

theorem denseList_sorted {w : ℕ} (P : DenseParameters w) :
    (denseList P).Pairwise (fun i j => i.val < j.val) :=
  (Finset.sortedLT_sort (Finset.Icc P.1 P.2.1 \ P.2.2.val)).pairwise

theorem exists_denseParameters {w : ℕ} (is : List (Fin w))
    (hs : is.Pairwise (fun i j => i.val < j.val)) (hn : 0 < is.length)
    (hloss : (indexSpan is - is.length : ℕ) ≤ (w : ℝ)/1048576) :
    ∃ P : DenseParameters w, denseList P = is := by
  classical
  let lo := is.get ⟨0, hn⟩
  let hi := is.get ⟨is.length-1, by omega⟩
  let S := is.toFinset
  have hm : StrictMono is.get := List.pairwise_iff_get.mp hs
  have hsub : S ⊆ Finset.Icc lo hi := by
    intro i hiS
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hiS)
    subst i
    exact Finset.mem_Icc.mpr ⟨hm.monotone (by exact Nat.zero_le _), hm.monotone (by
      change k.val ≤ is.length-1; omega)⟩
  have hcard : S.card = is.length := List.toFinset_card_of_nodup hs.nodup
  have hspan : (Finset.Icc lo hi).card = indexSpan is := by
    rw [Fin.card_Icc]
    have hh := indexSpan_ofFn is.get hn
    simpa only [List.ofFn_get] using hh.symm
  let H := Finset.Icc lo hi \ S
  have hH : (H.card : ℝ) ≤ (w : ℝ)/1048576 := by
    simpa only [H, Finset.card_sdiff_of_subset hsub, hcard, hspan] using hloss
  refine ⟨(lo, hi, ⟨H, hH⟩), ?_⟩
  dsimp only [denseList]
  rw [show Finset.Icc lo hi \ H = S from Finset.sdiff_sdiff_eq_self hsub]
  exact (List.toFinset_sort (· ≤ ·) hs.nodup).mpr (hs.imp (fun h => h.le))

def StrongLocal {α : Type*} {w : ℕ} (c : α → Fin w → Bool) : Prop :=
  ∀ a b : α, ∀ is js : List (Fin w),
    is.Pairwise (fun i j => i.val < j.val) →
    js.Pairwise (fun i j => i.val < j.val) →
    is.length = js.length → w ≤ 16*is.length →
    (indexSpan is - is.length : ℕ) ≤ (w : ℝ)/1048576 →
    (indexSpan js - js.length : ℕ) ≤ (w : ℝ)/1048576 →
    (∀ ij ∈ is.zip js, c a ij.1 = c b ij.2) →
    a = b ∧ ∃ i : Fin w, (i, i) ∈ is.zip js

abbrev DenseWitness (α : Type*) (w : ℕ) := (α × DenseParameters w) × (α × DenseParameters w)

def badDenseWitness {α : Type*} {w : ℕ} (W : DenseWitness α w) (ω : α × Fin w → Bool) : Prop :=
  let is := denseList W.1.2
  let js := denseList W.2.2
  is.length = js.length ∧ w ≤ 16*is.length ∧
  (W.1.1 ≠ W.2.1 ∨ ∀ i : Fin w, (i,i) ∉ is.zip js) ∧
  ∀ ij ∈ is.zip js, ω (W.1.1, ij.1) = ω (W.2.1, ij.2)

theorem card_badDenseWitness_le {α : Type*} [Fintype α] {w : ℕ}
    (W : DenseWitness α w) :
    (Finset.univ.filter (badDenseWitness W)).card ≤
      2^(Fintype.card α*w-w/64) := by
  classical
  let is := denseList W.1.2
  let js := denseList W.2.2
  by_cases hc : is.length = js.length ∧ w ≤ 16*is.length ∧
      (W.1.1 ≠ W.2.1 ∨ ∀ i : Fin w, (i,i) ∉ is.zip js)
  · obtain ⟨hlen, hw, hne⟩ := hc
    let f : Fin is.length → α × Fin w := fun k => (W.1.1, is.get k)
    let g : Fin is.length → α × Fin w := fun k => (W.2.1, js.get (Fin.cast hlen k))
    have his : StrictMono is.get := List.pairwise_iff_get.mp (denseList_sorted _)
    have hjs : StrictMono js.get := List.pairwise_iff_get.mp (denseList_sorted _)
    have hf : Function.Injective f := fun i j h => his.injective (congrArg Prod.snd h)
    have hg : Function.Injective g := by
      intro i j h
      have hh := hjs.injective (congrArg Prod.snd h)
      exact Fin.ext (show i.val = j.val from congrArg (fun k : Fin js.length => k.val) hh)
    have hpair (i : Fin is.length) : (is.get i, js.get (Fin.cast hlen i)) ∈ is.zip js := by
      apply List.mem_iff_get.mpr
      refine ⟨⟨i.val, by simp only [List.length_zip]; omega⟩, ?_⟩
      simp only [List.get_eq_getElem, List.getElem_zip, Fin.val_cast]
    have hn : ∀ i ∈ (Finset.univ : Finset (Fin is.length)), f i ≠ g i := by
      intro i _ he
      rcases hne with hne | hne
      · exact hne (show W.1.1 = W.2.1 from congrArg (fun x : α × Fin w => x.1) he)
      · have hh : is.get i = js.get (Fin.cast hlen i) := congrArg (fun x : α × Fin w => x.2) he
        exact hne (is.get i) (hh.symm ▸ hpair i)
    have hsub : Finset.univ.filter (badDenseWitness W) ⊆
        Finset.univ.filter (fun ω : α × Fin w → Bool => ∀ i ∈ (Finset.univ : Finset (Fin is.length)), ω (f i) = ω (g i)) := by
      intro ω hω
      have hω := (Finset.mem_filter.mp hω).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i _ => hω.2.2.2 _ (hpair i)⟩
    have hh := card_matching_equalities_le (Finset.univ : Finset (Fin is.length)) f g hf hg hn w (by simpa using hw)
    exact (Finset.card_le_card hsub).trans (by simpa [Fintype.card_prod, Fintype.card_fin] using hh)
  · have he : Finset.univ.filter (badDenseWitness W) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hω := (Finset.mem_filter.mp hω).2
      exact hc ⟨hω.1, hω.2.1, hω.2.2.1⟩
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem card_denseWitness_le {α : Type*} [Fintype α] (w : ℕ) :
    (Fintype.card (DenseWitness α w) : ℝ) ≤
      (Fintype.card α : ℝ)^2 * (w : ℝ)^4 * Real.exp ((w : ℝ)/256) := by
  classical
  have hk : (Fintype.card (SmallHoles w) : ℝ) ≤ Real.exp ((w : ℝ)/512) := by
    simpa only [SmallHoles, Fintype.card_subtype] using card_small_subsets_le w
  have he : Real.exp ((w : ℝ)/256) = Real.exp ((w : ℝ)/512)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hc : (Fintype.card (DenseWitness α w) : ℝ) =
      (Fintype.card α : ℝ)^2 * (w : ℝ)^4 * (Fintype.card (SmallHoles w) : ℝ)^2 := by
    simp only [DenseWitness, DenseParameters, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    ring
  rw [hc, he]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hk 2) (by positivity)

theorem dense_union_numerics {A w : ℕ} (hA : 2 ≤ A) (hw : 67108864 ≤ w)
    (hlog : 2048*Real.log (A : ℝ) ≤ w) (hd : 64 ∣ w) :
    (A : ℝ)^2 * (w : ℝ)^4 * Real.exp ((w : ℝ)/256) < (2 : ℝ)^(w/64) := by
  have hAp : (0 : ℝ) < A := by positivity
  have hwp : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hsqrt : 8192 ≤ Real.sqrt (w : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast hw
  have hlogw : Real.log (w : ℝ) ≤ 2*Real.sqrt (w : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hwp)
    rw [Real.log_sqrt hwp.le] at hh
    linarith
  have hsquare : (Real.sqrt (w : ℝ))^2 = w := Real.sq_sqrt hwp.le
  have hlogw' : 4096 * Real.log (w : ℝ) ≤ w := by
    nlinarith
  have hdiv : ((w/64 : ℕ) : ℝ)*64 = w := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hlog2 : (1 : ℝ)/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexpl : (A : ℝ)^2 * (w : ℝ)^4 * Real.exp ((w : ℝ)/256) =
      Real.exp (2*Real.log (A : ℝ) + 4*Real.log (w : ℝ) + (w : ℝ)/256) := by
    rw [Real.exp_add, Real.exp_add]
    have h2 := Real.exp_nat_mul (Real.log (A : ℝ)) 2
    have h4 := Real.exp_nat_mul (Real.log (w : ℝ)) 4
    norm_num only [Nat.cast_ofNat, Real.exp_log hAp, Real.exp_log hwp] at h2 h4
    rw [h2, h4]
  have hexpr : (2 : ℝ)^(w/64) = Real.exp (((w/64 : ℕ) : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hexpl, hexpr]
  apply Real.exp_lt_exp.mpr
  have hpos : (0 : ℝ) < (w/64 : ℕ) := by nlinarith
  have hm := mul_lt_mul_of_pos_left hlog2 hpos
  linarith

theorem exists_coding_width (A : ℕ) (hA : 2 ≤ A) :
    ∃ w : ℕ, 67108864 ≤ w ∧ 64 ∣ w ∧
      2048*Real.log (A : ℝ) ≤ w ∧
      (w : ℝ) ≤ 67108928 * Real.log (2*A) := by
  let t := Real.log (2*(A : ℝ))
  have hAp : (0 : ℝ) < A := by positivity
  have ht : 1 ≤ t := by
    have hh : (4 : ℝ) ≤ 2*A := by exact_mod_cast (by omega : 4 ≤ 2*A)
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hh
    have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    dsimp only [t]
    linarith [Real.log_two_gt_d9]
  have hAt : Real.log (A : ℝ) ≤ t := Real.log_le_log hAp (by nlinarith)
  let n := ⌈1048576*t⌉₊
  have hn : 1048576*t ≤ (n : ℝ) := Nat.le_ceil _
  have hn' : (n : ℝ) < 1048576*t+1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨64*n, ?_, dvd_mul_right _ _, ?_, ?_⟩
  · have hh : (67108864 : ℝ) ≤ 64*n := by nlinarith
    exact_mod_cast hh
  · push_cast
    nlinarith
  · push_cast
    change 64*(n : ℝ) ≤ 67108928*t
    nlinarith

theorem exists_strongLocal (α : Type*) [Fintype α] (hA : 2 ≤ Fintype.card α) :
    ∃ (w : ℕ) (c : α → Fin w → Bool), 67108864 ≤ w ∧ 64 ∣ w ∧
      (w : ℝ) ≤ 67108928 * Real.log (2*Fintype.card α) ∧ StrongLocal c := by
  classical
  obtain ⟨w, hw, hd, hlog, hwidth⟩ := exists_coding_width (Fintype.card α) hA
  let Ω := α × Fin w → Bool
  let B : Finset Ω := Finset.univ.biUnion (fun W : DenseWitness α w =>
    Finset.univ.filter (badDenseWitness W))
  have hcard : B.card ≤ Fintype.card (DenseWitness α w) * 2^(Fintype.card α*w-w/64) := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _W : DenseWitness α w, 2^(Fintype.card α*w-w/64) :=
        Finset.sum_le_sum (fun W _ => card_badDenseWitness_le W)
      _ = _ := by simp
  have hexp : (Fintype.card (DenseWitness α w) : ℝ) < (2 : ℝ)^(w/64) :=
    (card_denseWitness_le w).trans_lt (dense_union_numerics hA hw hlog hd)
  have hkn : w/64 ≤ Fintype.card α*w := by
    have hh : w ≤ Fintype.card α*w := by nlinarith
    exact (Nat.div_le_self _ _).trans hh
  have hstrict : (B.card : ℝ) < (2 : ℝ)^(Fintype.card α*w) := by
    have hc : (B.card : ℝ) ≤ (Fintype.card (DenseWitness α w) : ℝ) * (2 : ℝ)^(Fintype.card α*w-w/64) := by
      exact_mod_cast hcard
    calc
      _ ≤ _ := hc
      _ < (2 : ℝ)^(w/64) * (2 : ℝ)^(Fintype.card α*w-w/64) :=
        mul_lt_mul_of_pos_right hexp (by positivity)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hkn]
  have hB : B.card < (Finset.univ : Finset Ω).card := by
    have he : (Finset.univ : Finset Ω).card = 2^(Fintype.card α*w) := by
      simp [Ω, Fintype.card_prod]
    rw [he]
    exact_mod_cast hstrict
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hB
  have hω' (W : DenseWitness α w) : ¬badDenseWitness W ω := by
    intro hh
    apply hω
    exact Finset.mem_biUnion.mpr ⟨W, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
  refine ⟨w, fun a i => ω (a,i), hw, hd, hwidth, ?_⟩
  intro a b is js his hjs hlen hsize hli hlj hbits
  have hn : 0 < is.length := by omega
  obtain ⟨P, hP⟩ := exists_denseParameters is his hn hli
  obtain ⟨Q, hQ⟩ := exists_denseParameters js hjs (by omega) hlj
  by_contra hh
  apply hω' ((a,P),(b,Q))
  dsimp only [badDenseWitness]
  rw [hP, hQ]
  refine ⟨hlen, hsize, ?_, hbits⟩
  by_cases hab : a = b
  · exact Or.inr (fun i hi => hh ⟨hab, i, hi⟩)
  · exact Or.inl hab

end FiniteCircle

end OAI
