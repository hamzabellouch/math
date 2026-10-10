import OAI.Combinatorics.FiniteCircle.RandomCodes

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem StrongLocal.anchorLocal {α : Type*} {w : ℕ} {c : α → Fin w → Bool}
    (hc : StrongLocal c) : AnchorLocal (1/1048576) c := by
  intro a b is js his hjs hlen hsize hli hlj hbits
  apply hc a b is js his hjs hlen
  · have hh : (w : ℝ) ≤ 16*is.length := by nlinarith
    exact_mod_cast hh
  · convert hli using 1; ring
  · convert hlj using 1; ring
  · exact hbits

@[simp] theorem length_interval {α : Type*} {w : ℕ} (c : α → Fin w → Bool)
    (a : α) {s u : ℕ} (hs : s+u ≤ w) : (interval c a s u).length = u := by
  simp only [interval, List.length_take, List.length_drop, List.length_ofFn]
  omega

theorem get_interval {α : Type*} {w : ℕ} (c : α → Fin w → Bool)
    (a : α) {s u : ℕ} (hs : s+u ≤ w) (i : Fin (interval c a s u).length) :
    (interval c a s u).get i = c a ⟨s+i.val, by
      have hi := i.isLt
      simp only [length_interval c a hs] at hi
      omega⟩ := by
  change (((List.ofFn (c a)).drop s).take u)[i.val] = _
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem indexSpan_ofFn_le {w q s u : ℕ} (f : Fin q → Fin w)
    (hb : ∀ i, s ≤ (f i).val ∧ (f i).val < s+u) : indexSpan (List.ofFn f) ≤ u := by
  by_cases hq : 0 < q
  · rw [indexSpan_ofFn f hq]
    obtain ⟨hl, _⟩ := hb ⟨0, hq⟩
    obtain ⟨_, hh⟩ := hb ⟨q-1, by omega⟩
    omega
  · have he : q = 0 := by omega
    subst q
    simp [indexSpan]

theorem StrongLocal.offsetLocal {α : Type*} {w : ℕ} {c : α → Fin w → Bool}
    (hc : StrongLocal c) (hw : 0 < w) (hd : 8 ∣ w) : OffsetLocal (1/1048576) c := by
  intro a b hab s t hs ht
  let u := w/8
  let q := lcs (interval c a s u) (interval c b t u)
  have hsu : s+u ≤ w := hs
  have htu : t+u ≤ w := ht
  have hqu : q ≤ u := by simpa only [length_interval c a hsu] using lcs_le_length_left (interval c a s u) (interval c b t u)
  have huw : u*8 = w := Nat.div_mul_cancel hd
  by_contra hn
  have hn : (1-(1:ℝ)/1048576)*(u : ℝ) < q := lt_of_not_ge hn
  have hqpos : 0 < q := by
    have hu : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
    have hqr : (0 : ℝ) < q := by nlinarith
    exact_mod_cast hqr
  obtain ⟨M⟩ := exists_lcs_matching (interval c a s u) (interval c b t u)
  let f : Fin q → Fin w := fun i => ⟨s+(M.left i).val, by
    have hh := (M.left i).isLt
    simp only [length_interval c a hsu] at hh
    omega⟩
  let g : Fin q → Fin w := fun i => ⟨t+(M.right i).val, by
    have hh := (M.right i).isLt
    simp only [length_interval c b htu] at hh
    omega⟩
  have hf : StrictMono f := by
    intro i j hij
    have hh := M.left.strictMono hij
    change s+(M.left i).val < s+(M.left j).val
    exact Nat.add_lt_add_left hh s
  have hg : StrictMono g := by
    intro i j hij
    have hh := M.right.strictMono hij
    change t+(M.right i).val < t+(M.right j).val
    exact Nat.add_lt_add_left hh t
  have his : (List.ofFn f).Pairwise (fun i j => i.val < j.val) := by
    apply List.pairwise_iff_get.mpr
    intro i j hij
    simpa only [List.get_ofFn, Fin.lt_def] using hf (show (Fin.cast List.length_ofFn i) < Fin.cast List.length_ofFn j from hij)
  have hjs : (List.ofFn g).Pairwise (fun i j => i.val < j.val) := by
    apply List.pairwise_iff_get.mpr
    intro i j hij
    simpa only [List.get_ofFn, Fin.lt_def] using hg (show (Fin.cast List.length_ofFn i) < Fin.cast List.length_ofFn j from hij)
  have hsize : w ≤ 16*(List.ofFn f).length := by
    rw [List.length_ofFn]
    have hur : (u : ℝ)*8 = w := by exact_mod_cast huw
    have hqr : (w : ℝ) ≤ 16*q := by nlinarith
    exact_mod_cast hqr
  have hdef : ((u-q : ℕ) : ℝ) ≤ (w : ℝ)/1048576 := by
    rw [Nat.cast_sub hqu]
    have hur : (u : ℝ)*8 = w := by exact_mod_cast huw
    nlinarith
  have hli : ((indexSpan (List.ofFn f) - (List.ofFn f).length : ℕ) : ℝ) ≤ (w : ℝ)/1048576 := by
    have hh : indexSpan (List.ofFn f) ≤ u := indexSpan_ofFn_le (s := s) (u := u) f (fun i => by
      dsimp only [f]
      have hi := (M.left i).isLt
      simp only [length_interval c a hsu] at hi
      omega)
    rw [List.length_ofFn]
    exact (Nat.cast_le.mpr (Nat.sub_le_sub_right hh q)).trans hdef
  have hlj : ((indexSpan (List.ofFn g) - (List.ofFn g).length : ℕ) : ℝ) ≤ (w : ℝ)/1048576 := by
    have hh : indexSpan (List.ofFn g) ≤ u := indexSpan_ofFn_le (s := t) (u := u) g (fun i => by
      dsimp only [g]
      have hi := (M.right i).isLt
      simp only [length_interval c b htu] at hi
      omega)
    rw [List.length_ofFn]
    exact (Nat.cast_le.mpr (Nat.sub_le_sub_right hh q)).trans hdef
  have hbits : ∀ ij ∈ (List.ofFn f).zip (List.ofFn g), c a ij.1 = c b ij.2 := by
    intro ij hij
    rw [zip_ofFn] at hij
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hij
    have hh := M.letters i
    rw [get_interval c a hsu, get_interval c b htu] at hh
    exact hh
  exact hab (hc a b (List.ofFn f) (List.ofFn g) his hjs (by simp) hsize hli hlj hbits).1

theorem strongLocal_substitutionBounds {α : Type*} [Fintype α] {w : ℕ}
    {c : α → Fin w → Bool} (hw : 0 < w)
    (hwidth : (w : ℝ) ≤ 67108928*Real.log (2*Fintype.card α)) (hc : StrongLocal c) :
    SubstitutionBounds (1/2097152) 67108928 c := by
  refine ⟨hw, hwidth, ?_, editDistance_encode_le c⟩
  intro L x y hx hy
  refine ⟨?_, deficit_encode_le c x y⟩
  have hh := anchor_deficit_lower hw (by norm_num : (0 : ℝ) ≤ 1/1048576)
    (by norm_num : (1 : ℝ)/1048576 ≤ 1/10) hc.anchorLocal x y (hx.trans hy.symm)
  convert hh using 1; norm_num

theorem SubstitutionBounds.weaken {α : Type*} [Fintype α] {w : ℕ}
    {c : α → Fin w → Bool} {a b C : ℝ} (hc : SubstitutionBounds a C c)
    (hba : b ≤ a) : SubstitutionBounds b C c := by
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.2⟩
  intro L x y hx hy
  obtain ⟨hl,hu⟩ := hc.2.2.1 L x y hx hy
  refine ⟨?_,hu⟩
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hba
    (Nat.cast_nonneg w)) (Nat.cast_nonneg (deficit x y))).trans hl

theorem offsetLocal_substitutionBounds {α : Type*} [Fintype α] {w : ℕ}
    {c : α → Fin w → Bool} (hw : 12 ≤ w) (hd : 8 ∣ w)
    (hwidth : (w : ℝ) ≤ 67108928 * Real.log (2*Fintype.card α))
    (hc : OffsetLocal (1/1048576) c) : SubstitutionBounds (1/268435456) 67108928 c := by
  refine ⟨by omega,hwidth,?_,editDistance_encode_le c⟩
  intro L x y hx hy
  refine ⟨?_,deficit_encode_le c x y⟩
  have he : (8 : ℝ)*(w/8 : ℕ) = w := by exact_mod_cast (Nat.mul_div_cancel' hd)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0<w by omega)
  have hfit : 2*(1/33554432 : ℝ)*w < (1/1048576 : ℝ)*(w/8 : ℕ) := by
    linarith only [he,hw0]
  have hh := offset_deficit_lower hw (by norm_num : (1 : ℝ)/1048576 ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1/33554432) (by norm_num : (1 : ℝ)/33554432 ≤ 1)
    hfit hc x y (hx.trans hy.symm)
  apply le_trans _ hh
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (by norm_num : (1 : ℝ)/268435456 ≤ (1/33554432)/(4+32*(1/33554432)))
    (Nat.cast_nonneg w)) (Nat.cast_nonneg (deficit x y))

theorem two_codes : TwoCodes (1/268435456) 67108928 (1/1048576) (1/1048576) := by
  intro α _ hA
  obtain ⟨w, c, hw, hd, hwidth, hc⟩ := exists_strongLocal α hA
  have hwp : 0 < w := by omega
  have hd8 : 8 ∣ w := dvd_trans (by norm_num : 8 ∣ 64) hd
  have ho := hc.offsetLocal hwp hd8
  have hbo := offsetLocal_substitutionBounds (by omega) hd8 hwidth ho
  have hba := (strongLocal_substitutionBounds hwp hwidth hc).weaken
    (by norm_num : (1 : ℝ)/268435456 ≤ 1/2097152)
  exact ⟨⟨w,c,hbo,ho⟩,⟨w,c,hba,hc.anchorLocal⟩⟩

end FiniteCircle

end OAI
