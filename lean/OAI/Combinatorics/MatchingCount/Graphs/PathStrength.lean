import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Edge

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}
theorem sdiff_pair_card [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    (S \ {a,b}).card = S.card - 2 := by
  have hsub : ({a,b} : Finset V) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · subst x
      exact ha
    · have he := Finset.mem_singleton.mp h
      subst x
      exact hb
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hab]

theorem relocated_card [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∉ S) : (insert b (S.erase a)).card = S.card := by
  have hba : b ∉ S.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hba, Finset.card_erase_add_one ha]

theorem pair_fill_holeRatio [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (a b : V) (hab : a ≠ b) :
    edgeActivity w a b * holeRatio w {a,b} ≤ 1 := by
  have h := edge_fill_holeRatio w hw hz {a,b} a b (by simp) (by simp) hab
  simpa [holeRatio_empty w hz] using h

theorem adjacent_hole_fill [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard w a)
    (hrhi : ∀ a, rowMax hcard w a ≤ 4)
    (S : Finset V) (hS : S.card = 2 ∨ S.card = 4)
    (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (B : ℝ) (hB : 0 < B) (hBa : B ≤ edgeActivity w a b) :
    holeRatio w S / rowMax hcard w a ≤ 32 / B := by
  have hfill := edge_fill_holeRatio w hw hz S a b ha hb hab
  have hhole := holeRatio_nonneg w hw S
  have hp : B * holeRatio w S ≤ holeRatio w (S \ {a,b}) :=
    (mul_le_mul_of_nonneg_right hBa hhole).trans hfill
  have hs : (S \ {a,b}).card = 0 ∨ (S \ {a,b}).card = 2 := by
    rw [sdiff_pair_card S a b ha hb hab]
    omega
  have hg := zero_or_two_holes_le_four hcard w hz hrhi (S \ {a,b}) hs
  have hra := hrlo a
  have hrap : 0 < rowMax hcard w a := by linarith
  apply (div_le_iff₀ hrap).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hB).mpr
  nlinarith only [hp,hg,hra]

theorem toggle_small_holes_card [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hab : a ≠ b) (hS : S.card = 2 ∨ S.card = 4) :
    (S ∆ {a,b}).card = 0 ∨ (S ∆ {a,b}).card = 2 ∨ (S ∆ {a,b}).card = 4 := by
  by_cases hb : b ∈ S
  · rw [symmDiff_pair_of_mem_mem S a b ha hb, sdiff_pair_card S a b ha hb hab]
    omega
  · rw [symmDiff_pair_of_mem_notMem S a b ha hb, relocated_card S a b ha hb]
    omega

theorem normalized_relocation [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard w a)
    (hrhi : ∀ a, rowMax hcard w a ≤ 4)
    (S : Finset V) (hS : S.card = 2 ∨ S.card = 4)
    (a z : V) (ha : a ∈ S) (hzS : z ∉ S)
    (B : ℝ) (hB8 : 8 < B) (hBa : B ≤ edgeActivity w a z) :
    holeRatio w S / rowMax hcard w a ≤
      holeRatio w (insert z (S.erase a)) / rowMax hcard w z + 6144 / B := by
  have hB : 0 < B := by linarith
  have haz : a ≠ z := fun h => hzS (h ▸ ha)
  have hrap : ∀ v, 0 < rowMax hcard w v := fun v => by linarith [hrlo v]
  obtain ⟨p,hpz,hpr⟩ := rowMax_attained hcard w z
  have hfill := pair_fill_holeRatio w hw hz a z haz
  have hpair : B * holeRatio w {a,z} ≤ 1 :=
    (mul_le_mul_of_nonneg_right hBa (holeRatio_nonneg w hw {a,z})).trans hfill
  have hpa : p ≠ a := by
    intro h
    subst p
    rw [holeRatio_pair_comm w z a] at hpr
    have hlo := hrlo z
    rw [← hpr] at hlo
    nlinarith
  let R := S \ {a,p}
  let F := fun b => holeRatio w (S ∆ {a,b}) * holeRatio w ({z,p} ∆ {a,b})
  have hF : ∀ b, 0 ≤ F b := fun b => mul_nonneg
    (holeRatio_nonneg w hw _) (holeRatio_nonneg w hw _)
  have hcmp := mixed_holeRatio_comparison w hw hz S {z,p} a ha
    (by simp [haz, Ne.symm hpa])
  change holeRatio w S * holeRatio w {z,p} ≤
    ∑ b ∈ (S ∆ {z,p}).erase a, F b at hcmp
  rw [hpr] at hcmp
  have hsub : (S ∆ {z,p}).erase a ⊆ insert z (insert p R) := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_symmDiff, Finset.mem_insert,
      Finset.mem_singleton, R, Finset.mem_sdiff] at hx ⊢
    grind
  have hcmp' : holeRatio w S * rowMax hcard w z ≤ ∑ b ∈ insert z (insert p R), F b :=
    hcmp.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => hF b))
  have hzR : z ∉ R := fun h => hzS (Finset.mem_sdiff.mp h).1
  have hpR : p ∉ R := by simp [R]
  rw [Finset.sum_insert (by simp [hpz.symm, hzR]), Finset.sum_insert hpR] at hcmp'
  have htz : ({z,p} : Finset V) ∆ {a,z} = {a,p} := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have htp : ({z,p} : Finset V) ∆ {a,p} = {a,z} := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hFz : F z ≤ holeRatio w (insert z (S.erase a)) * rowMax hcard w a := by
    dsimp [F]
    rw [symmDiff_pair_of_mem_notMem S a z ha hzS, htz]
    exact mul_le_mul_of_nonneg_left (holeRatio_le_rowMax hcard w a p hpa.symm)
      (holeRatio_nonneg w hw _)
  have hFp : B * F p ≤ 48 := by
    have hh := small_holes_le_fortyeight hcard w hw hz hrhi (S ∆ {a,p})
      (toggle_small_holes_card S a p ha hpa.symm hS)
    have hn := holeRatio_nonneg w hw (S ∆ {a,p})
    dsimp [F]
    rw [htp]
    nlinarith only [hpair, hh, hn]
  have hFx : ∀ x ∈ R, B * F x ≤ 16 := by
    intro x hx
    have hxS := (Finset.mem_sdiff.mp hx).1
    have hxa : x ≠ a := by
      intro h
      exact (Finset.mem_sdiff.mp hx).2 (by simp [h])
    have hxp : x ≠ p := by
      intro h
      exact (Finset.mem_sdiff.mp hx).2 (by simp [h])
    have hxz : x ≠ z := fun h => hzS (h ▸ hxS)
    have ht : ({z,p} : Finset V) ∆ {a,x} = {z,p,a,x} := by
      ext v
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      grind
    have hs : (S \ {a,x}).card = 0 ∨ (S \ {a,x}).card = 2 := by
      rw [sdiff_pair_card S a x ha hxS hxa.symm]
      omega
    have hs4 := zero_or_two_holes_le_four hcard w hz hrhi (S \ {a,x}) hs
    have hs0 := holeRatio_nonneg w hw (S \ {a,x})
    have hf := edge_fill_holeRatio w hw hz {z,p,a,x} a z (by simp) (by simp) haz
    have he : ({z,p,a,x} : Finset V) \ {a,z} = {p,x} := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      grind
    rw [he] at hf
    have hf' : B * holeRatio w {z,p,a,x} ≤ 4 := by
      exact ((mul_le_mul_of_nonneg_right hBa (holeRatio_nonneg w hw _)).trans hf).trans
        ((holeRatio_le_rowMax hcard w p x hxp.symm).trans (hrhi p))
    dsimp [F]
    rw [ht, symmDiff_pair_of_mem_mem S a x ha hxS]
    have hm := mul_le_mul hs4 hf' (mul_nonneg hB.le (holeRatio_nonneg w hw _))
      (by norm_num : (0:ℝ) ≤ 4)
    nlinarith only [hm]
  have hRsub : R ⊆ S.erase a := by
    intro x hx
    dsimp [R] at hx
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_erase]
    grind
  have hRcard : R.card ≤ 3 := by
    have h := Finset.card_le_card hRsub
    have hc := Finset.card_erase_add_one ha
    omega
  have hsum : B * ∑ x ∈ R, F x ≤ 48 := by
    rw [Finset.mul_sum]
    calc
      ∑ x ∈ R, B * F x ≤ ∑ _x ∈ R, (16:ℝ) := Finset.sum_le_sum hFx
      _ = (R.card:ℝ) * 16 := by simp
      _ ≤ 48 := by exact_mod_cast (by omega : R.card * 16 ≤ 48)
  have hmain : B * holeRatio w S * rowMax hcard w z ≤
      B * holeRatio w (insert z (S.erase a)) * rowMax hcard w a + 96 := by
    have hm := mul_le_mul_of_nonneg_left hcmp' hB.le
    have hmz := mul_le_mul_of_nonneg_left hFz hB.le
    nlinarith only [hm, hmz, hFp, hsum]
  have hprod := mul_le_mul (hrlo a) (hrlo z) (by norm_num : (0:ℝ) ≤ 1/8)
    (le_of_lt (hrap a))
  apply (div_le_iff₀ (hrap a)).mpr
  apply (mul_le_mul_iff_left₀ (mul_pos hB (hrap z))).mp
  have he :
      ((holeRatio w (insert z (S.erase a)) / rowMax hcard w z + 6144 / B) *
        rowMax hcard w a) * (B * rowMax hcard w z) =
      B * holeRatio w (insert z (S.erase a)) * rowMax hcard w a +
        6144 * rowMax hcard w a * rowMax hcard w z := by
    field_simp [ne_of_gt (hrap z), ne_of_gt hB]
  rw [he]
  nlinarith only [hmain, hprod]

theorem normalized_path_relocation [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard w a)
    (hrhi : ∀ a, rowMax hcard w a ≤ 4)
    (B : ℝ) (hB8 : 8 < B) (L : List V) (a : V)
    (S : Finset V) (hS : S.card = 2 ∨ S.card = 4) (ha : a ∈ S)
    (hpath : List.IsChain (fun x y => B ≤ edgeActivity w x y) (a :: L))
    (hnodup : (a :: L).Nodup) (hend : ∃ j ∈ L, j ∈ S) :
    holeRatio w S / rowMax hcard w a ≤ 6144 * L.length / B := by
  have hB : 0 < B := by linarith
  induction L generalizing a S with
  | nil => simp at hend
  | cons z L ih =>
    obtain ⟨hazL, hnd⟩ := List.nodup_cons.mp hnodup
    have haz : a ≠ z := fun h => hazL (by simp [h])
    obtain ⟨hBa, hp⟩ := List.isChain_cons_cons.mp hpath
    by_cases hzS : z ∈ S
    · have hf := adjacent_hole_fill hcard w hw hz hrlo hrhi S hS a z ha hzS haz B hB hBa
      apply hf.trans
      apply (div_le_div_iff_of_pos_right hB).mpr
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      have hlen : (0:ℝ) ≤ L.length := Nat.cast_nonneg _
      linarith
    · let T := insert z (S.erase a)
      have hT : T.card = 2 ∨ T.card = 4 := by
        dsimp [T]
        rw [relocated_card S a z ha hzS]
        exact hS
      have he : ∃ j ∈ L, j ∈ T := by
        obtain ⟨j,hj,hjS⟩ := hend
        have hjz : j ≠ z := fun h => hzS (h ▸ hjS)
        have hja : j ≠ a := fun h => hazL (h ▸ hj)
        refine ⟨j, ?_, ?_⟩
        · simpa [hjz] using hj
        · simp [T, hja, hjS]
      have hi := ih z T hT (by simp [T]) hp hnd he
      have hs := normalized_relocation hcard w hw hz hrlo hrhi S hS a z ha hzS B hB8 hBa
      calc
        holeRatio w S / rowMax hcard w a ≤
          holeRatio w T / rowMax hcard w z + 6144 / B := hs
        _ ≤ 6144 * (L.length:ℝ) / B + 6144 / B := add_le_add hi le_rfl
        _ = 6144 * ((z :: L).length:ℝ) / B := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

theorem hole_relocation_of_strong_path [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard w a)
    (hrhi : ∀ a, rowMax hcard w a ≤ 4)
    (B : ℝ) (hB : 0 < B) (S : Finset V) (hS : S.card = 2 ∨ S.card = 4)
    (a : V) (ha : a ∈ S)
    (hpath : 8 < B → ∃ L : List V,
      List.IsChain (fun x y => B ≤ edgeActivity w x y) (a :: L) ∧
      (a :: L).Nodup ∧ ∃ j ∈ L, j ∈ S) :
    holeRatio w S ≤ 100000 * Fintype.card V / B := by
  by_cases hB8 : 8 < B
  · obtain ⟨L,hp,hn,he⟩ := hpath hB8
    have hb := normalized_path_relocation hcard w hw hz hrlo hrhi B hB8 L a S hS ha hp hn he
    have hra : 0 < rowMax hcard w a := by linarith [hrlo a]
    have hb' := (div_le_iff₀ hra).mp hb
    have hlen : L.length ≤ Fintype.card V := by
      have h := Finset.card_le_card (Finset.subset_univ (a :: L).toFinset)
      rw [List.toFinset_card_of_nodup hn, Finset.card_univ] at h
      simpa using Nat.le_trans (Nat.le_succ L.length) h
    have hlenR : (L.length:ℝ) ≤ Fintype.card V := by exact_mod_cast hlen
    apply (le_div_iff₀ hB).mpr
    have hmul := mul_le_mul_of_nonneg_right hb' hB.le
    have heq : (6144 * (L.length:ℝ) / B * rowMax hcard w a) * B =
        6144 * (L.length:ℝ) * rowMax hcard w a := by field_simp
    rw [heq] at hmul
    have hm := mul_le_mul_of_nonneg_left (hrhi a)
      (by positivity : (0:ℝ) ≤ 6144 * (L.length:ℝ))
    have hn0 : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith only [hmul,hm,hlenR,hn0]
  · have hc := small_holes_le_fortyeight hcard w hw hz hrhi S (by omega)
    have hn : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
    have hg0 := holeRatio_nonneg w hw S
    apply (le_div_iff₀ hB).mpr
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hB8) hg0
    nlinarith only [hc,hm,hn]

noncomputable def pathStrength [LinearOrder V] (w : V → V → ℝ) {a b : V}
    (hab : a ≠ b) (p : (⊤ : SimpleGraph V).Path a b) : ℝ :=
  p.val.darts.toFinset.inf' (by
    obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil p.val.darts
      (fun h => hab ((SimpleGraph.Walk.darts_eq_nil.mp h).eq))
    exact ⟨d,List.mem_toFinset.mpr hd⟩)
    (fun d => edgeActivity w d.fst d.snd)

noncomputable def bottleneck [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : ℝ :=
  if hab : a = b then 1 else
    max 1 ((Finset.univ : Finset ((⊤ : SimpleGraph V).Path a b)).sup'
      (by exact ⟨SimpleGraph.Path.singleton (by simpa using hab), Finset.mem_univ _⟩)
      (pathStrength w hab))

theorem one_le_bottleneck [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : 1 ≤ bottleneck w a b := by
  unfold bottleneck
  split_ifs
  · rfl
  · exact le_max_left _ _

theorem walk_isChain_of_darts [LinearOrder V] {G : SimpleGraph V}
    (w : V → V → ℝ) (B : ℝ) {a b : V} (p : G.Walk a b)
    (h : ∀ d ∈ p.darts, B ≤ edgeActivity w d.fst d.snd) :
    List.IsChain (fun x y => B ≤ edgeActivity w x y) p.support := by
  induction p with
  | nil => simp
  | @cons a c b hadj p ih =>
    rw [SimpleGraph.Walk.support_cons, ← p.cons_tail_support]
    apply List.isChain_cons_cons.mpr
    constructor
    · exact h ⟨(a,c),hadj⟩ (by simp)
    · rw [p.cons_tail_support]
      apply ih
      intro d hd
      exact h d (by simp [hd])

theorem bottleneck_path [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) (hab : a ≠ b) (hB : 1 < bottleneck w a b) :
    ∃ L : List V,
      List.IsChain (fun x y => bottleneck w a b ≤ edgeActivity w x y) (a :: L) ∧
      (a :: L).Nodup ∧ b ∈ L := by
  obtain ⟨p,hp,hmax⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ : Finset ((⊤ : SimpleGraph V).Path a b)).Nonempty from
      ⟨SimpleGraph.Path.singleton (by simpa using hab), Finset.mem_univ _⟩)
    (pathStrength w hab)
  have he : bottleneck w a b = pathStrength w hab p := by
    unfold bottleneck at hB ⊢
    rw [dite_eq_right hab, hmax] at hB ⊢
    exact max_eq_right ((lt_max_iff.mp hB).resolve_left (lt_irrefl 1)).le
  have hd : ∀ d ∈ p.val.darts, bottleneck w a b ≤ edgeActivity w d.fst d.snd := by
    intro d hd
    rw [he]
    exact Finset.inf'_le _ (List.mem_toFinset.mpr hd)
  refine ⟨p.val.support.tail, ?_, ?_, ?_⟩
  · rw [p.val.cons_tail_support]
    exact walk_isChain_of_darts w _ p.val hd
  · rw [p.val.cons_tail_support]
    exact p.property.support_nodup
  · exact p.val.end_mem_tail_support_of_ne hab

theorem edgeActivity_mono [LinearOrder V] (w u : V → V → ℝ)
    (h : ∀ a b, w a b ≤ u a b) (a b : V) : edgeActivity w a b ≤ edgeActivity u a b := by
  unfold edgeActivity
  split_ifs <;> apply h

theorem hole_relocation [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w u : V → V → ℝ)
    (hu : ∀ v z, 0 ≤ u v z) (hz : 0 < partition u ∅)
    (hwu : ∀ a b, w a b ≤ u a b)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hcard u a)
    (hrhi : ∀ a, rowMax hcard u a ≤ 4)
    (S : Finset V) (hS : S.card = 2 ∨ S.card = 4)
    (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    holeRatio u S ≤ 100000 * Fintype.card V / bottleneck w a b := by
  apply hole_relocation_of_strong_path hcard u hu hz hrlo hrhi
    (bottleneck w a b) (lt_of_lt_of_le (by norm_num) (one_le_bottleneck w a b)) S hS a ha
  intro hs
  obtain ⟨L,hp,hn,hbL⟩ := bottleneck_path w a b hab (by linarith)
  refine ⟨L, ?_,hn,b,hbL,hb⟩
  exact hp.imp fun {x y} h => h.trans (edgeActivity_mono w u hwu x y)

noncomputable def erasePair (m : Mate V) (a b : V) : Mate V := by
  classical
  by_cases h : m.1 a = b
  · refine ⟨fun v => if v = a ∨ v = b then v else m.1 v, ?_⟩
    intro v
    have hba : m.1 b = a := by rw [← h, mate_mate]
    by_cases hv : v = a ∨ v = b
    · simp [hv]
    · have hma : m.1 v ≠ a := by
        intro he
        have hh := congrArg m.1 he
        rw [mate_mate, h] at hh
        exact hv (Or.inr hh)
      have hmb : m.1 v ≠ b := by
        intro he
        have hh := congrArg m.1 he
        rw [mate_mate, hba] at hh
        exact hv (Or.inl hh)
      simp [hv, hma, hmb, mate_mate]
  · exact m

@[simp] theorem erasePair_apply (m : Mate V) (a b v : V) (h : m.1 a = b) :
    (erasePair m a b).1 v = if v = a ∨ v = b then v else m.1 v := by
  classical
  simp [erasePair, h]

theorem erasePair_holes [DecidableEq V] (m : Mate V) (S : Finset V)
    (hm : HasHoles m S) (a b : V) (h : m.1 a = b) :
    HasHoles (erasePair m a b) (insert a (insert b S)) := by
  intro v
  rw [erasePair_apply m a b v h]
  by_cases hv : v = a ∨ v = b
  · rcases hv with rfl | rfl <;> simp
  · have hva := (not_or.mp hv).1
    have hvb := (not_or.mp hv).2
    simp [hva, hvb, hm v]

theorem withEdge_erasePair (m : Mate V) (a b : V) (h : m.1 a = b) :
    withEdge (erasePair m a b) a b = m := by
  have hba : m.1 b = a := by rw [← h, mate_mate]
  apply Subtype.ext
  funext v
  rw [withEdge_apply _ _ _ _ (by simp [h]) (by simp [h])]
  by_cases hva : v = a
  · subst v
    simp [h]
  by_cases hvb : v = b
  · subst v
    simp [hba, hva]
  simp [hva, hvb, h]

theorem erasePair_withEdge (m : Mate V) (a b : V)
    (ha : m.1 a = a) (hb : m.1 b = b) :
    erasePair (withEdge m a b) a b = m := by
  apply Subtype.ext
  funext v
  rw [erasePair_apply _ _ _ _ (by simp [ha,hb]), withEdge_apply m a b v ha hb]
  by_cases hva : v = a
  · subst v
    simp [ha]
  by_cases hvb : v = b
  · subst v
    simp [hb]
  simp [hva, hvb]

end MatchingFPRAS.Switching

end OAI
