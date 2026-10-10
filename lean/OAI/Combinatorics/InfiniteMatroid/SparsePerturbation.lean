import OAI.Combinatorics.InfiniteMatroid.ProbeLimits

namespace OAI

section
open Set Filter Finset
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

lemma exists_strictMono_choice (P : ℕ → ℕ → Prop)
    (hP : ∀ j M, ∃ m, M ≤ m ∧ P j m) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ ∀ j, P j (m j) := by
  classical
  choose pick hpick using hP
  let m : ℕ → ℕ := Nat.rec (pick 0 0) (fun j prev ↦ pick (j+1) (prev+1))
  have he0 : m 0 = pick 0 0 := rfl
  have hes (j : ℕ) : m (j+1) = pick (j+1) (m j+1) := rfl
  refine ⟨m, strictMono_nat_of_lt_succ (fun j ↦ ?_), ?_⟩
  · rw [hes]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hpick (j+1) (m j+1)).1
  · intro j
    cases j with
    | zero => exact (hpick 0 0).2
    | succ j => exact (hpick (j+1) (m j+1)).2

lemma block_card_atTop : Tendsto (fun m ↦ ((wBlock m).card : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun m ↦ ?_) prefix_card_atTop
  have h := block_prefix_growth (le_refl m)
  exact_mod_cast (show (blockPrefix m).card ≤ (wBlock m).card by omega)

/-- A sparse collection of finite block selections with prescribed lower spikes. -/
lemma exists_small_spikes {G : Set E0} {δ : ℝ} (_hδ : 0 < δ)
    (hG : ∀ N, ∃ m, N ≤ m ∧ δ ≤ density G m)
    (b : ℕ → ℝ) (hbpos : ∀ j, 0 < b j) (hble : ∀ j, b j ≤ δ)
    (hbzero : Tendsto b atTop (𝓝 0)) (N : ℕ → ℕ) :
    ∃ P : Set E0, P ⊆ G ∧ Small P ∧ ∀ j, ∃ m, N j ≤ m ∧ b j ≤ density P m := by
  classical
  have hwzero : Tendsto (fun m ↦ (1:ℝ)/(wBlock m).card) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop block_card_atTop
  have hchoose : ∀ j M, ∃ m, M ≤ m ∧ N j ≤ m ∧ δ ≤ density G m ∧
      (1:ℝ)/(wBlock m).card ≤ b j := by
    intro j M
    obtain ⟨L,hL⟩ := eventually_atTop.mp (hwzero.eventually (gt_mem_nhds (hbpos j)))
    obtain ⟨m,hm,hGm⟩ := hG (max M (max (N j) L))
    refine ⟨m,(le_max_left _ _).trans hm,(le_max_left _ _).trans ((le_max_right _ _).trans hm),hGm,?_⟩
    exact (hL m ((le_max_right _ _).trans ((le_max_right _ _).trans hm))).le
  obtain ⟨m,hm,hmp⟩ := exists_strictMono_choice
    (fun j m ↦ N j ≤ m ∧ δ ≤ density G m ∧ (1:ℝ)/(wBlock m).card ≤ b j) hchoose
  have hwpos (j : ℕ) : (0:ℝ) < (wBlock (m j)).card := by rw [card_wBlock]; positivity
  have hselect (j : ℕ) : ∃ s : Finset E0, s ⊆ traceFinset (wBlock (m j)) G ∧
      s.card = ⌈b j * (wBlock (m j)).card⌉₊ := by
    apply Finset.exists_subset_card_eq
    apply Nat.ceil_le.mpr
    have hd := (hmp j).2.1
    change δ ≤ ((traceFinset (wBlock (m j)) G).card : ℝ) / (wBlock (m j)).card at hd
    exact (mul_le_mul_of_nonneg_right (hble j) (hwpos j).le).trans ((le_div_iff₀ (hwpos j)).mp hd)
  choose s hs hcard using hselect
  let P : Set E0 := ⋃ j, (s j : Set E0)
  have hP : P ⊆ G := by
    rintro x ⟨_,⟨j,rfl⟩,hx⟩
    exact ((mem_traceFinset _ _ _).mp (hs j hx)).2
  have hsm (j : ℕ) {x : E0} (hx : x ∈ s j) : x.1.1 = m j :=
    (mem_wBlock _ _).mp (((mem_traceFinset _ _ _).mp (hs j hx)).1)
  have htrace (j : ℕ) : traceFinset (wBlock (m j)) P = s j := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxw,hxP⟩ := mem_traceFinset _ _ _ |>.mp hx
      obtain ⟨i,hxi⟩ := mem_iUnion.mp hxP
      have he : i = j := hm.injective ((hsm i hxi).symm.trans ((mem_wBlock _ _).mp hxw))
      exact he ▸ hxi
    · intro hx
      exact (mem_traceFinset _ _ _).mpr ⟨(mem_wBlock _ _).mpr (hsm j hx), mem_iUnion.mpr ⟨j,hx⟩⟩
  have htrace0 (k : ℕ) (hk : k ∉ Set.range m) : traceFinset (wBlock k) P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxw,hxP⟩ := mem_traceFinset _ _ _ |>.mp hx
    obtain ⟨j,hxj⟩ := mem_iUnion.mp hxP
    exact hk ⟨j,(hsm j hxj).symm.trans ((mem_wBlock _ _).mp hxw)⟩
  have hden (j : ℕ) : b j ≤ density P (m j) ∧ density P (m j) ≤ 2 * b j := by
    change b j ≤ ((traceFinset (wBlock (m j)) P).card : ℝ)/(wBlock (m j)).card ∧
      ((traceFinset (wBlock (m j)) P).card : ℝ)/(wBlock (m j)).card ≤ 2 * b j
    rw [htrace, hcard]
    constructor
    · exact (le_div_iff₀ (hwpos j)).mpr (Nat.le_ceil _)
    · have hc := Nat.ceil_lt_add_one (mul_nonneg (hbpos j).le (hwpos j).le)
      have hi := (div_le_iff₀ (hwpos j)).mp (hmp j).2.2
      apply (div_le_iff₀ (hwpos j)).mpr
      nlinarith
  have hsmall : Small P := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hb2 : Tendsto (fun j ↦ 2 * b j) atTop (𝓝 0) := by simpa using hbzero.const_mul 2
    obtain ⟨J,hJ⟩ := eventually_atTop.mp (hb2.eventually (gt_mem_nhds hε))
    refine ⟨m J,fun k hk ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ density P k from finiteDensity_nonneg _ _)]
    by_cases hkr : k ∈ Set.range m
    · obtain ⟨j,rfl⟩ := hkr
      exact (hden j).2.trans_lt (hJ j (hm.le_iff_le.mp hk))
    · have hz : density P k = 0 := by simp [density,finiteDensity,htrace0 k hkr]
      rwa [hz]
  exact ⟨P,hP,hsmall,fun j ↦ ⟨m j,(hmp j).1,(hden j).1⟩⟩

lemma strictMono_intervals {N : ℕ → ℕ} (hN : StrictMono N) {n : ℕ} (hn : N 0 ≤ n) :
    ∃ j, N j ≤ n ∧ n < N (j+1) := by
  classical
  let j := Nat.findGreatest (fun j ↦ N j ≤ n) n
  refine ⟨j,Nat.findGreatest_spec (P := fun j ↦ N j ≤ n) (n := n) (Nat.zero_le n) hn,?_⟩
  by_contra! h
  exact Nat.findGreatest_is_greatest (show j < j+1 by omega)
    ((hN.id_le (j+1)).trans h) h

lemma spike_probe_bound {T X P : Set E0} (hXP : Disjoint X P) {n m : ℕ} (hnm : n ≤ m) :
    pProbe T X n + (blockPrefix n).card * (density P m - 2 * errorTail T X n) ≤
      fProbe T n (X ∪ P) := by
  have hsup := le_tailSup (dProbe_bddAbove T (X ∪ P)) hnm
  have heq : dProbe T (X ∪ P) m = dProbe T X m + density P m := by
    rw [dProbe, density, finiteDensity_union _ hXP]
    unfold dProbe density
    ring
  rw [heq] at hsup
  have hlow := (abs_le.mp ((abs_dProbe_le_errorTail T X hnm))).1
  have hinf : -errorTail T X n ≤ tailInf (dProbe T (X ∪ P)) n := by
    change -errorTail T X n ≤ sInf (dProbe T (X ∪ P) '' Ici n)
    apply le_csInf (tail_nonempty (dProbe T (X ∪ P)) n)
    rintro _ ⟨k,hk,rfl⟩
    exact ((abs_le.mp (abs_dProbe_le_errorTail T X hk)).1).trans
      (dProbe_mono T (Set.subset_union_left (s := X) (t := P)) k)
  have hp := pProbe_mono T (show X ⊆ X ∪ P from subset_union_left) n
  have ht : density P m - 2 * errorTail T X n ≤
      tailSup (dProbe T (X ∪ P)) n + tailInf (dProbe T (X ∪ P)) n := by linarith
  exact add_le_add hp (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))

lemma positive_pool_add {T X G : Set E0} (hX : SameClass T X)
    (hG : ¬ Small G) (hGX : G ⊆ Xᶜ) :
    ∃ P, P ⊆ G ∧ Small P ∧ Tendsto (fun n ↦ fProbe T n (X ∪ P)) atTop atTop := by
  classical
  obtain ⟨δ,hδ,hδG⟩ := small_iff_density hG
  let b (j : ℕ) : ℝ := δ / (j+1:ℕ)
  have hbpos : ∀ j, 0 < b j := by intro j; dsimp [b]; positivity
  have hble : ∀ j, b j ≤ δ := by
    intro j
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (j+1:ℕ))).mpr
    have : (1:ℝ) ≤ (j+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    nlinarith
  have hbzero : Tendsto b atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  let c (n : ℕ) : ℝ := (blockPrefix n).card
  let err (n : ℕ) : ℝ := |pProbe T X n| / c n + 2 * errorTail T X n + 1 / Real.sqrt (c n)
  have hE : Tendsto err atTop (𝓝 0) := by
    have hab : Tendsto (fun n ↦ |pProbe T X n| / c n) atTop (𝓝 0) := by
      simpa [c, abs_div] using (pProbe_normalized_zero hX).abs
    have hi : Tendsto (fun n ↦ (1:ℝ)/Real.sqrt (c n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp prefix_card_atTop)
    simpa only [zero_add,mul_zero,add_zero] using (hab.add ((errorTail_zero hX).const_mul 2)).add hi
  have hcut : ∀ j M, ∃ N, M ≤ N ∧ 1 ≤ N ∧ ∀ n, N ≤ n → err n ≤ b j := by
    intro j M
    obtain ⟨L,hL⟩ := eventually_atTop.mp (hE.eventually (gt_mem_nhds (hbpos j)))
    refine ⟨max M (max 1 L),le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),?_⟩
    exact fun n hn ↦ (hL n ((le_max_right _ _).trans ((le_max_right _ _).trans hn))).le
  obtain ⟨N,hN,hNcut⟩ := exists_strictMono_choice
    (fun j N ↦ 1 ≤ N ∧ ∀ n, N ≤ n → err n ≤ b j) hcut
  obtain ⟨P,hPG,hP,hspike⟩ := exists_small_spikes hδ hδG b hbpos hble hbzero (fun j ↦ N (j+1))
  refine ⟨P,hPG,hP,?_⟩
  have hXP : Disjoint X P := Set.disjoint_left.mpr (fun _ hx hp ↦ hGX (hPG hp) hx)
  have hbound : ∀ᶠ n in atTop, Real.sqrt (c n) ≤ fProbe T n (X ∪ P) := by
    filter_upwards [eventually_ge_atTop (N 0)] with n hn
    obtain ⟨j,hjn,hnj⟩ := strictMono_intervals hN hn
    obtain ⟨m,hm,hbm⟩ := hspike j
    have hs := spike_probe_bound (T := T) hXP (hnj.le.trans hm)
    have hcn : 0 < c n := by
      have hn1 : 1 ≤ n := (hNcut 0).1.trans hn
      have hprefix : 1 ≤ (blockPrefix n).card := by
        have hx : (⟨⟨0,fun _ ↦ false⟩,false⟩ : E0) ∈ blockPrefix n := (mem_prefix _ _).mpr (by change 0 < n; omega)
        exact Finset.card_pos.mpr ⟨_,hx⟩
      change (0:ℝ) < ((blockPrefix n).card : ℝ)
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hprefix)
    have he := (hNcut j).2 n hjn
    change |pProbe T X n| / c n + 2 * errorTail T X n + 1 / Real.sqrt (c n) ≤ b j at he
    have hsqrt : 0 < Real.sqrt (c n) := Real.sqrt_pos.2 hcn
    have hid : c n / Real.sqrt (c n) = Real.sqrt (c n) := by
      apply (div_eq_iff hsqrt.ne').mpr
      simpa only [pow_two] using (Real.sq_sqrt hcn.le).symm
    have hem := mul_le_mul_of_nonneg_right he hcn.le
    have hcne := hcn.ne'
    change pProbe T X n + c n * (density P m - 2 * errorTail T X n) ≤ _ at hs
    have hpabs := neg_abs_le (pProbe T X n)
    have hbmult := mul_le_mul_of_nonneg_left hbm hcn.le
    rw [add_mul, add_mul, div_mul_cancel₀ _ hcne] at hem
    have hm2 : (1 / Real.sqrt (c n)) * c n = Real.sqrt (c n) := by
      rw [one_div, inv_mul_eq_div, hid]
    rw [hm2] at hem
    nlinarith
  exact tendsto_atTop_mono' atTop hbound (Real.tendsto_sqrt_atTop.comp prefix_card_atTop)

end InfiniteMatroidCounterexample
end

end OAI
