import OAI.Combinatorics.FiniteCircle.OffsetRecovery

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem exists_disjoint_pair_subfamily {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (f g : ι → J) (hf : Function.Injective f) (hg : Function.Injective g)
    (I : Finset ι) (hne : ∀ i ∈ I, f i ≠ g i) :
    ∃ S ⊆ I, I.card ≤ 3*S.card ∧ ∀ i ∈ S, ∀ j ∈ S, f i ≠ g j := by
  induction I using Finset.strongInductionOn
  rename_i I ih
  by_cases he : I.Nonempty
  · obtain ⟨k, hk⟩ := he
    let N := I.filter (fun i => i = k ∨ f i = g k ∨ g i = f k)
    let T := I \ N
    have hkN : k ∈ N := Finset.mem_filter.mpr ⟨hk, Or.inl rfl⟩
    have hN : N ⊆ I := Finset.filter_subset _ _
    have hT : T ⊂ I := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, by
      intro heq
      have hmem : k ∈ T := heq.symm ▸ hk
      exact (Finset.mem_sdiff.mp hmem).2 hkN⟩
    have hca : (I.filter (fun i => f i = g k)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact hf ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    have hcb : (I.filter (fun i => g i = f k)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact hg ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    have hsub : N ⊆ {k} ∪ I.filter (fun i => f i = g k) ∪ I.filter (fun i => g i = f k) := by
      intro i hi
      obtain ⟨hi, hn⟩ := Finset.mem_filter.mp hi
      rcases hn with rfl | ha | hb
      · simp
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, ha⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, hb⟩)
    have hNc : N.card ≤ 3 := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ({k} ∪ I.filter (fun i => f i = g k)) (I.filter (fun i => g i = f k))
      have h3 := Finset.card_union_le ({k} : Finset ι) (I.filter (fun i => f i = g k))
      simp only [Finset.card_singleton] at h3
      omega
    obtain ⟨S, hST, hc, hcross⟩ := ih T hT (fun i hi => hne i (Finset.sdiff_subset hi))
    have hkS : k ∉ S := fun hks => (Finset.mem_sdiff.mp (hST hks)).2 hkN
    refine ⟨insert k S, Finset.insert_subset_iff.mpr ⟨hk, hST.trans Finset.sdiff_subset⟩, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hkS]
      have hIc : T.card = I.card - N.card := Finset.card_sdiff_of_subset hN
      have hNi := Finset.card_le_card hN
      omega
    · intro i hi j hj
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        rcases Finset.mem_insert.mp hj with hj | hj
        · subst j
          exact hne k hk
        · intro hh
          have hjI := (Finset.mem_sdiff.mp (hST hj)).1
          have hjN := (Finset.mem_sdiff.mp (hST hj)).2
          exact hjN (Finset.mem_filter.mpr ⟨hjI, Or.inr (Or.inr hh.symm)⟩)
      · rcases Finset.mem_insert.mp hj with hj | hj
        · subst j
          intro hh
          have hiI := (Finset.mem_sdiff.mp (hST hi)).1
          have hiN := (Finset.mem_sdiff.mp (hST hi)).2
          exact hiN (Finset.mem_filter.mpr ⟨hiI, Or.inr (Or.inl hh)⟩)
        · exact hcross i hi j hj
  · refine ⟨∅, Finset.empty_subset _, ?_, by simp⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp he]

theorem card_bit_equalities_le {ι J : Type*} [Fintype J] [DecidableEq J] [DecidableEq ι]
    (I : Finset ι) (f g : ι → J) (hg : Function.Injective g)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, f i ≠ g j) :
    (Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ I, ω (f i) = ω (g i))).card ≤
      2 ^ (Fintype.card J - I.card) := by
  classical
  let T := I.image g
  let π : (J → Bool) → (↥(Tᶜ : Finset J) → Bool) := fun ω j => ω j.val
  have hinj : Set.InjOn π (↑(Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ I, ω (f i) = ω (g i))) : Set (J → Bool)) := by
    intro ω hω η hη he
    have hω := (Finset.mem_filter.mp hω).2
    have hη := (Finset.mem_filter.mp hη).2
    funext j
    by_cases hj : j ∈ T
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      have hf : f i ∈ Tᶜ := by
        apply Finset.mem_compl.mpr
        intro hh
        obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hh
        exact hcross i hi k hk heq.symm
      have heq : ω (f i) = η (f i) := congrFun he ⟨f i, hf⟩
      exact (hω i hi).symm.trans (heq.trans (hη i hi))
    · exact congrFun he ⟨j, Finset.mem_compl.mpr hj⟩
  have hc := Finset.card_le_card_of_injOn π (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    Finset.card_compl, Finset.card_image_of_injective I hg, T] using hc

theorem card_matching_equalities_le {ι J : Type*} [Fintype J] [DecidableEq J] [DecidableEq ι]
    (I : Finset ι) (f g : ι → J) (hf : Function.Injective f) (hg : Function.Injective g)
    (hne : ∀ i ∈ I, f i ≠ g i) (w : ℕ) (hw : w ≤ 16*I.card) :
    (Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ I, ω (f i) = ω (g i))).card ≤
      2 ^ (Fintype.card J - w/64) := by
  classical
  obtain ⟨S, hSI, hcard, hcross⟩ := exists_disjoint_pair_subfamily f g hf hg I hne
  have hsub : (Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ I, ω (f i) = ω (g i))) ⊆
      Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ S, ω (f i) = ω (g i)) := by
    intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => (Finset.mem_filter.mp hω).2 i (hSI hi)⟩
  have hh : w/64 ≤ S.card := by omega
  exact (Finset.card_le_card hsub).trans ((card_bit_equalities_le S f g hg hcross).trans
    (Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_left hh _)))

theorem card_small_subsets_le (w : ℕ) :
    ((Finset.univ.filter (fun S : Finset (Fin w) => (S.card : ℝ) ≤ (w : ℝ)/1048576)).card : ℝ) ≤
      Real.exp ((w : ℝ)/512) := by
  classical
  let K := Finset.univ.filter (fun S : Finset (Fin w) => (S.card : ℝ) ≤ (w : ℝ)/1048576)
  let z : ℝ := 1/1024
  have hz : 0 < z := by norm_num [z]
  have hlog : -1024 ≤ Real.log z := by
    have h := Real.log_le_sub_one_of_pos (x := 1024) (by norm_num)
    simp only [z, one_div, Real.log_inv]
    linarith
  have hlow (S : Finset (Fin w)) (hS : S ∈ K) : Real.exp (-(w : ℝ)/1024) ≤ z^S.card := by
    have hs := (Finset.mem_filter.mp hS).2
    have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg S.card)
    have he : -(w : ℝ)/1024 ≤ (S.card : ℝ)*Real.log z := by nlinarith
    have h := Real.exp_le_exp.mpr he
    simpa only [Real.exp_nat_mul, Real.exp_log hz] using h
  have htotal : ∑ S : Finset (Fin w), z^S.card = (z+1)^w := by
    simpa using Finset.sum_pow_mul_eq_add_pow z (1 : ℝ) (Finset.univ : Finset (Fin w))
  have hsum : (K.card : ℝ) * Real.exp (-(w : ℝ)/1024) ≤ (z+1)^w := calc
    _ = ∑ _S ∈ K, Real.exp (-(w : ℝ)/1024) := by simp
    _ ≤ ∑ S ∈ K, z^S.card := Finset.sum_le_sum hlow
    _ ≤ ∑ S : Finset (Fin w), z^S.card := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => pow_nonneg hz.le _)
    _ = _ := htotal
  have hupper : (z+1)^w ≤ Real.exp ((w : ℝ)/1024) := by
    have hl := Real.log_le_sub_one_of_pos (x := z+1) (by positivity)
    have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg w)
    have hh : (w : ℝ)*Real.log (z+1) ≤ (w : ℝ)/1024 := by dsimp [z] at *; nlinarith
    have hh := Real.exp_le_exp.mpr hh
    simpa only [Real.exp_nat_mul, Real.exp_log (show 0 < z+1 by positivity)] using hh
  calc
    (K.card : ℝ) ≤ (z+1)^w / Real.exp (-(w : ℝ)/1024) := (le_div_iff₀ (Real.exp_pos _)).mpr hsum
    _ ≤ Real.exp ((w : ℝ)/1024) / Real.exp (-(w : ℝ)/1024) := div_le_div_of_nonneg_right hupper (Real.exp_pos _).le
    _ = Real.exp ((w : ℝ)/512) := by rw [← Real.exp_sub]; congr 1; ring

end FiniteCircle

end OAI
