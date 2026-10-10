import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicAssembly

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentDyadicCount

lemma indices_mono_upper (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hbc : b≤c) :
    indices a b ⊆ indices a c := by
  intro n hn
  rw [mem_indices_iff_scale a c ha (hb.trans_le hbc)]
  have h := (mem_indices_iff_scale a b ha hb n).mp hn
  exact ⟨h.1,h.2.trans (by linarith)⟩

lemma blocks_card_le (K R H nC nD : ℝ) (hH : 0<H)
    (hC : 1≤nC) (hD : 1≤nD) :
    Fintype.card (Blocks K R (H/nC) (H/nD)) ≤
      Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
        (![K,max 1 R,max 1 H,max 1 H] i))) := by
  have hcol (n : ℝ) (hn : 1≤n) : indices 1 (H/n) ⊆ indices 1 (max 1 H) := by
    apply indices_mono_upper _ _ _ (by norm_num) (div_pos hH (zero_lt_one.trans_le hn))
    exact (div_le_self hH.le hn).trans (le_max_right _ _)
  have hs (i : Fin 4) : bands K R (H/nC) (H/nD) i ⊆
      indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i) := by
    fin_cases i
    · exact Finset.Subset.refl _
    · intro n hn
      obtain ⟨hr,q,hq,hne⟩ := (mem_retainedIndices R n).mp hn
      exact retained_integral_mem R q hq n hr hne
    · exact hcol nC hC
    · exact hcol nD hD
  let f : Blocks K R (H/nC) (H/nD) →
      (∀i:Fin 4,↥(indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i))) :=
    fun x i => ⟨x i,hs i (x i).property⟩
  apply Fintype.card_le_of_injective f
  intro x y hxy
  funext i
  apply Subtype.ext
  exact congrArg (fun z => (z i).val) hxy

theorem blocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (_hCr : 0<Cr) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀K R H nC nD : ℝ,0<K → 0<H → 1≤nC → 1≤nD →
      R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := four_indices_subpower (max 1 Cr) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro K R H nC nD hK hH hnC hnD hR hHcap
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hbound : 1≤max 1 Cr*Z^(B+L) :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) hp
  have hR' : max 1 R≤max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hR.trans (mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      (Real.rpow_nonneg hz.le _) (by positivity))
  have hH' : max 1 H≤max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hHcap.trans ((Real.rpow_le_rpow_of_exponent_le hZ (by linarith : B≤B+L)).trans
      (le_mul_of_one_le_left (zero_le_one.trans hp) (le_max_left _ _)))
  have hfour := hcount ![K,1,1,1] ![K,max 1 R,max 1 H,max 1 H]
    (by intro i;fin_cases i <;> simp_all)
    (by intro i;fin_cases i <;> simp)
    (by intro i;fin_cases i
        · simpa [div_self hK.ne'] using hbound
        · simpa using hR'
        · simpa using hH'
        · simpa using hH')
  exact (show (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤
    Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
      (![K,max 1 R,max 1 H,max 1 H] i))) by
      exact_mod_cast blocks_card_le K R H nC nD hH hnC hnD).trans hfour

theorem original_blocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D : Ideal ActualEisensteinCubic.O), C≠0 → D≠0 →
      ∀(E : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
        (K R H : ℝ),0<K → 0<H → R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (Blocks (effectiveScale C D E K) R
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩ := blocks_subpower B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hcount
  intro C D hC hD E K R H hK hH hR hHcap
  have norm_one (I : Ideal ActualEisensteinCubic.O) (hI : I≠0) :
      (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hcount _ _ _ _ _ (effectiveScale_pos C D E K hK) hH
    (norm_one C hC) (norm_one D hD) hR hHcap

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI
