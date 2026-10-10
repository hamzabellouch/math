import OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate
import OAI.NumberTheory.DirichletL.Moments.SecondActiveCount
import OAI.NumberTheory.DirichletL.Moments.DyadicCount

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondBlockCount
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondWholeKernel
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondBlockAggregate CenteredMomentSecondActiveCount
open CenteredMomentSecondSectorFrequency CenteredMomentSecondRetainedRows
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondSectorColumns CenteredMomentSecondRetainedAggregate
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentDyadicCount
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentActiveSource
local notation "O" => ActualEisensteinCubic.O

lemma ideal_norm_ge_one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma sourceLower_le_upper (C D : Ideal O) (A : O) (K R H : ℝ) :
    ∀i,sourceLower C D A K i≤sourceUpper C D A K R H i := by
  intro i
  fin_cases i
  · exact le_rfl
  all_goals exact le_max_left _ _

lemma source_ratio_bound (B L Cr Z : ℝ) (hB : 0≤B) (hL : 0≤L)
    (_hCr : 0<Cr) (hZ : 1≤Z)
    (C D : Ideal O) (hC : C≠0) (hD : D≠0) (A : O) (hA : A≠0)
    (K R H : ℝ) (hK : 0<K) (hR : R≤Cr*Z^L) (hH : H≤Z^B) :
    ∀i,sourceUpper C D A K R H i/sourceLower C D A K i≤
      max 1 (4*Cr)*Z^(B+L) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hc : 1≤max 1 (4*Cr) := le_max_left _ _
  have hq : 1≤max 1 (4*Cr)*Z^(B+L) := one_le_mul_of_one_le_of_one_le hc hp
  have hN := normValue_ge_one A hA
  have hNC := ideal_norm_ge_one C hC
  have hND := ideal_norm_ge_one D hD
  have hBpow : Z^B≤Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hLpow : Z^L≤Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hH' : H≤max 1 (4*Cr)*Z^(B+L) :=
    hH.trans (hBpow.trans (le_mul_of_one_le_left (zero_le_one.trans hp) hc))
  have hR' : 4*R≤max 1 (4*Cr)*Z^(B+L) := by
    calc
      _≤4*Cr*Z^L := by linarith
      _≤max 1 (4*Cr)*Z^(B+L) :=
        mul_le_mul (le_max_right _ _) hLpow (Real.rpow_nonneg hz.le _) (by positivity)
  have hn (x d : ℝ) (hd : 1≤d) (hx : x≤max 1 (4*Cr)*Z^(B+L)) :
      max 1 (x/d)≤max 1 (4*Cr)*Z^(B+L) := by
    apply max_le hq
    apply (div_le_iff₀ (zero_lt_one.trans_le hd)).mpr
    exact hx.trans (le_mul_of_one_le_right (by positivity) hd)
  intro i
  fin_cases i
  · simpa [sourceUpper,sourceLower,
      div_self (secondEffectiveScale_pos C D hC hD A hA K hK).ne'] using hq
  · simpa [sourceUpper,sourceLower] using hn (4*R) (normValue A) hN hR'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm C) hNC hH'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm D) hND hH'

theorem sourceBlocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃D₀:ℝ,0<D₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal O),Supported C → Supported D →
      ∀(U:Finset (CommonIndex C D))(K R H:ℝ),0<K →
      R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (SourceBlocks C D U K R H):ℝ)≤D₀*Z^ε := by
  obtain ⟨D₀,hD₀,hcount⟩ := four_indices_subpower (max 1 (4*Cr)) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨D₀,hD₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hc hZ
  intro C D hC hD U K R H hK hR hH
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  exact hc _ _ (sourceLower_pos C D hC.1 hD.1 _ hA K hK)
    (sourceLower_le_upper C D _ K R H)
    (source_ratio_bound B L Cr Z hB hL hCr hZ C D hC.1 hD.1 _ hA K R H hK hR hH)

abbrev CommonSubsets (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :=
  (p : commonShell S β Y) × Finset (CommonIndex p.val.1 p.val.2)

lemma commonSubset_support (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    U.image Subtype.val⊆IdealMobiusDivisorSum.primeSupport (commonRadical C D) := by
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
  rw [commonRadical_support]
  exact Q.property

def commonSubsetLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (q : CommonSubsets S β Y) : partitionLabels S β Y :=
  ⟨(q.1.val,q.2.image Subtype.val),
    (mem_partitionLabels S β Y _).mpr ⟨q.1.property,commonSubset_support _ _ q.2⟩⟩

lemma commonSubsetLabel_injective (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Function.Injective (commonSubsetLabel S β Y) := by
  rintro ⟨p,U⟩ ⟨q,V⟩ he
  have hp : p=q := Subtype.ext (congrArg (fun x=>x.val.1) he)
  cases hp
  have hU : U=V := Finset.image_injective Subtype.val_injective (congrArg (fun x=>x.val.2) he)
  cases hU
  rfl

lemma commonSubsets_card_le (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Fintype.card (CommonSubsets S β Y)≤(partitionLabels S β Y).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (commonSubsetLabel S β Y) (commonSubsetLabel_injective S β Y)

abbrev BlockLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y K R H : ℝ) :=
  (q : CommonSubsets S β Y) × SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H

lemma blockLabels_card_eq (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y K R H : ℝ) :
    (Fintype.card (BlockLabels S β Y K R H):ℝ)=
      ∑p : commonShell S β Y,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ) := by
  calc
    _ = ∑q : CommonSubsets S β Y,
        (Fintype.card (SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H):ℝ) := by
      exact_mod_cast Fintype.card_sigma (ι:=CommonSubsets S β Y)
        (α:=fun q=>SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H)
    _ = _ := Fintype.sum_sigma _

theorem actual_block_count (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀p s₀:ℝ,0≤p → p≤B →
      ∀s:Ideal O,Squarefree s → s≠0 → Z^s₀≤(Ideal.absNorm s:ℝ) →
      ∀(S:Finset (Ideal O)) (β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → s∣I) →
      ∀K R H:ℝ,0<K → R≤Cr*Z^L → H≤Z^B →
      (∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤Z^B) →
      (Fintype.card (BlockLabels S β (Z^p) K R H):ℝ)≤C₀*Z^(p-s₀+ε) := by
  obtain ⟨C₁,hC₁,hpart⟩ := actual_partition_count B (ε/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hblocks⟩ := sourceBlocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨C₁*C₂,by positivity,?_⟩
  filter_upwards [hblocks,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro p s₀ hp hpB s hs hs0 hNs S β hmask K R H hK hR hH hsource
  have hcount : (Fintype.card (CommonSubsets S β (Z^p)):ℝ)≤C₁*Z^(p-s₀+ε/2) := by
    apply (Nat.cast_le.mpr (commonSubsets_card_le S β (Z^p))).trans
    exact hpart Z p s₀ hZ hp hpB s hs hs0 hNs S β hmask hsource
  have hbc (q : CommonSubsets S β (Z^p)) :
      (Fintype.card (SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H):ℝ)≤C₂*Z^(ε/2) := by
    have hd := commonLabels_supported (activeSource S β) q.1.val.1 q.1.val.2
      (Finset.mem_filter.mp q.1.property).1
    exact hb _ _ hd.1 hd.2 q.2 K R H hK hR hH
  calc
    _ = ∑q : CommonSubsets S β (Z^p),
        (Fintype.card (SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H):ℝ) := by
      exact_mod_cast Fintype.card_sigma (ι:=CommonSubsets S β (Z^p))
        (α:=fun q=>SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H)
    _ ≤ ∑q : CommonSubsets S β (Z^p),C₂*Z^(ε/2) := Finset.sum_le_sum (fun q _=>hbc q)
    _ = (Fintype.card (CommonSubsets S β (Z^p)):ℝ)*(C₂*Z^(ε/2)) := by simp
    _ ≤ (C₁*Z^(p-s₀+ε/2))*(C₂*Z^(ε/2)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C₁*C₂)*Z^(p-s₀+ε) := by
      rw [mul_mul_mul_comm,←Real.rpow_add (zero_lt_one.trans_le hZ)]
      congr 2
      ring

end SevenEighths.CenteredMomentSecondBlockCount

end

end OAI
