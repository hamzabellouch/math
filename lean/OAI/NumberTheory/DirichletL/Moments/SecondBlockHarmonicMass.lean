import OAI.NumberTheory.DirichletL.Moments.SecondBlockCount
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondBlockHarmonicMass
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate CenteredMomentSourceMass
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockCount
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentOriginalCommonHarmonic
local notation "O" => ActualEisensteinCubic.O

abbrev ActiveSubsets (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  (p : ActiveLabel S β) × Finset (CommonIndex p.val.1 p.val.2)

abbrev ActiveBlocks (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :=
  (q : ActiveSubsets S β) × SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H

def pairWeight (C D : Ideal O) : ℝ := 1/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)

lemma pairWeight_nonneg (C D : Ideal O) : 0≤pairWeight C D := by
  unfold pairWeight
  positivity

def activeSubsetLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (q : ActiveSubsets S β) : Label := (q.1.val,q.2.image Subtype.val)

lemma activeSubsetLabel_injective (S : Finset (Ideal O)) (β : Ideal O→ℂ) :
    Function.Injective (activeSubsetLabel S β) := by
  rintro ⟨p,U⟩ ⟨q,V⟩ he
  have hp : p=q := Subtype.ext (congrArg (fun x=>x.1) he)
  cases hp
  have hU : U=V := Finset.image_injective Subtype.val_injective
    (congrArg (fun x=>x.2) he)
  cases hU
  rfl

lemma active_common_shell (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) (p : ActiveLabel S β) :
    p.val∈commonShell S β Y := by
  have hs := commonLabels_supported (activeSource S β) _ _ p.property
  have hn := commonLabel_norm_bounds S β Y hN _ _ p.property
  exact Finset.mem_filter.mpr ⟨p.property,
    (commonRadical_norm_le _ _ hs.1.1 hs.2.1).trans ((min_le_left _ _).trans hn.1)⟩

lemma activeSubsetLabel_mem (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) (q : ActiveSubsets S β) :
    activeSubsetLabel S β q∈partitionLabels S β Y := by
  exact (mem_partitionLabels S β Y _).mpr
    ⟨active_common_shell S β Y hN q.1,commonSubset_support _ _ q.2⟩

lemma active_mass_le_partition (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) :
    (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
      pairWeight p.val.1 p.val.2)≤
    ∑v∈partitionLabels S β Y,pairWeight v.1.1 v.1.2 := by
  have he : (∑q : ActiveSubsets S β,pairWeight q.1.val.1 q.1.val.2)=
      ∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        pairWeight p.val.1 p.val.2 := Fintype.sum_sigma _
  rw [←he]
  let f := activeSubsetLabel S β
  calc
    _ = ∑v∈Finset.univ.image f,pairWeight v.1.1 v.1.2 := by
      rw [Finset.sum_image]
      · rfl
      · exact (activeSubsetLabel_injective S β).injOn
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro v hv;obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hv
          exact activeSubsetLabel_mem S β Y hN q)
      (fun v _ _=>pairWeight_nonneg _ _)

lemma active_blocks_sum_eq (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :
    (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)=
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ)*pairWeight p.val.1 p.val.2 := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Fintype.sum_sigma _

theorem actual_active_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z → ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z^B) →
      (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        pairWeight p.val.1 p.val.2)≤C*Z^δ/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=common_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn
  apply (active_mass_le_partition S β (Z^B) hn).trans
  apply hb Z hZ seed hs hs0 (partitionLabels S β (Z^B))
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β (Z^B) v).mp hv
    have hh:=active_common_data S β seed hs hm (Z^B) v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    exact commonLabel_norm_bounds S β (Z^B) hn _ _
      (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^B) v).mp hv).1).1

theorem actual_block_harmonic_mass (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z^B) →
      ∀K R H:ℝ,0<K → R≤Cr*Z^L → H≤Z^B →
      (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C₁,hC₁,hmass⟩:=actual_active_harmonic_mass B (ε/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hblocks⟩:=sourceBlocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  filter_upwards [hblocks,Filter.eventually_ge_atTop (2:ℝ)] with Z hb hZ
  intro seed hs hs0 S β hm hn K R H hK hR hH
  have hsum:=hmass Z hZ seed hs hs0 S β hm hn
  rw [active_blocks_sum_eq]
  calc
    _ ≤ ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (C₂*Z^(ε/2))*pairWeight p.val.1 p.val.2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      have hsupp:=commonLabels_supported (activeSource S β) _ _ p.property
      exact mul_le_mul_of_nonneg_right
        (hb _ _ hsupp.1 hsupp.2 U K R H hK hR hH) (pairWeight_nonneg _ _)
    _ = (C₂*Z^(ε/2))*(∑p : ActiveLabel S β,
        ∑U : Finset (CommonIndex p.val.1 p.val.2),pairWeight p.val.1 p.val.2) := by
      simp only [Finset.mul_sum]
    _ ≤ (C₂*Z^(ε/2))*(C₁*Z^(ε/2)/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (C₂*C₁)*Z^ε/(seed.absNorm:ℝ) := by
      calc
        _ = (C₂*C₁)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ) := by ring
        _ = _ := by rw [←Real.rpow_add (by linarith : 0<Z),add_halves]

theorem actual_original_block_harmonic_mass (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι] (s:CenteredMomentCommonRadialData.Input ι),
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ∀puncture seed:Ideal O,Squarefree seed → seed≠0 →
      ∀K R H:ℝ,0<K → R≤Cr*Z^L → H≤Z^B →
      (∑q : ActiveBlocks (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s puncture seed) K R H,pairWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=actual_block_harmonic_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with Z hZ
  intro ι inst inst' s hz₁ hz₂ hcap puncture seed hs hs0 K R H hK hR hH
  exact hZ seed hs hs0 _ _
    (fun I _ hI=>original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap)
    K R H hK hR hH

end SevenEighths.CenteredMomentSecondBlockHarmonicMass

end

end OAI
