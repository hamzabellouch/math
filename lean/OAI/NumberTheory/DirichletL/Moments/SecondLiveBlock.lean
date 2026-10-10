import OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate
import OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

def liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ):Finset (ActiveLabel S β):=
  Finset.univ.filter (fun p=>idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0)

lemma mem_liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β):
    p∈liveLabels η S β ↔ idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0:=by
  simp only [liveLabels,Finset.mem_filter,Finset.mem_univ,true_and]

lemma common_height_zero_of_not_live (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β)
    (hp:p∉liveLabels η S β):heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)=0:=by
  rw [mem_liveLabels] at hp
  push Not at hp
  by_cases hc:idealCoeff η p.val.1=0
  · simp only [heightCoeff,hc,zero_mul]
  · simp only [heightCoeff,hp hc,zero_mul,star_zero,mul_zero]

def liveRows (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O):Finset O:=
  rows.filter (fun z=>retainedWeight R
    (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0)

lemma liveRows_weight (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0:=
  (Finset.mem_filter.mp hz).2

lemma liveRows_geometry (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    0<R ∧ z≠0 ∧ 1≤normValue z ∧ normValue z≤
      4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)):=by
  obtain ⟨hr,hg,hv,hz0,h1,hbound,hmax⟩:=CenteredMomentSecondRetainedWidth.retained_geometry R
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U R rows z hz)
  exact ⟨hr,hz0,h1,hbound⟩

lemma physicalBlock_live_rows (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n:=by
  unfold physicalBlock liveRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hr:retainedWeight R
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))=0
  · simp only [hr,ne_eq,not_true_eq_false,physicalKernel,Complex.ofReal_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,ite_self]
  · simp only [hr,ne_eq,not_false_eq_true,ite_true]

lemma physicalBlock_row_split (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ) (p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter p) W K n+
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter (fun z=>¬p z)) W K n:=by
  rw [physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not _ p _).symm

theorem original_live_blocks (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H:ℝ) (hK:0<K)
    (hH:∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (liveRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)
                (retainedRows (frequencyRadius Tsec Z ξ)
                  (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)))
              W K (fun i=>(n i:ℤ)):=by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  trans ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (retainedRows (frequencyRadius Tsec Z ξ)
            (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
          W K (fun i=>(n i:ℤ))
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p hp hn
    rw [common_height_zero_of_not_live η t S β p hn,zero_mul]
  · apply Finset.sum_congr rfl
    intro p hp
    apply congrArg (fun x : ℂ => heightCoeff η t p.val.1 * star (heightCoeff η t p.val.2) * x)
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro n hn
    exact physicalBlock_live_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _

end SevenEighths.CenteredMomentSecondLiveBlock

end

end OAI
