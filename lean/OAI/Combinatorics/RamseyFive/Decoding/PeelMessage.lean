import Mathlib
import OAI.Combinatorics.RamseyFive.Probability.MeasurePreservingSplitSchedule
import OAI.Combinatorics.RamseyFive.Decoding.MetadataCodec
import OAI.Combinatorics.RamseyFive.Geometry.PeelingGeometry

namespace OAI

namespace SharpRamseyFive.Metadata
open Module GreedyTraining ProjectiveTraining MeasurePublicTable
open scoped Classical LinearAlgebra.Projectivization
variable {K V J : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype V] [Fintype (ℙ K V)] [LinearOrder J]

theorem one_peel_message (σ g P : ℝ) (hP : 0 ≤ P) (hd : finrank K V ≤ 5)
    (hσ : 100000 ≤ σ) (hq : Real.exp σ=Nat.card K)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K V)
    (X : Finset (ℙ K V)) (hX : (X.card:ℝ)=Real.exp (3*σ/2+g)) :
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    let ht : 0<t := by positivity
    let S := peelSet (P/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let raw := publicOwn (greedyList F hF (fun j=>flatPoints (Flat j)) X p)
    Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V))) ≤ Nat.card K ∧
    ∃c : TrainingCode V (listCap σ) (productCap σ) (Nat.card V),
      (∀x,messageOwn c x=raw x) ∧
      (∀L x,messageBase c L x=Real.exp (-L*(1-((S∩raw x).card:ℝ)/S.card))) := by
  dsimp only
  let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let p := peelLength (P/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  have hpc : p ≤ listCap σ := by
    by_cases hg : 0 ≤ g
    · have hlen : (p:ℝ)*Real.exp (σ+17*g/15) ≤ Real.exp (3*σ/2+g) := by
        rw [←hX,←ScoreScalars.plane_threshold_exp (σ:=σ) (g:=g) rfl rfl]
        exact peel_length_real _ F hF _ X t ht
      have he : (p:ℝ) ≤ Real.exp (σ/2-2*g/15) := by
        have hh := (le_div_iff₀ (Real.exp_pos (σ+17*g/15))).mpr hlen
        rw [←Real.exp_sub] at hh
        convert hh using 1
        congr 1
        ring
      have hp : (p:ℝ) ≤ 4*Real.exp (σ/2) := by
        have hh := he.trans (Real.exp_le_exp.mpr (by linarith : σ/2-2*g/15 ≤ σ/2))
        linarith only [hh,Real.exp_pos (σ/2)]
      exact_mod_cast hp.trans (Nat.le_ceil (4*Real.exp (σ/2)))
    · have he : ¬P/10000<g := by linarith
      have hz : p=0 := by simp only [p,peelLength,he,false_and,ite_false]
      rw [hz];exact Nat.zero_le _
  let H : Fin 0→Submodule K V := fun i=>Fin.elim0 i
  let Ps : Fin p→Submodule K V := fun i=>Flat (chosen F hF (fun j=>flatPoints (Flat j)) X i)
  have hPs : (fun i=>flatPoints (Ps i))=greedyList F hF (fun j=>flatPoints (Flat j)) X p := by rfl
  have hH : ∀x,publicOwn (fun i=>flatPoints (H i)) x=∅ := by
    intro x
    simp only [publicOwn,firstIndex,Finset.univ_eq_empty,Finset.filter_empty,
      Finset.not_nonempty_empty,↓reduceDIte]
  let c := encodeTraining σ hd (Nat.zero_le _) hpc (by simp) H Ps S
  refine ⟨?_,c,?_,?_⟩
  · rw [←hq];exact log_card_training_le σ hσ (vector_card_le_exp σ hq hd)
  · intro x
    have hc := decodeOwn_encode hd H Ps S (projective_card_le_vectors S) x
    change decodeOwn (encodeLists hd H Ps S (projective_card_le_vectors S)) x=_
    rw [hc]
    simp only [twoPublicOwn,hH,Finset.empty_union,hPs]
    rfl
  · intro L x
    have hc := decodeBaseScore_encode hd H Ps S (projective_card_le_vectors S) L x
    change decodeBaseScore (encodeLists hd H Ps S (projective_card_le_vectors S)) L x=_
    rw [hc]
    simp only [twoPublicOwn,hH,Finset.empty_union,hPs]
    rfl

end SharpRamseyFive.Metadata

end OAI
