import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Entropy.UniformCutoff
import OAI.Combinatorics.RamseyFive.Geometry.DimensionTwoPublic
import OAI.Combinatorics.RamseyFive.Decoding.PeelMessage

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_three_public_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=4 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (3*σ/2+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
    let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
    (∀i,(C i).card≤(S.card:ℝ)/25) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log (Nat.card (TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))))≤q ∧
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    ∃ Good : Set (Fin N→Fin R→ℙ K (I→K)→ℕ),
      (Measure.pi (fun _ : Fin N=>scheduleMeasure
        (fun x=>if x∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)).real
         Goodᶜ ≤ Real.exp (-(Nat.card K:ℝ)) ∧
      ∀u∈Good,∃ i : Fin N,∃z : Fin (Fintype.card (ℙ K (Dual K (I→K)))+1),
        let W := publicDecoded U (messageOwn c) (messageBase c L₀) z (u i)
        W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
        (9/20:ℝ)*X.card≤((W∩X).card:ℝ) := by
  have hh := eventually_three_training_score hη hη' Cb hCb
  filter_upwards [hh,eventually_ge_atTop (100000:ℝ)] with σ hh hσ
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hFlat hcover
  dsimp only
  let t := (Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let m := peelLength (P η σ D R/10000<g) F hF (fun j=>flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let C := clippedPart S F hF (fun j=>flatPoints (Flat j)) X m
  let a := queryPart F hF (fun j=>flatPoints (Flat j)) X m
  change (∀i,(C i).card≤(S.card:ℝ)/25) → _
  intro hsmall
  have hP : 0≤P η σ D R := le_trans (by norm_num : (0:ℝ)≤1)
    ((Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1)
  have hp := hh D b τ g R L₀ q K I J F hF Flat X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hFlat hcover hsmall
  change S⊆X ∧ X.card≤2*S.card ∧ _ at hp
  obtain ⟨hSX,hret,hprob⟩ := hp
  have hret' : (X.card:ℝ)≤2*S.card := by exact_mod_cast hret
  have hSn : 0<(S.card:ℝ) := by nlinarith only [hret',hX,Real.exp_pos (3*σ/2+g)]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn)
  obtain ⟨hcost,c,hOwn,hBase⟩ := one_peel_message σ g (P η σ D R) hP
    (by rw [Module.finrank_pi,hI];norm_num) hσ (hσq.trans (by rw [hcard])) F hF Flat X hX
  have hO : ∀x,S∩messageOwn c x=C (a x) := by
    intro x
    rw [hOwn]
    exact clipped_publicOwn S F hF (fun j=>flatPoints (Flat j)) X hSX m x
  have hb' : (fun x=>Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (a x)) ∅)))=messageBase c L₀ := by
    funext x
    rw [hBase]
    have hc := clipped_publicOwn S F hF (fun j=>flatPoints (Flat j)) X hSX m x
    change S∩publicOwn (greedyList F hF (fun j=>flatPoints (Flat j)) X m) x=C (a x) at hc
    rw [hc]
    simp only [ownFraction,Finset.union_empty]
    rfl
  rw [hb'] at hprob
  have hx := score_public_implementation U S hS (hSX.trans hXU) (fun x=>C (a x))
    (messageOwn c) hO (messageBase c L₀) (exceptional S C) R L₀
    (P η σ D R) τ ((S.card:ℝ)*Real.exp (10*P η σ D R)) hP hτ.le hprob
  dsimp only at hx
  let Good := ambientSuccess S (trueScoreSuccess U S (fun x=>C (a x)) (messageBase c L₀)
    (exceptional S C) R (2*(Nat.card K:ℝ)*P η σ D R) ((S.card:ℝ)*Real.exp (10*P η σ D R)) ((9/10:ℝ)*S.card))
  refine ⟨?_,hx.1,c,{u | firstIndex Good u≠none},?_,?_⟩
  · simpa only [hcard] using hcost
  · simpa only [Set.compl_ofPred,not_not] using hx.2.1
  · intro u hu
    obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp hu
    obtain ⟨z,hz,_,hsize,hcapture⟩ := hx.2.2 u i hi
    have hz' : z<Fintype.card (ℙ K (Dual K (I→K)))+1 :=
      Nat.lt_succ_of_le (hz.trans (Finset.card_le_univ _))
    refine ⟨i,⟨z,hz'⟩,Finset.filter_subset _ _,?_,?_⟩
    · exact hsize.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hSX) (Real.exp_pos _).le)
    · have hc : ((publicDecoded U (messageOwn c) (messageBase c L₀) z (u i)∩S).card:ℝ)≤
          (publicDecoded U (messageOwn c) (messageBase c L₀) z (u i)∩X).card := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left hSX)
      linarith only [hc,hcapture,hret']

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory PoissonScore ScoreAcceptance MeasurePublicTable ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_public_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [∀x : ℙ K V,Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S⊆U → S.card≤T.card →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      100*(Nat.card K:ℝ)*P η σ D R<(S.card:ℝ) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    ∃ Good : Set (Fin N→Fin R→ℙ K V→ℕ),
      (Measure.pi (fun _ : Fin N=>scheduleMeasure
        (fun x=>if x∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)).real
         Goodᶜ ≤ Real.exp (-(Nat.card K:ℝ)) ∧
      ∀t∈Good,∃ i : Fin N,∃z : Fin (Fintype.card (ℙ K (Dual K V))+1),
        let W := publicDecoded U (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ))) z (t i)
        W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P η σ D R) ∧
        (9/10:ℝ)*S.card≤((W∩S).card:ℝ) := by
  have hh := eventually_two_empty_procedure hη hη' Cb hCb
  filter_upwards [hh,eventually_ge_atTop (10:ℝ)] with σ hh hσ
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ S U T hdim hq hr hL hb hbhi hτ hτhi hSU hST hdens hprod hn
  dsimp only
  have hP : 0≤P η σ D R := le_trans (by norm_num : (0:ℝ)≤1)
    ((Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1)
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    (lt_of_le_of_lt (mul_nonneg (by positivity : (0:ℝ)≤100*(Nat.card K:ℝ)) hP) hn))
  have hp := hh D b τ R L₀ K V S U T hdim hq hr hL hb hbhi hτ hτhi hSU hST hdens hprod hn
  have hx := score_public_implementation U S hS hSU (fun _=>∅) (fun _=>∅) (by simp)
    (fun _=>Real.exp (-(L₀:ℝ))) (exceptional S (fun _ : Unit=>∅)) R L₀
    (P η σ D R) τ ((S.card:ℝ)*Real.exp (2*P η σ D R)) hP hτ.le hp
  dsimp only at hx
  let E := exceptional S (fun _ : Unit=>∅)
  let Accept := ambientSuccess S (trueScoreSuccess U S (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ)))
    E R (2*(Nat.card K:ℝ)*P η σ D R) ((S.card:ℝ)*Real.exp (2*P η σ D R)) ((9/10:ℝ)*S.card))
  refine ⟨hx.1,{t | firstIndex Accept t≠none},?_,?_⟩
  · simpa only [Set.compl_ofPred,not_not] using hx.2.1
  · intro t ht
    obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp ht
    obtain ⟨z,hz,_,hsize,hcapture⟩ := hx.2.2 t i hi
    have hz' : z < Fintype.card (ℙ K (Dual K V))+1 :=
      Nat.lt_succ_of_le (hz.trans (Finset.card_le_univ _))
    refine ⟨i,⟨z,hz'⟩,?_,hsize,hcapture⟩
    exact Finset.filter_subset _ _

end SharpRamseyFive.ScoreGeometry

end OAI
