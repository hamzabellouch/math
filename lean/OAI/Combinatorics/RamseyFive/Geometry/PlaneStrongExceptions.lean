import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Decoding.Training
import OAI.Combinatorics.RamseyFive.Geometry.PeelingGeometry
import OAI.Combinatorics.RamseyFive.Probability.UniformTails

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [∀x : ℙ K V,Fintype (RadialLine x)]

omit [∀x : ℙ K V,Fintype (RadialLine x)] in
lemma captured_global_rich {I : Type} [LinearOrder I]
    (F : Finset I) (hF : F.Nonempty) (Flat : I→Submodule K V)
    (X S : Finset (ℙ K V)) (hFlat : ∀i∈F,finrank K (Flat i)=3) (j : ℕ)
    (hS : S⊆X\remaining F hF (fun i => flatPoints (Flat i)) X j)
    (hj : (j:ℝ)*(Nat.card K:ℝ) ≤ X.card)
    (O : ℙ K V→Finset (ℙ K V))
    (hO : ∀x,ownCell F hF (fun i => flatPoints (Flat i)) X j x⊆O x)
    (δ : ℝ≥0) (hδ : 0<δ) (a : ℝ) (hacut : 8*(δ:ℝ)*(j+1) ≤ a)
    (hmass : (δ:ℝ)*X.card ≤ 4*Nat.card K)
    (Lines : Finset (Submodule K V)) (hLines : ∀l∈Lines,finrank K l=2) :
    (∑l∈Lines,((richCenters S O δ a l).card:ℝ))*a^2 ≤ 3072*(Nat.card K:ℝ)^2 := by
  have hδ' : 0<(δ:ℝ) := hδ
  have ha4 : 4*(δ:ℝ) ≤ a := by nlinarith only [hacut,hδ',(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  obtain ⟨M,hM,hlo,hhi⟩ := exists_scale hδ' ha4
  have hjM : j ≤ M := by
    have hh : (j:ℝ) ≤ M := by nlinarith only [hacut,hhi,hδ']
    exact_mod_cast hh
  have hm := captured_rich_centers F hF Flat X hFlat Lines hLines j M hM hjM hj O hO δ a hδ' hlo hhi
  have hs : (∑l∈Lines,((richCenters S O δ a l).card:ℝ)) ≤
      ∑l∈Lines,((richCenters (X\remaining F hF (fun i => flatPoints (Flat i)) X j) O δ a l).card:ℝ) := by
    apply Finset.sum_le_sum
    intro l hl
    exact Nat.cast_le.mpr (Finset.card_le_card (richCenters_mono S _ O O δ a δ.coe_nonneg hS
      (fun _ => Finset.Subset.refl _) l))
  apply ((mul_le_mul_of_nonneg_right hs (sq_nonneg a)).trans hm).trans
  nlinarith only [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (δ:ℝ)*X.card) hmass 2]

end

section

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K I J : Type} [Field K] [Finite K] [Fintype I] [LinearOrder J]
  [∀x : ℙ K (I→K),Fintype (RadialLine x)]

omit [∀x : ℙ K (I→K),Fintype (RadialLine x)] in
theorem literal_plane_global_rich {q : ℕ} [CharP K q]
    (hq : 2<q) (hcard : Nat.card K=q) (hI : Fintype.card I=4 ∨ Fintype.card I=5)
    (σ g b a : ℝ) (hσq : Real.exp σ=q) (hσ : 1000 ≤ σ)
    (hb : 100000000 ≤ b) (hen : b<g) (hghi : g ≤ 2*σ)
    (ha : Real.exp (-g/20) ≤ a) (ha2 : a ≤ 2)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
    (hFlat : ∀j∈F,finrank K (Flat j)=3)
    (hcover : ∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U)
    (X : Finset (ℙ K (I→K))) (hX : (X.card:ℝ) ≤ Real.exp (3*σ/2+g))
    (t : ℝ) (ht : t=(Real.exp (3*σ/2+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-g/5))
    (ht0 : 0<t) (S : Finset (ℙ K (I→K)))
    (hS : S=peelSet (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0))
    (hquarter : Real.exp (3*σ/2+g)/4 ≤ S.card)
    (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
    (hO : ∀x,ownCell F hF (fun j => flatPoints (Flat j)) X
      (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x)
    (δ : ℝ≥0) (hδ : (δ:ℝ)=(q:ℝ)/S.card)
    (Lines : Finset (Submodule K (I→K))) (hLines : ∀l∈Lines,finrank K l=2) :
    (∑l∈Lines,((richCenters S (fun x => S∩O x) δ a l).card:ℝ))*a^2 ≤ 333024*(q:ℝ)^2 := by
  simp only [richCenters_clip]
  have hq0 : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hn0 : 0<(S.card:ℝ) := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hquarter
  have hδ0 : 0<δ := by rw [←NNReal.coe_pos,hδ];positivity
  have hsub : S⊆X := hS▸peel_subset (b<g) F hF (fun j => flatPoints (Flat j)) X _ _
  have hSn : (S.card:ℝ) ≤ Real.exp (3*σ/2+g) := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hX
  have hscale : Real.exp (3*σ/2+g)*(δ:ℝ) ≤ 4*q := by
    rw [hδ,←mul_div_assoc]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [hquarter,hq0]
  have hg : 100000000 ≤ g := hb.trans hen.le
  have htE : t=Real.exp (σ+17*g/15) := ht.trans (ScoreScalars.plane_threshold_exp rfl rfl)
  have htq : (q:ℝ) ≤ t := by rw [htE,←hσq];apply Real.exp_le_exp.mpr;linarith only [hg]
  rcases peel_residual_real (b<g) hen F hF (fun j => flatPoints (Flat j)) X t ht0 with hcap|⟨hJ,hres⟩
  · have hc : S⊆X\remaining F hF (fun j => flatPoints (Flat j)) X
        (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) := by
      rw [hS,hcap]
    have hjt := peel_length_real (b<g) F hF (fun j => flatPoints (Flat j)) X t ht0
    have hjq : (peelLength (b<g) F hF (fun j => flatPoints (Flat j)) X ⌈t⌉₊ (Nat.ceil_pos.mpr ht0):ℝ)*(Nat.card K:ℝ) ≤ X.card := by
      rw [hcard];exact (mul_le_mul_of_nonneg_left htq (Nat.cast_nonneg _)).trans hjt
    have hcut := ScoreScalars.plane_list_cutoff (n:=Real.exp (3*σ/2+g)) (q:=(q:ℝ))
      rfl hσq.symm htE (by linarith only [hg]) hghi δ.coe_nonneg (Nat.cast_nonneg _)
      (hjt.trans hX) hscale
    have hmass : (δ:ℝ)*X.card ≤ 4*Nat.card K := by
      rw [hcard];exact (mul_le_mul_of_nonneg_left hX δ.coe_nonneg).trans (by simpa only [mul_comm] using hscale)
    have hh := captured_global_rich F hF Flat X S hFlat _ hc hjq O hO δ hδ0 a (hcut.trans ha) hmass Lines hLines
    rw [hcard] at hh
    nlinarith only [hh,sq_nonneg (q:ℝ)]
  · rw [hδ]
    apply residual_rich_centers hq hcard hI σ g S.card a hσq hσ hg hghi hquarter ha ha2 S hSn Lines hLines O
    intro U hU
    obtain ⟨j,hj,hjU⟩ := hcover U hU
    have hh := hres j hj
    rw [←hS,ht] at hh
    have he : (S.filter fun y => y.submodule ≤ U)=S∩flatPoints (Flat j) := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_inter,mem_flatPoints,hjU]
    rw [he]
    exact hh.le

omit [∀x : ℙ K (I→K),Fintype (RadialLine x)] in
lemma strong_exceptions_of_global (S : Finset (ℙ K (I→K)))
    (O : ℙ K (I→K)→Finset (ℙ K (I→K))) (δ a : ℝ)
    (Lines : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))) {C : ℝ}
    (hglobal : (∑l∈Lines,((richCenters S O δ a l).card:ℝ))*a^2 ≤ C) :
    ((badCenters S O δ a Lines Q 1).card:ℝ)*a^2 ≤ C := by
  have hh := badCenters_mass_le S O δ a Lines Q 1
  rw [mul_one] at hh
  exact (mul_le_mul_of_nonneg_right hh (sq_nonneg a)).trans hglobal

end

section
open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  (x : ℙ K V) [Fintype (RadialLine x)]

lemma plane_pair_card_zero (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) {t : ℝ} (ht : 0 < t) :
    (Finset.univ.filter fun z : DistinctPairs F => t ≤
      strength (pencilLines x F) (radialWeight x X δ) z).card=0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have he := plane_overlap_zero x hdim X δ F z.2.property.symm
  exact (not_le.mpr ht) (he▸(Finset.mem_filter.mp hz).2)

lemma plane_degree_card_zero (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H : F) {t : ℝ} (ht : 0 < t) :
    (Finset.univ.filter fun H':F => H≠H' ∧ t ≤
      mass (radialWeight x X δ) (pencilLines x F H∩pencilLines x F H')).card=0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro H' hH'
  obtain ⟨hne,hm⟩ := (Finset.mem_filter.mp hH').2
  rw [plane_overlap_zero x hdim X δ F hne] at hm
  exact (not_le.mpr ht) hm

lemma plane_validation_card_zero (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) {t : ℝ} (ht : 0 < t) :
    (Finset.univ.filter fun z : {z : F×F // z.1≠z.2} => t ≤
      mass (radialWeight x X δ) (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card=0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hm := (Finset.mem_filter.mp hz).2
  rw [plane_overlap_zero x hdim X δ F z.property] at hm
  exact (not_le.mpr ht) hm

end

open Module ProjectiveIncidence CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_two_score_tails {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (x : ℙ K V) [Fintype (RadialLine x)],
    ∀ {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (a b c : J)
      (F : Finset (ℙ K (Dual K V))) (t : ℝ),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0 ≤ b₀ → b₀ ≤ Cb*D*σ^(6*beta η) →
      τ ≤ σ^(-200*beta η) → S.Nonempty → C a⊆S → C b⊆S → C c=C a∩C b →
      (S.card:ℝ) ≤ 10*Real.exp (3*σ/2) →
      (Nat.card K:ℝ)/S.card ≤ 1/100 → ownFraction S (C a) (C b) ≤ 2/25 →
      (∀H∈F,Incident x H ∧ H∉exceptional S C) →
      x∉irregular (d:=2) S C ((L₀:ℝ)/100) →
      scale (K:=K) 2 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10 ≤ t →
      let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
      let E := {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
          (Real.exp (-(L₀:ℝ)*(1-ownFraction S (C a) (C b)))) ω|}
      μ.real E ≤ Real.exp (-P η σ D R/2) ∧ μ.real E ≤ (Nat.card K:ℝ)^(-(50:ℝ)) := by
  have ht := eventually_validation_original_tail hη hη' Cb hCb
  have ha := eventually_low_original_tail hη hη' Cb hCb
  have ho := eventually_moment_orders hη hη'
  filter_upwards [eventually_ge_atTop (100:ℝ),ht,ha,ho] with σ hσ ht ha ho
  intro D b₀ τ R L₀ K V _ _ _ _ _ _ _ x _ J _ S C a b c F t
    hdim hq hr hL hb₀ hbhi hτ hS hCa hCb hCc hSn hn hf hF hx ht₀
  dsimp only
  have hNor : (S.card:ℝ) ≤ 10*Real.exp (((2:ℝ)+1)*σ/2) := by norm_num;exact hSn
  have hP0 : 0 ≤ P η σ D R := by unfold P; rw [←hL];exact mul_nonneg L₀.coe_nonneg (Nat.cast_nonneg R)
  have hSlow : (S.card:ℝ) ≤ (Nat.card K:ℝ)^2*Real.exp (P η σ D R/10000) := by
    have he : (10:ℝ) ≤ Real.exp (σ/2) := by linarith [Real.add_one_le_exp (σ/2)]
    calc
      _ ≤ 10*Real.exp (3*σ/2) := hSn
      _ ≤ Real.exp (σ/2)*Real.exp (3*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = (Nat.card K:ℝ)^2 := by rw [hq,←Real.exp_add,←Real.exp_nat_mul];norm_num;ring
      _ ≤ _ := le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp_iff.mpr (by positivity))
  constructor
  · apply ht 2 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
      hCa hCb hCc hNor hn hf hF hx _ ht₀
    intro u hu hu2
    rw [plane_validation_card_zero x hdim _ _ F hu,Nat.cast_zero,zero_mul]
    positivity
  · apply ha 2 D b₀ τ R L₀ K V x S C a b c F t hdim (by norm_num) (by norm_num) hq hr hL hb₀ hbhi hτ hS
      hCa hCb hCc hNor hSlow hn hf hF hx _ _ _ ht₀
    · intro u hu hu2
      change ((Finset.univ.filter fun z : DistinctPairs F => u ≤ strength (pencilLines x F)
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) z).card:ℝ)*u^200 ≤ _
      rw [plane_pair_card_zero x hdim _ _ F hu,Nat.cast_zero,zero_mul]
      positivity
    · intro H u hu hu2
      rw [plane_degree_card_zero x hdim _ _ F H hu,Nat.cast_zero,zero_mul]
      unfold scale;positivity
    · intro H
      have hp : 0 < (momentOrder σ (P η σ D R):ℝ) := Nat.cast_pos.mpr (ho D R hr).2.1
      rw [plane_degree_card_zero x hdim _ _ F H (by positivity),Nat.cast_zero]
      unfold scale;positivity

end SharpRamseyFive.ScoreGeometry

end OAI
