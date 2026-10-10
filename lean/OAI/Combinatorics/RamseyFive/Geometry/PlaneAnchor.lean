import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.RadialOffException
import OAI.Combinatorics.RamseyFive.Geometry.AbsModifiedPointScore

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  (x : ℙ K V) [Fintype (RadialLine x)]

lemma plane_one_anchor (hdim : finrank K V=3)
    (F : Finset (ℙ K (Dual K V))) (l : RadialLine x) :
    (Finset.univ.filter fun H:F => l∈pencilLines x F H).card≤1 := by
  simpa only [hdim,Nat.reduceSub,Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,zero_add]
    using one_anchor_count x F l

lemma plane_two_anchor (hdim : finrank K V=3)
    (F : Finset (ℙ K (Dual K V))) (l m : RadialLine x) (hlm : l≠m) :
    (Finset.univ.filter fun H:F => l∈pencilLines x F H ∧ m∈pencilLines x F H).card≤0 := by
  simpa only [hdim,Nat.sub_self,Finset.range_zero,Finset.sum_empty]
    using two_anchor_count x F l m hlm

lemma plane_pencil_disjoint (hdim : finrank K V=3)
    (F : Finset (ℙ K (Dual K V))) {H H' : F} (hne : H≠H') :
    Disjoint (pencilLines x F H) (pencilLines x F H') := by
  apply Finset.disjoint_left.mpr
  intro l hl hl'
  have he := Finset.card_le_one.mp (plane_one_anchor x hdim F l) H
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩) H'
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl'⟩)
  exact hne he

lemma plane_overlap_zero (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) {H H' : F} (hne : H≠H') :
    mass (radialWeight x X δ) (pencilLines x F H∩pencilLines x F H')=0 := by
  rw [Finset.disjoint_iff_inter_eq_empty.mp (plane_pencil_disjoint x hdim F hne)]
  exact Finset.sum_empty

lemma plane_relation_sub_eq (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) {t : ℝ} (ht : 0<t)
    {H H' : F} (hh : AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) t H H') : H=H' := by
  by_contra he
  unfold AmbientEnumeration.overlapRelation at hh
  rw [plane_overlap_zero x hdim X δ F he] at hh
  exact (not_lt_of_ge ht.le) hh

theorem plane_ambient_moment (hdim : finrank K V=3)
    (X : Finset {y : ℙ K V // x≠y}) (δ L : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H)
    (B b base D₀ : ℝ) (hB : 0<B) (hb : 1≤b) (hD : 0≤D₀)
    (hL : 10000≤(L:ℝ)) (hbase : 23/25≤base)
    (hm : ∀H:F,mass (radialWeight x X δ) (pencilLines x F H)≤2)
    (hlower : ∀H:F,3/4 ≤ mass (radialWeight x X δ) (pencilLines x F H))
    (hdelta : ∀H:F,|mass (radialWeight x X δ) (pencilLines x F H)-base|≤17/100)
    {p : ℕ} (hp : 0<p) (R h : ℕ) (hKR : 200≤R/2) (hh : 0<h)
    (hsize : h≤(R/2)/(2*200)) (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (own : F→Fin R→Bool)
    (hDsum : (∑H:F,|mass (radialWeight x X δ) (pencilLines x F H)-base|^(R/2))≤D₀)
    (hcost : D₀+2*((p+1:ℝ)*lowMomentBudget (Nat.card K+1) 0 0 B b L p R 1 0)≤
      B*Real.exp (((L:ℝ)*R)/5))
    (hp2 : (p:ℝ)^2≤Real.exp (((L:ℝ)*R)/10))
    (hA : 1≤B*Real.exp (-((L:ℝ)*R)))
    (hpair : (Nat.card K:ℝ)+1≤B^2*Real.exp (((L:ℝ)*R)/10)) :
    (∫ω,(∑H:F,scoreTerm (pencilLines x F H) (Real.exp (-(L:ℝ)*base)) (own H)
      (fun r d => ω (r,d)))^p
      ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x X δ i.2))≤
      B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))) := by
  let Q : ℝ := (Nat.card K:ℝ)+1
  let C : ℝ := lowMomentBudget Q 0 0 B b L p R 1 0
  have hQ : 0≤Q := by dsimp [Q];positivity
  have hC := lowMomentBudget_bounds Q 0 0 B b L p R 1 0 hQ (le_refl _) (le_refl _)
    hB (zero_le_one.trans hb) L.coe_nonneg
  have hQsize : (F.card:ℝ)≤Q := by
    have hh := pencil_size x F hF
    simp only [hdim,Nat.reduceSub,Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,zero_add] at hh
    dsimp [Q]
    exact_mod_cast (hh.trans_eq (Nat.add_comm 1 _))
  have hPow : (∑z:DistinctPairs F,strength (pencilLines x F) (radialWeight x X δ) z^200)≤0 := by
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro z _
    have hz := plane_overlap_zero x hdim X δ F z.2.property.symm
    change (mass _ _)^200=0
    rw [hz]
    norm_num
  have hrows (H:F) : (∑H':F,offRow x X δ F H H'^200)≤0 := by
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro H' _
    unfold offRow
    by_cases he : H=H'
    · simp [he]
    · simp only [he,ite_false]
      rw [plane_overlap_zero x hdim X δ F he]
      norm_num
  have hmassL (H:F) : (∑d∈pencilLines x F H,((L*radialWeight x X δ d:ℝ≥0):ℝ))≤2*(L:ℝ) := by
    simpa only [mass,NNReal.coe_mul,Finset.mul_sum,mul_comm (L:ℝ) 2] using
      mul_le_mul_of_nonneg_left (hm H) L.coe_nonneg
  have ht : 0<1/(100*(p:ℝ)) := by positivity
  have hΔ (H:F) : Fintype.card {H':F // AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))) H H'}≤1 := by
    apply Fintype.card_le_one_iff.mpr
    intro u v
    apply Subtype.ext
    exact (plane_relation_sub_eq x hdim X δ F ht u.property).symm.trans
      (plane_relation_sub_eq x hdim X δ F ht v.property)
  have hRelPairs : (Fintype.card (ComponentEnumeration.RelatedPair (AmbientEnumeration.overlapRelation
      (radialWeight x X δ) (pencilLines x F) (1/(100*(p:ℝ))))):ℝ)≤B^2*Real.exp (((L:ℝ)*R)/10) := by
    apply (strong_pairs_le x X δ F _).trans
    have he : (Finset.univ.filter fun z:DistinctPairs F =>
        1/(100*(p:ℝ))≤ strength (pencilLines x F) (radialWeight x X δ) z).card=0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro z _
      change ¬1/(100*(p:ℝ)) ≤ mass _ _
      rw [plane_overlap_zero x hdim X δ F z.2.property.symm]
      exact not_le.mpr ht
    rw [he,Nat.cast_zero,add_zero]
    exact hQsize.trans hpair
  apply AmbientEnumeration.ambient_untruncated_moment (radialWeight x X δ) (pencilLines x F)
    hp R own L B b (2*(L:ℝ)) C D₀ base B hL hbase hlower hdelta hB hb (by positivity)
    hC.1 hD hB.le hmassL 200 h 1 0 (by norm_num) hKR hh hsize herr
    (plane_one_anchor x hdim F) (plane_two_anchor x hdim F) ?_ ?_ ?_ hDsum hcost hp2 1 hΔ
    (by simpa using hA) hRelPairs
  · exact (score_certificate_majorant x X δ L F p R 200 1 0 Q 0 B b hB (zero_le_one.trans hb)
      hQsize (le_refl _) hm hPow).trans hC.2.1
  · intro H
    exact (shift_row_from_power x X δ F H p 200 (by norm_num) 0 (hrows H)).trans hC.2.2.1
  · exact (shift_pair_from_power x X δ F p 200 0 hPow).trans
      ((add_le_add hQsize (le_refl _)).trans hC.2.2.2)

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Finite K] in
theorem unsampled_untruncated_tail (S O : Finset (ℙ K V)) (L δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀H∈F,Incident x H) {R : ℕ}
    {b t B : ℝ} (hb : b∈Set.Icc 0 1) {p : ℕ} (hp : Even p) (ht : 0<t)
    (hB : ∀own : F→Fin R→Bool,
      (∫ω,(∑H:F,scoreTerm (pencilLines x F H) b (own H) (fun r d => ω (r,d)))^p
        ∂batchMeasure (fun i : Fin R×RadialLine x => L*radialWeight x (outsideAt x S O) δ i.2))≤B) :
    (scheduleMeasure (fun _ : S => L*δ) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S O F b ω|} ≤ B/t^p := by
  have hn (ω : Fin R×RadialLine x→ℕ) : HighMoment.allTrunc R (R+1) ω=1 :=
    AmbientEnumeration.allTrunc_eq_one (Nat.lt_succ_self R) ω
  have h := unsampled_score_tail x S O L δ F hF hb (R:=R) (p:=p) (J:=R+1) (B:=B) hp ht (by
    intro own
    simpa only [hn,one_mul] using hB own)
  simpa only [hn,sub_self,integral_zero,add_zero] using h

end SharpRamseyFive.ScoreGeometry

end

end OAI
