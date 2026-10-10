import Mathlib
import OAI.Geometry.CAT0Fillings.Fillings.WeightedCone

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open Foundations MassMeasure BorelRestriction CurrentOperations Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma exists_smallCell_cut (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hm : 0 < mass T)
    (o : X) {r : ℝ} (hr : 0 < r) :
    ∃ s ∈ Ioo r (2*r), IsIntegral (k+1) (restrictCurrent hT.1 (ball o s)) ∧
      mass (boundarySucc (restrictCurrent hT.1 (ball o s))) ≤
        mass (boundarySucc T)+(2/r)*mass T := by
  obtain ⟨G,hG,hG0,hGI,hgood⟩ := ae_integral_restrict hT hX
    (LipschitzWith.dist_left o).neg
  have hLeb : volume.real (Ioo (-2*r) (-r)) = r := by
    simp only [Real.volume_real_Ioo]
    rw [max_eq_left (by linarith : 0 ≤ -r-(-2*r))]
    ring
  have hbound : ∃ t ∈ Ioo (-2*r) (-r),
      (IsIntegral (k+1) (restrictCurrent hT.1 {x | t < -dist x o}) ∧
        mass (boundarySucc (restrictCurrent hT.1 {x | t < -dist x o})) ≤
          mass (restrictCurrent hT.2.2.1 {x | t < -dist x o})+G t) ∧
      G t ≤ (2/r)*mass T := by
    by_contra hn
    push Not at hn
    have hg : ∀ᵐ t ∂volume.restrict (Ioo (-2*r) (-r)),
        (2/r)*mass T ≤ G t := by
      filter_upwards [hgood.filter_mono (ae_restrict_le),ae_restrict_mem measurableSet_Ioo] with t ht hti
      exact (hn t hti ht).le
    have hi := integral_mono_ae (integrable_const ((2/r)*mass T)) hG.integrableOn hg
    rw [integral_const,smul_eq_mul] at hi
    simp only [Measure.real,Measure.restrict_apply_univ] at hi
    rw [show (volume (Ioo (-2*r) (-r))).toReal = r from hLeb] at hi
    have hab : (∫ t in Ioo (-2*r) (-r),G t) ≤ ∫ t : ℝ,G t :=
      setIntegral_le_integral hG (Eventually.of_forall hG0)
    simp only [NNReal.coe_one,one_mul] at hGI
    have he : r*((2/r)*mass T) = 2*mass T := by field_simp [hr.ne']
    rw [he] at hi
    linarith
  obtain ⟨t,ht,htgood,htG⟩ := hbound
  have he : {x : X | t < -dist x o} = ball o (-t) := by
    ext x
    simp only [mem_ofPred_eq,mem_ball]
    constructor <;> intro hx <;> linarith
  refine ⟨-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,he ▸ htgood.1,?_⟩
  rw [←he]
  apply htgood.2.trans
  apply add_le_add _ htG
  rw [restriction_mass hT.2.2.1 (by rw [he]; exact measurableSet_ball)]
  rw [←currentMassMeasure_total hT.2.2.1]
  exact measureReal_mono (subset_univ _)

lemma restrictCurrent_add_compl {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T)
    {E : Set X} (hE : MeasurableSet E) :
    restrictCurrent hT E+restrictCurrent hT Eᶜ = T := by
  funext b π
  exact restrictCurrent_complement_sum hT hE b π

lemma mass_restriction_add_compl {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E) :
    mass (restrictCurrent hT E)+mass (restrictCurrent hT Eᶜ) = mass T := by
  rw [restriction_mass hT hE,restriction_mass hT hE.compl,
    ←currentMassMeasure_total hT]
  exact measureReal_add_measureReal_compl hE

lemma integral_dist_restriction_ball_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (o : X) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x, dist o x ∂currentMassMeasure
      (restrictCurrent_isMetricCurrent hT (measurableSet_ball (x := o) (ε := r)))) ≤
      r*mass (restrictCurrent hT (ball o r)) := by
  rw [restriction_massMeasure hT measurableSet_ball,restriction_mass hT measurableSet_ball]
  calc
    _ ≤ ∫ _ in ball o r, r ∂currentMassMeasure hT := by
      apply integral_mono_ae
      · refine (integrable_const r).mono'
          (continuous_const.dist continuous_id).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_ball] with point hpoint
        exact abs_le.mpr ⟨(neg_nonpos.mpr hr).trans dist_nonneg,
          (dist_comm o point) ▸ (mem_ball.mp hpoint).le⟩
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        exact (dist_comm o x) ▸ (mem_ball.mp hx).le
    _ = _ := by
      rw [integral_const,smul_eq_mul]
      simp only [Measure.real,Measure.restrict_apply_univ]
      ring

lemma integral_dist_le_diam {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (o : X) :
    (∫ x, dist o x ∂currentMassMeasure hT) ≤ diam (univ : Set X)*mass T := by
  calc
    _ ≤ ∫ _ : X, diam (univ : Set X) ∂currentMassMeasure hT := by
      apply integral_mono
      · exact (continuous_const.dist continuous_id).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact integrable_const _
      · intro x
        exact dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
    _ = _ := by rw [integral_const,smul_eq_mul,currentMassMeasure_total]; ring

end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open Foundations MassMeasure BorelRestriction CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem finite_cell_filling (hX : IsCAT0 X) {k : ℕ} {c p r : ℝ}
    (hc : 0 ≤ c) (hp : 0 < p) (hr : 0 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ c*(mass P)^p) (F : Finset X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Functional X (k+2), ∀ hT : IsIntegral (k+2) T,
      currentMassMeasure hT.1 (⋃ o ∈ F, ball o r)ᶜ = 0 →
      ∃ R : Functional X (k+2), ∃ S : Functional X (k+3),
        IsIntegral (k+2) R ∧ IsIntegral (k+3) S ∧
        boundarySucc R = boundarySucc T ∧ boundarySucc S = T-R ∧
        mass R ≤ C*(mass T+mass (boundarySucc T))^p ∧
        mass S ≤ 2*r*mass T+diam (univ : Set X)*C*(mass T+mass (boundarySucc T))^p := by
  classical
  have hzero : ∀ C : ℝ, 0 ≤ C → ∀ T : Functional X (k+2), ∀ hT : IsIntegral (k+2) T,
      mass T = 0 → ∃ R : Functional X (k+2), ∃ S : Functional X (k+3),
        IsIntegral (k+2) R ∧ IsIntegral (k+3) S ∧
        boundarySucc R = boundarySucc T ∧ boundarySucc S = T-R ∧
        mass R ≤ C*(mass T+mass (boundarySucc T))^p ∧
        mass S ≤ 2*r*mass T+diam (univ : Set X)*C*(mass T+mass (boundarySucc T))^p := by
    intro C hC T hT hm
    have he := hT.1.eq_zero_of_mass_eq_zero hm
    subst T
    refine ⟨0,0,isIntegral_zero _,isIntegral_zero _,rfl,?_,?_,?_⟩
    · funext b π; simp [boundarySucc]
    · rw [show mass (0 : Functional X (k+2)) = 0 from mass_zero _]
      exact mul_nonneg hC (Real.rpow_nonneg (add_nonneg (mass_nonneg _) (mass_nonneg _)) _)
    · rw [show mass (0 : Functional X (k+3)) = 0 from mass_zero _]
      exact add_nonneg (mul_nonneg (by positivity) (mass_nonneg _))
        (mul_nonneg (mul_nonneg diam_nonneg hC)
          (Real.rpow_nonneg (add_nonneg (mass_nonneg _) (mass_nonneg _)) _))
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨0,le_rfl,?_⟩
    intro T hT hs
    apply hzero 0 le_rfl T hT
    rw [←currentMassMeasure_total hT.1]
    have hs' : currentMassMeasure hT.1 univ = 0 := by simpa using hs
    simp only [Measure.real,hs',ENNReal.toReal_zero]
  | @insert o F ho ih =>
    obtain ⟨C,hC,hCF⟩ := ih
    let a : ℝ := 3+2/r
    have ha : 0 < a := by dsimp [a]; positivity
    let B : ℝ := (c+C)*a^p
    have hB : 0 ≤ B := by dsimp [B]; positivity
    refine ⟨B,hB,?_⟩
    intro T hT hs
    by_cases hm0 : mass T = 0
    · exact hzero B hB T hT hm0
    have hm : 0 < mass T := lt_of_le_of_ne (mass_nonneg _) (Ne.symm hm0)
    obtain ⟨s,hsr,hA,hAb⟩ := exists_smallCell_cut hX hT hm o hr
    let E := ball o s
    have hE : MeasurableSet E := measurableSet_ball
    let A := restrictCurrent hT.1 E
    let U := restrictCurrent hT.1 Eᶜ
    have hsum : A+U = T := restrictCurrent_add_compl hT.1 hE
    have hUeq : U = T-A := eq_sub_iff_add_eq.mpr ((add_comm U A).trans hsum)
    have hU : IsIntegral (k+2) U := by rw [hUeq]; exact hT.sub hA
    have hmsum : mass A+mass U = mass T := mass_restriction_add_compl hT.1 hE
    have hUb : mass (boundarySucc U) ≤ mass (boundarySucc T)+mass (boundarySucc A) := by
      rw [hUeq,boundarySucc_sub]
      exact mass_sub_le hT.boundarySucc.1 hA.boundarySucc.1
    have hUs : currentMassMeasure hU.1 (⋃ y ∈ F, ball y r)ᶜ = 0 := by
      change currentMassMeasure (restrictCurrent_isMetricCurrent hT.1 hE.compl) _ = 0
      rw [restriction_massMeasure hT.1 hE.compl,
        Measure.restrict_apply ((isOpen_iUnion fun y => isOpen_iUnion fun (_ : y ∈ F) => isOpen_ball).measurableSet.compl)]
      apply measure_mono_null _ hs
      intro x hx
      simp only [mem_inter_iff,mem_compl_iff,mem_iUnion,Finset.mem_insert] at hx ⊢
      intro hh
      obtain ⟨y,hy,hxy⟩ := hh
      rcases hy with heq | hf
      · subst y
        apply hx.2
        exact mem_ball.mpr ((mem_ball.mp hxy).trans hsr.1)
      · exact hx.1 ⟨y,hf,hxy⟩
    obtain ⟨R₂,S₂,hR₂,hS₂,hR₂b,hS₂b,hR₂m,hS₂m⟩ := hCF U hU hUs
    obtain ⟨R₁,hR₁,hR₁b,hR₁m⟩ := hfill (boundarySucc A) hA.boundarySucc
      (boundarySucc_boundarySucc hA.1)
    have hAZ : boundarySucc (A-R₁) = 0 := by rw [boundarySucc_sub,hR₁b,sub_self]
    obtain ⟨S₁,hS₁,hS₁b,hS₁m⟩ := hX.exists_integral_filling_weighted (hA.sub hR₁) hAZ o
    have hS₁bound : mass S₁ ≤ 2*r*mass A+diam (univ : Set X)*mass R₁ := by
      apply hS₁m.trans
      apply (integral_dist_massMeasure_sub_le hA.1 hR₁.1 o).trans
      apply add_le_add _ (integral_dist_le_diam hR₁.1 o)
      apply (integral_dist_restriction_ball_le hT.1 o (by linarith [hsr.1])).trans
      exact mul_le_mul_of_nonneg_right hsr.2.le (mass_nonneg _)
    let N := mass T+mass (boundarySucc T)
    have hN : 0 ≤ N := add_nonneg (mass_nonneg _) (mass_nonneg _)
    have hAbN : mass (boundarySucc A) ≤ a*N := by
      have hmT := mass_nonneg T
      have hmB := mass_nonneg (boundarySucc T)
      have hfrac : 0 ≤ 2/r := by positivity
      dsimp [a,N]
      change mass (boundarySucc A) ≤ _ at hAb
      nlinarith
    have hUN : mass U+mass (boundarySucc U) ≤ a*N := by
      have hmA := mass_nonneg A
      have hmT := mass_nonneg T
      have hmB := mass_nonneg (boundarySucc T)
      have hfrac : 0 ≤ 2/r := by positivity
      dsimp [a,N]
      change mass (boundarySucc A) ≤ _ at hAb
      nlinarith
    have hpow : (a*N)^p = a^p*N^p := Real.mul_rpow ha.le hN
    have hR₁N : mass R₁ ≤ c*a^p*N^p := by
      apply hR₁m.trans
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hc
      rw [←hpow]
      exact Real.rpow_le_rpow (mass_nonneg _) hAbN hp.le
    have hR₂N : mass R₂ ≤ C*a^p*N^p := by
      apply hR₂m.trans
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hC
      rw [←hpow]
      exact Real.rpow_le_rpow (add_nonneg (mass_nonneg _) (mass_nonneg _)) hUN hp.le
    have hRN : mass R₁+mass R₂ ≤ B*N^p := by
      dsimp [B]
      nlinarith [hR₁N,hR₂N]
    have hS₂N : mass S₂ ≤ 2*r*mass U+diam (univ : Set X)*C*a^p*N^p := by
      apply hS₂m.trans
      apply add_le_add_right
      rw [mul_assoc _ (a^p) (N^p),←hpow]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (add_nonneg (mass_nonneg _) (mass_nonneg _)) hUN hp.le)
        (mul_nonneg diam_nonneg hC)
    refine ⟨R₁+R₂,S₁+S₂,hR₁.add hR₂,hS₁.add hS₂,?_,?_,?_,?_⟩
    · rw [boundarySucc_add,hR₁b,hR₂b,←boundarySucc_add,hsum]
    · rw [boundarySucc_add,hS₁b,hS₂b]
      change A-R₁+(U-R₂) = T-(R₁+R₂)
      calc
        _ = (A+U)-(R₁+R₂) := by abel
        _ = _ := congrArg (fun V : Functional X (k+2) => V-(R₁+R₂)) hsum
    · exact (mass_add_le hR₁.1 hR₂.1).trans hRN
    · apply (mass_add_le hS₁.1 hS₂.1).trans
      have hd := diam_nonneg (s := univ (α := X))
      dsimp [B]
      change mass S₁+mass S₂ ≤ 2*r*mass T+diam (univ : Set X)*((c+C)*a^p)*N^p
      nlinarith [mul_le_mul_of_nonneg_left hR₁N hd]

end CAT0Fillings
end

end OAI
