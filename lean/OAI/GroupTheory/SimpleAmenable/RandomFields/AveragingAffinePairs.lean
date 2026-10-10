import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.FlagAveragingMatrices
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FullGroupAffineData

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AveragingAffinePairs
open Classical MeasureTheory

def SameAffineBranch {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z w : FlagTrackPoint a m v) : Prop :=
  z.1=w.1 ∧ flagAffineData g z.1 z.2=flagAffineData g w.1 w.2

theorem sameAffineBranch_inverse_iff {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z w : FlagTrackPoint a m v) :
    SameAffineBranch g⁻¹ (flagAction g z) (flagAction g w) ↔ SameAffineBranch g z w := by
  simp only [SameAffineBranch,flagAffineData_inverse,Prod.mk.injEq,neg_inj]
  rw [(flagAffineData_action g z).1,(flagAffineData_action g w).1]
  constructor
  · rintro ⟨ht,hzw,hu⟩
    exact ⟨hzw,Prod.ext ht hu⟩
  · rintro ⟨hzw,he⟩
    exact ⟨congrArg Prod.fst he,hzw,congrArg Prod.snd he⟩

theorem flagAveragingMatrix_nezero_separator {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (h : flagAveragingMatrix χ ρ N r η κ z w ≠ 0) :
    z.val.1=w.val.1 ∧ separatorMatrix (thresholdLaw (r/N) κ) z.val.2 w.val.2 ≠ 0 := by
  have ht : z.val.1=w.val.1 := by
    by_contra ht
    exact h (by simp [flagAveragingMatrix,ht])
  refine ⟨ht,fun hp => h ?_⟩
  simp [flagAveragingMatrix,hp]

theorem flagAveragingMatrix_common_branch {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) :
    ∃R : ℝ,0 ≤ R ∧ ∀(χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ),
      0 < N → 0 < r → 0 < κ → R ≤ κ/(r/N) →
      ∀z w : FlagSite a m D v,
      (flagAveragingMatrix χ ρ N r η κ z w ≠ 0 ∨
       flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w) ≠ 0) →
        SameAffineBranch g z.val w.val := by
  obtain ⟨R,hR,hcontrol⟩ := flagAffineData_separator_control (v:=v) g
  obtain ⟨T,hT,hcontrol'⟩ := flagAffineData_separator_control (v:=v) g⁻¹
  refine ⟨max R T,le_max_of_le_left hR,fun χ ρ N r η κ hN hr hκ hbound z w hm => ?_⟩
  rcases hm with hm|hm
  · obtain ⟨ht,hp⟩ := flagAveragingMatrix_nezero_separator χ ρ N r η κ z w hm
    refine ⟨ht,?_⟩
    rw [← ht]
    exact hcontrol (r/N) κ (div_pos hr hN) hκ ((le_max_left _ _).trans hbound) z.val.1 _ _ hp
  · obtain ⟨ht,hp⟩ := flagAveragingMatrix_nezero_separator χ ρ N r η κ
      (flagSiteAction hD g z) (flagSiteAction hD g w) hm
    apply (sameAffineBranch_inverse_iff g z.val w.val).mp
    refine ⟨ht,?_⟩
    change (flagAction g z.val).1=(flagAction g w.val).1 at ht
    rw [← ht]
    exact hcontrol' (r/N) κ (div_pos hr hN) hκ ((le_max_right _ _).trans hbound)
      (flagAction g z.val).1 _ _ hp

theorem planeTent_common_translation (s : ℝ) (x y b : ℝ×ℝ) :
    planeTent s (x+b) (y+b)=planeTent s x y := by
  simp only [planeTent,Prod.fst_add,Prod.snd_add,add_sub_add_right_eq_sub]

theorem sameAffineBranch_kernels {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z w : FlagSite a m D v) (hf : SameAffineBranch g z.val w.val)
    (s t : ℝ) :
    planeTent s (flagSiteOrdinary (flagSiteAction hD g z)) (flagSiteOrdinary (flagSiteAction hD g w))=
      planeTent s (flagSiteOrdinary z) (flagSiteOrdinary w) ∧
    planeTent t (flagSiteConjugate (flagSiteAction hD g z)) (flagSiteConjugate (flagSiteAction hD g w))=
      planeTent t (flagSiteConjugate z) (flagSiteConjugate w) := by
  constructor
  · change planeTent s (flagAction g z.val).2.val (flagAction g w.val).2.val=_
    rw [(flagAffineData_action g z.val).2,(flagAffineData_action g w.val).2,← hf.2]
    exact planeTent_common_translation _ _ _ _
  · rw [flagAffineData_conjugate hD,flagAffineData_conjugate hD,← hf.2]
    exact planeTent_common_translation _ _ _ _

noncomputable def affineConjugateCost (a : ℕ) (u : CutRing×CutRing) : ℝ :=
  |conjugate u.1|+|conjugate u.2|+∑j : Fin 4,|conjugate (integralCutForm a j u)|

theorem affineConjugateCost_nonneg (a : ℕ) (u : CutRing×CutRing) : 0 ≤ affineConjugateCost a u :=
  add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem flagAffineData_cost_bound {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m) :
    ∃C : ℝ,0 ≤ C ∧ ∀z : FlagTrackPoint a m v,affineConjugateCost a (flagAffineData g z.1 z.2).2 ≤ C := by
  obtain ⟨C,hC,h⟩ := flagAffineData_bounded (v:=v) g (affineConjugateCost a)
  exact ⟨C,hC,fun z => (abs_le.mp (h z)).2⟩

end AveragingAffinePairs

section AveragingEntryCovariance
open Classical MeasureTheory

theorem unit_pair_sub_bound {a b c d : ℝ}
    (hb : b∈Set.Icc (0:ℝ) 1) (hc : c∈Set.Icc (0:ℝ) 1) :
    |a*b-c*d| ≤ |a-c|+|b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| *b+c*|b-d| := by rw [abs_mul,abs_mul,abs_of_nonneg hb.1,abs_of_nonneg hc.1]
    _ ≤ _ := by nlinarith [abs_nonneg (a-c),abs_nonneg (b-d),hb.2,hc.2]

theorem unit_triple_sub_bound {a b c d e f : ℝ}
    (_ha : a∈Set.Icc (0:ℝ) 1) (hb : b∈Set.Icc (0:ℝ) 1)
    (hc : c∈Set.Icc (0:ℝ) 1) (hd : d∈Set.Icc (0:ℝ) 1)
    (he : e∈Set.Icc (0:ℝ) 1) :
    |a*b*c-d*e*f| ≤ |a-d|+|b-e|+|c-f| := by
  have hde : d*e∈Set.Icc (0:ℝ) 1 := ⟨mul_nonneg hd.1 he.1,
    (mul_le_mul hd.2 he.2 he.1 zero_le_one).trans_eq (one_mul 1)⟩
  have h₁ : |a*b*c-d*e*f| ≤ |a*b-d*e|+|c-f| := unit_pair_sub_bound hc hde
  have h₂ : |a*b-d*e| ≤ |a-d|+|b-e| := unit_pair_sub_bound hb hd
  linarith

theorem scaledSiteConjugate_action_diff {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) (N : ℝ) :
    (scaledSiteConjugate N (flagSiteAction hD g z)).1-(scaledSiteConjugate N z).1=
      conjugate (flagAffineData g z.val.1 z.val.2).2.1/N ∧
    (scaledSiteConjugate N (flagSiteAction hD g z)).2-(scaledSiteConjugate N z).2=
      conjugate (flagAffineData g z.val.1 z.val.2).2.2/N := by
  simp only [scaledSiteConjugate,flagAffineData_conjugate hD,Prod.fst_add,Prod.snd_add,add_div,add_sub_cancel_left]
  exact ⟨trivial,trivial⟩

theorem cutoff_action_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) {N L : ℝ} (hN : 0<N)
    (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    |χ (scaledSiteConjugate N z)-χ (scaledSiteConjugate N (flagSiteAction hD g z))| ≤
      L*(|conjugate (flagAffineData g z.val.1 z.val.2).2.1|+
         |conjugate (flagAffineData g z.val.1 z.val.2).2.2|)/N := by
  rw [abs_sub_comm]
  have h := hχ (scaledSiteConjugate N (flagSiteAction hD g z)) (scaledSiteConjugate N z)
  rw [(scaledSiteConjugate_action_diff hD g z N).1,(scaledSiteConjugate_action_diff hD g z N).2,
    abs_div,abs_div,abs_of_pos hN,← add_div,← mul_div_assoc] at h
  exact h

theorem flagAveragingMatrix_chart_difference {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z w : FlagSite a m D v) (hf : SameAffineBranch g z.val w.val)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {L ρ N r η κ : ℝ} (hL : 0 ≤ L) (hρ : 0<ρ) (hN : 0<N) (hr : 0<r) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    |flagAveragingMatrix χ ρ N r η κ z w-
      flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w)| ≤
      affineConjugateCost a (flagAffineData g z.val.1 z.val.2).2 * (2*L+r/κ)/(N*(ρ*(r*η)^2)) := by
  have : IsProbabilityMeasure (thresholdLaw (r/N) κ) := thresholdLaw_isProbability (div_pos hr hN) hκ
  let u := (flagAffineData g z.val.1 z.val.2).2
  let d := ρ*(r*η)^2
  have hd : 0<d := mul_pos hρ (sq_pos_of_pos (mul_pos hr hη))
  let A := |conjugate u.1|+|conjugate u.2|
  let B := ∑j : Fin 4,|conjugate (integralCutForm a j u)|
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hz := cutoff_action_bound hD g z hN χ hLip
  have hw := cutoff_action_bound hD g w hN χ hLip
  rw [← hf.2] at hw
  have hp := separatorMatrix_translation_bound (div_pos hr hN) hκ u z.val.2 w.val.2
    (flagAction g z.val).2 (flagAction g w.val).2
    (flagAffineData_action g z.val).2 (by rw [(flagAffineData_action g w.val).2,← hf.2])
  have ht : (flagSiteAction hD g z).val.1=(flagSiteAction hD g w).val.1 := by
    change (flagAction g z.val).1=(flagAction g w.val).1
    rw [(flagAffineData_action g z.val).1,(flagAffineData_action g w.val).1,hf.2]
  have hk := sameAffineBranch_kernels hD g z w hf (r/N) (N*η)
  let T := planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)*
    planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w)
  have hT₀ : 0 ≤ T := mul_nonneg (planeTent_nonneg _ _ _) (planeTent_nonneg _ _ _)
  have hT₁ : T ≤ 1 := (mul_le_mul (planeTent_le_one _ _ _) (planeTent_le_one _ _ _)
    (planeTent_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)
  have he : (flagAveragingMatrix χ ρ N r η κ z w-
      flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w))=
    (χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w)*
      separatorMatrix (thresholdLaw (r/N) κ) z.val.2 w.val.2-
     χ (scaledSiteConjugate N (flagSiteAction hD g z))*χ (scaledSiteConjugate N (flagSiteAction hD g w))*
      separatorMatrix (thresholdLaw (r/N) κ) (flagAction g z.val).2 (flagAction g w.val).2)*T/d := by
    rw [flagAveragingMatrix,flagAveragingMatrix,ite_eq_left hf.1,ite_eq_left ht,hk.1,hk.2]
    change _=(_-_*separatorMatrix (thresholdLaw (r/N) κ) (flagSiteAction hD g z).val.2
      (flagSiteAction hD g w).val.2)*T/d
    dsimp only [T,d]
    ring
  rw [he,abs_div,abs_mul,abs_of_pos hd,abs_of_nonneg hT₀]
  have htrip := unit_triple_sub_bound (f:=separatorMatrix (thresholdLaw (r/N) κ) (flagAction g z.val).2 (flagAction g w.val).2) (hχ (scaledSiteConjugate N z)) (hχ (scaledSiteConjugate N w))
    (separatorMatrix_bounds (thresholdLaw (r/N) κ) z.val.2 w.val.2)
    (hχ (scaledSiteConjugate N (flagSiteAction hD g z)))
    (hχ (scaledSiteConjugate N (flagSiteAction hD g w)))
  have hh := add_le_add (add_le_add hz hw) hp
  have hmain := htrip.trans hh
  change _ ≤ L*A/N+L*A/N+B*(r/N)/κ at hmain
  calc
    _ ≤ (L*A/N+L*A/N+B*(r/N)/κ)/d := by
      apply (div_le_div_iff_of_pos_right hd).mpr
      exact (mul_le_mul_of_nonneg_left hT₁ (abs_nonneg _)).trans (by simpa only [mul_one] using hmain)
    _ = (2*L*A+B*(r/κ))/(N*d) := by field_simp; ring
    _ ≤ (A+B)*(2*L+r/κ)/(N*d) := by
      apply (div_le_div_iff_of_pos_right (mul_pos hN hd)).mpr
      nlinarith [mul_nonneg hA (div_nonneg hr.le hκ.le),mul_nonneg hB hL]
    _ = _ := rfl

end AveragingEntryCovariance

end SimpleAmenable
end
end

end OAI
