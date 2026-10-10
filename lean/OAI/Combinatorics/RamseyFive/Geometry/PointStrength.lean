import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.LocalLines
import OAI.Combinatorics.RamseyFive.Probability.OwnFraction
import OAI.Combinatorics.RamseyFive.Geometry.RadialLabel

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def pointStrength (S : Finset (ℙ K V)) : ℝ≥0 :=
  (Nat.card K:ℝ≥0)/S.card

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma coe_pointStrength (S : Finset (ℙ K V)) :
    (pointStrength (K:=K) S:ℝ)=(Nat.card K:ℝ)/S.card := by
  simp only [pointStrength,NNReal.coe_div,NNReal.coe_natCast]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma mass_outside_pencil (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H) (H : F) :
    mass (radialWeight x (outsideAt x S O) (pointStrength S)) (pencilLines x F H) =
      outsideMass S O x H.val := by
  rw [mass_pencil x (outsideAt x S O) (pointStrength S) F hF H]
  change _*(((outsideAt x S O).filter fun y => y.val.submodule≤LinearMap.ker H.val.rep).card:ℝ)=_
  rw [outsideAt_filter_card,coe_pointStrength]
  rfl

omit [Finite K] [Fintype (ℙ K V)] in
theorem actual_radial_mass_bounds {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (hS : S.Nonempty)
    (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100) (H : F) :
    3/4 ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H) ∧
    |mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H)-
      (1-ownFraction S (C a) (C b))|≤17/100 ∧
    mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H)≤11/10 := by
  rw [mass_outside_pencil x S (C a∪C b) F (fun H hH => (hF H hH).1)]
  exact typical_mass_bounds S C hS a b c ha hb hc x (hF H.val H.property).2 hf hn

theorem actual_radial_variance {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (hn : (Nat.card K:ℝ)/S.card ≤1) :
    (∑ H : F,|mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (pencilLines x F H)-(1-ownFraction S (C a) (C b))|^2)≤
        40*scale (K:=K) d S.card*Real.exp ξ := by
  simp_rw [mass_outside_pencil x S (C a∪C b) F (fun H hH => (hF H hH).1),sq_abs]
  exact typical_mass_variance hdim hd S C hS a b c ha hb hc x F hF hξ hx hn

theorem actual_validation_second {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (L : ℝ≥0) (hL : 1≤(L:ℝ)) (R : ℕ) (hR : 2≤R) (own : F→Fin R→Bool) :
    (∫ ω,(typicalScore Finset.univ
      (fun H : F => Finset.univ.filter fun y : outsideAt x S (C a∪C b) => Incident y.val.val H.val)
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) own ω)^2
      ∂scheduleMeasure (fun _ : outsideAt x S (C a∪C b) => L*pointStrength S) R) ≤
      (F.card:ℝ)*(2*Real.exp (-(L:ℝ)*(3/4)))^R+
      (2*(L:ℝ)^2*Real.exp (-(L:ℝ)*(3/4)))^R*
        ((40*scale (K:=K) d S.card*Real.exp ξ)^2+
          ∑ H : F,∑ H'∈Finset.univ.erase H,
            (mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
              (pencilLines x F H∩pencilLines x F H'))^R) := by
  rw [original_radial_moment x _ L (pointStrength S) F (fun H hH => (hF H hH).1)]
  have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
  have hv := actual_radial_variance x hdim hd S C hS a b c ha hb hc F hF hξ hx
    (hn.trans (by norm_num))
  have h := ValidationMoment.poisson_validation_second
    (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F)
    L hL (1-ownFraction S (C a) (C b)) (3/4) (by norm_num) (by linarith)
    (fun H => (hm H).1) (fun H => (hm H).2.1.trans (by norm_num)) R hR own
  apply h.trans
  simp only [Fintype.card_coe]
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ (le_refl _)
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) hv 2

end SharpRamseyFive.ScoreGeometry

end OAI
