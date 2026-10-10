import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleNonflatHigh
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleSelectedFlat
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleResidualPartition

namespace OAI

/-! The remaining high exceptional boxes split exactly into the flat
subfamily and its complement. Both are negligible on the stated scale. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeTupleExceptionalSelector (i j : ℕ) (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : Prop :=
  ¬∃ q ∈ largePrimeTupleBox i j X,
    largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
      ¬largePrimeTupleExceptional δ q

def largePrimeTupleExceptionalNonflatSum (i j : ℕ) (ξ δ : ℝ) (Ct G : ℕ) (H X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if (X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      largeTupleExceptionalSelector i j ξ δ Ct H X d) ∧
      d ∉ largePrimeTupleFlatBoxSet i j 0 ξ Ct G H X then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0

lemma largePrimeTupleExceptionalHigh_split (i j : ℕ) (ξ δ : ℝ) (Ct G : ℕ) (H X : ℝ) :
    largePrimeTupleExceptionalHighSum i j ξ δ Ct H X =
      largePrimeTupleSelectedFlatHighSum i j ξ Ct G H X
        (largeTupleExceptionalSelector i j ξ δ Ct H X) +
      largePrimeTupleExceptionalNonflatSum i j ξ δ Ct G H X := by
  let S := largePrimeTupleFlatBoxSet i j 0 ξ Ct G H X
  let f := fun d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)) =>
    if X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      largeTupleExceptionalSelector i j ξ δ Ct H X d then
      largePrimeTuplePiece i j 0 ξ Ct H X d else 0
  have hs : Finset.univ.filter (fun d => d ∈ S) = S := by ext d; simp
  have he : (∑ d ∈ S, f d) = ∑ d, if d ∈ S then f d else 0 := by
    calc
      _ = ∑ d ∈ Finset.univ.filter (fun d => d ∈ S), f d := by rw [hs]
      _ = _ := by rw [Finset.sum_filter]
  unfold largePrimeTupleExceptionalHighSum largePrimeTupleSelectedFlatHighSum
    largePrimeTupleExceptionalNonflatSum
  dsimp only [f,S] at he
  rw [he,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [largeTupleExceptionalSelector]
  by_cases hp : X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
      largeTupleExceptionalSelector i j ξ δ Ct H X d
  · dsimp only [largeTupleExceptionalSelector] at hp
    by_cases hd : d ∈ S
    · dsimp only [S] at hd
      simp only [hp,hd,true_and,not_true_eq_false,and_false,ite_true,ite_false,add_zero]
    · dsimp only [S] at hd
      simp only [hp,hd,not_false_eq_true,and_true,ite_true,ite_false,zero_add]
  · dsimp only [largeTupleExceptionalSelector] at hp
    simp only [hp,false_and,ite_false,ite_self,add_zero]

theorem largePrimeTupleExceptionalHighSum_isLittleO (i j : ℕ) (hij : i+j = 3)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct : ℕ) (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop, 0 < H X) :
    (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X) =o[atTop] firstMomentScale := by
  obtain ⟨G,K,hK,hbound⟩ := largePrimeTuplePiece_nonflat_high_bound i j hij hSW hpub
    hHuxley hperiod hMV hC hξ hξz hδ hGI hGQ hVor hGamma (3+(i+j)) Ct
  obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i j
  have hn : (fun X => largePrimeTupleExceptionalNonflatSum i j ξ δ Ct G (H X) X)
      =o[atTop] firstMomentScale := by
    apply Asymptotics.IsBigO.trans_isLittleO
      (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
    apply Asymptotics.IsBigO.of_bound (D*K)
    filter_upwards [hbound,hH,eventually_ge_atTop (1:ℝ)] with X hb hH hX
    have hXp : 0 < X := zero_lt_one.trans_le hX
    have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
    let B := K*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j))
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hp (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
        ‖if (X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) ∧
          largeTupleExceptionalSelector i j ξ δ Ct (H X) X d) ∧
          d ∉ largePrimeTupleFlatBoxSet i j 0 ξ Ct G (H X) X then
          largePrimeTuplePiece i j 0 ξ Ct (H X) X d else 0‖ ≤ B := by
      split_ifs with hd
      · by_cases hz : largePrimeTuplePiece i j 0 ξ Ct (H X) X d = 0
        · rw [hz,norm_zero]; exact hB
        obtain ⟨q,hq,hqne⟩ := largePrimeTuplePiece_witness d hz
        have hex : largePrimeTupleExceptional δ q := by
          by_contra hh
          exact hd.1.2 ⟨q,hq,hqne,hh⟩
        exact hb (H X) hH d hd.1.1 hd.2 ⟨q,hq,hqne,hex⟩
      · simpa only [norm_zero] using hB
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
    unfold largePrimeTupleExceptionalNonflatSum
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun d _ => hp d)).trans
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (hcount X hX) hB).trans_eq
    dsimp [B]
    rw [pow_add]
    field_simp
    ring
  have hf := largePrimeTupleSelectedFlatHighSum_isLittleO i j hij hpnt hSW hpub hHuxley
    hperiod hMV hC hξ hξz hGI hGQ Ct G
    (fun X => largeTupleExceptionalSelector i j ξ δ Ct (H X) X) H hH
  have he : (fun X => largePrimeTupleExceptionalHighSum i j ξ δ Ct (H X) X) =
      (fun X => largePrimeTupleSelectedFlatHighSum i j ξ Ct G (H X) X
        (largeTupleExceptionalSelector i j ξ δ Ct (H X) X) +
        largePrimeTupleExceptionalNonflatSum i j ξ δ Ct G (H X) X) := by
    funext X
    exact largePrimeTupleExceptionalHigh_split i j ξ δ Ct G (H X) X
  rw [he]
  exact hf.add hn

lemma largePrimeTupleExceptionalHighSum_zero (i j : ℕ) (hij : i+j ≠ 3)
    (ξ δ : ℝ) (Ct : ℕ) (H X : ℝ) :
    largePrimeTupleExceptionalHighSum i j ξ δ Ct H X = 0 := by
  unfold largePrimeTupleExceptionalHighSum
  apply Finset.sum_eq_zero
  intro d _
  split_ifs with hd
  · by_contra hne
    obtain ⟨q,hq,hqne⟩ := largePrimeTuplePiece_witness d hne
    have hex : largePrimeTupleExceptional δ q := by
      by_contra hh
      exact hd.2 ⟨q,hq,hqne,hh⟩
    exact hij hex.1
  · rfl

end CubicFirstMoment

end

end OAI
