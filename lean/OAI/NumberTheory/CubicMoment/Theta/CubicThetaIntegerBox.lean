import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselSlopeNumerics

namespace OAI

/-! Finite coordinate boxes for the quantitative arithmetic theta tail. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace CubicFirstMoment

abbrev CubicThetaIntegerPoint := ℤ × ℤ

def cubicThetaIntegerRadius (p : CubicThetaIntegerPoint) : ℕ :=
  max p.1.natAbs p.2.natAbs

def cubicThetaIntegerBox (k : ℕ) : Finset CubicThetaIntegerPoint :=
  (Finset.Icc (-(k:ℤ)) k).product (Finset.Icc (-(k:ℤ)) k)

lemma cubicThetaIntegerBox_mem (p : CubicThetaIntegerPoint) (k : ℕ) :
    p∈cubicThetaIntegerBox k ↔ cubicThetaIntegerRadius p≤k := by
  simp only [cubicThetaIntegerBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,cubicThetaIntegerRadius,
    max_le_iff]
  omega

lemma cubicThetaIntegerBox_card (k : ℕ) :
    (cubicThetaIntegerBox k).card=(2*k+1)^2 := by
  unfold cubicThetaIntegerBox
  rw [Finset.product_eq_sprod,Finset.card_product,Int.card_Icc]
  have h : ((k:ℤ)+1- -(k:ℤ)).toNat=2*k+1 := by omega
  rw [h]
  ring

lemma cubicThetaIntegerBox_card_bound {k : ℕ} (hk : 1≤k) :
    ((cubicThetaIntegerBox k).card:ℝ)≤9*(k:ℝ)^2 := by
  rw [cubicThetaIntegerBox_card]
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  push_cast
  nlinarith

lemma cubicThetaInteger_finite_sum_bound (S : Finset CubicThetaIntegerPoint)
    (f : CubicThetaIntegerPoint → ℝ) (g : ℕ → ℝ) (hg : ∀ k,0≤g k)
    (hf : ∀ p∈S,f p≤g (cubicThetaIntegerRadius p)) :
    ∑ p∈S,f p≤∑ k∈S.image cubicThetaIntegerRadius,
      ((cubicThetaIntegerBox k).card:ℝ)*g k := by
  classical
  calc
    _ ≤ ∑ p∈S,g (cubicThetaIntegerRadius p) := Finset.sum_le_sum hf
    _ = ∑ k∈S.image cubicThetaIntegerRadius,
        ∑ p∈S with cubicThetaIntegerRadius p=k,g (cubicThetaIntegerRadius p) := by
      exact (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem _ hp)
        (fun p => g (cubicThetaIntegerRadius p))).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      have hsub : S.filter (fun p => cubicThetaIntegerRadius p=k)⊆cubicThetaIntegerBox k := by
        intro p hp
        apply (cubicThetaIntegerBox_mem p k).mpr
        exact (Finset.mem_filter.mp hp).2.le
      calc
        _ = ((S.filter (fun p => cubicThetaIntegerRadius p=k)).card:ℝ)*g k := by
          rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])]
          simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (hg k)

lemma cubicThetaInteger_tsum_bound (f : CubicThetaIntegerPoint → ℝ) (g : ℕ → ℝ)
    (hf0 : ∀ p,0≤f p) (hg : ∀ k,0≤g k)
    (hf : ∀ p,f p≤g (cubicThetaIntegerRadius p))
    (hs : Summable (fun k => ((cubicThetaIntegerBox k).card:ℝ)*g k)) :
    Summable f ∧ (∑' p,f p)≤∑' k,((cubicThetaIntegerBox k).card:ℝ)*g k := by
  have hbound (S : Finset CubicThetaIntegerPoint) :
      ∑ p∈S,f p≤∑' k,((cubicThetaIntegerBox k).card:ℝ)*g k := by
    exact (cubicThetaInteger_finite_sum_bound S f g hg (fun p _ => hf p)).trans
      (hs.sum_le_tsum _ (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hg k)))
  exact ⟨summable_of_sum_le hf0 hbound,Real.tsum_le_of_sum_le hf0 hbound⟩

end CubicFirstMoment

end

end OAI
