import OAI.NumberTheory.CubicMoment.Angular.AngularShortUnsplitTuple
import OAI.NumberTheory.CubicMoment.Angular.AngularFirstWeightedNeighborhood

namespace OAI

/-! Exact norm-partition reconstruction preserves the exceptional neighborhood. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_first_unsplit_tuple_neighborhood (hpub : PrimitiveAngularHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) →
      (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ A a 1 q η t V Y‖^2) ≤ Y^(7/3-ε) := by
  let D : ℝ := 2^(Fintype.card ι+1)
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hD2 : 2 ≤ D := by
    dsimp [D]
    rw [pow_succ]
    have h := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := Fintype.card ι)
    linarith
  have hD : 0 < D := zero_lt_one.trans_le hD1
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hw⟩ := angular_first_weighted_tuple_neighborhood (ι := ι) hpub ℓ V hV hpos hsm hGI hGQ hD
  obtain ⟨T₁,hT₁,hpart⟩ := norm_partition_moment_power (ι := ι) hε
  refine ⟨κ,hκ,hκhi,ε/2,by positivity,max T T₁,?_⟩
  intro F Y N A q η t P hY hNlo hNhi hF hA hq hη hqY ht hP
  have hYT : T ≤ Y := (le_max_left _ _).trans hY
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  let f : (ι → Fin (normPartitionCount (2*Y))) → P → ℂ := fun k a =>
    primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A a 1 q η
      (fun _ => normPartitionWeight) t V Y
  have hf (k : ι → Fin (normPartitionCount (2*Y))) : (∑ a : P, ‖f k a‖^2) ≤ Y^(7/3-ε) := by
    by_cases hg : Y ≤ (∏ i, (4/3:ℝ)^(k i).val) ∧ (∏ i, (4/3:ℝ)^(k i).val) ≤ D*Y
    · have h := hw F Y N (fun i => (4/3:ℝ)^(k i).val) A q η t P Y hYT hNlo hNhi
        (hF.trans (mul_le_mul_of_nonneg_right hD2 hYp.le)) hA
        (fun i => one_le_pow₀ (by norm_num)) ((div_le_self hYp.le hD1).trans hg.1)
        hg.2 hq hη hqY ht hP hYp
      change (∑ a ∈ P.attach, ‖f k a‖^2) ≤ _
      dsimp only [f]
      rw [Finset.sum_attach (f := fun a : Eisenstein =>
        ‖primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A a 1 q η
          (fun _ => normPartitionWeight) t V Y‖^2)]
      exact h
    · have hz (a : P) : f k a = 0 := primaryAngularShortTupleSum_zero_outside_scales ℓ _ A a 1 q η t V
        (fun i => pow_pos (by norm_num) _) hYp hVlo hVhi hg
      simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
      exact Real.rpow_nonneg hYp.le _
  have hm := hpart Y hYT₁ P f hf
  have he (a : Eisenstein) : primaryAngularUnsplitTuple ℓ A a 1 q η t V Y =
      ∑ k : ι → Fin (normPartitionCount (2*Y)),
        primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A a 1 q η
          (fun _ => normPartitionWeight) t V Y :=
    primaryAngularShortTupleSum_partition ℓ A a 1 q η t V hY1 hVhi
  simp_rw [he]
  change (∑ a ∈ P.attach, ‖∑ k, f k a‖^2) ≤ _ at hm
  dsimp only [f] at hm
  rw [Finset.sum_attach (f := fun a : Eisenstein =>
    ‖∑ k : ι → Fin (normPartitionCount (2*Y)),
      primaryAngularShortTupleSum ℓ (fun i => (4/3:ℝ)^(k i).val) A a 1 q η
        (fun _ => normPartitionWeight) t V Y‖^2)] at hm
  exact hm

end CubicFirstMoment

end

end OAI
