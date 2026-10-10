import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletion
import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerDivisors

namespace OAI

/-! The literal grouped coefficient in the long inverse-completion tail.
Its angular and coprimality phases are retained, while the remaining
Möbius divisor sum is bounded by a proved small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticTailPairs (F : ℝ) (e : Eisenstein) : Finset (Eisenstein × Eisenstein) :=
  ((primaryElementBall F).product (primaryElementBall F)).filter (fun cd => cd.1*cd.2 = e)

def metaplecticTailMoebius (C F : ℝ) (e : Eisenstein) : ℂ :=
  ∑ cd ∈ metaplecticTailPairs F e, if C < norm cd.1 then (idealMoebius cd.1:ℂ) else 0

def metaplecticTailCoefficient (r : Eisenstein) (ℓ : ℤ) (C F : ℝ) (e : Eisenstein) : ℂ :=
  ∑ cd ∈ metaplecticTailPairs F e, if C < norm cd.1 then
    (idealMoebius cd.1:ℂ)*metaplecticCompletionWeight r ℓ 0 cd.1*
      metaplecticCompletionWeight r ℓ 0 cd.2 else 0

lemma metaplecticTailCoefficient_factor (r : Eisenstein) (ℓ : ℤ) (C F : ℝ)
    (e : Eisenstein) :
    metaplecticTailCoefficient r ℓ C F e =
      metaplecticCompletionWeight r ℓ 0 e*metaplecticTailMoebius C F e := by
  unfold metaplecticTailCoefficient metaplecticTailMoebius
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro cd hcd
  obtain ⟨hmem,he⟩ := Finset.mem_filter.mp hcd
  have hc := (mem_primaryElementBall.mp (Finset.mem_product.mp hmem).1).1
  have hd := (mem_primaryElementBall.mp (Finset.mem_product.mp hmem).2).1
  by_cases hn : C < norm cd.1
  · simp only [hn,ite_true]
    rw [←he,metaplecticCompletionWeight_mul r ℓ 0 hc hd]
    ring
  · simp only [hn,ite_false,mul_zero]

/-- Exact collection of the two actual completion divisors into their
product, for any remaining norm-weighted Gauss sum. -/
theorem metaplecticTailCoefficient_collect (r : Eisenstein) (ℓ : ℤ) (C F : ℝ)
    (g : Eisenstein → ℂ) :
    (∑ c ∈ primaryElementBall F, ∑ d ∈ primaryElementBall F,
      (if C < norm c then (idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c*
        metaplecticCompletionWeight r ℓ 0 d else 0)*g (c*d)) =
      ∑ e ∈ ((primaryElementBall F).product (primaryElementBall F)).image
        (fun cd => cd.1*cd.2), metaplecticTailCoefficient r ℓ C F e*g e := by
  let P := (primaryElementBall F).product (primaryElementBall F)
  let f : Eisenstein × Eisenstein → ℂ := fun cd =>
    (if C < norm cd.1 then (idealMoebius cd.1:ℂ)*metaplecticCompletionWeight r ℓ 0 cd.1*
      metaplecticCompletionWeight r ℓ 0 cd.2 else 0)*g (cd.1*cd.2)
  rw [←Finset.sum_product']
  change (∑ cd ∈ P, f cd) = _
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun cd hcd => Finset.mem_image_of_mem (fun cd : Eisenstein × Eisenstein => cd.1*cd.2) hcd) f]
  apply Finset.sum_congr rfl
  intro e _
  rw [metaplecticTailCoefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro cd hcd
  dsimp only [f]
  rw [(Finset.mem_filter.mp hcd).2]

lemma metaplecticTailMoebius_zero {e : Eisenstein} (he : primary e) {C F : ℝ}
    (hC : norm e ≤ C) : metaplecticTailMoebius C F e = 0 := by
  apply Finset.sum_eq_zero
  intro cd hcd
  have hd := (Finset.mem_filter.mp hcd).2
  have hn : norm cd.1 ≤ norm e := norm_le_of_dvd (primary_ne_zero he) ⟨cd.2,hd.symm⟩
  exact ite_eq_right (not_lt_of_ge (hn.trans hC))

lemma metaplecticTailCoefficient_zero (r : Eisenstein) (ℓ : ℤ)
    {e : Eisenstein} (he : primary e) {C F : ℝ} (hC : norm e ≤ C) :
    metaplecticTailCoefficient r ℓ C F e = 0 := by
  rw [metaplecticTailCoefficient_factor,metaplecticTailMoebius_zero he hC,mul_zero]

theorem metaplecticTailMoebius_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (C F : ℝ) (e : Eisenstein), primary e →
      ‖metaplecticTailMoebius C F e‖ ≤ D*norm e^ε := by
  obtain ⟨D,hD,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨D,hD,?_⟩
  intro C F e he
  have hp (c : Eisenstein) (hc : c ∈ primaryElementBall F) : primary c :=
    (mem_primaryElementBall.mp hc).1
  have hcard : ((metaplecticTailPairs F e).card:ℝ) ≤ D*norm e^ε :=
    (Nat.cast_le.mpr (primary_pair_fiber_le_divisors _ hp e)).trans
      (hdiv _ hp e (primary_ne_zero he))
  unfold metaplecticTailMoebius
  calc
    _ ≤ ∑ cd ∈ metaplecticTailPairs F e,
        ‖if C < norm cd.1 then (idealMoebius cd.1:ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _cd ∈ metaplecticTailPairs F e, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro cd _
      split_ifs
      · exact norm_idealMoebius_le_one _
      · simp
    _ = ((metaplecticTailPairs F e).card:ℝ) := by simp
    _ ≤ _ := hcard

theorem metaplecticTailCoefficient_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r : Eisenstein) (ℓ : ℤ) (C F : ℝ) (e : Eisenstein), primary e →
      ‖metaplecticTailCoefficient r ℓ C F e‖ ≤ D*norm e^(1/2+ε) := by
  obtain ⟨D,hD,hbound⟩ := metaplecticTailMoebius_bound hε
  refine ⟨D,hD,?_⟩
  intro r ℓ C F e he
  have hw : ‖metaplecticCompletionWeight r ℓ 0 e‖ ≤ Real.sqrt (norm e) := by
    rw [norm_metaplecticCompletionWeight he]
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  rw [metaplecticTailCoefficient_factor,norm_mul]
  calc
    _ ≤ Real.sqrt (norm e)*(D*norm e^ε) :=
      mul_le_mul hw (hbound C F e he) (_root_.norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,Real.rpow_add (norm_pos_of_ne_zero (primary_ne_zero he))]
      ring

end CubicFirstMoment

end

end OAI
