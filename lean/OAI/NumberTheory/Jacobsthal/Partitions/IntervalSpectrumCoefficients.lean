import OAI.NumberTheory.Jacobsthal.Sieve.IntegerResidueVariance

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

noncomputable def intervalCoordinates (S : Finset ℤ) (M : ℤ) (J : ℕ) : Finset ℕ :=
  (Finset.range J).filter (fun j : ℕ => M+(j : ℤ) ∈ S)

theorem intervalCoordinates_image (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) :
    (intervalCoordinates S M J).image (fun j : ℕ => M+(j : ℤ)) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hj).2
  · intro hx
    have hr := Finset.mem_Ico.mp (hS hx)
    let j := (x-M).toNat
    have he : (j : ℤ) = x-M := Int.toNat_of_nonneg (by omega)
    have hj : j < J := by
      have hh : (j : ℤ) < (J : ℤ) := by rw [he];omega
      exact_mod_cast hh
    have hpoint : M+(j : ℤ) = x := by rw [he];ring
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hpoint.symm ▸ hx⟩,hpoint⟩

theorem intervalCoordinates_card (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) : (intervalCoordinates S M J).card = S.card := by
  have hi : Function.Injective (fun j : ℕ => M+(j : ℤ)) :=
    fun _ _ h => Int.ofNat_injective (add_left_cancel h)
  have hc := Finset.card_image_of_injective (intervalCoordinates S M J) hi
  exact hc.symm.trans (congrArg Finset.card (intervalCoordinates_image S M J hS))

noncomputable def indicatorCoefficient (S : Finset ℤ) (x : ℤ) : ℂ := if x ∈ S then 1 else 0

theorem indicator_weighted_sum (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) (f : ℤ → ℂ) :
    (∑ j ∈ Finset.range J,indicatorCoefficient S (M+(j : ℤ))*f (M+(j : ℤ))) = ∑ x ∈ S,f x := by
  have hi : Function.Injective (fun j : ℕ => M+(j : ℤ)) :=
    fun _ _ h => Int.ofNat_injective (add_left_cancel h)
  simp only [indicatorCoefficient,ite_mul,one_mul,zero_mul]
  rw [← Finset.sum_filter]
  change (∑ j ∈ intervalCoordinates S M J,f (M+(j : ℤ))) = ∑ x ∈ S,f x
  calc
    _ = ∑ x ∈ (intervalCoordinates S M J).image (fun j : ℕ => M+(j : ℤ)),f x :=
      (Finset.sum_image hi.injOn).symm
    _ = _ := congrArg (fun V : Finset ℤ => ∑ x ∈ V,f x) (intervalCoordinates_image S M J hS)

theorem indicator_energy (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) :
    (∑ j ∈ Finset.range J,‖indicatorCoefficient S (M+(j : ℤ))‖^2) = (S.card : ℝ) := by
  have he (x : ℤ) : ‖indicatorCoefficient S x‖^2 = if x ∈ S then (1 : ℝ) else 0 := by
    by_cases hx : x ∈ S <;> simp [indicatorCoefficient,hx]
  simp_rw [he]
  rw [Finset.sum_boole]
  change ((intervalCoordinates S M J).card : ℝ) = S.card
  rw [intervalCoordinates_card S M J hS]

theorem indicator_exponential_sum (S : Finset ℤ) (M : ℤ) (J : ℕ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) (a q : ℕ) :
    (∑ j ∈ Finset.range J,indicatorCoefficient S (M+(j : ℤ))*
      AdditiveLargeSieve.exponential ((((M+(j : ℤ) : ℤ) : ℝ)*(a : ℝ))/(q : ℝ))) =
        exponentialSum S a q :=
  indicator_weighted_sum S M J hS (fun x => AdditiveLargeSieve.exponential (((x : ℝ)*(a : ℝ))/(q : ℝ)))

end ErdosInverseSpectrum

end

end Erdos970

end OAI
