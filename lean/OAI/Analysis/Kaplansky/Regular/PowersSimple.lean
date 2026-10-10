import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.PowersAveraging

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal ComplexOrder

lemma conjugateMap_mem_ideal (I : ClosedStarIdeal (Algebra F2)) (g : F2)
    {x : Algebra F2} (hx : x ∈ I.toNonUnitalStarSubalgebra) :
    conjugateMap g x ∈ I.toNonUnitalStarSubalgebra :=
  I.mul_mem_right _ _ (I.mul_mem_left _ _ hx)

lemma averageConjugate_mem_ideal (I : ClosedStarIdeal (Algebra F2)) {N : ℕ}
    (h : Fin N → F2) {x : Algebra F2} (hx : x ∈ I.toNonUnitalStarSubalgebra) :
    averageConjugate h x ∈ I.toNonUnitalStarSubalgebra := by
  rw [averageConjugate_apply]
  exact I.toNonUnitalStarSubalgebra.smul_mem _ (I.toNonUnitalStarSubalgebra.sum_mem
    (fun i hi => conjugateMap_mem_ideal I (h i) hx))

theorem algebra_F2_simple : CStarSimple (Algebra F2) := by
  intro I
  by_cases hI : ∀ a : Algebra F2, a ∈ I.toNonUnitalStarSubalgebra → a=0
  · exact Or.inl hI
  · right
    push Not at hI
    obtain ⟨a,ha,hane⟩ := hI
    have ht : coefficient (star a*a) ≠ 0 := fun h => hane (coefficient_faithful a h)
    let b : Algebra F2 := (coefficient (star a*a))⁻¹ • (star a*a)
    have hb : coefficient b = 1 := by
      change canonicalTrace.functional ((coefficient (star a*a))⁻¹ • (star a*a))=1
      rw [map_smul]
      change (coefficient (star a*a))⁻¹ * coefficient (star a*a)=1
      exact inv_mul_cancel₀ ht
    have hbI : b ∈ I.toNonUnitalStarSubalgebra :=
      I.toNonUnitalStarSubalgebra.smul_mem _ (I.mul_mem_left _ _ ha)
    have hzero : coefficient (b-1)=0 := by
      change canonicalTrace.functional (b-1)=0
      rw [map_sub,canonicalTrace.normalized]
      change coefficient b - 1 = 0
      rw [hb,sub_self]
    obtain ⟨N,hN,h,hh⟩ := powers_averaging (b-1) hzero 1 zero_lt_one
    rw [map_sub,averageConjugate_one hN] at hh
    have hu : IsUnit (averageConjugate h b) := by
      have he : ‖1-averageConjugate h b‖<1 := by simpa only [norm_sub_rev] using hh
      simpa only [Units.val_oneSub,sub_sub_self] using (Units.oneSub (1-averageConjugate h b) he).isUnit
    obtain ⟨u,hu⟩ := hu
    have hunit : (u : Algebra F2) ∈ I.toNonUnitalStarSubalgebra := by
      rw [hu]
      exact averageConjugate_mem_ideal I h hbI
    have hone : (1 : Algebra F2) ∈ I.toNonUnitalStarSubalgebra := by
      simpa only [Units.inv_mul] using I.mul_mem_left (↑u⁻¹) u hunit
    intro x
    simpa only [mul_one] using I.mul_mem_left x 1 hone


end KaplanskyConsequences.Regular

end

end OAI
