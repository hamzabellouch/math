import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroSet

namespace OAI

/-! # Removing the actual finite zero factors of an entire character L-function -/

namespace Ostmann

open Filter Set
open scoped Topology BigOperators Classical

noncomputable def characterZeroPolynomial (χ : PrimitiveComplexCharacter)
    (S : Finset ℂ) (s : ℂ) : ℂ :=
  ∏ z ∈ S, (s - z) ^ analyticOrderNatAt χ.L z

theorem characterZeroPolynomial_analytic (χ : PrimitiveComplexCharacter)
    (S : Finset ℂ) (s : ℂ) : AnalyticAt ℂ (characterZeroPolynomial χ S) s := by
  exact S.analyticAt_fun_prod fun z _ => (analyticAt_id.sub analyticAt_const).pow _

theorem characterZeroPolynomial_ne_zero (χ : PrimitiveComplexCharacter)
    (S : Finset ℂ) (s : ℂ) (hs : s ∉ S) : characterZeroPolynomial χ S s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hs (he ▸ hz)))

theorem characterZeroPolynomial_insert (χ : PrimitiveComplexCharacter)
    (S : Finset ℂ) (z s : ℂ) (hz : z ∈ S) :
    characterZeroPolynomial χ S s =
      (s - z) ^ analyticOrderNatAt χ.L z * characterZeroPolynomial χ (S.erase z) s := by
  exact (Finset.mul_prod_erase S _ hz).symm

/-- The quotient by any finite collection of complete zero factors extends
analytically to the whole plane. It is nonzero at each removed zero. -/
theorem character_remove_finite_zeros (χ : PrimitiveComplexCharacter) (S : Finset ℂ) :
    ∃ g : ℂ → ℂ, (∀ s, AnalyticAt ℂ g s) ∧
      (∀ s, χ.L s = characterZeroPolynomial χ S s * g s) ∧
      (∀ s ∈ S, g s ≠ 0) := by
  choose R hR hRne heR using fun z =>
    (χ.L_analytic z).analyticOrderAt_ne_top.mp (χ.L_order_ne_top z)
  let g : ℂ → ℂ := fun z => if z ∈ S then
    R z z / characterZeroPolynomial χ (S.erase z) z
    else χ.L z / characterZeroPolynomial χ S z
  have hlocal (z : ℂ) (hz : z ∈ S) :
      g =ᶠ[𝓝 z] fun s => R z s / characterZeroPolynomial χ (S.erase z) s := by
    have hav : ∀ᶠ s in 𝓝 z, s ∉ S.erase z :=
      (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [hav, heR z] with s hs he
    by_cases hsz : s = z
    · subst s
      simp only [g, ite_eq_left hz]
    · have hsS : s ∉ S := fun h => hs (Finset.mem_erase.mpr ⟨hsz, h⟩)
      simp only [g, ite_eq_right hsS]
      rw [characterZeroPolynomial_insert χ S z s hz, he]
      simp only [smul_eq_mul]
      exact mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hsz))
  have ha : ∀ s, AnalyticAt ℂ g s := by
    intro s
    by_cases hs : s ∈ S
    · exact ((hR s).div (characterZeroPolynomial_analytic χ (S.erase s) s)
        (characterZeroPolynomial_ne_zero χ (S.erase s) s (by simp))).congr
          (hlocal s hs).symm
    · apply ((χ.L_analytic s).div (characterZeroPolynomial_analytic χ S s)
        (characterZeroPolynomial_ne_zero χ S s hs)).congr
      have hav : ∀ᶠ z in 𝓝 s, z ∉ S := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hs
      filter_upwards [hav] with z hz
      simp only [g, ite_eq_right hz, Pi.div_apply]
  refine ⟨g, ha, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ S
    · rw [(hlocal s hs).self_of_nhds, characterZeroPolynomial_insert χ S s s hs]
      have he := (heR s).self_of_nhds
      simp only [smul_eq_mul] at he
      rw [he]
      field_simp [characterZeroPolynomial_ne_zero χ (S.erase s) s (by simp)]
    · simp only [g, ite_eq_right hs]
      exact (mul_div_cancel₀ _ (characterZeroPolynomial_ne_zero χ S s hs)).symm
  · intro s hs
    simp only [g, ite_eq_left hs]
    exact div_ne_zero (hRne s) (characterZeroPolynomial_ne_zero χ (S.erase s) s (by simp))

end Ostmann

end OAI
