import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroPolynomial

namespace OAI

/-! # Finite zero-factor removal for the completed-character application -/

namespace Ostmann

open Filter Set
open scoped Topology BigOperators Classical

noncomputable def finiteZeroPolynomial (f : ℂ → ℂ)
    (S : Finset ℂ) (s : ℂ) : ℂ :=
  ∏ z ∈ S, (s - z) ^ analyticOrderNatAt f z

theorem finiteZeroPolynomial_analytic (f : ℂ → ℂ)
    (S : Finset ℂ) (s : ℂ) : AnalyticAt ℂ (finiteZeroPolynomial f S) s := by
  exact S.analyticAt_fun_prod fun z _ => (analyticAt_id.sub analyticAt_const).pow _

theorem finiteZeroPolynomial_ne_zero (f : ℂ → ℂ)
    (S : Finset ℂ) (s : ℂ) (hs : s ∉ S) : finiteZeroPolynomial f S s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hs (he ▸ hz)))

theorem finiteZeroPolynomial_insert (f : ℂ → ℂ)
    (S : Finset ℂ) (z s : ℂ) (hz : z ∈ S) :
    finiteZeroPolynomial f S s =
      (s - z) ^ analyticOrderNatAt f z * finiteZeroPolynomial f (S.erase z) s := by
  exact (Finset.mul_prod_erase S _ hz).symm

/-- The quotient by any finite collection of complete zero factors extends
analytically to the whole plane. It is nonzero at each removed zero. -/
theorem remove_finite_analytic_zeros (f : ℂ → ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z) (horder : ∀ z, analyticOrderAt f z ≠ ⊤) (S : Finset ℂ) :
    ∃ g : ℂ → ℂ, (∀ s, AnalyticAt ℂ g s) ∧
      (∀ s, f s = finiteZeroPolynomial f S s * g s) ∧
      (∀ s ∈ S, g s ≠ 0) := by
  choose R hR hRne heR using fun z =>
    (hf z).analyticOrderAt_ne_top.mp (horder z)
  let g : ℂ → ℂ := fun z => if z ∈ S then
    R z z / finiteZeroPolynomial f (S.erase z) z
    else f z / finiteZeroPolynomial f S z
  have hlocal (z : ℂ) (hz : z ∈ S) :
      g =ᶠ[𝓝 z] fun s => R z s / finiteZeroPolynomial f (S.erase z) s := by
    have hav : ∀ᶠ s in 𝓝 z, s ∉ S.erase z :=
      (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [hav, heR z] with s hs he
    by_cases hsz : s = z
    · subst s
      simp only [g, ite_eq_left hz]
    · have hsS : s ∉ S := fun h => hs (Finset.mem_erase.mpr ⟨hsz, h⟩)
      simp only [g, ite_eq_right hsS]
      rw [finiteZeroPolynomial_insert f S z s hz, he]
      simp only [smul_eq_mul]
      exact mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hsz))
  have ha : ∀ s, AnalyticAt ℂ g s := by
    intro s
    by_cases hs : s ∈ S
    · exact ((hR s).div (finiteZeroPolynomial_analytic f (S.erase s) s)
        (finiteZeroPolynomial_ne_zero f (S.erase s) s (by simp))).congr
          (hlocal s hs).symm
    · apply ((hf s).div (finiteZeroPolynomial_analytic f S s)
        (finiteZeroPolynomial_ne_zero f S s hs)).congr
      have hav : ∀ᶠ z in 𝓝 s, z ∉ S := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hs
      filter_upwards [hav] with z hz
      simp only [g, ite_eq_right hz, Pi.div_apply]
  refine ⟨g, ha, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ S
    · rw [(hlocal s hs).self_of_nhds, finiteZeroPolynomial_insert f S s s hs]
      have he := (heR s).self_of_nhds
      simp only [smul_eq_mul] at he
      rw [he]
      field_simp [finiteZeroPolynomial_ne_zero f (S.erase s) s (by simp)]
    · simp only [g, ite_eq_right hs]
      exact (mul_div_cancel₀ _ (finiteZeroPolynomial_ne_zero f S s hs)).symm
  · intro s hs
    simp only [g, ite_eq_left hs]
    exact div_ne_zero (hRne s) (finiteZeroPolynomial_ne_zero f (S.erase s) s (by simp))

end Ostmann

end OAI
