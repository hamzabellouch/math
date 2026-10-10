import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothContourRegularPart

namespace OAI

/-! # Removing finitely many actual character poles simultaneously -/

namespace Ostmann

open Filter Set
open scoped Topology BigOperators Classical

/-- Fill in the removable values after subtracting the principal parts of all
zeros in a prescribed region. The pole set is the actual zero set in that region. -/
theorem smoothContour_finite_regularization (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (K : Set ℂ) (S : Finset ℂ)
    (hzeros : ∀ z ∈ K, χ.L z = 0 → z ∈ S) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F K ∧
      ∀ z ∉ S, F z = (-deriv χ.L z / χ.L z) * smoothContourWeight X z +
        ∑ w ∈ S, (analyticOrderNatAt χ.L w : ℂ) * smoothContourWeight X w / (z - w) := by
  choose R hR heR using fun z => smoothContour_regular_part χ X hX z
  let f : ℂ → ℂ := fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z
  let C : ℂ → ℂ := fun w => (analyticOrderNatAt χ.L w : ℂ) * smoothContourWeight X w
  let F : ℂ → ℂ := fun z => if z ∈ S then
    R z z + ∑ w ∈ S.erase z, C w / (z - w)
    else f z + ∑ w ∈ S, C w / (z - w)
  refine ⟨F, ?_, fun z hz => by simp [F, hz, f, C]⟩
  intro z hzK
  by_cases hz : z ∈ S
  · have hsum : AnalyticAt ℂ (fun s => ∑ w ∈ S.erase z, C w / (s - w)) z := by
      apply (S.erase z).analyticAt_fun_sum
      intro w hw
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm)
    apply ((hR z).add hsum).congr
    have hav : ∀ᶠ s in 𝓝 z, s ∉ S.erase z :=
      (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    have he : ∀ᶠ s in 𝓝 z, s ≠ z → f s + C z / (s - z) = R z s := by
      simpa only [mem_compl_iff, mem_singleton_iff, f, C] using
        (eventually_nhdsWithin_iff.mp (heR z))
    filter_upwards [hav, he] with s hs hreg
    by_cases hsz : s = z
    · subst s
      simp [F, hz]
    · have hsS : s ∉ S := fun hsS => hs (Finset.mem_erase.mpr ⟨hsz, hsS⟩)
      simp only [F, ite_eq_right hsS]
      rw [← Finset.sum_erase_add _ _ hz]
      simp only [Pi.add_apply]
      rw [← hreg hsz]
      ring
  · have hnz : χ.L z ≠ 0 := fun he => hz (hzeros z hzK he)
    have hf : AnalyticAt ℂ f z :=
      (((χ.L_analytic z).deriv.neg.div (χ.L_analytic z) hnz).mul
        ((smoothContourWeight_differentiable X hX).analyticAt z))
    have hsum : AnalyticAt ℂ (fun s => ∑ w ∈ S, C w / (s - w)) z := by
      apply S.analyticAt_fun_sum
      intro w hw
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (fun he => hz (he ▸ hw)))
    apply (hf.add hsum).congr
    have hav : ∀ᶠ s in 𝓝 z, s ∉ S := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hz
    filter_upwards [hav] with s hs
    simp [F, hs]

end Ostmann

end OAI
