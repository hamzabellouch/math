import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_interior_flux_difference_ae {n : ℕ} (Q : Set (Coord n))
    (C : Coord n → Fin n → Fin n → ℝ) (P V : Fin n → Coord n → ℝ)
    (hsame : ∀ a, P a =ᵐ[volume.restrict (interior Q)] V a)
    (i : Fin n) (h : ℝ) :
    ∀ᵐ x ∂volume, x ∈ interior Q → x+Pi.single i h ∈ interior Q → ∀ j,
      realDifferenceQuotient i h (Q.indicator (fun y ↦ ∑ a, C y a j*P a y)) x =
        ∑ a, (C (x+Pi.single i h) a j*realDifferenceQuotient i h (Q.indicator (V a)) x+
          realDifferenceQuotient i h (fun y ↦ C y a j) x*(Q.indicator (V a)) x) := by
  have hall : ∀ᵐ x ∂volume.restrict (interior Q), ∀ a, P a x=V a x := ae_all_iff.mpr hsame
  have ht := real_ae_translation_endpoints isOpen_interior.measurableSet
    (fun x ↦ ∀ a, P a x=V a x) hall (Pi.single i h)
  filter_upwards [ht] with x hx
  intro hxi hti j
  have hxe := hx.1 hxi
  have hte := hx.2 hti
  have hxQ : x ∈ Q := interior_subset hxi
  have htQ : x+Pi.single i h ∈ Q := interior_subset hti
  have hid : realDifferenceQuotient i h (Q.indicator (fun y ↦ ∑ a, C y a j*P a y)) x =
      realDifferenceQuotient i h (fun y ↦ ∑ a, C y a j*(Q.indicator (V a)) y) x := by
    simp only [realDifferenceQuotient,indicator_of_mem hxQ,indicator_of_mem htQ,hxe,hte]
  rw [hid,realDifferenceQuotient_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact realDifferenceQuotient_mul i h _ _ x

end
end Yau

end OAI
