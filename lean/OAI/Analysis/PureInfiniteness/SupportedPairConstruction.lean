import OAI.Analysis.Nuclearity.NuclearCoefficientApproximation
import OAI.Analysis.PureInfiniteness.RelativeOneStepContraction
import OAI.Analysis.PureInfiniteness.SupportedTwoCopyMap
import OAI.Analysis.PureInfiniteness.UltrapowerCopiesExact
import OAI.Analysis.PureInfiniteness.NonunitalContractionLift
import OAI.Analysis.PureInfiniteness.RelativeCentralCuntz

namespace OAI

/-! The local relative Cuntz-pair construction. A single positive support
gives noncentral orthogonal copies. One-step approximation of their supported
two-copy map produces multiplicative local witnesses under the tensor-ideal
elementary-span hypothesis. -/

noncomputable section
open Filter
open scoped BigOperators ComplexOrder

namespace WeakPureInfiniteness

lemma norm_contractive_corner {D : Type*} [NonUnitalCStarAlgebra D]
    (r x s : D) (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1) : ‖star r * x * s‖ ≤ ‖x‖ := by
  calc
    _ ≤ (‖r‖ * ‖x‖) * ‖s‖ := by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (by simpa only [norm_star] using norm_mul_le (star r) x) (norm_nonneg s))
    _ ≤ (1 * ‖x‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hr (norm_nonneg x)) hs (norm_nonneg s) (by positivity)
    _ = ‖x‖ := by ring

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ)
  [Fact ((U : Filter ℕ) ≤ atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U

theorem finite_relative_pair_of_elementary_span (hP : MainGap.PropertyP A) (hA : Nuclear A)
    (hspan : ∀ (I : Type u) [Fintype I] (l : I → selfAdjoint N →L[ℝ] ℝ)
      (R : FunctionalTensorRepresentation l), R.elementarySpan U hA ι)
    (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Fin 2 → N, (∀ i, ‖v i‖ ≤ 1) ∧
      ∀ a ∈ F, ∀ i j, ‖star (v i) * ι a * v j - (if i = j then ι a else 0)‖ < ε := by
  classical
  obtain ⟨e, he, hen, hcut⟩ := exists_positive_contraction_sandwich_approximation F (ε / 2) (by positivity)
  obtain ⟨r, hr, _, hrel⟩ := ultrapower_relative_copies (I := Unit) (M := Fin 2) U hP
    (fun _ => ι e) (fun _ => map_nonneg ι he) (fun _ _ => Commute.refl _)
  have hrr (i j : Fin 2) : (star (r i) * r j) * ι e = if i = j then ι e else 0 := hrel () i j
  let T := supportedTwoCopyMap ι e r
  have hTn : ‖T‖ ≤ 1 := supportedTwoCopyMap_norm_le_one ι e he hen r hr hrr
  have hTi : ApproximatelyInnerAlong ι T := by
    intro G δ hδ
    refine ⟨2, (fun i => ι e * star (r i)), ?_⟩
    intro b _
    simpa only [T, supportedTwoCopyMap, twoInnerMap_apply, Fin.sum_univ_two,
      sub_self, norm_zero] using hδ
  have hTs := approximatelyOneStepAlong_of_nuclear_and_elementary_span U hP hA ι hspan hTi
  obtain ⟨d, hdn, hd⟩ := hTs.contractive_implementations ι T hTn F (ε / 2) (by positivity)
  refine ⟨fun i => d * r i, (fun i => (norm_mul_le _ _).trans
    ((mul_le_mul hdn (hr i) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))), ?_⟩
  intro a ha i j
  have herr : ‖star (r i) * (star d * ι a * d - T a) * r j‖ < ε / 2 :=
    (norm_contractive_corner _ _ _ (hr i) (hr j)).trans_lt
      (by simpa only [norm_sub_rev] using hd a ha)
  have hcorner : ‖star (r i) * T a * r j - (if i = j then ι a else 0)‖ < ε / 2 := by
    rw [show T = supportedTwoCopyMap ι e r from rfl,
      supportedTwoCopyMap_corner ι e he.isSelfAdjoint r hrr a i j]
    by_cases hij : i = j
    · simp only [hij, ite_true]
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le ι _).trans_lt (hcut a ha)
    · simpa only [hij, ite_false, sub_self, norm_zero] using (half_pos hε)
  have hsplit : star (d * r i) * ι a * (d * r j) - (if i = j then ι a else 0) =
      star (r i) * (star d * ι a * d - T a) * r j +
        (star (r i) * T a * r j - (if i = j then ι a else 0)) := by
    simp only [star_mul]
    noncomm_ring
  rw [hsplit]
  exact (norm_add_le _ _).trans_lt ((add_lt_add herr hcorner).trans_eq (by ring))

theorem identityDiagonalization_of_elementary_span (hP : MainGap.PropertyP A) (hA : Nuclear A)
    (hspan : ∀ (I : Type u) [Fintype I] (l : I → selfAdjoint N →L[ℝ] ℝ)
      (R : FunctionalTensorRepresentation l), R.elementarySpan U hA ι) :
    ContractiveIdentityDiagonalization A := by
  classical
  intro F ε hε
  obtain ⟨v, hv, happ⟩ := finite_relative_pair_of_elementary_span U hP hA hspan F hε
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)
  have hqc (b : A) : q (NonunitalGamma.boundedConstant (A := A) b) = ι b := rfl
  have hlift (i : Fin 2) : ∃ x : NormUltra.BoundedFamilies (fun _ : ℕ => A),
      q x = v i ∧ ‖x‖ ≤ 1 := nonunital_exists_contraction q
    NormUltra.QuotientAlgebra.mk_surjective (v i) (hv i)
  choose x hx hxn using hlift
  have he (a : F) (i j : Fin 2) : ∀ᶠ k in (U : Filter ℕ),
      ‖star (x i k) * a.val * x j k - (if i = j then a.val else 0)‖ < ε := by
    let y := star (x i) * NonunitalGamma.boundedConstant (A := A) a.val * x j -
      (if i = j then NonunitalGamma.boundedConstant (A := A) a.val else 0)
    have hy : ‖q y‖ < ε := by
      simpa only [y, map_sub, map_mul, map_star, apply_ite, map_zero, hx, hqc] using happ a.val a.property i j
    have hyk := NonunitalGamma.eventually_norm_lt_of_quotient_norm_lt U y hy
    filter_upwards [hyk] with k hk
    by_cases hij : i = j
    · simp only [y, hij, ite_true] at hk ⊢
      exact hk
    · simp only [y, hij, ite_false] at hk ⊢
      exact hk
  have hall : ∀ᶠ k in (U : Filter ℕ), ∀ a : F, ∀ i j : Fin 2,
      ‖star (x i k) * a.val * x j k - (if i = j then a.val else 0)‖ < ε :=
    eventually_all.mpr fun a => eventually_all.mpr fun i => eventually_all.mpr fun j => he a i j
  obtain ⟨k, hk⟩ := hall.exists
  refine ⟨x 0 k, x 1 k,
    (NormUltra.BoundedFamilies.norm_coordinate_le _ _).trans (hxn 0),
    (NormUltra.BoundedFamilies.norm_coordinate_le _ _).trans (hxn 1), ?_⟩
  intro a ha
  exact ⟨by simpa only [ite_true] using hk ⟨a, ha⟩ 0 0,
    by simpa only [ite_true] using hk ⟨a, ha⟩ 1 1,
    by simpa using hk ⟨a, ha⟩ 0 1⟩

theorem centralOInfinity_of_nuclear_and_elementary_span
    (hP : MainGap.PropertyP A) (hA : Nuclear A)
    (hspan : ∀ (I : Type u) [Fintype I] (l : I → selfAdjoint N →L[ℝ] ℝ)
      (R : FunctionalTensorRepresentation l), R.elementarySpan U hA ι) :
    Nonempty (OInfinity →⋆ₐ[ℂ] NonunitalGamma.CentralSequenceAlgebra (A := A) U) :=
  centralOInfinityMap_of_identityDiagonalization U
    (identityDiagonalization_of_elementary_span U hP hA hspan)

end WeakPureInfiniteness

end

end OAI
