import OAI.Combinatorics.MatchingPSD.TablePolynomials

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Averages
variable {X : Type u_1} {Y : Type u_2} [Fintype X] [Fintype Y]
lemma predicateAverage_equiv (e : X ≃ Y) (P : X → Prop) (Q : Y → Prop)
    (he : ∀ x, P x ↔ Q (e x)) (f : Y → ℝ) :
    predicateAverage P (f ∘ e) = predicateAverage Q f := by
  classical
  have hc : Fintype.card {x // P x} = Fintype.card {y // Q y} :=
    Fintype.card_congr (e.subtypeEquiv he)
  rw [predicateAverage_apply, predicateAverage_apply, hc]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Function.comp_apply, he])

lemma predicateAverage_eq_expect (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = 𝔼 x : {x // P x}, f x.1 := by
  rw [predicateAverage_apply, Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f

end Averages

noncomputable def lowProjection (h d : ℕ) : Module.End ℝ (Pairing (Vertices h) → ℝ) :=
  (matchingEquiv h).toLinearMap ∘ₗ (polynomialSpace h d).starProjection.toLinearMap ∘ₗ
    (matchingEquiv h).symm.toLinearMap

lemma lowProjection_mem (h d : ℕ) (f : Pairing (Vertices h) → ℝ) :
    lowProjection h d f ∈ lowDegree Pairing.edgeCoord d := by
  exact ((polynomialSpace h d).orthogonalProjectionOnto ((matchingEquiv h).symm f)).property

lemma lowProjection_equivariant (h d : ℕ) (p : Equiv.Perm (Vertices h))
    (f : Pairing (Vertices h) → ℝ) :
    lowProjection h d (Pairing.act p f) = Pairing.act p (lowProjection h d f) := by
  have he := starProjection_equivariant (polynomialSpace h d) (relabelIso p)
    (polynomialSpace_invariant p) (by simpa only [relabelIso_symm] using
      (polynomialSpace_invariant (d := d) p⁻¹)) ((matchingEquiv h).symm f)
  exact congrArg (matchingEquiv h) he.symm

lemma predicateAverage_relabel {V : Type u_3} [Fintype V] [DecidableEq V]
    (z : V → Fin 3) (t : Fin 6 → ℕ) (p : Equiv.Perm V) (f : Pairing V → ℝ) :
    predicateAverage (fun M => M.table z = t) (fun M => f (Pairing.relabel p M)) =
      predicateAverage (fun M => M.table (z ∘ p.symm) = t) f := by
  apply predicateAverage_equiv (Pairing.relabelEquiv p)
  intro M
  change M.table z = t ↔ (Pairing.relabel p M).table (z ∘ p.symm) = t
  rw [Pairing.table_relabel]
  have hz : (z ∘ p.symm) ∘ p = z := by funext a; simp
  rw [hz]

lemma expect_perm_colorings {V : Type u_4} {C : Type u_5} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (z : V → C) (φ : (V → C) → ℝ) :
    (𝔼 p : Equiv.Perm V, φ (z ∘ p)) =
      𝔼 w : Colorings V C (histogram z), φ w.1 := by
  have : Nonempty (Colorings V C (histogram z)) := ⟨⟨z,rfl⟩⟩
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  simpa only [mul_comm] using mean_perm_comp z φ

noncomputable def tableEnergy {V : Type u_6} [Fintype V] (s : Fin 3 → ℕ)
    (t : Fin 6 → ℕ) (f : Pairing V → ℝ) : ℝ :=
  𝔼 z : Colorings V (Fin 3) s, (predicateAverage (fun M => M.table z.1 = t) f)^2

lemma fiberAverage_eq_predicateAverage {X : Type u_7} {Z : Type u_8} [Fintype X] [Fintype Z]
    (P : X → Z → Prop) (f : X → ℝ) (z : Z) :
    fiberAverage P f z = predicateAverage (fun x => P x z) f := by
  simp only [fiberAverage, conditionalAverage, incidence, predicateAverage_apply,
    ite_mul, one_mul, zero_mul]

lemma fiberEnergy_eq {h : ℕ} (f₀ : Vertices h → Fin 3)
    (f : Pairing (Vertices h) → ℝ) :
    (∑ z, fiberAverage (tableRelation f₀) f z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) =
    tableEnergy (histogram f₀) (threeTable f₀) f := by
  simp_rw [fiberAverage_eq_predicateAverage]
  rw [tableEnergy, Fintype.expect_eq_sum_div_card]
  rfl

lemma permutation_energy_eq {V : Type u_9} [Fintype V] [DecidableEq V]
    (z : V → Fin 3) (t : Fin 6 → ℕ) (f : Pairing V → ℝ) :
    (𝔼 p : Equiv.Perm V, (predicateAverage (fun M => M.table z = t)
      (fun M => f (Pairing.relabel p M)))^2) = tableEnergy (histogram z) t f := by
  simp_rw [predicateAverage_relabel]
  calc
    _ = 𝔼 p : Equiv.Perm V,
        (predicateAverage (fun M => M.table (z ∘ p) = t) f)^2 := by
      apply Fintype.expect_equiv (Equiv.inv (Equiv.Perm V))
      intro p
      rfl
    _ = _ := expect_perm_colorings z (fun w =>
      (predicateAverage (fun M => M.table w = t) f)^2)

lemma uniform_permutation_smoothing (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (z : Vertices h → Fin 3), (∀ i, 0 < histogram z i) →
      ∀ (M₀ : Pairing (Vertices h)) (f : Pairing (Vertices h) → ℝ),
      (𝔼 p : Equiv.Perm (Vertices h),
        (predicateAverage (fun M => M.table z = M₀.table z)
          (fun M => (f - lowProjection h d f) (Pairing.relabel p M)))^2) ≤
      ((2*h : ℝ)^(2*K))⁻¹ * (𝔼 M, (f M)^2) := by
  obtain ⟨d,H,hd,hbound⟩ := uniform_table_smoothing K
  refine ⟨d,H,hd,?_⟩
  intro h hh z hz M₀ f
  obtain ⟨p₀, hp₀⟩ := Pairing.exists_relabel (standardPairing (H := Fin h)) M₀
  let f₀ := z ∘ p₀
  have hhist : histogram f₀ = histogram z := histogram_comp_perm z p₀
  have ht : threeTable f₀ = M₀.table z := by
    rw [← hp₀, Pairing.table_relabel, standardPairing_table]
  have hb := hbound h hh f₀ (by simpa only [hhist] using hz) ((matchingEquiv h).symm f)
  have heg : matchingEquiv h ((matchingEquiv h).symm f -
      polynomialProjection h d ((matchingEquiv h).symm f)) = f - lowProjection h d f := by
    simp only [map_sub, LinearEquiv.apply_symm_apply]
    rfl
  rw [fiberEnergy_eq, heg, ht, hhist] at hb
  rw [permutation_energy_eq, Fintype.expect_eq_sum_div_card]
  exact hb

end MatchingSmoothing

end OAI
