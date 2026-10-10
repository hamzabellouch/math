import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.EquivFin
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Algebra.LowerCrossRank
import OAI.Computability.PerfectCompleteness.Algebra.MatrixErasure
import OAI.Computability.PerfectCompleteness.Foundations.PartialTableInverse
import OAI.Computability.PerfectCompleteness.Sampling.RestrictionCrossLaw

namespace OAI


namespace PerfectCompleteness.LowerAffineSliceRank

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open BilinearGramCompression

variable {E : Type*} [AddCommGroup E] [Module F2 E]
  [Fintype E] [FiniteDimensional F2 E]
  {ℓ m : Nat}
  [Fintype (Module.Dual F2 E)]

def matrixRows (X : E →ₗ[F2] (Fin ℓ → F2)) : Fin ℓ → Module.Dual F2 E :=
  fun i => (LinearMap.proj i).comp X

def testedGram (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))
    (X : E →ₗ[F2] (Fin ℓ → F2)) : Matrix (Fin ℓ) (Fin ℓ) F2 :=
  gram F (matrixRows X)

omit [Fintype E] [FiniteDimensional F2 E] [Fintype (Module.Dual F2 E)] in
theorem coordinate_eq_sum (X : E →ₗ[F2] (Fin ℓ → F2))
    (q : Module.Dual F2 (Fin ℓ → F2)) :
    q.comp X = ∑ k, q (Pi.single k 1) • matrixRows X k := by
  apply LinearMap.ext
  intro e
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    matrixRows, LinearMap.proj_apply, smul_eq_mul]
  change q (X e) = ∑ k, q (Pi.single k 1) * X e k
  have hrows := pi_eq_sum_univ' (X e)
  calc
    q (X e) = q (∑ k : Fin ℓ, (X e k) • Pi.single k (1 : F2)) :=
      congrArg q hrows
    _ = ∑ k : Fin ℓ, (X e k) * q (Pi.single k 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := Finset.sum_congr rfl (fun k _ => mul_comm _ _)

omit [Fintype E] [FiniteDimensional F2 E] [Fintype (Module.Dual F2 E)] in
theorem coordinate_cross_rank_le
    (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))
    (X : E →ₗ[F2] (Fin ℓ → F2))
    (left right : Fin m → Module.Dual F2 (Fin ℓ → F2)) :
    Matrix.rank ((fun i j => F ((left i).comp X) ((right j).comp X)) :
      Matrix (Fin m) (Fin m) F2) ≤
      (testedGram F X).rank := by
  have hleft : combinations (matrixRows X)
      (fun i k => left i (Pi.single k 1)) = fun i => (left i).comp X := by
    funext i
    exact (coordinate_eq_sum X (left i)).symm
  have hright : combinations (matrixRows X)
      (fun j k => right j (Pi.single k 1)) = fun j => (right j).comp X := by
    funext j
    exact (coordinate_eq_sum X (right j)).symm
  have h := cross_rank_le F (matrixRows X)
    (fun i k => left i (Pi.single k 1))
    (fun j k => right j (Pi.single k 1))
  rw [hleft, hright] at h
  exact h

section Coordinates

variable {I : Type*} [Fintype I]
  (W : Submodule F2 E) (C' : Submodule F2 (Fin ℓ → F2))
  (b : Module.Basis I F2 C') (sel : (Fin m ⊕ Fin m) → I)

theorem slice_probability_le_of_coordinates (hsel : Function.Injective sel)
    (coordinates : I → Module.Dual F2 (Fin ℓ → F2))
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] (Fin ℓ → F2))
    (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))
    (r s : Nat) (hW : Module.finrank F2 W ≤ r)
    (hrank : s < Module.finrank F2 (LinearMap.range F)) :
    (FiniteDistribution.uniform (Parameter W C')).probability
        (fun A => decide ((testedGram F (translate W C' X A)).rank ≤ 1)) ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
        (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  have hlaw := RestrictionCrossLaw.crossMatrix_law W C' b sel hsel
    coordinates hcoordinates X F
  have hp := congrArg
    (fun μ : FiniteDistribution (Matrix (Fin m) (Fin m) F2) =>
      μ.probability (fun M => decide (M.rank ≤ 1))) hlaw
  simp only [FiniteDistribution.probability_pushforward] at hp
  have hsource := FiniteDistribution.probability_pushforward
    (Γ := Matrix (Fin m) (Fin m) F2)
    (FiniteDistribution.uniform (Parameter W C'))
    (fun A i j =>
      F ((coordinates (sel (Sum.inl i))).comp (translate W C' X A))
        ((coordinates (sel (Sum.inr j))).comp (translate W C' X A)))
    (fun M => decide (M.rank ≤ 1))
  have hp' := hsource.symm.trans hp
  have hcodim : Module.finrank F2
      (Module.Dual F2 E ⧸ W.dualAnnihilator) ≤ r := by
    rw [DualQuotientRows.codim_dualAnnihilator_eq]
    exact hW
  calc
    _ ≤ (FiniteDistribution.uniform (Parameter W C')).probability
        (fun A => decide (Matrix.rank ((fun i j =>
          F ((coordinates (sel (Sum.inl i))).comp (translate W C' X A))
            ((coordinates (sel (Sum.inr j))).comp (translate W C' X A))) :
              Matrix (Fin m) (Fin m) F2) ≤ 1)) := by
      apply FiniteDistribution.probability_mono
      intro A hA
      apply decide_eq_true
      exact (coordinate_cross_rank_le F (translate W C' X A)
        (fun i => coordinates (sel (Sum.inl i)))
        (fun j => coordinates (sel (Sum.inr j)))).trans (of_decide_eq_true hA)
    _ = _ := hp'
    _ ≤ _ := LowerCrossRank.cross_rank_probability_le_of_rank_gt F W.dualAnnihilator
      (fun i => (coordinates (sel (Sum.inl i))).comp X)
      (fun j => (coordinates (sel (Sum.inr j))).comp X) r s hcodim hrank

end Coordinates

theorem slice_rank_probability_le_of_rank_gt
    (W : Submodule F2 E) (C' : Submodule F2 (Fin ℓ → F2))
    (X : E →ₗ[F2] (Fin ℓ → F2))
    (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))
    (r s : Nat) (horder : order W C' ≤ r) (hrows : 2 * m + r ≤ ℓ)
    (hrank : s < Module.finrank F2 (LinearMap.range F)) :
    (FiniteDistribution.uniform (Parameter W C')).probability
        (fun A => decide ((testedGram F (translate W C' X A)).rank ≤ 1)) ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
        (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  let b := Module.finBasis F2 C'
  have hW : Module.finrank F2 W ≤ r := (Nat.le_add_right _ _).trans horder
  have hdim : 2 * m ≤ Module.finrank F2 C' := by
    have htotal := C'.finrank_quotient_add_finrank
    have hfull : Module.finrank F2 (Fin ℓ → F2) = ℓ := by
      simp [Module.finrank_fintype_fun_eq_card]
    rw [hfull] at htotal
    unfold order at horder
    omega
  obtain ⟨sel⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin m ⊕ Fin m) ≤
      Fintype.card (Fin (Module.finrank F2 C')) by
      simpa only [Fintype.card_sum, Fintype.card_fin, two_mul] using hdim)
  let coordinates : Fin (Module.finrank F2 C') → Module.Dual F2 (Fin ℓ → F2) :=
    fun i => Subspace.dualLift C' (b.coord i)
  have hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i := by
    intro i
    apply LinearMap.ext
    intro x
    change Subspace.dualLift C' (b.coord i) (x : Fin ℓ → F2) = b.coord i x
    exact Subspace.dualLift_of_subtype (φ := b.coord i) x
  exact slice_probability_le_of_coordinates W C' b sel sel.injective
    coordinates hcoordinates X F r s hW hrank


variable {Y : Type*} [Fintype Y]
  (f : (E →ₗ[F2] (Fin ℓ → F2)) → Option Y)
  (form : Y → Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))

private theorem probability_eq_expect_indicator {A : Type*} [Fintype A] [Nonempty A]
    (event : A → Bool) :
    (FiniteDistribution.uniform A).probability event =
      𝔼 a : A, if event a then (1 : ℝ) else 0 := by
  have h : (FiniteDistribution.uniform A).probability event =
      (FiniteDistribution.uniform A).expectation (fun a => if event a then (1 : ℝ) else 0) := by
    simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
  rw [h, FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

omit [Fintype Y] in
theorem dense_value_rank_le
    (tested : ∀ X y, f X = some y → (testedGram (form y) X).rank ≤ 1)
    (W : Submodule F2 E) (C' : Submodule F2 (Fin ℓ → F2))
    (X : E →ₗ[F2] (Fin ℓ → F2)) (y : Y)
    (r s : Nat) (ρ : ℝ) (horder : order W C' ≤ r) (hrows : 2 * m + r ≤ ℓ)
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ)
    (hdense : ρ < 𝔼 A : Parameter W C',
      restrict (PartialTableInverse.indicator f y) W C' X A) :
    Module.finrank F2 (LinearMap.range (form y)) ≤ s := by
  by_contra h
  have hbound := slice_rank_probability_le_of_rank_gt W C' X (form y) r s
    horder hrows (Nat.lt_of_not_ge h)
  have hdom : (𝔼 A : Parameter W C',
      restrict (PartialTableInverse.indicator f y) W C' X A) ≤
      (FiniteDistribution.uniform (Parameter W C')).probability
        (fun A => decide ((testedGram (form y) (translate W C' X A)).rank ≤ 1)) := by
    rw [probability_eq_expect_indicator]
    apply Finset.expect_le_expect
    intro A _
    by_cases hf : f (translate W C' X A) = some y
    · simp [restrict, PartialTableInverse.indicator, hf, tested _ _ hf]
    · simp only [restrict, PartialTableInverse.indicator, ite_eq_right hf]
      split_ifs <;> norm_num
  exact (not_le_of_gt hdense) (hdom.trans (hbound.trans herror))

theorem high_rank_agreement_lt
    [Fintype (E →ₗ[F2] (Fin ℓ → F2))]
    [Fintype ((Fin ℓ → F2) →ₗ[F2] E)]
    (tested : ∀ X y, f X = some y → (testedGram (form y) X).rank ≤ 1)
    (r s : Nat) (ρ η : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (hrows : 2 * m + r ≤ ℓ)
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ) :
    PartialTableInverse.nonzeroAgreement
      (MatrixErasure.erase f (fun X => ∃ y, f X = some y ∧
        Module.finrank F2 (LinearMap.range (form y)) ≤ s)) < η := by
  have hℓ : 0 < ℓ := by omega
  let : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  let T := fun X => ∃ y, f X = some y ∧
    Module.finrank F2 (LinearMap.range (form y)) ≤ s
  let g := MatrixErasure.erase f T
  have htested : ∀ X y, g X = some y → (testedGram (form y) X).rank ≤ 1 := by
    intro X y h
    exact tested X y ((MatrixErasure.erase_eq_some_iff f T X y).mp h).2
  by_contra h
  have hagreement : η ≤ PartialTableInverse.nonzeroAgreement g := le_of_not_gt h
  obtain ⟨y, W, C', X, horder, hdense⟩ :=
    PartialTableInverse.exists_dense_slice_nonzero r ρ η hρ hρ1 hconstants g hagreement
  have hrank := dense_value_rank_le g form htested W C' X y r s ρ horder hrows herror hdense
  have hnone (A : Parameter W C') : g (translate W C' X A) ≠ some y := by
    intro h
    have he := (MatrixErasure.erase_eq_some_iff f T _ y).mp h
    exact he.1 ⟨y, he.2, hrank⟩
  have hzero : (𝔼 A : Parameter W C',
      restrict (PartialTableInverse.indicator g y) W C' X A) = 0 := by
    apply Finset.expect_eq_zero
    intro A _
    simp [restrict, PartialTableInverse.indicator, hnone A]
  rw [hzero] at hdense
  exact (not_lt_of_ge hρ.le) hdense


end
end PerfectCompleteness.LowerAffineSliceRank

end OAI
