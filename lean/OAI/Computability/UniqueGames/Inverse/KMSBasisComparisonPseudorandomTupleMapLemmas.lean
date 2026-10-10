import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.UniqueGames.Analysis.A5FrequencyTransportLemmas
import OAI.Computability.UniqueGames.Analysis.HybridCounting
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionComplementLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionPresentationLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesRankLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyImageTransportCoreLemmas
import OAI.Computability.UniqueGames.Inverse.KMSBasisComparisonLemmas
import OAI.Computability.UniqueGames.Inverse.KMSBasisComparisonNeighborsRetention
import OAI.Computability.UniqueGames.Inverse.KMSFoundationLemmas

namespace OAI

section

/-! The restricted tuple law is the actual linear-map lift law in coordinates,
with all singular tuples still present in the uniform denominator. -/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison

variable {n q t : ℕ}

def tupleBasis (q t : ℕ) : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient (q + t)) :=
  (Pi.basisFun F2 (Fin (q + t))).reindex finSumFinEquiv.symm

def tupleMapEquiv : ((Fin q ⊕ Fin t) → Ambient n) ≃ BasisMap n (q + t) :=
  ((tupleBasis q t).constr F2).toEquiv

def tupleMap (x : (Fin q ⊕ Fin t) → Ambient n) : BasisMap n (q + t) :=
  (tupleBasis q t).constr F2 x

theorem tupleMap_range (x : (Fin q ⊕ Fin t) → Ambient n) :
    LinearMap.range (tupleMap x) = Submodule.span F2 (Set.range x) :=
  (tupleBasis q t).constr_range F2

@[simp] theorem tupleMap_basis (x : (Fin q ⊕ Fin t) → Ambient n)
    (i : Fin q ⊕ Fin t) : tupleMap x (tupleBasis q t i) = x i :=
  (tupleBasis q t).constr_basis F2 x i

theorem tupleMap_injective_iff (x : (Fin q ⊕ Fin t) → Ambient n) :
    Function.Injective (tupleMap x) ↔ LinearIndependent F2 x := by
  constructor
  · intro h
    have hi := (tupleBasis q t).linearIndependent.map' (tupleMap x)
      (LinearMap.ker_eq_bot.mpr h)
    simpa only [Function.comp_def, tupleMap_basis] using hi
  · intro h
    exact (tupleBasis q t).injective_constr_of_linearIndependent h

theorem inLift_tupleMap_iff (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) (z : Fin t → W) :
    InLift S (tupleMap (joinedTuple Q W z)) ↔ completionEvent S Q W z := by
  constructor
  · intro h
    have hi := (tupleMap_injective_iff _).mp (injective_of_inLift h)
    obtain ⟨L, hLS, hr⟩ := h
    refine ⟨hi, ?_⟩
    have he : completionVertex Q W ⟨z, hi⟩ = L := by
      apply Subtype.ext
      exact (tupleMap_range _).symm.trans hr
    simpa only [he] using hLS
  · rintro ⟨hi, hmem⟩
    exact ⟨completionVertex Q W ⟨z, hi⟩, hmem, tupleMap_range _⟩

/-- The tuple density equals the normalized expectation of the actual lift's
indicator on the prescribed basis-coordinate restriction. -/
theorem restrictedLiftDensity_eq_expect (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    restrictedLiftDensity S Q W =
      𝔼 z : Fin t → W, liftedIndicator S (tupleMap (joinedTuple Q W z)) := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [liftedIndicator, inLift_tupleMap_iff]
  rw [Finset.sum_boole]
  simp only [restrictedLiftDensity, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- KMS Lemma 2.8 in the actual linear-map coordinates, with the stronger ε
bound supplied by exact equal-size completion fibers. -/
theorem grassmann_pseudorandom_lift_expect {r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n (q + t))) (hS : GrassmannPseudorandom S r ε)
    (hε : 0 ≤ ε) (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 z : Fin t → W, liftedIndicator S (tupleMap (joinedTuple Q W z))) ≤ ε := by
  rw [← restrictedLiftDensity_eq_expect]
  exact grassmann_pseudorandom_restricted S hS hε Q W hbudget

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

section

/-!
The KMS restricted-tuple bound in any adapted basis, followed by an exact
uniform affine translation of the free coordinates. No generic rank-level
inequality is used: this is a change of coordinates for the actual lift.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom

variable {n ell q t r : ℕ} {ε : ℝ}

/-- The independent tuple law has the same bound in every basis of the domain.
The indicator depends only on the actual range of the constructed map. -/
theorem lifted_expect_in_basis (S : Finset (Vertex n ell))
    (hS : GrassmannPseudorandom S r ε) (hε : 0 ≤ ε)
    (b : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 z : Fin t → W, liftedIndicator S (b.constr F2 (joinedTuple Q W z))) ≤ ε := by
  have hdim : ell = q + t := by
    simpa [Ambient] using Module.finrank_eq_card_basis b
  subst ell
  have hc := grassmann_pseudorandom_lift_expect S hS hε Q W hbudget
  convert hc using 1
  apply Finset.expect_congr rfl
  intro z _
  unfold liftedIndicator InLift
  rw [b.constr_range F2, tupleMap_range]

/-- Coordinates of a uniform linear map, translated by a fixed linear map,
are still exactly uniform. This also covers zero-dimensional free domains. -/
def affineCoordinates {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T : E →ₗ[F2] W) :
    (E →ₗ[F2] W) ≃ (Fin t → W) :=
  ((b.constr F2).toEquiv).symm.trans (Equiv.addLeft (fun i => T (b i)))

@[simp] theorem affineCoordinates_apply {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T H : E →ₗ[F2] W) (i : Fin t) :
    affineCoordinates b T H i = T (b i) + H (b i) := rfl

/-- Actual uniform affine free-coordinate noise satisfies the tuple bound. -/
theorem lifted_expect_shifted_basis {E0 : Type*}
    [AddCommGroup E0] [Module F2 E0]
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S r ε) (hε : 0 ≤ ε)
    (b : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    [Fintype (E0 →ₗ[F2] W)]
    (b0 : Module.Basis (Fin t) F2 E0) (T0 : E0 →ₗ[F2] W)
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 H : E0 →ₗ[F2] W, liftedIndicator S
      (b.constr F2 (joinedTuple Q W (fun i => T0 (b0 i) + H (b0 i))))) ≤ ε := by
  have heq : (𝔼 H : E0 →ₗ[F2] W, liftedIndicator S
      (b.constr F2 (joinedTuple Q W (fun i => T0 (b0 i) + H (b0 i))))) =
      𝔼 z : Fin t → W, liftedIndicator S (b.constr F2 (joinedTuple Q W z)) := by
    apply Fintype.expect_equiv (affineCoordinates b0 T0)
    intro H
    rfl
  rw [heq]
  exact lifted_expect_in_basis S hS hε b Q W hbudget

end
end UniqueGamesTheorem.Inverse.KMSAffineRestriction

end

section

/-!
Grassmann interval pseudorandomness controls actual arbitrary affine matrix
restrictions, at twice the restriction order. The proof chooses a bounded
prefix containing the vanishing subspace and all nonhomogeneous directions,
splits the exact quotient-map parameter law, and applies the tuple estimate.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open KMSAffineRestrictionSplit

variable {n ell q t : ℕ}

/-- Basis obtained from a genuine complementary domain decomposition. -/
def complementBasis (U E0 : Submodule F2 (Ambient ell)) (hc : IsCompl U E0)
    (bU : Module.Basis (Fin q) F2 U) (b0 : Module.Basis (Fin t) F2 E0) :
    Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell) :=
  (bU.prod b0).map (Submodule.prodEquivOfIsCompl U E0 hc)

@[simp] theorem complementBasis_inl (U E0 : Submodule F2 (Ambient ell))
    (hc : IsCompl U E0) (bU : Module.Basis (Fin q) F2 U)
    (b0 : Module.Basis (Fin t) F2 E0) (i : Fin q) :
    complementBasis U E0 hc bU b0 (Sum.inl i) = (bU i : Ambient ell) := by
  simp [complementBasis, Module.Basis.prod_apply]

@[simp] theorem complementBasis_inr (U E0 : Submodule F2 (Ambient ell))
    (hc : IsCompl U E0) (bU : Module.Basis (Fin q) F2 U)
    (b0 : Module.Basis (Fin t) F2 E0) (i : Fin t) :
    complementBasis U E0 hc bU b0 (Sum.inr i) = (b0 i : Ambient ell) := by
  simp [complementBasis, Module.Basis.prod_apply]

/-- The affine center restricted to directions whose images already lie in W. -/
def freeCenter (E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (T : BasisMap n ell) (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T)) : E0 →ₗ[F2] W :=
  (T.comp E0.subtype).codRestrict W fun x =>
    (Submodule.Quotient.mk_eq_zero W).mp (hE0 x.property)

@[simp] theorem freeCenter_coe (E0 : Submodule F2 (Ambient ell))
    (W : Submodule F2 (Ambient n)) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T)) (x : E0) :
    (freeCenter E0 W T hE0 x : Ambient n) = T x := rfl

/-- Exact pointwise identity for the actual affine slice after splitting its
parameters. The fixed prefix includes the affine intercept. -/
theorem translate_join_eq_constr
    (D U E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (hDU : D ≤ U) (hc : IsCompl U E0) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T))
    (bU : Module.Basis (Fin q) F2 U) (b0 : Module.Basis (Fin t) F2 E0)
    (B : Parameter (localVanishing D U) W) (C : E0 →ₗ[F2] W) :
    translate D W T (join D U E0 W hDU hc B C) =
      (complementBasis U E0 hc bU b0).constr F2
        (joinedTuple
          (fun i => T (bU i) + (B ((localVanishing D U).mkQ (bU i)) : Ambient n)) W
          (fun i => freeCenter E0 W T hE0 (b0 i) + C (b0 i))) := by
  apply (complementBasis U E0 hc bU b0).ext
  intro i
  rw [Module.Basis.constr_basis]
  cases i with
  | inl i =>
      simp only [complementBasis_inl, joinedTuple, Sum.elim_inl,
        Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_left]
  | inr i =>
      simp only [complementBasis_inr, joinedTuple, Sum.elim_inr,
        Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_right]
      rfl

/-- A bounded adapted prefix controls the entire affine restriction law. -/
theorem affine_expect_of_complement {r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S r ε) (hε : 0 ≤ ε)
    (D U E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (hDU : D ≤ U) (hc : IsCompl U E0) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T))
    (hbudget : Module.finrank F2 U + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A) ≤ ε := by
  rw [expect_restrict D U E0 W hDU hc T]
  apply Finset.expect_le Finset.univ_nonempty
  intro B _
  let bU := Module.finBasis F2 U
  let b0 := Module.finBasis F2 E0
  have heq :
      (𝔼 C : E0 →ₗ[F2] W,
        liftedIndicator S (translate D W T (join D U E0 W hDU hc B C))) =
      𝔼 C : E0 →ₗ[F2] W,
        liftedIndicator S ((complementBasis U E0 hc bU b0).constr F2
          (joinedTuple
            (fun i => T (bU i) + (B ((localVanishing D U).mkQ (bU i)) : Ambient n)) W
            (fun i => freeCenter E0 W T hE0 (b0 i) + C (b0 i)))) := by
    apply Finset.expect_congr rfl
    intro C _
    rw [translate_join_eq_constr D U E0 W hDU hc T hE0 bU b0 B C]
  rw [heq]
  exact lifted_expect_shifted_basis S hS hε (complementBasis U E0 hc bU b0)
    _ W b0 (freeCenter E0 W T hE0) hbudget

/-- Every actual affine restriction of order d is sparse if all Grassmann
intervals of complexity at most 2d are sparse. Both sampling factors remain
uniform on their full finite spaces. -/
theorem affine_expect_bound {d : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S (2 * d) ε)
    (hε : 0 ≤ ε) (D : Submodule F2 (Ambient ell))
    (W : Submodule F2 (Ambient n)) (T : BasisMap n ell)
    (horder : order D W ≤ d) :
    (𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A) ≤ ε := by
  obtain ⟨U, E0, hDU, hE0, hc, hdim⟩ :=
    KMSAffineRestrictionComplement.exists_bounded_complement D W T
  have hcodim : n - Module.finrank F2 W = Module.finrank F2 (KMS.Ambient n ⧸ W) := by
    have hd := W.finrank_quotient_add_finrank
    have hn : Module.finrank F2 (KMS.Ambient n) = n := by simp [KMS.Ambient]
    rw [hn] at hd
    omega
  apply affine_expect_of_complement S hS hε D U E0 W hDU hc T hE0
  rw [hcodim]
  change Module.finrank F2 D + Module.finrank F2 (KMS.Ambient n ⧸ W) ≤ d at horder
  omega

/-- The normalized squared restriction norm is exactly the same sparse
probability because the full-rank lift is Boolean. -/
theorem affine_squared_expect_bound {d : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S (2 * d) ε)
    (hε : 0 ≤ ε) (D : Submodule F2 (Ambient ell))
    (W : Submodule F2 (Ambient n)) (T : BasisMap n ell)
    (horder : order D W ≤ d) :
    (𝔼 A : Parameter D W, (restrict (liftedIndicator S) D W T A) ^ 2) ≤ ε := by
  have heq : (𝔼 A : Parameter D W, (restrict (liftedIndicator S) D W T A) ^ 2) =
      𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A := by
    apply Finset.expect_congr rfl
    intro A _
    unfold restrict liftedIndicator
    split <;> norm_num
  rw [heq]
  exact affine_expect_bound S hS hε D W T horder

end
end UniqueGamesTheorem.Inverse.KMSAffineRestriction

end

section

/-!
# Ordered-basis retention versus Grassmann retention

This is the sampling comparison in KMS Lemma 2.7. The original experiment
uses all functionals and all directions, including zero. Its good event
induces exactly the full Grassmann-neighbor law; all other outcomes contribute
at most their explicit probability mass. Initial bases push forward uniformly
to the original Grassmann set.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

/-- The complete rank-one update experiment at a specified starting map. -/
def fullStepRetention {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ :=
  𝔼 p : Functional ell × KMS.Ambient n,
    liftedIndicator S (rankOneUpdate X p.1 p.2)

/-- Start uniformly in the lifted set, then run the unconditioned update. -/
def liftRetention {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : ℝ :=
  𝔼 X : lift S, fullStepRetention S X.val

/-- Equivalence of the two explicit presentations of the good sampling event. -/
def goodParametersEquiv {n ell : ℕ} (X : BasisMap n ell) :
    goodParameters X ≃ OutsideNeighborFactors X where
  toFun p := ⟨⟨p.val.1, ((mem_goodParameters X p.val).mp p.property).1⟩,
    ⟨p.val.2, ((mem_goodParameters X p.val).mp p.property).2⟩⟩
  invFun p := ⟨(p.1.val, p.2.val),
    (mem_goodParameters X _).mpr ⟨p.1.property, p.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Good-event conditioning is the exact full-neighbor Grassmann retention. -/
theorem goodParameters_expect {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    (goodParameters X).expect
      (fun p => liftedIndicator S (rankOneUpdate X p.1 p.2)) =
        KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX)) := by
  rw [← expect_coe_eq]
  calc
    _ = 𝔼 p : OutsideNeighborFactors X,
        liftedIndicator S (rankOneUpdate X p.1.val p.2.val) :=
      Fintype.expect_equiv (goodParametersEquiv X) _ _ (fun _ => rfl)
    _ = _ := outsideNeighbor_retention S X hX

/-- Quantitative local comparison, with a slightly smaller exceptional-mass
bound than the stated KMS Lemma 2.7. -/
theorem fullStepRetention_compare {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    |fullStepRetention S X -
      KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX))| ≤
        ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  rw [← goodParameters_expect S X hX]
  apply (abs_expect_sub_restrict_le (goodParameters X)
    (fun p => liftedIndicator S (rankOneUpdate X p.1 p.2))
    (fun p => liftedIndicator_nonneg S _) (fun p => liftedIndicator_le_one S _)).trans
  simpa only [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] using
    (badParameters_mass_le_compl X hX)

/-- Choosing a uniform accepted ordered basis chooses a uniform element of
the original Grassmann set. -/
theorem liftRange_retention_expect {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    (𝔼 X : lift S,
      KMS.relativeDensity S (KMS.neighbors (liftRange S X).val)) = KMS.retention S := by
  let : Nonempty (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
    ⟨LinearEquiv.refl _ _⟩
  rw [expect_eq_of_uniform_fibers (liftRange S) (liftRangeFiberAut S)
    (fun L : S => KMS.relativeDensity S (KMS.neighbors L.val))]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_coe, KMS.retention]
  congr 1
  exact (Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun L => KMS.relativeDensity S (KMS.neighbors L))).symm

/-- The actual full sampling-law comparison for the lifted Grassmann set. -/
theorem liftRetention_compare {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) :
    |liftRetention S - KMS.retention S| ≤
      ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by
  have hLift := (lift_nonempty_iff S).mpr hS
  let : Nonempty (lift S) := ⟨⟨hLift.choose, hLift.choose_spec⟩⟩
  rw [liftRetention, ← liftRange_retention_expect S,
    ← Finset.expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro X _
  exact fullStepRetention_compare S X.val
    (injective_of_inLift ((mem_lift S X.val).mp X.property))

/-- The bound in the primary statement, with ordinary quotient notation
instead of an integer exponent `ell - n`. -/
theorem liftRetention_compare_kms {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) :
    |liftRetention S - KMS.retention S| ≤
      ((2 : ℝ) ^ ell)⁻¹ + 2 * ((2 : ℝ) ^ ell / (2 : ℝ) ^ n) := by
  have hratio : 0 ≤ (2 : ℝ) ^ ell / (2 : ℝ) ^ n := by positivity
  exact (liftRetention_compare S hS).trans (by linarith)

/-- The indicator's density in the full linear-map space. -/
def liftDensity {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : ℝ :=
  𝔼 X : BasisMap n ell, liftedIndicator S X

theorem liftDensity_eq_card {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    liftDensity S = ((lift S).card : ℝ) / Fintype.card (BasisMap n ell) := by
  simp only [liftDensity, liftedIndicator, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, lift]

theorem liftDensity_pos {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (hS : S.Nonempty) : 0 < liftDensity S := by
  rw [liftDensity_eq_card]
  apply div_pos
  · exact Nat.cast_pos.mpr ((lift_nonempty_iff S).mpr hS).card_pos
  · exact Nat.cast_pos.mpr Fintype.card_pos

/-- Fourier correlation uses the full ambient space. This identity is the
exact conversion to the conditional-start retention and preserves density. -/
theorem liftDensity_mul_retention {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    liftDensity S * liftRetention S =
      𝔼 X : BasisMap n ell, liftedIndicator S X * fullStepRetention S X := by
  rw [liftDensity_eq_card, liftRetention, expect_coe_eq, mass_mul_expect,
    Fintype.expect_eq_sum_div_card]
  congr 1
  simp only [liftedIndicator, ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  rfl

/-- Swapping the independent factors matches the Fourier noise convention
of first choosing a direction, then a functional, including both zero cases. -/
theorem fullStepRetention_eq_noise {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) :
    fullStepRetention S X =
      𝔼 y : KMS.Ambient n, 𝔼 a : Functional ell,
        liftedIndicator S (X + a.smulRight y) := by
  unfold fullStepRetention
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact Finset.expect_comm _ _ _

/-- A proved ambient correlation bound converts directly to the conditional
retention bound; positive density follows from the actual nonempty lift. -/
theorem liftRetention_le_of_correlation_le {n ell : ℕ}
    (S : Finset (KMS.Vertex n ell)) (hS : S.Nonempty) (ζ : ℝ)
    (hc : (𝔼 X : BasisMap n ell,
      liftedIndicator S X * fullStepRetention S X) ≤ ζ * liftDensity S) :
    liftRetention S ≤ ζ := by
  rw [← liftDensity_mul_retention S, mul_comm ζ (liftDensity S)] at hc
  exact le_of_mul_le_mul_left hc (liftDensity_pos S hS)

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical
open KMSBasisComparisonPseudorandom

/-- The precise analytic obligation at the ordered-basis lift. Its constants
are fixed before the tuple length, which is fixed before the ambient size. -/
def LiftExpansionPrinciple : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∃ r ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ S : Finset (KMS.Vertex n ell), S.Nonempty →
            TuplePseudorandom S r ε → liftRetention S ≤ ζ

/-- Elementary eventual decay, using Archimedean unboundedness of powers.
No dimensional rate is hidden in a limit or a filter assumption. -/
theorem exists_binary_ratio_threshold (c ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → c / (2 : ℝ) ^ n ≤ ε := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (c / ε) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨k, fun n hn => ?_⟩
  have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  have hcp : c / ε ≤ (2 : ℝ) ^ n := hk.le.trans hp
  have hc : c ≤ (2 : ℝ) ^ n * ε := (div_le_iff₀ hε).mp hcp
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  simpa only [mul_comm] using hc

/-- Positive relative density implies a nonempty intersection, even though
relative density itself is defined to be zero on empty intervals. -/
theorem nonempty_of_relativeDensity_pos {Ω : Type*} [DecidableEq Ω]
    (S I : Finset Ω) (h : 0 < KMS.relativeDensity S I) : (S ∩ I).Nonempty := by
  by_contra hn
  have he : S ∩ I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [KMS.relativeDensity, he] at h

/-- The complete inverse implication from the explicit analytic lift theorem
to the dimension-uniform Grassmann theorem required by the inverse. -/
theorem expansion_of_liftExpansion (h : LiftExpansionPrinciple) :
    KMS.ExpansionPrinciple := by
  intro ζ hζ hζ1
  obtain ⟨ε, hε, hε1, r, ellA, hA⟩ :=
    h (ζ / 2) (by positivity) (by linarith)
  obtain ⟨ellE, hEllE⟩ := exists_binary_ratio_threshold 1 (ζ / 8) (by positivity)
  refine ⟨ε, hε, hε1, max r 1, le_max_right _ _, max ellA ellE, ?_⟩
  intro ell hEll
  obtain ⟨nA, hnA⟩ := hA ell ((le_max_left _ _).trans hEll)
  obtain ⟨nE, hnE⟩ := exists_binary_ratio_threshold ((2 : ℝ) ^ ell)
    (ζ / 8) (by positivity)
  refine ⟨max nA nE, ?_⟩
  intro n hn S hS hret
  have hError : ((2 : ℝ) ^ ell)⁻¹ + (2 : ℝ) ^ ell / (2 : ℝ) ^ n ≤ ζ / 4 := by
    have he := hEllE ell ((le_max_right _ _).trans hEll)
    have hn' := hnE n ((le_max_right _ _).trans hn)
    rw [one_div] at he
    linarith
  by_contra hNo
  have hPseudo : GrassmannPseudorandom S r ε := by
    intro A B hAB hbudget
    by_contra hd
    have hd' : ε < KMS.relativeDensity S (KMS.interval A B) := lt_of_not_ge hd
    apply hNo
    exact ⟨A, B, hAB, hbudget.trans (le_max_left _ _),
      nonempty_of_relativeDensity_pos S _ (hε.trans hd'), hd'.le⟩
  have hLift : liftRetention S ≤ ζ / 2 :=
    hnA n ((le_max_left _ _).trans hn) S hS
      (grassmann_pseudorandom_lift S hPseudo hε.le)
  have hCmp := (abs_le.mp ((liftRetention_compare S hS).trans hError)).1
  linarith

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
# Ordered tuples and binary linear maps

The ordinary tuple law is the full uniform map law under the standard-basis
equivalence, before any conditioning on linear independence. The generic
finite index permits both `Fin ell` and the split index `Fin q ⊕ Fin t`.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

/-- A finite family specifies exactly one linear map on its coordinate space. -/
def familyLinearEquiv (n : ℕ) (ι : Type*) [Fintype ι] :
    (ι → KMS.Ambient n) ≃ₗ[KMS.F2] ((ι → KMS.F2) →ₗ[KMS.F2] KMS.Ambient n) :=
  (Pi.basisFun KMS.F2 ι).constr KMS.F2

@[simp] theorem familyLinearEquiv_apply_basis (n : ℕ) (ι : Type*) [Fintype ι]
    (v : ι → KMS.Ambient n) (i : ι) :
    familyLinearEquiv n ι v (Pi.basisFun KMS.F2 ι i) = v i :=
  (Pi.basisFun KMS.F2 ι).constr_basis KMS.F2 v i

@[simp] theorem familyLinearEquiv_symm_apply (n : ℕ) (ι : Type*) [Fintype ι]
    (X : (ι → KMS.F2) →ₗ[KMS.F2] KMS.Ambient n) (i : ι) :
    (familyLinearEquiv n ι).symm X i = X (Pi.basisFun KMS.F2 ι i) := rfl

theorem familyLinearEquiv_range (n : ℕ) (ι : Type*) [Fintype ι]
    (v : ι → KMS.Ambient n) :
    LinearMap.range (familyLinearEquiv n ι v) = Submodule.span KMS.F2 (Set.range v) :=
  (Pi.basisFun KMS.F2 ι).constr_range KMS.F2

/-- Full rank of the corresponding map is exactly independence of the tuple. -/
theorem familyLinearEquiv_injective_iff (n : ℕ) (ι : Type*) [Fintype ι]
    (v : ι → KMS.Ambient n) :
    Function.Injective (familyLinearEquiv n ι v) ↔ LinearIndependent KMS.F2 v := by
  constructor
  · intro h
    have hv := (Pi.basisFun KMS.F2 ι).linearIndependent.map'
      (familyLinearEquiv n ι v) (LinearMap.ker_eq_bot.mpr h)
    simpa only [Function.comp_def, familyLinearEquiv_apply_basis] using hv
  · intro h
    exact (Pi.basisFun KMS.F2 ι).injective_constr_of_linearIndependent h

theorem family_expect {n : ℕ} {ι : Type*} [Fintype ι]
    [Fintype ((ι → KMS.F2) →ₗ[KMS.F2] KMS.Ambient n)]
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (g : ((ι → KMS.F2) →ₗ[KMS.F2] KMS.Ambient n) → M) :
    (𝔼 v : ι → KMS.Ambient n, g (familyLinearEquiv n ι v)) = 𝔼 X, g X :=
  Fintype.expect_equiv (familyLinearEquiv n ι).toEquiv _ _ (fun _ => rfl)

def tupleLinearEquiv (n ell : ℕ) :
    (Fin ell → KMS.Ambient n) ≃ₗ[KMS.F2] BasisMap n ell :=
  familyLinearEquiv n (Fin ell)

def tupleEquiv (n ell : ℕ) : (Fin ell → KMS.Ambient n) ≃ BasisMap n ell :=
  (tupleLinearEquiv n ell).toEquiv

theorem basisMap_card (n ell : ℕ) : Fintype.card (BasisMap n ell) = 2 ^ (n * ell) := by
  rw [← Fintype.card_congr (tupleEquiv n ell)]
  simp [KMS.Ambient, KMS.F2, ← pow_mul]

@[simp] theorem tupleLinearEquiv_apply_basis (n ell : ℕ)
    (v : Fin ell → KMS.Ambient n) (i : Fin ell) :
    tupleLinearEquiv n ell v (Pi.basisFun KMS.F2 (Fin ell) i) = v i :=
  familyLinearEquiv_apply_basis _ _ _ _

@[simp] theorem tupleLinearEquiv_symm_apply (n ell : ℕ)
    (X : BasisMap n ell) (i : Fin ell) :
    (tupleLinearEquiv n ell).symm X i = X (Pi.basisFun KMS.F2 (Fin ell) i) := rfl

theorem tupleLinearEquiv_range (n ell : ℕ) (v : Fin ell → KMS.Ambient n) :
    LinearMap.range (tupleLinearEquiv n ell v) = Submodule.span KMS.F2 (Set.range v) :=
  familyLinearEquiv_range _ _ _

theorem tupleLinearEquiv_injective_iff (n ell : ℕ) (v : Fin ell → KMS.Ambient n) :
    Function.Injective (tupleLinearEquiv n ell v) ↔ LinearIndependent KMS.F2 v :=
  familyLinearEquiv_injective_iff _ _ _

/-- The complete uniform tuple law equals the complete uniform map law. -/
theorem tuple_expect {n ell : ℕ} {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (g : BasisMap n ell → M) :
    (𝔼 v : Fin ell → KMS.Ambient n, g (tupleLinearEquiv n ell v)) = 𝔼 X, g X :=
  Fintype.expect_equiv (tupleEquiv n ell) _ _ (fun _ => rfl)

/-- On tuples, a rank-one map perturbation adds the same vector at coordinates
selected by the corresponding binary functional. -/
theorem rankOne_tuple_coordinate {n ell : ℕ} (X : BasisMap n ell)
    (l : KMS.Ambient ell →ₗ[KMS.F2] KMS.F2) (v : KMS.Ambient n) (i : Fin ell) :
    (tupleLinearEquiv n ell).symm (X + l.smulRight v) i =
      (tupleLinearEquiv n ell).symm X i + l (Pi.basisFun KMS.F2 (Fin ell) i) • v :=
  rfl

/-- The lift tests precisely whether the tuple spans a selected Grassmann
vertex; independence is forced by membership in the selected dimension. -/
theorem inLift_tuple_iff {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (v : Fin ell → KMS.Ambient n) :
    InLift S (tupleLinearEquiv n ell v) ↔
      ∃ L ∈ S, Submodule.span KMS.F2 (Set.range v) = L.val := by
  simp only [InLift, tupleLinearEquiv_range]

theorem linearIndependent_of_inLift_tuple {n ell : ℕ}
    {S : Finset (KMS.Vertex n ell)} {v : Fin ell → KMS.Ambient n}
    (h : InLift S (tupleLinearEquiv n ell v)) : LinearIndependent KMS.F2 v :=
  (tupleLinearEquiv_injective_iff n ell v).mp (injective_of_inLift h)

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.DerivativeDegree

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual selector multiplicity on frequencies of rank at most `d`.
This uses only the proved finite subspace count and Parseval. -/
theorem selector_energy_le (d : ℕ) (g : (E →ₗ[F2] F) → ℝ)
    (hg : DegreeAtMost d g) :
    hybridSelectorEnergy d g ≤ (2 : ℝ) ^ (3 * d * d) * (𝔼 X, g X ^ 2) := by
  unfold hybridSelectorEnergy hybridProjector
  apply selector_energy_sum_le
  intro Y hY
  have hrank : Module.finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hY (hg Y (Nat.lt_of_not_ge hn))
  have hc := HybridCounting.card_hybridIndex_le Y d hrank
  have hcount : selectorMultiplicity
      (fun s : HybridIndex (E := E) (F := F) d =>
        fun Y => LinearIdentities.Hybrid Y s.val.1 s.val.2) Y =
      Nat.card {s : HybridIndex (E := E) (F := F) d //
        LinearIdentities.Hybrid Y s.val.1 s.val.2} := by
    simp only [selectorMultiplicity, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcount]
  exact_mod_cast hc

/-- Generic closure of the fourth-moment estimate from a uniform bound on
the actual hybrid derivatives. Its eventual KMS application must prove `hH`
from the basis-invariant function and its local densities. -/
theorem fourth_moment_le_of_uniform_hybrid_energy
    (d : ℕ) (g : (E →ₗ[F2] F) → ℝ) (hg : DegreeAtMost d g)
    (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      order A B ≤ d → (𝔼 N, hybridDerivative A B T g N ^ 2) ≤ H) :
    (𝔼 X, g X ^ 4) ≤ (2 : ℝ) ^ (103 * d * d) * H * (𝔼 X, g X ^ 2) := by
  have hp : (2 : ℝ) ^ (100 * d ^ 2) * (2 : ℝ) ^ (3 * d * d) =
      (2 : ℝ) ^ (103 * d * d) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    (𝔼 X, g X ^ 4) ≤ (2 : ℝ) ^ (100 * d ^ 2) * hybridMomentSum d g :=
      A5Induction.derivative_inequality d g hg
    _ ≤ (2 : ℝ) ^ (100 * d ^ 2) * (H * hybridSelectorEnergy d g) :=
      mul_le_mul_of_nonneg_left (hybridMomentSum_le_of_uniform_energy d g H hH)
        (by positivity)
    _ ≤ (2 : ℝ) ^ (100 * d ^ 2) *
        (H * ((2 : ℝ) ^ (3 * d * d) * (𝔼 X, g X ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (selector_energy_le d g hg) hH0) (by positivity)
    _ = ((2 : ℝ) ^ (100 * d ^ 2) * (2 : ℝ) ^ (3 * d * d)) *
        H * (𝔼 X, g X ^ 2) := by ring
    _ = _ := by rw [hp]

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
The exact rank component meets the generic derivative inequality's degree
contract by its literal Fourier coefficient filter. This specializes the
checked aggregation to the same actual component used by the KMS spectral
argument; the separate basis-specific proof supplies its hybrid energy.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Actual finite Fourier support of the component, with no rank-level
inequality invoked. -/
theorem rankComponent_degree (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    DerivativeDegree.DegreeAtMost i (rankComponent i f) := by
  intro S hS
  apply rankComponent_coeff_eq_zero_of_ne i f S
  exact ne_of_gt hS

variable [Finite E] [Finite F]

/-- Generic fourth-moment closure for the literal KMS rank component. -/
theorem rankComponent_fourth_moment_le_of_hybrid (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      order A B ≤ i →
      (𝔼 N, Derivatives.hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ H) :
    (𝔼 X, rankComponent i f X ^ 4) ≤
      (2 : ℝ) ^ (103 * i * i) * H * (𝔼 X, rankComponent i f X ^ 2) :=
  fourth_moment_le_of_uniform_hybrid_energy i (rankComponent i f)
    (rankComponent_degree i f) H hH0 hH

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

end OAI
