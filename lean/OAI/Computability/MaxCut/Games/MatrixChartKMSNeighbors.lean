import Mathlib
import OAI.Computability.MaxCut.Games.RowErasure
import OAI.Computability.MaxCut.Games.KMSBasisComparisonNeighborsFiberFunctional

namespace OAI

/-! Exact full-neighbor count in the KMS vertex representation. -/

namespace MaxCutGames.Inverse.MatrixChart

open Module

/-- Ambient linear equivalence transports the actual neighbor subspaces. -/
noncomputable def grassmannNeighborsMapEquiv
    {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    (e : E ≃ₗ[ZMod 2] F) (L : Submodule (ZMod 2) E) :
    GrassmannNeighbors L ≃ GrassmannNeighbors (L.map e.toLinearMap) := by
  refine Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_
  intro W
  change (_ ∧ _) ↔
    (finrank (ZMod 2) (W.map e.toLinearMap) =
        finrank (ZMod 2) (L.map e.toLinearMap) ∧
      finrank (ZMod 2) (L.map e.toLinearMap ⊓ W.map e.toLinearMap :
        Submodule (ZMod 2) F) + 1 =
        finrank (ZMod 2) (L.map e.toLinearMap))
  rw [← Submodule.map_inf e.toLinearMap e.injective]
  simp only [LinearEquiv.finrank_map_eq]

/-- Extrinsic submodule neighbors and the finite KMS neighbor predicate agree. -/
def kmsNeighborsEquiv {n ell : Nat} (L : KMS.Vertex n ell) :
    GrassmannNeighbors L.val ≃ {W : KMS.Vertex n ell // KMS.Adjacent L W} where
  toFun W := ⟨⟨W.val, W.property.1.trans L.property⟩, by
    refine ⟨?_, ?_⟩
    · intro h
      have hv := congrArg Subtype.val h
      have hd := W.property.2
      rw [← hv, inf_idem] at hd
      omega
    · exact W.property.2.trans L.property⟩
  invFun W := ⟨W.val.val, W.val.property.trans L.property.symm,
    W.property.2.trans L.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_full_neighbors {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
  classical
  have h : Nat.card {W : KMS.Vertex (ell + m) ell //
      KMS.Adjacent (matrixVertex M) W} =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
    rw [← Nat.card_congr (kmsNeighborsEquiv (matrixVertex M))]
    change Nat.card (GrassmannNeighbors
      ((matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap)) = _
    rw [← Nat.card_congr (grassmannNeighborsMapEquiv
      (coordinateJoin (ZMod 2) ell m) (matrixGraph M))]
    exact card_grassmann_neighbors_graph M.vecMulLinear
  simpa only [Nat.card_eq_fintype_card, KMS.neighbors, Fintype.card_subtype] using h

/-- Exactly two full Grassmann neighbors for every nonzero factor pair. -/
theorem card_full_neighbors_twice {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      2 * ((2 ^ ell - 1) * (2 ^ m - 1)) := by
  rw [card_full_neighbors]
  have hpow : 2 ^ (m + 1) - 2 = 2 * (2 ^ m - 1) := by
    rw [pow_succ, Nat.mul_sub_left_distrib]
    simp [Nat.mul_comm]
  rw [hpow]
  ac_rfl

end MaxCutGames.Inverse.MatrixChart

/-! Local ordered-basis retention in the precise KMS vertex representation. -/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

private theorem relativeDensity_eq_expect_subtype_inline_KMSBasisComparisonNeighborsRetention {Ω : Type*} [Fintype Ω]
    (S : Finset Ω) (P : Ω → Prop) :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

/-- The ordered-basis test conditioned on its good event samples every full
Grassmann neighbor uniformly. The target observable is the original lifted
indicator, so this identity directly feeds the matrix-test retention bound. -/
theorem outsideNeighbor_retention {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    (𝔼 p : OutsideNeighborFactors X,
      liftedIndicator S (rankOneUpdate X p.1.val p.2.val)) =
        KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX)) := by
  let e : MatrixChart.GrassmannNeighbors X.range ≃
      {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} :=
    MatrixChart.kmsNeighborsEquiv (rangeVertex X hX)
  let : Fintype (MatrixChart.GrassmannNeighbors X.range) :=
    Fintype.ofEquiv {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} e.symm
  let g : MatrixChart.GrassmannNeighbors X.range → ℝ :=
    fun W => if (e W).val ∈ S then 1 else 0
  calc
    _ = 𝔼 p : OutsideNeighborFactors X, g (outsideNeighborSample X hX p) := by
      apply Finset.expect_congr rfl
      intro p _
      unfold liftedIndicator
      rw [inLift_iff_rangeVertex_mem S _
        (injective_rankOneUpdate X hX p.1.val p.2.property)]
      have hv : rangeVertex (rankOneUpdate X p.1.val p.2.val)
          (injective_rankOneUpdate X hX p.1.val p.2.property) =
            (e (outsideNeighborSample X hX p)).val := by
        apply Subtype.ext
        rfl
      rw [hv]
      by_cases hp : (e (outsideNeighborSample X hX p)).val ∈ S <;> simp [g, hp]
    _ = 𝔼 W : MatrixChart.GrassmannNeighbors X.range, g W :=
      expect_outsideNeighborSample X hX g
    _ = 𝔼 W : {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W},
        if W.val ∈ S then (1 : ℝ) else 0 :=
      Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := (relativeDensity_eq_expect_subtype_inline_KMSBasisComparisonNeighborsRetention S
      (KMS.Adjacent (rangeVertex X hX))).symm

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
# Ordered-basis retention versus Grassmann retention

This is the sampling comparison in KMS Lemma 2.7. The original experiment
uses all functionals and all directions, including zero. Its good event
induces exactly the full Grassmann-neighbor law; all other outcomes contribute
at most their explicit probability mass. Initial bases push forward uniformly
to the original Grassmann set.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

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
end MaxCutGames.Inverse.KMSBasisComparison

namespace MaxCutGames.Inverse.KMSBasisComparison

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
to the dimension-uniform Grassmann theorem required by the v2 inverse. -/
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
end MaxCutGames.Inverse.KMSBasisComparison

namespace MaxCutGames.Inverse.KMSMomentToExpansion
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSMomentScalar KMSAnalytic KMSLowLevel

/-- Any proved dimension-independent upper moment with a finite local budget
supplies the exact ordered-basis expansion interface. -/
theorem liftExpansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    LiftExpansionPrinciple := by
  intro ζ hζ _hζ1
  obtain ⟨r, _hr, ε, hε, hε1, hcut⟩ := exists_general_cutoff_parameters C hC hζ
  refine ⟨ε, hε, hε1, R r, ellMin r, ?_⟩
  intro ell hell
  refine ⟨0, ?_⟩
  intro n _hn S hS hPseudo
  have hf : IsBoolean (liftedIndicator S) := by
    intro X
    unfold liftedIndicator
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hδ : 0 ≤ liftDensity S := boolean_average_nonneg hf
  have hc := uniformNoise_bound_of_general_fourthMoments (liftedIndicator S) hf
    r (C r) ε (hC r) hε.le (hupper r ε hε.le hε1 ell hell n S hPseudo)
  have heq : (𝔼 X : BasisMap n ell,
      liftedIndicator S X * fullStepRetention S X) =
      𝔼 X : BasisMap n ell, liftedIndicator S X * uniformNoise (liftedIndicator S) X := by
    apply Finset.expect_congr rfl
    intro X _
    congr 1
    rw [fullStepRetention_eq_noise, uniformNoise_apply]
  apply liftRetention_le_of_correlation_le S hS ζ
  rw [heq]
  apply hc.trans
  change ((r + 1 : ℕ) * ((C r + 1) * ε ^ ((1 : ℝ) / 4)) +
    ((2 : ℝ) ^ (r + 1))⁻¹) * liftDensity S ≤ ζ * liftDensity S
  apply mul_le_mul_of_nonneg_right _ hδ
  exact hcut.trans (by linarith)

/-- Checked finite bridges and parameter choices reduce the full KMS expansion
principle to the displayed actual upper-moment estimate, and nothing weaker. -/
theorem expansion_of_upperMoments
    (C : ℕ → ℝ) (hC : ∀ r, 0 ≤ C r) (R ellMin : ℕ → ℕ)
    (hupper : ∀ r : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ ell : ℕ, ellMin r ≤ ell → ∀ n : ℕ,
      ∀ S : Finset (Vertex n ell), TuplePseudorandom S (R r) ε →
      ∀ i : ℕ, i ≤ r →
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
          C r * (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε) :
    KMS.ExpansionPrinciple :=
  expansion_of_liftExpansion (liftExpansion_of_upperMoments C hC R ellMin hupper)

end
end MaxCutGames.Inverse.KMSMomentToExpansion

/-! The proved KMS Grassmann expansion principle. Its quantitative analytic
input is the actual basis-invariant fourth-moment theorem, whose proof uses
fixed-character and fixed-point inductions. No expansion, inverse,
rank-level, or missing-moment premise occurs in this theorem. -/

namespace MaxCutGames.Inverse.KMSExpansion
noncomputable section

/-- The KMS expansion theorem with constants independent of both dimensions
and with the ambient threshold chosen after the plane dimension. -/
theorem kms_expansion : KMS.ExpansionPrinciple := by
  apply KMSMomentToExpansion.expansion_of_upperMoments
    KMSMomentConstants.fourthMomentConstant
    KMSMomentConstants.fourthMomentConstant_nonneg
    (fun r => 2 * r) (fun r => r)
  intro r ε hε _hε1 ell hell n S hS i hi
  exact KMSMomentTheorem.lifted_fourth_moment_bound r ε hε ell hell n S hS i hi

end
end MaxCutGames.Inverse.KMSExpansion

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

def matrixFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (Mat ell m) := Finset.univ.filter fun M => f M = y

def liftedFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (KMS.Vertex (ell + m) ell) := (matrixFiber f y).image matrixVertex

theorem liftedFiber_subset_chart {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    liftedFiber f y ⊆ matrixChart ell m := by
  intro L hL
  obtain ⟨M, _, rfl⟩ := Finset.mem_image.mp hL
  exact (mem_matrixChart _).mpr ⟨M, rfl⟩

@[simp] theorem matrixVertex_mem_liftedFiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    matrixVertex M ∈ liftedFiber f y ↔ f M = y := by
  constructor
  · intro h
    obtain ⟨N, hN, hNM⟩ := Finset.mem_image.mp h
    have : N = M := matrixVertex_injective hNM
    subst N
    exact (Finset.mem_filter.mp hN).2
  · intro h
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- The slice and the interval intersected with the chart correspond exactly.
The hypothesis states equality of the actual membership predicates. -/
theorem image_slice_points {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I) :
    S.points.image matrixVertex = I ∩ matrixChart ell m := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_inter.mpr ⟨(hS M).mp (Finset.mem_filter.mp hM).2,
      (mem_matrixChart _).mpr ⟨M, rfl⟩⟩
  · intro h
    obtain ⟨hI, hC⟩ := Finset.mem_inter.mp h
    obtain ⟨M, rfl⟩ := (mem_matrixChart _).mp hC
    exact Finset.mem_image.mpr ⟨M,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hS M).mpr hI⟩, rfl⟩

theorem image_slice_fiber {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    (S.points.filter fun M => f M = y).image matrixVertex =
      liftedFiber f y ∩ (I ∩ matrixChart ell m) := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hpoints, hfy⟩ := Finset.mem_filter.mp hM
    refine Finset.mem_inter.mpr ⟨(matrixVertex_mem_liftedFiber f y M).mpr hfy, ?_⟩
    rw [← image_slice_points S I hS]
    exact Finset.mem_image.mpr ⟨M, hpoints, rfl⟩
  · intro h
    obtain ⟨hf, hIC⟩ := Finset.mem_inter.mp h
    rw [← image_slice_points S I hS] at hIC
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hIC
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr
      ⟨hM, (matrixVertex_mem_liftedFiber f y M).mp hf⟩, rfl⟩

/-- Uniform agreement on a slice is the actual Grassmann fiber density in the
chart-intersected interval.  Empty sets are allowed on both sides of this
identity, with the standard zero-denominator convention. -/
theorem constantAgreement_eq_chart_density {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    S.constantAgreement f y =
      KMS.relativeDensity (liftedFiber f y) (I ∩ matrixChart ell m) := by
  unfold Slice.constantAgreement KMS.relativeDensity
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole]
  rw [← image_slice_fiber S I hS f y, ← image_slice_points S I hS]
  simp only [Finset.card_image_of_injective _ matrixVertex_injective]

theorem hasAffineSlice_of_dense_interval {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (S : Slice ell m) (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    {α : ℝ} {r : ℕ} (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : (liftedFiber f y ∩ I).Nonempty)
    (hdense : α ≤ KMS.relativeDensity (liftedFiber f y) I) :
    HasAffineSlice f α r := by
  obtain ⟨hIC, hα⟩ := KMS.density_bound_passes_to_chart
    (liftedFiber f y) I (matrixChart ell m)
    (liftedFiber_subset_chart f y) hne hdense
  have hpoints : S.points.Nonempty := by
    rw [← image_slice_points S I hS] at hIC
    exact Finset.image_nonempty.mp hIC
  apply hasAffineSlice_of_constant f α r S hrows hcolumns hpoints y
  rw [constantAgreement_eq_chart_density S I hS f y]
  exact hα

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-! Every Grassmann interval has a chart description with exactly `dim A`
lower equations and `codim B` upper equations. This supplies the quantitative
row/column budget used when the expansion theorem selects an interval.
-/

namespace MaxCutGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem span_basis_values {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    Submodule.span K (Set.range fun i => (b i).val) = A := by
  have h := congrArg (Submodule.map A.subtype) b.span_eq
  simpa only [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    ← Set.range_comp', Submodule.coe_subtype] using h

theorem lowerRows_basis {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    lowerRows (fun i => (b i).val.1) (fun i => (b i).val.2) = A := by
  exact span_basis_values A b

/-- Checking an annihilator basis suffices to test membership in a subspace. -/
theorem mem_iff_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) (x : X × Y) :
    x ∈ B ↔ ∀ i, (b i).val x = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_dualAnnihilator (b i).val).mp (b i).property x hx
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff B x).mp
    intro φ hφ
    let ev : B.dualAnnihilator →ₗ[K] K :=
      (Module.Dual.eval K (X × Y) x).comp B.dualAnnihilator.subtype
    have hev : ev = 0 := b.ext (fun i => h i)
    exact congrArg (fun f : B.dualAnnihilator →ₗ[K] K => f ⟨φ, hφ⟩) hev

/-- Split a product functional into its two coordinate functionals. -/
theorem functional_coordinate_decomposition (φ : (X × Y) →ₗ[K] K) (x : X) (y : Y) :
    φ (x, y) = φ (x, 0) + φ (0, y) := by
  have h : (x, y) = (x, 0) + (0, y) := by simp
  rw [h, map_add]

theorem upperColumns_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) :
    upperColumns
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) = B := by
  ext x
  rw [mem_iff_annihilator_basis B b]
  simp only [upperColumns, Submodule.mem_iInf]
  change (∀ i, x ∈ LinearMap.ker
    (((b i).val.comp (LinearMap.inr K X Y)).comp (LinearMap.snd K X Y) -
      (-((b i).val.comp (LinearMap.inl K X Y))).comp (LinearMap.fst K X Y))) ↔ _
  constructor <;> intro h i
  · have hi := h i
    change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0 at hi
    rw [functional_coordinate_decomposition]
    simpa only [sub_neg_eq_add, add_comm] using hi
  · change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0
    have hi := h i
    rw [functional_coordinate_decomposition] at hi
    simpa only [sub_neg_eq_add, add_comm] using hi

/-- Coordinates for an arbitrary interval. There are exactly `dim A` rows and
`codim B` columns, so an interval order bound gives the required slice bound. -/
theorem exists_interval_coordinates [FiniteDimensional K X] [FiniteDimensional K Y]
    (A B : Submodule K (X × Y)) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → X) (s : Fin n_r → Y)
      (t : Fin n_c → X →ₗ[K] K) (q : Fin n_c → Y →ₗ[K] K),
      n_r = Module.finrank K A ∧ n_c = Module.finrank K ((X × Y) ⧸ B) ∧
      ∀ T : X →ₗ[K] Y,
        (A ≤ T.graph ∧ T.graph ≤ B) ↔
          ((∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j)) := by
  let a := Module.finBasis K A
  let : Module.Free K B.dualAnnihilator := Module.Free.of_divisionRing K B.dualAnnihilator
  let b := Module.finBasis K B.dualAnnihilator
  refine ⟨Module.finrank K A, Module.finrank K B.dualAnnihilator,
    (fun i => (a i).val.1), (fun i => (a i).val.2),
    (fun i => -((b i).val.comp (LinearMap.inl K X Y))),
    (fun i => (b i).val.comp (LinearMap.inr K X Y)), rfl, ?_, ?_⟩
  · exact (Subspace.quotEquivAnnihilator B).finrank_eq.symm
  · intro T
    have h := interval_iff_slice (fun i => (a i).val.1) (fun i => (a i).val.2)
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) T
    simpa only [lowerRows_basis A a, upperColumns_annihilator_basis B b] using h

end MaxCutGames.Inverse.MatrixChart

/-! Extract actual vector-valued row/column data from an arbitrary interval.
The equation counts are the dimension/codimension of that interval, and no
homogeneity is imposed on the equation right-hand sides.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem dotFunctional_surjective :
    Function.Surjective (dotFunctional (K := K) (ι := ι)) := by
  classical
  intro f
  refine ⟨fun i => f (Pi.single i 1), ?_⟩
  apply (Pi.basisFun K ι).ext
  intro i
  change (fun j => f (Pi.single j 1)) ⬝ᵥ (Pi.basisFun K ι i) =
    f (Pi.basisFun K ι i)
  simp

theorem exists_matrix_interval_slice (A B : Submodule K ((ι → K) × (κ → K))) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → ι → K) (s : Fin n_r → κ → K)
      (t : Fin n_c → ι → K) (q : Fin n_c → κ → K),
      n_r = Module.finrank K A ∧
      n_c = Module.finrank K (((ι → K) × (κ → K)) ⧸ B) ∧
      ∀ M : Matrix ι κ K,
        (A ≤ matrixGraph M ∧ matrixGraph M ≤ B) ↔
          ((∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j)) := by
  classical
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_interval_coordinates A B
  choose tv htv using (fun j => dotFunctional_surjective (t j))
  choose qv hqv using (fun j => dotFunctional_surjective (q j))
  refine ⟨nr, nc, d, s, tv, qv, hnr, hnc, ?_⟩
  intro M
  rw [h M.vecMulLinear]
  have hj (j : Fin nc) : (q j).comp M.vecMulLinear = t j ↔ M *ᵥ qv j = tv j := by
    rw [← hqv j, ← htv j]
    exact column_equation_iff M (qv j) (tv j)
  simp only [Matrix.vecMulLinear_apply, hj]

/-- An interval order bound yields separate row and column budgets. -/
theorem exists_bounded_matrix_interval_slice
    (A B : Submodule K ((ι → K) × (κ → K))) (r : Nat)
    (horder : Module.finrank K A +
      Module.finrank K (((ι → K) × (κ → K)) ⧸ B) ≤ r) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → ι → K) (s : Fin n_r → κ → K)
      (t : Fin n_c → ι → K) (q : Fin n_c → κ → K),
      n_r ≤ r ∧ n_c ≤ r ∧
      ∀ M : Matrix ι κ K,
        (A ≤ matrixGraph M ∧ matrixGraph M ≤ B) ↔
          ((∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j)) := by
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_matrix_interval_slice A B
  refine ⟨nr, nc, d, s, t, q, ?_, ?_, h⟩ <;> omega

end MaxCutGames.Inverse.MatrixChart

end OAI
