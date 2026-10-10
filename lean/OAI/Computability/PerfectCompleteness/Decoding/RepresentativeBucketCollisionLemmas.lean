import OAI.Computability.PerfectCompleteness.Algebra.MatrixTriangularFoldingLemmas
import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.ManyGoodRowsLemmas

namespace OAI


namespace PerfectCompleteness.RepresentativeBucketCollision

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)
open TwoResponseCollision
open UniqueGamesTheorem.Foundations.Games

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)

def bucketTable (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
    (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H) (h : H) : Option (K × Z) :=
  RepresentativeMatrixTable.partialTable slots H other σ W s useful
    (MatrixRowQuotient.projectMatrix W (EvaluationMatrix.shift H X a h))

def bucketAccepted (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H) (h : H) : Bool :=
  decide (CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h))

theorem bucketTable_eq_some_iff
    (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
    (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H) (h : H) (y : K × Z) :
    bucketTable slots H other σ W s useful a X h = some y ↔
      useful (MatrixRowQuotient.projectMatrix W (EvaluationMatrix.shift H X a h)) ∧
        RepresentativeMatrixTable.response slots H other σ W s
          (EvaluationMatrix.shift H X a h) = y := by
  by_cases hu : useful (MatrixRowQuotient.projectMatrix W (EvaluationMatrix.shift H X a h)) <;>
    simp [bucketTable, RepresentativeMatrixTable.partialTable,
      RepresentativeMatrixTable.response, RepresentativeMatrixTable.representative, hu]

include hs in

theorem collision_probability_lower_bound [Finite K] [Finite Z] [Fintype H]
    (hW : RepresentativeMatrixTable.Determined slots H other W)
    (μ : FiniteDistribution H)
    (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
    (a : K) (ha : a ≠ 0) (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    μ.probability (goodDefined (bucketTable slots H other σ W s useful a X)
        (bucketAccepted slots H other σ a X)) ^ 2 / 2 ≤
      (μ.product μ).probability
        (collision (bucketTable slots H other σ W s useful a X)) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype Z := Fintype.ofFinite Z
  apply collision_probability_ge_of_response_set μ
    (bucketTable slots H other σ W s useful a X) (bucketAccepted slots H other σ a X)
    (fun y => ∃ h : H,
      CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h) ∧
        RepresentativeMatrixTable.response slots H other σ W s
          (EvaluationMatrix.shift H X a h) = y)
  · exact RepresentativeMatrixTable.card_accepted_responses_le_two
      slots H other σ W s hs hW a ha X
  · intro h y hgood hresponse
    refine ⟨h, ?_, ?_⟩
    · simpa only [bucketAccepted, decide_eq_true_eq] using hgood
    · exact ((bucketTable_eq_some_iff slots H other σ W s useful a X h y).mp hresponse).2

end
end PerfectCompleteness.RepresentativeBucketCollision



namespace PerfectCompleteness.RepresentativeDecoder

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)
open RepresentativeMatrixTable

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (W : Submodule F2 H)
  (s : (H ⧸ W) →ₗ[F2] H) (hs : W.mkQ.comp s = LinearMap.id)

theorem residualVector_subtype (b : W) :
    MatrixRowQuotient.residualVector W s hs (b : H) = b := by
  apply Subtype.ext
  rw [MatrixRowQuotient.residualVector_val]
  have hb : W.mkQ (b : H) = 0 :=
    (Submodule.Quotient.mk_eq_zero W).mpr b.property
  rw [hb, map_zero, sub_zero]

theorem residualVector_section (h : H ⧸ W) :
    MatrixRowQuotient.residualVector W s hs (s h) = 0 := by
  apply Subtype.ext
  rw [MatrixRowQuotient.residualVector_val]
  have hh := LinearMap.congr_fun hs h
  change W.mkQ (s h) = h at hh
  change s h - s (W.mkQ (s h)) = 0
  rw [hh, sub_self]

theorem correctionFunctional_comp_subtype (z : Z) :
    (correctionFunctional slots H other W s hs z).comp W.subtype =
      sideEvaluation slots H other W z := by
  apply LinearMap.ext
  intro b
  change sideEvaluation slots H other W z
    (MatrixRowQuotient.residualVector W s hs (b : H)) =
      sideEvaluation slots H other W z b
  rw [residualVector_subtype slots H W s hs]

theorem correctionFunctional_comp_section (z : Z) :
    (correctionFunctional slots H other W s hs z).comp s = 0 := by
  apply LinearMap.ext
  intro h
  change sideEvaluation slots H other W z
    (MatrixRowQuotient.residualVector W s hs (s h)) = 0
  rw [residualVector_section slots H W s hs, map_zero]

theorem correctionFunctional_decomposition (z : Z) (b : W) (h : H ⧸ W) :
    correctionFunctional slots H other W s hs z ((b : H) + s h) =
      sideEvaluation slots H other W z b := by
  rw [map_add]
  have hb := LinearMap.congr_fun
    (correctionFunctional_comp_subtype slots H other W s hs z) b
  have hh := LinearMap.congr_fun
    (correctionFunctional_comp_section slots H other W s hs z) h
  change correctionFunctional slots H other W s hs z (b : H) =
    sideEvaluation slots H other W z b at hb
  change correctionFunctional slots H other W s hs z (s h) = 0 at hh
  rw [hb, hh, add_zero]

theorem correctionFunctional_unique (z : Z) (f : Module.Dual F2 H)
    (hW : f.comp W.subtype = sideEvaluation slots H other W z)
    (hsection : f.comp s = 0) :
    f = correctionFunctional slots H other W s hs z := by
  apply LinearMap.ext
  intro h
  have hb := LinearMap.congr_fun hW (MatrixRowQuotient.residualVector W s hs h)
  have hh := LinearMap.congr_fun hsection (W.mkQ h)
  change f (s (W.mkQ h)) = 0 at hh
  change f (h - s (W.mkQ h)) =
    sideEvaluation slots H other W z (MatrixRowQuotient.residualVector W s hs h) at hb
  rw [map_sub, hh, sub_zero] at hb
  exact hb

theorem quotientFunctional_mem_annihilator (q : Module.Dual F2 (H ⧸ W)) :
    q.comp W.mkQ ∈ W.dualAnnihilator := by
  apply (Submodule.mem_dualAnnihilator (W := W) _).mpr
  intro b hb
  change q (W.mkQ b) = 0
  have hbzero : W.mkQ b = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hb
  rw [hbzero, map_zero]

theorem coset_apply (z : Z) (δ : Module.Dual F2 H)
    (hδ : δ ∈ W.dualAnnihilator) (b : W) :
    (correctionFunctional slots H other W s hs z + δ) (b : H) =
      sideEvaluation slots H other W z b := by
  have hb := LinearMap.congr_fun
    (correctionFunctional_comp_subtype slots H other W s hs z) b
  have hzero : δ (b : H) = 0 :=
    (Submodule.mem_dualAnnihilator (W := W) δ).mp hδ b b.property
  change correctionFunctional slots H other W s hs z (b : H) + δ (b : H) = _
  rw [hzero, add_zero]
  exact hb

theorem coset_comp_subtype (z : Z) (δ : Module.Dual F2 H)
    (hδ : δ ∈ W.dualAnnihilator) :
    (correctionFunctional slots H other W s hs z + δ).comp W.subtype =
      sideEvaluation slots H other W z := by
  apply LinearMap.ext
  exact coset_apply slots H other W s hs z δ hδ

theorem add_quotient_comp_subtype (z : Z) (q : Module.Dual F2 (H ⧸ W)) :
    (correctionFunctional slots H other W s hs z + q.comp W.mkQ).comp W.subtype =
      sideEvaluation slots H other W z :=
  coset_comp_subtype slots H other W s hs z _
    (quotientFunctional_mem_annihilator slots H W q)

theorem coset_apply_at_image (hW : Determined slots H other W)
    (x : Assignment slots) (δ : Module.Dual F2 H)
    (hδ : δ ∈ W.dualAnnihilator) (b : W) :
    (correctionFunctional slots H other W s hs (other x) + δ) (b : H) =
      b.val.val x := by
  rw [coset_apply slots H other W s hs (other x) δ hδ b,
    sideEvaluation_at_image slots H other W hW x]
  rfl

theorem coset_one_at_image (hW : Determined slots H other W)
    (x : Assignment slots) (δ : Module.Dual F2 H)
    (hδ : δ ∈ W.dualAnnihilator) (b : W)
    (hb : b.val.val = (1 : Assignment slots → F2)) :
    (correctionFunctional slots H other W s hs (other x) + δ) (b : H) = 1 := by
  rw [coset_apply_at_image slots H other W s hs hW x δ hδ b, hb]
  rfl

theorem coset_product_at_image (hW : Determined slots H other W)
    (x : Assignment slots) (δ : Module.Dual F2 H)
    (hδ : δ ∈ W.dualAnnihilator) (b : W)
    (f g : Assignment slots → F2) (hb : b.val.val = f * g) :
    (correctionFunctional slots H other W s hs (other x) + δ) (b : H) =
      f x * g x := by
  rw [coset_apply_at_image slots H other W s hs hW x δ hδ b, hb]
  rfl

variable (σ : KeyStrategy.Strategy n)

theorem matched_coset_realized_on_W (hW : Determined slots H other W)
    (X : CanonicalMatrixTable.Matrix (K := K) slots H) (y : K × Z)
    (hmatch : response slots H other σ W s X = y)
    (V : Submodule F2 (Module.Dual F2 H)) (hV : V ≤ W.dualAnnihilator) :
    ∃ x : Assignment slots, other x = y.2 ∧
      ∀ δ : V, ∀ b : W,
        (correctionFunctional slots H other W s hs y.2 + (δ : Module.Dual F2 H))
          (b : H) = b.val.val x := by
  obtain ⟨x, _, hx⟩ := CanonicalMatrixTable.response_realized slots H other σ
    (representative slots H W s X)
  change other x = (response slots H other σ W s X).2 at hx
  rw [hmatch] at hx
  refine ⟨x, hx, ?_⟩
  intro δ b
  rw [← hx]
  exact coset_apply_at_image slots H other W s hs hW x δ (hV δ.property) b

theorem raw_selected_output_at_match (hW : Determined slots H other W)
    (X : CanonicalMatrixTable.Matrix (K := K) slots H) (y : K × Z)
    (hmatch : response slots H other σ W s X = y) :
    (CanonicalMatrixTable.response slots H other σ X).1 =
      X (correctionFunctional slots H other W s hs y.2) + y.1 := by
  rw [raw_response slots H other σ W s hs hW X, hmatch]
  change y.1 + X (correctionFunctional slots H other W s hs y.2) = _
  exact add_comm _ _

end
end PerfectCompleteness.RepresentativeDecoder



namespace PerfectCompleteness.DenseWitnessRealization

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)
open ManyGoodRows PartialTableInverse

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

section Generic

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]
  {f : (E →ₗ[F2] F) → Option Y} {r : Nat} {ρ : ℝ}
  {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem witness_value_attained (w : Witness f r ρ A U) (hρ : 0 < ρ) :
    ∃ X : MatrixSlice.Slice w.columnSpace (LinearMap.ker A) w.base,
      f X.val = some w.value := by
  by_contra hnone
  have hzero :
      (𝔼 X : MatrixSlice.Slice w.columnSpace (LinearMap.ker A) w.base,
        indicator f w.value X.val) = 0 := by
    apply Finset.expect_eq_zero
    intro X _
    have hX : f X.val ≠ some w.value := fun h => hnone ⟨X, h⟩
    simp [indicator, hX]
  have hdensity := w.density
  rw [hzero] at hdensity
  exact (not_le_of_gt hρ) hdensity

end Generic


variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Z]
  (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
  {r : Nat} {ρ : ℝ} {A : RowMap K r}
  {U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2)}

abbrev RepresentativeWitness :=
  Witness (RepresentativeMatrixTable.partialTable slots H other σ W s useful) r ρ A U

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Z]

theorem exists_useful_match
    (w : RepresentativeWitness slots H other σ W s useful (r := r) (ρ := ρ) (A := A) (U := U))
    (hρ : 0 < ρ) :
    ∃ X : MatrixSlice.Slice w.columnSpace (LinearMap.ker A) w.base,
      useful X.val ∧
      CanonicalMatrixTable.response slots H other σ
        (MatrixRowQuotient.liftMatrix W s X.val) = w.value := by
  obtain ⟨X, hX⟩ := witness_value_attained w hρ
  have huseful : useful X.val := by
    by_contra hbad
    simp [RepresentativeMatrixTable.partialTable, hbad] at hX
  refine ⟨X, huseful, ?_⟩
  simpa [RepresentativeMatrixTable.partialTable, huseful] using hX

theorem exists_joint_realizer
    (w : RepresentativeWitness slots H other σ W s useful (r := r) (ρ := ρ) (A := A) (U := U))
    (hρ : 0 < ρ) :
    ∃ X : MatrixSlice.Slice w.columnSpace (LinearMap.ker A) w.base,
      useful X.val ∧ ∃ x : Assignment slots,
        CanonicalMatrixTable.query slots H other
          (MatrixRowQuotient.liftMatrix W s X.val) x = w.value := by
  obtain ⟨X, huseful, hmatch⟩ :=
    exists_useful_match slots H other σ W s useful w hρ
  obtain ⟨x, hfirst, hsecond⟩ := CanonicalMatrixTable.response_realized slots H other σ
    (MatrixRowQuotient.liftMatrix W s X.val)
  rw [hmatch] at hfirst hsecond
  refine ⟨X, huseful, x, ?_⟩
  exact Prod.ext hfirst hsecond

theorem selected_side_mem_range
    (w : RepresentativeWitness slots H other σ W s useful (r := r) (ρ := ρ) (A := A) (U := U))
    (hρ : 0 < ρ) : w.value.2 ∈ Set.range other := by
  obtain ⟨X, _, x, hx⟩ := exists_joint_realizer slots H other σ W s useful w hρ
  exact ⟨x, congrArg Prod.snd hx⟩

theorem exists_coset_realizer
    (hs : W.mkQ.comp s = LinearMap.id)
    (hW : RepresentativeMatrixTable.Determined slots H other W)
    (w : RepresentativeWitness slots H other σ W s useful (r := r) (ρ := ρ) (A := A) (U := U))
    (hρ : 0 < ρ) (V : Submodule F2 (Module.Dual F2 H))
    (hV : V ≤ W.dualAnnihilator) :
    ∃ X : MatrixSlice.Slice w.columnSpace (LinearMap.ker A) w.base,
      useful X.val ∧ ∃ x : Assignment slots,
        CanonicalMatrixTable.query slots H other
          (MatrixRowQuotient.liftMatrix W s X.val) x = w.value ∧
        ∀ δ : V, ∀ b : W,
          (RepresentativeMatrixTable.correctionFunctional slots H other W s hs w.value.2 +
            (δ : Module.Dual F2 H)) (b : H) = b.val.val x := by
  obtain ⟨X, huseful, x, hx⟩ := exists_joint_realizer slots H other σ W s useful w hρ
  refine ⟨X, huseful, x, hx, ?_⟩
  intro δ b
  have hxside : other x = w.value.2 := congrArg Prod.snd hx
  rw [← hxside]
  exact RepresentativeDecoder.coset_apply_at_image slots H other W s hs hW x δ
    (hV δ.property) b

theorem selected_columns_le_annihilator
    (w : RepresentativeWitness slots H other σ W s useful (r := r) (ρ := ρ) (A := A) (U := U)) :
    w.columnSpace.map W.mkQ.dualMap ≤ W.dualAnnihilator := by
  intro δ hδ
  obtain ⟨q, _, rfl⟩ := Submodule.mem_map.mp hδ
  exact RepresentativeDecoder.quotientFunctional_mem_annihilator slots H W q

end
end PerfectCompleteness.DenseWitnessRealization

end OAI
