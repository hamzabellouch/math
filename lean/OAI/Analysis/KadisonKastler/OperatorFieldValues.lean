import OAI.Analysis.KadisonKastler.PublishedFieldTomiyama
import OAI.Analysis.KadisonKastler.StrongCommutantTests

namespace OAI

/-! # Von Neumann algebra values of measurable operator fields

Commuting with constant operators in the commutant is a norm-closed
condition. Countably many strong-operator tests identify this condition
with pointwise membership outside one null set.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Pointwise BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closed field algebra commuting with the constant commutant. -/
def operatorFieldAlgebra (M : VonNeumannAlgebra H) :
    StarSubalgebra ℂ (WeakOperatorField (H := H) μ) :=
  StarSubalgebra.centralizer ℂ (operatorFieldConst μ '' (M.commutant : Set (H →L[ℂ] H)))

theorem isClosed_operatorFieldAlgebra (M : VonNeumannAlgebra H) :
    IsClosed (operatorFieldAlgebra (μ := μ) M : Set (WeakOperatorField (H := H) μ)) :=
  Set.isClosed_centralizer _

instance operatorFieldAlgebraCStar (M : VonNeumannAlgebra H) :
    CStarAlgebra (operatorFieldAlgebra (μ := μ) M) :=
  StarSubalgebra.cstarAlgebra _ (h_closed := isClosed_operatorFieldAlgebra M)

theorem mem_operatorFieldAlgebra_iff (M : VonNeumannAlgebra H)
    (q : WeakOperatorField (H := H) μ) :
    q ∈ operatorFieldAlgebra (μ := μ) M ↔
      ∀ T ∈ M.commutant, operatorFieldConst μ T * q = q * operatorFieldConst μ T := by
  rw [operatorFieldAlgebra, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h T hT
    exact (h _ ⟨T, hT, rfl⟩).1
  · intro h b hb
    obtain ⟨T, hT, rfl⟩ := hb
    exact ⟨h T hT, by simpa only [map_star] using h (star T) (star_mem hT)⟩

/-- Pointwise algebra membership of the canonical representative. -/
def HasOperatorValues (M : VonNeumannAlgebra H) (q : WeakOperatorField (H := H) μ) : Prop :=
  ∀ᵐ x ∂μ, WeakOperatorRepresentative.eval (WeakOperatorField.representative q) x ∈ M

theorem hasOperatorValues_quotient_iff (M : VonNeumannAlgebra H)
    (F : WeakOperatorRepresentative (H := H) μ) :
    HasOperatorValues M (operatorFieldQuotient μ F) ↔
      ∀ᵐ x ∂μ, WeakOperatorRepresentative.eval F x ∈ M := by
  have he := (operatorFieldQuotient_eq_iff μ _ _).mp
    (WeakOperatorField.quotient_representative (operatorFieldQuotient μ F))
  constructor
  · intro h
    filter_upwards [h, he] with x hx heq
    rwa [heq] at hx
  · intro h
    filter_upwards [h, he] with x hx heq
    rwa [heq]

theorem mem_operatorFieldAlgebra_of_values (M : VonNeumannAlgebra H)
    (q : WeakOperatorField (H := H) μ) (hq : HasOperatorValues M q) :
    q ∈ operatorFieldAlgebra (μ := μ) M := by
  apply (mem_operatorFieldAlgebra_iff M q).mpr
  intro T hT
  let R := WeakOperatorField.representative q
  have he : operatorFieldQuotient (H := H) μ
      (operatorRepresentativeConst μ T * R) =
      operatorFieldQuotient (H := H) μ (R * operatorRepresentativeConst μ T) := by
    apply (operatorFieldQuotient_eq_iff μ _ _).mpr
    filter_upwards [hq] with x hx
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hT) _ hx).symm
  simpa only [map_mul, R, WeakOperatorField.quotient_representative, operatorFieldConst,
    StarAlgHom.comp_apply] using he

variable [TopologicalSpace.SeparableSpace H]

/-- Countably many constant commutant tests suffice to recover actual
von Neumann algebra membership almost everywhere. -/
theorem hasOperatorValues_of_mem (M : VonNeumannAlgebra H)
    (q : WeakOperatorField (H := H) μ) (hq : q ∈ operatorFieldAlgebra (μ := μ) M) :
    HasOperatorValues M q := by
  obtain ⟨E, hEc, hES, hE⟩ := exists_countable_commutant_tests (unitBall M.commutant)
    (fun _ h => h.2)
  let R := WeakOperatorField.representative q
  have hc (T : E) : ∀ᵐ x ∂μ, Commute (WeakOperatorRepresentative.eval R x) (T : H →L[ℂ] H) := by
    have hT := (mem_operatorFieldAlgebra_iff M q).mp hq T (hES T.property).1
    have he : operatorFieldQuotient (H := H) μ (operatorRepresentativeConst μ T * R) =
        operatorFieldQuotient (H := H) μ (R * operatorRepresentativeConst μ T) := by
      simpa only [map_mul, R, WeakOperatorField.quotient_representative, operatorFieldConst,
        StarAlgHom.comp_apply] using hT
    filter_upwards [(operatorFieldQuotient_eq_iff μ _ _).mp he] with x hx
    exact hx.symm
  let : Countable E := hEc.to_subtype
  filter_upwards [ae_all_iff.mpr hc] with x hx
  change WeakOperatorRepresentative.eval R x ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro T hT
  by_cases hz : T = 0
  · simp [hz]
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hz
  have hTm : T ∈ M.commutant := by
    simpa only [← SetLike.mem_coe, VonNeumannAlgebra.coe_commutant] using hT
  let c : ℂ := (‖T‖⁻¹ : ℝ)
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast inv_ne_zero hn.ne'
  have ht : c • T ∈ unitBall M.commutant := by
    refine ⟨M.commutant.toStarSubalgebra.smul_mem hTm c, ?_⟩
    simp [c, norm_smul, Complex.norm_real, inv_mul_cancel₀ hn.ne']
  have hs := (hE (WeakOperatorRepresentative.eval R x)).mp
    (fun a ha => hx ⟨a, ha⟩) (c • T) ht
  have he : c • (WeakOperatorRepresentative.eval R x * T) =
      c • (T * WeakOperatorRepresentative.eval R x) := by
    simpa only [mul_smul_comm, smul_mul_assoc] using hs.eq
  exact (smul_right_inj hc0).mp he |>.symm

theorem mem_operatorFieldAlgebra_iff_values (M : VonNeumannAlgebra H)
    (q : WeakOperatorField (H := H) μ) :
    q ∈ operatorFieldAlgebra (μ := μ) M ↔ HasOperatorValues M q :=
  ⟨hasOperatorValues_of_mem M q, mem_operatorFieldAlgebra_of_values M q⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [IsFiniteMeasure μ] {α : NonsingularAction G D μ}

/-- The operator mean retains values in any specified von Neumann algebra. -/
theorem ScalarBoundaryMean.operatorMean_mem (m : ScalarBoundaryMean α)
    (hTom : PublishedFieldTomiyama (G := G) (H := H) (μ := μ))
    (M : VonNeumannAlgebra H) (F : G →ᵇ WeakOperatorField (H := H) μ)
    (hF : ∀ g, F g ∈ operatorFieldAlgebra (μ := μ) M) :
    m.operatorMean F ∈ operatorFieldAlgebra (μ := μ) M := by
  apply (mem_operatorFieldAlgebra_iff M _).mpr
  intro T hT
  have he : boundaryConstant (G := G) (operatorFieldConst μ T) * F =
      F * boundaryConstant (G := G) (operatorFieldConst μ T) := by
    apply BoundedContinuousFunction.ext
    intro g
    exact (mem_operatorFieldAlgebra_iff M (F g)).mp (hF g) T hT
  have hm := congrArg m.operatorMean he
  have hl := (hTom m.operatorMean m.norm_operatorMeanValue_le m.operatorMean_fixed).1
    (operatorFieldConst μ T) F
  have hr := (hTom m.operatorMean m.norm_operatorMeanValue_le m.operatorMean_fixed).2
    F (operatorFieldConst μ T)
  exact hl.symm.trans (hm.trans hr)

end

end KadisonKastler

end OAI
