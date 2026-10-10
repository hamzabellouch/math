import OAI.Probability.DilutedSpin.ConcentrationRate
import OAI.Probability.DilutedSpin.RegularNodeAverage

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance regularCovarianceLimitDecidableEq (valueType : Type) :
    DecidableEq valueType := Classical.decEq valueType
variable {p L : ℕ}

/-- The two precise outputs of the shared physical reservoir selection used by
the covariance induction. A witness is produced below from the model, with its
low-increment and parameter bounds retained alongside it. -/
structure ScheduledControl (M : Model p) (θB hB : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) : Prop where
  singleton : ∀ η : ℝ, 0<η → ∀ t : ℝ, 0<t → ∀ᶠ n in atTop,
    physicalShapeAverage M θB hB (Ns n+1) L (us n) .leaf η≤((L+1:ℕ):ℝ)⁻¹/η+t
  matrix : ∀ (α : Type) [Fintype α] [DecidableEq α]
    (D : (α → Fin (L+1)) → Prop)
    (S T : (α → Fin (L+1)) → PrescribedTree (L+1))
    (a : (Q : α → Fin (L+1)) → (S Q).Leaf)
    (k : (α → Fin (L+1)) → ℕ), (∀ Q, 0<k Q) →
    ∀ (q : (Q : α → Fin (L+1)) → Option (Fin (k Q)) → (T Q).Leaf)
      (denom : (α → Fin (L+1)) → ℝ),
    Tendsto (fun n => DepthAverage.average D (fun Q =>
      |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB
        (Ns n+1) (us n) (T Q) (q Q)|/|denom Q|)) atTop (𝓝 0)

noncomputable def physicalShapeLimsup (M : Model p) (θB hB : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) : ℝ :=
  limsup (fun n => physicalShapeAverage M θB hB (Ns n+1) L (us n) S η) atTop

lemma physicalShapeLimsup_nonneg (M : Model p) (θB hB : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    0≤physicalShapeLimsup M θB hB L Ns us S η :=
  unit_limsup_nonneg (fun n => physicalShapeAverage_nonneg M θB hB (Ns n+1) L (us n) S η)
    (fun n => physicalShapeAverage_le_one M θB hB (Ns n+1) L (us n) S η)

lemma physicalShapeLimsup_le_one (M : Model p) (θB hB : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    physicalShapeLimsup M θB hB L Ns us S η≤1 :=
  unit_limsup_le_one (fun n => physicalShapeAverage_nonneg M θB hB (Ns n+1) L (us n) S η)
    (fun n => physicalShapeAverage_le_one M θB hB (Ns n+1) L (us n) S η)

lemma physicalShapeLimsup_leaf {M : Model p} {θB hB : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : ScheduledControl M θB hB L Ns us)
    {η : ℝ} (hη : 0<η) :
    physicalShapeLimsup M θB hB L Ns us .leaf η≤((L+1:ℕ):ℝ)⁻¹/η := by
  apply le_of_forall_pos_le_add
  intro t ht
  exact limsup_le_of_le (IsCoboundedUnder.of_frequently_ge
    ((Eventually.of_forall (fun n => physicalShapeAverage_nonneg M θB hB (Ns n+1) L (us n) .leaf η)).frequently))
    (h.singleton η hη t ht)

/-- The full node recursion after the N-limit; the charge is uniform in L,
and the only signed-covariance errors have disappeared at fixed grid. -/
theorem physicalShapeLimsup_node {M : Model p} {θB hB : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : ScheduledControl M θB hB L Ns us)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ)) :
    η*physicalShapeLimsup M θB hB L Ns us (.node k hk C) η ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*nodeChargeConstant k hk C η*Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)) +
      (4*nodeChargeConstant k hk C η+4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (physicalShapeLimsup M θB hB L Ns us (C j) (η/2))) := by
  obtain ⟨S,T,a,q,J,hav⟩ := regular_node_average M θB hB L k hk C hη hlarge
  have he := h.matrix (Option (ReducedTopology.node k hk C).Vertex)
    (regularShapeDomain (.node k hk C) (L+1) η) S T a
    (fun _ => 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1) (fun _ => by omega) q J
  have hK := nodeChargeConstant_nonneg k hk C hη
  apply limsup_finite_sqrt_bound
    (fun n => physicalShapeAverage M θB hB (Ns n+1) L (us n) (.node k hk C) η)
    _ (fun j n => physicalShapeAverage M θB hB (Ns n+1) L (us n) (C j) (η/2))
    hη (by positivity) (by positivity)
    (fun n => physicalShapeAverage_nonneg M θB hB (Ns n+1) L (us n) _ η)
    (fun n => physicalShapeAverage_le_one M θB hB (Ns n+1) L (us n) _ η)
    (fun j n => physicalShapeAverage_le_one M θB hB (Ns n+1) L (us n) (C j) (η/2)) he
  intro n
  have hh := hav (Ns n+1) (us n)
  dsimp only [physicalChildrenAverage] at hh
  linarith only [hh]

end DilutedSpinGlass.UniversalDictionary

end

end OAI
