import OAI.Analysis.KadisonKastler.WeakFieldSpectralSupport

namespace OAI

/-! # Spectral step approximation of measurable fields

A common dyadic mesh is used for every point of the measure space.
Measurability of its finitely many projection fields follows inductively
from the constructed spectral support. The existing concrete spectral
interval estimate gives a uniform operator-norm error.
-/

namespace KadisonKastler

open MeasureTheory Generator.Tracial
open scoped Topology CStarAlgebra BigOperators

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

local instance densityFieldOrder : PartialOrder (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrder _
local instance densityFieldPreorder : Preorder (WeakOperatorRepresentative (H := H) μ) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance densityFieldLE : LE (WeakOperatorRepresentative (H := H) μ) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance densityFieldStarOrder : StarOrderedRing (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrderedRing _
local instance densityTopOrder : PartialOrder ((fullOperatorAlgebra (H := H)).toStarSubalgebra) :=
  CStarAlgebra.spectralOrder _
local instance densityTopPreorder : Preorder ((fullOperatorAlgebra (H := H)).toStarSubalgebra) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance densityTopLE : LE ((fullOperatorAlgebra (H := H)).toStarSubalgebra) :=
  (CStarAlgebra.spectralOrder _).toLE
local instance densityTopStarOrder : StarOrderedRing ((fullOperatorAlgebra (H := H)).toStarSubalgebra) :=
  CStarAlgebra.spectralOrderedRing _

private def projectionField (p : D → H →L[ℂ] H) (hp : ∀ x, IsStarProjection (p x))
    (hm : ∀ ξ, AEStronglyMeasurable (fun x => p x ξ) μ) :
    WeakOperatorRepresentative (H := H) μ :=
  mk p 1 (fun x => IsStarProjection.norm_le _ (hp x)) hm
    (fun ξ => by simpa only [(hp _).isSelfAdjoint.star_eq] using hm ξ)

private theorem projectionField_isStarProjection
    (p : D → H →L[ℂ] H) (hp : ∀ x, IsStarProjection (p x))
    (hm : ∀ ξ, AEStronglyMeasurable (fun x => p x ξ) μ) :
    IsStarProjection (projectionField p hp hm) := by
  constructor
  · apply ext_eval
    intro x
    exact (hp x).isIdempotentElem.eq
  · apply ext_eval
    intro x
    exact (hp x).isSelfAdjoint.star_eq

private theorem topElement_isSelfAdjoint (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F) (x : D) : IsSelfAdjoint (topElement F x) := by
  apply IsSelfAdjoint.of_map (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype
    Subtype.val_injective
  exact hF.map (evalHom x)

private theorem spectral_level_measurable (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F)
    (I : ∀ x : D, SpectralInterval (topElement F x))
    (L U : ℝ) (hL : ∀ x, (I x).lo = L) (hU : ∀ x, (I x).hi = U)
    (hm : ∀ ξ, AEStronglyMeasurable (fun x => ((I x).proj.val.val) ξ) μ) :
    ∀ (n : ℕ) (i : DyadicIndex n), ∃ l u : ℝ,
      (∀ x, ((I x).level (topElement_isSelfAdjoint F hF x) n i).lo = l) ∧
      (∀ x, ((I x).level (topElement_isSelfAdjoint F hF x) n i).hi = u) ∧
      (∀ ξ, AEStronglyMeasurable
        (fun x => ((I x).level (topElement_isSelfAdjoint F hF x) n i).proj.val.val ξ) μ) := by
  intro n
  induction n with
  | zero => intro i; exact ⟨L, U, hL, hU, hm⟩
  | succ n ih =>
    rintro ⟨i, b⟩
    obtain ⟨l, u, hl, hu, hm⟩ := ih i
    let J := fun x => (I x).level (topElement_isSelfAdjoint F hF x) n i
    let p := fun x => (J x).proj.val.val
    have hp (x : D) : IsStarProjection (p x) := (J x).proj.property.map
      (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype
    let P := projectionField p hp hm
    have hP : IsStarProjection P := projectionField_isStarProjection p hp hm
    let m : ℝ := (l + u) / 2
    let Z := P * F * P - (m : ℂ) • P
    have hZ : IsSelfAdjoint Z := by
      change star (P * F * P - (m : ℂ) • P) = P * F * P - (m : ℂ) • P
      simp only [star_sub, star_mul, star_smul, hP.isSelfAdjoint.star_eq,
        hF.star_eq, Complex.star_def, Complex.conj_ofReal, mul_assoc]
    have hmZ (x : D) : topElement Z x = cornerSpectralShift (J x).proj
        (topElement F x) (J x).midpoint := by
      apply Subtype.ext
      change eval Z x = _
      have hmid : (J x).midpoint = m := by
        dsimp [SpectralInterval.midpoint, m, J]
        rw [hl x, hu x]
      rw [hmid]
      rfl
    have hhigh (x : D) : eval (positiveSupport Z) x = (J x).highProjection.val.val := by
      rw [eval_positiveSupport Z hZ x, hmZ x]
      rfl
    have hhighMeas (ξ : H) : AEStronglyMeasurable
        (fun x => (J x).highProjection.val.val ξ) μ := by
      simpa only [hhigh] using (positiveSupport Z).eval_aestronglyMeasurable ξ
    cases b
    · refine ⟨l, m, ?_, ?_, ?_⟩
      · intro x
        exact hl x
      · intro x
        change (J x).midpoint = m
        dsimp [SpectralInterval.midpoint, m, J]
        rw [hl x, hu x]
      · intro ξ
        have hh := (hm ξ).sub (hhighMeas ξ)
        exact hh
    · refine ⟨m, u, ?_, ?_, hhighMeas⟩
      · intro x
        change (J x).midpoint = m
        dsimp [SpectralInterval.midpoint, m, J]
        rw [hl x, hu x]
      · intro x
        exact hu x

private def uniformInterval (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F) (x : D) : SpectralInterval (topElement F x) := by
  let a := topElement F x
  have ha : IsSelfAdjoint a := topElement_isSelfAdjoint F hF x
  have hn : ‖a‖ ≤ ‖F‖ := eval_norm_le F x
  have hupper : a ≤ (‖F‖ : ℂ) • (1 : (fullOperatorAlgebra (H := H)).toStarSubalgebra) := by
    have h := ha.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at h
    have hh : ‖a‖ • (1 : (fullOperatorAlgebra (H := H)).toStarSubalgebra) ≤ ‖F‖ • 1 :=
      smul_le_smul_of_nonneg_right hn zero_le_one
    simpa only [Complex.coe_smul] using h.trans hh
  have hlower : ((-‖F‖ : ℝ) : ℂ) • (1 : (fullOperatorAlgebra (H := H)).toStarSubalgebra) ≤ a := by
    have h := ha.neg_algebraMap_norm_le_self
    rw [Algebra.algebraMap_eq_smul_one] at h
    have hh : (-‖F‖) • (1 : (fullOperatorAlgebra (H := H)).toStarSubalgebra) ≤ (-‖a‖) • 1 :=
      smul_le_smul_of_nonneg_right (neg_le_neg hn) zero_le_one
    have hh' : -(‖F‖ • (1 : (fullOperatorAlgebra (H := H)).toStarSubalgebra)) ≤
        -(‖a‖ • 1) := by simpa only [neg_smul] using hh
    simpa only [Complex.coe_smul, neg_smul] using hh'.trans h
  exact ⟨⟨1, IsStarProjection.one _⟩, -‖F‖, ‖F‖,
    by simpa only [one_mul, mul_one] using sub_nonneg.mpr hlower,
    by simpa only [one_mul, mul_one] using sub_nonpos.mpr hupper⟩

/-- Every self-adjoint measurable field is uniformly approximated by
finite linear combinations of measurable projection fields. -/
theorem selfAdjoint_mem_closed_projection_span (F : WeakOperatorRepresentative (H := H) μ)
    (hF : IsSelfAdjoint F) :
    F ∈ (Submodule.span ℂ {p : WeakOperatorRepresentative (H := H) μ |
      IsStarProjection p}).topologicalClosure := by
  classical
  change F ∈ closure (Submodule.span ℂ {p : WeakOperatorRepresentative (H := H) μ |
    IsStarProjection p} : Set _)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * ‖F‖) / ε)
  have hwidth : (2 * ‖F‖) / (2 : ℝ) ^ n < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have hpow : (n : ℝ) < (2 : ℝ) ^ n := by
      exact_mod_cast (show n < 2 ^ n from Nat.lt_two_pow_self)
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith [mul_lt_mul_of_pos_left hpow hε]
  let I := uniformInterval F hF
  have hmeas := spectral_level_measurable F hF I (-‖F‖) ‖F‖
    (fun _ => rfl) (fun _ => rfl)
    (fun ξ => by
      change AEStronglyMeasurable (fun _ : D => (1 : H →L[ℂ] H) ξ) μ
      simpa only [one_apply_eq_self] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : D => ξ) μ)) n
  choose l u hl hu hm using hmeas
  let p (i : DyadicIndex n) : D → H →L[ℂ] H := fun x =>
    ((I x).level (topElement_isSelfAdjoint F hF x) n i).proj.val.val
  have hp (i : DyadicIndex n) (x : D) : IsStarProjection (p i x) :=
    (((I x).level (topElement_isSelfAdjoint F hF x) n i).proj.property).map
      (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype
  let Q (i : DyadicIndex n) := projectionField (p i) (hp i) (hm i)
  let Y : WeakOperatorRepresentative (H := H) μ := ∑ i, (l i : ℂ) • Q i
  have hY : Y ∈ Submodule.span ℂ {p : WeakOperatorRepresentative (H := H) μ |
      IsStarProjection p} := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact projectionField_isStarProjection (p i) (hp i) (hm i)
  have heval (x : D) : eval Y x = ((I x).approximant (topElement_isSelfAdjoint F hF x) n).val := by
    change evalHom x (∑ i, (l i : ℂ) • Q i) = _
    simp only [map_sum, map_smul, evalHom_apply, SpectralInterval.approximant]
    change (∑ i, (l i : ℂ) • p i x) =
      (fullOperatorAlgebra (H := H)).toStarSubalgebra.subtype
        (∑ i, (((I x).level (topElement_isSelfAdjoint F hF x) n i).lo : ℂ) •
          ((I x).level (topElement_isSelfAdjoint F hF x) n i).proj.val)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change (l i : ℂ) • p i x =
      (((I x).level (topElement_isSelfAdjoint F hF x) n i).lo : ℂ) • p i x
    rw [hl i x]
  have hnorm : ‖F - Y‖ ≤ (2 * ‖F‖) / (2 : ℝ) ^ n := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change ‖eval F x.ofTopology - eval Y x.ofTopology‖ ≤ _
    rw [heval]
    change ‖topElement F x.ofTopology -
      (I x.ofTopology).approximant (topElement_isSelfAdjoint F hF x.ofTopology) n‖ ≤ _
    have h := (I x.ofTopology).approximant_norm_error
      (topElement_isSelfAdjoint F hF x.ofTopology) n (neg_le_self (norm_nonneg F))
    simpa only [I, uniformInterval, one_mul, mul_one, sub_neg_eq_add, two_mul] using h
  exact ⟨Y, hY, by simpa only [dist_eq_norm] using hnorm.trans_lt hwidth⟩

/-- The measurable representative algebra has norm-dense projection span. -/
theorem closed_projection_span_eq_top :
    (Submodule.span ℂ {p : WeakOperatorRepresentative (H := H) μ |
      IsStarProjection p}).topologicalClosure = ⊤ := by
  apply top_unique
  intro F _
  obtain ⟨a, ha, _, hsum⟩ := CStarAlgebra.exists_sum_four_nonneg F
  rw [hsum]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (selfAdjoint_mem_closed_projection_span (a i) (ha i).isSelfAdjoint)

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
