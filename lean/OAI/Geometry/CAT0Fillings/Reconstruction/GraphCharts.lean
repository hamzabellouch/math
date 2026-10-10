import Mathlib
import OAI.Geometry.CAT0Fillings.BV.JointPoincare
import OAI.Geometry.CAT0Fillings.Reconstruction.BorelAtoms
import OAI.Geometry.CAT0Fillings.Reconstruction.AtomCarrier

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

abbrev FullGraphIndex := JointPieceIndex × AtomCode

theorem fullSlice_compact_atom_graphs {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i)) :
    ∃ (D : FullGraphIndex → Set (Euc (k+1)))
      (L U : FullGraphIndex → ℝ≥0)
      (γ : ∀ i : FullGraphIndex, D i → Fin i.2.size → X),
      (∀ i, IsCompact (D i)) ∧ (∀ᵐ z : Euc (k+1), z ∈ ⋃ i, D i) ∧
      (∀ i j, LipschitzWith (L i) (fun t => γ i t j)) ∧
      (∀ i j, AntilipschitzWith (U i) (fun t => γ i t j)) ∧
      (∀ i (t : D i) j, coordinateMap π (γ i t j) = t) ∧
      (∀ i (t : D i), UnitRepresentation (fullSlice h π t) i.2.weights (γ i t)) ∧
      (∀ i (t : D i), Function.Injective (γ i t)) := by
  classical
  have hπb (i) := boundedLip_of_lipschitz (hπ i)
  obtain ⟨D,L,γ,hD,hcover,hL,hI,hrep,hinj,hweights⟩ := joint_integer_atom_graphs
    (μ := volume) (fullSlice h π) (Eventually.of_forall (fullSlice_integral h π))
    (fun b hb hb1 => (fullSlice_eval_integrable h hX π hπb ⟨⟨1,hb⟩,1,hb1⟩
      (fun j => Fin.elim0 j)).locallyIntegrable)
    (fullSliceControl h π K) (C := 4*(2:ℝ)^(k+1)*(k+1)) (κ := 2)
    (by positivity) (by norm_num)
    (fun b hb hb1 a _r hr => fullSlice_ball_poincare h hX π hπ hb hb1 a hr)
  obtain ⟨A,hA⟩ := coordinateMap_lipschitz π hπ
  let (i : FullGraphIndex) : CompactSpace (D i) := isCompact_iff_compactSpace.mp (hD i)
  let F (i : FullGraphIndex) := {t : D i | ∀ j, coordinateMap π (γ i t j) = t}
  have hF (i) : IsCompact (F i) := by
    apply IsClosed.isCompact
    simpa only [F,ofPred_forall, Function.comp_def] using isClosed_iInter (fun j => isClosed_eq (hA.continuous.comp (hL i j).continuous) continuous_subtype_val)
  let D' (i : FullGraphIndex) : Set (Euc (k+1)) := Subtype.val '' F i
  have hsub (i) : D' i ⊆ D i := by
    rintro z ⟨t,ht,rfl⟩
    exact t.property
  let γ' (i : FullGraphIndex) (t : D' i) := γ i ⟨t,hsub i t.property⟩
  have hbase (i) (t : D' i) (j) : coordinateMap π (γ' i t j) = t := by
    obtain ⟨s,hs,he⟩ := t.property
    have ht : (⟨t,hsub i t.property⟩ : D i) = s := Subtype.ext he.symm
    change coordinateMap π (γ i ⟨t,hsub i t.property⟩ j) = t
    rw [ht,hs j,he]
  refine ⟨D',L,fun _ => A,γ',?_,?_,?_,?_,hbase,?_,?_⟩
  · intro i
    exact (hF i).image continuous_subtype_val
  · filter_upwards [hcover,ae_fullSlice_mass_fiber h hX π hπb] with z hz hmass
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    apply mem_iUnion.mpr
    refine ⟨i,⟨⟨z,hi⟩,?_,rfl⟩⟩
    intro j
    exact (hrep i ⟨z,hi⟩).atom_in_carrier (fullSlice_approx h π z).metric
      (hweights i ⟨z,hi⟩) (hinj i ⟨z,hi⟩)
      (measurableSet_eq_fun hA.continuous.measurable measurable_const) hmass j
  · intro i j
    apply LipschitzWith.of_dist_le_mul
    intro s t
    exact (hL i j).dist_le_mul ⟨s,hsub i s.property⟩ ⟨t,hsub i t.property⟩
  · intro i j
    apply AntilipschitzWith.of_le_mul_dist
    intro s t
    have hh := hA.dist_le_mul (γ' i s j) (γ' i t j)
    rwa [hbase i s j,hbase i t j] at hh
  · intro i t
    exact hrep i ⟨t,hsub i t.property⟩
  · intro i t
    exact hinj i ⟨t,hsub i t.property⟩

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] {k : ℕ}

noncomputable def jointGraphChart {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ) : IntegerChart X k where
  domain := D
  borel := hD.measurableSet
  bounded := hD.isBounded
  param := γ
  bilipschitz := hγ
  multiplicity := fun _ => a
  integrable := integrableOn_const (C := (a : ℝ)) (hD.measure_lt_top (μ := volume)).ne

lemma jointGraphChart_image {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ) :
    (jointGraphChart hD γ hγ a).image = Set.range γ := rfl

lemma jointGraphChart_base_jacobian {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K, LipschitzWith K (π i))
    (hbase : ∀ t : D, ∀ i, π i (γ t) = t.val i) :
    ∀ᵐ z ∂volume.restrict D, (jointGraphChart hD γ hγ a).jacobian π z = 1 := by
  let C := jointGraphChart hD γ hγ a
  have he (i : Fin k) := C.ae_fderivWithin_scalar_eq_linear C.borel (subset_refl _)
    (hπ i).choose_spec (EuclideanSpace.proj i) (by
      intro z hz
      rw [C.scalar_eq hz]
      exact hbase ⟨z,hz⟩ i)
  filter_upwards [ae_all_iff.mpr he] with z hz
  change (Matrix.of fun i j => fderivWithin ℝ (C.scalar (π i)) D z (EuclideanSpace.single j 1)).det = 1
  change ∀ i, fderivWithin ℝ (C.scalar (π i)) D z = EuclideanSpace.proj i at hz
  have hm : (Matrix.of fun i j => fderivWithin ℝ (C.scalar (π i)) D z (EuclideanSpace.single j 1)) =
      (1 : Matrix (Fin k) (Fin k) ℝ) := by
    ext i j
    rw [Matrix.of_apply,hz i]
    simp [Matrix.one_apply]
  rw [hm,Matrix.det_one]

noncomputable def jointGraphFunction {D : Set (Euc k)} (γ : D → X) (b : X → ℝ) (z : Euc k) : ℝ :=
  if hz : z ∈ D then b (γ ⟨z,hz⟩) else 0

lemma jointGraphChart_base_action [MeasurableSpace X] [BorelSpace X]
    {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K, LipschitzWith K (π i))
    (hbase : ∀ t : D, ∀ i, π i (γ t) = t.val i)
    {b : X → ℝ} (hb : BoundedLip b) :
    (jointGraphChart hD γ hγ a).action b π = ∫ z in D, (a : ℝ)*jointGraphFunction γ b z := by
  let C := jointGraphChart hD γ hγ a
  rw [IntegerChart.action,ite_eq_left ⟨hb,hπ⟩]
  apply integral_congr_ae
  filter_upwards [jointGraphChart_base_jacobian hD γ hγ a π hπ hbase,ae_restrict_mem hD.measurableSet] with z hj hz
  rw [hj,mul_one,C.scalar_eq hz]
  change z ∈ D at hz
  simp only [jointGraphFunction,dite_eq_left hz]
  rfl

end CAT0Fillings.SliceReconstruction
end

end OAI
