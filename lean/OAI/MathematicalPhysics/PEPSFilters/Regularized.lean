import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.FilterStationarity
import OAI.MathematicalPhysics.PEPSFilters.Coordinates

namespace OAI

/-! Regularized spectral coordinates, commuting optimizers and compact limits. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder

def regularizedCoordinateMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (b a : ℝ) (p : SpectralCoordinate n) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ p.1
    (Matrix.diagonal (fun i => (((p.2.val i + b) ^ (a/2) : ℝ) : ℂ)))

lemma regularizedCoordinateMatrix_zero {n : Type*} [Fintype n] [DecidableEq n]
    (a : ℝ) (p : SpectralCoordinate n) :
    regularizedCoordinateMatrix 0 a p = coordinateMatrix a p := by
  simp only [regularizedCoordinateMatrix, coordinateMatrix, add_zero]

lemma regularizedCoordinateMatrix_positive {n : Type*} [Fintype n] [DecidableEq n]
    {b : ℝ} (hb : 0 ≤ b) (a : ℝ) (p : SpectralCoordinate n) :
    (regularizedCoordinateMatrix b a p).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact_mod_cast Real.rpow_nonneg (add_nonneg (p.2.property.1 i) hb) (a/2)

lemma regularizedCoordinateMatrix_invertible {n : Type*} [Fintype n] [DecidableEq n]
    {b : ℝ} (hb : 0 < b) (a : ℝ) (p : SpectralCoordinate n) :
    IsUnit (regularizedCoordinateMatrix b a p).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply IsUnit.map (Unitary.conjStarAlgAut ℂ _ p.1).toRingHom
  apply Matrix.isUnit_diagonal.mpr
  apply Pi.isUnit_iff.mpr
  intro i
  apply isUnit_iff_ne_zero.mpr
  apply Complex.ofReal_ne_zero.mpr
  exact (Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos (p.2.property.1 i) hb) _).ne'

lemma regularizedCoordinateMatrix_continuous {n : Type*} [Fintype n] [DecidableEq n]
    (b a : ℝ) (ha : 0 < a) :
    Continuous (regularizedCoordinateMatrix (n := n) b a) := by
  unfold regularizedCoordinateMatrix Unitary.conjStarAlgAut
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_subtype_val.comp continuous_fst
    · apply continuous_matrix
      intro i k
      by_cases h : i = k
      · subst k
        simp only [Matrix.diagonal_apply_eq]
        exact Complex.continuous_ofReal.comp
          ((Real.continuous_rpow_const (by linarith : 0 ≤ a/2)).comp
            (((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).add continuous_const))
      · simp only [Matrix.diagonal_apply_ne _ h]
        exact continuous_const
  · exact (continuous_subtype_val.comp continuous_fst).star

lemma regularizedCoordinateMatrix_conjugate {n : Type*} [Fintype n] [DecidableEq n]
    (b a : ℝ) (p : SpectralCoordinate n) (U : unitary (Matrix n n ℂ)) :
    regularizedCoordinateMatrix b a (U * p.1, p.2) =
      (U : Matrix n n ℂ) * regularizedCoordinateMatrix b a p * star (U : Matrix n n ℂ) := by
  simp only [regularizedCoordinateMatrix, Unitary.conjStarAlgAut_apply, Submonoid.coe_mul,
    star_mul, Matrix.mul_assoc]

variable {L q m : ℕ} [NeZero q] {X : Fin m → Finset (Vertex L)}

def regularizedFilters {b : ℝ} (hb : 0 ≤ b) (a : Fin m → ℝ) (p : CoordinateFamily q X) :
    FilterFamily q m X := fun j =>
  ⟨regularizedCoordinateMatrix b (a j) (p j), regularizedCoordinateMatrix_positive hb _ _⟩

def IsRegularizedMaximizer {b : ℝ} (hb : 0 ≤ b) (Ω : State L q) (a : Fin m → ℝ)
    (p : CoordinateFamily q X) : Prop :=
  ∀ s : CoordinateFamily q X, ‖output (regularizedFilters hb a s) Ω‖ ≤
    ‖output (regularizedFilters hb a p) Ω‖

omit [NeZero q] in
lemma regularized_output_continuous {b : ℝ} (hb : 0 ≤ b) (Ω : State L q)
    {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) :
    Continuous (fun p : CoordinateFamily q X => output (regularizedFilters hb a p) Ω) := by
  apply continuous_chain
  · intro j
    have hc : Continuous (fun p : CoordinateFamily q X => regularizedCoordinateMatrix b (a j) (p j)) :=
      (regularizedCoordinateMatrix_continuous b (a j) (ha j)).comp (continuous_apply j)
    have hl : Continuous (liftLocal (q := q) (X j)) :=
      (liftLocalHom (q := q) (X j)).toLinearMap.continuous_of_finiteDimensional
    have hm : Continuous (asMap (L := L) (q := q)) := by
      change Continuous (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ))
      exact (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
    exact hm.comp (hl.comp hc)
  · exact continuous_const

lemma exists_regularized_maximizer {b : ℝ} (hb : 0 ≤ b) (Ω : State L q)
    {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) :
    ∃ p : CoordinateFamily q X, IsRegularizedMaximizer hb Ω a p := by
  classical
  let (j : Fin m) : CompactSpace (SpectralCoordinate (RegionConfiguration q (X j))) := by
    let := compact_unitary_coordinates (n := RegionConfiguration q (X j))
    let := compact_weight_coordinates (n := RegionConfiguration q (X j))
    infer_instance
  let p₀ : CoordinateFamily q X := fun j => uniformCoordinate (RegionConfiguration q (X j))
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn
    (⟨p₀, Set.mem_univ _⟩ : (Set.univ : Set (CoordinateFamily q X)).Nonempty)
    (regularized_output_continuous hb Ω ha).norm.continuousOn
  exact ⟨p, fun s => hp (Set.mem_univ s)⟩

omit [NeZero q] in
lemma insertion_stationarity_of_unitary_max {F : FilterFamily q m X} {Ω : State L q}
    (j : Fin m)
    (hmax : ∀ U : unitary (Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ),
      ‖insertionMap F Ω j ((U : Matrix _ _ ℂ) * (F j).matrix * star (U : Matrix _ _ ℂ))‖ ≤
      ‖output F Ω‖)
    (B : Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ)
    (hB : star B = -B) :
    (inner ℂ (output F Ω)
      (insertionMap F Ω j (B * (F j).matrix - (F j).matrix * B))).re = 0 := by
  let : NormedAlgebra ℚ (Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let C := (insertionMap F Ω j).toContinuousLinearMap
  let y (t : ℝ) := C (NormedSpace.exp (t • B) * (F j).matrix * star (NormedSpace.exp (t • B)))
  have hy : HasDerivAt y (C (B * (F j).matrix - (F j).matrix * B)) 0 := by
    have hd := (C.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (Stationarity.deriv_conjugation_matrix (F j).matrix B hB)
    convert hd using 1 <;> rfl
  have hzero : y 0 = output F Ω := by
    simp only [y, zero_smul, NormedSpace.exp_zero, one_mul, star_one, mul_one]
    exact insertionMap_self F Ω j
  have hh : ∀ t, ‖y t‖ ≤ ‖y 0‖ := by
    intro t
    rw [hzero]
    have hU : NormedSpace.exp (t • B) ∈ unitary _ := by
      apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      rw [skewAdjoint.mem_iff]
      simp [hB]
    exact hmax ⟨_, hU⟩
  have hs := Stationarity.re_inner_deriv_eq_zero_of_max hy hh
  rw [hzero] at hs
  exact hs

omit [NeZero q] in
lemma IsRegularizedMaximizer.insertion_unitary_max {b : ℝ} {hb : 0 ≤ b}
    {Ω : State L q} {a : Fin m → ℝ} {p : CoordinateFamily q X}
    (hp : IsRegularizedMaximizer hb Ω a p) (j : Fin m)
    (U : unitary (Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ)) :
    ‖insertionMap (regularizedFilters hb a p) Ω j
      ((U : Matrix _ _ ℂ) * (regularizedFilters hb a p j).matrix * star (U : Matrix _ _ ℂ))‖ ≤
      ‖output (regularizedFilters hb a p) Ω‖ := by
  classical
  let s : CoordinateFamily q X := Function.update p j (U * (p j).1, (p j).2)
  have he : output (regularizedFilters hb a s) Ω =
      insertionMap (regularizedFilters hb a p) Ω j
        ((U : Matrix _ _ ℂ) * (regularizedFilters hb a p j).matrix * star (U : Matrix _ _ ℂ)) := by
    change matrixOutput (fun k => liftLocal (X k) (regularizedCoordinateMatrix b (a k) (s k))) Ω =
      matrixOutput (Function.update _ j _) Ω
    congr 1
    funext k
    by_cases hk : k = j
    · subst k
      simp only [s, Function.update_self, regularizedFilters]
      rw [regularizedCoordinateMatrix_conjugate]
      rfl
    · simp only [s, Function.update_of_ne hk]
      rfl
  rw [← he]
  exact hp s

theorem exists_regularized_maximizer_commute {b : ℝ} (hb : 0 < b) (Ω : State L q)
    (hX : Monotone X) {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) :
    ∃ p : CoordinateFamily q X, IsRegularizedMaximizer hb.le Ω a p ∧
      ∀ j, Commute (regularizedFilters hb.le a p j).matrix
        (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j)) := by
  obtain ⟨p, hp⟩ := exists_regularized_maximizer (X := X) hb.le Ω ha
  refine ⟨p, hp, ?_⟩
  apply commute_of_insertion_stationarity X hX (regularizedFilters hb.le a p) Ω
  · intro j
    exact regularizedCoordinateMatrix_invertible hb (a j) (p j)
  · intro j B hB
    exact insertion_stationarity_of_unitary_max j (hp.insertion_unitary_max j) B hB

end PolynomialPEPS.PinnedEntropy.NestedFilter
namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open Filter Analytic

lemma regularizedCoordinateMatrix_jointContinuous {n : Type*} [Fintype n] [DecidableEq n]
    (a : ℝ) (ha : 0 < a) :
    Continuous (fun z : ℝ × SpectralCoordinate n => regularizedCoordinateMatrix z.1 a z.2) := by
  unfold regularizedCoordinateMatrix Unitary.conjStarAlgAut
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    · apply continuous_matrix
      intro i k
      by_cases h : i = k
      · subst k
        simp only [Matrix.diagonal_apply_eq]
        exact Complex.continuous_ofReal.comp
          ((Real.continuous_rpow_const (by linarith : 0 ≤ a/2)).comp
            (((continuous_apply i).comp
              (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).add continuous_fst))
      · simp only [Matrix.diagonal_apply_ne _ h]
        exact continuous_const
  · exact (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).star

variable {L q m : ℕ} [NeZero q] {X : Fin m → Finset (Vertex L)}

def regularizedRawOutput (b : ℝ) (a : Fin m → ℝ) (p : CoordinateFamily q X) (Ω : State L q) :
    State L q := matrixOutput (fun j => liftLocal (X j) (regularizedCoordinateMatrix b (a j) (p j))) Ω

omit [NeZero q] in
lemma regularizedRawOutput_eq {b : ℝ} (hb : 0 ≤ b) (a : Fin m → ℝ)
    (p : CoordinateFamily q X) (Ω : State L q) :
    regularizedRawOutput b a p Ω = output (regularizedFilters hb a p) Ω := rfl

omit [NeZero q] in
lemma regularizedRawOutput_zero (a : Fin m → ℝ) (p : CoordinateFamily q X) (Ω : State L q) :
    regularizedRawOutput 0 a p Ω = output (coordinateFilters a p) Ω := by
  unfold regularizedRawOutput
  simp only [regularizedCoordinateMatrix_zero]
  rfl

omit [NeZero q] in
lemma regularizedRawOutput_jointContinuous (Ω : State L q) {a : Fin m → ℝ}
    (ha : ∀ j, 0 < a j) :
    Continuous (fun z : ℝ × CoordinateFamily q X => regularizedRawOutput z.1 a z.2 Ω) := by
  apply continuous_chain
  · intro j
    have hc : Continuous (fun z : ℝ × CoordinateFamily q X =>
        regularizedCoordinateMatrix z.1 (a j) (z.2 j)) :=
      (regularizedCoordinateMatrix_jointContinuous (a j) (ha j)).comp₂ continuous_fst
        ((continuous_apply j).comp continuous_snd)
    have hl : Continuous (liftLocal (q := q) (X j)) :=
      (liftLocalHom (q := q) (X j)).toLinearMap.continuous_of_finiteDimensional
    have hm : Continuous (asMap (L := L) (q := q)) := by
      change Continuous (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ))
      exact (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
    exact hm.comp (hl.comp hc)
  · exact continuous_const

omit [NeZero q] in
lemma continuous_reducedDensity (A : Finset (Vertex L)) :
    Continuous (fun v : State L q => reducedDensity v A) := by
  have hc : Continuous (fun v : State L q => coefficientMatrix v A) := by
    apply continuous_matrix
    intro i k
    exact (EuclideanSpace.proj (joinConfigurations A i k)).continuous
  apply continuous_matrix
  intro i k
  change Continuous (fun v : State L q => ∑ z,
    coefficientMatrix v A i z * star (coefficientMatrix v A k z))
  exact continuous_finsetSum _ (fun z _ =>
    ((EuclideanSpace.proj (joinConfigurations A i z)).continuous).mul
      ((EuclideanSpace.proj (joinConfigurations A k z)).continuous).star)

omit [NeZero q] in
lemma isMaximizer_of_coordinate_max (Ω : State L q) {a : Fin m → ℝ}
    (ha : ∀ j, 0 < a j) (p : CoordinateFamily q X)
    (hp : ∀ s : CoordinateFamily q X,
      ‖output (coordinateFilters a s) Ω‖ ≤ ‖output (coordinateFilters a p) Ω‖) :
    IsMaximizer Ω a (coordinateFilters a p) := by
  classical
  refine ⟨coordinateFilters_admissible ha p, ?_⟩
  intro G hG
  have hc (j : Fin m) : ∃ s : SpectralCoordinate (RegionConfiguration q (X j)),
      coordinateMatrix (a j) s = (G j).matrix :=
    coordinateMatrix_surjective (G j).positive (ha j) (hG j)
  choose s hs using hc
  have heT : (fun j : Fin m => asMap (liftLocal (X j) (coordinateMatrix (a j) (s j)))) =
      (fun j : Fin m => asMap (liftLocal (X j) (G j).matrix)) := by
    funext j
    rw [hs j]
  have he : output (coordinateFilters a s) Ω = output G Ω := by
    change chain (fun j => asMap (liftLocal (X j) (coordinateMatrix (a j) (s j)))) Ω = _
    rw [heT]
    rfl
  rw [← he]
  exact hp s

theorem exists_maximizer_commute (Ω : State L q) (hX : Monotone X)
    {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) :
    ∃ F : FilterFamily q m X, IsMaximizer Ω a F ∧
      ∀ j, Commute (F j).matrix (reducedDensity (output F Ω) (X j)) := by
  classical
  let b (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hb (n : ℕ) : 0 < b n := by dsimp [b]; positivity
  have he (n : ℕ) : ∃ p : CoordinateFamily q X,
      IsRegularizedMaximizer (hb n).le Ω a p ∧
      ∀ j, Commute (regularizedFilters (hb n).le a p j).matrix
        (reducedDensity (output (regularizedFilters (hb n).le a p) Ω) (X j)) :=
    exists_regularized_maximizer_commute (hb n) Ω hX ha
  choose p hp hcomm using he
  let (j : Fin m) : CompactSpace (SpectralCoordinate (RegionConfiguration q (X j))) := by
    let := compact_unitary_coordinates (n := RegionConfiguration q (X j))
    let := compact_weight_coordinates (n := RegionConfiguration q (X j))
    infer_instance
  obtain ⟨s, ns, hns, hs⟩ := CompactSpace.tendsto_subseq p
  have hbs : Tendsto (fun n => b (ns n)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hns.tendsto_atTop
  have hpair : Tendsto (fun n => (b (ns n), p (ns n))) atTop (nhds (0, s)) :=
    hbs.prodMk_nhds hs
  have hout := ((regularizedRawOutput_jointContinuous Ω ha).tendsto (0, s)).comp hpair
  refine ⟨coordinateFilters a s, isMaximizer_of_coordinate_max Ω ha s ?_, ?_⟩
  · intro t
    have ht := ((regularizedRawOutput_jointContinuous Ω ha).tendsto (0, t)).comp
      (hbs.prodMk_nhds tendsto_const_nhds)
    have hh := le_of_tendsto_of_tendsto ht.norm hout.norm
      (Filter.Eventually.of_forall (fun n => hp (ns n) t))
    simpa only [regularizedRawOutput_zero] using hh
  · intro j
    have hc : Continuous (fun z : ℝ × CoordinateFamily q X =>
        regularizedCoordinateMatrix z.1 (a j) (z.2 j)) :=
      (regularizedCoordinateMatrix_jointContinuous (a j) (ha j)).comp₂ continuous_fst
        ((continuous_apply j).comp continuous_snd)
    have hd := (continuous_reducedDensity (X j)).comp (regularizedRawOutput_jointContinuous (X := X) Ω ha)
    have hclosed := isClosed_eq (hc.mul hd) (hd.mul hc)
    have hh := hclosed.mem_of_tendsto hpair
      (Filter.Eventually.of_forall (fun n => (hcomm (ns n) j).eq))
    change regularizedCoordinateMatrix 0 (a j) (s j) *
        reducedDensity (regularizedRawOutput 0 a s Ω) (X j) =
      reducedDensity (regularizedRawOutput 0 a s Ω) (X j) *
        regularizedCoordinateMatrix 0 (a j) (s j) at hh
    rw [regularizedCoordinateMatrix_zero, regularizedRawOutput_zero] at hh
    exact hh

end PolynomialPEPS.PinnedEntropy.NestedFilter

end

end OAI
