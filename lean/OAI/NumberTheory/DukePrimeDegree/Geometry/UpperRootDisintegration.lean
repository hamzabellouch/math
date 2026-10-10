import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootChart

namespace OAI

/-!
# Disintegration in the actual upper-root charts

Both the final Gaussian transversal and the finite product of root times
are standard Borel spaces. The open quotient charts therefore give
finite coordinate measures and genuine conditional probability kernels.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma isClosed_zeroPattern {n : ℕ} (P : Finset (Fin n × Fin n)) :
    IsClosed {g : G n | ZeroPattern P g} := by
  have H : IsClosed (⋂ p ∈ P, {g : G n | g.val p.1 p.2 = 0}) := by
    apply isClosed_biInter
    intro p _
    exact isClosed_eq (by fun_prop) continuous_const
  convert H using 1
  ext g
  simp [ZeroPattern]

lemma isOpen_nonzeroPivots {n : ℕ} (D : Finset (Fin n)) :
    IsOpen {g : G n | NonzeroPivots D g} := by
  have H : IsOpen (⋂ r ∈ D, {g : G n | g.val r r ≠ 0}) :=
    isOpen_biInter_finset (fun r _ => rootPivot_isOpen r r)
  convert H using 1
  ext g
  simp [NonzeroPivots]

instance specialLinear_standardBorel (n : ℕ) : StandardBorelSpace (G n) := by
  let : PolishSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (PolishSpace (Fin n → Fin n → ℝ))
  have hc : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.det = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  let : PolishSpace (G n) := hc.polishSpace
  infer_instance

instance eliminationSlice_standardBorel {n : ℕ}
    (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)) :
    StandardBorelSpace (EliminationSlice P D) :=
  ((isClosed_zeroPattern P).measurableSet.inter (isOpen_nonzeroPivots D).measurableSet).standardBorel

instance EliminationChain.time_secondCountable {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    SecondCountableTopology c.Time := by
  induction c with
  | done => exact inferInstanceAs (SecondCountableTopology PUnit)
  | step a b hab hP hb tail ih =>
      let := ih
      exact inferInstanceAs (SecondCountableTopology (tail.Time × ℝ))

instance EliminationChain.time_polish {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    PolishSpace c.Time := by
  induction c with
  | done => exact inferInstanceAs (PolishSpace PUnit)
  | step a b hab hP hb tail ih =>
      let := ih
      exact inferInstanceAs (PolishSpace (tail.Time × ℝ))

instance EliminationChain.time_measurableSpace {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    MeasurableSpace c.Time := borel c.Time

instance EliminationChain.time_borelSpace {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    BorelSpace c.Time := ⟨rfl⟩

instance EliminationChain.time_standardBorel {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    StandardBorelSpace c.Time := by infer_instance

instance EliminationChain.time_nonempty {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    Nonempty c.Time := ⟨c.zeroTime⟩

namespace UpperRootBox
variable {n : ℕ} {g : G n}

abbrev domain (B : UpperRootBox n g) := B.transverse ×ˢ B.time
abbrev param (B : UpperRootBox n g) := B.domain.domRestrict (upperRootQuotientParam n g)
def range (B : UpperRootBox n g) := Set.range B.param

lemma range_open (B : UpperRootBox n g) : IsOpen B.range := B.embedding.isOpen_range

def coordinateMeasure (B : UpperRootBox n g) (μ : Measure (X n)) :
    Measure (UpperRootTransverse n × UpperRootTime n) :=
  (Measure.comap B.param μ).map Subtype.val

instance coordinateMeasure_finite (B : UpperRootBox n g) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsFiniteMeasure (B.coordinateMeasure μ) := by
  have he := B.embedding.measurableEmbedding
  have : IsFiniteMeasure (Measure.comap B.param μ) := ⟨by
    rw [he.comap_apply]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top μ univ)⟩
  unfold coordinateMeasure
  infer_instance

lemma map_coordinateMeasure (B : UpperRootBox n g) (μ : Measure (X n)) :
    (B.coordinateMeasure μ).map (upperRootQuotientParam n g) = μ.restrict B.range := by
  rw [coordinateMeasure, Measure.map_map]
  · exact B.embedding.measurableEmbedding.map_comap μ
  · exact (upperRootQuotientParam_localHomeomorph n g).continuous.measurable
  · exact measurable_subtype_coe

def conditionalKernel (B : UpperRootBox n g) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    Kernel (UpperRootTransverse n) (UpperRootTime n) := (B.coordinateMeasure μ).condKernel

instance conditionalKernel_markov (B : UpperRootBox n g) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsMarkovKernel (B.conditionalKernel μ) := by
  unfold conditionalKernel
  infer_instance

theorem disintegrate (B : UpperRootBox n g) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    Measure.map (upperRootQuotientParam n g)
      ((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ) = μ.restrict B.range := by
  rw [conditionalKernel, Measure.disintegrate]
  exact B.map_coordinateMeasure μ

end UpperRootBox
end DukePrimeDegree

end

end OAI
