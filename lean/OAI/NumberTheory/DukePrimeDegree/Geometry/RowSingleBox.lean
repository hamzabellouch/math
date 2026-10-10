import OAI.NumberTheory.DukePrimeDegree.Geometry.RowCubes
import OAI.NumberTheory.DukePrimeDegree.Entropy.RowConditionalCompatibility

namespace OAI

/-!
# Compatible row and one-root boxes

For a row box with cubical time domain, separating any one root gives
an actual one-root box. The quotient parametrizations agree on their
domains, not merely up to a leaf-equivalence relation.
-/

noncomputable section
open Matrix Set Metric
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rowToSingleHomeomorph {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    (RowRootSlice i k × RowTime i) ≃ₜ (RootSlice i j k × ℝ) :=
  ((Homeomorph.refl _).prodCongr (rowTimeSplit hij)).trans
    ((Homeomorph.prodAssoc _ _ _).symm.trans
      ((rowReducedHomeomorph hij k).symm.prodCongr (Homeomorph.refl ℝ)))

lemma rowToSingleHomeomorph_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin n)
    (s : RowRootSlice i k) (a : RowTime i) :
    rowToSingleHomeomorph hij k (s, a) =
      ((rowReducedHomeomorph hij k).symm (s, (rowTimeSplit hij a).1), (rowTimeSplit hij a).2) := rfl

theorem rowToSingleHomeomorph_param {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin n)
    (z : RowRootSlice i k × RowTime i) :
    rootQuotientParametrization hij (rowToSingleHomeomorph hij k z) =
      rowQuotientParametrization i k z := by
  obtain ⟨s, a⟩ := z
  rw [rowToSingleHomeomorph_apply, row_one_root_parametrization]
  exact congrArg (fun b : RowTime i => rowQuotientParametrization i k (s, b))
    ((rowTimeSplit hij).symm_apply_apply a)

lemma rowCube_member_split {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {R : ℝ} (hR : 0 < R) (a : RowTime i) :
    a ∈ rowCube i R ↔ rowTimeSplit hij a ∈ rowRemainingCube i j R ×ˢ Ioo (-R) R := by
  rw [← rowTimeSplit_cube hij hR]
  change a ∈ rowCube i R ↔ (rowTimeSplit hij).symm (rowTimeSplit hij a) ∈ rowCube i R
  rw [Homeomorph.symm_apply_apply]

def rowSingleTransverse {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (B : RowRootBox i k) (R : ℝ) : Set (RootSlice i j k) :=
  (rowReducedHomeomorph hij k) ⁻¹' (B.transverse ×ˢ rowRemainingCube i j R)

lemma rowToSingle_domain {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (B : RowRootBox i k) {R : ℝ} (hR : 0 < R) (hT : B.time = rowCube i R)
    (z : RowRootSlice i k × RowTime i) :
    z ∈ B.domain ↔ rowToSingleHomeomorph hij k z ∈ rowSingleTransverse hij B R ×ˢ Ioo (-R) R := by
  obtain ⟨s, a⟩ := z
  rw [rowToSingleHomeomorph_apply]
  change (s ∈ B.transverse ∧ a ∈ B.time) ↔
    ((rowReducedHomeomorph hij k) ((rowReducedHomeomorph hij k).symm
      (s, (rowTimeSplit hij a).1)) ∈ B.transverse ×ˢ rowRemainingCube i j R) ∧
      (rowTimeSplit hij a).2 ∈ Ioo (-R) R
  rw [Homeomorph.apply_symm_apply, hT, rowCube_member_split hij hR]
  exact and_assoc.symm

def RowRootBox.singleRootBox {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (B : RowRootBox i k) {R : ℝ} (hR : 0 < R) (hT : B.time = rowCube i R) : RootBox hij k := by
  let E := rowToSingleHomeomorph hij k
  let eb := E.subtype (rowToSingle_domain hij B hR hT)
  refine ⟨rowSingleTransverse hij B R, Ioo (-R) R,
    (B.transverse_open.prod (isOpen_rowRemainingCube i j R)).preimage
      (rowReducedHomeomorph hij k).continuous, isOpen_Ioo, ?_⟩
  have H := B.embedding.comp eb.symm.isOpenEmbedding
  convert H using 1
  funext z
  have he : E (eb.symm z).val = z.val := congrArg Subtype.val (eb.apply_symm_apply z)
  change rootQuotientParametrization hij z.val = rowQuotientParametrization i k (eb.symm z).val
  rw [← he]
  exact rowToSingleHomeomorph_param hij k _

end DukePrimeDegree

end

end OAI
