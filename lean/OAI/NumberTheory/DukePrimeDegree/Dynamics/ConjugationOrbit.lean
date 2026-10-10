import OAI.NumberTheory.DukePrimeDegree.Dynamics.LatticeCentralizer
import OAI.NumberTheory.DukePrimeDegree.Geometry.MatrixConjugationDensity

namespace OAI

/-!
# Conjugation maps on actual lattice orbit quotients

A matrix commuting with the lattice stabilizer defines a continuous
conjugation map on the corresponding homogeneous orbit quotient. Right
invariance of a measure on that quotient gives conjugation invariance of
its pushforward. This is the geometric bridge used by the elementary
matrix-density argument.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def slMatrixConjugation {n : ℕ} (h : G n) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := h⁻¹.val * M * h.val

lemma slMatrixConjugation_mul {n : ℕ} (h k : G n) (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugation (h * k) M = slMatrixConjugation k (slMatrixConjugation h M) := by
  simp only [slMatrixConjugation, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul]
  simp only [mul_assoc]

lemma slMatrixConjugation_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugation (1 : G n) M = M := by
  simp [slMatrixConjugation]

lemma slMatrixConjugation_eq_self {n : ℕ} (h : G n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hc : Commute M h.val) : slMatrixConjugation h M = M := by
  change h⁻¹.val * M * h.val = M
  rw [mul_assoc, hc.eq, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]

lemma continuous_slMatrixConjugation {n : ℕ} (h : G n) :
    Continuous (slMatrixConjugation h) := by
  unfold slMatrixConjugation
  fun_prop

/-- The subgroup of the orbit group fixing the lattice represented by `g`. -/
def pointOrbitStabilizer {n : ℕ} (g : G n) (H : Subgroup (G n)) : Subgroup H :=
  (integralGroup n).comap ((MulAut.conj g).toMonoidHom.comp H.subtype)

abbrev LatticeOrbitQuotient {n : ℕ} (g : G n) (H : Subgroup (G n)) :=
  Quotient (QuotientGroup.rightRel (pointOrbitStabilizer g H))

instance latticeOrbitQuotientMeasurableSpace {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    MeasurableSpace (LatticeOrbitQuotient g H) := borel _

instance latticeOrbitQuotientBorelSpace {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    BorelSpace (LatticeOrbitQuotient g H) := ⟨rfl⟩

def latticeOrbitInverseHomeomorph {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    LatticeOrbitQuotient g H ≃ₜ (H ⧸ pointOrbitStabilizer g H) where
  toEquiv := QuotientGroup.quotientRightRelEquivQuotientLeftRel (pointOrbitStabilizer g H)
  continuous_toFun := by
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp continuous_inv
  continuous_invFun := by
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp continuous_inv

instance latticeOrbitQuotientSecondCountable {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    SecondCountableTopology (LatticeOrbitQuotient g H) := by
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  change SecondCountableTopology (Quotient (MulAction.orbitRel (pointOrbitStabilizer g H) H))
  exact ContinuousConstSMul.secondCountableTopology

def latticeOrbitRightAction {n : ℕ} (g : G n) (H : Subgroup (G n))
    (x : LatticeOrbitQuotient g H) (h : H) : LatticeOrbitQuotient g H :=
  Quotient.map (fun k => k * h) (by
    intro a b hab
    change (QuotientGroup.rightRel (pointOrbitStabilizer g H)) a b at hab
    change (QuotientGroup.rightRel (pointOrbitStabilizer g H)) (a * h) (b * h)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hab) x

lemma continuous_latticeOrbitRightAction {n : ℕ} (g : G n) (H : Subgroup (G n)) (h : H) :
    Continuous (fun x => latticeOrbitRightAction g H x h) := by
  apply continuous_quot_lift
  exact continuous_quotient_mk'.comp (continuous_id.mul continuous_const)

lemma latticeOrbitRightAction_transitive {n : ℕ} (g : G n) (H : Subgroup (G n))
    (x y : LatticeOrbitQuotient g H) : ∃ h : H, latticeOrbitRightAction g H x h = y := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      refine ⟨a⁻¹ * b, ?_⟩
      change Quotient.mk _ (a * (a⁻¹ * b)) = Quotient.mk _ b
      rw [mul_inv_cancel_left]

/-- A nonzero invariant measure on the transitive orbit quotient has
full support; full support is not a separate orbit assumption. -/
theorem latticeOrbit_support_eq_univ {n : ℕ} (g : G n) (H : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g H)) (hμ : μ ≠ 0)
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ) :
    μ.support = Set.univ := by
  obtain ⟨x, hx⟩ := Measure.nonempty_support hμ
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨h, rfl⟩ := latticeOrbitRightAction_transitive g H x y
  have hf := continuous_latticeOrbitRightAction g H h
  have hae : ∀ᵐ z ∂μ, latticeOrbitRightAction g H z h ∈ μ.support := by
    apply ae_of_ae_map hf.measurable.aemeasurable
    rw [hinv h]
    exact Measure.support_mem_ae
  exact Measure.support_subset_of_isClosed (Measure.isClosed_support.preimage hf) hae hx

/-- The conjugation orbit map exists because its value is unchanged by
the actual lattice point stabilizer. -/
def conjugationOrbitMap {n : ℕ} (g : G n) (H : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g H, Commute M s.val.val) :
    LatticeOrbitQuotient g H → Matrix (Fin n) (Fin n) ℝ :=
  Quotient.lift (fun h : H => slMatrixConjugation h.val M) (by
    intro a b hab
    change QuotientGroup.rightRel (pointOrbitStabilizer g H) a b at hab
    rw [QuotientGroup.rightRel_apply] at hab
    have hab' : a * b⁻¹ ∈ pointOrbitStabilizer g H := by
      simpa only [_root_.mul_inv_rev, inv_inv] using (pointOrbitStabilizer g H).inv_mem hab
    have hs := slMatrixConjugation_eq_self (a * b⁻¹).val M (hM ⟨a * b⁻¹, hab'⟩)
    calc
      slMatrixConjugation a.val M = slMatrixConjugation ((a * b⁻¹) * b).val M := by simp
      _ = slMatrixConjugation b.val (slMatrixConjugation (a * b⁻¹).val M) :=
        slMatrixConjugation_mul _ _ _
      _ = slMatrixConjugation b.val M := by rw [hs])

lemma continuous_conjugationOrbitMap {n : ℕ} (g : G n) (H : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g H, Commute M s.val.val) :
    Continuous (conjugationOrbitMap g H M hM) := by
  apply continuous_quot_lift
  unfold slMatrixConjugation
  fun_prop

lemma conjugationOrbitMap_rightAction {n : ℕ} (g : G n) (H : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g H, Commute M s.val.val)
    (x : LatticeOrbitQuotient g H) (h : H) :
    conjugationOrbitMap g H M hM (latticeOrbitRightAction g H x h) =
      slMatrixConjugation h.val (conjugationOrbitMap g H M hM x) := by
  induction x using Quotient.inductionOn with
  | h k => exact slMatrixConjugation_mul k.val h.val M

lemma conjugationOrbitMap_identity {n : ℕ} (g : G n) (H : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g H, Commute M s.val.val) :
    conjugationOrbitMap g H M hM (Quotient.mk _ (1 : H)) = M :=
  slMatrixConjugation_one M

/-- Invariant measure on the actual orbit quotient gives a finite
dimensional conjugation-invariant distribution. -/
theorem conjugationOrbitMap_map_invariant {n : ℕ} (g : G n) (H : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g H, Commute M s.val.val)
    (μ : Measure (LatticeOrbitQuotient g H))
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ) (h : H) :
    (μ.map (conjugationOrbitMap g H M hM)).map (slMatrixConjugation h.val) =
      μ.map (conjugationOrbitMap g H M hM) := by
  let F := conjugationOrbitMap g H M hM
  have hF : Measurable F := (continuous_conjugationOrbitMap g H M hM).measurable
  calc
    _ = μ.map (slMatrixConjugation h.val ∘ F) :=
      Measure.map_map (continuous_slMatrixConjugation h.val).measurable hF
    _ = μ.map (F ∘ fun x => latticeOrbitRightAction g H x h) := by
      congr 1
      funext x
      exact (conjugationOrbitMap_rightAction g H M hM x h).symm
    _ = (μ.map (fun x => latticeOrbitRightAction g H x h)).map F :=
      (Measure.map_map hF (continuous_latticeOrbitRightAction g H h).measurable).symm
    _ = μ.map F := by rw [hinv h]

end DukePrimeDegree

end

end OAI
