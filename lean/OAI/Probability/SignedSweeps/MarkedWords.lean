import OAI.Probability.SignedSweeps.SignedPair
import OAI.Probability.SignedSweeps.Imprimitivity
import OAI.Probability.SignedSweeps.HilbertFibers

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def markedTargetTransport {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) : SymmetricGroup p := (markedSpinTransport h g⁻¹ z)⁻¹

@[simp] lemma markedTargetTransport_one {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) : markedTargetTransport h 1 z = 1 := by
  simp [markedTargetTransport]

lemma markedTargetTransport_mul {p l n : ℕ} (h : p+l=n) (g t : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedTargetTransport h (g*t) z = markedTargetTransport h g z *
      markedTargetTransport h t (moveMarks g⁻¹ z) := by
  simp only [markedTargetTransport, mul_inv_rev, markedSpinTransport_mul]

lemma markedTargetTransport_at {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedTargetTransport h g (moveMarks g z) = markedSpinTransport h g z := by
  have he := markedSpinTransport_mul h g⁻¹ g z
  rw [inv_mul_cancel, markedSpinTransport_one] at he
  exact inv_eq_of_mul_eq_one_right he.symm

abbrev MarkedWordSpace (p l n : ℕ) (C : Type*) [Fintype C] :=
  HilbertFibers (MarkedAssignment l n) (WordSpace p (C ⊕ C))

def markedWordLinear {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) :
    MarkedWordSpace p l n C →ₗ[ℂ] MarkedWordSpace p l n C where
  toFun f := WithLp.toLp 2 (fun z =>
    signedWordRepresentation p C (markedTargetTransport h g z) (f.ofLp (moveMarks g⁻¹ z)))
  map_add' f k := by apply PiLp.ext; intro z; exact map_add _ _ _
  map_smul' c f := by apply PiLp.ext; intro z; exact map_smul (signedWordRepresentation p C (markedTargetTransport h g z)) c _

@[simp] lemma markedWordLinear_apply {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (f : MarkedWordSpace p l n C)
    (z : MarkedAssignment l n) :
    (markedWordLinear h g f).ofLp z =
      signedWordRepresentation p C (markedTargetTransport h g z) (f.ofLp (moveMarks g⁻¹ z)) := rfl

def markedWordRepresentation {p l n : ℕ} (h : p+l=n) (C : Type*) [Fintype C] :
    Representation ℂ (SymmetricGroup n) (MarkedWordSpace p l n C) where
  toFun := markedWordLinear h
  map_one' := by
    apply LinearMap.ext
    intro f
    apply PiLp.ext
    intro z
    simp only [markedWordLinear_apply, inv_one, moveMarks_one, markedTargetTransport_one,
      map_one, Module.End.one_apply]
  map_mul' g t := by
    apply LinearMap.ext
    intro f
    apply PiLp.ext
    intro z
    simp only [Module.End.mul_apply, markedWordLinear_apply, markedTargetTransport_mul,
      map_mul, mul_inv_rev, moveMarks_mul]

@[simp] lemma markedWordRepresentation_apply {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (f : MarkedWordSpace p l n C)
    (z : MarkedAssignment l n) :
    (markedWordRepresentation h C g f).ofLp z =
      signedWordRepresentation p C (markedTargetTransport h g z) (f.ofLp (moveMarks g⁻¹ z)) := rfl

lemma markedWordRepresentation_norm {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (f : MarkedWordSpace p l n C) :
    ‖markedWordRepresentation h C g f‖ = ‖f‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  simp only [markedWordRepresentation_apply, signedWordRepresentation_norm]
  exact Equiv.sum_comp (moveMarksEquiv g⁻¹) (fun z => ‖f.ofLp z‖^2)

lemma markedWordRepresentation_insertion {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (z : MarkedAssignment l n)
    (x : WordSpace p (C ⊕ C)) :
    markedWordRepresentation h C g (fiberInsertion z x) =
      fiberInsertion (moveMarks g z) (signedWordRepresentation p C (markedSpinTransport h g z) x) := by
  apply PiLp.ext
  intro w
  simp only [markedWordRepresentation_apply, fiberInsertion_apply]
  by_cases hw : w = moveMarks g z
  · subst w
    rw [← moveMarks_mul, inv_mul_cancel, moveMarks_one, markedTargetTransport_at]
    simp
  · have hn : moveMarks g⁻¹ w ≠ z := by
      intro he
      apply hw
      rw [← he, ← moveMarks_mul, mul_inv_cancel, moveMarks_one]
    rw [ite_eq_right hn, ite_eq_right hw, map_zero]

def markedTypeProjection {u v p l n : ℕ} (hu : u+v=p) (_h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    MarkedWordSpace p l n C →ₗ[ℂ] MarkedWordSpace p l n C :=
  fiberDiagonal (fun _ => pairTypeProjection hu a b C)

lemma markedTypeProjection_positive {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    (markedTypeProjection hu h a b C).IsPositive :=
  fiberDiagonal_positive _ (fun _ => pairTypeProjection_positive hu a b C)

lemma markedTypeProjection_idempotent {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    markedTypeProjection hu h a b C * markedTypeProjection hu h a b C =
      markedTypeProjection hu h a b C :=
  fiberDiagonal_idempotent _ (fun _ => pairTypeProjection_idempotent hu a b C)

lemma markedTypeProjection_commute {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] (g : SymmetricGroup n) :
    markedWordRepresentation h C g * markedTypeProjection hu h a b C =
      markedTypeProjection hu h a b C * markedWordRepresentation h C g := by
  apply LinearMap.ext
  intro f
  apply PiLp.ext
  intro z
  exact LinearMap.congr_fun (pairTypeProjection_signed_commute hu a b (markedTargetTransport h g z)).symm
    (f.ofLp (moveMarks g⁻¹ z))

def markedTypeSubrepresentation {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    Subrepresentation (markedWordRepresentation h C) :=
  projectionSubrepresentation (markedWordRepresentation h C) (markedTypeProjection hu h a b C)
    (markedTypeProjection_commute hu h a b C)

lemma markedWordRepresentation_pointwise {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (z : MarkedAssignment l n) (g : SymmetricGroup p)
    (x : WordSpace p (C ⊕ C)) :
    markedWordRepresentation h C (g.viaEmbedding (markedInjection h z)) (fiberInsertion z x) =
      fiberInsertion z (signedWordRepresentation p C g x) := by
  rw [markedWordRepresentation_insertion, moveMarks_viaEmbedding, markedSpinTransport_viaEmbedding]

end SignedSweeps
end

end OAI
