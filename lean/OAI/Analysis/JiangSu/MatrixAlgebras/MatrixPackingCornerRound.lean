import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.PackingRounds
import OAI.Analysis.JiangSu.Comparison.PrecisePackingRound

namespace OAI

noncomputable section
namespace DirectPacking
open CurrentMain
open scoped ComplexOrder

variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

lemma exists_packing_step_with_corner {I : Type*} [Fintype I] {q z : D} (U : ProjectionRow I q)
    (hcoef : CoefficientSupply (D := D)) (hinsert : InsertionSupply (D := D))
    (hz : IsStarProjection z) (K : Finset (unitary D)) {c η ε : ℝ}
    (hc : c ∈ Set.Icc 0 1) (hη : η < 1) (hε : 0 < ε)
    (happrox : ∀ x ∈ K, ∃ H : Matrix I I ℂ,
      ‖U.sample q * (x : D) * U.sample q - U.matrix q H‖ < η) :
    ∃ y t : D, IsStarProjection y ∧ IsStarProjection t ∧ t ≤ 1 - z ∧
      PackingStepBounds (U.sample q) z y t c η ε K ∧
      ∃ e : D, IsStarProjection e ∧ e ≤ q ∧ y=U.sample e := by
  obtain ⟨e, he, heq, hs⟩ := DirectPacking.sample_mass_overlap U hcoef z hc hε
  let y := U.sample e
  have hy : IsStarProjection y := U.sample_projection he
    ((he.le_iff_mul_eq_right U.projection).mp heq)
  obtain ⟨t, ht, htz, hmove⟩ := hinsert z y hz hy
  have hm (τ : RestrictedTracialState D) :
      |(τ.functional y).re - c * (τ.functional (U.sample q)).re| ≤ ε :=
    re_difference_le_of_complex (hs τ).1.le
  refine ⟨y, t, hy, ht, htz, {
    mass := hm
    overlap := fun τ => re_difference_le_of_complex (hs τ).2.le
    inserted_mass_lower := ?_
    inserted_mass_upper := fun τ => (hmove τ).1.2
    inserted_distance := ?_
    inserted_linear := fun τ => (hmove τ).2.2
    sampled_linear := ?_
    sampled_energy := ?_ },e,he,heq,rfl⟩
  · intro τ
    simpa only [τ.tracial y z] using (hmove τ).1.1
  · intro τ
    simpa only [τ.tracial y z] using (hmove τ).2.1
  · intro x hx τ
    have hb := (U.matrix_block_sampling he heq x hη hc.1 (happrox x hx) τ).1
    exact hb.trans (by dsimp [y] at hm ⊢; linarith [hm τ])
  · intro x hx τ
    have hb := (U.matrix_block_sampling he heq x hη hc.1 (happrox x hx) τ).2
    have hb' := (abs_le.mp hb).2
    dsimp [y] at hm ⊢
    linarith [hm τ]

lemma exists_precise_corner_round (hcoef : CoefficientSupply (D := D)) (hinsert : InsertionSupply (D := D))
    {z₀ r : D} (hz₀ : IsStarProjection z₀) (F : WeightedBlockFamily r)
    (K : Finset (unitary D)) {η σ δ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hση : σ ≤ η) (hδ : 0 < δ)
    (happrox : ∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
      ‖F.range j*(x : D)*F.range j-(F.row j).matrix (F.base j) H‖ < σ) :
    ∃ R : SampledPackingRound F z₀ K η δ, ∀ a,
      PackingStepBounds (F.range a.1) (R.occupied a) (R.sampled a) (R.inserted a)
        (η*F.weight a.1/2) σ δ K ∧
      ∃ e : D, IsStarProjection e ∧ e ≤ F.base a.1 ∧ R.sampled a=(F.row a.1).sample e := by
  classical
  let e := Fintype.equivFin (F.Index × Bool)
  let Q := fun (a : Fin (Fintype.card (F.Index × Bool))) (z y t : D) =>
    (PackingStepBounds (F.range (e.symm a).1) z y t (η*F.weight (e.symm a).1/2) σ δ K ∧
      ∃ b : D, IsStarProjection b ∧ b ≤ F.base (e.symm a).1 ∧ y=(F.row (e.symm a).1).sample b)
  have hc (a : F.Index × Bool) : η*F.weight a.1/2 ∈ Set.Icc (0 : ℝ) 1 := by
    have hw := F.weight_le_one a.1
    have hw0 := F.weight_pos a.1
    constructor
    · positivity
    · nlinarith
  have hstep (a : Fin (Fintype.card (F.Index × Bool))) (z : D) (hz : IsStarProjection z) :
      ∃ y t, IsStarProjection y ∧ IsStarProjection t ∧ t ≤ 1-z ∧ Q a z y t :=
    exists_packing_step_with_corner (F.row (e.symm a).1) hcoef hinsert hz K (hc _) (hση.trans_lt hη1) hδ (happrox _)
  obtain ⟨S,hS⟩ := exists_projection_insertion _ hz₀ Q hstep
  let R : SampledPackingRound F z₀ K η δ := {
    final := S.occupied (Fin.last _)
    occupied := fun a => S.occupied (e a).castSucc
    sampled := fun a => S.sampled (e a)
    inserted := fun a => S.inserted (e a)
    final_projection := S.occupied_projection _
    occupied_projection := fun a => S.occupied_projection _
    sampled_projection := fun a => S.sampled_projection _
    inserted_projection := fun a => S.inserted_projection _
    occupied_le_final := fun a => S.monotone (Fin.le_last _)
    inserted_orthogonal := fun a b hab => S.orthogonal (e.injective.ne hab)
    initial_orthogonal := fun a => S.initial_orthogonal _
    final_eq := by rw [e.sum_comp S.inserted]; exact S.final_eq
    bounds := by
      intro a
      have h : PackingStepBounds (F.range a.1) (S.occupied (e a).castSucc)
          (S.sampled (e a)) (S.inserted (e a)) (η*F.weight a.1/2) σ δ K := by
        simpa only [Q,Equiv.symm_apply_apply] using (hS (e a)).1
      exact h.mono_quality (F.range_projection a.1) (S.sampled_projection _) (hc a).1 hση }
  refine ⟨R,?_⟩
  intro a
  constructor
  · simpa only [Q,Equiv.symm_apply_apply] using (hS (e a)).1
  · obtain ⟨b,hb,hbf,hby⟩ := (hS (e a)).2
    refine ⟨b,hb,?_,?_⟩
    · simpa only [Equiv.symm_apply_apply] using hbf
    · exact hby.trans (congrArg (fun c : F.Index × Bool => (F.row c.1).sample b) (e.symm_apply_apply a))

end DirectPacking

end

noncomputable section
open scoped ComplexOrder

namespace DirectPacking
open Pureness CurrentMain

variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

structure MatrixPackingCertificate (z : D) (m : ℕ) where
  Index : Type
  fintype : Fintype Index
  piece : Index → D
  projection : ∀ i, IsStarProjection (piece i)
  orthogonal : Pairwise (fun i j => piece i*piece j=0)
  sum_eq : ∑ i,piece i=z
  hom : Index → (CStarMatrix (Fin m) (Fin m) ℂ →⋆ₙₐ[ℂ] D)

attribute [instance] MatrixPackingCertificate.fintype
namespace MatrixPackingCertificate
variable {z : D} {m : ℕ} (C : MatrixPackingCertificate z m)

def gap (τ : TracialState D) : ℝ := ∑ i,traceTwoNorm τ (C.piece i-C.hom i 1)^2
def energy (τ : TracialState D) (x : D) (P : CStarMatrix (Fin m) (Fin m) ℂ) : ℝ :=
  ∑ i,traceTwoNorm τ (x*C.hom i P-C.hom i P*x)^2

lemma piece_le (i : C.Index) : C.piece i≤z := by
  exact (Finset.single_le_sum (fun j _ => (C.projection j).nonneg) (Finset.mem_univ i)).trans_eq C.sum_eq

def zero (m : ℕ) : MatrixPackingCertificate (0:D) m where
  Index := Empty
  fintype := inferInstance
  piece := Empty.elim
  projection := by intro i; cases i
  orthogonal := by intro i; cases i
  sum_eq := by simp
  hom := Empty.elim

def rebase {w : D} (h : z=w) : MatrixPackingCertificate w m :=
  { C with sum_eq := C.sum_eq.trans h }

variable [TraceFamily D]
def append {r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}
    (hz : IsStarProjection z) (R : SampledPackingRound F z K η δ)
    (φ : F.Index × Bool → (CStarMatrix (Fin m) (Fin m) ℂ →⋆ₙₐ[ℂ] D)) :
    MatrixPackingCertificate R.final m where
  Index := C.Index ⊕ (F.Index × Bool)
  fintype := inferInstance
  piece := Sum.elim C.piece R.inserted
  projection := by intro i; cases i with
    | inl i => exact C.projection i
    | inr i => exact R.inserted_projection i
  orthogonal := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact C.orthogonal (fun h => hij (congrArg Sum.inl h))
      | inr j =>
        change C.piece i*R.inserted j=0
        calc
          C.piece i*R.inserted j=(C.piece i*z)*R.inserted j := by rw [((C.projection i).le_iff_mul_eq_left hz).mp (C.piece_le i)]
          _=0 := by rw [mul_assoc,R.initial_orthogonal,mul_zero]
    | inr i =>
      cases j with
      | inl j =>
        change R.inserted i*C.piece j=0
        have h : C.piece j*R.inserted i=0 := by
          calc
            C.piece j*R.inserted i=(C.piece j*z)*R.inserted i := by rw [((C.projection j).le_iff_mul_eq_left hz).mp (C.piece_le j)]
            _=0 := by rw [mul_assoc,R.initial_orthogonal,mul_zero]
        simpa only [star_mul,(C.projection j).isSelfAdjoint.star_eq,(R.inserted_projection i).isSelfAdjoint.star_eq,star_zero] using congrArg star h
      | inr j => exact R.inserted_orthogonal (fun h => hij (congrArg Sum.inr h))
  sum_eq := by rw [Fintype.sum_sum_type]; exact (congrArg (·+∑ a,R.inserted a) C.sum_eq).trans R.final_eq.symm
  hom := Sum.elim C.hom φ

lemma append_gap {r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}
    (hz : IsStarProjection z) (R : SampledPackingRound F z K η δ)
    (φ : F.Index × Bool → (CStarMatrix (Fin m) (Fin m) ℂ →⋆ₙₐ[ℂ] D)) (τ : TracialState D) :
    (C.append hz R φ).gap τ=C.gap τ+∑ a,traceTwoNorm τ (R.inserted a-φ a 1)^2 := by
  change (∑ i : C.Index ⊕ (F.Index × Bool),traceTwoNorm τ (Sum.elim C.piece R.inserted i-Sum.elim C.hom φ i 1)^2)=_
  rw [Fintype.sum_sum_type]
  rfl

lemma append_energy {r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}
    (hz : IsStarProjection z) (R : SampledPackingRound F z K η δ)
    (φ : F.Index × Bool → (CStarMatrix (Fin m) (Fin m) ℂ →⋆ₙₐ[ℂ] D)) (τ : TracialState D) (x : D) (P : CStarMatrix (Fin m) (Fin m) ℂ) :
    (C.append hz R φ).energy τ x P=C.energy τ x P+∑ a,traceTwoNorm τ (x*φ a P-φ a P*x)^2 := by
  change (∑ i : C.Index ⊕ (F.Index × Bool),traceTwoNorm τ (x*Sum.elim C.hom φ i P-Sum.elim C.hom φ i P*x)^2)=_
  rw [Fintype.sum_sum_type]
  rfl

end MatrixPackingCertificate
end DirectPacking

end

end OAI
