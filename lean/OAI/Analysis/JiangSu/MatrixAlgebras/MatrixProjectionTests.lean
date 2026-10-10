import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixSmallPacking
import OAI.Analysis.JiangSu.CentralSequences.MatrixCompressionCentrality

namespace OAI

noncomputable section
namespace ConcreteMatrixUnits
open Pureness CurrentMain
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma projection_tests_control_entries (L : CStarMatrix ι ι ℂ →ₗ[ℂ] D)
    (τ : TracialState D) {B : ℝ} (hB : 0≤B)
    (hb : ∀ P : CStarMatrix ι ι ℂ,IsStarProjection P →
      Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm P)=1 → traceTwoNorm τ (L P)≤B)
    (i j : ι) : traceTwoNorm τ (L (unit i j))≤2*B := by
  by_cases hij : i=j
  · subst j
    exact (hb _ (unit_projection i) (by simp [unit_trace])).trans (by linarith)
  have hp {z : ℂ} (hz : star z*z=1) : traceTwoNorm τ (L (pairProjection i j z))≤B :=
    hb _ (pairProjection_projection hij hz) (pairProjection_trace hij z)
  have h1 := hp (z:=1) (by simp)
  have hn1 := hp (z:=(-1)) (by simp)
  have hi := hp (z:=Complex.I) (by simp)
  have hni := hp (z:=(-Complex.I)) (by simp)
  have hsub1 := (traceTwoNorm_sub_le τ (L (pairProjection i j 1)) (L (pairProjection i j (-1)))).trans (add_le_add h1 hn1)
  have hsubi := (traceTwoNorm_sub_le τ (L (pairProjection i j Complex.I)) (L (pairProjection i j (-Complex.I)))).trans (add_le_add hi hni)
  rw [pairProjection_recovers i j,map_add,map_smul,map_smul,map_sub,map_sub]
  apply (traceTwoNorm_add_le τ _ _).trans
  simp only [traceTwoNorm_smul,norm_div,norm_neg,Complex.norm_I,Complex.norm_ofNat,norm_one]
  nlinarith

end ConcreteMatrixUnits

namespace DirectPacking
open CurrentMain Pureness
open scoped ComplexOrder

variable {A D : Type} [CStarAlgebra A] [CStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

structure TracialMatrixModel {S : Type*} (T : S → TracialState D)
    (ι : A →⋆ₐ[ℂ] D) (m : ℕ) (K : Finset (unitary A)) (ε : ℝ) where
  entry : Fin m → Fin m → D
  norm_entry : ∀ i j,‖entry i j‖≤1
  star_error : ∀ i j,familyTwoNorm T (star (entry i j)-entry j i)<ε
  mul_error : ∀ i j k l,familyTwoNorm T (entry i j*entry k l-if j=k then entry i l else 0)<ε
  unit_error : familyTwoNorm T ((∑ i,entry i i)-1)<ε
  comm_error : ∀ i j,∀ u∈K,familyTwoNorm T (entry i j*ι (u:A)-ι (u:A)*entry i j)<ε

end DirectPacking

namespace DirectPacking
open CurrentMain Pureness DirectComparison ConcreteMatrixUnits
open scoped ComplexOrder

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

namespace MatrixPackingCertificate
variable {z : D} {m : ℕ} (C : MatrixPackingCertificate z m)
def compressLinear : CStarMatrix (Fin m) (Fin m) ℂ →ₗ[ℂ] D where
  toFun := C.compress
  map_add' := C.compress_add
  map_smul' := C.compress_smul

omit [TraceFamily D] in
lemma compress_zero : C.compress 0=0 := C.compressLinear.map_zero
omit [TraceFamily D] in
lemma compress_sum_diag : (∑ i,C.compress (unit i i))=C.compress 1 := by
  change (∑ i,C.compressLinear (unit i i))=C.compressLinear 1
  rw [←map_sum,unit_sum_diag]

def commutatorLinear (x : D) : CStarMatrix (Fin m) (Fin m) ℂ →ₗ[ℂ] D where
  toFun := fun M => x*C.compress M-C.compress M*x
  map_add' := by intro M N; rw [C.compress_add]; noncomm_ring
  map_smul' := by intro c M; rw [C.compress_smul]; simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

lemma entry_commutator_bound (hinsert : InsertionSupply (D := D))
    {x : D} (hx : ‖x‖≤1) (τ : RestrictedTracialState D) {δ : ℝ} (hδ : 0≤δ)
    (hgap : C.gap τ≤δ)
    (henergy : ∀ P : CStarMatrix (Fin m) (Fin m) ℂ,IsStarProjection P →
      Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm P)=1 → C.energy τ x P≤δ)
    (i j : Fin m) : traceTwoNorm τ (x*C.compress (unit i j)-C.compress (unit i j)*x)≤2*Real.sqrt (124*δ) := by
  apply projection_tests_control_entries (C.commutatorLinear x) τ (Real.sqrt_nonneg _) ?_ i j
  intro P hP htr
  have he := C.compress_projection_energy hinsert hP hx τ
  have hb := henergy P hP htr
  change traceTwoNorm (τ : TracialState D) (x*C.compress P-C.compress P*x)≤Real.sqrt (124*δ)
  apply (Real.le_sqrt (traceTwoNorm_nonneg (τ : TracialState D) _) (by positivity)).mpr
  linarith

omit [TraceFamily D] in
lemma compress_unit_bound (hz : IsStarProjection z) (τ : TracialState D) :
    traceTwoNorm τ (C.compress 1-1)^2≤2*C.gap τ+2*(τ.functional (1-z)).re := by
  have he : C.compress 1-1=(C.compress 1-z)+(-(1-z)) := by abel
  rw [he]
  have h := BistochasticTest.square_add_le τ (C.compress 1-z) (-(1-z))
  rw [traceTwoNorm_neg,traceTwoNorm_projection_sq τ hz.one_sub] at h
  linarith [C.compress_unit_gap τ]
end MatrixPackingCertificate

lemma matrix_models_from_packing
    (hA : IsNuclear A) (ι : A →⋆ₐ[ℂ] D)
    (hsupply : SpectralProjectionSupply (fun τ : RestrictedTracialState D => (τ : TracialState D)))
    [Nonempty (RestrictedTracialState D)] (hcoef : CoefficientSupply (D := D))
    (hinsert : InsertionSupply (D := D)) {m : ℕ} (hm : 0 < m)
    (hmat : ∀ e : D,IsStarProjection e → ∃ p : D,∃ V : ProjectionRow (Fin m) p,V.sample p=e)
    (K : Finset (unitary A)) {ε : ℝ} (hε : 0<ε) :
    Nonempty (TracialMatrixModel (fun τ : RestrictedTracialState D => (τ : TracialState D)) ι m K ε) := by
  let δ := ε^2/2048
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hT : Nonempty (TracialState D) := ⟨(Classical.ofNonempty : RestrictedTracialState D).val⟩
  obtain ⟨z,hz,C,hrem,hgap,henergy⟩ := exists_small_matrix_packing hA ι hsupply hT hcoef hinsert hm hmat K hδ
  have hs : Real.sqrt δ<ε := by
    apply (Real.sqrt_lt' hε).mpr
    dsimp [δ]; nlinarith [sq_pos_of_pos hε]
  have hu : Real.sqrt (4*δ)<ε := by
    apply (Real.sqrt_lt' hε).mpr
    dsimp [δ]; nlinarith [sq_pos_of_pos hε]
  have hc : 2*Real.sqrt (124*δ)<ε := by
    have hh : Real.sqrt (124*δ)<ε/2 := by
      apply (Real.sqrt_lt' (by positivity : 0<ε/2)).mpr
      dsimp [δ]; nlinarith [sq_pos_of_pos hε]
    linarith
  refine ⟨{
    entry := fun i j => C.compress (unit i j)
    norm_entry := fun i j => C.compress_norm_le_one hz (unit_norm_le_one i j)
    star_error := ?_
    mul_error := ?_
    unit_error := ?_
    comm_error := ?_}⟩
  · intro i j
    rw [←C.compress_star,unit_star,sub_self,familyTwoNorm_zero]
    exact hε
  · intro i j k l
    have he : (if j=k then C.compress (unit i l) else 0)=C.compress (unit i j*unit k l) := by
      rw [unit_mul]; split_ifs <;> simp only [C.compress_zero]
    rw [he]
    apply lt_of_le_of_lt ?_ hs
    apply ciSup_le
    intro τ
    rw [traceTwoNorm_sub_swap]
    apply (Real.le_sqrt (traceTwoNorm_nonneg (τ : TracialState D) _) hδ.le).mpr
    exact (C.compress_mul_gap τ (unit_norm_le_one i j) (unit_norm_le_one k l)).trans (hgap τ).le
  · rw [C.compress_sum_diag]
    apply lt_of_le_of_lt ?_ hu
    apply ciSup_le
    intro τ
    apply (Real.le_sqrt (traceTwoNorm_nonneg (τ : TracialState D) _) (by positivity)).mpr
    have hh := C.compress_unit_bound hz τ
    have h1 := hgap τ
    have h2 := hrem τ
    linarith
  · intro i j u hku
    apply lt_of_le_of_lt ?_ hc
    apply ciSup_le
    intro τ
    rw [traceTwoNorm_sub_swap]
    have hnu : ‖ι (u:A)‖≤1 := by
      have hh := CStarRing.norm_coe_unitary_mul (mapUnitary ι u) (1:D)
      rw [mul_one] at hh
      exact hh.le.trans (IsStarProjection.one D).norm_le
    exact C.entry_commutator_bound hinsert hnu τ hδ.le (hgap τ).le
      (fun P hP htr => (henergy P hP htr u hku τ).le) i j

end DirectPacking

end

end OAI
