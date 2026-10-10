import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityLabelArray
import OAI.Probability.Perceptron.Cavity.CavityResidualFormula
import OAI.Probability.Perceptron.Cascade.CascadeTransport

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal

def cavityGaussianMark (n d : ℕ) (y : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) : CavityRPCMark n d :=
  (fun i=>y (Sum.inl i),fun i=>y (Sum.inr i))

def cavityGaussianState (n d : ℕ) (x : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) : CavityRPCState n d :=
  (fun i j=>x j (Sum.inl i),fun i j=>x j (Sum.inr i))

lemma cavityGaussianMark_preserving (n d : ℕ) :
    MeasurePreserving (cavityGaussianMark n d)
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) (cavityRPCMarkLaw n d : Measure (CavityRPCMark n d)) := by
  have hp : MeasurePreserving (fun p : Spin (n+1)×Spin d=>(WithLp.ofLp p.1,WithLp.ofLp p.2))
      ((stdGaussian (Spin (n+1))).prod (stdGaussian (Spin d)))
      ((Measure.pi fun _ : Fin (n+1)=>gaussianReal 0 1).prod (Measure.pi fun _ : Fin d=>gaussianReal 0 1)) :=
    (stdGaussian_ofLp_preserving (n+1)).prod (stdGaussian_ofLp_preserving d)
  exact hp.comp (gaussianSumSplit_preserving (I:=Fin (n+1)) (J:=Fin d))

lemma cavityGaussianState_measurable (n d : ℕ) : Measurable (cavityGaussianState n d) := by
  unfold cavityGaussianState
  apply Measurable.prodMk <;> apply Measurable.of_eval <;> intro i <;> apply Measurable.of_eval <;> intro j
  · exact (measurable_pi_apply (Sum.inl i)).comp ((MeasurableEquiv.toLp 2 _).symm.measurable.comp (measurable_pi_apply j))
  · exact (measurable_pi_apply (Sum.inr i)).comp ((MeasurableEquiv.toLp 2 _).symm.measurable.comp (measurable_pi_apply j))

lemma cavityGaussianState_step (n d : ℕ) (σ τ : ℕ→ℝ) (x : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d))
    (y : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    cavityGaussianState n d (gaussianLinearMarkStep (fun j=>diagonalMark (Sum.elim (fun _=>σ j) (fun _=>τ j))) (x,y))=
      cavityRPCStep n d σ τ (cavityGaussianState n d x,cavityGaussianMark n d y) := by
  rfl

lemma cavityRPC_fractional (n d k : ℕ) (σ τ : ℕ→ℝ) (F : ℝ→ᵇℝ)
    (z : Fin k→ℝ) (hz0 : ∀ i,0<z i) :
    finiteCascadeFractionalIntegrable (cavityRPCMarkLaw n d) (cavityRPCStep n d σ τ)
      (cavityRPCTerminal n d F) k z := by
  have hF : Measurable (fun a : ℕ→ℝ=>F (a 0)) := F.measurable.comp (measurable_pi_apply 0)
  have hFI := finiteCascadeFractionalIntegrable_of_bounded standardGaussianMark
    (gaussianShiftStep τ) (gaussianShiftStep_measurable τ) k z hz0 hF
    (fun a=>F.norm_coe_le_norm (a 0))
  have hs := finiteCascade_sum_pi (fun _ : Fin d=>standardGaussianMark)
    (fun _=>gaussianShiftStep τ) k z (fun _ a=>F (a 0)) (fun _=>hFI)
  have hv := coordinateRecursion_eq_backward (n+1) σ
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) k z hz0
  exact finiteCascadeFractionalIntegrable_add_product
    (piMarkLaw (fun _ : Fin (n+1)=>standardGaussianMark))
    (piMarkLaw (fun _ : Fin d=>standardGaussianMark))
    (canonicalCoordinateStep (n+1) σ) (canonicalCoordinateStep d τ) k z hz0 hv.2 hs.2

lemma cavityGaussian_fractional (n d k : ℕ) (σ τ : ℕ→ℝ) (F : ℝ→ᵇℝ)
    (z : Fin k→ℝ) (hz0 : ∀ i,0<z i) :
    finiteCascadeFractionalIntegrable (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
      (gaussianLinearMarkStep (fun j=>diagonalMark (Sum.elim (fun _=>σ j) (fun _=>τ j))))
      (cavityRPCTerminal n d F ∘ cavityGaussianState n d) k z :=
  finiteCascadeFractionalIntegrable_transport
    (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) (cavityRPCMarkLaw n d) _ _
    (cavityRPCStep_measurable n d σ τ)
    (cavityGaussianState n d) (cavityGaussianMark n d) (cavityGaussianMark_preserving n d)
    (cavityGaussianState_step n d σ τ) _ (cavityRPCTerminal_measurable n d F) k z
    (cavityRPC_fractional n d k σ τ F z hz0)

lemma cavityPairProfile_root (n d : ℕ) {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K) :
    profileGaussianRoot (cavityPairProfile n d p)=
      Sum.elim (fun _=>Real.sqrt (p 0).2.val) (fun _=>Real.sqrt (p 0).1.val) := by
  funext i; cases i <;> rfl

lemma cavityPairProfile_step (n d : ℕ) {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K) (j : ℕ) :
    profileGaussianStep (cavityPairProfile n d p) j=
      Sum.elim (fun _=>stepFieldIncrement k (fun l=>(p l).2.val/2) j)
        (fun _=>profileGaussianStep (fun l (_ : Fin 1)=>(p l).1.val) j 0) := by
  funext i
  cases i with
  | inl _index =>
    unfold profileGaussianStep stepFieldIncrement
    split_ifs with hj
    · have h₁ : (⟨k-j,by omega⟩ : Fin (k+1))=(Fin.rev (⟨j,hj⟩ : Fin k)).succ := by
        ext; simp only [Fin.val_rev,Fin.val_succ]; omega
      have h₂ : (⟨k-j-1,by omega⟩ : Fin (k+1))=(Fin.rev (⟨j,hj⟩ : Fin k)).castSucc := by
        ext; simp only [Fin.val_rev,Fin.val_castSucc]; omega
      simp only [cavityPairProfile,Sum.elim_inl,h₁,h₂]
      congr 1; ring
    · rfl
  | inr _index =>
    unfold profileGaussianStep
    split_ifs <;> rfl

lemma cavityGaussianState_root (n d : ℕ) {K : ℝ} {k : ℕ} (p : Fin (k+1)→BulkPairRange K)
    (y : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    cavityGaussianState n d (fun _=>diagonalMark (profileGaussianRoot (cavityPairProfile n d p)) y)=
      cavityRPCRootState n d (Real.sqrt (p 0).2.val) (Real.sqrt (p 0).1.val) (cavityGaussianMark n d y) := by
  rfl

lemma cavityPair_residual_formula (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (f : ℝ→ᵇℝ) (a s : ℝ≥0)
    (ha : (a:ℝ)=D.2.val-(p (Fin.last k)).2.val)
    (hs : (s:ℝ)=D.1.val-(p (Fin.last k)).1.val)
    (v : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    (∫ y,cavityFullSingle n d f (WithLp.toLp 2 (fun i=>v i+
      Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)*y i))
      ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))=
      Real.exp ((n+1:ℕ)*a/2+logSphericalExp n (Real.sqrt (n+1:ℕ)) (gaussianSumSplit v).1+
        ∑ i,heatLog s 1 f (v (Sum.inr i))) := by
  have he : (fun i=>Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i))=
      Sum.elim (fun _=>Real.sqrt a) (fun _=>Real.sqrt s) := by
    funext i; cases i <;> simp only [cavityPairDiagonal,cavityPairProfile,Sum.elim_inl,Sum.elim_inr,ha,hs]
  simp_rw [show ∀ i,Real.sqrt (cavityPairDiagonal n d D i-cavityPairProfile n d p (Fin.last k) i)=
    Sum.elim (fun _=>Real.sqrt a) (fun _=>Real.sqrt s) i from congrFun he]
  exact cavity_full_residual n d f a s v

lemma cavityGaussian_terminal (n d : ℕ) (f : ℝ→ᵇℝ) (a s : ℝ≥0)
    (x : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d)) :
    (n+1:ℕ)*a/2+logSphericalExp n (Real.sqrt (n+1:ℕ)) (gaussianSumSplit (x 0)).1+
      ∑ i,heatLog s 1 f (x 0 (Sum.inr i)) =
    (n+1:ℕ)*a/2+(cavityRPCTerminal n d (heatLogBCF s 1 f) ∘ cavityGaussianState n d) x := by
  change _=_+(_+_)
  exact add_assoc _ _ _

end SphericalPerceptronFreeEnergy
end

end OAI
