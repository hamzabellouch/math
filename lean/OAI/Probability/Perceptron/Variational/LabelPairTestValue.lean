import Mathlib
import OAI.Probability.Perceptron.Variational.LabelProfileReferenceFull
import OAI.Probability.Perceptron.Cavity.BulkMarkedMoments
import OAI.Probability.Perceptron.Interpolation.RestorationReplicaBlocks
import OAI.Probability.Perceptron.Variational.LabelRestorationMoments2
import OAI.Probability.Perceptron.Variational.LabelRestoredValue

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def labelProfilePairTest {k : ℕ} (q : Fin (k+1)→Time) (F : CompactOverlap →ᵇ ℝ) :
    CompactBlock CompactJointOverlap 2 →ᵇ ℝ :=
  F.compContinuous ⟨fun Q => labelProfileSpin q (Q 1 0).2,
    (labelProfileSpin_continuous q).comp (by fun_prop)⟩

lemma labelProfilePairTest_source (N k : ℕ) (q : Fin (k+1)→Time) (F : CompactOverlap →ᵇ ℝ)
    (x : Fin 2→NormalizedSpin N×IndexedLeaf k) :
    labelProfilePairTest q F (fun i j => sourceJointOverlap (x i) (x j))=
      F (timeSpin (q (indexedCommonDepth k (x 0).2 (x 1).2))) := by
  change F (labelProfileSpin q (sourceLabelLevel k (indexedCommonDepth k (x 0).2 (x 1).2)))=_
  rw [labelProfileSpin_node]

lemma sourceLabelRestorationRatio_pair_value (n k : ℕ) (f : ℝ →ᵇ ℝ) (g : Jet3)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (hh0 : ∀ i,0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (q : Fin (k+1)→Time) (s : ℝ≥0) (v w : ℝ →ᵇ ℝ)
    (F : CompactOverlap →ᵇ ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1) (t : ℝ≥0) :
    sourceLabelRestorationRatio n k 2 (fun i => (q i:ℝ)) s f g.f (fun _ => v) (fun _ => w)
      (labelProfilePairTest q F) p e h u z t =
      ∑ d, F (timeSpin (q d))*(twoVisitMass k z d).toReal*
        (labelPairCoefficient k z (fun i => (q i:ℝ)) g s v d *
          labelPairCoefficient k z (fun i => (q i:ℝ)) g s w d) := by
  rw [sourceLabelRestorationRatio_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh0 hh]
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  have hae := (measurePreserving_fst (μ:=P) (ν:=countableGaussianLaw.prod countableGaussianLaw)).quasiMeasurePreserving.ae
    (sourceFresh_exp_ae n k f p e h hh0 hh u z t)
  have he : (fun a => labelKernelRestoredRatio (sourceFullSpinLeafKernel n k)
      (sourceCouplingHamiltonian n k f p e h u) (fun i => (q i:ℝ)) s g.f (fun _ : Fin 2 => v) (fun _ => w)
      (fun x => labelProfilePairTest q F (fun i j => sourceJointOverlap (x i) (x j))) a) =ᵐ[P.prod (countableGaussianLaw.prod countableGaussianLaw)]
    (fun a => ∑ d, F (timeSpin (q d))*sourceLabelPairIntegrand n k f p e h u (fun i => (q i:ℝ)) g s d v w a) := by
    filter_upwards [hae] with a ha
    simp only [labelProfilePairTest_source]
    exact labelKernelRestoredRatio_depth k _ _ (sourceCouplingHamiltonian_measurable n k f p e h u)
      _ s g.f v w (fun d => F (timeSpin (q d))) a ha
  rw [integral_congr_ae he,integral_finsetSum _ (fun d _ =>
    (sourceLabelPairIntegrand_integrable n k f p e h hh0 hh u (fun i => (q i:ℝ)) g s d v w z t).const_mul _)]
  simp only [integral_const_mul,sourceLabelPairIntegrand_value n k f p e h hh0 hh u _ g s _ v w z hz hz0 hz1 t,mul_assoc]

def scalarPairMatrixTest (F : CompactOverlap →ᵇ ℝ) : Matrix (Fin 2) (Fin 2) ℝ →ᵇ ℝ :=
  F.compContinuous ⟨fun Q => Set.projIcc (-1) 1 (by norm_num) (Q 1 0),
    by fun_prop⟩

def scalarFrontMatrixTest (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ) :
    (j : ℕ) → Matrix (Fin (r+j)) (Fin (r+j)) ℝ →ᵇ ℝ
  | 0 => F
  | j+1 => (scalarFrontMatrixTest r F j).compContinuous
      ⟨fun Q i l => Q i.succ l.succ,by fun_prop⟩

def scalarRestorationPairMoment (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) (j : ℕ) :
    Matrix (Fin (2+j)) (Fin (2+j)) ℝ →ᵇ ℝ :=
  scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j *
    freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f (fun _ : Fin 2 => v) j)) *
    freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f (fun _ : Fin 2 => w) j))

lemma restorationMarkTest_gaussianMixed {r : ℕ} (f : ℝ →ᵇ ℝ) (v : Fin r → ℝ →ᵇ ℝ) (j : ℕ) :
    restorationMarkTest r f (gaussianMixedTest v) j =
      gaussianMixedTest (labelRestoredFunctions f v j) := by
  induction j with
  | zero =>
    ext x
    simp only [restorationMarkTest,BoundedContinuousFunction.mul_apply,gaussianReplicaTest_apply,
      gaussianMixedTest_apply,labelRestoredFunctions,Finset.prod_mul_distrib]
    rfl
  | succ j hj =>
    ext x
    change (expBCF 1 f) (x 0) * restorationMarkTest r f (gaussianMixedTest v) j
      (WithLp.toLp 2 (fun i => x i.succ)) =
        gaussianMixedTest (Fin.cons (expBCF 1 f) (labelRestoredFunctions f v j)) x
    rw [hj]
    simp only [gaussianMixedTest_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

def compactPairTest (F : CompactOverlap →ᵇ ℝ) : CompactBlock CompactOverlap 2 →ᵇ ℝ :=
  F.compContinuous ⟨fun Q => Q 1 0,by fun_prop⟩

lemma scalarFrontMatrixTest_compact (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ)
    (j : ℕ) (Q : CompactBlock CompactOverlap (r+j)) :
    scalarFrontMatrixTest r F j (fun i l => (Q i l).val) =
      restorationBlockTest r (F.compContinuous ⟨fun Q i l => (Q i l).val,by fun_prop⟩) j Q := by
  induction j with
  | zero => rfl
  | succ j hj => exact hj _

lemma scalarRestorationPairMoment_compact (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ)
    (j : ℕ) (Q : CompactBlock CompactOverlap (2+j)) :
    scalarRestorationPairMoment f v w F j (fun i l => (Q i l).val) =
      (restorationBlockTest 2 (compactPairTest F) j *
        freshMarkedCompactBlockKernel (restorationMarkTest 2 f (gaussianMixedTest (fun _ => v)) j) *
        freshMarkedCompactBlockKernel (restorationMarkTest 2 f (gaussianMixedTest (fun _ => w)) j)) Q := by
  have he : (scalarPairMatrixTest F).compContinuous
      ⟨fun Q : CompactBlock CompactOverlap 2 => fun i l => (Q i l).val,by fun_prop⟩=compactPairTest F := by
    ext Q
    change F (Set.projIcc (-1) 1 (by norm_num : (-1:ℝ)≤1) (Q 1 0).val)=F (Q 1 0)
    rw [Set.projIcc_of_mem _ (Q 1 0).prop]
  change scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j (fun i l => (Q i l).val) *
      freshMarkedMatrixKernel _ (fun i l => (Q i l).val) * freshMarkedMatrixKernel _ (fun i l => (Q i l).val) = _
  rw [scalarFrontMatrixTest_compact,he]
  simp only [BoundedContinuousFunction.mul_apply,restorationMarkTest_gaussianMixed]
  rfl

def labelProfileGram {k r : ℕ} (q : Fin (k+1)→Time) (Q : CompactBlock CompactJointOverlap r) :
    Matrix (Fin r) (Fin r) ℝ := fun i l => if i=l then 1 else (labelProfileSpin q (Q i l).2).val

lemma scalarFrontMatrixTest_label {k : ℕ} (q : Fin (k+1)→Time) (F : CompactOverlap →ᵇ ℝ)
    (j : ℕ) (Q : CompactBlock CompactJointOverlap (2+j)) :
    scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j (labelProfileGram q Q) =
      jointRestorationBlockTest 2 (labelProfilePairTest q F) j Q := by
  induction j with
  | zero =>
    change F (Set.projIcc (-1) 1 (by norm_num : (-1:ℝ)≤1) (if (1 : Fin 2)=0 then 1 else (labelProfileSpin q (Q 1 0).2).val)) = _
    simp only [show (1 : Fin 2) ≠ 0 by decide,ite_false,Set.projIcc_of_mem _ (labelProfileSpin q (Q 1 0).2).prop]
    rfl
  | succ j hj =>
    change scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j (fun i l => labelProfileGram q Q i.succ l.succ) = _
    have he : (fun i l => labelProfileGram q Q i.succ l.succ)=labelProfileGram q (fun i l => Q i.succ l.succ) := by
      funext i l
      simp only [labelProfileGram,Fin.succ_inj]
    exact (congrArg (fun M : Matrix (Fin (2+j)) (Fin (2+j)) ℝ => scalarFrontMatrixTest 2 (scalarPairMatrixTest F) j M) he).trans (hj _)

lemma labelMarkedBlockKernel_profile {k r : ℕ} (q : Fin (k+1)→Time)
    (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (Q : CompactBlock CompactJointOverlap r)
    (hN : ∀ i l,(Q i l).2∈Set.range (sourceLabelLevel k)) :
    labelMarkedBlockKernel (fun i => (q i:ℝ)) Ψ Q = freshMarkedMatrixKernel Ψ (labelProfileGram q Q) := by
  apply congrArg (freshMarkedMatrixKernel Ψ)
  funext i l
  change (if i=l then 1 else labelProfileInterpolant (fun i => (q i:ℝ)) (Q i l).2)=_
  by_cases hil : i=l
  · simp only [hil,labelProfileGram,ite_true]
  · obtain ⟨d,hd⟩ := hN i l
    simp only [labelProfileGram,ite_eq_right hil,←hd,labelProfileInterpolant_node,labelProfileSpin_node,timeSpin]

lemma scalarRestorationPairMoment_label {k : ℕ} (q : Fin (k+1)→Time)
    (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) (j : ℕ)
    (Q : CompactBlock CompactJointOverlap (2+j))
    (hN : ∀ i l,(Q i l).2∈Set.range (sourceLabelLevel k)) :
    scalarRestorationPairMoment f v w F j (labelProfileGram q Q) =
      labelRestorationBlockMoment (fun i => (q i:ℝ)) f (fun _ => v) (fun _ => w)
        (labelProfilePairTest q F) j Q := by
  simp only [scalarRestorationPairMoment,labelRestorationBlockMoment,BoundedContinuousFunction.mul_apply,
    scalarFrontMatrixTest_label,labelMarkedBlockKernel_profile q _ Q hN]

lemma scalarRestorationPairMoment_diagonalMap {k : ℕ} (q : Fin (k+1)→Time)
    (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) (j : ℕ)
    (Q : CompactArray CompactJointOverlap) (hN : CompactLabelNodes k Q) :
    scalarRestorationPairMoment f v w F j (fun i l =>
      (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q i l).1.val) =
      labelRestorationBlockMoment (fun i => (q i:ℝ)) f (fun _ => v) (fun _ => w)
        (labelProfilePairTest q F) j (compactBlock (2+j) Q) := by
  have he : (fun i l : Fin (2+j) => (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal Q i l).1.val)=
      labelProfileGram q (compactBlock (2+j) Q) := by
    funext i l
    simp only [compactDiagonalMapArray,labelProfileGram,Fin.val_inj]
    split_ifs <;> rfl
  rw [he]
  exact scalarRestorationPairMoment_label q f v w F j _ (fun i l => hN i l)

end SphericalPerceptronFreeEnergy
end

end OAI
