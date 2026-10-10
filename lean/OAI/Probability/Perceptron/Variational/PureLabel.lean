import Mathlib
import OAI.Probability.Perceptron.Pressure.EnrichedPatternMean
import OAI.Probability.Perceptron.Sphere.GaussianAffineCoordinate

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma inner_eraseMarkCoordinate {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (x y : EuclideanSpace ℝ I) :
    inner ℝ (eraseMarkCoordinate i x) y=inner ℝ x y-y i*x i := by
  change (∑ j, y j*(eraseMarkCoordinate i x) j)=(∑ j, y j*x j)-y i*x i
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have he : (∑ j∈Finset.univ.erase i, y j*(eraseMarkCoordinate i x) j)=
      ∑ j∈Finset.univ.erase i, y j*x j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [eraseMarkCoordinate,Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he]
  simp [eraseMarkCoordinate]

lemma inner_eraseMarkCoordinate_right {I : Type} [Fintype I] [DecidableEq I]
    (i : I) (x y : EuclideanSpace ℝ I) :
    inner ℝ x (eraseMarkCoordinate i y)=inner ℝ x y-x i*y i := by
  rw [real_inner_comm,inner_eraseMarkCoordinate,real_inner_comm y x]

def pureLabelIndex {N : ℕ} (p : Fin N→ℕ) (j : Fin N) (hp : p j=0) : EnrichedIndex N N p :=
  Sum.inr ⟨j,fun l => Fin.elim0 (Fin.cast hp l)⟩

lemma sourceFeature_pure_coordinate {N : ℕ} (p : Fin N→ℕ) (u : Fin N→ℝ)
    (j : Fin N) (hp : p j=0) (x : NormalizedSpin N) :
    sourceEnrichedFeature N p u x (pureLabelIndex p j hp)=perturbationAmplitude N u j := by
  simp only [sourceEnrichedFeature,enrichedFeature,pureLabelIndex,WithLp.ofLp_toLp]
  have he : spinTensorFeature N (p j) x (fun l => Fin.elim0 (Fin.cast hp l))=1 := by
    unfold spinTensorFeature
    have hx : IsEmpty (Fin (p j)) := by rw [hp]; infer_instance
    simp
  rw [he,mul_one]

lemma sourceFeature_erase_pure {N : ℕ} (p : Fin N→ℕ) (u : Fin N→ℝ)
    (j : Fin N) (hp : p j=0) (x : NormalizedSpin N) :
    sourceEnrichedFeature N p (Function.update u j 0) x=
      eraseMarkCoordinate (pureLabelIndex p j hp) (sourceEnrichedFeature N p u x) := by
  classical
  ext i
  rcases i with i|⟨l,t⟩
  · simp [sourceEnrichedFeature,enrichedFeature,eraseMarkCoordinate,pureLabelIndex]
  · by_cases hl : l=j
    · subst l
      have hs : Subsingleton (SpinTensorIndex N (p j)) := by
        unfold SpinTensorIndex
        rw [hp]
        infer_instance
      have ht : t=(fun l => Fin.elim0 (Fin.cast hp l)) := Subsingleton.elim _ _
      subst t
      simp [sourceEnrichedFeature,enrichedFeature,eraseMarkCoordinate,pureLabelIndex,
        perturbationAmplitude]
    · have hi : (Sum.inr ⟨l,t⟩ : EnrichedIndex N N p)≠pureLabelIndex p j hp := by
        intro he
        have := congrArg (fun a : EnrichedIndex N N p => match a with | .inl _ => j | .inr a => a.1) he
        exact hl this
      simp [sourceEnrichedFeature,enrichedFeature,eraseMarkCoordinate,Function.update_of_ne hi,
        perturbationAmplitude,Function.update_of_ne hl]

lemma enrichedTerminal_free_pure (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M→Fin (n+1)→ℝ) (p : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ)
    (j : Fin (n+1)) (hp : p j=0) (htop : ℝ) :
    ∀ a, enrichedTerminal n M f g p (Function.update u j 0) htop
      (eraseMarkCoordinate (pureLabelIndex p j hp) a)=
      enrichedTerminal n M f g p (Function.update u j 0) htop a := by
  intro a
  unfold enrichedTerminal vectorLogPartition vectorPartition
  congr 3
  funext x
  congr 1
  congr 1
  change inner ℝ (sourceEnrichedFeature (n+1) p (Function.update u j 0) x)
    (eraseMarkCoordinate (pureLabelIndex p j hp) a)=_
  rw [inner_eraseMarkCoordinate_right,sourceFeature_pure_coordinate p _ j hp]
  simp [perturbationAmplitude]

lemma enrichedTerminal_affine_pure (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M→Fin (n+1)→ℝ) (p : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ)
    (j : Fin (n+1)) (hp : p j=0) (htop : ℝ) :
    enrichedTerminal n M f g p u htop = fun a =>
      enrichedTerminal n M f g p (Function.update u j 0) htop a+
        perturbationAmplitude (n+1) u j*a (pureLabelIndex p j hp) := by
  funext a
  let v := Function.update u j 0
  let c := perturbationAmplitude (n+1) u j*a (pureLabelIndex p j hp)
  have hinner (x : NormalizedSpin (n+1)) :
      inner ℝ (sourceEnrichedFeature (n+1) p u x) a=
      inner ℝ (sourceEnrichedFeature (n+1) p v x) a+c := by
    rw [sourceFeature_erase_pure p u j hp,inner_eraseMarkCoordinate,
      sourceFeature_pure_coordinate p u j hp]
    dsimp [c]
    ring
  have hW : Measurable (normalizedPatternEnergy (n+1) M f g) :=
    ((normalizedPatternEnergy_continuous (n+1) M f).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hV : Measurable (fun x : NormalizedSpin (n+1) =>
      innerSL ℝ (sourceEnrichedFeature (n+1) p v x)) :=
    ((innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)).measurable
  have hpos := vectorPartition_pos (unitSphereLaw (n+1)) hW hV
    (normalizedPatternEnergy_bound (n+1) M f g)
    (fun x => by rw [innerSL_apply_norm,sourceEnrichedFeature_norm]) a
  have he : vectorPartition (unitSphereLaw (n+1)) (normalizedPatternEnergy (n+1) M f g)
      (fun x => innerSL ℝ (sourceEnrichedFeature (n+1) p u x)) a=
      vectorPartition (unitSphereLaw (n+1)) (normalizedPatternEnergy (n+1) M f g)
      (fun x => innerSL ℝ (sourceEnrichedFeature (n+1) p v x)) a*Real.exp c := by
    unfold vectorPartition
    simp only [innerSL_apply_apply,hinner,← add_assoc,Real.exp_add]
    exact integral_mul_const _ _
  unfold enrichedTerminal vectorLogPartition
  rw [he,Real.log_mul hpos.ne' (Real.exp_ne_zero c),Real.log_exp]
  dsimp [v,c]
  ring

section DiagonalWord
variable {I : Type} [Fintype I]

def diagonalCascadeWord (A : ℕ→I→ℝ) : (k : ℕ)→(Fin k→ℝ)→List (ℝ×(I→ℝ))
  | 0,_ => []
  | k+1,z => (z 0,A k)::diagonalCascadeWord A k (fun i => z i.succ)

lemma diagonalCascadeWord_exact (A : ℕ→I→ℝ) (k : ℕ) (z : Fin k→ℝ) :
    diagonalWord (diagonalCascadeWord A k z)=linearCascadeWord (fun j => diagonalMark (A j)) k z := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [diagonalCascadeWord,diagonalWord,List.map_cons,linearCascadeWord]; rw [← ih]; rfl

omit [Fintype I] in
lemma diagonalCascadeWord_nonneg (A : ℕ→I→ℝ) (k : ℕ) (z : Fin k→ℝ) (hz : ∀ i, 0≤z i) :
    ∀ a∈diagonalCascadeWord A k z, 0≤a.1 := by
  induction k with
  | zero => simp [diagonalCascadeWord]
  | succ k ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact hz 0
    · exact ih (fun i => z i.succ) (fun i => hz i.succ) a ha

end DiagonalWord

def enrichedIncrementFactors {N k : ℕ} (p d : Fin N→ℕ) (h : Fin (k+1)→ℝ)
    (j : ℕ) : EnrichedIndex N N p→ℝ :=
  if hj : j<k then fun i => Real.sqrt
    (enrichedCoordinateLevel p d h ⟨k-j,by omega⟩ i-
     enrichedCoordinateLevel p d h ⟨k-j-1,by omega⟩ i) else fun _ => 0

lemma enrichedIncrementFactors_exact {N k : ℕ} (p d : Fin N→ℕ) (h : Fin (k+1)→ℝ) :
    (fun j => diagonalMark (enrichedIncrementFactors p d h j))=enrichedIncrementMap p d h := by
  funext j
  simp only [enrichedIncrementFactors,enrichedIncrementMap]
  split_ifs
  · rfl
  · ext x i
    change 0*x i=0
    ring

def pureLabelResponse {N : ℕ} (p d : Fin N→ℕ) (j : Fin N) (hp : p j=0)
    (k : ℕ) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) : ℝ :=
  ((diagonalCascadeWord (enrichedIncrementFactors p d h) k z).map
    (fun a => a.1*(a.2 (pureLabelIndex p j hp))^2)).sum

lemma enrichedExpectedLog_pure_response (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ)
    (j : Fin (n+1)) (hp : p j=0) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    enrichedExpectedLog n M k f p d u h z g=
      enrichedExpectedLog n M k f p d (Function.update u j 0) h z g+
        (perturbationAmplitude (n+1) u j)^2/2*pureLabelResponse p d j hp k h z := by
  classical
  unfold enrichedExpectedLog
  rw [(enrichedCascadeLog_joint_mean n M k f g p d u h z hz hz0 hz1).2,
    (enrichedCascadeLog_joint_mean n M k f g p d (Function.update u j 0) h z hz hz0 hz1).2]
  rw [enrichedTerminal_affine_pure n M f g p u j hp]
  have he := diagonalCascadeWord_exact (enrichedIncrementFactors p d h) k z
  rw [enrichedIncrementFactors_exact] at he
  rw [← he]
  exact gaussianLinearBackward_affine_root_mean (pureLabelIndex p j hp) _
    (diagonalCascadeWord_nonneg _ k z (fun i => (hz0 i).le))
    (fun i => Real.sqrt (enrichedCoordinateLevel p d h 0 i))
    (enrichedTerminal_lipschitz n M f g p (Function.update u j 0) _)
    (enrichedTerminal_free_pure n M f g p u j hp _) _

end SphericalPerceptronFreeEnergy
end

end OAI
