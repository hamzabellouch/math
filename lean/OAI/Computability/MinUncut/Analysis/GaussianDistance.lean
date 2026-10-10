import Mathlib
import OAI.Computability.MinUncut.Graphs.EdgeMean
import OAI.Computability.MinUncut.Analysis.GaussianRows

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Composition
open MinUncut.Inner RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient
variable {V W A B : Type*}
  [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B] {m n : ℕ}

lemma comparisonRow_distance_integrable (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) (x : Point m n) (r : Row m n)
    (D : Rest (W := Forms B) r) :
    Integrable (fun c => rowDistance π
      (comparisonRow f σ η c x r (fun t => formPullback π (D t)))
      (comparisonRow g σ η c x r D)) (gauss (Point m n)) := by
  apply integrable_expect
  intro z
  exact ((gradient_memLp g _ hσ η x).sub (gradient_memLp f _ hσ η x)).integrable_sq

omit [Fintype A] in
lemma comparisonRow_distance_mean (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B)
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) (r : Row m n) :
    (𝔼 D : Rest (W := Forms B) r, rowDistance π
      (comparisonRow f σ η c x r (fun t => formPullback π (D t)))
      (comparisonRow g σ η c x r D)) =
    𝔼 C : FaceArray B m n,
      (MinUncut.Inner.gradient f (pullbackFaces π C) σ η c x-MinUncut.Inner.gradient g C σ η c x)^2 := by
  simpa only [rowDistance,sub_sq_comm] using comparisonRow_average π f g σ η c x r

lemma comparisonRow_distance_integral (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) (x : Point m n) (r : Row m n) :
    (𝔼 D : Rest (W := Forms B) r, ∫ c, rowDistance π
      (comparisonRow f σ η c x r (fun t => formPullback π (D t)))
      (comparisonRow g σ η c x r D) ∂gauss (Point m n)) =
    jointEnergy (fun C c => MinUncut.Inner.gradient f (pullbackFaces π C) σ η c x-
      MinUncut.Inner.gradient g C σ η c x) := by
  rw [← integral_expect _ (fun D => comparisonRow_distance_integrable π f g hσ η x r D)]
  simp_rw [comparisonRow_distance_mean]
  exact integral_expect _ (fun C => ((gradient_memLp f _ hσ η x).sub
    (gradient_memLp g C hσ η x)).integrable_sq)

lemma comparisonRow_distance_total (π : A →ᵃ[F₂] B) (f : FoldedProof A) (g : FoldedProof B)
    (hm : 0 < m) {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    (𝔼 x : Point m n, 𝔼 i : Fin m,
      𝔼 D : Rest (W := Forms B) (⟨i,face x i⟩ : Row m n), ∫ c, rowDistance π
        (comparisonRow f σ η c x ⟨i,face x i⟩ (fun t => formPullback π (D t)))
        (comparisonRow g σ η c x ⟨i,face x i⟩ D) ∂gauss (Point m n)) =
      averagedEnergy (m := m) (n := n) (fun C c x => MinUncut.Inner.gradient f (pullbackFaces π C) σ η c x-
        MinUncut.Inner.gradient g C σ η c x) := by
  let : NeZero m := ⟨hm.ne'⟩
  simp_rw [comparisonRow_distance_integral π f g hσ,Fintype.expect_const]
  exact (averagedEnergy_eq_expect_joint _ (fun C x => (gradient_memLp f _ hσ η x).sub
    (gradient_memLp g C hσ η x))).symm
end MinUncut.Composition

open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

def listTerm (M u θ : ℝ) (q k : ℕ) : ℝ :=
  (⌈M^2/u^2⌉₊ : ℝ)*(⌈M^2/θ^2⌉₊ : ℝ)*hintRate q^k

def remainderTerm (M u θ : ℝ) (q k t : ℕ) : ℝ :=
  (256/θ^4)*(u^2*M^2+Real.sqrt (((2 : ℝ)^(4*(q+3)*k)-1)*(k : ℝ)^2/t)*(M+M^2/u)^4)

def ProofFamily.atomAt (f : ProofFamily Name I) (σ η θ : ℝ) (x : Point m n) (i : Fin m) :
    EdgeStatistic Name I :=
  fun U h pos => rowEventProbability (f.second (secondQuestion U h pos)) σ η θ x i

def ProofFamily.distanceAt (f : ProofFamily Name I) (σ η : ℝ) (x : Point m n) (i : Fin m) :
    EdgeStatistic Name I := fun U h pos =>
  𝔼 D : Rest (W := Forms (SecondAlphabet (secondQuestion U h pos))) (⟨i,face x i⟩ : Row m n),
    ∫ c, (f.rows σ η c x ⟨i,face x i⟩).distance U h pos D ∂gauss (Point m n)

lemma ProofFamily.atomAt_integral (f : ProofFamily Name I) (equations : S → Equation Name)
    (k : ℕ) {σ θ : ℝ} (hσ : σ≠0) (hθ : 0<θ) (η : ℝ)
    (x : Point m n) (i : Fin m) :
    (∫ c, backgroundMean equations k ((f.rows σ η c x ⟨i,face x i⟩).atom θ) ∂gauss (Point m n)) =
      edgeMean equations k (f.atomAt σ η θ x i) := by
  rw [integral_backgroundMean _ _ _ (f.rows_atom_integrable hσ hθ η x i)]
  unfold backgroundMean edgeMean ProofFamily.atomAt rowEventProbability LocalRows.atom ProofFamily.rows
  simp_rw [← rowAtomIndicator_eq_list _ σ η hθ]
  rfl

lemma ProofFamily.distanceAt_integral (f : ProofFamily Name I) (equations : S → Equation Name)
    (k : ℕ) {σ : ℝ} (hσ : σ≠0) (η : ℝ) (x : Point m n) (i : Fin m) :
    (∫ c, backgroundMean equations k (f.rows σ η c x ⟨i,face x i⟩).distance ∂gauss (Point m n)) =
      edgeMean equations k (f.distanceAt σ η x i) :=
  integral_backgroundMean _ _ _ (f.rows_distance_integrable hσ η x _)

theorem ProofFamily.row_soundness [Fintype Name] [Nonempty I] [Nonempty S]
    (f : ProofFamily Name I) (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s≤3/4)
    {k : ℕ} (hk : k≤Fintype.card I) {σ u θ : ℝ} (hσ : 0<σ) (hu : 0<u) (hθ : 0<θ)
    (η : ℝ) (x : Point m n) (i : Fin m) :
    edgeMean equations k (f.atomAt σ η θ x i) ≤
      listTerm (Real.sqrt (n^m:ℕ)/σ) u θ (Fintype.card (Row m n)-1) k +
      (16/θ^2)*edgeMean equations k (f.distanceAt σ η x i) +
      remainderTerm (Real.sqrt (n^m:ℕ)/σ) u θ (Fintype.card (Row m n)-1) k (Fintype.card I) := by
  let M : ℝ := Real.sqrt (n^m:ℕ)/σ
  let L := listTerm M u θ (Fintype.card (Row m n)-1) k
  let R := remainderTerm M u θ (Fintype.card (Row m n)-1) k (Fintype.card I)
  have hpoint (c : Point m n → ℝ) :
      backgroundMean equations k ((f.rows σ η c x ⟨i,face x i⟩).atom θ) ≤
        L+(16/θ^2)*backgroundMean equations k (f.rows σ η c x ⟨i,face x i⟩).distance+R := by
    have h := (f.rows σ η c x ⟨i,face x i⟩).atom_bound equations hsound hk
      (by positivity : 0≤M) hu hθ (f.rows_first_bound hσ η c x _) (f.rows_second_bound hσ η c x _)
    simpa only [rest_card,L,R,listTerm,remainderTerm] using h
  have hiA := backgroundMean_integrable equations k _ (f.rows_atom_integrable hσ.ne' hθ η x i)
  have hiD := backgroundMean_integrable equations k _ (f.rows_distance_integrable hσ.ne' η x ⟨i,face x i⟩)
  have h := integral_mono hiA (((integrable_const L).add (hiD.const_mul (16/θ^2))).add (integrable_const R)) hpoint
  rw [f.atomAt_integral equations k hσ.ne' hθ η x i] at h
  simp only [Pi.add_apply] at h
  have hiL : Integrable (fun c => L+(16/θ^2)*backgroundMean equations k (f.rows σ η c x ⟨i,face x i⟩).distance) (gauss (Point m n)) :=
    (integrable_const L).add (hiD.const_mul _)
  rw [integral_add hiL (integrable_const R),
    integral_add (integrable_const L) (hiD.const_mul (16/θ^2)),integral_const_mul,
    f.distanceAt_integral equations k hσ.ne' η x i] at h
  simpa only [integral_const,MeasureTheory.probReal_univ,one_smul] using h
end MinUncut.Outer

end

end OAI
