import OAI.Probability.StrongRayleigh.Model
import OAI.Probability.StrongRayleigh.InclusionUniqueness

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate
namespace Problem336AdditiveD139

def binaryPullbackLaw {A : Type u_1} {B : Type u_2} (μ : ProbabilityMeasure (B → Bool)) (e : A → B) :
    ProbabilityMeasure (A → Bool) :=
  μ.map (fun x i => x (e i))

lemma binaryPullbackLaw_toMeasure {A : Type u_3} {B : Type u_4}
    (μ : ProbabilityMeasure (B → Bool)) (e : A → B) :
    (binaryPullbackLaw μ e : Measure (A → Bool)) =
      Measure.map (fun x i => x (e i)) (μ : Measure (B → Bool)) := rfl

lemma inclusionDeterminant_map {A : Type u_5} {B : Type u_6} [DecidableEq A] [DecidableEq B] (K : B → B → ℂ)
    (e : A ↪ B) (S : Finset A) :
    Matrix.det (fun i j : S.map e => K i.1 j.1) =
      Matrix.det (fun i j : S => K (e i.1) (e j.1)) := by
  classical
  let f : S ≃ S.map e := Equiv.ofBijective
    (fun i => ⟨e i.1, Finset.mem_map.mpr ⟨i.1, i.2, rfl⟩⟩)
    (by
      constructor
      · intro i j h
        exact Subtype.ext (e.injective (congrArg Subtype.val h))
      · intro j
        obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.2
        exact ⟨⟨i, hi⟩, Subtype.ext hij⟩)
  exact (Matrix.det_submatrix_equiv_self f (fun i j : S.map e => K i.1 j.1)).symm

lemma isDeterminantalLaw_binaryPullback {A : Type u_7} {B : Type u_8}
    (μ : ProbabilityMeasure (B → Bool)) (K : B → B → ℂ)
    (hμ : IsDeterminantalLaw μ K) (e : A ↪ B) :
    IsDeterminantalLaw (binaryPullbackLaw μ e) (fun i j => K (e i) (e j)) := by
  classical
  intro S
  rw [binaryPullbackLaw_toMeasure, Measure.map_apply
    (Measurable.of_eval fun i => measurable_pi_apply (e i))
    (measurableSet_inclusionEvent S)]
  have hevent : (fun (x : B → Bool) i => x (e i)) ⁻¹'
      {x : A → Bool | ∀ i ∈ S, x i = true} =
      {x : B → Bool | ∀ j ∈ S.map e, x j = true} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Finset.forall_mem_map]
  rw [hevent, hμ (S.map e), inclusionDeterminant_map]

lemma isFiniteDeterminantalLaw_binaryPullback {A : Type u_9} {B : Type u_10}
    [Fintype A] [Fintype B] (μ : ProbabilityMeasure (B → Bool)) (K : B → B → ℂ)
    (hμ : IsFiniteDeterminantalLaw μ K) (e : A ↪ B) :
    IsFiniteDeterminantalLaw (binaryPullbackLaw μ e) (fun i j => K (e i) (e j)) :=
  isDeterminantalLaw_binaryPullback μ K hμ e

lemma finiteDppFamily_projective {I : Type u_11} (K : I → I → ℂ)
    (P : ∀ S : Finset I, ProbabilityMeasure (S → Bool))
    (hP : ∀ S, IsFiniteDeterminantalLaw (P S) (fun i j : S => K i.1 j.1))
    (hunique : ∀ (S : Finset I) (ν : ProbabilityMeasure (S → Bool)),
      IsFiniteDeterminantalLaw ν (fun i j : S => K i.1 j.1) → ν = P S) :
    IsProjectiveMeasureFamily (α := fun _ : I => Bool) (fun S => (P S : Measure (S → Bool))) := by
  classical
  intro S T hTS
  let e : T ↪ S := ⟨fun i => ⟨i.1, hTS i.2⟩,
    fun a b h => Subtype.ext (congrArg (fun x : S => (x : I)) h)⟩
  have hd : IsFiniteDeterminantalLaw (binaryPullbackLaw (P S) e)
      (fun i j : T => K i.1 j.1) :=
    isFiniteDeterminantalLaw_binaryPullback (P S) (fun i j : S => K i.1 j.1) (hP S) e
  have heq := hunique T (binaryPullbackLaw (P S) e) hd
  exact congrArg (fun ν : ProbabilityMeasure (T → Bool) => (ν : Measure (T → Bool)))
    heq.symm

end Problem336AdditiveD139

end

end OAI
