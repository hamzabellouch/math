import OAI.NumberTheory.Ostmann.Construction.DistinctValueWeights
import OAI.NumberTheory.Ostmann.Construction.RepeatedPrimeGroups
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsUnion

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem injected_tuple_distinct_weight_sum_le {Ω κ : Type*} [Fintype Ω] [Fintype κ]
    [DecidableEq κ] (b : ℕ) (f : Ω → (Fin b → κ)) (hf : Function.Injective f)
    (w : κ → ℝ) (hw : ∀a,0≤w a) :
    (∑x:Ω,∏q∈tupleImage b (f x),w q)≤(b:ℝ)^b*Real.exp (∑q,w q) := by
  classical
  calc
    _ = ∑y∈Finset.univ.image f,∏q∈tupleImage b y,w q := by
      rw [Finset.sum_image (fun x _ y _ h => hf h)]
    _ ≤ ∑y:Fin b→κ,∏q∈tupleImage b y,w q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => Finset.prod_nonneg fun q _ => hw q)
    _ ≤ _ := tuple_distinct_weight_sum_le b w hw

namespace InitialEta

def candidateTuple (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (aux : ι → PrimeSource) (b s : ℕ)
    (x : JointSample giant bulk spectator aux b s) :
    Fin (Fintype.card (Position b s ι)) → ↥(candidateValues giant bulk spectator aux b s) :=
  fun i => ⟨tupleValues x ((Fintype.equivFin (Position b s ι)).symm i),
    tupleValues_mem_candidateValues x _⟩

theorem candidateTuple_injective (giant bulk spectator : PrimeSource) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource) (b s : ℕ) :
    Function.Injective (candidateTuple giant bulk spectator aux b s) := by
  intro x y hxy
  apply (tupleEquiv giant bulk spectator aux b s).injective
  funext i
  apply Subtype.ext
  change tupleValues x i=tupleValues y i
  have he := congrArg (fun f => (f ((Fintype.equivFin (Position b s ι)) i):ℕ)) hxy
  simpa only [candidateTuple,Equiv.symm_apply_apply] using he

lemma candidateTuple_distinct_product (giant bulk spectator : PrimeSource) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource) (b s : ℕ)
    (x : JointSample giant bulk spectator aux b s) :
    (∏q∈tupleImage (Fintype.card (Position b s ι))
      (candidateTuple giant bulk spectator aux b s x),1/((q:ℕ):ℝ)) =
      1/((∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ):ℝ) := by
  classical
  let f := candidateTuple giant bulk spectator aux b s x
  have he : (tupleImage (Fintype.card (Position b s ι)) f).image Subtype.val =
      tupleDistinctPrimes (tupleValues x) := by
    ext q
    simp only [tupleImage,Finset.mem_image,Finset.mem_univ,true_and,tupleDistinctPrimes]
    constructor
    · rintro ⟨z,⟨i,rfl⟩,rfl⟩
      exact ⟨(Fintype.equivFin (Position b s ι)).symm i,rfl⟩
    · rintro ⟨i,rfl⟩
      refine ⟨f ((Fintype.equivFin (Position b s ι)) i),⟨_,rfl⟩,?_⟩
      simp only [f,candidateTuple,Equiv.symm_apply_apply]
  have hp := Finset.prod_image (s := tupleImage (Fintype.card (Position b s ι)) f)
    (f := fun q : ℕ => 1/(q:ℝ)) (g := Subtype.val)
    (fun a _ b _ h => Subtype.ext h)
  rw [he] at hp
  rw [← hp,Finset.prod_div_distrib,Finset.prod_const_one]
  congr 1
  rw [Finset.prod_coe_sort (tupleDistinctPrimes (tupleValues x)) (fun q : ℕ => q),Nat.cast_prod]

theorem original_tuple_reciprocal_distinct_sum_le (giant bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource) (b s : ℕ) :
    (∑x:JointSample giant bulk spectator aux b s,
      1/((∏q:↥(tupleDistinctPrimes (tupleValues x)),(q:ℕ):ℕ):ℝ))≤
      (Fintype.card (Position b s ι):ℝ)^(Fintype.card (Position b s ι))*
      Real.exp (harmonicPrimeMass (candidateValues giant bulk spectator aux b s)) := by
  classical
  have h := injected_tuple_distinct_weight_sum_le (Fintype.card (Position b s ι))
    (candidateTuple giant bulk spectator aux b s) (candidateTuple_injective giant bulk spectator aux b s)
    (fun q => 1/((q:ℕ):ℝ)) (fun q => by positivity)
  simp_rw [candidateTuple_distinct_product] at h
  rw [Finset.sum_coe_sort (candidateValues giant bulk spectator aux b s) (fun q : ℕ => 1/(q:ℝ))] at h
  exact h

end InitialEta
end Ostmann.Construction

end

end OAI
