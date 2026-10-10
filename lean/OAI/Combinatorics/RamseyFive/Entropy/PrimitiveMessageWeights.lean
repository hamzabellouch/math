import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.MessageWeights
import OAI.Combinatorics.RamseyFive.Geometry.FourFinitePredictor

namespace OAI

section
namespace SharpRamseyFive.ReverseCap
open MessageWeights
open scoped Classical BigOperators
variable {B : Type} [Fintype B]
omit [Fintype B] in
lemma universalFresh_weight (W : Finset B) (H : ℕ) (q : ℝ) :
    (∑m : UniversalFreshMessage W H q,Real.exp (-universalFreshCost W H q m))≤1 := by
  have hh := sigma_header_weight (Fin (H+1)) (fun n : Fin (H+1)=>FreshMessage W n q)
    (fun n m=>Real.log (W.card+1:ℝ)+Real.log (Fintype.card (Fin (cardCutoff q m.1 W.card n)):ℝ))
    (fun n=>by
      simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
        sigma_header_weight (Fin (W.card+1)) (fun k : Fin (W.card+1)=>Fin (cardCutoff q k W.card n))
          (fun k _=>Real.log (Fintype.card (Fin (cardCutoff q k W.card n)):ℝ))
          (fun k=>log_card_weight _))
  simpa only [universalFreshCost,Fintype.card_fin,Nat.cast_add,Nat.cast_one,add_assoc] using hh
end SharpRamseyFive.ReverseCap
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_weight (U : Finset (ℙ K V)) (P τ : ℝ) :
    (∑m : BaseMessage U P τ,Real.exp (-baseFiniteCost U P τ m))≤1 := by
  simpa only [baseFiniteCost,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    sigma_header_weight (Fin (Fintype.card (ℙ K V)+1)) (fun n : Fin (Fintype.card (ℙ K V)+1)=>baseAlphabet U n P τ)
      (fun n _=>Real.log (Fintype.card (baseAlphabet U n P τ):ℝ)) (fun n=>log_card_weight _)
omit [Finite K] [FiniteDimensional K V] in
lemma scoreFinite_weight [Fintype V] (U : Finset (ℙ K V)) (σ P τ : ℝ) :
    (∑m : ScoredMessage U σ P τ,Real.exp (-scoreFiniteCost U σ P τ m))≤1 := by
  simpa only [scoreFiniteCost,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    sigma_header_weight (Fin (Fintype.card (ℙ K V)+1)) (fun n : Fin (Fintype.card (ℙ K V)+1)=>ScoredPayload U n σ P τ)
      (fun n _=>Real.log (Fintype.card (ScoredPayload U n σ P τ):ℝ)) (fun n=>log_card_weight _)
end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ProjectiveIncidence
open Module MessageWeights ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma ambientPair_weight (UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V)) (H : ℕ) (q : ℝ)
    (t : AmbientPairTape K V H q) :
    (∑m : AmbientPairMessage UB W H q t,Real.exp (-ambientPairCost UB W H q t m))≤1 := by
  exact sigma_weight_le _ _ _ _ (universalFresh_weight W H q) (fun _=>universalFresh_weight _ H q)
end SharpRamseyFive.ProjectiveIncidence

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights ReverseCap
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal

def FinitePredictor.Normalized {A B : Type} [Fintype A] [Fintype B]
    (p : FinitePredictor A B) : Prop :=
  ∀t,(∑m : p.Message t,Real.exp (-p.cost t m))≤1

lemma FinitePredictor.normalized_transform {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (p : FinitePredictor A B) (e : A↪C) (h : Finset C→Finset D→Finset A×Finset B)
    (hp : p.Normalized) : (p.transform e h).Normalized := hp

lemma FinitePredictor.normalized_family {A B I : Type}
    [Fintype A] [Fintype B] [Fintype I] (p : I→FinitePredictor A B)
    (s : Finset A→Finset B→I) (hp : ∀i,(p i).Normalized) :
    (FinitePredictor.family p s).Normalized := by
  intro t
  let (i : I) : Fintype ((p i).Message (t i)) := (p i).messageFintype (t i)
  exact sigma_header_weight I (fun i=>(p i).Message (t i))
    (fun i m=>(p i).cost (t i) m) (fun i=>hp i (t i))

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma reversedBase_weight (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (q : ℝ)
    (t : ReversedBaseTape UT P τ H q) :
    (∑m : ReversedBaseMessage UT P τ H q t,Real.exp (-reversedBaseCost UT P τ H q t m))≤1 := by
  exact sigma_weight_le _ _ _ _ (baseFinite_weight UT P τ) (fun _=>universalFresh_weight _ H q)
omit [Finite K] [FiniteDimensional K V] in
lemma twoPublic_weight (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : TwoPublicTape U UT P τ H q) :
    (∑m : TwoPublicMessage U UT P τ H q t,Real.exp (-twoPublicCost U UT P τ H q t m))≤1 := by
  convert sum_bit_weight _ _ _ _ (baseFinite_weight U P τ) (reversedBase_weight UT P τ H q t.2) using 1
  congr 1
  funext m
  cases m <;> rfl
omit [Finite K] in
lemma orientedFinite_weight
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (d H : ℕ) (q P c B : ℝ) (hf : f.Normalized) (hr : r.Normalized) :
    (orientedFinitePredictor f r U UT d H q P c B).Normalized := by
  intro t
  have hs := sigma_weight_le (r.Message t.2.1)
    (fun m=>UniversalFreshMessage (r.decoded t.2.1 m) H q)
    (r.cost t.2.1) (fun m u=>universalFreshCost (r.decoded t.2.1 m) H q u)
    (hr t.2.1) (fun _=>universalFresh_weight _ H q)
  convert sum_bit_weight _ _ _ _ (hf t.1) hs using 1
  congr 1
  funext m
  cases m <;> rfl
end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma planePublic_weight (A : Submodule K V) [Fintype (ℙ K A)]
    [Fintype (ℙ K (Dual K A))] [Fintype (ℙ K (Dual K (Dual K A)))]
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (k : ℕ)
    (t : PlanePublicTape A U UT P τ k) :
    (∑m : PlanePublicMessage A U UT P τ k t,Real.exp (-planePublicCost A U UT P τ k t m))≤1 :=
  twoPublic_weight _ _ _ _ _ _ t
end SharpRamseyFive.ProjectiveRestriction
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]
lemma threeLocal_weight (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (br : ThreePublicIndex K σ)
    (t : ThreeLocalTape U UT σ P τ br) :
    (∑m : ThreeLocalMessage U UT σ P τ br t,Real.exp (-threeLocalCost U UT σ P τ br t m))≤1 := by
  rcases br with b|b
  · exact baseFinite_weight U P τ
  · rcases b with b|b
    · exact scoreFinite_weight U σ P τ
    · exact planePublic_weight _ U UT P τ _ t
lemma threePublic_weight (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ)
    (t : ThreePublicTape U UT σ P τ) :
    (∑m : ThreePublicMessage U UT σ P τ t,Real.exp (-threePublicCost U UT σ P τ t m))≤1 :=
  sigma_header_weight _ _ _ (fun br=>threeLocal_weight U UT σ P τ br (t br))
end SharpRamseyFive.ScoreGeometry
end

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
lemma threeFinite_weight (hd : finrank K V=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (threeFinitePredictor hd σ U UT P τ R L₀).Normalized := by
  let : Fintype K := Fintype.ofFinite _
  let : Finite (Dual K (Fin 4→K)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Fin 4→K)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Fin 4→K))) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Finite (Dual K A) := Module.finite_of_finite K
  let (A : Submodule K (Fin 4→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  unfold threeFinitePredictor
  try dsimp only
  intro t
  exact threePublic_weight _ _ σ P τ t
lemma threeOrientedFinite_weight [Fintype (ℙ K (Dual K (Dual K V)))]
    (hd : finrank K V=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (threeOrientedFinitePredictor hd σ U UT P τ R L₀).Normalized := by
  exact orientedFinite_weight _ _ _ _ _ _ _ _ _ _
    (threeFinite_weight _ _ _ _ _ _ _ _) (threeFinite_weight _ _ _ _ _ _ _ _)
end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
lemma threeFlatFinite_weight (A : Submodule K V) (hA : finrank K A=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (τ P : ℝ) (R : ℕ) (L₀ : ℝ≥0) (k : ℕ) :
    (threeFlatFinitePredictor A hA σ U UT τ P R L₀ k).Normalized := by
  let : Finite A := Module.finite_of_finite K
  let : Finite (Dual K A) := Module.finite_of_finite K
  let : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let : Fintype (ℙ K A) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  unfold threeFlatFinitePredictor
  try dsimp only
  apply FinitePredictor.normalized_transform
  exact threeOrientedFinite_weight _ _ _ _ _ _ _ _
end SharpRamseyFive.ProjectiveRestriction
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 5→K))] [Fintype (ℙ K (Dual K (Fin 5→K)))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K (Dual K A)))]
lemma fourLocal_weight (U : Finset (ℙ K (Fin 5→K)))
    (UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (br : FourPublicIndex K σ) : (fourLocalPredictor U UT σ P τ R L₀ br).Normalized := by
  rcases br with b|b
  · intro t;exact baseFinite_weight U P τ
  · rcases b with b|b
    · intro t;exact scoreFinite_weight U σ P τ
    · rcases b with b|b
      · intro t;exact planePublic_weight _ U UT P τ _ t
      · exact threeFlatFinite_weight _ _ σ U UT τ P R L₀ _
lemma fourCertified_weight (U : Finset (ℙ K (Fin 5→K)))
    (UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (fourCertifiedPredictor U UT σ P τ R L₀).Normalized :=
  FinitePredictor.normalized_family _ _ (fourLocal_weight U UT σ P τ R L₀)
end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
lemma fourFinite_weight (hd : finrank K V=5) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (fourFinitePredictor hd σ U UT P τ R L₀).Normalized := by
  let : Fintype K := Fintype.ofFinite _
  let : Finite (Dual K (Fin 5→K)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Fin 5→K)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Fin 5→K))) := Fintype.ofFinite _
  let (A : Submodule K (Fin 5→K)) : Finite (Dual K A) := Module.finite_of_finite K
  let (A : Submodule K (Fin 5→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let (A : Submodule K (Fin 5→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  let (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  unfold fourFinitePredictor
  try dsimp only
  apply FinitePredictor.normalized_transform
  exact fourCertified_weight _ _ σ P τ R L₀
end SharpRamseyFive.ScoreGeometry

end OAI
