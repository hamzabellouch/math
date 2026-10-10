import OAI.Probability.SwitchChain.PairOrbit
import OAI.Probability.SwitchChain.SliceMoments

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceGramOrbit

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem average_relabel (q : ℕ) (e : Equiv.Perm α) (f : Finset α → ℝ) :
    SliceMoments.average Finset.univ q (fun S => f (S.image e)) =
      SliceMoments.average Finset.univ q f := by
  unfold SliceMoments.average
  congr 1
  apply Finset.sum_bij (fun S _ => S.image e)
  · intro S hS
    have hc := (Finset.mem_powersetCard.mp hS).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective S e.injective, hc]
  · intro S hS T hT hST
    have hh := congrArg (Finset.image e.symm) hST
    simpa [Finset.image_image] using hh
  · intro T hT
    refine ⟨T.image e.symm, ?_, ?_⟩
    · have hc := (Finset.mem_powersetCard.mp hT).2
      simp [Finset.mem_powersetCard, Finset.card_image_of_injective T e.symm.injective, hc]
    · simp [Finset.image_image]
  · intro S hS
    rfl

def pairEquality (P S : Finset α) : ℝ :=
  if (P ∩ S).card = 0 ∨ (P ∩ S).card = 2 then 1 else 0

omit [Fintype α] in
theorem pairEquality_relabel (e : Equiv.Perm α) (P S : Finset α) :
    pairEquality (P.image e) (S.image e) = pairEquality P S := by
  unfold pairEquality
  rw [← Finset.image_inter P S e.injective, Finset.card_image_of_injective _ e.injective]

omit [Fintype α] in
theorem pairEquality_pair (i j : α) (hij : i ≠ j) (S : Finset α) :
    pairEquality {i,j} S = SliceMoments.equalIndicator i j S := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [pairEquality, SliceMoments.equalIndicator, hi, hj, hij]

def centeredPair (q : ℕ) (P S : Finset α) : ℝ :=
  pairEquality P S - SliceMoments.equalMean (Finset.univ : Finset α) q

theorem centeredPair_relabel (q : ℕ) (e : Equiv.Perm α) (P S : Finset α) :
    centeredPair q (P.image e) (S.image e) = centeredPair q P S := by
  simp only [centeredPair, pairEquality_relabel]

theorem centeredPair_pair (q : ℕ) (i j : α) (hij : i ≠ j) (S : Finset α) :
    centeredPair q {i,j} S = SliceMoments.centeredEqual Finset.univ q i j S := by
  simp only [centeredPair, SliceMoments.centeredEqual, pairEquality_pair i j hij]

def gram (q : ℕ) (P Q : Finset α) : ℝ :=
  SliceMoments.average Finset.univ q (fun S => centeredPair q P S * centeredPair q Q S)

theorem gram_relabel (q : ℕ) (e : Equiv.Perm α) (P Q : Finset α) :
    gram q (P.image e) (Q.image e) = gram q P Q := by
  unfold gram
  rw [← average_relabel q e (fun S =>
    centeredPair q (P.image e) S * centeredPair q (Q.image e) S)]
  simp_rw [centeredPair_relabel]

theorem gram_eq_of_intersection (q : ℕ) (P Q R T : Finset α)
    (hP : P.card = 2) (hQ : Q.card = 2) (hR : R.card = 2) (hT : T.card = 2)
    (hI : (P ∩ Q).card = (R ∩ T).card) :
    gram q P Q = gram q R T := by
  exact PairOrbit.invariant_pair_kernel_eq_of_intersection (gram q) (gram_relabel q)
    P Q R T hP hQ hR hT hI

theorem centeredEqual_gram_eq_of_intersection (q : ℕ)
    (i j k l a b c d : α)
    (hij : i ≠ j) (hkl : k ≠ l) (hab : a ≠ b) (hcd : c ≠ d)
    (hI : (({i,j} : Finset α) ∩ {k,l}).card = (({a,b} : Finset α) ∩ {c,d}).card) :
    SliceMoments.average Finset.univ q (fun S =>
      SliceMoments.centeredEqual Finset.univ q i j S *
      SliceMoments.centeredEqual Finset.univ q k l S) =
    SliceMoments.average Finset.univ q (fun S =>
      SliceMoments.centeredEqual Finset.univ q a b S *
      SliceMoments.centeredEqual Finset.univ q c d S) := by
  have h := gram_eq_of_intersection q {i,j} {k,l} {a,b} {c,d}
    (by simp [hij]) (by simp [hkl]) (by simp [hab]) (by simp [hcd]) hI
  simpa only [gram, centeredPair_pair q i j hij, centeredPair_pair q k l hkl,
    centeredPair_pair q a b hab, centeredPair_pair q c d hcd] using h

end Problem315.SliceGramOrbit

end

end OAI
