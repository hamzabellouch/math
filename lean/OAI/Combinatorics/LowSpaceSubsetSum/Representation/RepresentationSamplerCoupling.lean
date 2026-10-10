import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteProductSamplerCoupling
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSeparatorTrial
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorSamplingBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.GuessArrayExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CanonicalPartition

namespace OAI

/-! # The bounded samplers for the actual dependent representation history -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

def bitArrayCoupling (n : ℕ) : SamplerCoupling (Fin n → Bool) where
  Seed := Fin n → Bool
  finiteSeed := inferInstance
  law := FiniteLaw.uniform
  ideal := id
  bounded := some
  agrees _ := Or.inr rfl

theorem bitArrayCoupling_uniform (n : ℕ) :
    (bitArrayCoupling n).idealLaw = FiniteLaw.uniform := by
  apply FiniteLaw.eq_of_mass
  intro b
  exact FiniteLaw.probability_eq _ b

theorem bitArrayCoupling_failure (n : ℕ) : (bitArrayCoupling n).failure = 0 := by
  simp [SamplerCoupling.failure, bitArrayCoupling, FiniteLaw.probability]

def bitsSubsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun b := Finset.univ.filter (fun i => b i = true)
  invFun S i := decide (i ∈ S)
  left_inv b := by funext i; cases h : b i <;> simp [h]
  right_inv S := by ext i; simp

def signCoupling (n : ℕ) : SamplerCoupling (Finset (Fin n)) :=
  (bitArrayCoupling n).map (bitsSubsetEquiv n)

theorem signCoupling_uniform (n : ℕ) :
    (signCoupling n).idealLaw = FiniteLaw.uniform := by
  rw [signCoupling, SamplerCoupling.map_idealLaw, bitArrayCoupling_uniform]
  exact FiniteLaw.map_equiv_uniform (bitsSubsetEquiv n)

theorem signCoupling_failure (n : ℕ) : (signCoupling n).failure = 0 := by
  rw [signCoupling, SamplerCoupling.map_failure, bitArrayCoupling_failure]

def initialSubset (g e : ℕ) (he : e ≤ g) : Finset (Fin g) :=
  Finset.univ.map (Fin.castLEEmb he)

@[simp] theorem initialSubset_card (g e : ℕ) (he : e ≤ g) :
    (initialSubset g e he).card = e := by simp [initialSubset]

def initialSubsetEquiv (g e : ℕ) (he : e ≤ g) :
    ↥((Finset.univ : Finset (Fin g)).powersetCard (initialSubset g e he).card) ≃
      SeparatorSample (Finset.univ : Finset (Fin g)) e where
  toFun S := ⟨S.val, by simpa only [initialSubset_card] using S.property⟩
  invFun S := ⟨S.val, by simpa only [initialSubset_card] using S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fixedSizeCoupling (n g e : ℕ) (he : e ≤ g) :
    SamplerCoupling (SeparatorSample (Finset.univ : Finset (Fin g)) e) :=
  (subsetCoupling n g (initialSubset g e he)).map (initialSubsetEquiv g e he)

theorem fixedSizeCoupling_uniform (n g e : ℕ) (he : e ≤ g) :
    (fixedSizeCoupling n g e he).idealLaw =
      @FiniteLaw.uniform _ inferInstance
        ⟨⟨initialSubset g e he, Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, initialSubset_card g e he⟩⟩⟩ := by
  let : Nonempty ↥((Finset.univ : Finset (Fin g)).powersetCard
      (initialSubset g e he).card) :=
    ⟨⟨initialSubset g e he, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩⟩
  let : Nonempty (SeparatorSample (Finset.univ : Finset (Fin g)) e) :=
    ⟨⟨initialSubset g e he, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, initialSubset_card g e he⟩⟩⟩
  rw [fixedSizeCoupling, SamplerCoupling.map_idealLaw, subsetCoupling_uniform]
  exact FiniteLaw.map_equiv_uniform (initialSubsetEquiv g e he)

theorem fixedSizeCoupling_failure (n g e : ℕ) (he : e ≤ g) :
    (fixedSizeCoupling n g e he).failure ≤ g / (2 : ℝ) ^ (n ^ 3) := by
  rw [fixedSizeCoupling, SamplerCoupling.map_failure]
  exact subsetCoupling_failure _ _ _

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

private instance guessNonempty (n : ℕ) : Nonempty ↥(guessRange n) :=
  (guessRange_nonempty n).to_subtype

def layoutCoupling (_R : RepresentationSetup n) : SamplerCoupling (Layout n) :=
  (permutationCoupling n n).prod (signCoupling n)

theorem layoutCoupling_uniform : R.layoutCoupling.idealLaw = R.layoutLaw := by
  exact SamplerCoupling.prod_uniform _ _ (permutationCoupling_uniform _ _)
    (signCoupling_uniform _)

theorem layoutCoupling_failure : R.layoutCoupling.failure ≤ n / (2 : ℝ) ^ (n ^ 3) := by
  exact (SamplerCoupling.prod_failure_le _ _).trans
    (by simpa only [signCoupling_failure, add_zero] using permutationCoupling_failure n n)

def guessesCoupling (_R : RepresentationSetup n) : SamplerCoupling (Guesses n) :=
  GuessArrayExecution.coupling n

theorem guessesCoupling_uniform : R.guessesCoupling.idealLaw = FiniteLaw.uniform := by
  exact SamplerCoupling.pi_uniform 3 _ _ (fun _ => CanonicalGuesses.coupling_uniform n)

theorem guessesCoupling_failure : R.guessesCoupling.failure ≤ 3 / (2 : ℝ) ^ (n ^ 3) := by
  have h := SamplerCoupling.pi_failure_le 3 (fun _ => ↥(guessRange n))
    (fun _ => CanonicalGuesses.coupling n) (fun _ => 1 / (2 : ℝ) ^ (n ^ 3))
    (fun _ => CanonicalGuesses.coupling_failure n)
  have he : (∑ _ : Fin 3, 1 / (2 : ℝ) ^ (n ^ 3)) = 3 / (2 : ℝ) ^ (n ^ 3) := by
    simp
    ring
  simpa only [guessesCoupling, GuessArrayExecution.coupling, he] using h

def partitionsCoupling (z : Layout n) : SamplerCoupling (R.Partitions z) :=
  SamplerCoupling.pi 3 (fun i => R.Partition z i)
    (fun i => CanonicalPartition.coupling R z i)

theorem partitionsCoupling_uniform (z : Layout n) :
    (R.partitionsCoupling z).idealLaw = FiniteLaw.uniform := by
  exact SamplerCoupling.pi_uniform 3 _ _ (fun i =>
    CanonicalPartition.coupling_uniform R z i)

theorem partitionsCoupling_failure (z : Layout n) :
    (R.partitionsCoupling z).failure ≤ 3 * mixerSize n / (2 : ℝ) ^ (n ^ 3) := by
  have h := SamplerCoupling.pi_failure_le 3 (fun i => R.Partition z i)
    (fun i => CanonicalPartition.coupling R z i)
    (fun _ => (mixerSize n : ℝ) / (2 : ℝ) ^ (n ^ 3))
    (fun i => CanonicalPartition.coupling_failure R z i)
  dsimp only [partitionsCoupling]
  convert h using 1
  simp
  ring

def guessHistoryCoupling : SamplerCoupling R.GuessHistory :=
  R.layoutCoupling.bind (fun _ => Guesses n) (fun _ => R.guessesCoupling)

def partitionHistoryCoupling : SamplerCoupling R.PartitionHistory :=
  R.guessHistoryCoupling.bind (fun h => R.Partitions h.1)
    (fun h => R.partitionsCoupling h.1)

theorem guessHistoryCoupling_uniform : R.guessHistoryCoupling.idealLaw = R.guessLaw := by
  rw [guessHistoryCoupling, SamplerCoupling.bind_idealLaw, R.layoutCoupling_uniform]
  simp only [R.guessesCoupling_uniform, guessLaw]

theorem partitionHistoryCoupling_uniform :
    R.partitionHistoryCoupling.idealLaw = R.partitionLaw := by
  rw [partitionHistoryCoupling, SamplerCoupling.bind_idealLaw, R.guessHistoryCoupling_uniform]
  simp only [R.partitionsCoupling_uniform, partitionLaw]

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
