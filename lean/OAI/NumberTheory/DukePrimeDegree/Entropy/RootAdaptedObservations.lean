import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientSeparatingCuts
import OAI.NumberTheory.DukePrimeDegree.Entropy.DiagonalConditionalEntropy

namespace OAI

/-! # Finite generating observations with root neighborhoods in future atoms -/

noncomputable section
open Set Filter MeasureTheory MeasurableSpace
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

private noncomputable instance : Encodable QuotientCutIndex := Encodable.ofCountable _

def quotientCutEnumeration (n : ℕ) : QuotientCutIndex :=
  (Encodable.decode n).getD (Classical.choice inferInstance)

lemma quotientCutEnumeration_surjective : Function.Surjective quotientCutEnumeration :=
  Encodable.surjective_decode_getD _ _

def quotientCutBits {d : ℕ} (r : QuotientCutIndex → ℝ) (n : ℕ) (x : X d) : Fin n → Bool :=
  fun i => quotientCutBit r x (quotientCutEnumeration i.val)

lemma quotientCutBits_measurable {d : ℕ} (r : QuotientCutIndex → ℝ) (n : ℕ) :
    Measurable (quotientCutBits (d := d) r n) :=
  measurable_pi_iff.mpr fun i => quotientCutBit_measurable r (quotientCutEnumeration i.val)

lemma quotientCutBits_monotone {d : ℕ} (r : QuotientCutIndex → ℝ) :
    Monotone (fun n => observationSigma (quotientCutBits (d := d) r n)) := by
  intro n m hnm s hs
  obtain ⟨t,_,rfl⟩ := hs
  refine ⟨{v : Fin m → Bool | (fun i : Fin n => v ⟨i.val,lt_of_lt_of_le i.isLt hnm⟩) ∈ t},
    trivial,?_⟩
  rfl

theorem quotientCutBits_generate {d : ℕ} (r : QuotientCutIndex → ℝ)
    (hr : ∀ i, (i.2.val.1 : ℝ)<r i ∧ r i<(i.2.val.2 : ℝ)) :
    (⨆ n, observationSigma (quotientCutBits (d := d) r n)) =
      (inferInstance : MeasurableSpace (X d)) := by
  let F : X d → ℕ → Bool := fun x k => quotientCutBit r x (quotientCutEnumeration k)
  have hF : Measurable F := measurable_pi_iff.mpr fun k =>
    quotientCutBit_measurable r (quotientCutEnumeration k)
  have hFi : Function.Injective F := by
    intro x y hxy
    apply quotientCutBit_injective r hr
    funext i
    obtain ⟨k,rfl⟩ := quotientCutEnumeration_surjective i
    exact congrFun hxy k
  have hgen := (hF.measurableEmbedding hFi).comap_eq
  apply le_antisymm
  · apply iSup_le
    intro n
    exact observationSigma_le _ fun b => (quotientCutBits_measurable r n) (measurableSet_singleton b)
  · rw [←hgen, show F=(fun x k => quotientCutBit r x (quotientCutEnumeration k)) from rfl,
      MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro k
    apply le_trans _ (le_iSup (fun n => observationSigma (quotientCutBits (d := d) r n)) (k+1))
    rintro s ⟨t,ht,rfl⟩
    refine ⟨{v : Fin (k+1) → Bool | v ⟨k,Nat.lt_succ_self k⟩ ∈ t},trivial,?_⟩
    rfl

def quotientCutObservation {d : ℕ} (r : QuotientCutIndex → ℝ) (n : ℕ) (x : X d) :
    Fin (Fintype.card (Fin n → Bool)) :=
  Fintype.equivFin _ (quotientCutBits r n x)

lemma quotientCutObservation_sigma {d : ℕ} (r : QuotientCutIndex → ℝ) (n : ℕ) :
    observationSigma (quotientCutObservation (d := d) r n) =
      observationSigma (quotientCutBits r n) :=
  observationSigma_comp_injective _ _ (Fintype.equivFin (Fin n → Bool)).injective

lemma quotientCutObservation_measurable {d : ℕ} (r : QuotientCutIndex → ℝ) (n : ℕ) :
    Measurable (quotientCutObservation (d := d) r n) :=
  (measurable_of_finite (Fintype.equivFin (Fin n → Bool))).comp (quotientCutBits_measurable r n)

theorem quotientCutObservation_entropy {d : ℕ} (r : QuotientCutIndex → ℝ)
    (hr : ∀ i, (i.2.val.1 : ℝ)<r i ∧ r i<(i.2.val.2 : ℝ))
    (μ : Measure (X d)) [IsProbabilityMeasure μ] {T : X d → X d}
    (hT : MeasurePreserving T μ μ) :
    measureEntropy μ T = ⨆ n, ENNReal.ofReal
      (conditionalSigmaEntropy μ (quotientCutObservation r n)
        (⨆ k, observationSigma (futureName T (quotientCutObservation r n) k))) := by
  have hm : Monotone (fun n => observationSigma (quotientCutObservation (d := d) r n)) := by
    simpa only [quotientCutObservation_sigma] using quotientCutBits_monotone (d := d) r
  have hg : (⨆ n, observationSigma (quotientCutObservation (d := d) r n)) =
      (inferInstance : MeasurableSpace (X d)) := by
    simpa only [quotientCutObservation_sigma] using quotientCutBits_generate (d := d) r hr
  rw [measureEntropy_eq_iSup_generating μ hT (quotientCutObservation r)
    (fun n b => quotientCutObservation_measurable r n (measurableSet_singleton b)) hm hg]
  congr 1
  funext n
  rw [observationEntropyRate_eq_futureConditional μ hT _
    (fun b => quotientCutObservation_measurable r n (measurableSet_singleton b))]

theorem exists_observations_with_root_neighborhoods (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0<ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    ∃ r : QuotientCutIndex → ℝ,
      (∀ i, (i.2.val.1 : ℝ)<r i ∧ r i<(i.2.val.2 : ℝ)) ∧
      ∀ᵐ x ∂μ, ∀ n : ℕ,
        ∀ᶠ t in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
          quotientCutObservation r n
            ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
              (rightAction x ((completeRootChain (d+1)).word t))) =
          quotientCutObservation r n
            ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x) := by
  obtain ⟨r,hr,hgood⟩ := exists_good_quotient_cuts d ell hell ε hε hgap μ hA
  refine ⟨r,hr,?_⟩
  filter_upwards [hgood] with x hx
  intro n
  have hf : ∀ i : Fin n, ∀ᶠ t in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      quotientCutBit r
        ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word t))) (quotientCutEnumeration i.val) =
      quotientCutBit r
        ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)
          (quotientCutEnumeration i.val) := fun i => hx _
  filter_upwards [Filter.eventually_all.mpr hf] with t ht
  intro k
  apply congrArg (Fintype.equivFin (Fin n → Bool))
  funext i
  exact ht i k

end DukePrimeDegree

end

end OAI
