import OAI.NumberTheory.DukePrimeDegree.Entropy.UpperRootCutItineraries
import OAI.NumberTheory.PrimePackets.FutureConditionalEntropy

namespace OAI

/-! # Countable separating distance cuts on the lattice quotient

Distance cuts can be chosen in every rational interval. Together with a
countable dense set of centers they separate points. Their finite prefixes
therefore generate the Borel sigma algebra, while the good-cut construction
keeps every finite future itinerary locally constant along upper roots.
-/

noncomputable section
open Set Filter MeasureTheory MeasurableSpace
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

abbrev RationalCutInterval := {p : ℚ × ℚ // p.1 < p.2}
abbrev QuotientCutIndex := ℕ × RationalCutInterval

instance : Nonempty RationalCutInterval := ⟨⟨(0,1),by norm_num⟩⟩

def quotientCutBit {n : ℕ} (r : QuotientCutIndex → ℝ)
    (x : X n) (i : QuotientCutIndex) : Bool :=
  decide (quotientLogDistance (TopologicalSpace.denseSeq (X n) i.1) x < r i)

lemma quotientCutBit_measurable {n : ℕ} (r : QuotientCutIndex → ℝ)
    (i : QuotientCutIndex) : Measurable (fun x : X n => quotientCutBit r x i) := by
  apply measurable_to_bool
  have he : (fun x : X n => quotientCutBit r x i) ⁻¹' {true} =
      {x | quotientLogDistance (TopologicalSpace.denseSeq (X n) i.1) x < r i} := by
    ext x
    simp [quotientCutBit]
  rw [he]
  exact measurableSet_lt (continuous_quotientLogDistance n _).measurable measurable_const

theorem quotientCutBit_injective {n : ℕ} (r : QuotientCutIndex → ℝ)
    (hr : ∀ i, (i.2.val.1 : ℝ) < r i ∧ r i < (i.2.val.2 : ℝ)) :
    Function.Injective (fun x : X n => quotientCutBit r x) := by
  intro x y hbits
  by_contra hxy
  have hne : quotientLogDistance x y ≠ 0 :=
    mt (quotientLogDistance_eq_zero_iff x y).mp hxy
  have hpos : 0 < quotientLogDistance x y :=
    lt_of_le_of_ne (quotientLogDistance_nonneg x y) (Ne.symm hne)
  have hU : IsOpen {z : X n | quotientLogDistance x z < quotientLogDistance x y/3} :=
    isOpen_lt (continuous_quotientLogDistance n x) continuous_const
  obtain ⟨k,hk⟩ := (TopologicalSpace.denseRange_denseSeq (X n)).exists_mem_open hU
    ⟨x,by simpa only [Set.mem_ofPred_eq,quotientLogDistance_self] using (div_pos hpos (by norm_num : (0:ℝ)<3))⟩
  let z := TopologicalSpace.denseSeq (X n) k
  have hk' : quotientLogDistance z x < quotientLogDistance x y/3 := by
    change quotientLogDistance x z < quotientLogDistance x y/3 at hk
    rwa [quotientLogDistance_symm x z] at hk
  have htri := quotientLogDistance_triangle x z y
  rw [quotientLogDistance_symm x z] at htri
  have hlt : quotientLogDistance z x < quotientLogDistance z y := by linarith
  obtain ⟨a,hxa,hay⟩ := exists_rat_btwn hlt
  obtain ⟨b,hab,hby⟩ := exists_rat_btwn hay
  let i : QuotientCutIndex := ⟨k,⟨(a,b),by exact_mod_cast hab⟩⟩
  have hi := hr i
  have hx : quotientCutBit r x i=true := by
    simp only [quotientCutBit,decide_eq_true_eq]
    exact hxa.trans hi.1
  have hy : quotientCutBit r y i=false := by
    simp only [quotientCutBit,decide_eq_false_iff_not]
    exact not_lt.mpr (hi.2.le.trans hby.le)
  have he := congrFun hbits i
  change quotientCutBit r x i = quotientCutBit r y i at he
  rw [hx,hy] at he
  cases he

theorem quotientCutBit_measurableEmbedding {n : ℕ} (r : QuotientCutIndex → ℝ)
    (hr : ∀ i, (i.2.val.1 : ℝ) < r i ∧ r i < (i.2.val.2 : ℝ)) :
    MeasurableEmbedding (fun x : X n => quotientCutBit r x) :=
  (measurable_pi_iff.mpr (quotientCutBit_measurable r)).measurableEmbedding
    (quotientCutBit_injective r hr)

theorem exists_good_quotient_cuts (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0<ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    ∃ r : QuotientCutIndex → ℝ,
      (∀ i, (i.2.val.1 : ℝ)<r i ∧ r i<(i.2.val.2 : ℝ)) ∧
      ∀ᵐ x ∂μ, ∀ i : QuotientCutIndex,
        ∀ᶠ t in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
          quotientCutBit r
            ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
              (rightAction x ((completeRootChain (d+1)).word t))) i =
          quotientCutBit r
            ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x) i := by
  have hex (i : QuotientCutIndex) := exists_cut_with_upperRoot_itinerary_neighborhoods
    d ell hell ε hε hgap μ hA (TopologicalSpace.denseSeq (X (d+1)) i.1)
    (a := (i.2.val.1 : ℝ)) (b := (i.2.val.2 : ℝ)) (by exact_mod_cast i.2.property)
  choose r hr hgood using hex
  refine ⟨r,hr,?_⟩
  filter_upwards [ae_all_iff.mpr hgood] with x hx
  intro i
  filter_upwards [hx i] with t ht
  intro k
  simp only [quotientCutBit]
  simp only [ht k]

end DukePrimeDegree

end

end OAI
