import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.SampledPoints
import OAI.Combinatorics.RamseyFive.Probability.MeasurePublicTable
import OAI.Combinatorics.RamseyFive.Probability.PoissonProposal

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def publicScore (O : Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
    {R : ℕ} (b : ℝ) (ω : Fin R→ℙ K V→ℕ) : ℝ :=
  ∑ H : F, ∏ r, (if (∀ y,y∈O → Incident y H.val → ω r y=0) then 1 else 0)*
    ((if (∀ y,y∉O → Incident y H.val → ω r y=0) then 1 else 0)-b)

noncomputable def publicSamples (U : Finset (ℙ K V)) {R : ℕ}
    (ω : Fin R→ℙ K V→ℕ) : Finset (ℙ K V) :=
  U.filter fun x=>∃r,ω r x≠0

noncomputable def publicDecoded (U : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (b : ℙ K V→ℝ) (z : ℕ) {R : ℕ} (ω : Fin R→ℙ K V→ℕ) : Finset (ℙ K V) :=
  accepted U (publicSamples U ω) (fun x=>publicScore (O x) (pencil x) (b x) ω)
    ((z:ℝ)/(2*(Nat.card K:ℝ)))

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma support_forall_restrict (S : Finset (ℙ K V)) {R : ℕ}
    (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0)
    (r : Fin R) (P : ℙ K V→Prop) :
    (∀y,P y→ω r y=0) ↔ ∀y:S,P y.val→ω r y=0 := by
  constructor
  · intro h y;exact h y
  · intro h y hy
    by_cases hs : y∈S
    · exact h ⟨y,hs⟩ hy
    · exact hω r y hs

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma publicScore_restrict (S O rawO : Finset (ℙ K V))
    (hO : S∩rawO=O) (F : Finset (ℙ K (Dual K V))) {R : ℕ}
    (b : ℝ) (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0) :
    publicScore rawO F b ω=pointScore S O F b (fun r y=>ω r y) := by
  unfold publicScore pointScore
  apply Finset.sum_congr rfl
  intro H _
  apply Finset.prod_congr rfl
  intro r _
  have ho (y : S) : y.val∈rawO ↔ y.val∈O := by
    rw [←hO,Finset.mem_inter]
    exact ⟨fun h=>⟨y.prop,h⟩,And.right⟩
  have ha : (∀y,y∈rawO → Incident y H.val → ω r y=0) ↔
      (∀y:S,y.val∈O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI;exact h y ((ho y).mpr hy) hI
    · intro h y hy hI
      by_cases hs : y∈S
      · exact h ⟨y,hs⟩ ((ho ⟨y,hs⟩).mp hy) hI
      · exact hω r y hs
  have hb : (∀y,y∉rawO → Incident y H.val → ω r y=0) ↔
      (∀y:S,y.val∉O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI;exact h y (fun hh=>hy ((ho y).mp hh)) hI
    · intro h y hy hI
      by_cases hs : y∈S
      · exact h ⟨y,hs⟩ (fun hh=>hy ((ho ⟨y,hs⟩).mpr hh)) hI
      · exact hω r y hs
  simp only [ha,hb]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma publicSamples_restrict (U S : Finset (ℙ K V)) (hSU : S⊆U) {R : ℕ}
    (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0) :
    publicSamples U ω=sampledPoints S (fun r y=>ω r y) := by
  ext x
  rw [←not_iff_not]
  rw [not_mem_sampledPoints]
  simp only [publicSamples,Finset.mem_filter,not_and,not_exists,not_not]
  constructor
  · intro h r y hxy
    subst x
    exact h (hSU y.prop) r
  · intro h hx r
    by_cases hs : x∈S
    · exact h r ⟨x,hs⟩ rfl
    · exact hω r x hs

omit [Finite K] [FiniteDimensional K V] in
lemma publicDecoded_restrict (U S : Finset (ℙ K V)) (hSU : S⊆U)
    (O rawO : ℙ K V→Finset (ℙ K V)) (hO : ∀x,S∩rawO x=O x)
    (b : ℙ K V→ℝ) (z : ℕ) {R : ℕ}
    (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0) :
    publicDecoded U rawO b z ω=decoded U S O b z (fun r y=>ω r y) := by
  unfold publicDecoded decoded
  rw [publicSamples_restrict U S hSU ω hω]
  congr 1
  funext x
  exact publicScore_restrict S (O x) (rawO x) (hO x) (pencil x) (b x) ω hω

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory MeasurePublicTable
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma enclosure_success_mass (S U : Finset ι) (hS : S.Nonempty) (hSU : S⊆U)
    (rho : ℝ≥0) (R : ℕ) (K A : ℝ) (E : Set (Fin R→S→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K)
    (hprob : Real.exp (-A)≤(scheduleMeasure (fun _ : S=>rho/(S.card:ℝ≥0)) R).real E) :
    Real.exp (-(Real.log ((U.card:ℝ)/S.card)*K+A))≤
      (scheduleMeasure (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0) R).real (ambientSuccess S E) := by
  have hh := enclosure_hidden_event_likelihood S U hS hSU rho R K E hsize
  calc
    _ = Real.exp (-Real.log ((U.card:ℝ)/S.card)*K)*Real.exp (-A) := by rw [←Real.exp_add];congr 1;ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hprob (Real.exp_nonneg _)).trans hh

theorem enclosure_search_failure (S U : Finset ι) (hS : S.Nonempty) (hSU : S⊆U)
    (rho : ℝ≥0) (R : ℕ) (K A q : ℝ) (hq : 0≤q) (E : Set (Fin R→S→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K)
    (hprob : Real.exp (-A)≤(scheduleMeasure (fun _ : S=>rho/(S.card:ℝ≥0)) R).real E) :
    let N := ⌈q*Real.exp (Real.log ((U.card:ℝ)/S.card)*K+A)⌉₊
    (Measure.pi (fun _ : Fin N=>scheduleMeasure (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0) R)).real
      {t | firstIndex (ambientSuccess S E) t=none}≤Real.exp (-q) := by
  dsimp only
  exact finite_cutoff_failure _ _ (Set.to_countable _ |>.measurableSet) hq _
    (enclosure_success_mass S U hS hSU rho R K A E hsize hprob) (Nat.le_ceil _)

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance MeasurePublicTable
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def trueScoreSuccess (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (b : ℙ K V→ℝ) (E : Finset (ℙ K (Dual K V))) (R : ℕ) (s M c : ℝ) : Set (Fin R→S→ℕ) :=
  {ω | let W := decoded U S O b (emptyTests E (hyperplaneSupport S) ω).card ω
    (sampleCount ω:ℝ)≤ s ∧ (W.card:ℝ)≤ M ∧ c≤((W∩S).card:ℝ)}

omit [Finite K] [FiniteDimensional K V] in
theorem public_table_decodes (U S : Finset (ℙ K V)) (hSU : S⊆U)
    (O rawO : ℙ K V→Finset (ℙ K V)) (hO : ∀x,S∩rawO x=O x)
    (b : ℙ K V→ℝ) (E : Finset (ℙ K (Dual K V))) (R : ℕ) (s M c : ℝ)
    {N : ℕ} (t : Fin N→Fin R→ℙ K V→ℕ) {i : Fin N}
    (hi : firstIndex (ambientSuccess S (trueScoreSuccess U S O b E R s M c)) t=some i) :
    ∃ z ≤ E.card, (sampleCount (t i):ℝ)≤ s ∧
      ((publicDecoded U rawO b z (t i)).card:ℝ)≤ M ∧
      c≤(((publicDecoded U rawO b z (t i))∩S).card:ℝ) := by
  have hh := firstIndex_some_mem _ t hi
  change (∀r y,y∉S → t i r y=0) ∧
    (fun r (y : S)=>t i r y)∈trueScoreSuccess U S O b E R s M c at hh
  let ω : Fin R→S→ℕ := fun r y=>t i r y
  let z := (emptyTests E (hyperplaneSupport S) ω).card
  refine ⟨z,Finset.card_le_card (Finset.filter_subset _ _),?_,?_,?_⟩
  · rw [sampleCount_restrict S (t i) hh.1]
    exact hh.2.1
  · rw [publicDecoded_restrict U S hSU O rawO hO b z (t i) hh.1]
    exact hh.2.2.1
  · rw [publicDecoded_restrict U S hSU O rawO hO b z (t i) hh.1]
    exact hh.2.2.2

end SharpRamseyFive.ScoreGeometry

end OAI
