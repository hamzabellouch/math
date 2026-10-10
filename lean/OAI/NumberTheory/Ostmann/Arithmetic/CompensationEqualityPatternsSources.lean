import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatterns

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.CompensationEqualityPatterns
open Construction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commonCandidates (sources : SourceFamily) (origin : ι → ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun i => (sources (origin i)).candidates

abbrev CommonSample (sources : SourceFamily) (origin : ι → ℕ) :=
  ↥(commonCandidates sources origin)

abbrev IndependentSamples (sources : SourceFamily) (origin : ι → ℕ) :=
  ∀ i, (sources (origin i)).Sample

def sourceEmbed (sources : SourceFamily) (origin : ι → ℕ) (i : ι)
    (v : (sources (origin i)).Sample) : CommonSample sources origin :=
  ⟨v.val, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, v.property⟩⟩

def tupleEmbed (sources : SourceFamily) (origin : ι → ℕ)
    (x : IndependentSamples sources origin) : ι → CommonSample sources origin :=
  fun i => sourceEmbed sources origin i (x i)

omit [DecidableEq ι] in
theorem tupleEmbed_injective (sources : SourceFamily) (origin : ι → ℕ) :
    Function.Injective (tupleEmbed sources origin) := by
  intro x y h
  funext i
  apply Subtype.ext
  exact congrArg (fun v : CommonSample sources origin => v.val) (congrFun h i)

def sourceWeight (sources : SourceFamily) (origin : ι → ℕ) (i : ι)
    (v : CommonSample sources origin) : ℝ :=
  if h : v.val ∈ (sources (origin i)).candidates then
    (sources (origin i)).law.mass ⟨v.val, h⟩ else 0

omit [DecidableEq ι] in
@[simp] theorem sourceWeight_embed (sources : SourceFamily) (origin : ι → ℕ) (i : ι)
    (v : (sources (origin i)).Sample) :
    sourceWeight sources origin i (sourceEmbed sources origin i v) =
      (sources (origin i)).law.mass v := by
  simp [sourceWeight, sourceEmbed, v.property]

omit [DecidableEq ι] in
theorem sourceWeight_nonneg (sources : SourceFamily) (origin : ι → ℕ) (i : ι)
    (v : CommonSample sources origin) : 0 ≤ sourceWeight sources origin i v := by
  unfold sourceWeight
  split_ifs
  · exact (sources (origin i)).law.mass_nonneg _
  · exact le_rfl

theorem source_sum_eq_common (sources : SourceFamily) (origin : ι → ℕ)
    (F : (ι → CommonSample sources origin) → ℂ) :
    (∑ x : IndependentSamples sources origin,
      (∏ i, (sources (origin i)).law.mass (x i)) • F (tupleEmbed sources origin x)) =
      ∑ w : ι → CommonSample sources origin,
        (∏ i, sourceWeight sources origin i (w i)) • F w := by
  apply Fintype.sum_of_injective (tupleEmbed sources origin) (tupleEmbed_injective sources origin)
  · intro w hw
    have hn : ¬ ∀ i, (w i).val ∈ (sources (origin i)).candidates := by
      intro hs
      apply hw
      refine ⟨fun i => ⟨(w i).val, hs i⟩, ?_⟩
      funext i
      apply Subtype.ext
      rfl
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hz : (∏ j, sourceWeight sources origin j (w j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [sourceWeight, hi])
    simp only [hz, zero_smul]
  · intro x
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact (sourceWeight_embed sources origin i (x i)).symm

theorem source_cmean_eq_patterns (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : (ι → CommonSample sources origin) → ℂ) :
    (dependentProductPrior (fun i => (sources (origin i)).law)).cmean
        (fun x => F (tupleEmbed sources origin x)) =
      ∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
        (∏ q : Block p, blockWeight p (sourceWeight sources origin) q (b.val q)) •
          F (expand p b) := by
  have h := source_sum_eq_common sources origin F
  have h' := product_weighted_sum_eq_patterns τ (sourceWeight sources origin) F
  apply Eq.trans _ (h.trans h')
  unfold FinitePrior.cmean dependentProductPrior
  rfl

omit [DecidableEq ι] in
theorem commonSample_prime (sources : SourceFamily) (origin : ι → ℕ)
    (v : CommonSample sources origin) : Nat.Prime v.val := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp v.property
  exact (sources (origin i)).prime _ hi

omit [DecidableEq ι] in
theorem source_product_by_multiplicity (sources : SourceFamily) (origin τ : ι → ℕ)
    (p : Pattern τ) (b : BlockDraw p (CommonSample sources origin)) :
    (∏ i, (((expand p b i).val : ℕ) : ℝ)) =
      ∏ q : Block p, (((b.val q).val : ℕ) : ℝ) ^ multiplicity p q :=
  product_by_multiplicity p b (fun v => (v.val : ℝ))

end Ostmann.Arithmetic.CompensationEqualityPatterns

end

end OAI
