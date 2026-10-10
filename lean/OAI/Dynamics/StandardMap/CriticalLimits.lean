import OAI.Dynamics.StandardMap.NonaffineLimits

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal CompactlySupported Classical
namespace StandardMapEntropy
lemma vague_zero_of_tests {ι : Type*} (l : Filter ι) (μ : ι → Measure DistanceArray)
    [∀ i, IsFiniteMeasure (μ i)]
    (ht : ∀ j : ArrayTestIndex,Tendsto (fun i => ∫ d,arrayTest j d ∂μ i) l (𝓝 0))
    (g : C_c(NonAffineArray,ℝ)) : Tendsto (fun i => ∫ d,g d ∂nonaffinePart (μ i)) l (𝓝 0) := by
  obtain ⟨t,C,hC,hdom⟩ := compact_test_domination g
  have hsum : Tendsto (fun i => ∑ j∈t,∫ d,arrayTest j d ∂μ i) l (𝓝 0) := by
    simpa using tendsto_finsetSum t (fun j hj => ht j)
  have hbound := fun i => cc_integral_nonaffine_bound (μ i) g t C hC hdom
  apply squeeze_zero_norm (fun i => by simpa only [Real.norm_eq_abs] using hbound i)
  simpa only [mul_zero] using hsum.const_mul C
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
lemma initial_vague_zero (g : C_c(NonAffineArray,ℝ)) :
    Tendsto (fun i => ∫ d,g d ∂nonaffinePart (S.initialLaw i)) atTop (𝓝 0) :=
  vague_zero_of_tests atTop S.initialLaw S.initialLaw_test_tendsto g

structure LimitLaws where
  filter : Ultrafilter ℕ
  refines : (filter : Filter ℕ) ≤ atTop
  multi : Measure NonAffineArray
  terminal : Measure NonAffineArray
  multi_regular : multi.Regular
  terminal_regular : terminal.Regular
  multi_local : IsFiniteMeasureOnCompacts multi
  terminal_local : IsFiniteMeasureOnCompacts terminal
  multi_converges : ∀ g : C_c(NonAffineArray,ℝ),
    Tendsto (fun i => ∫ d,g d ∂nonaffinePart (S.multiLaw i)) (filter:Filter ℕ) (𝓝 (∫ d,g d ∂multi))
  terminal_converges : ∀ g : C_c(NonAffineArray,ℝ),
    Tendsto (fun i => ∫ d,g d ∂nonaffinePart (S.terminalLaw i)) (filter:Filter ℕ) (𝓝 (∫ d,g d ∂terminal))
lemma exists_limitLaws : Nonempty (S.LimitLaws) := by
  let l : Ultrafilter ℕ := Ultrafilter.of atTop
  have hl : (l:Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨μ,hμr,hμl,hμ⟩ := exists_nonaffine_vague_limit l S.multiLaw (fun j => by
    obtain ⟨C,hC⟩ := S.multiLaw_test_bound j
    exact ⟨C,hl hC⟩)
  obtain ⟨ν,hνr,hνl,hν⟩ := exists_nonaffine_vague_limit l S.terminalLaw (fun j => by
    obtain ⟨C,hC⟩ := S.terminalLaw_test_bound j
    exact ⟨C,hl hC⟩)
  exact ⟨⟨l,hl,μ,ν,hμr,hνr,hμl,hνl,hμ,hν⟩⟩
end CriticalScaleSequence
end StandardMapEntropy

end OAI
