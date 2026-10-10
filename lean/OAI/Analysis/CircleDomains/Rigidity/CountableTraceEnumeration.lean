import OAI.Analysis.CircleDomains.Rigidity.MatchedRoundDisks

namespace OAI

/-! Enumerate a countable family without repetitions. Missing natural
codes carry zero radii, so empty and finite families use the same bounds. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 def traceEnumeration {ι E : Type*} [Encodable ι] (v : ι → E) (fallback : E) : ℕ → E :=
  Function.extend Encodable.encode v (fun _ => fallback)

 theorem traceEnumeration_encode {ι E : Type*} [Encodable ι] (v : ι → E) (e : E) (i : ι) :
    traceEnumeration v e (Encodable.encode i) = v i :=
  Encodable.encode_injective.extend_apply v (fun _ => e) i

 theorem traceEnumeration_missing {ι E : Type*} [Encodable ι] (v : ι → E) (e : E)
    {n : ℕ} (hn : n ∉ Set.range (Encodable.encode : ι → ℕ)) : traceEnumeration v e n = e :=
  Function.extend_apply' v (fun _ => e) n hn

 theorem traceEnumeration_map {ι E F : Type*} [Encodable ι] (v : ι → E) (e : E) (g : E → F) :
    (fun n => g (traceEnumeration v e n)) = traceEnumeration (g ∘ v) (g e) := by
  funext n
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨i,rfl⟩ := hn
    simp only [traceEnumeration_encode,comp_apply]
  · rw [traceEnumeration_missing v e hn,traceEnumeration_missing _ _ hn]

 theorem traceEnumeration_nonneg {ι : Type*} [Encodable ι] {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) : ∀ n, 0 ≤ traceEnumeration v 0 n := by
  intro n
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨i,rfl⟩ := hn
    rw [traceEnumeration_encode]
    exact hv i
  · rw [traceEnumeration_missing v 0 hn]

 theorem traceEnumeration_summable_sq {ι : Type*} [Encodable ι] {v : ι → ℝ}
    (hv : Summable (fun i => v i^2)) : Summable (fun n => traceEnumeration v 0 n^2) := by
  rw [traceEnumeration_map v 0 (fun t : ℝ => t^2)]
  simp only [Function.comp_def,zero_pow (by norm_num : (2:ℕ) ≠ 0),traceEnumeration]
  exact (summable_extend_zero Encodable.encode_injective).mpr hv

 theorem traceEnumeration_ball_disjoint {ι : Type*} [Encodable ι]
    {c : ι → ℂ} {r : ι → ℝ}
    (hd : Pairwise (Disjoint on fun i => ball (c i) (r i))) (fallback : ℂ) :
    Pairwise (Disjoint on fun n => ball (traceEnumeration c fallback n) (traceEnumeration r 0 n)) := by
  intro m n hmn
  change Disjoint (ball (traceEnumeration c fallback m) (traceEnumeration r 0 m))
    (ball (traceEnumeration c fallback n) (traceEnumeration r 0 n))
  by_cases hm : m ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨i,rfl⟩ := hm
    rw [traceEnumeration_encode,traceEnumeration_encode]
    by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
    · obtain ⟨j,rfl⟩ := hn
      rw [traceEnumeration_encode,traceEnumeration_encode]
      exact hd (fun hij => hmn (congrArg Encodable.encode hij))
    · rw [traceEnumeration_missing r 0 hn,ball_zero]
      exact disjoint_empty _
  · rw [traceEnumeration_missing r 0 hm,ball_zero]
    exact empty_disjoint _

end CircleDomainRigidity

end

end OAI
