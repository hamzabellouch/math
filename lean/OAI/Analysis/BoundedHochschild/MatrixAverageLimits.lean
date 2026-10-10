import OAI.Analysis.BoundedHochschild.FiniteGroupMultimodularity
import OAI.Analysis.BoundedHochschild.CountableMatrixGroups

namespace OAI

/-! Finite matrix-section averages and passage of their module identities
through a bounded pointwise weak-star limit. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
lemma predualTendsto_congr_eventually (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type v} {l : Filter I} {a b : I → M} {c : M}
    (hab : a =ᶠ[l] b) (ha : PredualTendsto e a l c) : PredualTendsto e b l c := by
  intro z
  exact (ha z).congr' (hab.mono (fun i hi => congrArg (fun d : M => e.symm d z) hi))

lemma multimodularAt_of_predualTendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type v} {l : Filter I} [l.NeBot] {n : ℕ}
    (F : I → Cochain M (n + 1)) (f : Cochain M (n + 1)) (r : M)
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (f x))
    (hF : ∀ᶠ i in l, MultimodularAt (F i) r) : MultimodularAt f r := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hR := (HochschildSakai.abstract_multiplication_normal e).2
  constructor
  · intro x
    apply predual_tendsto_unique e (ht (Function.update x 0 (r * x 0)))
    exact predualTendsto_congr_eventually e
      (hF.mono (fun i hi => (hi.left x).symm)) ((hL r).tendsto e (ht x))
  · intro x
    apply predual_tendsto_unique e (ht (Function.update x (Fin.last n) (x (Fin.last n) * r)))
    exact predualTendsto_congr_eventually e
      (hF.mono (fun i hi => (hi.right x).symm)) ((hR r).tendsto e (ht x))
  · intro x j
    apply predual_tendsto_unique e (ht (Function.update x j.castSucc (x j.castSucc * r)))
    exact predualTendsto_congr_eventually e
      (hF.mono (fun i hi => (hi.balance x j).symm))
      (ht (Function.update x j.succ (r * x j.succ)))

lemma exists_finite_matrix_section_average (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → HochschildComparison.PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (f : Cochain M (n + 1)) (k : ℕ) :
    ∃ (G : Type u) (_ : Group G) (_ : Fintype G) (ρ : G →* unitary M),
      (∀ g, (ρ g : M) ∈ countableMatrixClosure e c) ∧
      ‖finiteGroupCochainAverage ρ f‖ ≤ ‖f‖ ∧
      ∀ i j : Fin k, MultimodularAt (finiteGroupCochainAverage ρ f)
        (countableMatrixUnit c i.val j.val) := by
  obtain ⟨G, hG, hGF, ρ, hρ, hspan⟩ := finite_group_spans_matrix_section e c hi ho k
  let := hG
  let := hGF
  let _ : Fintype G := Fintype.ofFinite G
  exact ⟨G, hG, inferInstance, ρ, hρ, finiteGroupCochainAverage_norm ρ f,
    fun i j => finiteGroupCochainAverage_span ρ f (hspan i j)⟩

/-- This retains the limit of the supplied averages, so any separately
verified linear identity of those averages can be passed to the same limit. -/
theorem matrix_section_average_limit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → HochschildComparison.PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    {n : ℕ} (F : ℕ → Cochain M (n + 1)) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ k, ‖F k‖ ≤ C)
    (hmodule : ∀ k, ∀ i j : Fin k, MultimodularAt (F k) (countableMatrixUnit c i.val j.val)) :
    ∃ A : Cochain M (n + 1), ‖A‖ ≤ C ∧ MultimodularOver (countableMatrixAlgebra c) A ∧
      ∀ x, PredualTendsto e (fun k => F k x) (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ) (A x) := by
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨A, hA, ht⟩ := bounded_cochain_ultralimit e U F C hC hF
  refine ⟨A, hA, multimodular_of_matrixUnits c hi ho A (fun i j => ?_), ht⟩
  apply multimodularAt_of_predualTendsto e F A _ ht
  apply hU
  filter_upwards [eventually_gt_atTop (max i j)] with k hk
  exact hmodule k ⟨i, lt_of_le_of_lt (le_max_left i j) hk⟩
    ⟨j, lt_of_le_of_lt (le_max_right i j) hk⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
