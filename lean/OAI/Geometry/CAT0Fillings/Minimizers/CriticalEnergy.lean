import Mathlib
import OAI.Geometry.CAT0Fillings.Minimizers.WeakSequence

namespace OAI

section

open Set Filter Metric TopologicalSpace
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {H E F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [SeparableSpace H] in
lemma inner_tendsto_map [SeparableSpace H] (I : H →L[ℝ] E) {u : ℕ → H} {v : H}
    (h : ∀ w, Tendsto (fun j => inner ℝ (u j) w) atTop (𝓝 (inner ℝ v w))) (w : E) :
    Tendsto (fun j => inner ℝ (I (u j)) w) atTop (𝓝 (inner ℝ (I v) w)) := by
  simpa only [ContinuousLinearMap.adjoint_inner_right] using h (I.adjoint w)

lemma exists_weak_strong_subsequence (I : H →L[ℝ] E) (hI : IsCompactOperator I)
    (u : ℕ → H) (M : ℝ) (hM : ∀ j, ‖u j‖ ≤ M) :
    ∃ v : H, ‖v‖ ≤ M ∧ ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ w, Tendsto (fun j => inner ℝ (u (s j)) w) atTop (𝓝 (inner ℝ v w))) ∧
      Tendsto (fun j => I (u (s j))) atTop (𝓝 (I v)) := by
  obtain ⟨v,hv,s,hs,hw⟩ := exists_inner_weak_subsequence u M hM
  have hc := hI.isCompact_closure_image_closedBall M
  have hmem (j : ℕ) : I (u (s j)) ∈ closure (I '' closedBall (0 : H) M) :=
    subset_closure ⟨u (s j),by simpa using hM (s j),rfl⟩
  obtain ⟨z,hz,t,ht,hl⟩ := hc.isSeqCompact hmem
  have hweak (w : H) := (hw w).comp ht.tendsto_atTop
  have heq : z = I v := by
    apply ext_inner_right ℝ
    intro w
    have h1 : Tendsto (fun j => inner ℝ (I (u (s (t j)))) w) atTop (𝓝 (inner ℝ z w)) :=
      (show Continuous (fun x : E => inner ℝ x w) from continuous_id.inner continuous_const).continuousAt.tendsto.comp hl
    have h2 := inner_tendsto_map I (u := fun j => u (s (t j))) hweak w
    exact tendsto_nhds_unique h1 h2
  exact ⟨v,hv,s ∘ t,hs.comp ht,hweak,by simpa [heq,Function.comp_def] using hl⟩

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter Metric TopologicalSpace
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {H E F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def energy (I : H →L[ℝ] E) (G : H →L[ℝ] F) (A B : ℝ) (u : H) : ℝ :=
  A*‖G u‖^2+B*‖I u‖^2

omit [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F] in
lemma energy_nonneg [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F]
    (I : H →L[ℝ] E) (G : H →L[ℝ] F) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (u : H) : 0 ≤ energy I G A B u := by
  exact add_nonneg (mul_nonneg hA (sq_nonneg _)) (mul_nonneg hB (sq_nonneg _))

omit [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F] in
lemma energy_smul [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F]
    (I : H →L[ℝ] E) (G : H →L[ℝ] F) (A B c : ℝ) (u : H) :
    energy I G A B (c • u) = c^2*energy I G A B u := by
  simp only [energy,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

lemma energy_defect (I : H →L[ℝ] E) (G : H →L[ℝ] F) (A B : ℝ)
    {u : ℕ → H} {v : H} {Λ : ℝ}
    (hweak : ∀ w, Tendsto (fun j => inner ℝ (u j) w) atTop (𝓝 (inner ℝ v w)))
    (hQ : Tendsto (fun j => energy I G A B (u j)) atTop (𝓝 Λ)) :
    Tendsto (fun j => energy I G A B (u j-v)) atTop (𝓝 (Λ-energy I G A B v)) := by
  have hG := inner_tendsto_map G hweak (G v)
  have hI := inner_tendsto_map I hweak (I v)
  have hh := ((hQ.sub ((hG.const_mul (2*A)).add (hI.const_mul (2*B)))).add_const
    (energy I G A B v))
  simp only [real_inner_self_eq_norm_sq] at hh
  convert hh using 1
  · ext j
    simp only [energy,map_sub,norm_sub_sq_real]
    ring
  · congr 1
    dsimp [energy]
    ring

lemma energy_le_limit (I : H →L[ℝ] E) (G : H →L[ℝ] F) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {u : ℕ → H} {v : H} {Λ : ℝ}
    (hweak : ∀ w, Tendsto (fun j => inner ℝ (u j) w) atTop (𝓝 (inner ℝ v w)))
    (hQ : Tendsto (fun j => energy I G A B (u j)) atTop (𝓝 Λ)) :
    energy I G A B v ≤ Λ := by
  have hh := ge_of_tendsto' (energy_defect I G A B hweak hQ)
    (fun j => energy_nonneg I G hA hB (u j-v))
  linarith

end CAT0Fillings.AnalyticMinimizer
end

end OAI
