import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathConcatenation
import Mathlib.Algebra.Group.Subgroup.Basic

namespace OAI

/-! # Concatenating the bounded generator word

The one-letter visit is applied on each successive height-zero sheet. The
result is one continuous path to the whole word, with constants depending
only on the bounded number of letters.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G W I : Type*} [Group G] [PseudoMetricSpace G]
  [AddCommGroup W]

theorem exists_word_support_path
    (π : G →* Multiplicative W) (f : I → G) (P : I → Prop)
    (hπf : ∀ i, P i → π (f i) = 1)
    {S : Set G} (d₀ : G) (hbase : ∀ n, π n = 1 → n * d₀ ∈ S)
    {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hstep : ∀ n, π n = 1 → ∀ i, P i →
      ∃ γ : Path (n * d₀) (n * f i * d₀),
        PathMetricBound γ L κ ∧ ∀ t, γ t ∈ S)
    (u : List I) (hu : ∀ i ∈ u, P i) (n : G) (hn : π n = 1) :
    ∃ γ : Path (n * d₀) (n * (u.map f).prod * d₀),
      PathMetricBound γ (L * 2 ^ u.length) (κ * 2 ^ u.length) ∧ ∀ t, γ t ∈ S := by
  induction u generalizing n with
  | nil =>
    let γ : Path (n * d₀) (n * (([] : List I).map f).prod * d₀) :=
      (Path.refl (n * d₀)).cast rfl (by simp)
    refine ⟨γ, ?_, fun _ => hbase n hn⟩
    intro s t
    change dist (n * d₀) (n * d₀) ≤ _
    simp only [dist_self, List.length_nil, pow_zero, mul_one]
    positivity
  | cons i u ih =>
    have hi := hu i List.mem_cons_self
    have hu' : ∀ j ∈ u, P j := fun j hj => hu j (List.mem_cons_of_mem i hj)
    obtain ⟨γ, hγ, hγS⟩ := hstep n hn i hi
    have hn' : π (n * f i) = 1 := by rw [map_mul, hn, hπf i hi, one_mul]
    obtain ⟨δ, hδ, hδS⟩ := ih hu' (n * f i) hn'
    have hp : 1 ≤ (2 : ℝ) ^ u.length := one_le_pow₀ (by norm_num)
    have hγ' : PathMetricBound γ (L * 2 ^ u.length) (κ * 2 ^ u.length) :=
      hγ.mono (by nlinarith) (by nlinarith)
    let ε : Path (n * d₀) (n * ((i :: u).map f).prod * d₀) :=
      (γ.trans δ).cast rfl (by simp [mul_assoc])
    refine ⟨ε, ?_, path_trans_range_mem hγS hδS⟩
    have hb := (hγ'.trans (mul_nonneg hκ (by positivity)) hδ).cast rfl
      (show n * ((i :: u).map f).prod * d₀ = (n * f i) * (u.map f).prod * d₀ by
        simp [mul_assoc])
    convert hb using 1 <;> simp only [List.length_cons, pow_succ] <;> ring

end PolycyclicRecognition

end

end OAI
