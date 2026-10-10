import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockNoncentral
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCompactness

namespace OAI

/-!
# A transverse limit from actual normalized return matrices

The shearing root, diverging first stopping times and transverse limit
are all constructed. In particular, being outside the block group is
a conclusion about the limit, not an additional hypothesis imposed on
a subsequence.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixDifference_of_rootShearLimit {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (T : ℕ → ℝ) (a : ℝ)
    (hsize : ∀ m, rootShearSize hij (g m) (T m) = a)
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-(T m))) atTop (𝓝 h)) :
    slMatrixDifference h 1 = a := by
  have he := continuous_slMatrixDifference.continuousAt.tendsto.comp (hlim.prodMk_nhds hg)
  have hc : Tendsto (fun m => slMatrixDifference
      (Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-(T m))) (g m)) atTop (𝓝 a) := by
    simpa only [show ∀ m, slMatrixDifference
      (Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-(T m))) (g m) = a from hsize] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  exact tendsto_nhds_unique he hc

theorem exists_singleBlock_transverse_shearing_limit {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hout : ∀ m, g m ∉ blockMatrixGroup (blockComplementSetoid S))
    (c : ℕ → ℝ)
    (hpart : ∀ᶠ m in atTop,
      (∀ i ∈ S, (g m).val i i = c m) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g m).val i j = 0)
    (a : ℝ) (ha : 0 < a) :
    ∃ (i j : Fin n) (hij : i ≠ j), i ∈ S ∧ j ∈ S ∧
      ∃ (φ : ℕ → ℕ) (T : ℕ → ℝ) (h : G n),
        StrictMono φ ∧ Tendsto T atTop atTop ∧ h ≠ 1 ∧
        h ∉ blockMatrixGroup (blockComplementSetoid S) ∧
        slMatrixDifference h 1 = a ∧
        Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (T m) * g (φ m) *
          Matrix.SpecialLinearGroup.transvection hij (-(T m))) atTop (𝓝 h) ∧
        (∀ m, 0 < T m ∧ rootShearSize hij (g (φ m)) (T m) = a ∧
          ∀ t ∈ Icc 0 (T m), rootShearSize hij (g (φ m)) t ≤ a) ∧
        ∀ t : ℝ, h * Matrix.SpecialLinearGroup.transvection hij t =
          Matrix.SpecialLinearGroup.transvection hij t * h := by
  obtain ⟨i, j, hij, hi, hj, σ, hσ, hnoncentral⟩ :=
    exists_fixed_noncentral_root_subsequence S k l hkl hk hl g hout
  have hgσ : Tendsto (g ∘ σ) atTop (𝓝 1) := hg.comp hσ.tendsto_atTop
  obtain ⟨T, hTtop, hT⟩ := exists_diverging_first_rootShearScale hij (g ∘ σ)
    hgσ hnoncentral ha
  obtain ⟨h, hne, ψ, hψ, hlim, hcentral⟩ := exists_nontrivial_rootShearLimit hij
    (g ∘ σ) hgσ T (fun m => (hT m).1) hTtop ha (fun m => (hT m).2.1)
    (fun m => (hT m).2.2)
  have hdiff : slMatrixDifference h 1 = a := slMatrixDifference_of_rootShearLimit hij
    (g ∘ (σ ∘ ψ)) (hg.comp (hσ.comp hψ).tendsto_atTop) (T ∘ ψ) a
    (fun m => (hT (ψ m)).2.1) h hlim
  refine ⟨i, j, hij, hi, hj, σ ∘ ψ, T ∘ ψ, h, hσ.comp hψ,
    hTtop.comp hψ.tendsto_atTop, hne, ?_, hdiff, hlim, ?_, hcentral⟩
  · apply singleBlock_conjugation_limit_outside_blocks S
      (g ∘ (σ ∘ ψ)) (fun m => Matrix.SpecialLinearGroup.transvection hij (T (ψ m)))
      (c ∘ (σ ∘ ψ)) (hg.comp (hσ.comp hψ).tendsto_atTop)
      (fun m => root_mem_singleBlockRootGroup S i hi j hj hij (T (ψ m)))
      ((hσ.comp hψ).tendsto_atTop.eventually hpart) h hne
    simpa only [Function.comp_apply, Matrix.SpecialLinearGroup.transvection_inv] using hlim
  · intro m
    exact hT (ψ m)

end DukePrimeDegree

end

end OAI
