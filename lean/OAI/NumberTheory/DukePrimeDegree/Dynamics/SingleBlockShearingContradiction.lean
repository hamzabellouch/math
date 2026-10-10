import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockGenericSet
import OAI.NumberTheory.DukePrimeDegree.Geometry.TerminalPairComparison

namespace OAI

/-!
# The fixed-window contradiction for a normalized transverse pair

All quantifiers retain the order needed by the argument: the compact
shell and its separating tests are fixed first, then the terminal
fraction and the generic set, and only then the nearby pair and its
root-dependent stopping times.  The limit is proved to lie in the shell
by its normalized matrix entries.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem singleBlock_fixed_window_contradiction {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n))
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
    (hsep : ∀ h ∈ transverseMatrixShell (blockComplementSetoid S) a,
      ∃ f ∈ F, ε < |invarianceDefect μ f h|)
    (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ < 1)
    (hwindow : ∀ (i j : Fin n) (hij : i ≠ j)
        (g : ℕ → G n) (T : ℕ → ℝ),
        (∀ m, 0 < T m) →
        (∀ m, ∀ t ∈ Icc 0 (T m), rootShearSize hij (g m) t ≤ a) →
        ∀ h ∈ transverseMatrixShell (blockComplementSetoid S) a,
          Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
            Matrix.SpecialLinearGroup.transvection hij (-(T m))) atTop (𝓝 h) →
          ∀ᶠ m in atTop, ∀ s ∈ Icc (1 - δ) 1, ∀ f ∈ F, ∀ x : X n,
            |f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (s * T m) *
                g m * Matrix.SpecialLinearGroup.transvection hij (-(s * T m)))) -
              f (rightAction x h)| < ε / 4)
    (E : Set (X n)) (R : ℝ)
    (hgood : ∀ x ∈ E, ∀ i ∈ S, ∀ j ∈ S, ∀ (hij : i ≠ j), ∀ f ∈ F, ∀ T ≥ R,
      |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
        f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t)))) -
          ∫ y, f y ∂μ| ≤ ε / 4 ∧
      ∀ h ∈ transverseMatrixShell (blockComplementSetoid S) a,
        |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
          f (rightAction (rightAction x
            (Matrix.SpecialLinearGroup.transvection hij (-t))) h)) -
              ∫ y, f (rightAction y h) ∂μ| ≤ ε / 4)
    (p q : ℕ → X n) (g : ℕ → G n) (c : ℕ → ℝ)
    (hg : Tendsto g atTop (𝓝 1))
    (hpq : ∀ m, q m = rightAction (p m) (g m) ∧
      g m ∉ blockMatrixGroup (blockComplementSetoid S))
    (hE : ∀ᶠ m in atTop, p m ∈ E ∧ q m ∈ E)
    (hpart : ∀ᶠ m in atTop,
      (∀ i ∈ S, (g m).val i i = c m) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g m).val i j = 0) : False := by
  obtain ⟨i, j, hij, hi, hj, φ, T, h, hφ, hTtop, _hne, _hout,
    hdiff, hlim, hT, _hcentral⟩ :=
    exists_singleBlock_transverse_shearing_limit S k l hkl hk hl g hg
      (fun m => (hpq m).2) c hpart a ha
  have hh : h ∈ transverseMatrixShell (blockComplementSetoid S) a := by
    refine ⟨?_, hdiff⟩
    apply singleBlock_conjugation_limit_withinPart S (g ∘ φ)
      (fun m => Matrix.SpecialLinearGroup.transvection hij (T m)) (c ∘ φ)
      (hg.comp hφ.tendsto_atTop)
      (fun m => root_mem_singleBlockRootGroup S i hi j hj hij (T m))
      (hφ.tendsto_atTop.eventually hpart) h
    simpa only [Function.comp_apply, Matrix.SpecialLinearGroup.transvection_inv] using hlim
  obtain ⟨f, hf, hfh⟩ := hsep h hh
  have hclose := hwindow i j hij (g ∘ φ) T (fun m => (hT m).1)
    (fun m => (hT m).2.2) h hh hlim
  obtain ⟨m, ⟨hmclose, hmE⟩, hmR⟩ :=
    ((hclose.and (hφ.tendsto_atTop.eventually hE)).and
      (hTtop.eventually (eventually_ge_atTop R))).exists
  let P (t : ℝ) := rightAction (p (φ m)) (Matrix.SpecialLinearGroup.transvection hij (-t))
  let Q (t : ℝ) := rightAction (q (φ m)) (Matrix.SpecialLinearGroup.transvection hij (-t))
  have hP : Continuous P := (continuous_rightAction_uncurry n).comp
    (continuous_const.prodMk ((continuous_rootTransvection hij).comp continuous_neg))
  have hQ : Continuous Q := (continuous_rightAction_uncurry n).comp
    (continuous_const.prodMk ((continuous_rootTransvection hij).comp continuous_neg))
  apply no_terminal_pair_with_separated_defect μ f h P Q hP hQ δ (T m) ε
    hδ (hT m).1 hε hfh
  · exact (hgood (p (φ m)) hmE.1 i hi j hj hij f hf (T m) hmR).2 h hh
  · exact (hgood (q (φ m)) hmE.2 i hi j hj hij f hf (T m) hmR).1
  · intro t ht
    have hTm : 0 < T m := (hT m).1
    have hs : t / T m ∈ Icc (1 - δ) 1 := by
      constructor
      · exact (le_div_iff₀ hTm).mpr ht.1
      · exact (div_le_iff₀ hTm).mpr (by simpa only [one_mul] using ht.2)
    have hc := hmclose (t / T m) hs f hf (P t)
    rw [div_mul_cancel₀ t (ne_of_gt hTm)] at hc
    simp only [Function.comp_apply] at hc
    have heq : Q t = rightAction (P t)
        (Matrix.SpecialLinearGroup.transvection hij t * g (φ m) *
          Matrix.SpecialLinearGroup.transvection hij (-t)) := by
      dsimp only [Q, P]
      rw [(hpq (φ m)).1]
      exact reverse_root_pair_displacement hij (p (φ m)) (g (φ m)) t
    rw [← heq] at hc
    exact (by simpa only [abs_sub_comm] using hc.le)

end DukePrimeDegree

end

end OAI
