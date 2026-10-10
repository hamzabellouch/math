import OAI.GroupTheory.PolycyclicRecognition.Analysis.SuccessfulBlockPaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SuccessfulSamplePaths

namespace OAI

/-! # Separate geometric paths for successive sampled bundles -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {N G : Type*} [Group N] [Group G]

/-- The actual difference word of one block of the global sample vector. -/
def sampledBlockWord {h m : ℕ} (sample : ℕ → ℝ → N)
    (t : Fin (h * m + h * m) → ℝ) (i : Fin h) : List N :=
  List.ofFn (fun j : Fin m => sample (finProdFinEquiv (i, j)).val
    (t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
      t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))))

/-- Products of complete sampled blocks, extended by the identity. -/
def sampledBlockProducts {h m : ℕ} (sample : ℕ → ℝ → N)
    (t : Fin (h * m + h * m) → ℝ) (j : ℕ) : N :=
  if hj : j < h then (sampledBlockWord sample t ⟨j, hj⟩).prod else 1

variable [PseudoMetricSpace G] [IsTopologicalGroup G]

/-- A single block inherits successful sheets from the global coupled
sample. Its geometric path may use a block-specific template. -/
theorem successful_sample_block_path {h m : ℕ}
    (ι : N →* G) (x d₀ : G) (A : Set N) (S : Set G)
    (sample : ℕ → ℝ → N)
    (hsub : ∀ j s t, sample j s * (sample j t)⁻¹ = sample j (s - t))
    (i : Fin h)
    (d : Fin m → ℝ → G) (hd : ∀ j, Continuous (d j)) (hd₀ : ∀ j, d j 0 = 1)
    (hf : ∀ j : Fin m, Continuous (fun b => ι (sample (finProdFinEquiv (i, j)).val b)))
    (hf₀ : ∀ j : Fin m, ι (sample (finProdFinEquiv (i, j)).val 0) = 1)
    (r : ℝ) {L κ ρ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hbase : ∀ n ∈ A, x * ι n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ j : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ →
      n * sample (finProdFinEquiv (i, j)).val b ∈ A →
      PathMetricBound (supportVisitPath (d j) (hd j) (hd₀ j)
        (fun t => ι (sample (finProdFinEquiv (i, j)).val t)) (hf j) (hf₀ j)
        (x * ι n) d₀ r b) L κ ∧
      ∀ t, supportVisitPath (d j) (hd j) (hd₀ j)
        (fun t => ι (sample (finProdFinEquiv (i, j)).val t)) (hf j) (hf₀ j)
        (x * ι n) d₀ r b t ∈ S)
    (hinj : Function.Injective ι)
    (n : N) (hn : n ∈ A) (t : Fin (h * m + h * m) → ℝ) (ht : ‖t‖ ≤ ρ)
    (hs : SwitchSuccessful (fun _ => A) 0 (h * m) n
      (sampledSwitchParameters sample (h * m) t)) :
    let start := n * wordPrefix (sampledBlockProducts sample t) i.val
    ∃ γ : Path (x * ι start * d₀)
      (x * ι (start * (sampledBlockWord sample t i).prod) * d₀),
      PathMetricBound γ (L * 2 ^ m) (κ * 2 ^ m) ∧ ∀ u, γ u ∈ S := by
  dsimp only
  let w : ℕ → List N := fun j =>
    if hj : j < h then sampledBlockWord sample t ⟨j, hj⟩ else []
  have hw : (fun j => (w j).prod) = sampledBlockProducts sample t := by
    funext j
    dsimp only [w, sampledBlockProducts]
    split_ifs <;> rfl
  have hgood := wordSheetsGood_sampled A sample hsub (h * m) t n hn hs
  rw [ofFn_eq_flatten_bundles] at hgood
  have hgood' : WordSheetsGood A n (List.ofFn (fun j : Fin h => w j.val)).flatten := by
    simpa only [w, sampledBlockWord, dite_eq_left (Fin.isLt _)] using hgood
  have hb := hgood'.ofFn_block w i
  rw [hw] at hb
  have hwi : w i.val = sampledBlockWord sample t i := by simp only [w, dite_eq_left i.isLt]
  rw [hwi] at hb
  let start := n * wordPrefix (sampledBlockProducts sample t) i.val
  let f : Fin m → ℝ → G := fun j b => ι (sample (finProdFinEquiv (i, j)).val b)
  let word := List.ofFn (fun j : Fin m =>
    (j, t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
      t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))))
  have hg : WordSheetsGood ((fun v => x * ι v) '' A) (x * ι start)
      (word.map (fun z => f z.1 z.2)) := by
    simpa only [word, List.map_ofFn, f, Function.comp_def, sampledBlockWord]
      using hb.map_mul_hom ι x
  have hparam : ∀ z ∈ word, |z.2| ≤ 2 * ρ := by
    intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    have h₁ := (norm_le_pi_norm t (Fin.castAdd (h * m) (finProdFinEquiv (i, j)))).trans ht
    have h₂ := (norm_le_pi_norm t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))).trans ht
    have hh := abs_sub (t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))))
      (t (Fin.natAdd (h * m) (finProdFinEquiv (i, j))))
    rw [Real.norm_eq_abs] at h₁ h₂
    linarith
  obtain ⟨hbound, hrange⟩ := supportWordPath_good_bound d f hd hf hd₀ hf₀ d₀ r
    ((fun v => x * ι v) '' A) S (fun _ b => |b| ≤ 2 * ρ) hL hκ
    (by rintro _ ⟨v, hv, rfl⟩; exact hbase v hv)
    (by
      rintro _ ⟨v, hv, rfl⟩ j b hbj ⟨z, hz, he⟩
      have hv' : v * sample (finProdFinEquiv (i, j)).val b ∈ A := by
        have he' : z = v * sample (finProdFinEquiv (i, j)).val b :=
          hinj (by simpa [map_mul, mul_assoc, f] using he)
        exact he' ▸ hz
      exact hstep v hv j b hbj hv') word hparam (x * ι start) hg
  let γ := supportWordPath d f hd hf hd₀ hf₀ d₀ r word (x * ι start)
  have hend : x * ι (start * (sampledBlockWord sample t i).prod) * d₀ =
      (x * ι start) * indexedWordProduct f word * d₀ := by
    simp only [map_mul, map_list_prod, List.map_ofFn, indexedWordProduct,
      word, f, sampledBlockWord, Function.comp_def, mul_assoc]
  refine ⟨γ.cast rfl hend, ?_, hrange⟩
  change PathMetricBound γ (L * 2 ^ m) (κ * 2 ^ m)
  simpa only [word, List.length_ofFn] using hbound

end PolycyclicRecognition

end

end OAI
