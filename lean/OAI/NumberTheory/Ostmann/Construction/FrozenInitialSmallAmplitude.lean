import OAI.NumberTheory.Ostmann.Construction.SelectedInitialScheduledAmplitude
import OAI.NumberTheory.Ostmann.Construction.ScheduledAmplitudeAlphabet
import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantAmbientAmplitude

namespace OAI

/-! # The constructed positive statistic on the actual regular-prime alphabet -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

def restrictPrimeSamples {P Q : Finset ℕ} {d : ℕ} (s : Fin d → P)
    (hs : ∀ i, (s i : ℕ) ∈ Q) : Fin d → Q := fun i => ⟨s i, hs i⟩

theorem restrictPrimeSamples_embedding {P Q : Finset ℕ} {d : ℕ} (hQP : Q ⊆ P)
    (s : Fin d → P) (hs : ∀ i, (s i : ℕ) ∈ Q) :
    primeAlphabetEmbedding hQP ∘ restrictPrimeSamples s hs = s := by
  funext i
  exact Subtype.ext rfl

theorem restrictPrimeSamples_append_injective {P Q : Finset ℕ} {d : ℕ}
    (sl sr : Fin d → P) (hl : ∀ i, (sl i : ℕ) ∈ Q) (hr : ∀ i, (sr i : ℕ) ∈ Q)
    (hinj : Function.Injective (Fin.append sl sr)) :
    Function.Injective (Fin.append (restrictPrimeSamples sl hl) (restrictPrimeSamples sr hr)) := by
  have hvalue (i : Fin (d + d)) :
      ((Fin.append (restrictPrimeSamples sl hl) (restrictPrimeSamples sr hr) i : Q) : ℕ) =
        ((Fin.append sl sr i : P) : ℕ) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right, restrictPrimeSamples]
  intro i j hij
  apply hinj
  apply Subtype.ext
  rw [← hvalue i, ← hvalue j, hij]

theorem frozen_initial_small_amplitude
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D Qd : Finset ℕ} {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) cs targets)
    (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)] (hP : ∀ p ∈ P, p.Prime)
    (hQP : initialRegularPrimeRange L ⊆ P)
    (hgiant : smoothGiantPrimeRange G ⊆ P)
    (bulk : Finset ℕ) (hbulk : bulk ⊆ initialRegularPrimeRange L)
    (b d : ℕ) (sl sr : Fin d → initialRegularPrimeRange L)
    (hinj : Function.Injective (Fin.append
      (primeAlphabetEmbedding hQP ∘ sl) (primeAlphabetEmbedding hQP ∘ sr)))
    (hsl : ∀ i, (sl i : ℕ) ∈ Qd) (hsr : ∀ i, (sr i : ℕ) ∈ Qd)
    (fallback : initialRegularPrimeRange L)
    (sets : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool) (ψ : 𝓢(ℝ, ℂ))
    (Qμ : ℕ → Finset ℕ) (childBound pivotBound V : ℕ → ℕ)
    (hV0 : (V 0 : ℝ) < Real.exp (G - 1)) :
    let Q := initialRegularPrimeRange L
    let e := primeAlphabetEmbedding hQP
    let cells := initialSmallCellList top cs
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append (e ∘ sl) (e ∘ sr) i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property)
        (hP _ (Fin.append (e ∘ sl) (e ∘ sr) j).property)).mpr
          (fun h => hij (hinj (Subtype.ext h)))
    let _ : ∀ i, Fact (q i).Prime := fun i =>
      ⟨hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property⟩
    let Δ := selectedInitialLogCenter G Y cb cd top cs
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d cells.length cb cd sl sr fallback)
      (fun i => normalizedResidueFamily sets (q i)) (initialSpectatorCofactor q hc) Finset.univ
      (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ))
      (Real.exp (Δ - 2 * (cells.length + 3))) (Real.exp (Δ + 2 * (cells.length + 3)))
    initialFrozenAmplitude P b d cells.length (smoothGiantPrior P logCellProfile G)
      (fun _ => primeSubsetPrior P bulk)
      (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y endpoint D (cells.get i)))
      (Fin.append (primeHalfTests (n := b + (d + cells.length)) P (fun p => sets p) (fun p => fav p))
        (primeHalfTests (n := b + (d + cells.length)) P (fun p => sets p) (fun p => fav p)))
      ψ (Real.exp Y) (V 0)
      (doubledHalfWeight (fun x : Fin (b + (d + cells.length) + 1) → P =>
        (initialHalfCutoffWeight Subtype.val b d cells.length cb cd (Fin.tail x) : ℂ)))
      (e ∘ sl) (e ∘ sr) =
    scheduledCellAmplitude Subtype.val (List.ofFn q) (fun j => primeSubsetPrior Q (Qμ j))
      childBound pivotBound V F logCellProfile (fun _ => G)
      (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
      (fun c => primeSubsetPrior Q (selectedTailCellPrimes A B N Y endpoint D c))
      (primeSubsetPrior Q bulk) top cs 0 (b + b)
      (normalizedResidueFamily sets) (normalizedResidueFamily sets) fav := by
  intro Q e cells q hc inst Δ F
  have hstart := selected_initial_frozen_scheduled_amplitude (cb := cb) (cd := cd) htop hcs P hP b d
    (primeSubsetPrior P bulk) (e ∘ sl) (e ∘ sr) hinj hsl hsr (e fallback) sets fav ψ
    (fun j => primeSubsetPrior P (Qμ j)) childBound pivotBound V logCellProfile (fun _ => G) hV0
  dsimp only at hstart
  unfold scheduledCellAmplitude at hstart
  rw [movingTemplatePrimeAmplitude_giant_ambient Subtype.val (List.ofFn q)
    (fun j => primeSubsetPrior P (Qμ j)) childBound pivotBound V _ logCellProfile
    (fun _ => G) 0 _ (b + b) P hP logCellProfile G logCellProfile_zero_outside hgiant] at hstart
  have halphabet := scheduledCellAmplitude_initial_prime_alphabet P Q hQP q (List.ofFn q)
    Qμ (selectedTailCellPrimes A B N Y endpoint D) bulk childBound pivotBound V b d top cs
    cb cd sl sr fallback (fun i => normalizedResidueFamily sets (q i))
    (initialSpectatorCofactor q hc) Finset.univ (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ))
    (Real.exp (Δ - 2 * (cells.length + 3))) (Real.exp (Δ + 2 * (cells.length + 3)))
    logCellProfile (fun _ => G) 0 (smoothGiantPrimeRange G)
    (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
    (fun j hj => by omega)
    (fun c hc => (Classical.choose_spec (initial_selected_cells_valid htop hcs c hc)).subset_initialRegularPrimeRange)
    hbulk (normalizedResidueFamily sets) (normalizedResidueFamily sets) fav
  exact hstart.trans halphabet

end Ostmann

end OAI
