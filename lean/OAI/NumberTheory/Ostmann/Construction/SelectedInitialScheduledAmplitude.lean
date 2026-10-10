import OAI.NumberTheory.Ostmann.Construction.SelectedInitialMovingAmplitude
import OAI.NumberTheory.Ostmann.Construction.ScheduledAmplitude
import OAI.NumberTheory.Ostmann.Construction.SmoothLogCellProfile

namespace OAI

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem selected_initial_frozen_scheduled_amplitude
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D Qd : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) centers targets)
    (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)] (hP : ∀ p ∈ P, p.Prime)
    (b d : ℕ) (μb : P → ℝ) (sl sr : Fin d → P)
    (hdistinct : Function.Injective (Fin.append sl sr))
    (hsl : ∀ i, (sl i : ℕ) ∈ Qd) (hsr : ∀ i, (sr i : ℕ) ∈ Qd) (fallback : P)
    (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool) (ψ : 𝓢(ℝ, ℂ))
    (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ) (φ : ℝ → ℝ) (Gseq : ℕ → ℝ)
    (hV0 : (V 0 : ℝ) < Real.exp (G - 1)) :
    let cells := initialSmallCellList top centers
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y endpoint D (cells.get i))
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append sl sr i).property)
        (hP _ (Fin.append sl sr j).property)).mpr (fun h => hij (hdistinct (Subtype.ext h)))
    let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
    let F := movingOriginalLeaf (fun p : P => (p : ℕ)) q
      (initialMovingDataCutoff (fun p : P => (p : ℕ)) b d cells.length cb cd sl sr fallback)
      (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) Finset.univ
      (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ))
      (Real.exp (Δ - 2 * (cells.length + 3))) (Real.exp (Δ + 2 * (cells.length + 3)))
    initialFrozenAmplitude P b d cells.length (smoothGiantPrior P logCellProfile G) (fun _ => μb) μc
      (Fin.append (primeHalfTests (n := b + (d + cells.length)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + cells.length)) P (fun p => S p) (fun p => fav p)))
      ψ (Real.exp Y) (V 0)
      (doubledHalfWeight (fun x : Fin (b + (d + cells.length) + 1) → P =>
        (initialHalfCutoffWeight (fun p : P => (p : ℕ)) b d cells.length cb cd (Fin.tail x) : ℂ))) sl sr =
    scheduledCellAmplitude (fun p : P => (p : ℕ)) (List.ofFn q) μ childBound pivotBound V
      F φ Gseq P (smoothGiantPrior P logCellProfile G)
      (fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y endpoint D c)) μb
      top centers 0 (b + b) (normalizedResidueFamily S) (normalizedResidueFamily S) fav := by
  intro cells μc Δ q hc inst F
  have hlarge (p : P) (hp : smoothGiantPrior P logCellProfile G p ≠ 0) : V 0 < (p : ℕ) := by
    have hp' := (smoothGiantPrior_active_bounds P hP logCellProfile G
      logCellProfile_zero_outside p hp).1
    exact_mod_cast hV0.trans hp'
  have he := selected_initial_frozen_moving_amplitude (cb := cb) (cd := cd) htop hcenters P hP b d (fun _ => μb)
    sl sr hdistinct hsl hsr fallback S fav ψ μ childBound pivotBound V φ Gseq hlarge
  refine he.trans ?_
  exact movingTemplatePrimeAmplitude_initial_schedule Subtype.val
    (fun p => (hP p p.property).ne_zero) b d top centers cb cd sl sr fallback
    q (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) Finset.univ
    (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ)) (Real.exp (Δ - 2 * (cells.length + 3)))
    (Real.exp (Δ + 2 * (cells.length + 3))) (List.ofFn q) μ childBound pivotBound V φ Gseq
    P (fun p hp => (hP p hp).ne_zero) (smoothGiantPrior P logCellProfile G)
    (fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y endpoint D c)) μb
    (normalizedResidueFamily S) (normalizedResidueFamily S) fav

end Ostmann

end OAI
