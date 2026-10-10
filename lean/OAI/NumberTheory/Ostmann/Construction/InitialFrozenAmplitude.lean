import OAI.NumberTheory.Ostmann.Construction.InitialSpectatorWitness
import OAI.NumberTheory.Ostmann.Construction.RegularInitialAmplitude

namespace OAI

/-! # The actual Fourier amplitude with both spectator lists fixed -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def initialFrozenAmplitude (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (sl sr : Fin d → P) : ℂ :=
  let νr := Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)
  ∑ yl : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yl i) : ℝ) : ℂ) *
    ∑ yr : Unit ⊕ (Fin b ⊕ Fin r) → P, ((∏ i, νr i (yr i) : ℝ) : ℂ) *
      let x := Fin.append (initialHalfAssemble b d r sl yl) (initialHalfAssemble b d r sr yr)
      w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0

theorem regularInitialAmplitude_freeze (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ) :
    let ν := Fin.cons μg (Fin.append μb (Fin.append μd μc))
    regularInitialAmplitude P (Fin.append ν ν) F ψ X V w =
      ∑ sl : Fin d → P, (productPrior μd sl : ℂ) *
        ∑ sr : Fin d → P, (productPrior μd sr : ℂ) *
          initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr := by
  intro ν
  have hh := initial_doubled_prior_split b d r μg μb μd μc
    (fun x => w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0)
  simpa only [regularInitialAmplitude, initialFrozenAmplitude, mul_assoc] using hh

theorem exists_initial_frozen_amplitude (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (hμd : ∀ i p, 0 ≤ μd i p) (hμdmass : ∀ i, ∑ p, μd i p = 1)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ) (β : ℝ)
    (hβ : let ν := Fin.cons μg (Fin.append μb (Fin.append μd μc))
      β ≤ ‖regularInitialAmplitude P (Fin.append ν ν) F ψ X V w‖) :
    ∃ sl sr : Fin d → P,
      (∀ i, μd i (sl i) ≠ 0) ∧ (∀ i, μd i (sr i) ≠ 0) ∧
      β ≤ ‖initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr‖ := by
  dsimp only at hβ
  rw [regularInitialAmplitude_freeze] at hβ
  have hμ := productPrior_nonneg μd hμd
  have hm := productPrior_mass μd hμdmass
  obtain ⟨sl, hsl, hl⟩ := exists_supported_complex_mean_witness (productPrior μd) hμ hm _ β hβ
  obtain ⟨sr, hsr, hr⟩ := exists_supported_complex_mean_witness (productPrior μd) hμ hm _ β hl
  refine ⟨sl, sr, ?_, ?_, hr⟩
  · intro i
    exact (Finset.prod_ne_zero_iff.mp hsl.ne') i (Finset.mem_univ _)
  · intro i
    exact (Finset.prod_ne_zero_iff.mp hsr.ne') i (Finset.mem_univ _)

theorem initialFrozenAmplitude_support (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (sl sr : Fin d → P)
    (hne : initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr ≠ 0) :
    Function.Injective (Fin.append sl sr) := by
  unfold initialFrozenAmplitude at hne
  obtain ⟨yl, _, hyl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hyrsum := right_ne_zero_of_mul hyl
  obtain ⟨yr, _, hyr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hyrsum
  have hkernel := right_ne_zero_of_mul hyr
  have hfull : Function.Injective (Fin.append (initialHalfAssemble b d r sl yl)
      (initialHalfAssemble b d r sr yr)) := by
    by_contra hn
    simp only [hn, ite_false, mul_zero] at hkernel
    exact hkernel rfl
  exact initial_doubled_spectators_injective b d r sl sr yl yr hfull

theorem exists_distinct_initial_spectators (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (hμd : ∀ i p, 0 ≤ μd i p) (hμdmass : ∀ i, ∑ p, μd i p = 1)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (β : ℝ) (hβpos : 0 < β)
    (hβ : let ν := Fin.cons μg (Fin.append μb (Fin.append μd μc))
      β ≤ ‖regularInitialAmplitude P (Fin.append ν ν) F ψ X V w‖) :
    ∃ sl sr : Fin d → P, Function.Injective (Fin.append sl sr) ∧
      (∀ i, μd i (sl i) ≠ 0) ∧ (∀ i, μd i (sr i) ≠ 0) ∧
      β ≤ ‖initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr‖ := by
  obtain ⟨sl, sr, hsl, hsr, hlower⟩ := exists_initial_frozen_amplitude P b d r
    μg μb μd μc hμd hμdmass F ψ X V w β hβ
  have hne : initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr ≠ 0 :=
    norm_pos_iff.mp (hβpos.trans_le hlower)
  exact ⟨sl, sr, initialFrozenAmplitude_support P b d r μg μb μc F ψ X V w sl sr hne,
    hsl, hsr, hlower⟩

end Ostmann

end OAI
