import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.SelectionLogBound

namespace OAI

section
namespace SharpLogRamsey.Selection
open Real Finset
open scoped Classical
noncomputable section
variable {Ω α : Type} [Fintype Ω] [Fintype α] [Nonempty α]

theorem selected_map_entropy {N ℓ d : ℕ} (hd : 1 ≤ d) (hℓ : 0 < ℓ) (hN : ℓ ≤ N)
    (p : Law Ω) (stream : Ω → Fin N → α) (F : Ω → Fin ℓ → α)
    (reverse : (Fin ℓ → α) → (Fin ℓ → α))
    {C q σ η c : ℝ} (hC : 0 < C) (hq : 0 < q) (hσ : 0 < σ) (hc : 0 < c)
    (hdom : ∀ g, (p.map stream).mass g ≤ C/(Fintype.card α:ℝ)^N)
    (hselect : ∀ x, p.mass x ≠ 0 → Occurs (F x) (stream x) ∨ Occurs (reverse (F x)) (stream x))
    (hsize : (N:ℝ) ≤ q^d*σ) (hlength : c*q*σ^(1+η) ≤ (ℓ:ℝ))
    (halphabet : q^(2*d-1) ≤ (Fintype.card α:ℝ)) :
    (ℓ:ℝ)*((d:ℝ)*log q+η*log σ+log c-1)-log (2*C) ≤ entropy (p.map F) := by
  let P := p.map (fun x => (stream x,F x))
  have hfst : P.fst = p.map stream := by
    rw [←Law.map_fst]
    dsimp only [P]
    rw [Law.map_map]
    rfl
  have hsnd : P.snd = p.map F := by
    rw [←Law.map_snd]
    dsimp only [P]
    rw [Law.map_map]
    rfl
  have hh := selected_entropy_source_scales hd hℓ hN P reverse hC hq hσ hc
    (by simpa only [hfst] using hdom) (by
      intro g f hgf
      obtain ⟨x,hx,he⟩ := p.map_support (fun x => (stream x,F x)) (g,f) hgf
      have hh := hselect x hx
      have he1 : stream x = g := congrArg Prod.fst he
      have he2 : F x = f := congrArg Prod.snd he
      simpa only [he1,he2] using hh) hsize hlength halphabet
  rwa [hsnd] at hh

theorem selected_map_linear_deficit {N ℓ d : ℕ} (hd : 1 ≤ d) (hℓ : 0 < ℓ) (hN : ℓ ≤ N)
    (p : Law Ω) (stream : Ω → Fin N → α) (F : Ω → Fin ℓ → α)
    (reverse : (Fin ℓ → α) → (Fin ℓ → α))
    {C q σ η c : ℝ} (hC : 0 < C) (hq : 0 < q) (hσ : 1 ≤ σ) (hη : 0 ≤ η) (hc : 0 < c)
    (hdom : ∀ g, (p.map stream).mass g ≤ C/(Fintype.card α:ℝ)^N)
    (hselect : ∀ x, p.mass x ≠ 0 → Occurs (F x) (stream x) ∨ Occurs (reverse (F x)) (stream x))
    (hsize : (N:ℝ) ≤ q^d*σ) (hlength : c*q*σ^(1+η) ≤ (ℓ:ℝ))
    (halphabet : q^(2*d-1) ≤ (Fintype.card α:ℝ)) :
    (ℓ:ℝ)*((d:ℝ)*log q)-(1+|log c|+|log (2*C)|)*ℓ ≤ entropy (p.map F) := by
  have hh := selected_map_entropy hd hℓ hN p stream F reverse hC hq (by linarith) hc
    hdom hselect hsize hlength halphabet
  have hpos : (1:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hl : 0 ≤ log σ := log_nonneg hσ
  have hgain : 0 ≤ (ℓ:ℝ)*(η*log σ) := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hη hl)
  have hc' : -|log c| ≤ log c := neg_abs_le _
  have hm : log (2*C) ≤ |log (2*C)| := le_abs_self _
  have hm' : |log (2*C)| ≤ (ℓ:ℝ)*|log (2*C)| := le_mul_of_one_le_left (abs_nonneg _) hpos
  have hc'' := mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg ℓ)
  nlinarith only [hh,hgain,hm,hm',hc'']
end
end SharpLogRamsey.Selection

end

end OAI
