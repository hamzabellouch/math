import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceData

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSourceScales

def scaleStep (γ : ℝ) : ℝ := γ/4
def scaleCount (β γ : ℝ) : ℕ := ⌈β/scaleStep γ⌉₊+1
def lowerExponent (α γ : ℝ) : ℝ := min α (scaleStep γ/2)
def shortExponent (γ : ℝ) (n : ℕ) : ℝ := (n:ℝ)*scaleStep γ
def longExponent (γ : ℝ) (n : ℕ) : ℝ := ((n:ℝ)+1)*scaleStep γ

theorem scale_exponents {α γ : ℝ} (hα : 0<α) (hγ : 0<γ) {n : ℕ} (hn : 0<n) :
    0<lowerExponent α γ ∧ lowerExponent α γ ≤ shortExponent γ n ∧
      shortExponent γ n < longExponent γ n := by
  have hh : 0<scaleStep γ := by unfold scaleStep; positivity
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨lt_min hα (by positivity),?_,?_⟩
  · have hm := min_le_right α (scaleStep γ/2)
    dsimp only [lowerExponent,shortExponent] at *
    nlinarith
  · dsimp only [shortExponent,longExponent]
    nlinarith

theorem exists_grid_of_gap {β γ L a b : ℝ} (hγ : 0<γ) (hL : 0<L)
    (hb : 0<b) (hbβ : b≤β*L) (hgap : b+γ*L≤ a) :
    ∃n : Fin (scaleCount β γ),0<n.val ∧
      b≤ shortExponent γ n.val*L ∧
      (longExponent γ n.val+scaleStep γ)*L≤ a := by
  have hh : 0<scaleStep γ := by unfold scaleStep; positivity
  have hhL : 0<scaleStep γ*L := mul_pos hh hL
  let n := ⌈b/(scaleStep γ*L)⌉₊
  have hn : 0<n := Nat.one_le_ceil_iff.mpr (div_pos hb hhL)
  have hratio : b/(scaleStep γ*L)≤β/scaleStep γ := by
    apply (div_le_div_iff₀ hhL hh).mpr
    nlinarith [mul_le_mul_of_nonneg_left hbβ hh.le]
  have hnle : n≤⌈β/scaleStep γ⌉₊ := Nat.ceil_mono hratio
  have hnlt : n<scaleCount β γ := by unfold scaleCount; omega
  refine ⟨⟨n,hnlt⟩,hn,?_,?_⟩
  · have hc := (div_le_iff₀ hhL).mp (Nat.le_ceil (b/(scaleStep γ*L)))
    change b≤(n:ℝ)*scaleStep γ*L
    simpa only [n,mul_assoc] using hc
  · have hc := Nat.ceil_lt_add_one (div_nonneg hb.le hhL.le)
    have hc' := mul_lt_mul_of_pos_right hc hhL
    rw [add_mul,div_mul_cancel₀ _ hhL.ne'] at hc'
    change (((n:ℝ)+1)*scaleStep γ+scaleStep γ)*L≤ a
    have hstep : 4*scaleStep γ=γ := by unfold scaleStep; ring
    change (n:ℝ)*(scaleStep γ*L)<b+1*(scaleStep γ*L) at hc'
    nlinarith

end Ostmann.Characters.TemplateOneSidedSourceScales

end

end OAI
