import OAI.MathematicalPhysics.RapidForcing.FormulaNames
import OAI.MathematicalPhysics.RapidForcing.ForceSyntax

namespace OAI

section

open scoped BigOperators Topology
open Set Filter
namespace RapidForcing
namespace EffectiveProfile.Formula

def readReal (c : Program) (n : ℕ) : Part ℚ :=
  (c.eval n).bind (fun k => Part.ofOption (Encodable.decode k))
def readPoint (c : Program) (n : ℕ) : Part RationalPoint :=
  (c.eval n).bind (fun k => Part.ofOption (Encodable.decode k))

lemma readReal_mem {c : Program} {x : ℝ} (hc : NamesReal c x) (n : ℕ) :
    ∃ q : ℚ, q ∈ readReal c n ∧ |(q : ℝ) - x| ≤ accuracy n := by
  obtain ⟨q, hq, he⟩ := hc n
  exact ⟨q, Part.mem_bind_iff.mpr ⟨Encodable.encode q, hq, by simp⟩, he⟩
lemma readPoint_mem {c : Program} {t : ℝ} {x : Space} (hc : NamesPoint c t x) (n : ℕ) :
    ∃ q : RationalPoint, q ∈ readPoint c n ∧ |(q.1 : ℝ) - t| ≤ accuracy n ∧
      ‖rationalVector q.2 - x‖ ≤ accuracy n := by
  obtain ⟨q, hq, he⟩ := hc n
  exact ⟨q, Part.mem_bind_iff.mpr ⟨Encodable.encode q, hq, by simp⟩, he⟩

lemma readPoint_spec {c : Program} {t : ℝ} {x : Space} (hc : NamesPoint c t x)
    {n : ℕ} {q : RationalPoint} (hq : q ∈ readPoint c n) :
    |(q.1 : ℝ) - t| ≤ accuracy n ∧ ‖rationalVector q.2 - x‖ ≤ accuracy n := by
  obtain ⟨q', hq', he⟩ := readPoint_mem hc n
  exact Part.mem_unique hq hq' ▸ he

def coordinateName (visc input : Program) (n : ℕ) : Part (Fin 5 → ℚ) := do
  let v ← readReal visc n
  let q ← readPoint input n
  pure ![q.1, q.2.1, q.2.2.1, q.2.2.2, v]

lemma coordinateName_spec {visc input : Program} {ν t : ℝ} {x : Space}
    (hν : NamesReal visc ν) (hp : NamesPoint input t x) :
    RationalName (coordinateName visc input) (pack ν t x) := by
  intro n
  obtain ⟨v, hv, hev⟩ := readReal_mem hν n
  obtain ⟨q, hq, het, hex⟩ := readPoint_mem hp n
  refine ⟨![q.1, q.2.1, q.2.2.1, q.2.2.2, v], ?_, ?_⟩
  · exact Part.mem_bind_iff.mpr ⟨v, hv, Part.mem_bind_iff.mpr ⟨q, hq, Part.mem_some _⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (by unfold accuracy; positivity : 0 ≤ accuracy n)).mpr
    intro i
    have hx' (j : Fin 3) : |rationalVector q.2 j - x j| ≤ accuracy n :=
      (PiLp.norm_apply_le (rationalVector q.2 - x) j).trans hex
    fin_cases i
    · simpa [pack, Real.norm_eq_abs] using het
    · simpa [pack, Real.norm_eq_abs, rationalVector, vec] using hx' 0
    · simpa [pack, Real.norm_eq_abs, rationalVector, vec] using hx' 1
    · simpa [pack, Real.norm_eq_abs, rationalVector, vec] using hx' 2
    · simpa [pack, Real.norm_eq_abs] using hev

def timeWindow (q : RationalPoint) : ℕ := ⌈q.1⌉₊ + 2

lemma timeWindow_spec {c : Program} {t : ℝ} {x : Space} (hc : NamesPoint c t x)
    {q : RationalPoint} (hq : q ∈ readPoint c 0) : t < (timeWindow q : ℝ) + 1 := by
  have he := (readPoint_spec hc hq).1
  have hr : (q.1 : ℝ) ≤ (⌈q.1⌉₊ : ℕ) := by exact_mod_cast (Nat.le_ceil q.1)
  have ht := (abs_le.mp he).1
  simp only [accuracy, pow_zero] at ht
  simp only [timeWindow, Nat.cast_add, Nat.cast_ofNat]
  linarith

def evaluateForce (M : Machine) (w : M.Input) (visc input : Program)
    (l : ℕ) (α : MultiIndex) (ε : ℚ) : Part RationalVector := do
  let q ← readPoint input 0
  let a := fun i => (forceFormula M w (timeWindow q) i).mixed l α
  let name := coordinateName visc input
  let b₀ ← (a 0).evalName name (ε / 3)
  let b₁ ← (a 1).evalName name (ε / 3)
  let b₂ ← (a 2).evalName name (ε / 3)
  pure (b₀.center, b₁.center, b₂.center)

lemma evaluateForce_spec (M : Machine) (w : M.Input) {visc input : Program}
    {ν t : ℝ} {x : Space} (hν : NamesReal visc ν) (hp : NamesPoint input t x)
    (ht : 0 ≤ t) (l : ℕ) (α : MultiIndex) (ε : ℚ) (hε : 0 < ε)
    {r : RationalVector} (hr : r ∈ evaluateForce M w visc input l α ε) :
    ‖rationalVector r - mixedD l α (addressedForce ν M w) t x‖ ≤ (ε : ℝ) := by
  obtain ⟨q, hq, hrest⟩ := Part.mem_bind_iff.mp hr
  obtain ⟨b₀, h₀, hrest⟩ := Part.mem_bind_iff.mp hrest
  obtain ⟨b₁, h₁, hrest⟩ := Part.mem_bind_iff.mp hrest
  obtain ⟨b₂, h₂, hr⟩ := Part.mem_bind_iff.mp hrest
  have hr' := Part.mem_some_iff.mp hr
  subst r
  have hn := coordinateName_spec hν hp
  have hε' : 0 < ε / 3 := by positivity
  let a := fun i => (forceFormula M w (timeWindow q) i).mixed l α
  have spec (i : Fin 3) (b : Ball) (hb : b ∈ (a i).evalName (coordinateName visc input) (ε / 3)) :
      |(b.center : ℝ) - (a i).value (pack ν t x)| ≤ (ε : ℝ) / 3 := by
    obtain ⟨hb, he⟩ := (a i).evalName_spec hn _ hε' hb
    exact hb.trans (by exact_mod_cast he)
  rw [mixed_forceFormula_correct M w (timeWindow q) l α ν t ht (timeWindow_spec hp hq)]
  have hcoord (i : Fin 3) : |(rationalVector (b₀.center, b₁.center, b₂.center) -
      vectorField a ν t x) i| ≤ (ε : ℝ) / 3 := by
    fin_cases i
    · exact spec 0 b₀ h₀
    · exact spec 1 b₁ h₁
    · exact spec 2 b₂ h₂
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  exact (norm_le_two_mul_of_coord_le (by positivity : 0 ≤ (ε : ℝ) / 3) hcoord).trans
    (by linarith)

lemma evaluateForce_dom (M : Machine) (w : M.Input) {visc input : Program}
    {ν t : ℝ} {x : Space} (hν : NamesReal visc ν) (hp : NamesPoint input t x)
    (l : ℕ) (α : MultiIndex) (ε : ℚ) (hε : 0 < ε) :
    (evaluateForce M w visc input l α ε).Dom := by
  have hn := coordinateName_spec hν hp
  obtain ⟨q, hq, _⟩ := readPoint_mem hp 0
  refine ⟨hq.fst, ?_⟩
  exact ⟨evalName_dom _ hn _ (by positivity), evalName_dom _ hn _ (by positivity),
    evalName_dom _ hn _ (by positivity), trivial⟩

end EffectiveProfile.Formula
end RapidForcing

end

end OAI
