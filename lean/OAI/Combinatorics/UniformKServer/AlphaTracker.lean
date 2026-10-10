import Mathlib
import OAI.Combinatorics.UniformKServer.LogPrimitive
import OAI.Combinatorics.UniformKServer.SimplexTracker

namespace OAI

section
namespace UniformKServer.AlphaTracker
open Set Filter
open scoped Topology
open UniformKServer.Denominators UniformKServer.LogPrimitive UniformKServer.SimplexTracker
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def regularG (h B : ι → ℝ) (ell ct C : ℝ) (i : ι) : ℝ → ℝ :=
  primitive (regular (h i)) 0 (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i)
noncomputable def markedF (o : ι) (u : ℝ) (h : ι → ℝ) (i : ι) (x : ℝ) : ℝ :=
  if i = o then marked u x else regular (h i) x
noncomputable def markedG (o : ι) (u : ℝ) (h B : ι → ℝ) (ell ct C : ℝ) (i : ι) : ℝ → ℝ :=
  primitive (markedF o u h i) (if i = o then 1 else 0)
    (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i)
def UpdateConclusion (g : ι → ℝ → ℝ) (B h : ι → ℝ) (ell ct : ℝ) (a₀ : ι → ℝ) : Prop :=
  ∃ a, simplex a ∧ IsMinOn (objective g (∑ i, B i) a₀) {a | simplex a} a ∧
    (∀ i, (∑ r, B r)*a i ≤ (1+ct*h i/ell)*B i) ∧
    (∑ i, B i)*movement a a₀ ≤ (∑ i, g i (a₀ i))-(∑ i, g i (a i))
-- CANDIDATE PROOFS
omit [DecidableEq ι] in
theorem analytic_data {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (hB : ∀ i, 0 ≤ B i) (hh : ∀ i, 0 < h i)
    (hl : 0 < ell) (hc : 0 < ct) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (heta : ∀ i, ct*h i/ell ≤ E) (hm : 2*A*(1+E) < C*ct)
    (hF : ∀ i x, 0 < x → x ≤ 1 → 0 < F i x)
    (hsum : ∀ a, simplex a → (∑ i, a i*F i (a i)) ≤ A*(∑ i, a i*h i))
    (hg : ∀ i, Contract (g i) (F i) (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i)) :
    AnalyticData g B h F ell ct C A E := by
  have hC : 0 < C := pos_of_mul_pos_left
    (lt_of_le_of_lt (by positivity : 0 ≤ 2*A*(1+E)) hm) hc.le
  refine ⟨hB, hh, hl, hc, hA, hE, heta, hm, hF, hsum, fun i => (hg i).1, ?_, ?_⟩
  · intro i x hx hx₁
    convert! (hg i).2.1 x hx hx₁ using 1 ; ring
  · intro i hi
    apply (hg i).2.2
    · apply mul_pos _ hi
      have hp := div_pos (mul_pos hc (hh i)) hl
      linarith
    · exact mul_pos hC hl

theorem regular_update (h B a₀ : ι → ℝ) (ell ct C E Z : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hh : ∀ i, 1 ≤ h i) (hl : 0 < ell) (hc : 0 < ct)
    (hE : 0 ≤ E) (hZ : 0 ≤ Z) (heta : ∀ i, ct*h i/ell ≤ E)
    (hm : 2*(25+32*Z)*(1+E) < C*ct) (he : (∑ i, Real.exp (-h i)) ≤ Z)
    (ha₀ : simplex a₀) : UpdateConclusion (regularG h B ell ct C) B h ell ct a₀ := by
  apply update _ B h (fun i => regular (h i)) ell ct C (25+32*Z) E _ a₀ ha₀
  apply analytic_data hB (fun i => lt_of_lt_of_le (by norm_num) (hh i)) hl hc
    (by positivity) hE heta hm
  · exact fun i x hx hx₁ => regular_pos (by linarith [hh i]) hx.le hx₁
  · exact fun a ha => regular_simplex h a Z hh ha.1 ha.2 he
  · exact fun i => regular_contract (h i) (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i) (hh i)

theorem marked_update (o : ι) (u c Z : ℝ) (h B a₀ : ι → ℝ) (ell ct C E : ℝ)
    (hu : 0 < u) (hu₁ : u ≤ 1) (hc₀ : 0 < c) (hc₁ : c ≤ 1) (hZ : 0 ≤ Z)
    (ho : h o = u) (hh : ∀ i, i ≠ o → 1 ≤ h i)
    (hhc : ∀ i, i ≠ o → c*height u ≤ h i)
    (he : (∑ i ∈ Finset.univ.erase o, Real.exp (-h i)) ≤ Z*u)
    (hB : ∀ i, 0 ≤ B i) (hl : 0 < ell) (hct : 0 < ct) (hE : 0 ≤ E)
    (heta : ∀ i, ct*h i/ell ≤ E) (hm : 2*(25+(2+32*Z)/c)*(1+E) < C*ct)
    (ha₀ : simplex a₀) : UpdateConclusion (markedG o u h B ell ct C) B h ell ct a₀ := by
  have hp : ∀ i, 0 < h i := by
    intro i
    by_cases hi : i = o
    · simpa [hi, ho] using hu
    · linarith [hh i hi]
  apply update _ B h (markedF o u h) ell ct C (25+(2+32*Z)/c) E _ a₀ ha₀
  apply analytic_data hB hp hl hct (by positivity) hE heta hm
  · intro i x hx hx₁
    by_cases hi : i = o
    · simp only [markedF, hi]
      exact marked_pos hu hu₁ hx.le hx₁
    · simp only [markedF, ite_eq_right hi]
      exact regular_pos (hp i) hx.le hx₁
  · intro a ha
    exact marked_simplex o u c Z h a hu hu₁ hc₀ hc₁ hZ ho hh hhc he ha.1 ha.2
  · intro i
    by_cases hi : i = o
    · have hf : markedF o u h i = marked u := by funext x; simp [markedF, hi]
      simpa only [markedG, hf, ite_eq_left hi] using
        marked_contract u (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i) hu hu₁
    · have hf : markedF o u h i = regular (h i) := by funext x; simp [markedF, hi]
      simpa only [markedG, hf, ite_eq_right hi] using
        regular_contract (h i) (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i) (hh i hi)
end UniformKServer.AlphaTracker

end


end OAI
