import OAI.Analysis.Triangular.Taylor.Taylor

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def finiteWaveJet (q br : Fin 2) (t : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  taylorAmplitude q br t * exp (taylorPhase q br t*s) * (taylorPhase q br t)^k
lemma hasDerivAt_finiteWaveJet (q br : Fin 2) (t : ℝ) (k : ℕ) (s : ℂ) :
    HasDerivAt (finiteWaveJet q br t k) (finiteWaveJet q br t (k+1) s) s := by
  unfold finiteWaveJet
  have hh := (((hasDerivAt_id s).const_mul (taylorPhase q br t)).cexp.const_mul
    (taylorAmplitude q br t)).mul_const ((taylorPhase q br t)^k)
  simpa only [finiteWaveJet,mul_one,one_mul,pow_succ,mul_assoc,mul_comm,mul_left_comm,
    id_eq] using hh

def finiteJJet (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ r : Fin 8, (e r:ℂ) * (∑ q : Fin 2, ∑ j : Fin 31,
    (finiteSpectrum side q j r * finiteWaveJet q 0 (frequency j) k s +
    finiteSpectrum (otherSide side) q j r * finiteWaveJet q 1 (frequency j) k s))
def finiteJ (side : Fin 2) (e : Fin 8 → ℝ) (s : ℝ) : ℝ := (finiteJJet side e 0 s).re
lemma hasDerivAt_finiteJJet (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) (s : ℂ) :
    HasDerivAt (finiteJJet side e k) (finiteJJet side e (k+1) s) s := by
  have hj (r : Fin 8) (q : Fin 2) (j : Fin 31) :=
    ((hasDerivAt_finiteWaveJet q 0 (frequency j) k s).const_mul (finiteSpectrum side q j r)).add
    ((hasDerivAt_finiteWaveJet q 1 (frequency j) k s).const_mul (finiteSpectrum (otherSide side) q j r))
  have hq (r : Fin 8) (q : Fin 2) := HasDerivAt.sum (u := Finset.univ) (fun j _ => hj r q j)
  have hr (r : Fin 8) := (HasDerivAt.sum (u := Finset.univ) (fun q _ => hq r q)).const_mul (e r:ℂ)
  simpa only [finiteJJet,Finset.sum_apply,Pi.add_apply] using!
    HasDerivAt.sum (u := Finset.univ) (fun r _ => hr r)
lemma finiteJJet_re_iterated (side : Fin 2) (e : Fin 8 → ℝ) (k : ℕ) :
    (fun s : ℝ => (finiteJJet side e k s).re) = iteratedDeriv k (finiteJ side e) := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [iteratedDeriv_succ,← hk]
    exact funext fun s => ((hasDerivAt_finiteJJet side e k s).real_of_complex).deriv.symm
lemma taylorWave_eq (q br : Fin 2) (m : ℤ) (l : ℕ) (t : ℝ) :
    taylorWave q br m l t = finiteWaveJet q br t (l+2) m / ((l+2).factorial:ℂ) := rfl
lemma taylorRow_dot (side : Fin 2) (m : ℤ) (y : ℝ) (l : ℕ) (e : Fin 8 → ℝ) :
    (∑ r : Fin 8, taylorRow side m y l r*e r) =
      (iteratedDeriv (l+2) (finiteJ side e) m) * y^l / ((l+2).factorial:ℝ) := by
  rw [← finiteJJet_re_iterated]
  simp only [taylorRow,taylorWave_eq,finiteJJet,Complex.ofReal_intCast,
    ← mul_div_assoc,← add_div,← Finset.sum_div]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  simp only [Finset.sum_mul,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Complex.re_sum,← Complex.ofReal_natCast,Complex.div_ofReal_re,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.add_re]
  ring
lemma finiteTaylor_exact (side : Fin 2) (m : ℤ) (y : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) :
    finiteTaylor side m y e τ = ∑ l ∈ Finset.range 21,
      (iteratedDeriv (l+2) (finiteJ side e) m) * y^l / ((l+2).factorial:ℝ) * τ^l := by
  unfold finiteTaylor
  apply Finset.sum_congr rfl
  intro l hl
  rw [taylorRow_dot]
end AtomicTriangular.Construction
end

end OAI
