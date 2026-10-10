import OAI.Analysis.PeriodicLattice.ElementaryFunctions
import OAI.MathematicalPhysics.RapidForcing.RatOperations
import OAI.MathematicalPhysics.RapidForcing.RecursiveComputable

namespace OAI

namespace PeriodicLattice.CertifiedReal

open Encodable Filter
open scoped Topology
local instance effectiveLogRatPrimcodable : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable

section
variable {A : Type*} [Primcodable A]

def logLower (z : ℕ) : ℚ := (decode z.unpair.1).getD 0
def logUpper (z : ℕ) : ℚ := (decode z.unpair.2.unpair.1).getD 0
def logAccuracy (z : ℕ) : ℕ := z.unpair.2.unpair.2

@[fun_prop] theorem logLower_computable : Computable logLower := by
  unfold logLower
  fun_prop
@[fun_prop] theorem logUpper_computable : Computable logUpper := by
  unfold logUpper
  fun_prop
@[fun_prop] theorem logAccuracy_computable : Computable logAccuracy := by
  unfold logAccuracy
  fun_prop

abbrev logTest (q : A × ℕ → ℚ) (e : ℚ × ℕ → ℚ) (an : A × ℕ) (z : ℕ) : Prop :=
  logUpper z - logLower z ≤ 2*qerror an.2 ∧
  e (logLower z, logAccuracy z) + 2*qerror (logAccuracy z) < q (an.1, logAccuracy z) ∧
  q (an.1, logAccuracy z) + 2*qerror (logAccuracy z) < e (logUpper z, logAccuracy z)

instance logTest_decidable (q : A × ℕ → ℚ) (e : ℚ × ℕ → ℚ) (an : A × ℕ) (z : ℕ) :
    Decidable (logTest q e an z) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem logTest_computable {q : A × ℕ → ℚ} {e : ℚ × ℕ → ℚ}
    (hq : Computable q) (he : Computable e) :
    Computable (fun p : (A × ℕ) × ℕ => decide (logTest q e p.1 p.2)) := by
  unfold logTest
  simp only [Bool.decide_and]
  apply Primrec.and.to_comp.comp
  · exact RecursiveArithmetic.ratLE.decide.to_comp.comp (by fun_prop) (by fun_prop)
  · apply Primrec.and.to_comp.comp
    · exact RecursiveArithmetic.ratLT.decide.to_comp.comp (by fun_prop) (by fun_prop)
    · exact RecursiveArithmetic.ratLT.decide.to_comp.comp (by fun_prop) (by fun_prop)

omit [Primcodable A] in
theorem logTest_exists {f : A → ℝ} (q : A × ℕ → ℚ) (e : ℚ × ℕ → ℚ)
    (eq : ∀ a n, |f a - (q (a,n) : ℝ)| ≤ error n)
    (ee : ∀ (a : ℚ) n, |Real.exp (a : ℝ) - (e (a,n) : ℝ)| ≤ error n)
    (hpos : ∀ a, 0 < f a) (an : A × ℕ) : ∃ z, logTest q e an z := by
  obtain ⟨l, hl, hl'⟩ := exists_rat_btwn
    (show Real.log (f an.1) - error an.2 < Real.log (f an.1) by linarith [error_pos an.2])
  obtain ⟨u, hu, hu'⟩ := exists_rat_btwn
    (show Real.log (f an.1) < Real.log (f an.1) + error an.2 by linarith [error_pos an.2])
  have hlExp : Real.exp (l : ℝ) < f an.1 := by
    rw [← Real.exp_log (hpos an.1)]
    exact Real.exp_lt_exp.mpr hl'
  have huExp : f an.1 < Real.exp (u : ℝ) := by
    rw [← Real.exp_log (hpos an.1)]
    exact Real.exp_lt_exp.mpr hu
  have tq := Effective.approximants_tendsto eq an.1
  have tl := Effective.approximants_tendsto ee l
  have tu := Effective.approximants_tendsto ee u
  have tl' := (tl.add (error_tendsto.const_mul 2)).eventually_lt tq
    (by simpa using hlExp)
  have tu' := (tq.add (error_tendsto.const_mul 2)).eventually_lt tu
    (by simpa using huExp)
  obtain ⟨s, hs, hs'⟩ := (tl'.and tu').exists
  refine ⟨Nat.pair (encode l) (Nat.pair (encode u) s), ?_⟩
  have hw : u-l ≤ 2*qerror an.2 := by
    have : (u : ℝ)-(l : ℝ) ≤ 2*error an.2 := by linarith
    exact_mod_cast (show (u : ℝ)-(l : ℝ) ≤ 2*(qerror an.2 : ℝ) by simpa using this)
  have hsl : e (l,s)+2*qerror s < q (an.1,s) := by
    exact_mod_cast (show (e (l,s) : ℝ)+2*(qerror s : ℝ) < (q (an.1,s) : ℝ) by simpa using hs)
  have hsu : q (an.1,s)+2*qerror s < e (u,s) := by
    exact_mod_cast (show (q (an.1,s) : ℝ)+2*(qerror s : ℝ) < (e (u,s) : ℝ) by simpa using hs')
  simpa only [logTest, logLower, logUpper, logAccuracy, Nat.unpair_pair, encodek, Option.getD_some]
    using And.intro hw (And.intro hsl hsu)

omit [Primcodable A] in
theorem logTest_sound {f : A → ℝ} (q : A × ℕ → ℚ) (e : ℚ × ℕ → ℚ)
    (eq : ∀ a n, |f a - (q (a,n) : ℝ)| ≤ error n)
    (ee : ∀ (a : ℚ) n, |Real.exp (a : ℝ) - (e (a,n) : ℝ)| ≤ error n)
    (hpos : ∀ a, 0 < f a) (a : A) (n z : ℕ) (hs : logTest q e (a,n) z) :
    |Real.log (f a) - (((logLower z+logUpper z)/2 : ℚ) : ℝ)| ≤ error n := by
  obtain ⟨hw, hl, hu⟩ := hs
  have el := ee (logLower z) (logAccuracy z)
  have eu := ee (logUpper z) (logAccuracy z)
  have ef := eq a (logAccuracy z)
  have hlr : (e (logLower z,logAccuracy z) : ℝ)+2*error (logAccuracy z) < q (a,logAccuracy z) := by
    simpa only [cast_qerror] using (show (e (logLower z,logAccuracy z) : ℝ)+2*(qerror (logAccuracy z) : ℝ) <
      (q (a,logAccuracy z) : ℝ) by exact_mod_cast hl)
  have hur : (q (a,logAccuracy z) : ℝ)+2*error (logAccuracy z) < e (logUpper z,logAccuracy z) := by
    simpa only [cast_qerror] using (show (q (a,logAccuracy z) : ℝ)+2*(qerror (logAccuracy z) : ℝ) <
      (e (logUpper z,logAccuracy z) : ℝ) by exact_mod_cast hu)
  have hlo : Real.exp (logLower z : ℝ) < f a := by
    have h1 := (abs_le.mp el).2
    have h2 := (abs_le.mp ef).1
    linarith
  have hhi : f a < Real.exp (logUpper z : ℝ) := by
    have h1 := (abs_le.mp eu).1
    have h2 := (abs_le.mp ef).2
    linarith
  have hloglo : (logLower z : ℝ) < Real.log (f a) := by
    rw [← Real.exp_log (hpos a)] at hlo
    exact Real.exp_lt_exp.mp hlo
  have hloghi : Real.log (f a) < (logUpper z : ℝ) := by
    rw [← Real.exp_log (hpos a)] at hhi
    exact Real.exp_lt_exp.mp hhi
  have hwidth : (logUpper z : ℝ)-(logLower z : ℝ) ≤ 2*error n := by
    simpa only [cast_qerror] using
      (show (logUpper z : ℝ)-(logLower z : ℝ) ≤ 2*(qerror n : ℝ) by exact_mod_cast hw)
  change |Real.log (f a) - (((logLower z+logUpper z)/2 : ℚ) : ℝ)| ≤ error n
  push_cast
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem Effective.log {f : A → ℝ} (hf : Effective f) (hpos : ∀ a, 0 < f a) :
    Effective (fun a => Real.log (f a)) := by
  obtain ⟨q, hq, eq⟩ := hf
  obtain ⟨e, he, ee⟩ := (rational (Computable.id : Computable (id : ℚ → ℚ))).exp
  change ∀ (a : ℚ) (n : ℕ), |Real.exp (a : ℝ) - (e (a,n) : ℝ)| ≤ error n at ee
  have hex := logTest_exists q e eq ee hpos
  let pick (an : A × ℕ) := Nat.find (hex an)
  have hpick : Computable pick := computable_find (logTest_computable hq he) hex
  refine ⟨fun an => (logLower (pick an)+logUpper (pick an))/2, by fun_prop, ?_⟩
  intro a n
  exact logTest_sound q e eq ee hpos a n (pick (a,n)) (Nat.find_spec (hex (a,n)))

end
end PeriodicLattice.CertifiedReal

end OAI
