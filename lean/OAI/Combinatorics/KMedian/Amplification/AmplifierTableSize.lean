import Mathlib
import OAI.Combinatorics.KMedian.Amplification.AmplifierProgram
import OAI.Combinatorics.KMedian.Machines.TableCounts

namespace OAI

section Inline_PCPAmplifierTableSize
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic CloudSpec
open scoped Classical

noncomputable def rawCo (K : Type) [Fintype K] [DecidableEq K] (t cap : ℕ) : ℕ :=
  1+2*ExpanderFamily.growth^2*(AlphabetProgram.B K+
    (Ordered.fixed (PowerProgram.Tag (D := RegularProgram.Port) t cap)).entries.length*
      (AlphabetProgram.I K+AlphabetProgram.S K+(Ordered.fixed (AlphabetProgram.Tag K)).entries.length))
lemma rawCo_pos (K : Type) [Fintype K] [DecidableEq K] (t cap : ℕ) : 0<rawCo K t cap :=
  Nat.add_pos_left Nat.zero_lt_one _
private lemma arithmetic (v e a b nv ne f g c t n z : ℕ)
    (ha : a=v) (hb : b=v*z) (hnv : nv=a*f+b*g+b*c)
    (hne : ne=b*t) (hv : v≤n*e) :
    nv+ne ≤ (1+n*(f+z*(g+c+t)))*e := by
  subst a; subst b; subst nv; subst ne
  calc
    _ = v*(f+z*(g+c+t)) := by ring
    _ ≤ (n*e)*(f+z*(g+c+t)) := Nat.mul_le_mul_right _ hv
    _ ≤ (1+n*(f+z*(g+c+t)))*e := by nlinarith
lemma raw_count (K : Type) [Fintype K] [DecidableEq K] (t cap : ℕ)
    (e : Advice RegularProgram.Port Label cap ≃ BitVector K)
    (s : CSPTable Label) (h : s.WellFormed) [Nonempty (Fin s.2.length)] :
    let out := AlphabetProgram.table K (CSPTable.relabel e (PowerProgram.table t cap s))
    out.1.length+out.2.length≤rawCo K t cap*s.2.length := by
  let b := CSPTable.relabel e (PowerProgram.table t cap s)
  have hb1 : b.1.length=(PowerProgram.seeds s).length := rfl
  have hb2 : b.2.length=(PowerProgram.seeds s).length*
      (Ordered.fixed (PowerProgram.Tag (D := RegularProgram.Port) t cap)).entries.length := by
    change ((PowerProgram.table t cap s).2.map _).length=_
    rw [List.length_map]
    exact (PowerProgram.counts t cap s).2
  have hc := AlphabetProgram.counts K b
  exact arithmetic _ _ _ _ _ _ _ _ _ _ _ _ hb1 hb2 hc.1 hc.2 (PowerProgram.seeds_upper s h)
lemma raw_exists (K : Type) [Fintype K] [DecidableEq K] (t cap : ℕ)
    (e : Advice RegularProgram.Port Label cap ≃ BitVector K) :
    ∃ c : ℕ, 0<c ∧ ∀ (s : CSPTable Label) (_h : s.WellFormed),
      let out := AlphabetProgram.table K (CSPTable.relabel e (PowerProgram.table t cap s))
      out.1.length+out.2.length≤c*s.2.length := by
  refine ⟨rawCo K t cap,rawCo_pos K t cap,?_⟩
  intro s h
  let : Nonempty (Fin s.2.length) := Fin.pos_iff_nonempty.mp h.1
  exact raw_count K t cap e s h
lemma coefficient_exists : ∃ c : ℕ, 0<c ∧ ∀ (s : CSPTable Label) (_h : s.WellFormed),
    (next s).1.length+(next s).2.length≤c*s.2.length :=
  raw_exists Bits steps radius (Advice.bitsEquiv Degree (Fin 4) radius)
noncomputable def co : ℕ := coefficient_exists.choose
lemma co_pos : 0<co := coefficient_exists.choose_spec.1
lemma next_count (s : CSPTable Label) (h : s.WellFormed) :
    (next s).1.length+(next s).2.length≤co*s.2.length :=
  coefficient_exists.choose_spec.2 s h
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierTableSize

end OAI
