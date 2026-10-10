import Mathlib
import OAI.Combinatorics.KMedian.Amplification.AmplifierGuard

namespace OAI

section Inline_PCPAmplifierCompiler
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic Polynomial
open scoped Classical

lemma normalize_count (s : CSPTable Label) :
    (normalize s).1.length+(normalize s).2.length≤(enc s).length+2 := by
  unfold normalize
  split_ifs
  · exact (CSPTable.count_le_encoding s).trans (by omega)
  · change 2≤_
    omega
noncomputable def countPoly : Polynomial ℕ := C co*((X+2)^co*(X+2))
noncomputable def sizePoly : Polynomial ℕ :=
  2*(X+3)+1+(2*(2*(X+2)+1)+1+
    (2*(countPoly*C (2*(enc ()).length+1))+1+
      countPoly*(2*(2*(countPoly+1)+1+(2*(countPoly+1)+1+C (CSPTable.relationBound (A := Label))))+1)))
lemma reachable_size (s : CSPTable Label) (i : ℕ) :
    (enc (guarded^[i] ((normalize s).2.length,(1,normalize s)))).length ≤ sizePoly.eval (enc s).length := by
  rw [guarded_iterate _ (normalize_valid s)]
  have hn := normalize_count s
  have he : (normalize s).2.length≤(enc s).length+2 := by omega
  have hc := schedule_count (normalize s) (normalize_valid s) i
  have hc' : (schedule (normalize s) i).2.2.1.length+(schedule (normalize s) i).2.2.2.length ≤
      countPoly.eval (enc s).length := by
    apply hc.trans
    unfold countPoly
    simp only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_ofNat]
    gcongr
  have ht := CSPTable.size_bound (schedule_valid (normalize s) (normalize_valid s) i) _ hc'
  have hb : (normalize s).2.length.bits.length ≤ (enc s).length+3 :=
    (NatBinary.length_le_height Nat.lt_two_pow_self.le).trans (by omega)
  have hh : (schedule (normalize s) i).2.1.bits.length ≤ 2*((enc s).length+2)+1 := by
    apply (NatBinary.length_le_height Nat.lt_two_pow_self.le).trans
    have hh := schedule_counter (normalize s) (normalize_valid s) i
    omega
  change (encodePair Nat.bits (encodePair Nat.bits enc) _).length≤_
  rw [encodePair_length,encodePair_length]
  change 2*(normalize s).2.length.bits.length+1+(2*(schedule (normalize s) i).2.1.bits.length+1+
    (enc (schedule (normalize s) i).2.2).length)≤_
  apply (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hb) _)
    (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) _) ht)).trans
  unfold CSPTable.sizeBound sizePoly
  simp only [eval_add,eval_mul,eval_C,eval_X,eval_one,eval_ofNat]
  omega
lemma poly_initialState : Poly (fun s : CSPTable Label => ((normalize s).2.length,(1,normalize s))) :=
  Poly.pair (Poly.list_length.comp (Poly.snd.comp poly_normalize)) (Poly.pair (Automatic.Poly.const _) poly_normalize)
lemma poly_steps : Poly (fun s : CSPTable Label => (normalize s).2.length+2) := by
  exact Poly.nat_add.comp (Poly.pair (Poly.list_length.comp (Poly.snd.comp poly_normalize)) (Automatic.Poly.const _))
lemma poly_trajectory : Poly (fun s : CSPTable Label =>
    Iteration.iterates guarded ((normalize s).2.length,(1,normalize s)) ((normalize s).2.length+2)) := by
  refine ⟨poly_guarded.program.iteratesFrom poly_initialState.program poly_steps.program
    (0,(1,fallback)) (X+4) sizePoly ?_ ?_⟩
  · intro s
    have hn := normalize_count s
    simp only [eval_add,eval_X,eval_ofNat]
    omega
  · intro s i hi
    exact reachable_size s i
lemma poly_generate : Poly generate := by
  have hi : Poly (fun s : CSPTable Label => (normalize s).2.length+1) :=
    Poly.nat_add.comp (Poly.pair (Poly.list_length.comp (Poly.snd.comp poly_normalize)) (Automatic.Poly.const _))
  have hg := Poly.list_getD_comp (0,(1,fallback)) poly_trajectory hi
  apply poly_congr (Poly.snd.comp (Poly.snd.comp hg))
  intro s
  change ((Iteration.iterates guarded ((normalize s).2.length,(1,normalize s)) ((normalize s).2.length+2))[(normalize s).2.length+1]?.getD
    (0,(1,fallback))).2.2=generate s
  rw [Iteration.iterates_eq]
  simp only [List.getElem?_map,List.getElem?_range,show (normalize s).2.length+1<(normalize s).2.length+2 by omega,
    Option.map_some,Option.getD_some,generate]
lemma generate_complete {s : CSPTable Label} (h : s.WellFormed)
    (hc : ∃ a, (s.csp h).Satisfies a) : ∃ a, ((generate s).csp (generate_valid s)).Satisfies a := by
  have he := generate_eq s
  rw [normalize_eq h] at he
  suffices hh : ∀ (t : CSPTable Label) (ht : t.WellFormed),
      t=iterate (Nat.log 2 s.2.length+1) s → ∃ a, (t.csp ht).Satisfies a by
    exact hh (generate s) (generate_valid s) he
  rintro t ht rfl
  exact iterate_complete h hc _
lemma generate_sound {s : CSPTable Label} (h : s.WellFormed)
    (hc : ¬∃ a, (s.csp h).Satisfies a) :
    ∀ a, 1/(capLoss:ℝ)≤((generate s).csp (generate_valid s)).rejection a := by
  have hi : ∀a, 1/((s.2.length:ℕ):ℝ)≤(s.csp h).rejection a := by
    intro a
    have he : ∃ e, (a ((s.csp h).left e),a ((s.csp h).right e)) ∉ (s.csp h).allowed e := by
      by_contra hh
      push Not at hh
      exact hc ⟨a,hh⟩
    obtain ⟨e,he⟩ := he
    simpa only [BinaryCSP.rejection,Fintype.card_fin] using
      testRate_ge_atom (fun e => (a ((s.csp h).left e),a ((s.csp h).right e)) ∉ (s.csp h).allowed e) e he
  let n := Nat.log 2 s.2.length+1
  have hn : s.2.length ≤ 2^n := Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega : 1<2) _)
  have hn' : (s.2.length:ℝ)≤2^n := by exact_mod_cast hn
  have he : 0<(s.2.length:ℝ) := Nat.cast_pos.mpr h.1
  have hl : (1:ℝ)≤capLoss := by norm_num [capLoss]
  have hh : 1/(capLoss:ℝ)≤2^n*(1/(s.2.length:ℝ)) := by
    have h1 : (1:ℝ)≤2^n/(s.2.length:ℝ) := (le_div_iff₀ he).mpr (by simpa using hn')
    have h2 : (1:ℝ)/(capLoss:ℝ)≤1 := (div_le_one (Nat.cast_pos.mpr capLoss_pos)).mpr hl
    simpa only [mul_one_div] using h2.trans h1
  have hx := generate_eq s
  rw [normalize_eq h] at hx
  suffices hg : ∀ (t : CSPTable Label) (ht : t.WellFormed),
      t=iterate n s → ∀ a, 1/(capLoss:ℝ)≤(t.csp ht).rejection a by
    exact hg (generate s) (generate_valid s) hx
  rintro t ht rfl
  simpa only [min_eq_right hh] using iterate_gap h _ hi n
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierCompiler

end OAI
