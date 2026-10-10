import OAI.Computability.WLIdentification.MachinePresentation

namespace OAI

namespace WLIdentification
namespace FinitePresentation.MachineRealizer
open WordExpressions Machine
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Factor the finite enumerations through the compiled type names so instance
search does not repeatedly expand the entire cellular compiler. -/
noncomputable instance compiledRealTypeFintype (M : Machine) (d : ℕ) (w : Word) :
    Fintype (M.compiledCircuit d w).RealType := by infer_instance

noncomputable instance compiledComparisonFintype (M : Machine) (d : ℕ) (w : Word) :
    Fintype (M.compiledCircuit d w).Comparison := by infer_instance

theorem width_poly (C e : ℕ) : NatPoly (fun X : Fin 1 → Word => addressWidth C e (X 0).length) :=
  NatPoly.add (NatPoly.add (NatPoly.add
    (NatPoly.mul (NatPoly.const C) (NatPoly.pow_const (NatPoly.succ (NatPoly.var 0)) e)) (NatPoly.var 0))
    (NatPoly.const 32)) (NatPoly.const 2)

theorem inputSpan_lt_width (C e : ℕ) (w : Word) : inputSpan w<2^addressWidth C e w.length := by
  have hs : inputSpan w≤w.length+1 := max_le (by omega) (by omega)
  have hd : w.length+1≤addressWidth C e w.length := by unfold addressWidth paddedExponent; omega
  exact hs.trans_lt ((Nat.lt_two_pow_self (n := w.length+1)).trans_le
    (Nat.pow_le_pow_right (by decide) hd))

theorem dimension_poly (C e : ℕ) : NatPoly (fun X : Fin 1 → Word => reductionDimension C e (X 0).length) :=
  NatPoly.add (width_poly C e) (width_poly C e)

noncomputable def compiled (M : Machine) (C e : ℕ) :=
  circuit M (fun w => addressWidth C e w.length) (width_poly C e) (inputSpan_lt_width C e)

theorem wire_poly (C e : ℕ) : NatPoly (fun X : Fin 1 → Word => 4*(reductionDimension C e (X 0).length+1)-1) :=
  NatPoly.sub (NatPoly.mul (NatPoly.const 4) (NatPoly.succ (dimension_poly C e))) (NatPoly.const 1)

noncomputable def ring (M : Machine) (C e : ℕ) := (compiled M C e).schemas.ring
  (fun w => 4*(reductionDimension C e w.length+1)-1) (wire_poly C e)

noncomputable def affine (M : Machine) (C e : ℕ) := (ring M C e).affine
  (fun w => by have := reductionDimension_ge C e w.length; change 2≤reductionDimension C e w.length; omega)

noncomputable def uncolored (M : Machine) (C e : ℕ) := (affine M C e).uncolored

 theorem graph_isomorphic (M : Machine) (C e : ℕ) (w : Word) :
    Isomorphic ((uncolored M C e).graph w) (M.reductionGraph C e w) :=
  (affine M C e).uncolored_isomorphic w

 theorem graph_nonempty (M : Machine) (C e : ℕ) (w : Word) :
    0<((uncolored M C e).graph w).order := by
  obtain ⟨f,_⟩ := graph_isomorphic M C e w
  have he : ((uncolored M C e).graph w).order=(M.reductionGraph C e w).order := by
    simpa only [Fintype.card_fin] using Fintype.card_congr f
  rw [he]
  exact M.reductionGraph_nonempty C e w

noncomputable def output (M : Machine) (C e : ℕ) : Word → Word :=
  (uncolored M C e).output (fun w => reductionDimension C e w.length)

 theorem output_poly (M : Machine) (C e : ℕ) : Poly (fun X : Fin 1 → Word => output M C e (X 0)) :=
  (uncolored M C e).output_poly (dimension_poly C e)

 theorem output_correct {L : BinaryLanguage} {M : Machine} {C e : ℕ}
    (h : DecidesWithin M L (fun m => 2^(C*(m+1)^e))) (w : Word) :
    w∈L ↔ output M C e w∈dimensionLanguage := by
  rw [output,PresentedGraph.output_eq,inputWord_mem_iff _ (graph_nonempty M C e w) _
    (by have := reductionDimension_ge C e w.length; omega),
    WLdim_isomorphic (graph_isomorphic M C e w),M.reductionGraph_correct h w]
end FinitePresentation.MachineRealizer

/-- The reduction is an actual polynomial-time tape transducer. Relabeling is
by effective rank/select on polynomial finite coding families, not by an
arbitrary Fintype enumeration. Its semantic conclusion retains all graph mates. -/
theorem dimensionLanguage_hard : ∀ L : BinaryLanguage, InEXPTIME L → PolytimeManyOne L dimensionLanguage := by
  intro L ⟨M,C,e,h⟩
  obtain ⟨N,c,d,hN⟩ := (FinitePresentation.MachineRealizer.output_poly M C e).computes
  exact ⟨FinitePresentation.MachineRealizer.output M C e,N,c,d,hN,
    FinitePresentation.MachineRealizer.output_correct h⟩

end WLIdentification

end OAI
