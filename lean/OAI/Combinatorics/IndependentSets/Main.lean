import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.GraphReduction
import OAI.Combinatorics.IndependentSets.Reduction.ClampCube
import OAI.Combinatorics.IndependentSets.PCP.FinalCNF
import OAI.Combinatorics.IndependentSets.Reduction.MapEquiv
import OAI.Combinatorics.IndependentSets.Machines.ProfileMachine
import OAI.Combinatorics.IndependentSets.Encoding.PortTableEncoding
import OAI.Combinatorics.IndependentSets.Machines.MachineLazyTableRuntime
import OAI.Combinatorics.IndependentSets.Machines.PCPGapMachine
import OAI.Combinatorics.IndependentSets.Machines.TargetLCMachine
import OAI.Combinatorics.IndependentSets.Geometry.GeometryOutput

namespace OAI

namespace LargeIndependentSets
open IndependentSetsGames.Foundations
open scoped Classical
noncomputable section

namespace CompleteReduction
open PCP Hastad.SourceContexts Hastad.SourceGame
open Complexity

def gapInput (H : RoundTables.BaseTable) (b : List Bool) : TargetLC.Input :=
  ⟨TableIteration.gapMap H (BinaryNormalize.normalize b),TableIteration.gapMap_nonempty H _⟩

def gapView (H : RoundTables.BaseTable) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun F : TargetLC.Input => Complexity.formulaBits F.val) (gapInput H) where
  tm := (BinaryNormalize.gapCertificate H).tm
  inputAlphabet := (BinaryNormalize.gapCertificate H).inputAlphabet
  outputAlphabet := (BinaryNormalize.gapCertificate H).outputAlphabet
  time := (BinaryNormalize.gapCertificate H).time
  outputsFun := (BinaryNormalize.gapCertificate H).outputsFun

def lcComputer (H : RoundTables.BaseTable) (u : ℕ) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) UniformLC.Table.bits
      (fun b => TargetLC.table u (gapInput H b)) :=
  MachineSequential.composeBits (gapView H) (TargetLC.certificate u)

lemma lcComputer_finiteAlphabet (H : RoundTables.BaseTable) (u : ℕ) :
    MachineFiniteAlphabet.FiniteAlphabet (lcComputer H u).tm :=
  MachineFiniteAlphabet.composeBits (gapView H) (TargetLC.certificate u)
    (BinaryNormalize.gap_finiteAlphabet H) (TargetLC.finiteAlphabet u)

def reduce (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (b : List Bool) : Graph := GeometryNames.output (J u) (I u) p q hq (TargetLC.table u (gapInput H b))

def certificate (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) graphBits (reduce H p u q hq) :=
  MachineSequential.composeBits (f := fun b => TargetLC.table u (gapInput H b))
    (g := GeometryNames.output (J u) (I u) p q hq)
    (lcComputer H u) (GeometryNames.graphComputer (J u) (I u) p q hq)

lemma finiteAlphabet (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q) :
    MachineFiniteAlphabet.FiniteAlphabet (certificate H p u q hq).tm :=
  MachineFiniteAlphabet.composeBits (lcComputer H u) (GeometryNames.graphComputer (J u) (I u) p q hq)
    (lcComputer_finiteAlphabet H u) (GeometryNames.graphComputer_finiteAlphabet (J u) (I u) p q hq)

lemma normalize_bits (b : List Bool) :
    (Complexity.formulaBits (BinaryNormalize.normalize b)).length ≤ 100*(b.length+1)^2 := by
  have h := Complexity.formulaBits_length_le (BinaryNormalize.normalize b)
  rw [BinaryNormalize.clauses_length] at h
  change (Complexity.formulaBits (BinaryNormalize.normalize b)).length ≤
    b.length+1+2*b.length+2+2*b.length*(3*(b.length+1+2)) at h
  nlinarith [Nat.zero_le b.length]

def clausePolynomial : Polynomial ℕ := TableIteration.formulaBitsPolynomial.comp
  (Polynomial.C 100*(Polynomial.X+Polynomial.C 1)^2)

lemma clauses_bound (H : RoundTables.BaseTable) (b : List Bool) :
    (gapInput H b).val.clauses.length ≤ clausePolynomial.eval b.length := by
  have h0 := Hastad.SourceBounds.formulaBits_length_ge_clauses (gapInput H b).val
  have h1 := TableIteration.gapMap_bits_le H (BinaryNormalize.normalize b)
  have h2 := MachineComposition.natPolynomial_eval_mono TableIteration.formulaBitsPolynomial (normalize_bits b)
  apply h0.trans (h1.trans _)
  simpa only [clausePolynomial,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X] using h2

def vertexPolynomial (p : SamplerParameters) (u q : ℕ) : Polynomial ℕ :=
  Polynomial.C q + (Polynomial.C 3*clausePolynomial)^(u*p.n) *
    Polynomial.C (GeometryNames.outcomeCount (J u) (I u) p)

lemma vertices_bound (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (b : List Bool) : (reduce H p u q hq b).vertices ≤
      (vertexPolynomial p u q).eval b.length := by
  have hs : (reduce H p u q hq b).vertices ≤ q+
      ((gapInput H b).val.clauses.length*3)^(u*p.n)*GeometryNames.outcomeCount (J u) (I u) p := by
    unfold reduce GeometryNames.output
    split
    · change q ≤ _
      omega
    · change (TargetLC.table u (gapInput H b)).ne^p.n*GeometryNames.outcomeCount (J u) (I u) p ≤ _
      simp only [TargetLC.table,← pow_mul]
      omega
  apply hs.trans
  simp only [vertexPolynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_pow]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_left
  nlinarith [clauses_bound H b]

def outputPolynomial (p : SamplerParameters) (u q : ℕ) : Polynomial ℕ :=
  Polynomial.C 4*(vertexPolynomial p u q+Polynomial.C 1)^2

lemma output_bound (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (b : List Bool) : (graphBits (reduce H p u q hq b)).length ≤
      (outputPolynomial p u q).eval b.length := by
  apply (graphBits_bound _).trans
  simp only [outputPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_pow]
  exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
    (Nat.add_le_add_right (vertices_bound H p u q hq b) 1) 2)

lemma complete (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (F : Formula) (hF : F.Satisfiable) : (reduce H p u q hq (formulaBits F)).ThreeColorable := by
  have hgap : (gapInput H (formulaBits F)).val.Satisfiable :=
    TableIteration.gapMap_completeness H _ ((BinaryNormalize.satisfiable_iff F).mpr hF)
  obtain ⟨l,r,hr⟩ := TargetLC.complete u (gapInput H (formulaBits F)) hgap
  exact (GeometryNames.outputRenaming (J u) (I u) p q hq (TargetLC.table u (gapInput H (formulaBits F)))).symm.colorable
    (p.output_complete q hq _ l r hr)

end CompleteReduction

theorem mainTheoremReal :
    ∀ δ : ℝ, 0 < δ → δ < 1 / 3 → Nonempty (RealGraphReduction δ) := by
  intro δ hδ _hδ3
  obtain ⟨H,hH⟩ := PCP.ExpanderTables.exists_base_table
  obtain ⟨p,σ,q,hq,hσ,_hσ1,hp⟩ := finite_graph_reduction hδ
  obtain ⟨u,_hu,hrep⟩ := LCInput.uniform_repetition
    PCP.PCPIteration.finalClauseGap_positive PCP.TableGapReduction.finalClauseGap_le_one hσ
  refine ⟨{
    reduce := CompleteReduction.reduce H p u q hq
    computation := CompleteReduction.certificate H p u q hq
    finiteAlphabets := CompleteReduction.finiteAlphabet H p u q hq
    outputBound := CompleteReduction.outputPolynomial p u q
    outputSize := CompleteReduction.output_bound H p u q hq
    completeness := CompleteReduction.complete H p u q hq
    soundness := ?_ }⟩
  intro F hF
  have hg : Hastad.SourceGap.ClauseGap (CompleteReduction.gapInput H (formulaBits F)).val
      PCP.PCPIteration.finalClauseGap :=
    PCP.TableGapReduction.gapMap_clauseGap H hH _
      (fun h => hF ((BinaryNormalize.satisfiable_iff F).mp h))
  have hs := TargetLC.sound u (CompleteReduction.gapInput H (formulaBits F)) (hrep _ hg)
  have hout := (hp _ _ _ _ _ (TargetLC.table u (CompleteReduction.gapInput H (formulaBits F))).lc).2 hs
  exact (GeometryNames.outputRenaming (Hastad.SourceContexts.J u) (Hastad.SourceContexts.I u) p q hq
    (TargetLC.table u (CompleteReduction.gapInput H (formulaBits F)))).symm.strict_density hout

end
end LargeIndependentSets

end OAI
