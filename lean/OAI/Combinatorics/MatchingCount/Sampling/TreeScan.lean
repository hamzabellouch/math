import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeScanChoice
import OAI.Combinatorics.MatchingCount.Sampling.TreeLocalSampler

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped ExecutableOptions

variable {I A B C : Type} [Codec I] [Codec A] [Codec B] [Codec C]
variable [LinearOrder I] [Inhabited I] [Inhabited A]
attribute [local instance] Transport.prodOrder Transport.sumOrder
local instance treeScanUpdateInhabited : Inhabited (Replica.Update I) := ⟨Sum.inr default⟩
abbrev ScanInput (C I A B : Type) := (ScanSetup C I×StateTable I A)×(List Bool×B)

def scan (g : C×(I×I)→Bool) (p : LocalPairInput C I A B→A×A)
    (r : LocalRefreshInput C I B→A) (x : ScanInput C I A B) : StateTable I A :=
  localSampler p r ((x.1.1.1,(x.1.2,x.2.2)),draw none (scanChoice g x.1.1,x.2.1))
def scanRealizer {g : C×(I×I)→Bool} {p : LocalPairInput C I A B→A×A}
    {r : LocalRefreshInput C I B→A} (G : Realizer g) (P : Realizer p) (R : Realizer r)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (L : Realizer (fun x : I×I=>decide (x.1≤x.2))) : Realizer (scan g p r) :=
  (composition (pair (pair first.fst.fst (pair first.snd second.snd))
    (composition (pair (composition first.fst (scanChoiceRealizer G E L)) second.fst) (drawRealizer none)))
    (localSamplerRealizer P R E)).congr (fun _=>rfl)
lemma polynomial_scan {g : C×(I×I)→Bool} {p : LocalPairInput C I A B→A×A}
    {r : LocalRefreshInput C I B→A} {G : Realizer g} {P : Realizer p} {R : Realizer r}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {L : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    (hG : PolynomialTime G) (hP : PolynomialTime P) (hR : PolynomialTime R)
    (hE : PolynomialTime E) (hL : PolynomialTime L) : PolynomialTime (scanRealizer G P R E L) := by
  unfold scanRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_scanChoice hG hE hL
  have := polynomial_draw (none : Option (Replica.Update I))
  have := polynomial_localSampler hP hR hE
  tree_cost

variable {Ω D : Type} [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D]
variable (e : Ω→A) (d : D→B) (c : C) (keys : List I) (hk : ∀ i,i∈keys)
variable (guides : I→Finset I) (base : Finset I) (hb : base.Nonempty)
variable (g : C×(I×I)→Bool) (hg : ∀ i j,g (c,(i,j))=decide (j∈guides i))
variable (p : LocalPairInput C I A B→A×A) (r : LocalRefreshInput C I B→A)
variable (sp : I→I→(Ω×Ω)→D→Ω×Ω) (sr : I→D→Ω)
    (hp : ∀ i j a b,p ((c,(i,j)),((e a.1,e a.2),d b))=(e (sp i j a b).1,e (sp i j a b).2))
    (hr : ∀ i b,r ((c,i),d b)=e (sr i b))
omit [Codec I] [Codec A] [Codec B] [Codec C] [Inhabited I] in
include hp hr hk hg in
lemma scan_rep {k : ℕ} (s : I→Ω) (bs : Fin k→Bool) (b : D) :
    scan g p r (((c,(Finset.univ,base)),stateRep keys (e ∘ s)),(List.ofFn bs,d b))=
      stateRep keys (e ∘ Replica.sampleScan guides base hb sp sr k s (bs,b)) := by
  unfold scan
  rw [scanChoice_eq guides base hb g c hg]
  have hh := draw_repr id (Replica.scanChoice guides base hb) (none : Option (Replica.Update I)) bs
  dsimp only [id_eq] at hh
  rw [hh]
  exact localSampler_rep e d c keys hk p r sp sr hp hr s _ b
end MatchingFPRAS.ExecutableLadder

end OAI
