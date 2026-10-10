import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeScan
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeStateNormalize

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E B C : Type} [Codec I] [Codec E] [Codec B] [Codec C]
variable [LinearOrder I] [Inhabited I] [LinearOrder E]
attribute [local instance] Transport.prodOrder Transport.sumOrder
local instance treeScanRunUpdateInhabited : Inhabited (Replica.Update I) := ⟨Sum.inr default⟩
abbrev RunSetup (C I E : Type) := ScanSetup C I×StateEnvelope I E
abbrev RunState (C I E : Type) := RunSetup C I E×StateTable I (Finset E)

def runStep (g : C×(I×I)→Bool) (p : LocalPairInput C I (Finset E) B→Finset E×Finset E)
    (r : LocalRefreshInput C I B→Finset E) (x : (List Bool×B)×RunState C I E) : RunState C I E :=
  (x.2.1,normalizeState (x.2.1.2,scan g p r ((x.2.1.1,x.2.2),x.1)))
def runStepRealizer {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} (G : Realizer g) (P : Realizer p) (R : Realizer r)
    (Eq : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (Le : Realizer (fun x : I×I=>decide (x.1≤x.2)))
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (runStep g p r) :=
  (pair second.fst (composition (pair second.fst.snd
    (composition (pair (pair second.fst.fst second.snd) first) (scanRealizer G P R Eq Le)))
    (normalizeStateRealizer Eq EqE))).congr (fun _=>rfl)
lemma polynomial_runStep {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} {G : Realizer g} {P : Realizer p} {R : Realizer r}
    {Eq : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {Le : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    {EqE : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hG : PolynomialTime G) (hP : PolynomialTime P) (hR : PolynomialTime R)
    (hEq : PolynomialTime Eq) (hLe : PolynomialTime Le) (hE : PolynomialTime EqE) :
    PolynomialTime (runStepRealizer G P R Eq Le EqE) := by
  unfold runStepRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_scan hG hP hR hEq hLe
  have := polynomial_normalizeState hEq hE
  tree_cost

omit [Codec I] [Codec E] [Codec B] [Codec C] [Inhabited I] in
lemma fold_runStep {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} (bs : List (List Bool×B)) (c : RunSetup C I E)
    (s : StateTable I (Finset E)) :
    bs.foldl (fun z b=>runStep g p r (b,z)) (c,s)=
      (c,bs.foldl (fun t b=>normalizeState (c.2,scan g p r ((c.1,t),b))) s) := by
  induction bs generalizing s with
  | nil=>rfl
  | cons b bs ih=>exact ih _

omit [Codec B] [Codec C] [Inhabited I] in
lemma fold_normalized_weight {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} (bs : List (List Bool×B)) (c : RunSetup C I E)
    (s : StateTable I (Finset E)) :
    weight (bs.foldl (fun t b=>normalizeState (c.2,scan g p r ((c.1,t),b))) s)≤
      max (weight s) ((weight c.2.1+1)*(weight c.2.2+3)) := by
  induction bs generalizing s with
  | nil=>exact le_max_left _ _
  | cons b bs ih=>
    exact (ih _).trans (max_le (le_trans (normalizeState_weight _ _ _) (le_max_right _ _)) (le_max_right _ _))

lemma polynomial_scanRun {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} {G : Realizer g} {P : Realizer p} {R : Realizer r}
    {Eq : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {Le : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    {EqE : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hG : PolynomialTime G) (hP : PolynomialTime P) (hR : PolynomialTime R)
    (hEq : PolynomialTime Eq) (hLe : PolynomialTime Le) (hE : PolynomialTime EqE) :
    PolynomialTime (fold (runStepRealizer G P R Eq Le EqE)) := by
  apply polynomial_fold (polynomial_runStep hG hP hR hEq hLe hE) (2*X+(X+1)*(X+3))
  intro _ ⟨c,s⟩ pre _ _
  rw [fold_runStep,weight_prod]
  have h:=fold_normalized_weight (g:=g) (p:=p) (r:=r) pre c s
  simp only [eval_mul,eval_add,eval_X,eval_one,eval_ofNat,weight_prod]
  have hm : max (weight s) ((weight c.2.1+1)*(weight c.2.2+3))≤
      weight s+(weight c.2.1+1)*(weight c.2.2+3) := max_le (by omega) (by omega)
  have hc1 : weight c.2.1≤weight c := by rcases c with ⟨a,⟨k,u⟩⟩; simp only [weight_prod]; omega
  have hc2 : weight c.2.2≤weight c := by rcases c with ⟨a,⟨k,u⟩⟩; simp only [weight_prod]; omega
  have hp : (weight c.2.1+1)*(weight c.2.2+3)≤(weight c+1)*(weight c+3) := Nat.mul_le_mul (by omega) (by omega)
  calc
    _ ≤ 1+weight c+weight s+(weight c+1)*(weight c+3) := by omega
    _ ≤ _ := Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega) (by omega))

variable {Ω D : Type} [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D]
variable (e : Ω→Finset E) (d : D→B) (c : C) (keys : List I) (hk : ∀ i,i∈keys)
    (univ : Finset E) (he : ∀ a,e a⊆univ)
variable (guides : I→Finset I) (base : Finset I) (hb : base.Nonempty)
variable (g : C×(I×I)→Bool) (hg : ∀ i j,g (c,(i,j))=decide (j∈guides i))
variable (p : LocalPairInput C I (Finset E) B→Finset E×Finset E) (r : LocalRefreshInput C I B→Finset E)
variable (sp : I→I→(Ω×Ω)→D→Ω×Ω) (sr : I→D→Ω)
    (hp : ∀ i j a b,p ((c,(i,j)),((e a.1,e a.2),d b))=(e (sp i j a b).1,e (sp i j a b).2))
    (hr : ∀ i b,r ((c,i),d b)=e (sr i b))
omit [Codec I] [Codec E] [Codec B] [Codec C] [Inhabited I] in
include hp hr hk hg he in
lemma scanRun_rep {k n : ℕ} (s : I→Ω) (bs : Fin n→((Fin k→Bool)×D)) :
    (List.ofFn (fun i=>(List.ofFn (bs i).1,d (bs i).2))).foldl
      (fun z b=>runStep g p r (b,z)) (((c,(Finset.univ,base)),(keys,univ)),stateRep keys (e ∘ s))=
    (((c,(Finset.univ,base)),(keys,univ)),stateRep keys
      (e ∘ Variation.runSample (Replica.sampleScan guides base hb sp sr k) s n bs)) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [List.ofFn_succ_last,List.foldl_append]
    change runStep g p r ((List.ofFn (bs (Fin.last n)).1,d (bs (Fin.last n)).2),_)=_
    rw [ih (fun i=>bs i.castSucc)]
    unfold runStep
    rw [scan_rep e d c keys hk guides base hb g hg p r sp sr hp hr,
      normalizeState_rep keys univ e he]
    rfl
end MatchingFPRAS.ExecutableLadder

end OAI
