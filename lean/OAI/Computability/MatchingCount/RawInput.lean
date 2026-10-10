import OAI.Computability.MatchingCount.UnaryClog

namespace OAI

section

namespace BinaryMatching.Raw.InputData
open StackCode Algorithm Raw.Optimize
abbrev Rec := ℕ×(ℕ×List Bool)
abbrev Data := ℕ×List Rec

def repr (r : Record) : Rec := (r.left,(r.right,r.multiplicity.bits))
def decodeRecord (b : ℕ) (r : Parse.RecordBits) : Rec :=
  (Parse.boundedValue b r.1,(Parse.boundedValue b r.2.1,r.2.2))
lemma decodeRecord_repr (G : Input) (b : ℕ) (hb : G.n≤b) (r : Record) (hr : r∈G.records) :
    decodeRecord b (Parse.recordRepr r)=repr r := by
  have hv := G.valid r hr
  simp only [decodeRecord,Parse.recordRepr,Parse.boundedValue_bits,repr]
  rw [min_eq_right (by omega : r.left≤b),min_eq_right (by omega : r.right≤b)]
@[fun_prop] theorem decodeRecord_poly : Poly (fun z : ℕ×Parse.RecordBits => decodeRecord z.1 z.2) := by
  unfold decodeRecord
  fun_prop

def bound (rs : List Parse.RecordBits) : ℕ := 2*rs.length+1
def decode (z : List Bool×List Parse.RecordBits) : Data :=
  (Parse.boundedValue (bound z.2) z.1,z.2.map (decodeRecord (bound z.2)))
lemma decode_encoded (G : Input) (hn : G.n≤2*G.records.length) :
    decode (G.n.bits,G.records.map Parse.recordRepr)=(G.n,G.records.map repr) := by
  unfold decode
  simp only [bound,List.length_map,Parse.boundedValue_bits]
  rw [min_eq_right (by omega : G.n≤2*G.records.length+1)]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro r hr
  exact decodeRecord_repr G _ (by omega) r hr
lemma decode_n_encoded (G : Input) :
    (decode (G.n.bits,G.records.map Parse.recordRepr)).1=min (2*G.records.length+1) G.n := by
  simp only [decode,bound,List.length_map,Parse.boundedValue_bits]
lemma decode_length (z : List Bool×List Parse.RecordBits) : (decode z).2.length=z.2.length := by simp [decode]
@[fun_prop] theorem decode_poly : Poly decode := by
  have hm := Poly.mapWith (fun z : List Bool×List Parse.RecordBits => z.2)
    (fun z : (List Bool×List Parse.RecordBits)×Parse.RecordBits => decodeRecord (bound z.1.2) z.2)
    (by fun_prop) (by unfold bound; fun_prop)
  unfold decode bound
  fun_prop

def multiplicityBits (rs : List Rec) (i j : ℕ) : List Bool :=
  ((rs.find? (fun a => a.1=i && a.2.1=j)).map (fun a => a.2.2)).getD []
lemma multiplicityBits_repr (G : Input) (i j : ℕ) :
    multiplicityBits (G.records.map repr) i j=(rawMultiplicity G i j).bits := by
  unfold multiplicityBits rawMultiplicity
  rw [List.find?_map]
  change (((G.records.find? (fun r => r.left=i && r.right=j)).map repr).map (fun a => a.2.2)).getD []=_
  cases G.records.find? (fun r => r.left=i && r.right=j) <;> rfl
lemma multiplicityBits_pair (G : Input) (e : Pair G.n) :
    multiplicityBits (G.records.map repr) e.val.1.val e.val.2.val=(multiplicity G e).bits := by
  rw [multiplicityBits_repr]
  unfold rawMultiplicity multiplicity
  cases G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) <;> rfl
@[fun_prop] theorem multiplicityBits_poly : Poly (fun z : List Rec×(ℕ×ℕ) => multiplicityBits z.1 z.2.1 z.2.2) := by
  have hf := Poly.findWith (fun z : List Rec×(ℕ×ℕ) => z.1)
    (fun z : (List Rec×(ℕ×ℕ))×Rec => decide (z.2.1=z.1.2.1) && decide (z.2.2.1=z.1.2.2)) (by fun_prop) (by fun_prop)
  unfold multiplicityBits
  fun_prop

def bitsBudget (rs : List Rec) : ℕ := (rs.map (fun r => r.2.2.length-1)).foldl max 0
lemma bitsBudget_repr (G : Input) : bitsBudget (G.records.map repr)=B G := by
  unfold bitsBudget B
  simp only [List.map_map,Function.comp_def,repr,←Parse.log2_bits_length]
@[fun_prop] theorem bitsBudget_poly : Poly bitsBudget := by
  have hf := Poly.listFoldAdd (fun z : ℕ×ℕ => max z.1 z.2) Poly.natMax 1 (by
    intro z
    simp only [code_nat_length]
    omega)
  exact Poly.comp _ (fun rs : List Rec => (rs.map (fun r => r.2.2.length-1),0)) hf (by fun_prop)

def pairs (n : ℕ) : ℕ := (upperSum n (fun _ _ => (1:ℤ))).toNat
lemma pairs_eq (n : ℕ) : pairs n=q n := by
  have h := upperSum_rep (fun _ : Pair n => (1:ℤ)) (fun _ _ => (1:ℤ)) (fun _ => rfl)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  unfold pairs
  rw [h]
  simp [q]
@[fun_prop] theorem pairs_poly : Poly pairs := by
  have h := Raw.Optimize.Compiler.upperSum_poly id (fun _ => (1:ℤ)) (by fun_prop) (by fun_prop)
  unfold pairs
  fun_prop

def betaValue (rs : List Rec) (L i j : ℕ) : ℤ :=
  let bits := multiplicityBits rs i j
  if bits.isEmpty then -(L:ℤ) else (bits.length-1:ℕ)
lemma betaValue_repr (G : Input) (e : Pair G.n) :
    betaValue (G.records.map repr) (L G) e.val.1.val e.val.2.val=Algorithm.beta G e := by
  unfold betaValue Algorithm.beta
  rw [multiplicityBits_pair]
  simp only [List.isEmpty_iff,Parse.bits_nil_iff,Parse.log2_bits_length]
@[fun_prop] theorem betaValue_poly : Poly (fun z : (List Rec×ℕ)×(ℕ×ℕ) => betaValue z.1.1 z.1.2 z.2.1 z.2.2) := by
  unfold betaValue
  fun_prop

def betaMatrix (n : ℕ) (rs : List Rec) (L : ℕ) : Matrix ℤ :=
  matrix n (fun i j => if i < j then betaValue rs L i j else 0)
lemma betaMatrix_repr (G : Input) :
    betaMatrix G.n (G.records.map repr) (L G)=tableRep (toTable (Algorithm.beta G)) := by
  apply matrix_eq_rep
  intro i j
  by_cases hij : i < j
  · simp [toTable,tabulate,hij,betaValue_repr G ⟨(i,j),hij⟩]
  · simp [toTable,tabulate,hij]
@[fun_prop] theorem betaMatrix_poly : Poly (fun z : Data×ℕ => betaMatrix z.1.1 z.1.2 z.2) := by
  have hb : Poly (fun z : ((Data×ℕ)×ℕ)×ℕ => betaValue z.1.1.1.2 z.1.1.2 z.1.2 z.2) :=
    Poly.comp _ (fun z : ((Data×ℕ)×ℕ)×ℕ => ((z.1.1.1.2,z.1.1.2),(z.1.2,z.2))) betaValue_poly (by fun_prop)
  have h := Poly.rawMatrix (fun z : Data×ℕ => z.1.1)
    (fun z : ((Data×ℕ)×ℕ)×ℕ => if decide (z.1.2<z.2) then betaValue z.1.1.1.2 z.1.1.2 z.1.2 z.2 else 0)
    (by fun_prop) (by fun_prop)
  exact h.congr (fun _ => by simp only [betaMatrix,decide_eq_true_eq])

def parameters (z : Data) : Params :=
  let q := pairs z.1
  let k := Nat.clog 2 q
  let l := 100*(z.1+bitsBudget z.2+1)^3
  let m := q*(k+l)*(2+10*z.1^2)
  let d := q*(k+l+m)^2
  ⟨z.1,q,k,l,d,m,2^(Nat.clog 2 q),betaMatrix z.1 z.2 l⟩
lemma parameters_repr (G : Input) : parameters (G.n,G.records.map repr)=params G := by
  simp only [parameters,pairs_eq,bitsBudget_repr,params,K,L,M₀,D₀,A₀]
  congr 1
  exact betaMatrix_repr G
@[fun_prop] theorem parameters_poly : Poly parameters := by
  let p (z : Data) : ParamData :=
    let q := pairs z.1
    let k := Nat.clog 2 q
    let l := 100*(z.1+bitsBudget z.2+1)^3
    let m := q*(k+l)*(2+10*z.1^2)
    let d := q*(k+l+m)^2
    (z.1,(q,(k,(l,(d,(m,(2^(Nat.clog 2 q),betaMatrix z.1 z.2 l)))))))
  have hb : Poly (fun z : Data => betaMatrix z.1 z.2 (100*(z.1+bitsBudget z.2+1)^3)) :=
    Poly.comp _ (fun z : Data => (z,100*(z.1+bitsBudget z.2+1)^3)) betaMatrix_poly (by fun_prop)
  have hpw : Poly (fun z : Data => 2^(Nat.clog 2 (pairs z.1))) :=
    Poly.comp _ (fun z : Data => pairs z.1) Poly.powClog2 (by fun_prop)
  have hp : Poly p := by dsimp only [p]; fun_prop
  exact Poly.comp _ p Raw.Optimize.Compiler.paramsOfData_poly hp
end BinaryMatching.Raw.InputData
end

end OAI
