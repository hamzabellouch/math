import OAI.Computability.MeanPayoff.Counters

namespace OAI

section
namespace MeanPayoff.TreeDevice
open BinaryData
namespace Prefix

def suffix : List Bool → List Bool
  | [] => []
  | false::xs => xs
  | true::xs => suffix xs

theorem fold_suffix (c : Count) (xs : List Bool) :
    (Fold.fold step (false,(c,[])) xs).2.2.reverse = suffix xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false =>
      change (Fold.fold step (true,(c,[])) bs).2.2.reverse = bs
      rw [read_from_done]
      simp
    | true =>
      change (Fold.fold step (false,(()::c,[])) bs).2.2.reverse = suffix bs
      exact ih _

theorem read_suffix (xs : List Bool) : (read xs).2=suffix xs := fold_suffix [] xs

theorem suffix_isSuffix (xs : List Bool) : ∃ pre, pre++suffix xs=xs := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨[false],rfl⟩
    | true =>
      obtain ⟨pre,hp⟩ := ih
      exact ⟨true::pre,by simpa only [List.cons_append,suffix] using congrArg (List.cons true) hp⟩
end Prefix

theorem listTree_append_right_le {α : Type} (ea : α → Data) (xs ys : List α) :
    treeSize (listTree ea ys) ≤ treeSize (listTree ea (xs++ys)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,listTree,treeSize_pair]; omega

theorem listTree_drop_le {α : Type} (ea : α → Data) (xs : List α) (n : ℕ) :
    treeSize (listTree ea (xs.drop n)) ≤ treeSize (listTree ea xs) := by
  have h := listTree_append_right_le ea (xs.take n) (xs.drop n)
  simpa only [List.take_append_drop] using h

namespace Prefix
theorem remainder_size (xs : List Bool) : treeSize (listTree boolData (read xs).2) ≤ treeSize (listTree boolData xs) := by
  rw [read_suffix]
  obtain ⟨pre,hp⟩ := suffix_isSuffix xs
  simpa only [hp] using listTree_append_right_le boolData pre (suffix xs)
end Prefix

namespace Split
theorem fold_rest (xs acc : List Bool) (ks : Median.Count) :
    (Fold.fold step (acc,xs) ks).2 = xs.drop ks.length := by
  induction ks generalizing xs acc with
  | nil => rfl
  | cons u ks ih =>
    change (Fold.fold step (xs.headD false::acc,xs.tail) ks).2 = _
    rw [ih]
    cases xs <;> simp

theorem rest (xs : List Bool) (ks : Median.Count) : (split (xs,ks)).2 = xs.drop ks.length := fold_rest _ _ _

theorem remainder_size (xs : List Bool) (ks : Median.Count) :
    treeSize (listTree boolData (split (xs,ks)).2) ≤ treeSize (listTree boolData xs) := by
  rw [rest]
  exact listTree_drop_le _ _ _
end Split

namespace IntegerRead
theorem nat_remainder_size (xs : List Bool) :
    treeSize (listTree boolData (readNat xs).2) ≤ treeSize (listTree boolData xs) :=
  (Split.remainder_size (Prefix.read xs).2 (Prefix.read xs).1).trans (Prefix.remainder_size xs)

theorem int_remainder_size (xs : List Bool) :
    treeSize (listTree boolData (readInt xs).2) ≤ treeSize (listTree boolData xs) := by
  have h := nat_remainder_size xs.tail
  have ht : treeSize (listTree boolData xs.tail) ≤ treeSize (listTree boolData xs) := by
    cases xs <;> simp [listTree] ; omega
  exact h.trans ht
end IntegerRead

namespace EdgeRead
theorem remainder_size (env xs : List Bool) :
    treeSize (restData (read (env,xs)).2) ≤ treeSize (restData xs) := by
  exact (IntegerRead.int_remainder_size (IntegerRead.readNat (IntegerRead.readNat xs).2).2).trans
    ((IntegerRead.nat_remainder_size (IntegerRead.readNat xs).2).trans (IntegerRead.nat_remainder_size xs))
end EdgeRead
end MeanPayoff.TreeDevice
namespace MeanPayoff.TreeDevice.StreamFold
open BinaryData
abbrev State (α β ρ : Type) := α × (List β × ρ)
def stateData {α β ρ : Type} (ea : α → Data) (eb : β → Data) (er : ρ → Data) := product ea (product (listTree eb) er)
def inputData {α β ρ : Type} (ea : α → Data) (eb : β → Data) (er : ρ → Data) := product (stateData ea eb er) Median.unitData

def step {α β ρ : Type} (f : α × ρ → β × ρ) (z : State α β ρ × Unit) : State α β ρ :=
  let p := f (z.1.1,z.1.2.2)
  (z.1.1,(p.1::z.1.2.1,p.2))

variable {α β ρ : Type} (ea : α → Data) (eb : β → Data) (er : ρ → Data)
noncomputable def envDevice : Device (inputData ea eb er) ea (fun z : State α β ρ × Unit => z.1.1) :=
  compose (first (stateData ea eb er) Median.unitData) (first ea (product (listTree eb) er))
noncomputable def localDevice : Device (inputData ea eb er) (product (listTree eb) er) (fun z : State α β ρ × Unit => z.1.2) :=
  compose (first (stateData ea eb er) Median.unitData) (second ea (product (listTree eb) er))
noncomputable def accDevice : Device (inputData ea eb er) (listTree eb) (fun z : State α β ρ × Unit => z.1.2.1) :=
  compose (localDevice ea eb er) (first (listTree eb) er)
noncomputable def streamDevice : Device (inputData ea eb er) er (fun z : State α β ρ × Unit => z.1.2.2) :=
  compose (localDevice ea eb er) (second (listTree eb) er)

variable {ea eb er} {f : α × ρ → β × ρ} (F : Device (product ea er) (product eb er) f)
noncomputable def parseDevice : Device (inputData ea eb er) (product eb er)
    (fun z : State α β ρ × Unit => f (z.1.1,z.1.2.2)) :=
  compose (fanout (envDevice ea eb er) (streamDevice ea eb er)) F
noncomputable def itemDevice : Device (inputData ea eb er) eb
    (fun z : State α β ρ × Unit => (f (z.1.1,z.1.2.2)).1) :=
  compose (parseDevice F) (first eb er)
noncomputable def restDevice : Device (inputData ea eb er) er
    (fun z : State α β ρ × Unit => (f (z.1.1,z.1.2.2)).2) :=
  compose (parseDevice F) (second eb er)
noncomputable def newAccDevice : Device (inputData ea eb er) (listTree eb)
    (fun z : State α β ρ × Unit => (f (z.1.1,z.1.2.2)).1::z.1.2.1) :=
  compose (fanout (itemDevice F) (accDevice ea eb er)) (Lists.consDevice eb)
noncomputable def stepDevice : Device (inputData ea eb er) (stateData ea eb er) (step f) :=
  fanout (envDevice ea eb er) (fanout (newAccDevice F) (restDevice F))

variable (ea eb er)
theorem env_linear : LinearCost (envDevice ea eb er) := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem local_linear : LinearCost (localDevice ea eb er) := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem acc_linear : LinearCost (accDevice ea eb er) := LinearCost.compose (local_linear _ _ _) (LinearCost.first _ _)
theorem stream_linear : LinearCost (streamDevice ea eb er) := LinearCost.compose (local_linear _ _ _) (LinearCost.second _ _)
variable {ea eb er}
theorem parse_polynomial (hF : PolynomialCost F) : PolynomialCost (parseDevice F) :=
  PolynomialCost.compose (LinearCost.fanout (env_linear _ _ _) (stream_linear _ _ _)).polynomial hF
theorem item_polynomial (hF : PolynomialCost F) : PolynomialCost (itemDevice F) :=
  PolynomialCost.compose (parse_polynomial F hF) (LinearCost.first _ _).polynomial
theorem rest_polynomial (hF : PolynomialCost F) : PolynomialCost (restDevice F) :=
  PolynomialCost.compose (parse_polynomial F hF) (LinearCost.second _ _).polynomial
theorem newAcc_polynomial (hF : PolynomialCost F) : PolynomialCost (newAccDevice F) :=
  PolynomialCost.compose (PolynomialCost.fanout (item_polynomial F hF) (acc_linear _ _ _).polynomial) (LinearCost.cons _).polynomial
theorem step_polynomial (hF : PolynomialCost F) : PolynomialCost (stepDevice F) :=
  PolynomialCost.fanout (env_linear _ _ _).polynomial
    (PolynomialCost.fanout (newAcc_polynomial F hF) (rest_polynomial F hF))

include F in
theorem fold_bound (K d : ℕ) (hF : ∀ z, F.limit z≤K*(treeSize (product ea er z)+1)^d)
    (hr : ∀ p r, treeSize (er (f (p,r)).2)≤treeSize (er r))
    (s : State α β ρ) (xs : List Unit) (N : ℕ)
    (hN : treeSize (ea s.1)+treeSize (er s.2.2)+2 ≤ N) :
    (Fold.fold (step f) s xs).1=s.1 ∧
    treeSize (er (Fold.fold (step f) s xs).2.2)≤treeSize (er s.2.2) ∧
    treeSize (listTree eb (Fold.fold (step f) s xs).2.1)≤
      treeSize (listTree eb s.2.1)+xs.length*(N+K*N^d+1) := by
  induction xs generalizing s with
  | nil => simp [Fold.fold]
  | cons u xs ih =>
    let s' := step f (s,u)
    have hre := hr s.1 s.2.2
    have hh := ih s' (by change treeSize (ea s.1)+treeSize (er (f (s.1,s.2.2)).2)+2≤N; omega)
    have ho := output_size F (s.1,s.2.2)
    have hx : treeSize (product ea er (s.1,s.2.2))+1 ≤ N := by simp only [product,treeSize_pair]; omega
    have ht := (hF (s.1,s.2.2)).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hx d))
    change (Fold.fold (step f) s' xs).1=s.1 ∧ _
    refine ⟨hh.1,hh.2.1.trans hre,?_⟩
    have hs : treeSize (listTree eb s'.2.1)≤treeSize (listTree eb s.2.1)+N+K*N^d+1 := by
      simp only [s',step,listTree,treeSize_pair,product] at *
      omega
    have hh' := hh.2.2
    change treeSize (listTree eb (Fold.fold (step f) s' xs).2.1)≤_
    simp only [List.length_cons]
    nlinarith
end MeanPayoff.TreeDevice.StreamFold
namespace MeanPayoff.TreeDevice.Fold
open BinaryData

theorem polynomial_of_prefix {α β : Type} {ea : α → Data} {eb : β → Data}
    {f : α × β → α} {F : Device (product ea eb) ea f} (hF : PolynomialCost F)
    (B e : ℕ) (ha : ∀ a xs k, k≤xs.length →
      treeSize (ea (fold f a (xs.take k)))≤B*(treeSize (product ea (listTree eb) (a,xs))+1)^e) :
    PolynomialCost (device F) := by
  obtain ⟨K,d,hK⟩ := hF
  refine ⟨12*B+K*(B+3)^d+13,(e+1)*(d+1)+1,?_⟩
  rintro ⟨a,xs⟩
  let N := treeSize (product ea (listTree eb) (a,xs))+1
  have hN : 1≤N := by dsimp [N]; omega
  have hn : N≤N^(e+1) := by simpa only [pow_one] using pow_le_pow_right' hN (show 1≤e+1 by omega)
  have hp : 1≤N^(e+1) := one_le_pow₀ hN
  have he : N^e≤N^(e+1) := pow_le_pow_right' hN (by omega)
  have hs : treeSize (listTree eb xs)≤N := by simp only [N,product,treeSize_pair]; omega
  have hl : xs.length+1≤N := by have := list_length_le_size eb xs; simp only [N,product,treeSize_pair]; omega
  have ht := time_of_prefix_bound F K d (B*N^(e+1)) N hK a xs hs
    (by intro k hk; exact (ha a xs k hk).trans (Nat.mul_le_mul_left B he))
  have hb : B*N^(e+1)+N+2≤(B+3)*N^(e+1) := by nlinarith
  have hbpow := Nat.pow_le_pow_left hb d
  rw [mul_pow,← pow_mul] at hbpow
  have hd : N^((e+1)*d)≤N^((e+1)*(d+1)) := pow_le_pow_right' hN (by nlinarith)
  have hg : N^(e+1)≤N^((e+1)*(d+1)) := pow_le_pow_right' hN (by nlinarith)
  have hr : 1≤N^((e+1)*(d+1)) := one_le_pow₀ hN
  have hbp := hbpow.trans (Nat.mul_le_mul_left ((B+3)^d) hd)
  have hlocal : 12*(B*N^(e+1))+K*(B*N^(e+1)+N+2)^d+11 ≤
      (12*B+K*(B+3)^d+11)*N^((e+1)*(d+1)) := by
    nlinarith
  have hall := ht.trans (Nat.mul_le_mul hl hlocal)
  have hpos : 1≤N^((e+1)*(d+1)+1) := one_le_pow₀ hN
  change time F a xs+2≤(12*B+K*(B+3)^d+13)*N^((e+1)*(d+1)+1)
  rw [pow_succ] at hpos ⊢
  nlinarith
end MeanPayoff.TreeDevice.Fold

namespace MeanPayoff.TreeDevice.StreamFold
open BinaryData

theorem polynomial {α β ρ : Type} {ea : α → Data} {eb : β → Data} {er : ρ → Data}
    {f : α × ρ → β × ρ} (F : Device (product ea er) (product eb er) f)
    (hF : PolynomialCost F) (hr : ∀ p r, treeSize (er (f (p,r)).2)≤treeSize (er r)) :
    PolynomialCost (Fold.device (stepDevice F)) := by
  obtain ⟨K,d,hK⟩ := hF
  apply Fold.polynomial_of_prefix (step_polynomial F ⟨K,d,hK⟩) (K+4) (d+2)
  intro s xs k hk
  let N := treeSize (product (stateData ea eb er) (listTree Median.unitData) (s,xs))+1
  have hN : 1≤N := by dsimp [N]; omega
  have hs : treeSize (ea s.1)+treeSize (listTree eb s.2.1)+treeSize (er s.2.2)+treeSize (listTree Median.unitData xs)+4=N := by
    simp only [N,product,stateData,treeSize_pair]; omega
  have hi : treeSize (ea s.1)+treeSize (er s.2.2)+2≤N := by have := treeSize_pos (listTree eb s.2.1); omega
  have hl : (xs.take k).length≤N := by have := list_length_le_size Median.unitData xs; have := List.length_take_le k xs; omega
  have hb := fold_bound F K d hK hr s (xs.take k) N hi
  have henv := hb.1
  have hrest := hb.2.1
  have hacc := hb.2.2
  have hlast := Nat.mul_le_mul_right (N+K*N^d+1) hl
  have hp : N≤N^(d+1) := by simpa only [pow_one] using pow_le_pow_right' hN (show 1≤d+1 by omega)
  have hd : N^d≤N^(d+1) := pow_le_pow_right' hN (by omega)
  have hone : 1≤N^(d+1) := one_le_pow₀ hN
  have hfactor : N+K*N^d+1≤(K+2)*N^(d+1) := by nlinarith
  have hmul := Nat.mul_le_mul_left N hfactor
  change treeSize (stateData ea eb er (Fold.fold (step f) s (xs.take k)))≤(K+4)*N^(d+2)
  simp only [stateData,product,treeSize_pair,henv]
  rw [show d+2=(d+1)+1 by omega,pow_succ]
  nlinarith
end MeanPayoff.TreeDevice.StreamFold
namespace MeanPayoff.TreeDevice.EdgesRead
open BinaryData
abbrev Edge := EdgeRead.Edge
abbrev Count := Median.Count
abbrev State := StreamFold.State (List Bool) Edge (List Bool)
abbrev Args := List Bool × (List Bool × Count)
def restData := listTree boolData
def countData := listTree Median.unitData
def edgesData := listTree EdgeRead.edgeData
def stateData := StreamFold.stateData restData EdgeRead.edgeData restData
def argsData := product restData (product restData countData)
def outputData := product edgesData restData

def read (z : Args) : List Edge × List Bool :=
  let s := Fold.fold (StreamFold.step EdgeRead.read) (z.1,([],z.2.1)) z.2.2
  (s.2.1.reverse,s.2.2)

noncomputable def moreDevice : Device argsData (product restData countData) (fun z : Args => z.2) := second restData (product restData countData)
noncomputable def streamDevice : Device argsData restData (fun z : Args => z.2.1) :=
  compose moreDevice (first restData countData)
noncomputable def countDevice : Device argsData countData (fun z : Args => z.2.2) :=
  compose moreDevice (second restData countData)
noncomputable def stateDevice : Device argsData stateData (fun z : Args => (z.1,([],z.2.1))) :=
  fanout (first restData (product restData countData)) (compose streamDevice (Lists.nilPrefix restData EdgeRead.edgeData))
noncomputable def initDevice : Device argsData (product stateData countData)
    (fun z : Args => ((z.1,([],z.2.1)),z.2.2)) := fanout stateDevice countDevice
noncomputable def finishDevice : Device stateData outputData (fun s : State => (s.2.1.reverse,s.2.2)) :=
  compose (second restData (product edgesData restData))
    (pairMap (Lists.reverseDevice EdgeRead.edgeData) (identity restData))
noncomputable def foldDevice : Device (product stateData countData) outputData
    (fun z : State × Count => let s := Fold.fold (StreamFold.step EdgeRead.read) z.1 z.2; (s.2.1.reverse,s.2.2)) :=
  compose (Fold.device (StreamFold.stepDevice EdgeRead.device)) finishDevice
noncomputable def device : Device argsData outputData read := compose initDevice foldDevice

def lower (e : BinaryInput.Edge) : Edge := (List.replicate e.1 (),(List.replicate e.2.1 (),EdgeRead.encodedWord e.2.2))
def code (es : List BinaryInput.Edge) : List Bool := (es.map BinaryInput.encodeEdge).flatten

theorem fold_exact (es : List BinaryInput.Edge) (env suffix : List Bool) (acc : List Edge)
    (hd : ∀ e∈es, e.1≤env.length ∧ e.2.1≤env.length) :
    Fold.fold (StreamFold.step EdgeRead.read) (env,(acc,code es++suffix)) (List.replicate es.length ()) =
      (env,((es.map lower).reverse++acc,suffix)) := by
  induction es generalizing acc with
  | nil => simp [code,Fold.fold]
  | cons e es ih =>
    have he := hd e (by simp)
    have hread := EdgeRead.exact e.1 e.2.1 e.2.2 env (code es++suffix) he.1 he.2
    have hc : code (e::es)++suffix=BinaryInput.encodeEdge e++(code es++suffix) := by simp [code,List.append_assoc]
    rw [hc]
    simp only [List.length_cons,List.replicate_succ,Fold.fold,List.foldl_cons]
    change Fold.fold (StreamFold.step EdgeRead.read)
      (StreamFold.step EdgeRead.read ((env,(acc,BinaryInput.encodeEdge e++(code es++suffix))),()))
      (List.replicate es.length ()) = _
    simp only [StreamFold.step,hread]
    change Fold.fold (StreamFold.step EdgeRead.read) (env,(lower e::acc,code es++suffix)) _ = _
    rw [ih (lower e::acc) (by intro x hx; exact hd x (by simp [hx]))]
    simp [List.reverse_cons,List.append_assoc]

theorem exact (es : List BinaryInput.Edge) (env suffix : List Bool)
    (hd : ∀ e∈es, e.1≤env.length ∧ e.2.1≤env.length) :
    read (env,(code es++suffix,List.replicate es.length ())) = (es.map lower,suffix) := by
  simp only [read,fold_exact es env suffix [] hd,List.append_nil,List.reverse_reverse]

theorem more_linear : LinearCost moreDevice := LinearCost.second _ _
theorem stream_linear : LinearCost streamDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem count_linear : LinearCost countDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem state_linear : LinearCost stateDevice :=
  LinearCost.fanout (LinearCost.first _ _) (LinearCost.compose stream_linear (LinearCost.nilPrefix _ _))
theorem init_linear : LinearCost initDevice := LinearCost.fanout state_linear count_linear
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.compose (LinearCost.second _ _).polynomial
    (PolynomialCost.pairMap (PolynomialCost.reverse _) (LinearCost.identity _).polynomial)
theorem fold_polynomial : PolynomialCost foldDevice :=
  PolynomialCost.compose (StreamFold.polynomial EdgeRead.device EdgeRead.polynomial EdgeRead.remainder_size) finish_polynomial
theorem polynomial : PolynomialCost device := PolynomialCost.compose init_linear.polynomial fold_polynomial
end MeanPayoff.TreeDevice.EdgesRead
end

end OAI
