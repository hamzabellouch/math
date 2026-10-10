import OAI.Computability.MeanPayoff.PolynomialCosts

namespace OAI

section

namespace MeanPayoff.TreeDevice.EnvMap
open BinaryData

abbrev Acc (α γ : Type) := α × List γ

def step {α β γ : Type} (f : α × β → γ) (z : Acc α γ × β) : Acc α γ :=
  (z.1.1,f (z.1.1,z.2)::z.1.2)

noncomputable def argument {α β γ : Type} (ea : α → Data) (eb : β → Data) (ec : γ → Data) :
    Device (product (product ea (listTree ec)) eb) (product ea eb)
      (fun z : Acc α γ × β => (z.1.1,z.2)) :=
  fanout (compose (first (product ea (listTree ec)) eb) (first ea (listTree ec)))
    (second (product ea (listTree ec)) eb)

noncomputable def stepDevice {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) :
    Device (product (product ea (listTree ec)) eb) (product ea (listTree ec)) (step f) :=
  fanout (compose (first (product ea (listTree ec)) eb) (first ea (listTree ec)))
    (compose (fanout (compose (argument ea eb ec) F)
      (compose (first (product ea (listTree ec)) eb) (second ea (listTree ec)))) (Lists.consDevice ec))

theorem fold_eq {α β γ : Type} (f : α × β → γ) (p : α) (xs : List β) (acc : List γ) :
    Fold.fold (step f) (p,acc) xs = (p,(xs.map (fun x => f (p,x))).reverse++acc) := by
  induction xs generalizing acc with
  | nil => simp [Fold.fold]
  | cons x xs ih =>
    change Fold.fold (step f) (p,f (p,x)::acc) xs = _
    rw [ih]
    simp [List.reverse_cons,List.append_assoc]

noncomputable def device {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) :
    Device (product ea (listTree eb)) (listTree ec)
      (fun z : α × List β => z.2.map (fun x => f (z.1,x))) := by
  let initial := fanout (compose (first ea (listTree eb)) (Lists.nilSuffix ea ec))
    (second ea (listTree eb))
  let P := compose initial (compose (Fold.device (stepDevice F))
    (compose (second ea (listTree ec)) (Lists.reverseDevice ec)))
  exact P.extFun (by
    rintro ⟨p,xs⟩
    change (Fold.fold (step f) (p,[]) xs).2.reverse = _
    rw [fold_eq]
    simp)

end MeanPayoff.TreeDevice.EnvMap

namespace MeanPayoff.TreeDevice.Graph
open BinaryData

abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev Pot := List W
abbrev Edge := Count × W
abbrev Edges := Edge × List Edge
abbrev Vertex := Bool × Edges
abbrev Batch := EdgeScan.Pair × List EdgeScan.Pair

def countData := listTree Median.unitData
def potData := listTree wordData
def edgeData := product countData wordData
def edgesData := product edgeData (listTree edgeData)
def vertexData := product Compare.bitTree edgesData
def valuePairData := product wordData wordData
def batchData := product valuePairData (listTree valuePairData)

def lookup (z : Pot × Count) : W := (z.1.drop z.2.length).headD Median.zeroWord

noncomputable def lookupDevice : Device (product potData countData) wordData lookup :=
  compose (Median.dropDevice wordData) (Head.device wordData Median.zeroWord)

def edgePair (z : Pot × Edge) : EdgeScan.Pair := (z.2.2,lookup (z.1,z.2.1))

noncomputable def edgeDevice : Device (product potData edgeData) valuePairData edgePair :=
  fanout (compose (second potData edgeData) (second countData wordData))
    (compose (fanout (first potData edgeData)
      (compose (second potData edgeData) (first countData wordData))) lookupDevice)

def batch (z : Pot × Edges) : Batch :=
  (edgePair (z.1,z.2.1),z.2.2.map (fun e => edgePair (z.1,e)))

noncomputable def batchDevice : Device (product potData edgesData) batchData batch :=
  fanout (compose (fanout (first potData edgesData)
      (compose (second potData edgesData) (first edgeData (listTree edgeData)))) edgeDevice)
    (compose (fanout (first potData edgesData)
      (compose (second potData edgesData) (second edgeData (listTree edgeData)))) (EnvMap.device edgeDevice))

def vertex (z : Pot × Vertex) : W :=
  if z.2.1 then EdgeScan.maxScan (batch (z.1,z.2.2)) else EdgeScan.minScan (batch (z.1,z.2.2))

noncomputable def vertexDevice : Device (product potData vertexData) wordData vertex := by
  let B := compose (fanout (first potData vertexData)
    (compose (second potData vertexData) (second Compare.bitTree edgesData))) batchDevice
  exact branch (compose (second potData vertexData) (first Compare.bitTree edgesData))
    (compose B EdgeScan.maxDevice) (compose B EdgeScan.minDevice)

noncomputable def device : Device (product potData (listTree vertexData)) potData
    (fun z : Pot × List Vertex => z.2.map (fun v => vertex (z.1,v))) := EnvMap.device vertexDevice

def codeEdge (G : Game) (w : Fin G.m → W) (e : Fin G.m) : Edge :=
  (List.replicate (G.head e).val (),w e)

def codePot {n : ℕ} (p : Fin n → W) : Pot := List.ofFn p

theorem lookup_exact {n : ℕ} (p : Fin n → W) (i : Fin n) :
    lookup (codePot p,List.replicate i.val ()) = p i := by
  unfold lookup codePot
  rw [List.length_replicate,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp [i.isLt]

theorem edgePair_exact (G : Game) (p : Fin G.n → W) (w : Fin G.m → W) (e : Fin G.m) :
    edgePair (codePot p,codeEdge G w e) = (w e,p (G.head e)) := by
  simp only [edgePair,codeEdge,lookup_exact]

theorem batch_represents (G : Game) (p : Fin G.n → W) (w : Fin G.m → W)
    (hw : ∀ e, (w e).val = transformed G e) (v : Fin G.n)
    (e : Fin G.m) (es : List (Fin G.m))
    (hes : ∀ f, f∈e::es ↔ f∈outgoing G v) :
    EdgeScan.Represents G (fun i => (p i).val) v
      (batch (codePot p,(codeEdge G w e,es.map (codeEdge G w)))) := by
  have eqs : (batch (codePot p,(codeEdge G w e,es.map (codeEdge G w)))).1::
      (batch (codePot p,(codeEdge G w e,es.map (codeEdge G w)))).2 =
      (e::es).map (fun f => (w f,p (G.head f))) := by
    simp only [batch,edgePair_exact,List.map_map,List.map_cons,Function.comp_def]
  constructor
  · intro ab hab
    rw [eqs] at hab
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hab
    exact ⟨f,(hes f).mp hf,by rw [hw]⟩
  · intro f hf
    refine ⟨(w f,p (G.head f)),?_,?_⟩
    · rw [eqs]
      exact List.mem_map.mpr ⟨f,(hes f).mpr hf,rfl⟩
    · rw [hw]

theorem vertex_exact (G : Game) (p : Fin G.n → W) (w : Fin G.m → W)
    (hw : ∀ e, (w e).val = transformed G e) (v : Fin G.n)
    (e : Fin G.m) (es : List (Fin G.m)) (hes : ∀ f, f∈e::es ↔ f∈outgoing G v) :
    (vertex (codePot p,(G.maxOwner v,(codeEdge G w e,es.map (codeEdge G w))))).val =
      operator G (fun i => (p i).val) v := by
  have hh := EdgeScan.operator_exact G (fun i => (p i).val) v _ (batch_represents G p w hw v e es hes)
  simpa only [vertex,apply_ite] using hh

end MeanPayoff.TreeDevice.Graph

namespace MeanPayoff.TreeDevice.EnvMap
open BinaryData

theorem step_limit {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) (p : α) (acc : List γ) (b : β) :
    (stepDevice F).limit ((p,acc),b) ≤
      1000*(treeSize (ea p)+treeSize (listTree ec acc)+treeSize (eb b)+F.limit (p,b)+1) := by
  have ho := output_size F (p,b)
  simp only [product,treeSize_pair] at ho
  simp only [stepDevice,argument,fanout_limit,compose_limit,first_limit,second_limit,
    Function.comp_def,product,treeSize_pair,listTree_cons,Lists.consDevice,Device.recode,identity]
  nlinarith

def resource {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) (p : α) (acc : List γ) (xs : List β) : ℕ :=
  treeSize (ea p)+treeSize (listTree ec acc)+treeSize (listTree eb xs)+
    xs.length*(treeSize (ea p)+1)+(xs.map (fun b => F.limit (p,b))).sum+1

theorem resource_decrease {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) (p : α) (acc : List γ) (b : β) (bs : List β) :
    resource F p (f (p,b)::acc) bs ≤ resource F p acc (b::bs) := by
  have ho := output_size F (p,b)
  simp only [product,treeSize_pair] at ho
  simp only [resource,listTree,treeSize_pair,List.length_cons,List.map_cons,List.sum_cons]
  nlinarith

theorem fold_time {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} (F : Device (product ea eb) ec f) (p : α) (acc : List γ) (xs : List β) :
    Fold.time (stepDevice F) (p,acc) xs ≤ 1200*(xs.length+1)*resource F p acc xs := by
  induction xs generalizing acc with
  | nil =>
    simp only [Fold.time,resource,product,treeSize_pair,listTree,treeSize_nil,List.length_nil,List.map_nil,List.sum_nil]
    nlinarith
  | cons b bs ih =>
    have hs := step_limit F p acc b
    have hd := resource_decrease F p acc b bs
    have hr := ih (f (p,b)::acc)
    have hm := Nat.mul_le_mul_left (1200*(bs.length+1)) hd
    have hlocal : treeSize (ea p)+treeSize (listTree ec acc)+treeSize (eb b)+F.limit (p,b)+1 ≤ resource F p acc (b::bs) := by
      simp only [resource,listTree,treeSize_pair,List.length_cons,List.map_cons,List.sum_cons]
      omega
    change 12*treeSize (product ea (listTree ec) (p,acc))+(stepDevice F).limit ((p,acc),b)+11+
      Fold.time (stepDevice F) (step f ((p,acc),b)) bs ≤ _
    dsimp only [step]
    simp only [product,treeSize_pair,List.length_cons]
    have hp : 1 ≤ resource F p acc (b::bs) := by unfold resource; omega
    nlinarith

theorem fold_polynomial {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} {F : Device (product ea eb) ec f} (hF : PolynomialCost F) :
    PolynomialCost (Fold.device (stepDevice F)) := by
  obtain ⟨K,d,hK⟩ := hF
  refine ⟨1200*(K+3)+2,d+3,?_⟩
  rintro ⟨⟨p,acc⟩,xs⟩
  let N := treeSize (product (product ea (listTree ec)) (listTree eb) ((p,acc),xs))+1
  have hN : N = treeSize (ea p)+treeSize (listTree ec acc)+treeSize (listTree eb xs)+3 := by
    simp [N,product,treeSize_pair]; omega
  have hn : 1 ≤ N := by omega
  have hlen : xs.length+1 ≤ N := (list_length_le_size eb xs).trans (by omega)
  have he : ∀ x∈xs, F.limit (p,x) ≤ K*N^d := by
    intro x hx
    have hh := element_size_le eb hx
    have hi : treeSize (product ea eb (p,x))+1 ≤ N := by
      simp only [product,treeSize_pair]; omega
    exact (hK (p,x)).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hi d))
  have hsum : (xs.map (fun b => F.limit (p,b))).sum ≤ xs.length*(K*N^d) := by
    have hh := List.sum_le_length_nsmul (xs.map (fun b => F.limit (p,b))) (K*N^d) (by
      intro y hy
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
      exact he b hb)
    simpa using hh
  have hs := hsum.trans (Nat.mul_le_mul_right (K*N^d) (show xs.length ≤ N by omega))
  have hd : N^(d+1) ≤ N^(d+2) := pow_le_pow_right' hn (by omega)
  have htwo : N^2 ≤ N^(d+2) := pow_le_pow_right' hn (by omega)
  have hlin : N ≤ N^(d+2) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+2 by omega)
  have hpm := Nat.mul_le_mul (show xs.length ≤ N by omega) (show treeSize (ea p)+1 ≤ N by omega)
  have hcost : resource F p acc xs ≤ (K+3)*N^(d+2) := by
    unfold resource
    rw [pow_succ] at hd
    rw [pow_two] at htwo
    have hh := Nat.mul_le_mul_left K hd
    nlinarith
  have ht := fold_time F p acc xs
  have hl := Nat.mul_le_mul (show 1200*(xs.length+1) ≤ 1200*N from Nat.mul_le_mul_left _ hlen) hcost
  have hpos : 1 ≤ N^(d+3) := one_le_pow₀ hn
  change Fold.time (stepDevice F) (p,acc) xs+2 ≤ (1200*(K+3)+2)*N^(d+3)
  rw [show d+3=(d+2)+1 by omega,pow_succ] at hpos ⊢
  nlinarith

theorem polynomial {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α × β → γ} {F : Device (product ea eb) ec f} (hF : PolynomialCost F) :
    PolynomialCost (device F) := by
  apply PolynomialCost.compose
    (LinearCost.fanout (LinearCost.compose (LinearCost.first _ _) (LinearCost.nilSuffix _ _))
      (LinearCost.second _ _)).polynomial
  apply PolynomialCost.compose (fold_polynomial hF)
  exact PolynomialCost.compose (LinearCost.second _ _).polynomial (PolynomialCost.reverse _)

end MeanPayoff.TreeDevice.EnvMap

namespace MeanPayoff.TreeDevice
open BinaryData
namespace PolynomialCost

theorem branch {α β : Type} {ea : α → Data} {eb : β → Data}
    {test : α → Bool} {f g : α → β} {T : Device ea Compare.bitTree test}
    {F : Device ea eb f} {G : Device ea eb g}
    (hT : PolynomialCost T) (hF : PolynomialCost F) (hG : PolynomialCost G) :
    PolynomialCost (TreeDevice.branch T F G) :=
  compose (fanout hT (fanout hF hG)) (LinearCost.select _).polynomial

end PolynomialCost
namespace EdgeScan

theorem max_polynomial : PolynomialCost maxDevice := by
  apply PolynomialCost.compose
    (PolynomialCost.pairMap LinearCost.add.polynomial (PolynomialCost.map LinearCost.add.polynomial))
  apply Fold.polynomial LinearCost.max.polynomial
  intro a b
  rcases high_mem (a,b) with h | h <;> rw [h] <;> dsimp only <;> omega

theorem min_polynomial : PolynomialCost minDevice := by
  apply PolynomialCost.compose
    (PolynomialCost.pairMap LinearCost.add.polynomial (PolynomialCost.map LinearCost.add.polynomial))
  apply Fold.polynomial LinearCost.min.polynomial
  intro a b
  rcases low_mem (a,b) with h | h <;> rw [h] <;> dsimp only <;> omega

end EdgeScan
namespace Graph

theorem lookup_polynomial : PolynomialCost lookupDevice :=
  PolynomialCost.compose (Median.drop_polynomial _) (LinearCost.head _ _).polynomial

theorem edge_polynomial : PolynomialCost edgeDevice := by
  refine PolynomialCost.fanout ?_ ?_
  · exact (LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)).polynomial
  · exact PolynomialCost.compose
      (LinearCost.fanout (LinearCost.first _ _)
        (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _))).polynomial lookup_polynomial

theorem batch_polynomial : PolynomialCost batchDevice := by
  refine PolynomialCost.fanout ?_ ?_
  · exact PolynomialCost.compose
      (LinearCost.fanout (LinearCost.first _ _)
        (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _))).polynomial edge_polynomial
  · exact PolynomialCost.compose
      (LinearCost.fanout (LinearCost.first _ _)
        (LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _))).polynomial
      (EnvMap.polynomial edge_polynomial)

theorem vertex_polynomial : PolynomialCost vertexDevice := by
  have hB := PolynomialCost.compose
    (LinearCost.fanout (LinearCost.first potData vertexData)
      (LinearCost.compose (LinearCost.second potData vertexData)
        (LinearCost.second Compare.bitTree edgesData))).polynomial batch_polynomial
  exact PolynomialCost.branch
    (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)).polynomial
    (PolynomialCost.compose hB EdgeScan.max_polynomial)
    (PolynomialCost.compose hB EdgeScan.min_polynomial)

theorem polynomial : PolynomialCost device := EnvMap.polynomial vertex_polynomial

end Graph
end MeanPayoff.TreeDevice
end

end OAI
