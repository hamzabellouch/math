import OAI.Computability.MeanPayoff.ArithmeticDevices

namespace OAI

section

namespace MeanPayoff.TreeDevice
open BinaryData

def PolynomialCost {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : Prop := ∃ K d : ℕ, ∀ x, F.limit x ≤ K*(treeSize (ea x)+1)^d

theorem LinearCost.polynomial {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    {F : Device ea eb f} (h : LinearCost F) : PolynomialCost F := by
  obtain ⟨K,hK⟩ := h
  exact ⟨K,1,by simpa using hK⟩

namespace PolynomialCost

theorem compose {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} {F : Device ea eb f} {G : Device eb ec g}
    (hF : PolynomialCost F) (hG : PolynomialCost G) : PolynomialCost (TreeDevice.compose F G) := by
  obtain ⟨K,d,hK⟩ := hF
  obtain ⟨M,e,hM⟩ := hG
  let D := d+1+(d+1)*e
  refine ⟨K+M*(K+2)^e+2,D,?_⟩
  intro x
  let N := treeSize (ea x)+1
  have hn : 1 ≤ N := by dsimp [N]; omega
  have hd : N^d ≤ N^(d+1) := pow_le_pow_right' hn (by omega)
  have hn' : N ≤ N^(d+1) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+1 by omega)
  have h₁ := hK x
  have ho := output_size F x
  have hb : treeSize (eb (f x))+1 ≤ (K+2)*N^(d+1) := by dsimp [N] at *; nlinarith
  have h₂ := (hM (f x)).trans (Nat.mul_le_mul_left M (Nat.pow_le_pow_left hb e))
  rw [mul_pow,←pow_mul] at h₂
  have hD : N^d ≤ N^D := pow_le_pow_right' hn (by dsimp [D]; omega)
  have he : N^((d+1)*e) ≤ N^D := pow_le_pow_right' hn (by dsimp [D]; omega)
  have hpos : 1 ≤ N^D := one_le_pow₀ hn
  have hk := Nat.mul_le_mul_left K hD
  have hm := Nat.mul_le_mul_left (M*(K+2)^e) he
  rw [compose_limit]
  dsimp [N] at *
  nlinarith

theorem pairMap {α β γ δ : Type} {ea : α → Data} {eb : β → Data}
    {ec : γ → Data} {ed : δ → Data} {f : α → β} {g : γ → δ}
    {F : Device ea eb f} {G : Device ec ed g} (hF : PolynomialCost F) (hG : PolynomialCost G) :
    PolynomialCost (TreeDevice.pairMap F G) := by
  obtain ⟨K,d,hK⟩ := hF
  obtain ⟨M,e,hM⟩ := hG
  let D := d+e+1
  refine ⟨25*K+13*M+100,D,?_⟩
  rintro ⟨x,y⟩
  let N := treeSize (ea x)+treeSize (ec y)+2
  have hn : 1 ≤ N := by dsimp [N]; omega
  have hnx : treeSize (ea x)+1 ≤ N := by dsimp [N]; omega
  have hny : treeSize (ec y)+1 ≤ N := by dsimp [N]; omega
  have hd : N^d ≤ N^D := pow_le_pow_right' hn (by dsimp [D]; omega)
  have he : N^e ≤ N^D := pow_le_pow_right' hn (by dsimp [D]; omega)
  have hn' : N ≤ N^D := by simpa using pow_le_pow_right' hn (show 1 ≤ D by dsimp [D]; omega)
  have h₁ := (hK x).trans (Nat.mul_le_mul_left K ((Nat.pow_le_pow_left hnx d).trans hd))
  have h₂ := (hM y).trans (Nat.mul_le_mul_left M ((Nat.pow_le_pow_left hny e).trans he))
  have ho₁ := output_size F x
  have ho₂ := output_size G y
  rw [pairMap_limit]
  simp only [product,treeSize_pair]
  change _ ≤ (25*K+13*M+100)*N^D
  change treeSize (ea x)+treeSize (ec y)+2 ≤ N^D at hn'
  nlinarith

theorem fanout {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : α → γ} {F : Device ea eb f} {G : Device ea ec g}
    (hF : PolynomialCost F) (hG : PolynomialCost G) : PolynomialCost (TreeDevice.fanout F G) :=
  compose (LinearCost.dup ea).polynomial (pairMap hF hG)

end PolynomialCost

namespace Fold

theorem time_le {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) (K d : ℕ)
    (hF : ∀ z, F.limit z ≤ K*(treeSize (product ea eb z)+1)^d)
    (hg : ∀ a b, treeSize (ea (f (a,b))) ≤ treeSize (ea a)+treeSize (eb b)+1)
    (a : α) (xs : List β) (M : ℕ) (hM : treeSize (ea a)+treeSize (listTree eb xs)+1 ≤ M) :
    time F a xs ≤ (xs.length+1)*(12*M+K*M^d+11) := by
  induction xs generalizing a with
  | nil =>
    have ha : treeSize (ea a) ≤ M := by omega
    simp only [time,List.length_nil]
    omega
  | cons b bs ih =>
    have hg' := hg a b
    have hc : treeSize (ea (f (a,b)))+treeSize (listTree eb bs)+1 ≤ M := by
      simp only [listTree,treeSize_pair] at hM
      omega
    have hs : treeSize (product ea eb (a,b))+1 ≤ M := by
      have hp : 1 ≤ treeSize (listTree eb bs) := treeSize_pos _
      simp only [product,treeSize_pair,listTree] at *
      omega
    have hlim := (hF (a,b)).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left hs d))
    have hrec := ih (f (a,b)) hc
    simp only [time,List.length_cons]
    nlinarith

theorem polynomial {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    {F : Device (product ea eb) ea f} (hF : PolynomialCost F)
    (hg : ∀ a b, treeSize (ea (f (a,b))) ≤ treeSize (ea a)+treeSize (eb b)+1) :
    PolynomialCost (device F) := by
  obtain ⟨K,d,hK⟩ := hF
  refine ⟨K+30,d+2,?_⟩
  rintro ⟨a,xs⟩
  let N := treeSize (product ea (listTree eb) (a,xs))+1
  have hn : 1 ≤ N := by dsimp [N]; omega
  have he : xs.length+1 ≤ N := by
    dsimp [N,product]
    rw [treeSize_pair,listTree_size]
    omega
  have ht := time_le F K d hK hg a xs N (by dsimp [N,product]; rw [treeSize_pair]; omega)
  have hh := ht.trans (Nat.mul_le_mul_right _ he)
  have hd : N^d ≤ N^(d+1) := pow_le_pow_right' hn (by omega)
  have hn' : N ≤ N^(d+1) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+1 by omega)
  have hpos : 1 ≤ N^(d+2) := one_le_pow₀ hn
  change time F a xs+2 ≤ (K+30)*N^(d+2)
  have hmul := Nat.mul_le_mul_left N hd
  have hmul' := Nat.mul_le_mul_left N hn'
  have hmono : N ≤ N^(d+2) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+2 by omega)
  rw [show d+2=(d+1)+1 by omega,pow_succ] at hpos hmono ⊢
  nlinarith

end Fold
end MeanPayoff.TreeDevice

namespace MeanPayoff.TreeDevice
open BinaryData
namespace LinearCost

theorem recode {α β γ δ : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    {F : Device ea eb f} (hF : LinearCost F) (ec : γ → Data) (ed : δ → Data)
    (i : γ → α) (h : γ → δ) (hi : ∀ x, ea (i x)=ec x) (ho : ∀ x, eb (f (i x))=ed (h x)) :
    LinearCost (F.recode ec ed i h hi ho) := by
  obtain ⟨K,hK⟩ := hF
  refine ⟨K,?_⟩
  intro x
  simpa only [Device.recode,hi] using hK (i x)

theorem pairSwap {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (TreeDevice.pairSwap ea eb) :=
  fanout (second ea eb) (first ea eb)

theorem nilPrefix {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (Lists.nilPrefix ea eb) := by
  refine ⟨6,?_⟩
  intro x
  change 6 ≤ 6*(treeSize (ea x)+1)
  omega

theorem nilSuffix {α β : Type} (ea : α → Data) (eb : β → Data) : LinearCost (Lists.nilSuffix ea eb) :=
  compose (nilPrefix ea eb) (pairSwap _ _)

theorem cons {α : Type} (ea : α → Data) : LinearCost (Lists.consDevice ea) :=
  recode (identity _) _ _ _ _ _ _

theorem consAcc {α : Type} (ea : α → Data) : LinearCost (Lists.consAcc ea) :=
  compose (pairSwap _ _) (cons _)
end LinearCost
namespace Forest

theorem literal_limit {α : Type} (t : Data) (a : α → List Data) (x : α) :
    (literal t a).limit x ≤ 6*treeSize t := by
  induction t generalizing a with
  | nil => simp [literal,atom]
  | pair u v ihu ihv =>
    have h₁ := ihu (fun z => v::a z)
    have h₂ := ihv a
    change (literal v a).limit x+((literal u (fun z => v::a z)).limit x+2+2)+2 ≤ _
    rw [treeSize_pair]
    omega
end Forest
namespace LinearCost

theorem constant {α β : Type} (ea : α → Data) (eb : β → Data) (b : β) :
    LinearCost (TreeDevice.constant ea eb b) := by
  refine ⟨6*treeSize (eb b)+12,?_⟩
  intro x
  have h := Forest.literal_limit (eb b) (fun _ : α => []) x
  change (Forest.drop ea (fun _ => [])).limit x + (Forest.literal (eb b) (fun _ : α => [])).limit x+2 ≤ _
  dsimp [Forest.drop,Forest.Segment.seq,Forest.move01] at *
  nlinarith

theorem branch {α β : Type} {ea : α → Data} {eb : β → Data}
    {test : α → Bool} {f g : α → β} {T : Device ea Compare.bitTree test}
    {F : Device ea eb f} {G : Device ea eb g} (hT : LinearCost T) (hF : LinearCost F) (hG : LinearCost G) :
    LinearCost (TreeDevice.branch T F G) := compose (fanout hT (fanout hF hG)) (select _)

theorem not : LinearCost Bits.notDevice :=
  branch (identity _) (constant _ _ _) (constant _ _ _)

theorem tail {α : Type} (ea : α → Data) : LinearCost (Tail.device ea) := by
  refine ⟨10,?_⟩
  intro xs
  cases xs with
  | nil => change 2 ≤ 10*(treeSize (listTree ea [])+1); omega
  | cons x xs =>
    change (Forest.drop ea (fun _ => [])).limit x+3 ≤ _
    dsimp [Forest.drop,Forest.Segment.seq,Forest.move01,listTree]
    rw [treeSize_pair]
    omega

theorem head {α : Type} (ea : α → Data) (a : α) : LinearCost (Head.device ea a) := by
  obtain ⟨K,hK⟩ := constant (listTree ea) ea a
  refine ⟨K+50,?_⟩
  intro xs
  cases xs with
  | nil =>
    have h := hK []
    change (TreeDevice.constant (listTree ea) ea a).limit []+3 ≤ _
    simp only [listTree,treeSize_nil] at *
    omega
  | cons x xs =>
    change (TreeDevice.first ea (listTree ea)).limit (x,xs)+3 ≤ _
    rw [first_limit]
    simp only [listTree,treeSize_pair]
    nlinarith
end LinearCost
namespace PolynomialCost

theorem reverse {α : Type} (ea : α → Data) : PolynomialCost (Lists.reverseDevice ea) := by
  apply compose (LinearCost.nilPrefix _ _).polynomial
  apply Fold.polynomial (LinearCost.consAcc _).polynomial
  intro a b
  simp only [listTree,treeSize_pair]
  omega
end PolynomialCost
namespace «Sort»

theorem carry_linear : LinearCost carryDevice := by
  have hp : LinearCost pairDevice := LinearCost.fanout
    (LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)) (LinearCost.second _ _)
  have ht : LinearCost tailDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
  exact LinearCost.fanout (LinearCost.compose hp LinearCost.max)
    (LinearCost.compose (LinearCost.fanout (LinearCost.compose hp LinearCost.min) ht) (LinearCost.cons _))

theorem carry_size (a : Acc) (b : W) :
    treeSize (product wordData (listTree wordData) (carryStep (a,b))) ≤
      treeSize (product wordData (listTree wordData) a)+treeSize (wordData b)+1 := by
  rcases a with ⟨w,xs⟩
  unfold carryStep Order.high Order.low
  split_ifs <;> simp only [product,treeSize_pair,listTree] <;> omega

theorem initial_linear : LinearCost initialDevice :=
  LinearCost.fanout (LinearCost.compose (LinearCost.first _ _) (LinearCost.nilSuffix _ _)) (LinearCost.second _ _)

theorem insert_polynomial : PolynomialCost insertDevice :=
  PolynomialCost.compose initial_linear.polynomial
    (PolynomialCost.compose (Fold.polynomial carry_linear.polynomial carry_size)
      (PolynomialCost.compose (LinearCost.cons _).polynomial (PolynomialCost.reverse _)))

theorem sort_polynomial : PolynomialCost sortDevice := by
  apply PolynomialCost.compose (LinearCost.nilPrefix _ _).polynomial
  apply Fold.polynomial (PolynomialCost.compose (LinearCost.pairSwap _ _).polynomial insert_polynomial)
  intro a b
  dsimp only [Function.comp_def]
  rw [insert_size]
  omega
end «Sort»
end MeanPayoff.TreeDevice

namespace MeanPayoff.TreeDevice
open BinaryData

theorem element_size_le {α : Type} (ea : α → Data) {x : α} {xs : List α} (hx : x∈xs) :
    treeSize (ea x)+1 ≤ treeSize (listTree ea xs) := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [listTree,treeSize_pair]; omega
    · have h := ih hx
      simp only [listTree,treeSize_pair]; omega

theorem list_length_le_size {α : Type} (ea : α → Data) (xs : List α) :
    xs.length+1 ≤ treeSize (listTree ea xs) := by rw [listTree_size]; omega

namespace PolynomialCost

theorem map {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    {F : Device ea eb f} (hF : PolynomialCost F) : PolynomialCost (Map.device F) := by
  obtain ⟨K,d,hK⟩ := hF
  refine ⟨128*(K+2)^2,(d+1)*2,?_⟩
  intro xs
  let N := treeSize (listTree ea xs)+1
  have hn : 1 ≤ N := by dsimp [N]; omega
  have hlen : xs.length ≤ N := (list_length_le_size ea xs).trans (by dsimp [N]; omega) |>.trans' (by omega)
  have he : ∀ x∈xs, F.limit x ≤ K*N^d := by
    intro x hx
    exact (hK x).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left ((element_size_le ea hx).trans (by dsimp [N]; omega)) d))
  have sum_bound (ys : List α) (C : ℕ) (hc : ∀ y∈ys, F.limit y ≤ C) :
      (ys.map F.limit).sum ≤ ys.length*C := by
    induction ys with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have hh := hc y (List.mem_cons_self ..)
      have ht := ih (fun z hz => hc z (List.mem_cons_of_mem _ hz))
      nlinarith
  have hsum := sum_bound xs (K*N^d) he
  have hs := hsum.trans (Nat.mul_le_mul_right (K*N^d) hlen)
  have hpow : N ≤ N^(d+1) := by simpa using pow_le_pow_right' hn (show 1 ≤ d+1 by omega)
  have hr : Map.resource F xs+1 ≤ (K+2)*N^(d+1) := by
    change treeSize (listTree ea xs)+(xs.map F.limit).sum+1 ≤ _
    have hnEq : treeSize (listTree ea xs)+1=N := rfl
    rw [pow_succ] at hpow ⊢
    nlinarith
  have hm := (Map.limit_le F xs).trans (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hr 2))
  change Map.limit F xs ≤ _
  simpa only [mul_pow,←pow_mul,Nat.mul_assoc] using hm

end PolynomialCost
namespace Median

theorem halfStep_linear : LinearCost halfStepDevice := by
  have hi : LinearCost incrementDevice := LinearCost.compose
    (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)) (LinearCost.cons _)
  exact LinearCost.fanout (LinearCost.compose (LinearCost.first _ _) LinearCost.not)
    (LinearCost.branch (LinearCost.first _ _) (LinearCost.compose (LinearCost.second _ _) hi) (LinearCost.second _ _))

theorem halfStep_size {α : Type} (ea : α → Data) (s : State) (x : α) :
    treeSize (stateData (halfStep s)) ≤ treeSize (stateData s)+treeSize (ea x)+1 := by
  have h := treeSize_pos (ea x)
  rcases s with ⟨b,c⟩
  cases b <;> simp only [halfStep,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true,
    stateData,product,Compare.bitTree,listData,boolData,listTree,treeSize_pair,treeSize_nil,unitData] <;> omega

theorem count_polynomial {α : Type} (ea : α → Data) : PolynomialCost (countDevice ea) := by
  apply PolynomialCost.compose
    (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)).polynomial
  apply PolynomialCost.compose ?_ (LinearCost.second _ _).polynomial
  apply Fold.polynomial (LinearCost.compose (LinearCost.first _ _) halfStep_linear).polynomial
  intro a b
  exact halfStep_size ea a b

theorem drop_polynomial {α : Type} (ea : α → Data) : PolynomialCost (dropDevice ea) := by
  apply Fold.polynomial (LinearCost.compose (LinearCost.first _ _) (LinearCost.tail _)).polynomial
  intro a b
  change treeSize (listTree ea a.tail) ≤ treeSize (listTree ea a)+treeSize (unitData b)+1
  cases a <;> simp [listTree] ; omega

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.fanout Sort.sort_polynomial (count_polynomial _))
    (PolynomialCost.compose (drop_polynomial _) (LinearCost.head _ _).polynomial)
end Median
end MeanPayoff.TreeDevice
end

end OAI
