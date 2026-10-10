import OAI.Computability.MeanPayoff.InputCode

namespace OAI

section

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Allocation
noncomputable def double : Code (Count×Unit) Count := (fst ⋏ₚ fst) ≫ₚ Counter.add
noncomputable def init : Code Count (Count×Count) := const [()] ⋏ₚ Code.id
noncomputable def device : Device encode encode (fun cs : Count => Fold.fold double.eval [()] cs) :=
  @compose Count (Count×Count) Count encode encode encode init.eval (fun z => Fold.fold double.eval z.1 z.2) init.device (Fold.device double.device)

 theorem fold_length (a cs : Count) : (Fold.fold double.eval a cs).length=2^cs.length*a.length := by
  induction cs generalizing a with
  | nil => simp [Fold.fold]
  | cons u us ih =>
    change (Fold.fold double.eval (double (a,u)) us).length=_
    rw [ih]
    simp only [double,comp_eval,pair_eval,fst_eval,Counter.add_length,List.length_cons,pow_succ]
    ring
 theorem exact (cs : Count) : Fold.fold double.eval [()] cs=List.replicate (2^cs.length) () := by
  have h := fold_length [()] cs
  simpa using (List.eq_replicate_of_mem (a:=()) (by intro a ha; exact Subsingleton.elim _ _)).trans (by rw [h]; simp)

 theorem fold_bound : ∃ K d : ℕ, ∀ (a cs : Count),
    (Fold.device double.device).limit (a,cs) ≤ K*(a.length*2^cs.length+cs.length+1)^d := by
  obtain ⟨K,d,h⟩ := double.polynomial
  refine ⟨49+K*8^d,d+2,?_⟩
  intro a cs
  let N := a.length*2^cs.length+cs.length+1
  have hn : 1≤N := by dsimp [N]; omega
  have ha : ∀ k≤cs.length, treeSize (encode (Fold.fold double.eval a (cs.take k))) ≤ 3*N := by
    intro k hk
    rw [Size.count,fold_length]
    have hp : 2^(cs.take k).length ≤ 2^cs.length := Nat.pow_le_pow_right (by decide) ((List.length_take_le _ _).trans hk)
    have hm := Nat.mul_le_mul_right a.length hp
    have hm' : 2^(cs.take k).length*a.length ≤ a.length*2^cs.length := by simpa only [Nat.mul_comm] using hm
    dsimp [N]; omega
  have hs : treeSize (encode cs)≤3*N := by rw [Size.count]; dsimp [N]; omega
  have ht := Fold.time_of_prefix_bound double.device K d (3*N) (3*N) h a cs hs ha
  have hb : 3*N+3*N+2≤8*N := by omega

  have hd : cs.length+1≤N := by dsimp [N]; omega
  change Fold.time double.device a cs+2 ≤ _
  have hbpow := Nat.mul_le_mul_left K (Nat.pow_le_pow_left hb d)
  have hlow : 12*(3*N)+K*(3*N+3*N+2)^d+11 ≤ 47*N+K*(8*N)^d := by omega
  have ht' := ht.trans (Nat.mul_le_mul hd hlow)
  have hnp : N≤N^(d+1) := Nat.le_pow (by omega)
  have hp : N^d ≤ N^(d+1) := Nat.pow_le_pow_right hn (by omega)
  have hpow : N^2≤N^(d+2) := Nat.pow_le_pow_right hn (by omega)
  rw [mul_pow] at ht'

  have hx : N*(47*N+K*8^d*N^d)+2 ≤ (49+K*8^d)*N^(d+2) := by
    have h1 := Nat.mul_le_mul_left 47 hpow
    have h2 : N*N^d≤N^(d+2) := by rw [←pow_succ']; exact Nat.pow_le_pow_right hn (by omega)
    have h3 := Nat.mul_le_mul_left (K*8^d) h2
    have h4 : 1≤N^(d+2) := one_le_pow₀ hn
    nlinarith
  exact (Nat.add_le_add_right ht' 2).trans (by simpa only [Nat.mul_assoc] using hx)
end Allocation
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff

def PolyBound {ι : Type} (base f : ι→ℕ) : Prop :=
  ∃ K d : ℕ, ∀ i, f i≤K*(base i+1)^d
namespace PolyBound
variable {ι : Type} {r f g : ι→ℕ}
theorem mono (h : PolyBound r g) (hf : ∀ i, f i≤g i) : PolyBound r f := by
  obtain ⟨K,d,h⟩ := h
  exact ⟨K,d,fun i => (hf i).trans (h i)⟩
theorem base (r : ι→ℕ) : PolyBound r r := ⟨1,1,by intro i; simp⟩
theorem const (r : ι→ℕ) (a : ℕ) : PolyBound r (fun _ => a) := ⟨a,0,by simp⟩
theorem add (hf : PolyBound r f) (hg : PolyBound r g) : PolyBound r (fun i => f i+g i) := by
  obtain ⟨K,d,hf⟩ := hf
  obtain ⟨M,e,hg⟩ := hg
  refine ⟨K+M,d+e,fun i => ?_⟩
  have hp : 1≤r i+1 := by omega
  have hd := (hf i).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_right hp (show d≤d+e by omega)))
  have he := (hg i).trans (Nat.mul_le_mul_left M (Nat.pow_le_pow_right hp (show e≤d+e by omega)))
  nlinarith
theorem mul (hf : PolyBound r f) (hg : PolyBound r g) : PolyBound r (fun i => f i*g i) := by
  obtain ⟨K,d,hf⟩ := hf
  obtain ⟨M,e,hg⟩ := hg
  refine ⟨K*M,d+e,fun i => ?_⟩
  have h := Nat.mul_le_mul (hf i) (hg i)
  rw [pow_add]
  nlinarith only [h]
theorem pow (hf : PolyBound r f) (n : ℕ) : PolyBound r (fun i => f i^n) := by
  obtain ⟨K,d,hf⟩ := hf
  refine ⟨K^n,d*n,fun i => ?_⟩
  simpa only [mul_pow,←pow_mul] using Nat.pow_le_pow_left (hf i) n
theorem apply {k : ℕ→ℕ} (hf : PolyBound r f) (hk : ∃ K d, ∀ n, k n≤K*(n+1)^d) :
    PolyBound r (fun i => k (f i)) := by
  obtain ⟨K,d,hk⟩ := hk
  exact ((const r K).mul ((hf.add (const r 1)).pow d)).mono (fun i => hk _)
end PolyBound
namespace TreeDevice
open BinaryData
 theorem polynomial_limit {ι α β : Type} {ea : α→Data} {eb : β→Data} {f : α→β}
    {F : Device ea eb f} (hF : PolynomialCost F) (r : ι→ℕ) (x : ι→α)
    (hx : PolyBound r (fun i => treeSize (ea (x i)))) : PolyBound r (fun i => F.limit (x i)) := by
  obtain ⟨K,d,h⟩ := hF
  exact ((PolyBound.const r K).mul ((hx.add (PolyBound.const r 1)).pow d)).mono (fun i => h (x i))
 theorem polynomial_output {ι α β : Type} {ea : α→Data} {eb : β→Data} {f : α→β}
    (F : Device ea eb f) (r : ι→ℕ) (x : ι→α)
    (hx : PolyBound r (fun i => treeSize (ea (x i))))
    (hc : PolyBound r (fun i => F.limit (x i))) : PolyBound r (fun i => treeSize (eb (f (x i)))) :=
  (hx.add hc).mono (fun i => output_size F (x i))
end TreeDevice
end MeanPayoff

end

end OAI
