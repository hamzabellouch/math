import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialRoutine
import OAI.Analysis.MatrixSigning.Realization.ScalarRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {ι α β γ : Type*} {L f g : ι → ℕ}

def IsPoly (L f : ι → ℕ) : Prop := ∃ p : NaturalPolynomial,∀i,f i≤p.eval (L i)
lemma IsPoly.mono (hf : IsPoly L f) (h : ∀i,g i≤f i) : IsPoly L g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => (h i).trans (hp i)⟩
lemma IsPoly.add (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i+g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun i => Nat.add_le_add (hp i) (hq i)⟩
lemma IsPoly.mul (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i*g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun i => Nat.mul_le_mul (hp i) (hq i)⟩
lemma IsPoly.pow (hf : IsPoly L f) (k : ℕ) : IsPoly L (fun i => (f i)^k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k,fun i => Nat.pow_le_pow_left (hp i) k⟩
lemma isPoly_const (L : ι → ℕ) (c : ℕ) : IsPoly L (fun _ => c) := ⟨.constant c,fun _ => le_rfl⟩
lemma isPoly_self (L : ι → ℕ) : IsPoly L L := ⟨X,fun _ => le_rfl⟩
lemma IsPoly.eval (hf : IsPoly L f) (p : NaturalPolynomial) : IsPoly L (fun i => p.eval (f i)) := by
  obtain ⟨q,hq⟩ := hf
  exact ⟨p.comp q,fun i => by simpa only [NaturalPolynomial.eval_comp] using p.eval_mono (hq i)⟩
lemma IsPoly.reindex {κ : Type*} (hf : IsPoly L f) (a : κ → ι) : IsPoly (L ∘ a) (f ∘ a) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => hp (a i)⟩
lemma isPoly_pair {ea : α → Word} {eb : β → Word} {a : ι → α} {b : ι → β}
    (ha : IsPoly L (fun i => (ea (a i)).length)) (hb : IsPoly L (fun i => (eb (b i)).length)) :
    IsPoly L (fun i => (prodCode ea eb (a i,b i)).length) := by
  simpa only [prodCode_length] using (((isPoly_const L 2).mul ha).add (isPoly_const L 1)).add hb

variable {ea : α → Word} {eb : β → Word} {ec : γ → Word} {F : α → β} {G : β → γ}

structure RunsPoly (L : ι → ℕ) (r : Realizes ea eb F) (a : ι → α) : Prop where
  input : IsPoly L (fun i => (ea (a i)).length)
  cost : IsPoly L (fun i => r.cost (a i))
lemma RunsPoly.of_poly (r : Realizes ea eb F) [PolyTime r] (a : ι → α)
    (h : IsPoly L (fun i => (ea (a i)).length)) : RunsPoly L r a := by
  refine ⟨h,?_⟩
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  exact (h.eval p).mono (fun i => hp (a i))
lemma RunsPoly.output {r : Realizes ea eb F} {a : ι → α} (h : RunsPoly L r a) :
    IsPoly L (fun i => (eb (F (a i))).length) := (h.input.add h.cost).mono (fun i => r.output_length (a i))
lemma RunsPoly.then {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s (fun i => F (a i))) : RunsPoly L (r.then s) a :=
  ⟨hr.input,hr.cost.add hs.cost⟩
lemma RunsPoly.then_poly {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    (s : Realizes eb ec G) [PolyTime s] : RunsPoly L (r.then s) a :=
  hr.then (RunsPoly.of_poly s _ hr.output)
lemma RunsPoly.both {G : α → γ} {r : Realizes ea eb F} {s : Realizes ea ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.both s) a := by
  refine ⟨hr.input,?_⟩
  have h := (((((isPoly_const L 4).mul hr.input).add ((isPoly_const L 12).mul hr.output)).add hr.cost).add hs.cost).add (isPoly_const L 15)
  apply h.mono
  intro i
  change PairRoutine.pairingTicks ea (fun x => eb (F x)) r.cost s.cost (a i)≤_
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega
lemma RunsPoly.congr {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {F' : α → β} (h : ∀x,F x=F' x) : RunsPoly L (r.congr h) a := by
  have he : F=F' := funext h
  subst F'
  exact hr
lemma RunsPoly.changeOutput {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {δ : Type*} (ed : δ → Word) (g : α → δ) (h : ∀x,eb (F x)=ed (g x)) :
    RunsPoly L (r.changeOutput ed g h) a := ⟨hr.input,hr.cost⟩
lemma RunsPoly.reindex {r : Realizes ea eb F} {δ : Type*} (ed : δ → Word) (g : δ → α)
    (h : ∀x,ed x=ea (g x)) {a : ι → δ} (hr : RunsPoly L r (fun i => g (a i))) :
    RunsPoly L (r.reindex ed g h) a := by
  refine ⟨?_,hr.cost⟩
  simpa only [h] using hr.input
lemma Realizes.congr_cost {r : Realizes ea eb F} {F' : α → β} (h : ∀x,F x=F' x) :
    (r.congr h).cost=r.cost := by
  have he : F=F' := funext h
  subst F'
  rfl
lemma RunsPoly.ite {P : α → Bool} {G : α → β} {b : Realizes ea boolCode P}
    {r : Realizes ea eb F} {s : Realizes ea eb G} {a : ι → α}
    (hb : RunsPoly L b a) (hr : RunsPoly L r a) (hs : RunsPoly L s a) :
    RunsPoly L (b.ite r s) a := by
  unfold Realizes.ite
  have ht := hb.both (RunsPoly.of_poly (identity ea) a hb.input)
  apply ht.then
  refine ⟨ht.output,?_⟩
  apply ((hr.cost.add hs.cost).add (isPoly_const L 6)).mono
  intro i
  change 5+(if P (a i) then r.cost (a i) else s.cost (a i))+1≤r.cost (a i)+s.cost (a i)+6
  split <;> omega
end CurrentKS.Realization

end

end OAI
