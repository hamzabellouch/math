import OAI.Combinatorics.CycleDecomposition.BatchEndpoints

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56 cycleUniverse57 cycleUniverse58 cycleUniverse59 cycleUniverse60 cycleUniverse61 cycleUniverse62 cycleUniverse63 cycleUniverse64

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch
open Finset
noncomputable section

def Pairing (V : Type cycleUniverse1) := {f : V → V // Function.Involutive f ∧ ∀ x, f x ≠ x}

namespace Pairing
variable {V : Type cycleUniverse2} {W : Type cycleUniverse3}
instance : CoeFun (Pairing V) (fun _ => V → V) := ⟨Subtype.val⟩
instance [Fintype V] : Fintype (Pairing V) := by
  classical
  unfold Pairing
  infer_instance
instance [Fintype V] : DecidableEq (Pairing V) := Classical.decEq _

@[simp] theorem apply_apply (p : Pairing V) (v : V) : p (p v) = v := p.property.1 v
@[simp] theorem apply_ne (p : Pairing V) (v : V) : p v ≠ v := p.property.2 v

def transport (e : V ≃ W) : Pairing V ≃ Pairing W where
  toFun p := ⟨fun x => e (p (e.symm x)),
    (by intro x; simp), (by intro x h; have := congrArg e.symm h; simp at this)⟩
  invFun p := ⟨fun x => e.symm (p (e x)),
    (by intro x; simp), (by intro x h; have := congrArg e h; simp at this)⟩
  left_inv p := by apply Subtype.ext; funext x; simp
  right_inv p := by apply Subtype.ext; funext x; simp

@[simp] theorem transport_apply (e : V ≃ W) (p : Pairing V) (x : W) :
    transport e p x = e (p (e.symm x)) := rfl

theorem nonempty_of_even [Fintype V] (h : Even (Fintype.card V)) : Nonempty (Pairing V) := by
  classical
  obtain ⟨k,hk⟩ := h
  let q : Pairing (Fin k ⊕ Fin k) := ⟨fun x => x.swap,
    (by intro x; cases x <;> rfl), (by intro x h; cases x <;> nomatch h)⟩
  let e : (Fin k ⊕ Fin k) ≃ V := Fintype.equivOfCardEq (by simpa using hk.symm)
  exact ⟨transport e q⟩

variable [Fintype V]

def oneCount (a b : V) : ℕ := by
  classical
  exact Fintype.card {p : Pairing V // p a = b}
def twoCount (a b c d : V) : ℕ := by
  classical
  exact Fintype.card {p : Pairing V // p a = b ∧ p c = d}

@[simp] theorem oneCount_self (a : V) : oneCount a a = 0 := by
  classical
  unfold oneCount
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun p => p.val.apply_ne a p.property⟩

theorem oneCount_transport (e : V ≃ V) (a b : V) :
    oneCount (e a) (e b) = oneCount a b := by
  classical
  symm
  exact Fintype.card_congr ((transport e).subtypeEquiv (by intro p; simp))

theorem oneCount_eq (a b c : V) (hab : a ≠ b) (hac : a ≠ c) :
    oneCount a b = oneCount a c := by
  classical
  have h := oneCount_transport (Equiv.swap b c) a b
  simpa [Equiv.swap_apply_of_ne_of_ne hab hac] using h.symm

theorem oneCount_balance (a b : V) (hab : a ≠ b) :
    (Fintype.card V - 1) * oneCount a b = Fintype.card (Pairing V) := by
  classical
  have hsum : (∑ c : V, oneCount a c) = Fintype.card (Pairing V) := by
    unfold oneCount
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun p : Pairing V => p a))
  have heq : (∑ c : V, oneCount a c) = ∑ c ∈ (univ.erase a), oneCount a b := by
    rw [← Finset.sum_erase_add _ _ (mem_univ a),oneCount_self,add_zero]
    apply Finset.sum_congr rfl
    intro c hc
    exact oneCount_eq a c b (Finset.mem_erase.mp hc).1.symm hab
  rw [heq,Finset.sum_const,Finset.card_erase_of_mem (mem_univ a)] at hsum
  simpa using hsum

theorem twoCount_transport (e : V ≃ V) (a b c d : V) :
    twoCount (e a) (e b) (e c) (e d) = twoCount a b c d := by
  classical
  symm
  exact Fintype.card_congr ((transport e).subtypeEquiv (by intro p; simp))

theorem twoCount_eq (a b c d e : V)
    (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) : twoCount a b c d = twoCount a b c e := by
  classical
  have h := twoCount_transport (Equiv.swap d e) a b c d
  simpa [Equiv.swap_apply_of_ne_of_ne had hae,
    Equiv.swap_apply_of_ne_of_ne hbd hbe,Equiv.swap_apply_of_ne_of_ne hcd hce] using h.symm

theorem twoCount_forbidden (a b c d : V) (hac : a ≠ c) (hbc : b ≠ c)
    (hd : d = a ∨ d = b ∨ d = c) : twoCount a b c d = 0 := by
  classical
  unfold twoCount
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun p => ?_⟩
  rcases p.property with ⟨hab,hcd⟩
  rcases hd with rfl | rfl | rfl
  · have h := congrArg p.val hcd
    simp only [apply_apply,hab] at h
    exact hbc h.symm
  · have h := congrArg p.val hab
    have h' := congrArg p.val hcd
    simp only [apply_apply] at h h'
    exact hac (h.trans h'.symm)
  · exact p.val.apply_ne _ hcd

theorem twoCount_balance (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (Fintype.card V - 3) * twoCount a b c d = oneCount a b := by
  classical
  let Q := {p : Pairing V // p a = b}
  have hsum : (∑ e : V, twoCount a b c e) = oneCount a b := by
    have hcard : ∀ e : V, Fintype.card {p : Q // p.val c = e} = twoCount a b c e := by
      intro e
      apply Fintype.card_congr
      exact ⟨fun p => ⟨p.val.val,p.val.property,p.property⟩,
        fun p => ⟨⟨p.val,p.property.1⟩,p.property.2⟩,fun _ => rfl,fun _ => rfl⟩
    calc
      (∑ e : V, twoCount a b c e) = ∑ e : V, Fintype.card {p : Q // p.val c = e} := by simp_rw [hcard]
      _ = Fintype.card Q := by
        rw [← Fintype.card_sigma]
        exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun p : Q => p.val c))
      _ = oneCount a b := rfl
  let S : Finset V := {a,b,c}
  have hScard : S.card = 3 := by simp [S,hab,hac,hbc]
  have hsum' : (∑ e : V, twoCount a b c e) = ∑ e ∈ univ \ S, twoCount a b c d := by
    rw [← Finset.sum_sdiff (s₁:=S) (s₂:=univ) (by simp)]
    have hz : ∑ e ∈ S, twoCount a b c e = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      exact twoCount_forbidden a b c e hac hbc (by simpa [S] using he)
    rw [hz,add_zero]
    apply Finset.sum_congr rfl
    intro e he
    have he' : e ≠ a ∧ e ≠ b ∧ e ≠ c := by simpa [S] using (Finset.mem_sdiff.mp he).2
    exact twoCount_eq a b c e d he'.1.symm had he'.2.1.symm hbd he'.2.2.symm hcd
  rw [hsum',Finset.sum_const,Finset.card_sdiff,Finset.inter_univ,hScard] at hsum
  simpa using hsum

theorem one_fraction (hV : Even (Fintype.card V)) (a b : V) (hab : a ≠ b) :
    (oneCount a b : ℝ) / Fintype.card (Pairing V) = 1 / (Fintype.card V - 1 : ℝ) := by
  classical
  have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff_nontrivial.mpr ⟨a,b,hab⟩
  have hbal := oneCount_balance a b hab
  have hbal' : ((Fintype.card V:ℝ)-1)*(oneCount a b:ℝ) = Fintype.card (Pairing V) := by
    have h := congrArg (fun n : ℕ => (n:ℝ)) hbal
    simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ Fintype.card V by omega),Nat.cast_one] using h
  have : Nonempty (Pairing V) := nonempty_of_even hV
  have hp : (0:ℝ) < Fintype.card (Pairing V) := by exact_mod_cast Fintype.card_pos
  have hn' : (0:ℝ) < Fintype.card V-1 := by
    have hnR : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  apply (div_eq_div_iff hp.ne' hn'.ne').mpr
  nlinarith

theorem two_fraction (hV : Even (Fintype.card V)) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (twoCount a b c d : ℝ) / Fintype.card (Pairing V) =
      1 / ((Fintype.card V - 1 : ℝ)*(Fintype.card V - 3 : ℝ)) := by
  classical
  have hn : 4 ≤ Fintype.card V := by
    have : ({a,b,c,d}:Finset V).card = 4 := by simp [hab,hac,had,hbc,hbd,hcd]
    exact this.symm ▸ Finset.card_le_univ _
  have hone := oneCount_balance a b hab
  have htwo := twoCount_balance a b c d hab hac had hbc hbd hcd
  have hb : ((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)*(twoCount a b c d:ℝ) =
      Fintype.card (Pairing V) := by
    have h1 : ((Fintype.card V:ℝ)-1)*(oneCount a b:ℝ) = Fintype.card (Pairing V) := by
      have h := congrArg (fun n : ℕ => (n:ℝ)) hone
      simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ Fintype.card V by omega),Nat.cast_one] using h
    have h2 : ((Fintype.card V:ℝ)-3)*(twoCount a b c d:ℝ) = oneCount a b := by
      have h := congrArg (fun n : ℕ => (n:ℝ)) htwo
      simpa only [Nat.cast_mul,Nat.cast_sub (show 3 ≤ Fintype.card V by omega),Nat.cast_ofNat] using h
    nlinarith
  have : Nonempty (Pairing V) := nonempty_of_even hV
  have hp : (0:ℝ) < Fintype.card (Pairing V) := by exact_mod_cast Fintype.card_pos
  have hn' : (0:ℝ) < Fintype.card V-3 := by
    have hnR : (4:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hn'' : (0:ℝ) < Fintype.card V-1 := by linarith
  apply (div_eq_div_iff hp.ne' (mul_pos hn'' hn').ne').mpr
  nlinarith

end Pairing
end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
open Finset
noncomputable section

def finiteAverage {α : Type cycleUniverse4} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

lemma finiteAverage_equiv {α : Type cycleUniverse5} {β : Type cycleUniverse6} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : finiteAverage (fun x => f (e x)) = finiteAverage f := by
  unfold finiteAverage
  rw [e.sum_comp,Fintype.card_congr e]

lemma finiteAverage_add {α : Type cycleUniverse7} [Fintype α] (f g : α → ℝ) :
    finiteAverage (fun x => f x+g x) = finiteAverage f+finiteAverage g := by
  simp [finiteAverage,Finset.sum_add_distrib,add_div]

lemma finiteAverage_sum {α : Type cycleUniverse8} {ι : Type cycleUniverse9} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    finiteAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, finiteAverage (f i) := by
  unfold finiteAverage
  rw [Finset.sum_comm,Finset.sum_div]

lemma finiteAverage_mul_const {α : Type cycleUniverse10} [Fintype α] (f : α → ℝ) (r : ℝ) :
    finiteAverage (fun x => f x*r) = finiteAverage f*r := by
  simp only [finiteAverage,← Finset.sum_mul]
  ring

lemma finiteAverage_const {α : Type cycleUniverse11} [Fintype α] [Nonempty α] (r : ℝ) :
    finiteAverage (fun _ : α => r) = r := by
  have h : (Fintype.card α:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage,h]

lemma finiteAverage_mono {α : Type cycleUniverse12} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : finiteAverage f ≤ finiteAverage g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun a _ => h a)

lemma finiteAverage_prod {α : Type cycleUniverse13} {β : Type cycleUniverse14} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) :
    finiteAverage (fun x : α × β => f x.1*g x.2) = finiteAverage f*finiteAverage g := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

lemma exists_le_finiteAverage {α : Type cycleUniverse15} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ a, f a ≤ finiteAverage f := by
  have hp : (0:ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h : ∑ a, f a ≤ ∑ _a : α, finiteAverage f := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,finiteAverage]
    field_simp
    rfl
  obtain ⟨a,ha,h⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty) h
  exact ⟨a,h⟩

lemma finiteAverage_indicator {α : Type cycleUniverse16} [Fintype α] (P : α → Prop) [DecidablePred P] :
    finiteAverage (fun a => if P a then 1 else 0) = (Fintype.card {a // P a} : ℝ)/Fintype.card α := by
  unfold finiteAverage
  congr 1
  simp [Fintype.card_subtype]

lemma finiteAverage_pi_eval {ι : Type cycleUniverse17} [Fintype ι] [DecidableEq ι] {Ω : ι → Type cycleUniverse60}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (i : ι) (f : Ω i → ℝ) :
    finiteAverage (fun ω : ∀ j, Ω j => f (ω i)) = finiteAverage f := by
  classical
  let e := Equiv.piSplitAt i Ω
  have he := finiteAverage_equiv e.symm (fun ω : ∀ j, Ω j => f (ω i))
  have he' : finiteAverage (fun x : Ω i × (∀ j : {j // j ≠ i}, Ω j.val) => f x.1) =
      finiteAverage f := by
    have h := finiteAverage_prod f (fun _ : (∀ j : {j // j ≠ i}, Ω j.val) => (1:ℝ))
    simpa only [mul_one,finiteAverage_const] using h
  rw [← he]
  simpa [e,Equiv.piSplitAt_symm_apply] using he'

lemma finiteAverage_pi_pair {ι : Type cycleUniverse18} [Fintype ι] [DecidableEq ι] {Ω : ι → Type cycleUniverse61}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (i j : ι) (hij : i ≠ j)
    (f : Ω i → ℝ) (g : Ω j → ℝ) :
    finiteAverage (fun ω : ∀ k, Ω k => f (ω i)*g (ω j)) = finiteAverage f*finiteAverage g := by
  classical
  let e := Equiv.piSplitAt i Ω
  rw [← finiteAverage_equiv e.symm (fun ω : ∀ k, Ω k => f (ω i)*g (ω j))]
  have hfun : (fun x => f (e.symm x i)*g (e.symm x j)) =
      (fun x : Ω i × (∀ k : {k // k ≠ i}, Ω k.val) => f x.1*g (x.2 ⟨j,hij.symm⟩)) := by
    funext x
    simp [e,Equiv.piSplitAt_symm_apply,hij.symm]
  rw [hfun,finiteAverage_prod f (fun x : (∀ k : {k // k ≠ i}, Ω k.val) => g (x ⟨j,hij.symm⟩)),
    finiteAverage_pi_eval]

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section

abbrev PairingSpace (V : Type cycleUniverse19) [Fintype V] := Pairing (V ⊕ Fin (Fintype.card V % 2))

lemma pairingSpace_even (V : Type cycleUniverse20) [Fintype V] :
    Even (Fintype.card (V ⊕ Fin (Fintype.card V % 2))) := by
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.even_iff]
  omega

instance pairingSpace_nonempty (V : Type cycleUniverse21) [Fintype V] : Nonempty (PairingSpace V) :=
  Pairing.nonempty_of_even (pairingSpace_even V)

def paired {V : Type cycleUniverse22} [Fintype V] (p : PairingSpace V) (u v : V) : Prop :=
  p (Sum.inl u) = Sum.inl v

instance paired_decidable {V : Type cycleUniverse23} [Fintype V] (p : PairingSpace V) (u v : V) :
    Decidable (paired p u v) := Classical.propDecidable _

lemma paired_ne {V : Type cycleUniverse24} [Fintype V] (p : PairingSpace V) {u v : V}
    (h : paired p u v) : u ≠ v := by
  rintro rfl
  exact p.apply_ne _ h

lemma paired_symm {V : Type cycleUniverse25} [Fintype V] (p : PairingSpace V) {u v : V}
    (h : paired p u v) : paired p v u := by
  have hh := congrArg p h
  simpa only [paired,Pairing.apply_apply] using hh.symm

lemma paired_unique {V : Type cycleUniverse26} [Fintype V] (p : PairingSpace V) {u v w : V}
    (hv : paired p u v) (hw : paired p u w) : v = w :=
  Sum.inl_injective (hv.symm.trans hw)

def pairingInvolution {V : Type cycleUniverse27} [Fintype V] (p : PairingSpace V) (u : V) : V :=
  match p (Sum.inl u) with
  | Sum.inl v => v
  | Sum.inr _ => u

lemma pairingInvolution_eq_or_paired {V : Type cycleUniverse28} [Fintype V] (p : PairingSpace V) (u v : V) :
    pairingInvolution p u = v → u = v ∨ paired p u v := by
  unfold pairingInvolution paired
  cases h : p (Sum.inl u) with
  | inl w => simp only [Sum.inl.injEq]; exact Or.inr
  | inr w => intro hh; exact Or.inl hh

lemma pairingInvolution_involutive {V : Type cycleUniverse29} [Fintype V] (p : PairingSpace V) :
    Function.Involutive (pairingInvolution p) := by
  intro u
  unfold pairingInvolution
  cases h : p (Sum.inl u) with
  | inl v =>
    have hh := congrArg p h
    simp only [Pairing.apply_apply] at hh
    rw [← hh]
  | inr w => rw [h]

lemma paired_first_moment {V : Type cycleUniverse30} [Fintype V] (u v : V) (huv : u ≠ v) :
    finiteAverage (fun p : PairingSpace V => if paired p u v then 1 else 0) =
      1 / ((Fintype.card V:ℝ) + (Fintype.card V % 2 : ℕ) - 1) := by
  classical
  rw [finiteAverage_indicator]
  have h := Pairing.one_fraction (pairingSpace_even V) (Sum.inl u) (Sum.inl v)
    (by simpa using huv)
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add] at h
  dsimp only [Pairing.oneCount,paired] at h ⊢
  convert h using 1
  congr 2

lemma paired_two_moment {V : Type cycleUniverse31} [Fintype V] (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finiteAverage (fun p : PairingSpace V => if paired p a b ∧ paired p c d then 1 else 0) =
      1 / (((Fintype.card V:ℝ)+(Fintype.card V%2:ℕ)-1)*
        ((Fintype.card V:ℝ)+(Fintype.card V%2:ℕ)-3)) := by
  classical
  rw [finiteAverage_indicator]
  have h := Pairing.two_fraction (pairingSpace_even V)
    (Sum.inl a) (Sum.inl b) (Sum.inl c) (Sum.inl d)
    (by simpa using hab) (by simpa using hac) (by simpa using had)
    (by simpa using hbc) (by simpa using hbd) (by simpa using hcd)
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add] at h
  dsimp only [Pairing.twoCount,paired] at h ⊢
  convert h using 1
  congr 2

lemma paired_first_bound {V : Type cycleUniverse32} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (u v : V) (huv : u ≠ v) :
    finiteAverage (fun p : PairingSpace V => if paired p u v then 1 else 0) ≤
      1 / ((Fintype.card V:ℝ)-1) := by
  classical
  rw [paired_first_moment u v huv]
  have hn : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hm : (0:ℝ) ≤ (Fintype.card V%2:ℕ) := Nat.cast_nonneg _
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma paired_two_bound {V : Type cycleUniverse33} [Fintype V] (hV : 4 ≤ Fintype.card V)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finiteAverage (fun p : PairingSpace V => if paired p a b ∧ paired p c d then 1 else 0) ≤
      1 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) := by
  classical
  rw [paired_two_moment a b c d hab hac had hbc hbd hcd]
  have hn : (4:ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hm : (0:ℝ) ≤ (Fintype.card V%2:ℕ) := Nat.cast_nonneg _
  apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma finiteAverage_or_le {Ω : Type cycleUniverse34} [Fintype Ω] (P Q : Ω → Prop) :
    finiteAverage (fun ω => if P ω ∨ Q ω then 1 else 0) ≤
      finiteAverage (fun ω => if P ω then 1 else 0) +
      finiteAverage (fun ω => if Q ω then 1 else 0) := by
  rw [← finiteAverage_add]
  apply finiteAverage_mono
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]

lemma paired_event_local {I : Type cycleUniverse35} [Fintype I] [DecidableEq I]
    {V : I → Type cycleUniverse62} [∀ i, Fintype (V i)] (i : I) (a b : V i) (hab : a ≠ b) :
    finiteAverage (fun p : ∀ j, PairingSpace (V j) => if paired (p i) a b then 1 else 0) =
      1 / ((Fintype.card (V i):ℝ)+(Fintype.card (V i)%2:ℕ)-1) := by
  rw [finiteAverage_pi_eval (Ω:=fun j => PairingSpace (V j)) i
    (fun p => if paired p a b then 1 else 0),paired_first_moment a b hab]

lemma pairing_patterns_internal {V : Type cycleUniverse36} [Fintype V] (hV : 4 ≤ Fintype.card V)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    finiteAverage (fun p : PairingSpace V =>
      if (paired p a c ∧ paired p b d) ∨ (paired p a d ∧ paired p b c) then 1 else 0) ≤
      2 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) := by
  have h₁ := paired_two_bound hV a c b d hac hab had hbc.symm hcd hbd
  have h₂ := paired_two_bound hV a d b c had hab hac hbd.symm hcd.symm hbc
  have h := finiteAverage_or_le
    (fun p : PairingSpace V => paired p a c ∧ paired p b d)
    (fun p : PairingSpace V => paired p a d ∧ paired p b c)
  calc
    _ ≤ finiteAverage (fun p : PairingSpace V => if paired p a c ∧ paired p b d then 1 else 0) +
        finiteAverage (fun p : PairingSpace V => if paired p a d ∧ paired p b c then 1 else 0) := by
      convert h using 1 <;> congr 3 <;> funext p <;> split_ifs <;> rfl
    _ ≤ 1 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) +
      1 / (((Fintype.card V:ℝ)-1)*((Fintype.card V:ℝ)-3)) := add_le_add h₁ h₂
    _ = _ := by ring

lemma pairing_patterns_cross {I : Type cycleUniverse37} [Fintype I] [DecidableEq I]
    {V : I → Type cycleUniverse63} [∀ i, Fintype (V i)] (i j : I) (hij : i ≠ j)
    (a c : V i) (hac : a ≠ c) (b d : V j) (hbd : b ≠ d) :
    finiteAverage (fun p : ∀ k, PairingSpace (V k) =>
      if paired (p i) a c ∧ paired (p j) b d then 1 else 0) =
      (1 / ((Fintype.card (V i):ℝ)+(Fintype.card (V i)%2:ℕ)-1)) *
      (1 / ((Fintype.card (V j):ℝ)+(Fintype.card (V j)%2:ℕ)-1)) := by
  have hind : (fun p : ∀ k, PairingSpace (V k) =>
      if paired (p i) a c ∧ paired (p j) b d then (1:ℝ) else 0) =
      (fun p => (if paired (p i) a c then 1 else 0)*(if paired (p j) b d then 1 else 0)) := by
    funext p
    split_ifs <;> simp_all
  rw [hind,finiteAverage_pi_pair (Ω:=fun k => PairingSpace (V k)) i j hij
    (fun p => if paired p a c then 1 else 0) (fun p => if paired p b d then 1 else 0),paired_first_moment a c hac,paired_first_moment b d hbd]

lemma pairing_patterns_cross_bound {I : Type cycleUniverse38} [Fintype I] [DecidableEq I]
    {V : I → Type cycleUniverse64} [∀ i, Fintype (V i)] (i j : I) (hij : i ≠ j)
    (hi : 2 ≤ Fintype.card (V i)) (hj : 2 ≤ Fintype.card (V j))
    (a c : V i) (hac : a ≠ c) (b d : V j) (hbd : b ≠ d) :
    finiteAverage (fun p : ∀ k, PairingSpace (V k) =>
      if paired (p i) a c ∧ paired (p j) b d then 1 else 0) ≤
      1 / (((Fintype.card (V i):ℝ)-1)*((Fintype.card (V j):ℝ)-1)) := by
  rw [pairing_patterns_cross i j hij a c hac b d hbd,one_div_mul_one_div]
  have hi' : (2:ℝ) ≤ Fintype.card (V i) := by exact_mod_cast hi
  have hj' : (2:ℝ) ≤ Fintype.card (V j) := by exact_mod_cast hj
  have hmi : (0:ℝ) ≤ (Fintype.card (V i)%2:ℕ) := Nat.cast_nonneg _
  have hmj : (0:ℝ) ≤ (Fintype.card (V j)%2:ℕ) := Nat.cast_nonneg _
  apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
namespace Pairing
variable {V : Type cycleUniverse39}

def pairSetoid (p : Pairing V) : Setoid V where
  r u v := u = v ∨ p u = v
  iseqv := ⟨fun _ => Or.inl rfl, (by
    intro u v h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (by have hh := congrArg p h; simpa using hh.symm)), (by
    intro u v w h1 h2
    rcases h1 with rfl | h1
    · exact h2
    rcases h2 with rfl | h2
    · exact Or.inr h1
    · left
      have hh := congrArg p h1
      simpa only [apply_apply,h2] using hh)⟩

def PairQuotient (p : Pairing V) := Quotient (pairSetoid p)

instance [Fintype V] (p : Pairing V) : Fintype (PairQuotient p) := by
  classical
  unfold PairQuotient
  infer_instance

instance (p : Pairing V) : DecidableEq (PairQuotient p) := Classical.decEq _

def project (p : Pairing V) (v : V) : PairQuotient p := Quotient.mk (pairSetoid p) v

lemma project_eq_iff (p : Pairing V) (u v : V) :
    project p u = project p v ↔ u = v ∨ p u = v := Quotient.eq

lemma project_surjective (p : Pairing V) : Function.Surjective (project p) := by
  intro q
  exact Quotient.exists_rep q

@[simp] lemma project_apply (p : Pairing V) (v : V) : project p (p v) = project p v :=
  (project_eq_iff p _ _).mpr (Or.inr (apply_apply p v))

lemma fiber_card [Fintype V] (p : Pairing V) (q : PairQuotient p) :
    Fintype.card {v // project p v = q} = 2 := by
  classical
  obtain ⟨x,rfl⟩ := project_surjective p q
  rw [Fintype.card_subtype]
  have heq : (univ.filter (fun v => project p v = project p x)) = {x,p x} := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    rw [project_eq_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        have hh := congrArg p h
        simpa only [apply_apply] using hh
    · rintro (h | h)
      · exact Or.inl h
      · right
        subst v
        simp
  rw [heq]
  simp [Ne.symm (apply_ne p x)]

lemma card_pairQuotient [Fintype V] (p : Pairing V) :
    2 * Fintype.card (PairQuotient p) = Fintype.card V := by
  classical
  have h : (∑ q : PairQuotient p, Fintype.card {v // project p v = q}) = Fintype.card V := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (project p))
  simpa only [fiber_card,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_comm] using h
end Pairing

def oldProject {V : Type cycleUniverse40} [Fintype V] (p : PairingSpace V) (v : V) : Pairing.PairQuotient p :=
  p.project (Sum.inl v)

lemma oldProject_eq_iff {V : Type cycleUniverse41} [Fintype V] (p : PairingSpace V) (u v : V) :
    oldProject p u = oldProject p v ↔ u = v ∨ paired p u v := by
  simp only [oldProject,Pairing.project_eq_iff,Sum.inl.injEq,paired]

lemma dummy_partner_is_old {V : Type cycleUniverse42} [Fintype V] (p : PairingSpace V)
    (d : Fin (Fintype.card V % 2)) : ∃ v : V, p (Sum.inr d) = Sum.inl v := by
  cases h : p (Sum.inr d) with
  | inl v => exact ⟨v,rfl⟩
  | inr e =>
    have he : e = d := by
      apply Fin.ext
      have hd := d.isLt
      have he := e.isLt
      have hh := Nat.mod_lt (Fintype.card V) (by omega : 0 < 2)
      omega
    subst e
    exact False.elim (p.apply_ne _ h)

lemma oldProject_surjective {V : Type cycleUniverse43} [Fintype V] (p : PairingSpace V) :
    Function.Surjective (oldProject p) := by
  intro q
  obtain ⟨x,rfl⟩ := p.project_surjective q
  cases x with
  | inl v => exact ⟨v,rfl⟩
  | inr d =>
    obtain ⟨v,hv⟩ := dummy_partner_is_old p d
    refine ⟨v,?_⟩
    change p.project (Sum.inl v) = p.project (Sum.inr d)
    rw [← hv,p.project_apply]

lemma old_quotient_order {V : Type cycleUniverse44} [Fintype V] (p : PairingSpace V) :
    Fintype.card (Pairing.PairQuotient p) = Fintype.card V - Fintype.card V / 2 := by
  have h := p.card_pairQuotient
  simp only [Fintype.card_sum,Fintype.card_fin] at h
  omega

lemma old_fiber_card_le_two {V : Type cycleUniverse45} [Fintype V] (p : PairingSpace V)
    (q : Pairing.PairQuotient p) : Fintype.card {v // oldProject p v = q} ≤ 2 := by
  classical
  calc
    _ ≤ Fintype.card {v // p.project v = q} := ?_
    _ = 2 := p.fiber_card q
  apply Fintype.card_le_of_injective (fun x : {v // oldProject p v = q} =>
    (⟨Sum.inl x.val,x.property⟩ : {v // p.project v = q}))
  intro x y h
  apply Subtype.ext
  exact Sum.inl_injective (congrArg Subtype.val h)

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section

variable {V : Type cycleUniverse46} {I : Type cycleUniverse47} [Fintype V] [Fintype I] (X : I → Finset V)

abbrev Outside := {v : V // ∀ i, v ∉ X i}
abbrev FoldDomain := Outside X ⊕ (Σ i, X i)

def unfoldVertex : FoldDomain X → V
  | Sum.inl v => v.val
  | Sum.inr v => v.2.val

lemma unfoldVertex_bijective {V : Type cycleUniverse48} {I : Type cycleUniverse49} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise (fun i j => Disjoint (X i) (X j))) :
    Function.Bijective (unfoldVertex X) := by
  classical
  constructor
  · rintro (u | ⟨i,u⟩) (v | ⟨j,v⟩) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · change u.val = v.val at h
      exact False.elim (u.property j (h.symm ▸ v.property))
    · change u.val = v.val at h
      exact False.elim (v.property i (h ▸ u.property))
    · change u.val = v.val at h
      have hij : i = j := by
        by_contra hij
        exact Finset.disjoint_left.mp (hd hij) u.property (h.symm ▸ v.property)
      subst j
      exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Subtype.ext h)))
  · intro v
    by_cases h : ∃ i, v ∈ X i
    · obtain ⟨i,hi⟩ := h
      exact ⟨Sum.inr ⟨i,⟨v,hi⟩⟩,rfl⟩
    · exact ⟨Sum.inl ⟨v,by simpa only [not_exists] using h⟩,rfl⟩

def splitEquiv (hd : Pairwise (fun i j => Disjoint (X i) (X j))) : FoldDomain X ≃ V :=
  Equiv.ofBijective (unfoldVertex X) (unfoldVertex_bijective X hd)

abbrev FamilyQuotient (p : ∀ i, PairingSpace (X i)) :=
  Outside X ⊕ (Σ i, Pairing.PairQuotient (p i))

instance (p : ∀ i, PairingSpace (X i)) : Fintype (FamilyQuotient X p) := by
  classical
  unfold FamilyQuotient
  infer_instance

instance (p : ∀ i, PairingSpace (X i)) : DecidableEq (FamilyQuotient X p) := Classical.decEq _

def foldOnDomain (p : ∀ i, PairingSpace (X i)) : FoldDomain X → FamilyQuotient X p
  | Sum.inl v => Sum.inl v
  | Sum.inr ⟨i,v⟩ => Sum.inr ⟨i,oldProject (p i) v⟩

def familyProject (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) : V → FamilyQuotient X p :=
  foldOnDomain X p ∘ (splitEquiv X hd).symm

lemma familyProject_surjective (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) : Function.Surjective (familyProject X hd p) := by
  have h : Function.Surjective (foldOnDomain X p) := by
    rintro (v | ⟨i,q⟩)
    · exact ⟨Sum.inl v,rfl⟩
    · obtain ⟨v,hv⟩ := oldProject_surjective (p i) q
      exact ⟨Sum.inr ⟨i,v⟩,by simp only [foldOnDomain,hv]⟩
  exact h.comp (splitEquiv X hd).symm.surjective

lemma family_quotient_order_add (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) :
    Fintype.card (FamilyQuotient X p) + ∑ i, (X i).card / 2 = Fintype.card V := by
  classical
  have hV := Fintype.card_congr (splitEquiv X hd)
  have hV' : Fintype.card (Outside X) + ∑ i, (X i).card = Fintype.card V := by
    simpa only [FoldDomain,Fintype.card_sum,Fintype.card_sigma,Fintype.card_coe] using hV
  rw [Fintype.card_sum,Fintype.card_sigma,add_assoc,← Finset.sum_add_distrib]
  simp_rw [old_quotient_order,Fintype.card_coe,Nat.sub_add_cancel (Nat.div_le_self _ _)]
  exact hV'

theorem family_quotient_order (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) :
    Fintype.card (FamilyQuotient X p) = Fintype.card V - ∑ i, (X i).card / 2 := by
  have h := family_quotient_order_add X hd p
  omega

lemma familyProject_eq_on_outside (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (v : Outside X) :
    familyProject X hd p v.val = Sum.inl v := by
  have hv : (splitEquiv X hd) (Sum.inl v) = v.val := rfl
  rw [familyProject,Function.comp_apply,← hv,Equiv.symm_apply_apply]
  rfl

lemma familyProject_eq_on_inside (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (i : I) (v : X i) :
    familyProject X hd p v.val = Sum.inr ⟨i,oldProject (p i) v⟩ := by
  have hv : (splitEquiv X hd) (Sum.inr ⟨i,v⟩) = v.val := rfl
  rw [familyProject,Function.comp_apply,← hv,Equiv.symm_apply_apply]
  rfl

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse50} {I : Type cycleUniverse51} [Fintype V] [Fintype I] (X : I → Finset V)

def familyPaired (p : ∀ i, PairingSpace (X i)) (u v : V) : Prop :=
  ∃ (i : I) (hu : u ∈ X i) (hv : v ∈ X i), paired (p i) ⟨u,hu⟩ ⟨v,hv⟩

lemma familyProject_apply_split (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (x : FoldDomain X) :
    familyProject X hd p ((splitEquiv X hd) x) = foldOnDomain X p x := by
  simp only [familyProject,Function.comp_apply,Equiv.symm_apply_apply]

lemma familyProject_eq_iff (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (u v : V) :
    familyProject X hd p u = familyProject X hd p v ↔ u = v ∨ familyPaired X p u v := by
  constructor
  · intro h
    obtain ⟨a,rfl⟩ := (splitEquiv X hd).surjective u
    obtain ⟨b,rfl⟩ := (splitEquiv X hd).surjective v
    rw [familyProject_apply_split,familyProject_apply_split] at h
    rcases a with a | ⟨i,a⟩ <;> rcases b with b | ⟨j,b⟩
    · exact Or.inl (congrArg (splitEquiv X hd) (congrArg Sum.inl (Sum.inl.inj h)))
    · simp only [foldOnDomain,Sum.inl_ne_inr] at h
    · simp only [foldOnDomain,Sum.inr_ne_inl] at h
    · have hh := Sum.inr.inj h
      have hij := congrArg Sigma.fst hh
      change i = j at hij
      subst j
      have hval : oldProject (p i) a = oldProject (p i) b := by
        simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh
      obtain hab | hab := (oldProject_eq_iff (p i) a b).mp hval
      · subst b
        exact Or.inl rfl
      · exact Or.inr ⟨i,a.property,b.property,hab⟩
  · rintro (rfl | ⟨i,hu,hv,hp⟩)
    · rfl
    · rw [familyProject_eq_on_inside X hd p i ⟨u,hu⟩,
        familyProject_eq_on_inside X hd p i ⟨v,hv⟩]
      congr 2
      exact (oldProject_eq_iff (p i) ⟨u,hu⟩ ⟨v,hv⟩).mpr (Or.inr hp)

lemma familyPaired_ne {V : Type cycleUniverse52} {I : Type cycleUniverse53} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (p : ∀ i, PairingSpace (X i)) {u v : V}
    (h : familyPaired X p u v) : u ≠ v := by
  obtain ⟨i,hu,hv,hp⟩ := h
  intro he
  subst v
  exact Pairing.apply_ne (p i) (Sum.inl ⟨u,hu⟩) hp

lemma familyPaired_unique {V : Type cycleUniverse54} {I : Type cycleUniverse55} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) {u v w : V}
    (hv : familyPaired X p u v) (hw : familyPaired X p u w) : v = w := by
  obtain ⟨i,hu,hv,hpi⟩ := hv
  obtain ⟨j,hu',hw,hpj⟩ := hw
  have hij : i = j := by
    by_contra hij
    exact Finset.disjoint_left.mp (hd hij) hu hu'
  subst j
  exact congrArg Subtype.val (paired_unique (p i) hpi hpj)

lemma familyProject_fiber_triple (hd : Pairwise (fun i j => Disjoint (X i) (X j)))
    (p : ∀ i, PairingSpace (X i)) (u v w : V)
    (huv : familyProject X hd p u = familyProject X hd p v)
    (huw : familyProject X hd p u = familyProject X hd p w) :
    u = v ∨ u = w ∨ v = w := by
  obtain huv | huv := (familyProject_eq_iff X hd p u v).mp huv
  · exact Or.inl huv
  obtain huw | huw := (familyProject_eq_iff X hd p u w).mp huw
  · exact Or.inr (Or.inl huw)
  · exact Or.inr (Or.inr (familyPaired_unique X hd p huv huw))

end
end ErdosGallai.Batch
namespace ErdosGallai.Batch
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse56} {I : Type cycleUniverse57} [Fintype V] [Fintype I] (X : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (X i) (X j))) (p : ∀ i, PairingSpace (X i))

lemma loop_iff_familyPaired {u v : V} (huv : u ≠ v) :
    (Sym2.map (familyProject X hd p) s(u,v)).IsDiag ↔ familyPaired X p u v := by
  simp only [Sym2.map_mk,Sym2.mk_isDiag_iff,
    familyProject_eq_iff,huv,false_or]

lemma shared_endpoint_collision {v u w : V} (huw : u ≠ w)
    (h : Sym2.map (familyProject X hd p) s(v,u) =
      Sym2.map (familyProject X hd p) s(v,w)) : familyPaired X p u w := by
  have h := (Sym2.mk_eq_mk_iff (p := (familyProject X hd p v, familyProject X hd p u))
    (q := (familyProject X hd p v, familyProject X hd p w))).mp h
  simp only [Prod.mk.injEq,Prod.swap_prod_mk] at h
  have he : familyProject X hd p u = familyProject X hd p w := by
    rcases h with h | h
    · exact h.2
    · exact h.2.trans h.1
  exact ((familyProject_eq_iff X hd p u w).mp he).resolve_left huw

lemma four_endpoint_collision {u v x y : V}
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (h : Sym2.map (familyProject X hd p) s(u,v) =
      Sym2.map (familyProject X hd p) s(x,y)) :
    (familyPaired X p u x ∧ familyPaired X p v y) ∨
    (familyPaired X p u y ∧ familyPaired X p v x) := by
  have h := (Sym2.mk_eq_mk_iff (p := (familyProject X hd p u, familyProject X hd p v))
    (q := (familyProject X hd p x, familyProject X hd p y))).mp h
  simp only [Prod.mk.injEq,Prod.swap_prod_mk] at h
  rcases h with h | h
  · exact Or.inl ⟨((familyProject_eq_iff X hd p u x).mp h.1).resolve_left hux,
      ((familyProject_eq_iff X hd p v y).mp h.2).resolve_left hvy⟩
  · exact Or.inr ⟨((familyProject_eq_iff X hd p u y).mp h.1).resolve_left huy,
      ((familyProject_eq_iff X hd p v x).mp h.2).resolve_left hvx⟩

lemma paired_fibers_placement {V : Type cycleUniverse58} {I : Type cycleUniverse59} [_contextInstance2 : Fintype V] [_contextInstance3 : Fintype I] (X : I → Finset V) (p : (i : I) → ErdosGallai.Batch.PairingSpace (Subtype fun x => x ∈ X i)) {u v x y : V}
    (hux : familyPaired X p u x) (hvy : familyPaired X p v y) :
    (∃ i, u ∈ X i ∧ v ∈ X i ∧ x ∈ X i ∧ y ∈ X i) ∨
    (∃ i j, i ≠ j ∧ u ∈ X i ∧ x ∈ X i ∧ v ∈ X j ∧ y ∈ X j) := by
  obtain ⟨i,hu,hx,_⟩ := hux
  obtain ⟨j,hv,hy,_⟩ := hvy
  by_cases hij : i = j
  · subst j
    exact Or.inl ⟨i,hu,hv,hx,hy⟩
  · exact Or.inr ⟨i,j,hij,hu,hx,hv,hy⟩

end
end ErdosGallai.Batch

end
end
end

end OAI
