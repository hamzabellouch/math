import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialEmptyInterior

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

namespace PolynomialSignSet
open Set
open scoped Classical
variable {X ι : Type*} {c : X → ι → ℝ}

lemma univ : PolynomialSignSet c Set.univ := by simpa using zero (c := c) 0
lemma empty : PolynomialSignSet c ∅ := by simpa using (univ (c := c)).compl
lemma inter {S T : Set X} (hS : PolynomialSignSet c S) (hT : PolynomialSignSet c T) :
    PolynomialSignSet c (S ∩ T) := by
  simpa only [compl_union,compl_compl] using (hS.compl.union hT.compl).compl
lemma const (p : Prop) : PolynomialSignSet c {_x : X | p} := by
  by_cases h : p
  · simpa [h] using (univ (c := c))
  · simpa [h] using (empty (c := c))

lemma exists_finset {α : Type*} (s : Finset α) (P : α → X → Prop)
    (hP : ∀ a ∈ s, PolynomialSignSet c {x | P a x}) :
    PolynomialSignSet c {x | ∃ a ∈ s, P a x} := by
  induction s using Finset.induction_on with
  | empty => simpa using (empty (c := c))
  | @insert a s ha ih =>
    have he : {x | ∃ b ∈ insert a s, P b x} = {x | P a x} ∪ {x | ∃ b ∈ s, P b x} := by
      ext x
      simp
    rw [he]
    exact (hP a (by simp)).union (ih (fun b hb => hP b (by simp [hb])))

lemma exists_finite {α : Type*} [Finite α] (P : α → X → Prop)
    (hP : ∀ a, PolynomialSignSet c {x | P a x}) :
    PolynomialSignSet c {x | ∃ a, P a x} := by
  let := Fintype.ofFinite α
  simpa using exists_finset Finset.univ P (fun a _ => hP a)

lemma forall_finite {α : Type*} [Finite α] (P : α → X → Prop)
    (hP : ∀ a, PolynomialSignSet c {x | P a x}) :
    PolynomialSignSet c {x | ∀ a, P a x} := by
  convert (exists_finite (fun a x => ¬ P a x) (fun a => (hP a).compl)).compl using 1
  ext x
  simp

lemma sign (p : MvPolynomial ι ℝ) (s : SignType) :
    PolynomialSignSet c {x | SignType.sign (MvPolynomial.eval (c x) p) = s} := by
  cases s
  · simpa only [SignType.zero_eq_zero,sign_eq_zero_iff] using zero (c := c) p
  · simpa only [SignType.neg_eq_neg_one,sign_eq_neg_one_iff,map_neg,neg_pos] using positive (c := c) (-p)
  · simpa only [SignType.pos_eq_one,sign_eq_one_iff] using positive (c := c) p

end PolynomialSignSet

namespace SignElimination
open MvPolynomial Set
open scoped Classical BigOperators

def RationalOn {X ι : Type*} (c : X → ι → ℝ) (S : Set X) (f : X → ℝ) : Prop :=
  ∃ p q : MvPolynomial ι ℝ, ∀ x ∈ S,
    MvPolynomial.eval (c x) q ≠ 0 ∧ f x = MvPolynomial.eval (c x) p / MvPolynomial.eval (c x) q

namespace RationalOn
variable {X ι : Type*} {c : X → ι → ℝ} {S T : Set X} {f g : X → ℝ}

lemma congr (hf : RationalOn c S f) (hfg : ∀ x ∈ S, f x = g x) : RationalOn c S g := by
  obtain ⟨p,q,h⟩ := hf
  exact ⟨p,q,fun x hx => ⟨(h x hx).1,(hfg x hx).symm.trans (h x hx).2⟩⟩

lemma mono (hf : RationalOn c S f) (hTS : T ⊆ S) : RationalOn c T f := by
  obtain ⟨p,q,h⟩ := hf
  exact ⟨p,q,fun x hx => h x (hTS hx)⟩

lemma polynomial (p : MvPolynomial ι ℝ) : RationalOn c S (fun x => MvPolynomial.eval (c x) p) := by
  exact ⟨p,1,fun x hx => by simp⟩

lemma const (a : ℝ) : RationalOn c S (fun _ => a) := by
  simpa using polynomial (c := c) (S := S) (C a)

lemma add (hf : RationalOn c S f) (hg : RationalOn c S g) : RationalOn c S (fun x => f x + g x) := by
  obtain ⟨p,q,hp⟩ := hf
  obtain ⟨r,s,hr⟩ := hg
  refine ⟨p*s+r*q,q*s,fun x hx => ?_⟩
  obtain ⟨hq,hf⟩ := hp x hx
  obtain ⟨hs,hg⟩ := hr x hx
  simp only [map_add,map_mul]
  refine ⟨mul_ne_zero hq hs,?_⟩
  rw [hf,hg]
  field_simp

lemma neg (hf : RationalOn c S f) : RationalOn c S (fun x => -f x) := by
  obtain ⟨p,q,h⟩ := hf
  exact ⟨-p,q,fun x hx => ⟨(h x hx).1,by simp [(h x hx).2,neg_div]⟩⟩

lemma sub (hf : RationalOn c S f) (hg : RationalOn c S g) : RationalOn c S (fun x => f x-g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma mul (hf : RationalOn c S f) (hg : RationalOn c S g) : RationalOn c S (fun x => f x*g x) := by
  obtain ⟨p,q,hp⟩ := hf
  obtain ⟨r,s,hr⟩ := hg
  refine ⟨p*r,q*s,fun x hx => ?_⟩
  exact ⟨by simp [mul_ne_zero (hp x hx).1 (hr x hx).1],by
    simp only [(hp x hx).2,(hr x hx).2,map_mul,div_mul_div_comm]⟩

lemma pow (hf : RationalOn c S f) (n : ℕ) : RationalOn c S (fun x => f x ^ n) := by
  induction n with
  | zero => simpa using (const (c := c) (S := S) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma inv (hf : RationalOn c S f) (hn : ∀ x ∈ S, f x ≠ 0) : RationalOn c S (fun x => (f x)⁻¹) := by
  obtain ⟨p,q,h⟩ := hf
  refine ⟨q,p,fun x hx => ?_⟩
  have hp : MvPolynomial.eval (c x) p ≠ 0 := by
    intro hz
    have he := (h x hx).2
    simp [hz] at he
    exact hn x hx he
  exact ⟨hp,by simp [(h x hx).2]⟩

lemma div (hf : RationalOn c S f) (hg : RationalOn c S g) (hn : ∀ x ∈ S, g x ≠ 0) :
    RationalOn c S (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hn)

lemma sum {α : Type*} (s : Finset α) (f : α → X → ℝ)
    (hf : ∀ a ∈ s, RationalOn c S (f a)) : RationalOn c S (fun x => ∑ a ∈ s, f a x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (const (c := c) (S := S) 0)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (by simp)).add (ih (fun b hb => hf b (by simp [hb])))

lemma eval {α : Type*} (p : MvPolynomial α ℝ) (f : α → X → ℝ)
    (hf : ∀ a, RationalOn c S (f a)) :
    RationalOn c S (fun x => MvPolynomial.eval (fun a => f a x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (const (c := c) (S := S) a)
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p a hp => simpa only [map_mul,MvPolynomial.eval_X] using hp.mul (hf a)

lemma sign_inv_real (a : ℝ) : SignType.sign a⁻¹ = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [sign_neg ha,sign_neg (inv_lt_zero.mpr ha)]
  · simp [ha]
  · rw [sign_pos ha,sign_pos (inv_pos.mpr ha)]

lemma sign_set (hf : RationalOn c S f) (hS : PolynomialSignSet c S) (s : SignType) :
    PolynomialSignSet c (S ∩ {x | SignType.sign (f x) = s}) := by
  obtain ⟨p,q,h⟩ := hf
  have he : S ∩ {x | SignType.sign (f x) = s} =
      S ∩ {x | SignType.sign (MvPolynomial.eval (c x) (p*q)) = s} := by
    ext x
    simp only [mem_inter_iff,mem_ofPred_eq]
    apply and_congr_right
    intro hx
    rw [(h x hx).2,map_mul,div_eq_mul_inv,sign_mul,sign_mul,sign_inv_real]
  rw [he]
  exact hS.inter (PolynomialSignSet.sign _ _)

end RationalOn

lemma polynomialSignSet_finite_signs {X ι α : Type*} [Finite α]
    {c : X → ι → ℝ} {S : Set X} (hS : PolynomialSignSet c S)
    (f : α → X → ℝ) (hf : ∀ a, RationalOn c S (f a)) (W : (α → SignType) → Prop) :
    PolynomialSignSet c (S ∩ {x | W (fun a => SignType.sign (f a x))}) := by
  have h (σ : α → SignType) :
      PolynomialSignSet c {x | x ∈ S ∧ W σ ∧ ∀ a, SignType.sign (f a x) = σ a} := by
    have hsign := PolynomialSignSet.forall_finite
      (fun a x => x ∈ S ∧ SignType.sign (f a x) = σ a)
      (fun a => (hf a).sign_set hS (σ a))
    have hh := (hS.inter (PolynomialSignSet.const (c := c) (W σ))).inter hsign
    convert hh using 1
    ext x
    simp only [mem_ofPred_eq,mem_inter_iff]
    constructor
    · rintro ⟨hx,hw,hs⟩
      exact ⟨⟨hx,hw⟩,fun a => ⟨hx,hs a⟩⟩
    · rintro ⟨⟨hx,hw⟩,hs⟩
      exact ⟨hx,hw,fun a => (hs a).2⟩
  have hh := PolynomialSignSet.exists_finite _ h
  convert hh using 1
  ext x
  simp only [mem_ofPred_eq,mem_inter_iff]
  constructor
  · rintro ⟨hx,hw⟩
    exact ⟨_,hx,hw,fun _ => rfl⟩
  · rintro ⟨σ,hx,hw,hs⟩
    exact ⟨hx,(funext hs) ▸ hw⟩

end SignElimination
end Release061

end

end OAI
