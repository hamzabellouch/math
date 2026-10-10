import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.OutputRebase
import OAI.Combinatorics.SharpRamsey.Entropy.SelectedEntropy

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α β Ω : Type} [Fintype α] [Fintype β] [Fintype Ω]

def reverseTuple {n : ℕ} (f : Fin n→α) : Fin n→α:=fun i=>f i.rev

omit [Fintype α] in
lemma occurs_iff_orderEmbedding {N n : ℕ} (f : Fin n→α) (g : Fin N→α) :
    Occurs f g ↔ ∃ e : Fin n↪o Fin N,∀ i,g (e i)=f i := by
  constructor
  · rintro ⟨S,hS⟩
    exact ⟨S.val.orderEmbOfFin S.property,hS⟩
  · rintro ⟨e,he⟩
    let S : Finset (Fin N):=univ.image e
    have hS : S.card=n:=by rw [card_image_of_injective _ e.injective,card_univ,Fintype.card_fin]
    refine ⟨⟨S,hS⟩,?_⟩
    have hh : e=S.orderEmbOfFin hS:=orderEmbOfFin_unique' hS (fun i=>mem_image.mpr ⟨i,mem_univ _,rfl⟩)
    intro i
    change g (S.orderEmbOfFin hS i)=f i
    simpa only [←hh] using he i

omit [Fintype α] in
lemma occurs_restrict {N n m : ℕ} {f : Fin n→α} {g : Fin N→α}
    (e : Fin m↪o Fin n) (h : Occurs f g) : Occurs (fun i=>f (e i)) g := by
  obtain ⟨j,hj⟩:=(occurs_iff_orderEmbedding _ _).mp h
  exact (occurs_iff_orderEmbedding _ _).mpr ⟨e.trans j,fun i=>hj (e i)⟩

omit [Fintype α] in
lemma occurs_reverse_restrict {N n m : ℕ} {f : Fin n→α} {g : Fin N→α}
    (e : Fin m↪o Fin n) (h : Occurs (reverseTuple f) g) :
    Occurs (reverseTuple (fun i=>f (e i))) g := by
  let er : Fin m↪o Fin n:=OrderEmbedding.ofStrictMono (fun i=>(e i.rev).rev) (by
    intro i j hij
    exact Fin.rev_lt_rev.mpr (e.strictMono (Fin.rev_lt_rev.mpr hij)))
  have hh:=occurs_restrict er h
  change Occurs (fun i=>f (Fin.rev ((e i.rev).rev))) g at hh
  change Occurs (fun i=>f (e i.rev)) g
  simpa only [Fin.rev_rev] using hh

variable {N n m : ℕ} {p : Law Ω} {G : Ω→Fin n→β} {B C L : ℝ}

lemma ContextOutput.map_domination (e : ContextOutput p G m B C L)
    (stream : Ω→Fin N→α) {D : ℝ} (hL : 0 ≤ L)
    (hdom : ∀ g,(p.map stream).mass g ≤ D/(Fintype.card α:ℝ)^N) :
    ∀ g,(e.μ.map (stream∘e.source)).mass g ≤ L*D/(Fintype.card α:ℝ)^N := by
  intro g
  rw [←Law.map_map]
  calc
    _ ≤ ∑ x ∈ univ.filter (fun x=>stream x=g),L*p.mass x:=by
      dsimp only [Law.map]
      convert sum_le_sum (fun x (_ : x∈univ.filter (fun x=>stream x=g))=>e.dominated x) using 1
      congr!
    _ = L*(p.map stream).mass g:=by
      simp only [Law.map,mul_sum]
      congr!
    _ ≤ L*(D/(Fintype.card α:ℝ)^N):=mul_le_mul_of_nonneg_left (hdom g) hL
    _ = _:=by ring

lemma ContextOutput.length_le (e : ContextOutput p G m B C L) : m ≤ n := by
  have hx : Nonempty e.X:=by
    by_contra hh
    have hz : Fintype.card e.X=0:=Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hh)
    have : IsEmpty e.X:=Fintype.card_eq_zero_iff.mp hz
    have he : (0:ℝ)=1:=by simpa using e.μ.total
    norm_num at he
  obtain ⟨x⟩:=hx
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (e.chosen x) (e.chosen x).injective

theorem ContextOutput.tracked_entropy [Nonempty α]
    (e : ContextOutput p G m B C L) (stream : Ω→Fin N→α) (F : Ω→Fin n→α)
    (φ : α→β) (hφ : Function.Injective φ) (hG : ∀ x i,G x i=φ (F x i))
    {d : ℕ} (hd : 1 ≤ d) (hm : 0 < m) (hn : n ≤ N)
    {D q σ η c : ℝ} (hD : 0 < D) (hL : 0 < L) (hq : 0 < q) (hσ : 0 < σ) (hc : 0 < c)
    (hdom : ∀ g,(p.map stream).mass g ≤ D/(Fintype.card α:ℝ)^N)
    (hselect : ∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x))
    (hsize : (N:ℝ) ≤ q^d*σ) (hlength : c*q*σ^(1+η) ≤ m)
    (halphabet : q^(2*d-1) ≤ (Fintype.card α:ℝ)) :
    (m:ℝ)*((d:ℝ)*log q+η*log σ+log c-1)-log (2*(L*D)) ≤
      entropy (e.μ.map (fun x i=>G (e.source x) (e.chosen x i))) := by
  let f:=fun x i=>F (e.source x) (e.chosen x i)
  have hselection : ∀ x,e.μ.mass x≠0→Occurs (f x) (stream (e.source x)) ∨
      Occurs (reverseTuple (f x)) (stream (e.source x)):=by
    intro x _
    rcases hselect (e.source x) (e.supported x) with h|h
    · exact Or.inl (occurs_restrict (e.chosen x) h)
    · exact Or.inr (occurs_reverse_restrict (e.chosen x) h)
  have hh:=selected_map_entropy hd hm (e.length_le.trans hn) e.μ (stream∘e.source) f reverseTuple
    (mul_pos hL hD) hq hσ hc (e.map_domination stream hL.le hdom) hselection hsize hlength halphabet
  have he : entropy (e.μ.map (fun x i=>G (e.source x) (e.chosen x i)))=entropy (e.μ.map f) := by
    have hp : Function.Injective (fun a : Fin m→α=>φ∘a):=by
      intro a b hab
      funext i
      exact hφ (congrFun hab i)
    have h:=entropy_map_eq_of_injective (e.μ.map f) (fun a : Fin m→α=>φ∘a) hp
    rw [Law.map_map] at h
    convert h using 1
    congr 2
    funext x i
    exact hG _ _
  rwa [he]
end
end SharpLogRamsey.Selection

end

end OAI
