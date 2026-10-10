import Mathlib
import OAI.Analysis.BoundedHochschild.RareScales

namespace OAI

/-! Centered free coefficients and vanishing graded moments. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
namespace HochschildFreeMoments
variable {M G : Type*} [Ring M] [Algebra ℂ M] [Group G]
  (B : Subalgebra ℂ M) (u : G →* M) (τ : M →ₗ[ℂ] ℂ)

abbrev Letter := B ⊕ G

def tag : Letter B (G := G) → Bool
  | .inl _ => false
  | .inr _ => true

def value : Letter B (G := G) → M
  | .inl b => b
  | .inr g => u g

def degreeLetter : Letter B (G := G) → G
  | .inl _ => 1
  | .inr g => g

def evaluate (l : List (Letter B (G := G))) : M := (l.map (value B u)).prod

def degree (l : List (Letter B (G := G))) : G := (l.map (degreeLetter B)).prod

@[simp] lemma evaluate_nil : evaluate B u []=1 := rfl
@[simp] lemma evaluate_cons (x : Letter B (G := G)) (l : List (Letter B (G := G))) :
    evaluate B u (x::l)=value B u x*evaluate B u l := rfl
@[simp] lemma evaluate_append (p q : List (Letter B (G := G))) :
    evaluate B u (p++q)=evaluate B u p*evaluate B u q := by simp [evaluate,List.prod_append]
@[simp] lemma degree_nil : degree B ([] : List (Letter B (G := G)))=1 := rfl
@[simp] lemma degree_cons (x : Letter B (G := G)) (l : List (Letter B (G := G))) :
    degree B (x::l)=degreeLetter B x*degree B l := rfl
@[simp] lemma degree_append (p q : List (Letter B (G := G))) :
    degree B (p++q)=degree B p*degree B q := by simp [degree,List.prod_append]

 

def FreeCoefficients : Prop :=
  ∀ l : List (Letter B (G := G)),
    l.IsChain (fun x y => tag B x ≠ tag B y) → l ≠ [] →
    (∀ x ∈ l, τ (value B u x)=0) → τ (evaluate B u l)=0

def center : Letter B (G := G) → Letter B (G := G)
  | .inl b => .inl (b-(τ (b:M)) • (1:B))
  | .inr g => .inr g

omit [Group G] in
@[simp] lemma tag_center (x : Letter B (G := G)) : tag B (center B τ x)=tag B x := by
  cases x <;> rfl
@[simp] lemma degreeLetter_center (x : Letter B (G := G)) :
    degreeLetter B (center B τ x)=degreeLetter B x := by cases x <;> rfl
@[simp] lemma degree_center (l : List (Letter B (G := G))) :
    degree B (l.map (center B τ))=degree B l := by simp [degree,List.map_map,Function.comp_def]

lemma center_replacement (p q : List (Letter B (G := G))) (b : B) :
    τ (evaluate B u (p++center B τ (.inl b)::q))=
      τ (evaluate B u (p++(.inl b)::q))-
        τ (b:M)*τ (evaluate B u (p++q)) := by
  simp only [evaluate_append,evaluate_cons,center,value,Subalgebra.coe_sub,
    Subalgebra.coe_smul,Subalgebra.coe_one,mul_sub,sub_mul,mul_smul_comm,
    smul_mul_assoc,one_mul,map_sub,map_smul,smul_eq_mul]

 

lemma center_moment (l : List (Letter B (G := G))) (hl : degree B l ≠ 1)
    (hshort : ∀ k : List (Letter B (G := G)), k.length<l.length → degree B k ≠ 1 →
      τ (evaluate B u k)=0) :
    τ (evaluate B u (l.map (center B τ)))=τ (evaluate B u l) := by
  have h (q p : List (Letter B (G := G)))
      (hn : (p++q).length=l.length) (hd : degree B (p++q) ≠ 1) :
      τ (evaluate B u (p++q.map (center B τ)))=τ (evaluate B u (p++q)) := by
    induction q generalizing p with
    | nil => rfl
    | cons x q ih =>
      have hn' : ((p++[center B τ x])++q).length=l.length := by
        simpa only [List.length_append,List.length_singleton,List.length_cons,List.length_nil,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn
      have hd' : degree B ((p++[center B τ x])++q) ≠ 1 := by
        simpa [mul_assoc] using hd
      have heq := ih (p++[center B τ x]) hn' hd'
      simp only [List.append_assoc,List.singleton_append] at heq
      rw [List.map_cons,heq]
      cases x with
      | inr g => rfl
      | inl b =>
        rw [center_replacement]
        have hs := hshort (p++q) (by simp only [List.length_append,List.length_cons] at hn ⊢; omega)
          (by simpa [degreeLetter] using hd)
        simp only [hs,mul_zero,sub_zero]
  simpa using h l [] (by simp) (by simpa using hl)

 

theorem moment_eq_zero_of_degree_ne_one
    (h1 : τ 1=1) (hu : ∀ g : G, g ≠ 1 → τ (u g)=0)
    (hfree : FreeCoefficients B u τ)
    (l : List (Letter B (G := G))) (hl : degree B l ≠ 1) :
    τ (evaluate B u l)=0 := by
  classical
  suffices h : ∀ N : ℕ, ∀ k : List (Letter B (G := G)), k.length=N →
      degree B k ≠ 1 → τ (evaluate B u k)=0 from h l.length l rfl hl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro k hk hd
    have H (t : List (Letter B (G := G))) (ht : t.length<k.length)
        (hdt : degree B t ≠ 1) : τ (evaluate B u t)=0 :=
      ih t.length (hk ▸ ht) t rfl hdt
    by_cases hone : Sum.inr (1:G) ∈ k
    · obtain ⟨p,q,rfl⟩ := List.mem_iff_append.mp hone
      have hz := H (p++q) (by simp) (by simpa [degreeLetter] using hd)
      simpa [value] using hz
    by_cases halt : k.IsChain (fun x y => tag B x ≠ tag B y)
    · have hkc : τ (evaluate B u (k.map (center B τ)))=0 := by
        apply hfree
        · rw [List.isChain_map]
          simpa only [tag_center] using halt
        · intro hnil
          have hk0 : k=[] := List.map_eq_nil_iff.mp hnil
          exact hd (by simp [hk0])
        · intro x hx
          obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
          cases y with
          | inl b => simp [center,value,map_sub,map_smul,h1]
          | inr g =>
            apply hu
            intro hg
            exact hone (hg ▸ hy)
      rw [center_moment B u τ k hd H] at hkc
      exact hkc
    · rw [List.isChain_iff_forall_rel_of_append_cons_cons] at halt
      push Not at halt
      obtain ⟨a,b,p,q,hk',hab⟩ := halt
      subst k
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          have hz := H (p++Sum.inl (a*b)::q) (by simp)
            (by simpa [degreeLetter,mul_assoc] using hd)
          simpa [value,mul_assoc] using hz
        | inr b => simp [tag] at hab
      | inr a =>
        cases b with
        | inl b => simp [tag] at hab
        | inr b =>
          have hz := H (p++Sum.inr (a*b)::q) (by simp)
            (by simpa [degreeLetter,mul_assoc] using hd)
          simpa [value,map_mul,mul_assoc] using hz

end HochschildFreeMoments
end

end OAI
