import OAI.Analysis.FourierLLogL.Compress.Blocks
/-! # Cost of a coupling of contextual rows -/

open Set Function Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Law Real
variable {A B U V W G Ω Ω' E : Type} [Fintype A] [Fintype B]
  [Fintype U] [Fintype V] [Fintype W] [Fintype G] [Fintype E] [Nonempty E]
  [AddCommGroup G] [Fintype Ω] [Fintype Ω']
  {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}

/-- Context part of a vector of full rows. -/
def ctxt (w : A → V) (X : Ω → I → A) (a : Ω) (i : I) := w (X a i)
def readP (X : Ω → I → A) (i : I) (a : Ω) : A := X a i

/-- Contextual cost of a coupling with tag-sum output and random error ø of alphabet E. -/
def rent (tag : A → G) (w : A → V) (u : E → G) (c : E → ℝ)
    (P : Law Ω) (X : Ω → I → A) (U : Ω → E) :=
  (∑ i, P.Hcond (readP X i) (w ∘ readP X i)) -
    P.Hcond X (fun a => (ans tag X (fun x => u (U x)) a, ctxt w X a)) +
      P.Ex (fun a => c (U a))

def hasRows (p : Law A) (P : Law Ω) (X : Ω → I → A) : Prop :=
  ∀ i, P.send (readP X i) = p

omit [DecidableEq I] in
lemma rent_first {P : Law Ω} {X : Ω → I → A} {p : Law A} (h : hasRows p P X)
    (w : A → V) :
    ∑ i, P.Hcond (readP X i) (w ∘ readP X i) = Fintype.card I * p.Hcond (fun x => x) w := by
  have heq (i : I) :
      P.Hcond (readP X i) (w ∘ readP X i) = p.Hcond (fun x => x) w := by
    rw [← h i,Hcond_send]; rfl
  simp_rw [heq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

omit [Fintype E] [Nonempty E] in
lemma rent_nonneg (tag : A → G) (w : A → V) (u : E → G) (c : E → ℝ)
    (hc : ∀ x, 0 ≤ c x) (P : Law Ω) (X : Ω → I → A) (U : Ω → E) :
    0 ≤ rent tag w u c P X U := by
  refine add_nonneg (sub_nonneg.mpr ?_) (P.Ex_nonneg fun a => hc _)
  refine (P.Hcond_vec_le X _).trans (Finset.sum_le_sum fun i _ => ?_)
  apply Hcond_antitone
  intro a b hh
  exact congrFun (congrArg Prod.snd hh) i

omit [Fintype E] [Nonempty E] in
lemma rent_send (tag : A → G) (w : A → V) (u : E → G) (c : E → ℝ)
    (P : Law Ω) (X : Ω' → I → A) (U : Ω' → E) (b : Ω → Ω') :
    rent tag w u c (P.send b) X U = rent tag w u c P (fun a => X (b a)) (fun a => U (b a)) := by
  unfold rent; simp_rw [Hcond_send,Ex_send]
  rfl

omit [Fintype E] [Nonempty E] in
lemma rent_cont (tag : A → G) (w : A → V) (u : E → G) (c : E → ℝ)
    (X : Ω → I → A) (U : Ω → E) :
    Continuous (fun P : Law Ω => rent tag w u c P X U) :=
  ((continuous_finsetSum _ fun _ _ => continuous_Hcond _ _).sub (continuous_Hcond _ _)).add
    (continuous_Ex _)

/-- Min rent uses r rows. -/
def opt (n : ℕ) (p : Law A) (tag : A → G) (w : A → V) (u : E → G) (c : E → ℝ) :=
  sInf ((fun P : Law (WordSample n A E) => rent tag w u c P Prod.fst Prod.snd) ''
    {P | hasRows p P Prod.fst})

lemma opt_spec (n : ℕ) (p : Law A) (tag : A → G) (w : A → V) (u : E → G) (c : E → ℝ) :
    let C (P : Law (WordSample n A E)) := rent tag w u c P Prod.fst Prod.snd
    (∃ P : Law (WordSample n A E), hasRows p P Prod.fst ∧ C P = opt n p tag w u c) ∧
    ∀ P : Law (WordSample n A E), hasRows p P Prod.fst → opt n p tag w u c ≤ C P := by
  classical
  intro C
  let s := {P : Law (WordSample n A E) | hasRows p P Prod.fst}
  have hs : IsCompact s := by
    apply IsClosed.isCompact
    have heq : s = ⋂ i, {P | P.send (readP Prod.fst i) = p} := by ext; simp [s,hasRows]
    rw [heq]
    exact isClosed_iInter fun i => isClosed_eq (continuous_send _) continuous_const
  let Q := pack fun _ : Fin n => p
  obtain ⟨e⟩ := (inferInstance : Nonempty E)
  have h1 : s.Nonempty := by
    refine ⟨Q.send (fun x => (x,e)),fun i => ?_⟩
    rw [send_send]; exact marginalPack _ i
  have hh := hs.image (rent_cont tag w u c Prod.fst Prod.snd)
  have H1 : (C '' s).Nonempty := h1.image _
  exact ⟨hh.sInf_mem H1,fun P h => csInf_le hh.bddBelow ⟨_, h,rfl⟩⟩

lemma opt_le_rent (tag : A → G) (w : A → V) (u : E → G) (c : E → ℝ)
    (p : Law A) (P : Law Ω) (X : Ω → Fin n → A) (U : Ω → E) (h : hasRows p P X) :
    opt n p tag w u c ≤ rent tag w u c P X U := by
  let Q := P.send (fun a => (X a,U a))
  have hh := (opt_spec n p tag w u c).2 Q (by
    intro i
    dsimp only [Q]; rw [send_send]; exact h i)
  dsimp only [Q] at hh
  rw [rent_send] at hh
  exact hh

lemma opt_nonneg (n : ℕ) (p : Law A) (tag : A → G) (w : A → V) (u : E → G) (c : E → ℝ)
    (hc : ∀ x, 0 ≤ c x) : 0 ≤ opt n p tag w u c := by
  obtain ⟨P,_,he⟩ := (opt_spec n p tag w u c).1
  rw [← he]
  exact rent_nonneg tag w u c hc P _ _


lemma Hcond_function (P : Law Ω) (X : Ω → A) (W : A → V) :
    P.Hcond X (fun x => W (X x)) = P.H X - P.H (fun x => W (X x)) := by
  unfold Hcond
  congr 1
  apply H_partition
  simp [Prod.mk.injEq]; grind

/-- Chain rule for deterministic reduction f(X). -/
lemma Hcond_reduce (P : Law Ω) (X : Ω → A) (W : Ω → V) (f : A → B) :
    P.Hcond X W = P.Hcond X (fun x => (f (X x),W x)) + P.Hcond (fun x => f (X x)) W := by
  rw [← Hcond_chain P X (fun x => f (X x)) W]
  unfold Hcond
  congr 1
  refine H_partition _ fun a b => ?_
  simp only [Prod.mk.injEq]
  constructor <;> grind

omit [Fintype E] [Nonempty E] in
/-- Improving contexts, for the same full rows and tag, reduces the rent. -/
lemma rent_antitone (tag : A → G) (w : A → V) (w' : A → W) (u : E → G) (c : E → ℝ)
    (p : V → W) (h : w' = p ∘ w)
    (P : Law Ω) (X : Ω → I → A) (U : Ω → E) :
    rent tag w u c P X U ≤ rent tag w' u c P X U := by
  subst w'
  let Y := ans tag X (fun x => u (U x))
  let W₁ := ctxt w X
  let W₂ := ctxt (p ∘ w) X
  have h (i : I) : P.Hcond (readP X i) ((p ∘ w) ∘ readP X i) =
      P.Hcond (readP X i) (w ∘ readP X i) + P.Hcond (readP W₁ i) (readP W₂ i) := by
    have h1 := Hcond_function P (readP X i) (p ∘ w)
    have h2 := Hcond_function P (readP X i) w
    have h3 := Hcond_function P (readP W₁ i) p
    change P.Hcond (readP X i) (fun x => p (w ((readP X i) x))) = _
    dsimp only [comp_apply] at h1
    rw [h1]
    change _ = P.Hcond (readP X i) (fun x => w ((readP X i) x)) +
      P.Hcond (readP W₁ i) (fun x => p (readP W₁ i x))
    rw [h2,h3]; simp only [W₁]; unfold readP ctxt; ring
  let vmap (x : I → A) (i : I) := w (x i)
  let Z₁ (x : Ω) := (Y x,W₁ x)
  let Z₂ (x : Ω) := (Y x,W₂ x)
  have hz : P.Hcond X Z₂ = P.Hcond X Z₁ + P.Hcond W₁ Z₂ := by
    nth_rw 1 [Hcond_reduce P X Z₂ vmap]
    have H : P.Hcond X (fun x => (vmap (X x), Z₂ x)) = P.Hcond X Z₁ := by
      apply Hcond_right_partition
      intro a b
      simp only [Z₁,Z₂,W₁,W₂,ctxt,vmap,Prod.mk.injEq,funext_iff,comp_apply]
      constructor
      · tauto
      · rintro ⟨hh,hx⟩
        simp [hx,hh]
    rw [H]; rfl
  have H : P.Hcond W₁ Z₂ ≤ ∑ i, P.Hcond (readP W₁ i) (readP W₂ i) := by
    refine (P.Hcond_vec_le W₁ Z₂).trans (Finset.sum_le_sum fun i _ => ?_)
    exact Hcond_antitone P _ fun _ _ hh => congrFun (congrArg Prod.snd hh) i
  unfold rent
  refine add_le_add_left ?_ _
  change _ - P.Hcond X Z₁ ≤ _ - P.Hcond X Z₂
  rw [hz]
  simp_rw [h,Finset.sum_add_distrib]
  linarith

end FourierLLogL.Compress

end OAI
