import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.YoungModules

namespace OAI

noncomputable section

namespace Foulkes.Young
open Finset

section Counts
variable {D A B : Type*} [Fintype D] [Fintype A] [Fintype B]

def counts (f : D → A) (a : A) : ℕ := Nat.card {i // f i = a}

omit [Fintype D] [Fintype A] in
lemma counts_reindex (f : D → A) (σ : Equiv.Perm D) : counts (f ∘ σ) = counts f := by
  funext a
  exact Nat.card_congr (Equiv.subtypeEquiv σ (fun i => Iff.rfl))

omit [Fintype A] in
lemma exists_perm_of_counts_eq (f g : D → A) (h : counts f = counts g) :
    ∃ σ : Equiv.Perm D, f ∘ σ = g := by
  classical
  let e (a : A) : {i // g i = a} ≃ {i // f i = a} :=
    Fintype.equivOfCardEq (by simpa [counts, Nat.card_eq_fintype_card] using (congrFun h a).symm)
  let σ : Equiv.Perm D := (Equiv.sigmaFiberEquiv g).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f))
  refine ⟨σ, ?_⟩
  funext i
  exact (e (g i) ⟨i,rfl⟩).property

lemma counts_total (f : D → A) : ∑ a, counts f a = Fintype.card D := by
  classical
  simp only [counts, Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

omit [Fintype A] in
lemma counts_pair_fst (f : D → A) (g : D → B) (a : A) :
    ∑ b, counts (fun i => (f i,g i)) (a,b) = counts f a := by
  classical
  let he (b : B) : {z : {i // f i = a} // g z.val = b} ≃
      {i // (f i,g i) = (a,b)} := {
    toFun z := ⟨z.val.val, Prod.ext z.val.property z.property⟩
    invFun z := ⟨⟨z.val, congrArg Prod.fst z.property⟩, congrArg Prod.snd z.property⟩
    left_inv z := rfl
    right_inv z := rfl }
  have hh := counts_total (fun z : {i // f i = a} => g z.val)
  simp only [counts, Nat.card_eq_fintype_card] at hh ⊢
  rw [← hh]
  exact Finset.sum_congr rfl (fun b hb => (Fintype.card_congr (he b)).symm)

omit [Fintype B] in
lemma counts_pair_snd (f : D → A) (g : D → B) (b : B) :
    ∑ a, counts (fun i => (f i,g i)) (a,b) = counts g b := by
  classical
  let he (a : A) : {z : {i // g i = b} // f z.val = a} ≃
      {i // (f i,g i) = (a,b)} := {
    toFun z := ⟨z.val.val, Prod.ext z.property z.val.property⟩
    invFun z := ⟨⟨z.val, congrArg Prod.snd z.property⟩, congrArg Prod.fst z.property⟩
    left_inv z := rfl
    right_inv z := rfl }
  have hh := counts_total (fun z : {i // g i = b} => f z.val)
  simp only [counts, Nat.card_eq_fintype_card] at hh ⊢
  rw [← hh]
  exact Finset.sum_congr rfl (fun a ha => (Fintype.card_congr (he a)).symm)

lemma exists_coloring (mu : A → ℕ) (hmu : ∑ a, mu a = Fintype.card D) :
    ∃ f : D → A, counts f = mu := by
  classical
  let e : D ≃ (Σ a, Fin (mu a)) := Fintype.equivOfCardEq (by simp [hmu])
  let f : D → A := fun i => (e i).1
  let ea (a : A) : {t : (Σ a, Fin (mu a)) // t.1 = a} ≃ Fin (mu a) := {
    toFun t := t.property ▸ t.val.2
    invFun j := ⟨⟨a,j⟩,rfl⟩
    left_inv t := by rcases t with ⟨⟨b,j⟩,h⟩; dsimp at h; subst b; rfl
    right_inv j := rfl }
  refine ⟨f, funext fun a => ?_⟩
  have hcard := Nat.card_congr ((Equiv.subtypeEquiv e (fun i => Iff.rfl)).trans (ea a))
  simpa [counts, f] using hcard

end Counts

def Coloring (D A : Type*) [Fintype D] (mu : A → ℕ) :=
  {f : D → A // counts f = mu}

instance {D A : Type*} [Fintype D] [Fintype A] (mu : A → ℕ) :
    Fintype (Coloring D A mu) := by
  classical
  unfold Coloring
  infer_instance

instance coloringAction {D A : Type*} [Fintype D] [Fintype A] (mu : A → ℕ) :
    MulAction (Equiv.Perm D) (Coloring D A mu) where
  smul σ f := ⟨f.val ∘ σ.symm, (counts_reindex f.val σ.symm).trans f.property⟩
  one_smul f := by apply Subtype.ext; rfl
  mul_smul σ τ f := by apply Subtype.ext; rfl

@[simp] lemma coloring_smul_apply {D A : Type*} [Fintype D] [Fintype A] (mu : A → ℕ)
    (σ : Equiv.Perm D) (f : Coloring D A mu) (i : D) :
    (σ • f).val i = f.val (σ.symm i) := rfl

def Contingency {A B : Type*} [Fintype A] [Fintype B] (mu : A → ℕ) (nu : B → ℕ) :=
  {M : Matrix A B ℕ // (∀ a, ∑ b, M a b = mu a) ∧ (∀ b, ∑ a, M a b = nu b)}

section ColorPairs
variable {D A B : Type*} [Fintype D] [Fintype A] [Fintype B]
    (mu : A → ℕ) (nu : B → ℕ)

def intersectionCounts (p : Coloring D A mu × Coloring D B nu) : Contingency mu nu :=
  ⟨fun a b => counts (fun i => (p.1.val i,p.2.val i)) (a,b),
    (fun a => (counts_pair_fst p.1.val p.2.val a).trans (congrFun p.1.property a)),
    fun b => (counts_pair_snd p.1.val p.2.val b).trans (congrFun p.2.property b)⟩

lemma intersectionCounts_smul (σ : Equiv.Perm D)
    (p : Coloring D A mu × Coloring D B nu) :
    intersectionCounts mu nu (σ • p) = intersectionCounts mu nu p := by
  apply Subtype.ext
  ext a b
  exact congrFun (counts_reindex (fun i => (p.1.val i,p.2.val i)) σ.symm) (a,b)

lemma orbit_iff_intersectionCounts (p q : Coloring D A mu × Coloring D B nu) :
    MulAction.orbitRel (Equiv.Perm D) _ p q ↔
      intersectionCounts mu nu p = intersectionCounts mu nu q := by
  constructor
  · rintro ⟨σ,rfl⟩
    exact intersectionCounts_smul mu nu σ q
  · intro h
    have he : counts (fun i => (q.1.val i,q.2.val i)) =
        counts (fun i => (p.1.val i,p.2.val i)) := by
      funext ab
      exact (congrFun (congrFun (congrArg Subtype.val h) ab.1) ab.2).symm
    obtain ⟨σ,hσ⟩ := exists_perm_of_counts_eq _ _ he
    refine ⟨σ.symm, ?_⟩
    apply Prod.ext
    · apply Subtype.ext; funext i; exact congrArg Prod.fst (congrFun hσ i)
    · apply Subtype.ext; funext i; exact congrArg Prod.snd (congrFun hσ i)

lemma intersectionCounts_surjective (hmu : ∑ a, mu a = Fintype.card D) :
    Function.Surjective (intersectionCounts (D := D) mu nu) := by
  intro M
  have ht : ∑ ab : A × B, M.val ab.1 ab.2 = Fintype.card D := by
    rw [Fintype.sum_prod_type]
    simp only [M.property.1]
    exact hmu
  obtain ⟨f,hf⟩ := exists_coloring (D := D) (fun ab : A × B => M.val ab.1 ab.2) ht
  have ha : counts (fun i => (f i).1) = mu := by
    funext a
    rw [← counts_pair_fst (fun i => (f i).1) (fun i => (f i).2) a]
    simpa only [Prod.eta, hf] using M.property.1 a
  have hb : counts (fun i => (f i).2) = nu := by
    funext b
    rw [← counts_pair_snd (fun i => (f i).1) (fun i => (f i).2) b]
    simpa only [Prod.eta, hf] using M.property.2 b
  refine ⟨(⟨fun i => (f i).1,ha⟩,⟨fun i => (f i).2,hb⟩), ?_⟩
  apply Subtype.ext
  ext a b
  exact congrFun hf (a,b)

def orbitContingencyEquiv (hmu : ∑ a, mu a = Fintype.card D) :
    MulAction.orbitRel.Quotient (Equiv.Perm D) (Coloring D A mu × Coloring D B nu) ≃
      Contingency mu nu := by
  let f := Quotient.lift (intersectionCounts (D := D) mu nu)
    (fun p q h => (orbit_iff_intersectionCounts mu nu p q).mp h)
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    induction p using Quotient.inductionOn with | _ p =>
      induction q using Quotient.inductionOn with | _ q =>
        exact Quotient.sound ((orbit_iff_intersectionCounts mu nu p q).mpr h)
  · intro M
    obtain ⟨p,hp⟩ := intersectionCounts_surjective mu nu hmu M
    exact ⟨Quotient.mk _ p,hp⟩

end ColorPairs
end Foulkes.Young

namespace Foulkes.Young
open Module Finset

theorem young_hom_finrank {K D A B : Type*} [Field K]
    [Fintype D] [Fintype A] [Fintype B] (mu : A → ℕ) (nu : B → ℕ)
    (hnu : ∑ b, nu b = Fintype.card D) :
    finrank K ((permRep K (Equiv.Perm D) (Coloring D A mu)).IntertwiningMap
      (permRep K (Equiv.Perm D) (Coloring D B nu))) = Nat.card (Contingency nu mu) := by
  rw [perm_hom_finrank]
  exact Nat.card_congr (orbitContingencyEquiv nu mu hnu)
end Foulkes.Young

end

end OAI
