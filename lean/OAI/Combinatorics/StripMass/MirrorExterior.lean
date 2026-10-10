import Mathlib
import OAI.Combinatorics.StripMass.PhaseAlgebra
import OAI.Combinatorics.StripMass.TriplePatch

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def mirrorInterface : Fin 6 → Fin n ⊕ Fin n :=
  ![.inl s.c,.inl s.b,.inl s.a,.inr s.c,.inr s.b,.inr s.a]

def mirrorActive (p q : Pairing n) : Fin 6 → Prop :=
  ![p.Occupied s.c,p.Occupied s.b,p.Occupied s.a,
    q.Occupied s.c,q.Occupied s.b,q.Occupied s.a]

def mirrorExterior (p q : Pairing n) : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → Prop
  | .inl i,.inl j => p.Adj i j
  | .inl i,.inr j | .inr j,.inl i => i=j ∧ i≠s.c ∧ i≠s.b ∧ i≠s.a ∧ q.Occupied i
  | .inr _,.inr _ => False

def MirrorOutside (p q : Pairing n) : Prop :=
  ∀ i, i≠s.c → i≠s.b → i≠s.a → (p.Occupied i ↔ q.Occupied i)

def mirrorAttached (p q : Pairing n) (t : ThreeBox.Config) :=
  Graph.Attached.wiring (s.mirrorWiring p t) s.mirrorBoundary q.Occupied

def mirrorPatch (p q : Pairing n) (t : ThreeBox.Config) :=
  Patch.glued (ThreeBox.Adj t) (s.mirrorExterior p q) ThreeBox.boundary s.mirrorInterface (s.mirrorActive p q)

def mirrorExteriorEquiv : ((Fin n ⊕ Fin 12) ⊕ Fin n) ≃ (Fin 12 ⊕ (Fin n ⊕ Fin n)) where
  toFun
    | .inl (.inl i) => .inr (.inl i)
    | .inl (.inr v) => .inl v
    | .inr i => .inr (.inr i)
  invFun
    | .inl v => .inl (.inr v)
    | .inr (.inl i) => .inl (.inl i)
    | .inr (.inr i) => .inr i
  left_inv := by rintro ((i|v)|i) <;> rfl
  right_inv := by rintro (v|(i|i)) <;> rfl

lemma mirror_boundary_old (i j : Fin n) :
    ((.inl i : Fin n ⊕ Fin 12)=s.mirrorBoundary j) ↔
      i=j ∧ i≠s.c ∧ i≠s.b ∧ i≠s.a := by
  by_cases ha : j=s.c <;> by_cases hb : j=s.b <;> by_cases hc : j=s.a <;>
    simp_all [mirrorBoundary]

lemma mirror_boundary_new (v : Fin 12) (j : Fin n) :
    ((.inr v : Fin n ⊕ Fin 12)=s.mirrorBoundary j) ↔
      (j=s.c ∧ v=6) ∨ (j=s.b ∧ v=10) ∨ (j=s.a ∧ v=11) := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : j=s.c <;> by_cases hb : j=s.b <;> by_cases hc : j=s.a <;>
    simp_all [mirrorBoundary]

lemma mirror_interface_old (p q : Pairing n) (v : Fin 12) (i : Fin n) :
    (∃ k, s.mirrorActive p q k ∧ v=ThreeBox.boundary k ∧ (.inl i : Fin n ⊕ Fin n)=s.mirrorInterface k) ↔
      (i=s.c ∧ v=4 ∧ p.Occupied s.c) ∨
      (i=s.b ∧ v=0 ∧ p.Occupied s.b) ∨ (i=s.a ∧ v=1 ∧ p.Occupied s.a) := by
  simp only [Fin.exists_fin_succ,mirrorInterface,mirrorActive,ThreeBox.boundary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Sum.inl.injEq,Sum.inl_ne_inr,and_false,or_false,Fin.exists_fin_zero]
  itauto

lemma mirror_interface_new (p q : Pairing n) (v : Fin 12) (i : Fin n) :
    (∃ k, s.mirrorActive p q k ∧ v=ThreeBox.boundary k ∧ (.inr i : Fin n ⊕ Fin n)=s.mirrorInterface k) ↔
      ((i=s.c ∧ v=6) ∨ (i=s.b ∧ v=10) ∨ (i=s.a ∧ v=11)) ∧ q.Occupied i := by
  simp only [Fin.exists_fin_succ,mirrorInterface,mirrorActive,ThreeBox.boundary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Sum.inr.injEq,Sum.inr_ne_inl,and_false,false_or,or_false,Fin.exists_fin_zero]
  constructor
  · rintro (⟨h,hv,hi⟩ | ⟨h,hv,hi⟩ | ⟨h,hv,hi⟩) <;> subst i
    · exact ⟨Or.inl ⟨rfl,hv⟩,h⟩
    · exact ⟨Or.inr (Or.inl ⟨rfl,hv⟩),h⟩
    · exact ⟨Or.inr (Or.inr ⟨rfl,hv⟩),h⟩
  · rintro ⟨(⟨rfl,hv⟩|⟨rfl,hv⟩|⟨rfl,hv⟩),h⟩
    · exact Or.inl ⟨h,hv,rfl⟩
    · exact Or.inr (Or.inl ⟨h,hv,rfl⟩)
    · exact Or.inr (Or.inr ⟨h,hv,rfl⟩)

lemma mirror_exterior_edge (p q : Pairing n) (t : ThreeBox.Config)
    (v w : (Fin n ⊕ Fin 12) ⊕ Fin n) :
    s.mirrorAttached p q t v w ↔ s.mirrorPatch p q t (mirrorExteriorEquiv v) (mirrorExteriorEquiv w) := by
  rcases v with (i|v)|i <;> rcases w with (j|w)|j
  all_goals dsimp only [mirrorAttached,Graph.Attached.wiring,mirrorPatch,Patch.glued,mirrorExteriorEquiv,Equiv.coe_fn_mk]
  · rfl
  · simpa only [mirrorWiring,and_comm,and_left_comm,and_assoc] using (s.mirror_interface_old p q w i).symm
  · rw [s.mirror_boundary_old]
    change ((i=j ∧ i≠s.c ∧ i≠s.b ∧ i≠s.a) ∧ q.Occupied j) ↔
      i=j ∧ i≠s.c ∧ i≠s.b ∧ i≠s.a ∧ q.Occupied i
    constructor
    · rintro ⟨⟨rfl,ha,hb,hc⟩,hq⟩; exact ⟨rfl,ha,hb,hc,hq⟩
    · rintro ⟨rfl,ha,hb,hc,hq⟩; exact ⟨⟨rfl,ha,hb,hc⟩,hq⟩
  · exact (s.mirror_interface_old p q v j).symm
  · rfl
  · rw [s.mirror_boundary_new]
    exact (s.mirror_interface_new p q v j).symm
  · rw [s.mirror_boundary_old]
    change ((j=i ∧ j≠s.c ∧ j≠s.b ∧ j≠s.a) ∧ q.Occupied i) ↔
      j=i ∧ j≠s.c ∧ j≠s.b ∧ j≠s.a ∧ q.Occupied j
    constructor
    · rintro ⟨⟨rfl,ha,hb,hc⟩,hq⟩; exact ⟨rfl,ha,hb,hc,hq⟩
    · rintro ⟨rfl,ha,hb,hc,hq⟩; exact ⟨⟨rfl,ha,hb,hc⟩,hq⟩
  · rw [s.mirror_boundary_new]
    simpa only [and_comm,and_left_comm,and_assoc] using (s.mirror_interface_new p q w i).symm
  · rfl

end TriplePosition
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

lemma reverseSlots_involutive : Function.Involutive reverseSlots := by intro i; fin_cases i <;> rfl

@[simp] lemma reverseSlots_twice (i : Fin 6) : reverseSlots (reverseSlots i)=i := reverseSlots_involutive i

def reverseEquiv : Fin 6 ≃ Fin 6 :=
  ⟨reverseSlots,reverseSlots,reverseSlots_involutive,reverseSlots_involutive⟩

lemma support_mirror (k : Fin 51) (i : Fin 6) :
    boundarySupport (diagram (mirrorIndex k)) i ↔
      boundarySupport (diagram k) (reverseSlots i) := by
  unfold boundarySupport
  simp only [diagram_mirror]
  exact reverseEquiv.surjective.exists.symm

lemma exterior_mirror {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (k : Fin 51) :
    diagramExterior (diagram k) s (b∘reverseSlots) (active∘reverseSlots) =
      diagramExterior (diagram (mirrorIndex k)) s b active := by
  funext x y
  apply propext
  unfold diagramExterior
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨i,j,hi,hj,h,he,hf⟩
    refine ⟨reverseSlots i,reverseSlots j,hi,hj,?_,he,hf⟩
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr ((diagram_mirror k _ _).mpr (by simpa only [reverseSlots_twice] using h))
  · rintro ⟨i,j,hi,hj,h,he,hf⟩
    refine ⟨reverseSlots i,reverseSlots j,?_,?_,?_,?_,?_⟩
    · simpa only [Function.comp_apply,reverseSlots_twice] using hi
    · simpa only [Function.comp_apply,reverseSlots_twice] using hj
    · exact h.elim (fun he => Or.inl (congrArg _ he)) (fun hh => Or.inr ((diagram_mirror k i j).mp hh))
    · simpa only [Function.comp_apply,reverseSlots_twice] using he
    · simpa only [Function.comp_apply,reverseSlots_twice] using hf

lemma exteriorTest_mirror {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (out : B → Prop) (test : (B → B → Prop) → Prop) (k : Fin 51) :
    exteriorTest s (b∘reverseSlots) (active∘reverseSlots) out test k ↔
      exteriorTest s b active out test (mirrorIndex k) := by
  unfold exteriorTest
  rw [exterior_mirror]
  refine and_congr ?_ Iff.rfl
  simp only [support_mirror,Function.comp_apply]
  constructor
  · intro h i
    simpa only [reverseSlots_twice] using h (reverseSlots i)
  · intro h i
    simpa only [reverseSlots_twice] using h (reverseSlots i)

end
end CriticalStrip.Diagram.ThreeBox

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def mirrorExteriorPredicate (p q : Pairing n) (k : Fin 51) : Prop :=
  s.MirrorOutside p q ∧ ThreeBox.exteriorTest (s.mirrorExterior p q) s.mirrorInterface (s.mirrorActive p q)
    (output q) (reachTest q) k

def mirrorPatchEquiv (p q : Pairing n) (t : ThreeBox.Config) :
    Graph.BoundaryEquiv (s.mirrorAttached p q t) (s.mirrorPatch p q t) Sum.inr
      (fun i => .inr (.inr i)) :=
  Graph.BoundaryEquiv.ofEquiv mirrorExteriorEquiv (s.mirror_exterior_edge p q t) (fun _ => rfl)

lemma mirror_active_iff (p q : Pairing n) (t : ThreeBox.Config) :
    (∀ i, s.mirrorActive p q i ↔ ThreeBox.boundaryOccupied t i) ↔
      (p.Occupied s.c ↔ t.2.1.Occupied 0) ∧
      (p.Occupied s.b ↔ t.1.Occupied 0) ∧ (p.Occupied s.a ↔ t.1.Occupied 1) ∧
      (q.Occupied s.c ↔ t.2.1.Occupied 2) ∧
      (q.Occupied s.b ↔ t.2.2.Occupied 2) ∧ (q.Occupied s.a ↔ t.2.2.Occupied 3) := by
  simp [Fin.forall_fin_succ,mirrorActive,ThreeBox.boundaryOccupied,ThreeBox.boundary,
    ThreeBox.atRow,ThreeBox.row,ThreeBox.port]

lemma mirror_compatible_support_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.Compatible p (s.leftCircuit t) ∧ (∀ i, q.Occupied i ↔ s.mirrorSupport p t i) ↔
      s.MirrorOutside p q ∧ ThreeBox.Compatible t ∧
        (∀ i, s.mirrorActive p q i ↔ ThreeBox.boundaryOccupied t i) := by
  rw [s.mirror_compatible_iff,s.mirror_active_iff]
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  constructor
  · rintro ⟨⟨hc,ha,hb,hc'⟩,hs⟩
    refine ⟨?_,hc,ha,hb,hc',?_,?_,?_⟩
    · intro i hia hib hic
      simpa only [mirrorSupport,ite_eq_right hia,ite_eq_right hib,ite_eq_right hic] using (hs i).symm
    · simpa [mirrorSupport] using hs s.c
    · simpa [mirrorSupport,s.ab,s.bc,s.ac,s.ab.symm,s.bc.symm,s.ac.symm] using hs s.b
    · simpa [mirrorSupport,s.ab,s.bc,s.ac,s.ab.symm,s.bc.symm,s.ac.symm] using hs s.a
  · rintro ⟨ho,hc,ha,hb,hc',hqa,hqb,hqc⟩
    refine ⟨⟨hc,ha,hb,hc'⟩,?_⟩
    intro i
    by_cases hia : i=s.c
    · subst i; simpa [mirrorSupport] using hqa
    · by_cases hib : i=s.b
      · subst i; simpa [mirrorSupport,hia] using hqb
      · by_cases hic : i=s.a
        · subst i; simpa [mirrorSupport,hia,hib] using hqc
        · simpa only [mirrorSupport,ite_eq_right hia,ite_eq_right hib,ite_eq_right hic] using (ho i hia hib hic).symm

lemma mirror_patchTest_realizes (p q : Pairing n) (t : ThreeBox.Config) :
    ThreeBox.patchTest (s.mirrorExterior p q) s.mirrorInterface (s.mirrorActive p q) (output q) (reachTest q) t ↔
      ThreeBox.Compatible t ∧ (∀ i, s.mirrorActive p q i ↔ ThreeBox.boundaryOccupied t i) ∧
        GraphRealizes (s.mirrorPatch p q t) (fun i => .inr (.inr i)) q := by
  unfold ThreeBox.patchTest
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  constructor
  · rintro ⟨hd,hr⟩
    refine ⟨?_,hr⟩
    intro v w he
    obtain ⟨(x|(i|i)),hi,h⟩ := hd v w he
    · exact hi.elim
    · exact hi.elim
    · exact ⟨i,hi,h⟩
  · intro h
    refine ⟨?_,h.reach⟩
    intro v w he
    obtain ⟨i,hi,hr⟩ := h.no_loop v w he
    exact ⟨.inr (.inr i),hi,hr⟩

lemma mirror_eval_patch_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.leftCircuit t)=some q ↔
      s.MirrorOutside p q ∧ ThreeBox.patchTest (s.mirrorExterior p q) s.mirrorInterface (s.mirrorActive p q)
        (output q) (reachTest q) t := by
  rw [s.mirror_eval_iff,s.mirror_patchTest_realizes]
  constructor
  · rintro ⟨hc,hr⟩
    have hs : ∀ i, q.Occupied i ↔ s.mirrorSupport p t i := fun i =>
      (hr.boundary_used_iff s.mirror_boundary_injective i).symm.trans (s.mirror_boundary_used p t i)
    obtain ⟨ho,hc',ha⟩ := (s.mirror_compatible_support_iff p q t).mp ⟨hc,hs⟩
    refine ⟨ho,hc',ha,?_⟩
    apply (s.mirrorPatchEquiv p q t).realizes_iff.mp
    exact (Graph.Attached.contraction (s.mirrorWiring p t) s.mirrorBoundary q.Occupied
      (fun i => (hs i).trans (s.mirror_boundary_used p t i).symm) s.mirror_boundary_injective).realizes_inv hr
  · rintro ⟨ho,hc,ha,hr⟩
    obtain ⟨hc',hs⟩ := (s.mirror_compatible_support_iff p q t).mpr ⟨ho,hc,ha⟩
    refine ⟨hc',?_⟩
    apply (Graph.Attached.contraction (s.mirrorWiring p t) s.mirrorBoundary q.Occupied
      (fun i => (hs i).trans (s.mirror_boundary_used p t i).symm) s.mirror_boundary_injective).realizes
    exact (s.mirrorPatchEquiv p q t).realizes_iff.mpr hr

lemma mirror_eval_profile_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.leftCircuit t)=some q ↔
      ∃ k, ThreeBox.profile t=some k ∧ s.mirrorExteriorPredicate p q k := by
  rw [s.mirror_eval_patch_iff,ThreeBox.patchTest_iff]
  unfold mirrorExteriorPredicate
  constructor
  · rintro ⟨ho,k,hk,hp⟩; exact ⟨k,hk,ho,hp⟩
  · rintro ⟨k,hk,ho,hp⟩; exact ⟨ho,k,hk,hp⟩

end TriplePosition
end

 

 

noncomputable section
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

lemma mirror_interface : s.mirrorInterface=s.interface ∘ ThreeBox.reverseSlots := by
  funext i; fin_cases i <;> rfl

lemma mirror_active (p q : Pairing n) :
    s.mirrorActive p q=s.active p q ∘ ThreeBox.reverseSlots := by
  funext i; fin_cases i <;> rfl

lemma mirror_exterior (p q : Pairing n) : s.mirrorExterior p q=s.exterior p q := by
  funext x y
  rcases x with x|x <;> rcases y with y|y
  all_goals simp only [mirrorExterior,exterior]
  all_goals apply propext
  all_goals itauto

lemma mirror_outside (p q : Pairing n) : s.MirrorOutside p q ↔ s.Outside p q := by
  unfold MirrorOutside Outside
  constructor <;> intro h i ha hb hc
  · exact h i hc hb ha
  · exact h i hc hb ha

lemma mirror_predicate (p q : Pairing n) (k : Fin 51) :
    s.mirrorExteriorPredicate p q k ↔ s.exteriorPredicate p q (ThreeBox.mirrorIndex k) := by
  unfold mirrorExteriorPredicate exteriorPredicate
  rw [s.mirror_outside,s.mirror_interface,s.mirror_active,s.mirror_exterior]
  exact and_congr_right fun _ => ThreeBox.exteriorTest_mirror _ _ _ _ _ k

end TriplePosition

 

 

open scoped Classical
open Finset

variable {K : Type*} [CommRing K] {n : ℕ}

def tripleCircuit (a b : Position n) (t : ThreeBox.Config) : Circuit n :=
  .snoc (.snoc (.snoc .nil (a.gate t.1)) (b.gate t.2.1)) (a.gate t.2.2)

def tripleProgram (a b : Position n) (w₀ w₁ w₂ : Weights K) : Program n K :=
  .snoc (.snoc (.snoc .nil a w₀) b w₁) a w₂

lemma triple_expansion (a b : Position n) (w₀ w₁ w₂ : Weights K) (p q : Pairing n) :
    (localR a w₂ * localR b w₁ * localR a w₀) q p =
      ∑ t : ThreeBox.Config, if Circuit.eval p (tripleCircuit a b t)=some q
        then w₀.tile t.1*w₁.tile t.2.1*w₂.tile t.2.2 else 0 := by
  have h := (tripleProgram a b w₀ w₁ w₂).matrix_apply q p
  simp only [tripleProgram,Program.matrix,mul_one] at h
  rw [Matrix.mul_assoc]
  rw [h]
  change (∑ x : ((PUnit × Tile) × Tile) × Tile, _) = ∑ t : Tile × (Tile × Tile), _
  simp only [Fintype.sum_prod_type,Fintype.sum_unique,Program.weight,Program.circuit,
    one_mul,tripleCircuit]
  rfl

namespace ThreeBox

def mirrorConfig : Config ≃ Config :=
  Equiv.prodCongr Tile.mirrorEquiv (Equiv.prodCongr Tile.mirrorEquiv Tile.mirrorEquiv)

lemma config_sum_mirror (f : Config → K) : ∑ t, f t = ∑ t, f (mirrorConfig t) :=
  (Equiv.sum_comp mirrorConfig f).symm

end ThreeBox

lemma triple_expansion_mirror (a b : Position n) (w₀ w₁ w₂ : Weights K) (p q : Pairing n) :
    (localR a w₂ * localR b w₁ * localR a w₀) q p =
      ∑ t : ThreeBox.Config, if Circuit.eval p (tripleCircuit a b (ThreeBox.mirrorConfig t))=some q
        then w₀.tile t.1*w₁.tile t.2.1*w₂.tile t.2.2 else 0 := by
  rw [triple_expansion,ThreeBox.config_sum_mirror]
  apply sum_congr rfl
  intro t _
  simp only [ThreeBox.mirrorConfig, Equiv.prodCongr, Tile.mirrorEquiv]
  change (if Circuit.eval p (tripleCircuit a b (ThreeBox.mirrorConfig t))=some q then
      w₀.tile t.1.mirror*w₁.tile t.2.1.mirror*w₂.tile t.2.2.mirror else 0) = _
  simp only [Tile.weight_mirror]
  rfl

end

 

 

noncomputable section
open scoped Classical
namespace TriplePosition
variable {n m : ℕ} (s : TriplePosition n)

 

theorem torus_yang_baxter (z w : SpectralField m)
    (hz : z≠0) (hw : w≠0) (hLz : torusL z≠0) (hLw : torusL w≠0)
    (hLzw : torusL (z*w)≠0) :
    localR s.right (torusWeights w) * localR s.left (torusWeights (z*w)) *
        localR s.right (torusWeights z) =
      localR s.left (torusWeights z) * localR s.right (torusWeights (z*w)) *
        localR s.left (torusWeights w) := by
  ext q p
  rw [triple_expansion,triple_expansion_mirror]
  change (∑ t : ThreeBox.Config, if Circuit.eval p (s.rightCircuit t)=some q
    then (torusWeights z).tile t.1*(torusWeights (z*w)).tile t.2.1*(torusWeights w).tile t.2.2 else 0) =
    (∑ t : ThreeBox.Config, if Circuit.eval p (s.leftCircuit t)=some q
    then (torusWeights w).tile t.1*(torusWeights (z*w)).tile t.2.1*(torusWeights z).tile t.2.2 else 0)
  simp_rw [s.eval_profile_iff,s.mirror_eval_profile_iff,s.mirror_predicate]
  exact ThreeBox.braid_partition z w hz hw hLz hLw hLzw (s.exteriorPredicate p q)

end TriplePosition

 

 

namespace Position
variable {n : ℕ}

def Disjoint (a b : Position n) : Prop :=
  a.left≠b.left ∧ a.left≠b.right ∧ a.right≠b.left ∧ a.right≠b.right

lemma disjoint_symm {a b : Position n} (h : a.Disjoint b) : b.Disjoint a :=
  ⟨h.1.symm,h.2.2.1.symm,h.2.1.symm,h.2.2.2.symm⟩

def pairCircuit (a b : Position n) (t u : Tile) : Circuit n :=
  .snoc (.snoc .nil (a.gate t)) (b.gate u)

def exchangeEquiv : ((Fin n ⊕ Fin 4) ⊕ Fin 4) ≃ ((Fin n ⊕ Fin 4) ⊕ Fin 4) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr k) => .inr k
    | .inr k => .inl (.inr k)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr k) => .inr k
    | .inr k => .inl (.inr k)
  left_inv := by rintro ((i|k)|k) <;> rfl
  right_inv := by rintro ((i|k)|k) <;> rfl

lemma exchange_edge (a b : Position n) (h : a.Disjoint b) (p : Pairing n) (t u : Tile)
    (v w : ((Fin n ⊕ Fin 4) ⊕ Fin 4)) :
    Circuit.compactWiring p (pairCircuit a b t u) v w ↔
      Circuit.compactWiring p (pairCircuit b a u t) (exchangeEquiv v) (exchangeEquiv w) := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  rcases v with (i|k)|k <;> rcases w with (j|l)|l
  all_goals simp [pairCircuit,Circuit.compactWiring,CompactGate.wiring,Circuit.support,
    Circuit.compactBoundary,CompactGate.boundary,gate,exchangeEquiv,
    h₀,h₁,h₂,h₃,h₀.symm,h₁.symm,h₂.symm,h₃.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp only [Sum.inl.injEq]

lemma exchange_boundary (a b : Position n) (h : a.Disjoint b) (t u : Tile) (i : Fin n) :
    exchangeEquiv ((pairCircuit a b t u).compactBoundary i)=
      (pairCircuit b a u t).compactBoundary i := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  by_cases ha : i=a.left <;> by_cases ha' : i=a.right <;>
    by_cases hb : i=b.left <;> by_cases hb' : i=b.right
  all_goals simp_all [pairCircuit,Circuit.compactBoundary,CompactGate.boundary,gate,exchangeEquiv]
  all_goals rfl

lemma exchange_compatible (a b : Position n) (h : a.Disjoint b) (p : Pairing n) (t u : Tile) :
    Circuit.Compatible p (pairCircuit a b t u) ↔ Circuit.Compatible p (pairCircuit b a u t) := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  simp only [pairCircuit,Circuit.Compatible,Circuit.support,gate,
    h₀,h₁,h₂,h₃,h₀.symm,h₁.symm,h₂.symm,h₃.symm,true_and]
  itauto

lemma exchange_eval (a b : Position n) (h : a.Disjoint b) (p q : Pairing n) (t u : Tile) :
    Circuit.eval p (pairCircuit a b t u)=some q ↔ Circuit.eval p (pairCircuit b a u t)=some q := by
  rw [Circuit.compact_eval_iff,Circuit.compact_eval_iff,exchange_compatible a b h]
  exact and_congr_right fun _ =>
    (Graph.BoundaryEquiv.ofEquiv exchangeEquiv (exchange_edge a b h p t u)
      (exchange_boundary a b h t u)).realizes_iff

lemma steps_commute (a b : Position n) (h : a.Disjoint b) (p : Pairing n) (t u : Tile) :
    (p.tileStep a.left a.right a.adjacent t).bind (fun q => q.tileStep b.left b.right b.adjacent u) =
      (p.tileStep b.left b.right b.adjacent u).bind (fun q => q.tileStep a.left a.right a.adjacent t) := by
  apply Option.ext
  intro q
  exact exchange_eval a b h p q t u

end Position

lemma localR_commute {K : Type*} [CommRing K] {n : ℕ} (a b : Position n)
    (h : a.Disjoint b) (w v : Weights K) :
    localR a w * localR b v = localR b v * localR a w := by
  unfold localR
  simp only [Finset.sum_mul,Finset.mul_sum,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  rw [optionMatrix_mul,optionMatrix_mul]
  congr 1
  · ring
  · apply congrArg optionMatrix
    funext p
    exact (a.steps_commute b h p t u).symm


 

 

namespace Pairing
variable {n m : ℕ} (f : Fin n ↪o Fin m)

lemma map_adj (p : Pairing n) (x y : Fin m) :
    (p.map f).Adj x y ↔ ∃ i j, p.Adj i j ∧ f i=x ∧ f j=y := by
  simp only [map,Adj,Finset.mem_map,Prod.exists,Function.Embedding.coe_prodMap,Prod.map_apply,Prod.mk.injEq]
  constructor
  · rintro (⟨i,j,h,hi,hj⟩|⟨i,j,h,hj,hi⟩)
    · exact ⟨i,j,Or.inl h,hi,hj⟩
    · exact ⟨j,i,Or.inr h,hi,hj⟩
  · rintro ⟨i,j,(h|h),hi,hj⟩
    · exact Or.inl ⟨i,j,h,hi,hj⟩
    · exact Or.inr ⟨j,i,h,hj,hi⟩

@[simp] lemma map_occupied (p : Pairing n) (i : Fin n) :
    (p.map f).Occupied (f i) ↔ p.Occupied i := by
  simp only [Occupied,map_adj]
  constructor
  · rintro ⟨_,a,b,h,ha,_⟩
    have := f.injective ha
    subst a
    exact ⟨b,h⟩
  · rintro ⟨j,h⟩
    exact ⟨f j,i,j,h,rfl,rfl⟩

@[simp] lemma map_partnerOrSelf (p : Pairing n) (i : Fin n) :
    (p.map f).partnerOrSelf (f i)=f (p.partnerOrSelf i) := by
  by_cases hi : p.Occupied i
  · have hmap : (p.map f).Adj (f i) (f (p.partnerOrSelf i)) :=
      (map_adj_image f p _ _).mpr ((p.adj_partnerOrSelf i _).mpr ⟨hi,rfl⟩)
    exact ((p.map f).adj_partnerOrSelf _ _).mp hmap |>.2.symm
  · simp [partnerOrSelf,hi]

@[simp] lemma map_cutShape (p : Pairing n) (a b : Fin n) :
    (p.map f).cutShape (f a) (f b)=p.cutShape a b := by
  simp only [cutShape,map_occupied,map_adj_image]

lemma map_cutLabels (p : Pairing n) (a b : Fin n) (i : Fin 4) :
    (p.map f).cutLabels (f a) (f b) i=f (p.cutLabels a b i) := by
  fin_cases i <;> simp [cutLabels]

lemma map_omit_adj (p : Pairing n) (a b : Fin n) (x y : Fin m) :
    ((p.map f).omitTwo (f a) (f b)).Adj x y ↔
      ∃ i j, (p.omitTwo a b).Adj i j ∧ f i=x ∧ f j=y := by
  simp only [omitTwo_adj,map_adj]
  constructor
  · rintro ⟨⟨i,j,h,rfl,rfl⟩,hia,hib,hja,hjb⟩
    exact ⟨i,j,⟨h,fun he => hia (congrArg f he),fun he => hib (congrArg f he),
      fun he => hja (congrArg f he),fun he => hjb (congrArg f he)⟩,rfl,rfl⟩
  · rintro ⟨i,j,⟨h,hia,hib,hja,hjb⟩,rfl,rfl⟩
    exact ⟨⟨i,j,h,rfl,rfl⟩,fun he => hia (f.injective he),fun he => hib (f.injective he),
      fun he => hja (f.injective he),fun he => hjb (f.injective he)⟩

lemma map_cutRelation (p : Pairing n) (a b : Fin n) (d : Finset (Fin 4 × Fin 4)) (x y : Fin m) :
    (p.map f).cutRelation (f a) (f b) d x y ↔
      ∃ i j, p.cutRelation a b d i j ∧ f i=x ∧ f j=y := by
  simp only [cutRelation,map_omit_adj,map_cutLabels]
  constructor
  · rintro (⟨i,j,h,hi,hj⟩|⟨r,s,h,hi,hj⟩)
    · exact ⟨i,j,Or.inl h,hi,hj⟩
    · exact ⟨p.cutLabels a b r,p.cutLabels a b s,Or.inr ⟨r,s,h,rfl,rfl⟩,hi,hj⟩
  · rintro ⟨i,j,(h|⟨r,s,h,rfl,rfl⟩),hi,hj⟩
    · exact Or.inl ⟨i,j,h,hi,hj⟩
    · exact Or.inr ⟨r,s,h,hi,hj⟩

lemma map_tileStep (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val)
    (hf : (f a).val+1=(f b).val) (t : Tile) :
    (p.map f).tileStep (f a) (f b) hf t=(p.tileStep a b hab t).map (Pairing.map f) := by
  cases hp : p.tileStep a b hab t with
  | none =>
    simp only [Option.map_none]
    rw [tileStep_none_iff,map_cutShape,←tileStep_none_iff p a b hab t,hp]
  | some q =>
    have hd : CutPatch.profile (p.cutShape a b) t≠none := by
      rw [ne_eq,←tileStep_none_iff p a b hab t,hp]
      exact Option.some_ne_none q
    obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp hd
    have hn : (p.map f).tileStep (f a) (f b) hf t≠none := by
      rw [ne_eq,tileStep_none_iff,map_cutShape,hd]
      exact Option.some_ne_none d
    obtain ⟨r,hr⟩ := Option.ne_none_iff_exists'.mp hn
    simp only [hr,Option.map_some,Option.some.injEq]
    apply ext_adj
    intro x y
    rw [tileStep_sound (p.map f) _ _ hf t r d hr (by simpa only [map_cutShape] using hd),
      map_cutRelation,map_adj]
    simp_rw [tileStep_sound p a b hab t q d hp hd]

end Pairing
end
end CriticalStrip.Diagram

end OAI
