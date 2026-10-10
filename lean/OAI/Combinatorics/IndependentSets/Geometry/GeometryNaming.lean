import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.CircleCost

namespace OAI

noncomputable section

namespace LargeIndependentSets.ShortestPaths

open scoped ENNReal

lemma pathDistance_surjective {X Y : Type*} (e : X → Y) (he : Function.Surjective e)
    (w : Y → Y → ℝ≥0∞) (x y : X) :
    pathDistance (fun a b => w (e a) (e b)) x y = pathDistance w (e x) (e y) := by
  unfold pathDistance
  apply le_antisymm
  · apply le_iInf
    intro zs
    obtain ⟨ws,hws⟩ := List.map_surjective_iff.mpr he zs
    apply iInf_le_of_le ws
    rw [walkLength_reindex,hws]
  · apply le_iInf
    intro zs
    rw [walkLength_reindex]
    exact iInf_le_of_le (zs.map e) le_rfl

theorem cover_allPairs_exact {Q : Type*} [DecidableEq Q] {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] {n : ℕ} (e : Fin n → GridLocation M D)
    (he : Function.Surjective e) (i j : Fin n) :
    let a : Matrix n := Vector.ofFn (fun x => Vector.ofFn (fun y => linkCost S (e x) (e y)))
    (a.allPairs.get i j : ℝ≥0∞)/(D : ℝ≥0∞) = pathDistance S.linkLength (e i) (e j) := by
  dsimp only
  rw [Matrix.scaled_allPairs_exact]
  have hh : (fun x y : Fin n =>
      ((Matrix.get (Vector.ofFn (fun x => Vector.ofFn (fun y => linkCost S (e x) (e y)))) x y : ℝ≥0∞) /
        (D : ℝ≥0∞))) = (fun x y => S.linkLength (e x) (e y)) := by
    funext x y
    simpa only [Matrix.get,Vector.getElem_ofFn] using linkCost_exact S (e x) (e y)
  rw [hh,pathDistance_surjective e he]

end LargeIndependentSets.ShortestPaths

namespace LargeIndependentSets.GeometryNames

section
open scoped ENNReal Classical BigOperators

def mixed {U V : Type*} {n : ℕ} (u : Fin n → U) (v : Fin n → V) (i : ℕ) :
    MixedTuple U V n i :=
  ⟨fun k => if k.val < i then Sum.inl (v k) else Sum.inr (u k),by
    intro k; by_cases hk : k.val < i <;> simp [hk]⟩

@[simp] lemma mixed_val {U V : Type*} {n : ℕ} (u : Fin n → U) (v : Fin n → V)
    (i : ℕ) (k : Fin n) : (mixed u v i).val k =
      if k.val < i then Sum.inl (v k) else Sum.inr (u k) := rfl

lemma mixed_surjective {U V : Type*} [Nonempty U] [Nonempty V] {n i : ℕ}
    (q : MixedTuple U V n i) : ∃ u v, mixed u v i=q := by
  let u : Fin n → U := fun k => (q.val k).elim (fun _ => Classical.choice inferInstance) id
  let v : Fin n → V := fun k => (q.val k).elim id (fun _ => Classical.choice inferInstance)
  refine ⟨u,v,Subtype.ext ?_⟩
  funext k
  have h := q.property k
  cases he : q.val k with
  | inl a =>
    have hk : k.val < i := by simpa [he] using h.symm
    simp [mixed,u,v,he,hk]
  | inr a =>
    have hk : ¬k.val < i := by simpa [he] using h.symm
    simp [mixed,u,v,he,hk]

abbrev StaticPoint (L R : Type) (n D : ℕ) :=
  Σ i : Fin (n+1), MixedTuple L R n i.val → ZMod D

def decode {U V L R : Type} {n D : ℕ}
    (u : Fin n → U) (v : Fin n → V) (a : StaticPoint L R n D) :
    GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=n)) D :=
  ⟨⟨a.1,mixed u v a.1.val⟩,a.2⟩

lemma decode_surjective {U V L R : Type} [Nonempty U] [Nonempty V] {n D : ℕ}
    (x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=n)) D) :
    ∃ u v a, decode u v a=x := by
  rcases x with ⟨⟨i,q⟩,x⟩
  obtain ⟨u,v,h⟩ := mixed_surjective q
  refine ⟨u,v,⟨i,x⟩,?_⟩
  cases h
  rfl

abbrev Node (L R : Type) (n D nu nv : ℕ) :=
  ((Fin n → Fin nu) × (Fin n → Fin nv)) × StaticPoint L R n D

def nodeDecode {L R : Type} {n D nu nv : ℕ} (x : Node L R n D nu nv) :=
  decode x.1.1 x.1.2 x.2

lemma nodeDecode_surjective {L R : Type} {n D nu nv : ℕ} (hu : 0<nu) (hv : 0<nv) :
    Function.Surjective (@nodeDecode L R n D nu nv) := by
  let : Nonempty (Fin nu) := ⟨⟨0,hu⟩⟩
  let : Nonempty (Fin nv) := ⟨⟨0,hv⟩⟩
  intro x
  obtain ⟨u,v,a,h⟩ := decode_surjective x
  exact ⟨((u,v),a),h⟩

def nodeEquiv (L R : Type) [Fintype L] [Fintype R] (n D nu nv : ℕ) [NeZero D] :
    Node L R n D nu nv ≃ Fin ((nu^n*nv^n)*Fintype.card (StaticPoint L R n D)) :=
  (Equiv.prodCongr ((Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv).trans
    finProdFinEquiv) (Fintype.equivFin (StaticPoint L R n D))).trans finProdFinEquiv

def names (L R : Type) [Fintype L] [Fintype R] (n D nu nv : ℕ) [NeZero D] :=
  fun i => nodeDecode ((nodeEquiv L R n D nu nv).symm i)

lemma names_surjective (L R : Type) [Fintype L] [Fintype R] (n D nu nv : ℕ) [NeZero D]
    (hu : 0<nu) (hv : 0<nv) : Function.Surjective (names L R n D nu nv) :=
  (nodeDecode_surjective hu hv).comp (nodeEquiv L R n D nu nv).symm.surjective

end

open scoped Classical

def PointStep {L R : Type} {n D : ℕ} (h : Fin n) (f : L → R)
    (a b : StaticPoint L R n D) : Prop :=
  ∃ (x : MixedTuple L R n h.val → ZMod D) (y : MixedTuple L R n (h.val+1) → ZMod D),
    a=⟨h.castSucc,x⟩ ∧ b=⟨h.succ,y⟩ ∧ x=y ∘ mixedProject h f

def QuestionStep {U V L R C : Type} {n : ℕ} (lc : LabelCoverData U V L R C)
    (h : Fin n) (c : C) (u u' : Fin n → U) (v v' : Fin n → V) : Prop :=
  u h=lc.left c ∧ v' h=lc.right c ∧
    ∀ k, k≠h → if k.val<h.val then v k=v' k else u k=u' k

lemma questionStep_iff {U V L R C : Type} {n : ℕ} (lc : LabelCoverData U V L R C)
    (h : Fin n) (c : C) (u u' : Fin n → U) (v v' : Fin n → V) :
    QuestionStep lc h c u u' v v' ↔
      (mixed u v h.val).val h=Sum.inr (lc.left c) ∧
      (mixed u' v' (h.val+1)).val h=Sum.inl (lc.right c) ∧
      ∀ k, k≠h → (mixed u v h.val).val k=(mixed u' v' (h.val+1)).val k := by
  simp only [QuestionStep,mixed_val,lt_self_iff_false,ite_false,Sum.inr.injEq,
    Nat.lt_succ_self,ite_true,Sum.inl.injEq]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro k
  by_cases hk : k=h
  · simp [hk]
  · have hne : k.val≠h.val := fun e => hk (Fin.ext e)
    by_cases hl : k.val<h.val
    · simp [hk,hl,show k.val<h.val+1 by omega]
    · simp [hk,hl,show ¬k.val<h.val+1 by omega]

lemma forward_iff {U V L R C : Type} {n D : ℕ} (lc : LabelCoverData U V L R C)
    (u u' : Fin n → U) (v v' : Fin n → V) (a b : StaticPoint L R n D) :
    (layeredSystem lc n).ForwardZero D (decode u v a) (decode u' v' b) ↔
      ∃ h c, PointStep h (lc.project c) a b ∧ QuestionStep lc h c u u' v v' := by
  constructor
  · intro hz
    rw [ShortestPaths.forwardZero_iff] at hz
    obtain ⟨π,hπ,hcoord⟩ := hz
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    change LayerImposed lc n ⟨i,mixed u v i.val⟩ ⟨j,mixed u' v' j.val⟩ π at hπ
    cases hπ with
    | adjacent h q q' c hl hr ho =>
      refine ⟨h,c,?_,?_⟩
      · exact ⟨a,b,rfl,rfl,hcoord⟩
      · exact (questionStep_iff lc h c u u' v v').mpr ⟨hl,hr,ho⟩
  · rintro ⟨h,c,⟨x,y,rfl,rfl,hxy⟩,hq⟩
    rw [ShortestPaths.forwardZero_iff]
    obtain ⟨hl,hr,ho⟩ := (questionStep_iff lc h c u u' v v').mp hq
    exact ⟨mixedProject h (lc.project c),.adjacent h _ _ c hl hr ho,hxy⟩

end LargeIndependentSets.GeometryNames

end

end OAI
