import OAI.Combinatorics.SquareDifference.GoodPairSupport

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

def OtherVertices {V : Type*} (u v : V) := {w : V // w≠u ∧ w≠v}

instance {V : Type*} [Fintype V] [DecidableEq V] (u v : V) : Fintype (OtherVertices u v) := inferInstanceAs (Fintype {w : V // w≠u ∧ w≠v})

instance {V : Type*} [DecidableEq V] (u v : V) : DecidableEq (OtherVertices u v) := inferInstanceAs (DecidableEq {w : V // w≠u ∧ w≠v})

lemma product_pair_split {V E : Type*} [Fintype V] [DecidableEq V] [CommMonoid E]
    (u v : V) (huv : u≠v) (f : V → E) :
    (∏w,f w)=f u*f v*∏w : OtherVertices u v,f w.val := by
  rw [←prod_mul_prod_compl {u,v} f]
  rw [prod_insert (by simpa using huv),prod_singleton]
  congr 1
  exact prod_subtype _ (fun w => by simp only [mem_compl,mem_insert,mem_singleton,not_or]) f

lemma otherVertices_card {V : Type*} [Fintype V] [DecidableEq V] (u v : V) (huv : u≠v) :
    Fintype.card (OtherVertices u v)+2=Fintype.card V := by
  have he : Fintype.card (OtherVertices u v)=({u,v}ᶜ : Finset V).card := by
    change Fintype.card {w : V // w≠u ∧ w≠v} = _
    rw [Fintype.card_subtype]
    congr 1
    ext w
    simp only [mem_filter,mem_univ,true_and,mem_compl,mem_insert,mem_singleton,not_or]
  rw [he,card_compl,card_insert_of_notMem (by simpa using huv),card_singleton]
  have ht : 2≤Fintype.card V := by
    have hcard := card_le_univ ({u,v} : Finset V)
    simpa [huv] using hcard
  omega

lemma multilinear_pair_expand {V X I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (u v : V) (huv : u≠v)
    (F G : X → ℝ) (f : OtherVertices u v → I → X → ℝ) :
    multilinearIntegral L (fun w => if hu : w=u then F else if hv : w=v then G else
      fun x => ∑i,f ⟨w,hu,hv⟩ i x)=
    ∑a : OtherVertices u v → I,L (fun z => F (z u)*G (z v)*∏w,f w (a w) (z w.val)) := by
  classical
  unfold multilinearIntegral
  have he (z : V → X) : (∏w,(if hu : w=u then F else if hv : w=v then G else
      fun x => ∑i,f ⟨w,hu,hv⟩ i x) (z w))=
      ∑a : OtherVertices u v → I,F (z u)*G (z v)*∏w,f w (a w) (z w.val) := by
    rw [product_pair_split u v huv]
    simp only [dite_true,Ne.symm huv,dite_false]
    have hw (w : OtherVertices u v) :
        (if hu : w.val=u then F else if hv : w.val=v then G else
          fun x => ∑i,f ⟨w.val,hu,hv⟩ i x) (z w.val)=∑i,f w i (z w.val) := by
      rcases w with ⟨w,hw⟩
      simp only [hw.1,hw.2,dite_false]
    simp_rw [hw]
    rw [Fintype.prod_sum,mul_sum]
  simp_rw [he]
  have hs : (fun z : V → X => ∑a : OtherVertices u v → I,F (z u)*G (z v)*∏w,f w (a w) (z w.val))=
      ∑a : OtherVertices u v → I,fun z : V → X => F (z u)*G (z v)*∏w,f w (a w) (z w.val) := by
    funext z
    exact (Finset.sum_apply z (univ : Finset (OtherVertices u v → I))
      (fun a z => F (z u)*G (z v)*∏w,f w (a w) (z w.val))).symm
  rw [hs,map_sum]

lemma primeProduct_union_le {J : Type*} [DecidableEq J] (p : J → ℕ)
    (hp : ∀j,1≤p j) (U W : Finset J) : (∏j∈U∪W,p j)≤(∏j∈U,p j)*(∏j∈W,p j) := by
  have hge : 1≤∏j∈U∩W,p j := one_le_prod₀ (fun j _ => hp j)
  calc
    _ ≤ (∏j∈U∪W,p j)*(∏j∈U∩W,p j) := Nat.le_mul_of_pos_right _ (by omega)
    _ = _ := prod_union_inter

lemma primeProduct_biUnion_le {J I : Type*} [DecidableEq J] (p : J → ℕ)
    (hp : ∀j,1≤p j) (s : Finset I) (U : I → Finset J) :
    (∏j∈s.biUnion U,p j)≤∏i∈s,∏j∈U i,p j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [biUnion_insert,prod_insert hi]
    exact (primeProduct_union_le p hp _ _).trans (Nat.mul_le_mul_left _ ih)

lemma intervalPiece_depends {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,NeZero (p j)] (a L : ℕ) (f : ℕ → ℝ) (U : Finset J)
    (x y : ResidueSpace p) (hxy : ∀j∈U,x j=y j) : intervalPiece p a L f U x=intervalPiece p a L f U y := by
  unfold intervalPiece
  congr 1
  apply sum_congr rfl
  intro n hn
  congr 1
  unfold exactGate
  apply prod_congr rfl
  intro j hj
  simp only [Pi.sub_apply,hxy j hj]

section PieceBound

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma interval_piece_product_bound (hinj : Function.Injective p)
    (Llaw : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀j F,(∀z,0≤F z) → 0≤Llaw j F) (hmass : ∀j,Llaw j (fun _ => 1)=1)
    (u v : V) (a : V → ℕ) (L : ℕ) (f : V → ℕ → ℝ) (M : ℝ) (hM : 0≤M)
    (hf : ∀v n,|f v n|≤M) (T : ℕ) (U : OtherVertices u v → Finset J)
    (hU : ∀w,∏j∈U w,p j≤T) (F G : ResidueSpace p → ℝ) (E : ℝ) (hE : 0≤E)
    (hpair : ∀(B : Finset J),(∏j∈B,p j)≤T^(Fintype.card (OtherVertices u v)) →
      ∀z,lawDensity (tensorLaw Llaw) z≠0 →
      |tensorLaw Llaw (fun x => F (freezeCoordinates B (z u) (x u))*
        G (freezeCoordinates B (z v) (x v)))|≤E) :
    |tensorLaw Llaw (fun z =>
      (∏w,intervalPiece p (a w.val) L (f w.val) (U w) (z w.val))*F (z u)*G (z v))|≤
      (M*T)^(Fintype.card (OtherVertices u v))*E := by
  classical
  let B := univ.biUnion U
  have hB : (∏j∈B,p j)≤T^(Fintype.card (OtherVertices u v)) := by
    apply (primeProduct_biUnion_le p (fun j => (Fact.out : (p j).Prime).one_lt.le) univ U).trans
    calc
      _ ≤ ∏w : OtherVertices u v,T := prod_le_prod (fun w _ => hU w)
      _ = _ := by simp
  apply tensorLaw_localized_pair Llaw hpos hmass B
    (fun z => ∏w,intervalPiece p (a w.val) L (f w.val) (U w) (z w.val)) F G u v
    ((M*T)^(Fintype.card (OtherVertices u v))) E (pow_nonneg (mul_nonneg hM (Nat.cast_nonneg T)) _) hE
  · intro z x
    apply prod_congr rfl
    intro w _
    apply intervalPiece_depends p
    intro j hj
    have hjB : j∈B := mem_biUnion.mpr ⟨w,mem_univ _,hj⟩
    simp only [hjB,ite_true]
  · intro z
    rw [abs_prod]
    calc
      _ ≤ ∏w : OtherVertices u v,M*T := by
        apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro w _
        apply (intervalPiece_sup p hinj (a w.val) L (f w.val) M hM (hf w.val) (U w) (z w.val)).trans
        apply mul_le_mul_of_nonneg_left _ hM
        exact_mod_cast hU w
      _ = _ := by simp
  · intro z hz
    exact hpair B hB z hz

end PieceBound

end SquareDifference

end

end OAI
