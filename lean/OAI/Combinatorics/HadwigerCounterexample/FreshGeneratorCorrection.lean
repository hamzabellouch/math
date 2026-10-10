import OAI.Combinatorics.HadwigerCounterexample.LabeledGenerators

namespace OAI

/-! # Fresh Generator Correction -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Submodule Module
open scoped BigOperators
namespace StatusAnalysis
variable {L I X Y : Type} [DecidableEq L] [DecidableEq I]
variable [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
namespace Club
variable (C : Club I X L)

omit [DecidableEq L] [DecidableEq I] [AddCommGroup X] [Module F X] in
theorem bundle_back {p : Finset I} {s t : Straps L} (ht : s≤t) (h : bundle C p t) :
    bundle C p s := ⟨fun i hi=> zone_smaller C ht i (h.1 i hi),h.2⟩
omit [AddCommGroup X] [Module F X] in
theorem bundle_combine {p q : Finset I} {s : Straps L} (h : bundle C p s)
    (hQ : bundle C q (s⊔addrs C p)) :
    bundle C (p∪q) s∧ Disjoint p q := by
  classical
  have he {i j} (hi:i∈q) (hj:j∈p) : different C i j := fun b ht => (hQ.1 i hi).2 b
    (mem_union_right _ (mem_image.mpr ⟨j,hj,Eq.symm ht⟩))
  refine ⟨⟨fun i h'=>?_, fun b i hi j hj ht=>?_⟩,
    Finset.disjoint_left.mpr (fun i hi ht=> (he ht hi) true rfl)⟩
  · rcases mem_union.mp h' with hp|hp
    · exact h.1 i hp
    exact (bundle_back C le_sup_left hQ).1 i hp
  rcases mem_union.mp hi with hi|hi <;> rcases mem_union.mp hj with hj|hj
  · exact h.2 b hi hj ht
  · exact (he hj hi b ht.symm).elim
  · exact (he hi hj b ht).elim
  exact hQ.2 b hi hj ht

private theorem binary_word {x z : X} (h : z∈ Submodule.span F {x}) :
    z=0 ∨ z=x := by
  obtain ⟨a,ha⟩ := (Submodule.mem_span_singleton.mp h)
  rcases bit_cases a with h|h <;> simpa [h,eq_comm,ha] using (by
    simp [h] at ha; tauto : z=0∨z=x)

abbrev sizeB (t : Straps L) (r : ℕ) := ∀ i,(t i).card≤ r

def travels (s : Straps L) (n : ℕ) (π : X →ₗ[F] Y) (V : Space X) :=
  ∀ t:Straps L,sizeB t n→ C.band (s⊔t)=V ∧ C.yield3 (s⊔t) π

omit [DecidableEq I] in
theorem travel_more {s : Straps L} {a b : ℕ} {π : X→ₗ[F] Y} {V}
    (h : C.travels s a π V) {n : ℕ} (t : Straps L) (ht : sizeB t b) (hh : n+b ≤ a) :
    C.travels (s⊔t) n π V := by
  intro u hu
  rw [sup_assoc]
  apply h
  exact fun i=> (Finset.card_union_le ..).trans
    ((Nat.add_le_add (ht i) (hu i)).trans (add_comm b n ▸ hh))
omit [DecidableEq I] in
theorem travel_now {s : Straps L} {a : ℕ} {π : X→ₗ[F] Y} {V} (h : C.travels s a π V) :
    band C s=V ∧ yield3 C s π := by simpa using h ⊥ (by intro i; change (∅:Finset L).card≤_; simp)

theorem length3_rich {s : Straps L} {a : ℕ} {π : X→ₗ[F] Y} {V} (h : C.travels s a π V) :
    Submodule.span F (C.length3 s π) = V⊓LinearMap.ker π :=
  (ration_eq C s π (travel_now C h).2).trans (congrArg (·⊓LinearMap.ker π) (travel_now C h).1)

variable [Module.Finite F X]
set_option maxHeartbeats 1000000 in
theorem jump_two {s : Straps L} {π : X →ₗ[F] Y} {V : Space X}
    (h : C.travels s 3 π V)
    (he : dim (V ⊓ LinearMap.ker π : Space X) ≤ 2) (x : X) (hx : x∈ V⊓LinearMap.ker π) :
    ∃ p:Finset I,C.bundle p s∧p.card≤6∧C.contents p=x := by
  classical
  by_cases h0 : x=0
  · obtain ⟨p,h1,h2,h3,_⟩:=length3_zero C s π
    exact ⟨p,h1,h2.trans (by decide),h3.trans h0.symm⟩
  let R := V⊓LinearMap.ker π
  have hh {t : Straps L} {i : ℕ} (h : C.travels t i π V)
      (Q : Space X) (e : x∉Q) :
      ∃ y,y∈R∧C.length3 t π y∧y∉Q := by
    rw [←length3_rich C h] at hx
    by_contra! hg
    apply e
    exact (Submodule.span_le.mpr (fun i (hi : C.length3 _ _ _) =>
      hg i ((length3_rich C h).le (Submodule.subset_span hi)) hi)) hx
  obtain ⟨y,hy,⟨p,hp,hP,hQ,hd⟩,ht⟩:=hh h ⊥ (by simpa using h0)
  have hy' : y≠0 := by simpa using ht
  let S:=Submodule.span F {y}
  by_cases hh1 : x∈ S
  · exact ⟨p,hp,hP.trans (by decide),hQ.trans (((binary_word hh1).resolve_left h0).symm)⟩
  let T:=s⊔C.addrs p
  have hT : C.travels T 0 π V := travel_more C h (C.addrs p)
    (fun i=>card_image_le.trans hP) (Nat.le_refl 3)
  obtain ⟨z,hz,⟨q,hq,hq',hZ,_⟩,hv⟩:=hh hT S hh1
  let B:=Submodule.span F {z}
  have hm : S⊔B=R := by
    have hk : S⊔B≤ R := sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr hy)
      ((Submodule.span_singleton_le_iff_mem ..).mpr hz)
    have hh:= Submodule.finrank_sup_span_singleton hv
    have ht : dim S=1 := finrank_span_singleton hy'
    exact Submodule.eq_of_le_of_finrank_le hk (by
      change dim R≤dim (S⊔B : Space X)
      change dim (S⊔B : Space X) = dim S+1 at hh
      rw [hh,ht]; exact he)
  obtain ⟨u,hu,t,ht,hx⟩:= Submodule.mem_sup.mp (show x∈ S⊔B from hm.symm ▸ hx)
  rcases binary_word hu with hA|hA <;> rcases binary_word ht with hB|hB
  · rw [hA,hB,zero_add] at hx; exact (h0 hx.symm).elim
  · rw [hA,hB,zero_add] at hx
    exact ⟨q,bundle_back C le_sup_left hq,hq'.trans (by decide),hZ.trans hx⟩
  · rw [hA,hB,add_zero] at hx; exact ⟨p,hp,hP.trans (by decide),hQ.trans hx⟩
  obtain ⟨hg,hD⟩:=bundle_combine C hp hq
  refine ⟨p∪q,hg,(card_union_le ..).trans (by omega),?_⟩
  rw [contents,Finset.sum_union hD]; change C.contents _+_=_
  exact (congrArg₂ (·+·) (hQ.trans hA.symm) (hZ.trans hB.symm)).trans hx
end Club
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
