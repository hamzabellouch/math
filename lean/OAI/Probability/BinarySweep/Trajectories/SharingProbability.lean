import Mathlib
import OAI.Probability.BinarySweep.Trajectories.SharingWitness
import OAI.Probability.BinarySweep.FiniteLaws.FiniteProductProbability

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I H Ω : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype Ω]

 def sharingGraph (R : Ω → Ω → Prop)
    (hs : ∀ ⦃first second⦄, R first second → R second first) (x : I → Ω) : SimpleGraph I where
  Adj i j := i ≠ j ∧ R (x i) (x j)
  symm := ⟨fun _ _ h => ⟨h.1.symm,hs h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def incidentSet (R : Ω → Ω → Prop) (roots : H → Ω) (x : I → Ω) : Finset I :=
  Finset.univ.filter (fun i => (∃ j, i ≠ j ∧ R (x i) (x j)) ∨ ∃ h, R (x i) (roots h))

omit [Fintype Ω] in
lemma sharing_depthOne (R : Ω → Ω → Prop)
    (hs : ∀ ⦃first second⦄, R first second → R second first)
    (roots : H → Ω) (x : I → Ω) (w : ℕ) (hw : w ≤ (incidentSet R roots x).card) :
    ∃ T : Finset I, w ≤ 2*T.card ∧
      ∃ f : T → {i // i ∉ T} ⊕ H, ∀ i : T,
        R (x i) ((f i).elim (fun j : {i // i ∉ T} => x j.val) roots) := by
  classical
  obtain ⟨T,_,hc,hT⟩ := sharing_witness (sharingGraph R hs x) (fun i h => R (x i) (roots h))
  have hc' : (incidentSet R roots x).card ≤ 2*T.card := by
    convert hc using 1
    congr 1
    ext i
    simp only [incidentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

  refine ⟨T,hw.trans hc',?_⟩
  have hp (i : T) : ∃ a : {i // i ∉ T} ⊕ H,
      R (x i) (a.elim (fun j : {i // i ∉ T} => x j.val) roots) := by
    obtain ⟨j,hj,hij⟩ | ⟨h,hi⟩ := hT i i.property
    · exact ⟨Sum.inl ⟨j,hj⟩,hij.2⟩
    · exact ⟨Sum.inr h,hi⟩
  choose f hf using hp
  exact ⟨f,hf⟩

theorem sharing_probability_le
    (p : Ω → ℝ) (hp : ∀ u, 0 ≤ p u) (hp1 : ∑ u, p u = 1)
    (R : Ω → Ω → Prop)
    (hs : ∀ ⦃first second⦄, R first second → R second first) (roots : H → Ω)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hR : ∀ v, (∑ u, p u * (if R u v then 1 else 0)) ≤ ω)
    (w : ℕ) (hsmall : ((Fintype.card I + Fintype.card H : ℕ) : ℝ)*ω ≤ 1) :
    productProbability p (fun x : I → Ω => w ≤ (incidentSet R roots x).card) ≤
      (2:ℝ)^Fintype.card I *
        (((Fintype.card I + Fintype.card H : ℕ):ℝ)*ω)^((w+1)/2) := by
  classical
  let E (T : Finset I) (f : T → {i // i ∉ T} ⊕ H) (x : I → Ω) :=
    ∀ i : T, R (x i) ((f i).elim (fun j : {i // i ∉ T} => x j.val) roots)
  let r : ℝ := ((Fintype.card I + Fintype.card H : ℕ):ℝ)*ω
  have hr : 0 ≤ r := mul_nonneg (Nat.cast_nonneg _) hω
  have hT (T : Finset I) : productProbability p (fun x => w ≤ 2*T.card ∧ ∃ f, E T f x) ≤
      r^((w+1)/2) := by
    by_cases hc : w ≤ 2*T.card
    · have h1 := productProbability_union_le hp (E T)
      have h2 : (∑ f, productProbability p (E T f)) ≤
          (Fintype.card (T → {i // i ∉ T} ⊕ H) : ℝ)*ω^T.card := by
        simpa [E] using Finset.sum_le_sum (s:=Finset.univ) (fun f _ => depthOne_probability_le p hp hp1 R ω hω hR T f roots)
      have hd : Fintype.card ({i // i ∉ T} ⊕ H) ≤ Fintype.card I + Fintype.card H := by
        rw [Fintype.card_sum]
        exact Nat.add_le_add_right (Fintype.card_subtype_le _) _
      have h3 : (Fintype.card (T → {i // i ∉ T} ⊕ H) : ℝ)*ω^T.card ≤ r^T.card := by
        rw [Fintype.card_fun,Fintype.card_coe,Nat.cast_pow]
        dsimp [r]
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hω _)
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hd) _
      have he : (w+1)/2 ≤ T.card := by omega
      simpa only [hc,true_and] using h1.trans (h2.trans (h3.trans
        (pow_le_pow_of_le_one hr hsmall he)))
    · simp only [hc,false_and,productProbability,ite_false,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hr _
  calc
    _ ≤ productProbability p (fun x => ∃ T : Finset I, w ≤ 2*T.card ∧ ∃ f, E T f x) :=
      productProbability_mono hp (fun x hx => sharing_depthOne R hs roots x w hx)
    _ ≤ ∑ T : Finset I, productProbability p (fun x => w ≤ 2*T.card ∧ ∃ f, E T f x) :=
      productProbability_union_le hp _
    _ ≤ ∑ T : Finset I, r^((w+1)/2) := Finset.sum_le_sum (fun T _ => hT T)
    _ = _ := by simp [r,Fintype.card_finset]

end BinaryCoordinateSweeps.Sparse

end

end OAI
