import Mathlib
import OAI.Probability.Perceptron.Variational.ShapeSampleLaw

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal NNReal BigOperators

lemma cascadeShapeFocus_cast (n : ℕ) {s t : CascadeVisitShape n}
    (h : s = t) (hs : s.Valid n) (ht : t.Valid n) :
    cast (congrArg (CascadeShapeReplicas n) h) (cascadeShapeFocus n s hs) =
      cascadeShapeFocus n t ht := by
  cases h
  rfl

lemma cascadeShapeReplicasOfFn_focus (n m : ℕ) (hm : 0 < m)
    (ss : Fin m → CascadeVisitShape n) (hv : ∀ i, (ss i).Valid n)
    (hs : CascadeVisitShape.Valid (n+1) (List.ofFn ss)) :
    cascadeShapeReplicasOfFnEquiv n m ss ⟨⟨0,hm⟩,cascadeShapeFocus n (ss ⟨0,hm⟩) (hv _)⟩ =
      cascadeShapeFocus (n+1) (List.ofFn ss) hs := by
  simp only [cascadeShapeReplicasOfFnEquiv,Equiv.sigmaCongr,cascadeShapeFocus]
  apply Sigma.ext (by rfl)
  have hlen : 0 < (List.ofFn ss).length := by simpa using hm
  have h : (List.ofFn ss)[0] = ss ⟨0,hm⟩ := by simp
  change HEq (cast _ (cascadeShapeFocus n (ss ⟨0,hm⟩) (hv _)))
    (cascadeShapeFocus n (List.ofFn ss)[0] (hs.2 _ (List.getElem_mem hlen)))
  exact heq_of_eq (cascadeShapeFocus_cast n h.symm (hv _) (hs.2 _ (List.getElem_mem (by simpa using hm))))

theorem finite_leaf_tuple_pointed_shape (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] (xs : ι → IndexedLeaf n) (i₀ : ι),
      ∃ s : CascadeVisitShape n, ∃ hs : s.Valid n,
        ∃ e : ι ≃ CascadeShapeReplicas n s,
          e i₀ = cascadeShapeFocus n s hs ∧
          ∀ i j, indexedCommonDepth n (xs i) (xs j) =
            indexedCommonDepth n (cascadeShapeLeaves n s (e i))
              (cascadeShapeLeaves n s (e j)) := by
  classical
  induction n with
  | zero =>
    intro ι _ xs i₀
    let : Nonempty ι := ⟨i₀⟩
    let e := Fintype.equivFin ι
    let z : Fin (Fintype.card ι) := ⟨0,Fintype.card_pos⟩
    refine ⟨Fintype.card ι,Fintype.card_pos,e.trans (Equiv.swap (e i₀) z),?_,fun _ _ => rfl⟩
    exact Equiv.swap_apply_left (e i₀) z
  | succ n ih =>
    intro ι _ xs i₀
    let : Nonempty ι := ⟨i₀⟩
    let root : ι → ℕ×ℕ := fun i => ((xs i).1,(xs i).2.1)
    let V := Set.range root
    let : Fintype V := (Set.finite_range root).fintype
    let g₀ : ι → V := fun i => ⟨root i,⟨i,rfl⟩⟩
    have hg₀ : Function.Surjective g₀ := by
      rintro ⟨v,i,hi⟩
      exact ⟨i,Subtype.ext hi⟩
    let : Nonempty V := Nonempty.map g₀ inferInstance
    let z : Fin (Fintype.card V) := ⟨0,Fintype.card_pos⟩
    let eV := (Fintype.equivFin V).trans (Equiv.swap ((Fintype.equivFin V) (g₀ i₀)) z)
    let g : ι → Fin (Fintype.card V) := fun i => eV (g₀ i)
    have hg : Function.Surjective g := eV.surjective.comp hg₀
    have hgzero : g i₀ = z := Equiv.swap_apply_left _ _
    have hroot (i j : ι) : g i = g j ↔ (xs i).1 = (xs j).1 ∧ (xs i).2.1 = (xs j).2.1 := by
      change eV (g₀ i) = eV (g₀ j) ↔ _
      rw [Equiv.apply_eq_iff_eq,Subtype.ext_iff]
      exact Prod.ext_iff
    let J (a : Fin (Fintype.card V)) := {i : ι // g i = a}
    let r (a : Fin (Fintype.card V)) : J a :=
      if h : a = z then ⟨i₀,hgzero.trans h.symm⟩ else
        ⟨Classical.choose (hg a),Classical.choose_spec (hg a)⟩
    have hc (a : Fin (Fintype.card V)) := ih (J a) (fun i => (xs i.val).2.2) (r a)
    choose ss hv ee hf he using hc
    let s : CascadeVisitShape (n+1) := List.ofFn ss
    have hs : s.Valid (n+1) := by
      constructor
      · apply List.length_pos_iff.mp
        simpa only [s,List.length_ofFn] using (Fintype.card_pos (α := V))
      · intro t ht
        obtain ⟨a,rfl⟩ := List.mem_ofFn.mp ht
        exact hv a
    let E : ι ≃ CascadeShapeReplicas (n+1) s :=
      ((Equiv.sigmaFiberEquiv g).symm.trans (Equiv.sigmaCongrRight ee)).trans
        (cascadeShapeReplicasOfFnEquiv n (Fintype.card V) ss)
    refine ⟨s,hs,E,?_,?_⟩
    · have hr : r z = ⟨i₀,hgzero⟩ := by simp [r]
      have hE : E i₀ = cascadeShapeReplicasOfFnEquiv n (Fintype.card V) ss ⟨z,ee z (r z)⟩ := by
        simp only [E,Equiv.trans_apply,Equiv.sigmaFiberEquiv,Equiv.coe_fn_mk,
          Equiv.symm_mk,Equiv.sigmaCongrRight_apply]
        have hi : (Sigma.mk (g i₀) ⟨i₀,rfl⟩ : Σ a, J a) = ⟨z,r z⟩ := by
          rw [hr]
          apply Sigma.ext hgzero
          apply (Subtype.heq_iff_coe_eq (fun x => by simp only [hgzero])).mpr
          rfl
        exact congrArg (fun p : Σ a, J a =>
          cascadeShapeReplicasOfFnEquiv n (Fintype.card V) ss ⟨p.1,ee p.1 p.2⟩) hi
      rw [hE,hf z]
      exact cascadeShapeReplicasOfFn_focus n (Fintype.card V) Fintype.card_pos ss hv hs
    · intro i j
      obtain ⟨⟨a,i⟩,rfl⟩ := (Equiv.sigmaFiberEquiv g).surjective i
      obtain ⟨⟨b,j⟩,rfl⟩ := (Equiv.sigmaFiberEquiv g).surjective j
      have hE (a : Fin (Fintype.card V)) (i : J a) :
          cascadeShapeLeaves (n+1) s (E ((Equiv.sigmaFiberEquiv g) ⟨a,i⟩)) =
            (a.val,0,cascadeShapeLeaves n (ss a) (ee a i)) := by
        simp only [E,Equiv.trans_apply,Equiv.symm_apply_apply,
          Equiv.sigmaCongrRight_apply,s,cascadeShapeLeaves_ofFn]
      rw [hE,hE]
      change indexedCommonDepth (n+1) (xs i.val) (xs j.val) = _
      by_cases hab : a = b
      · subst b
        have hij : (xs i.val).1 = (xs j.val).1 ∧ (xs i.val).2.1 = (xs j.val).2.1 :=
          (hroot i.val j.val).mp (i.property.trans j.property.symm)
        simp only [indexedCommonDepth,ite_eq_left hij,and_self,↓reduceIte]
        exact congrArg Fin.succ (he a i j)
      · have hij : ¬ ((xs i.val).1 = (xs j.val).1 ∧ (xs i.val).2.1 = (xs j.val).2.1) := by
          intro hij
          exact hab (i.property.symm.trans ((hroot i.val j.val).mpr hij) |>.trans j.property)
        have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
        simp only [indexedCommonDepth,ite_eq_right hij,habv,false_and,↓reduceIte]

lemma ennreal_tsum_pi_focus (m : ℕ) (J : Fin (m+1) → Type*)
    (f : ∀ i, J i → ℝ≥0∞) (g : J 0 → ℝ≥0∞) :
    (∑' ys : ∀ i, J i, (∏ i, f i (ys i)) * g (ys 0)) =
      (∑' y, f 0 y * g y) * ∏ i : Fin m, ∑' y, f i.succ y := by
  rw [← (Fin.consEquiv J).tsum_eq, ENNReal.tsum_prod']
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have he (a : J 0) (b : ∀ i : Fin m, J i.succ) :
      (f 0 a * ∏ i, f i.succ (b i)) * g a =
        (f 0 a * g a) * ∏ i, f i.succ (b i) := by ring
  simp_rw [he, ENNReal.tsum_mul_left, ennreal_tsum_pi_prod, ENNReal.tsum_mul_right]

lemma root_partition_sum_focused {A B : Type*} (m : ℕ) (J : Fin (m+1) → Type*)
    [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)] (r : J 0)
    (p : A → ℝ≥0∞) (q : A → B → ℝ≥0∞)
    (H : ∀ i, (J i → B) → ℝ≥0∞) (K : A → (J 0 → B) → ℝ≥0∞) :
    (∑' xs : (Σ i, J i) → A × B,
      if RootPartitionMatch xs then
        ((∏ u, p (xs u).1 * q (xs u).1 (xs u).2) *
          ∏ i, H i (fun j => (xs ⟨i,j⟩).2)) *
          (p (xs ⟨0,r⟩).1 * K (xs ⟨0,r⟩).1 (fun j => (xs ⟨0,j⟩).2)) else 0) =
    ∑' a : Fin (m+1) ↪ A,
      (p (a 0)) ^ (Fintype.card (J 0)+1) *
        (∑' ys : J 0 → B, ((∏ j, q (a 0) (ys j)) * H 0 ys) * K (a 0) ys) *
      ∏ i : Fin m, (p (a i.succ)) ^ Fintype.card (J i.succ) *
        (∑' ys : J i.succ → B, (∏ j, q (a i.succ) (ys j)) * H i.succ ys) := by
  rw [tsum_rootPartition]
  apply tsum_congr
  intro a
  rw [← (Equiv.piCurry (fun (i : Fin (m+1)) (_ : J i) => B)).symm.tsum_eq]
  simp only [Equiv.piCurry_symm_apply,rootPartitionEncode,Sigma.uncurry]
  simp_rw [Fintype.prod_sigma]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  have he (ys : ∀ i, J i → B) :
      (((∏ i, p (a i)^Fintype.card (J i)) * ∏ i, ∏ j, q (a i) (ys i j)) *
        ∏ i, H i (ys i)) * (p (a 0) * K (a 0) (ys 0)) =
      (∏ i, p (a i)^Fintype.card (J i) * ((∏ j, q (a i) (ys i j))*H i (ys i))) *
        (p (a 0) * K (a 0) (ys 0)) := by
    simp only [Finset.prod_mul_distrib]
    ring
  simp_rw [he]
  rw [ennreal_tsum_pi_focus m (fun i => J i → B)
    (fun i ys => p (a i)^Fintype.card (J i) * ((∏ j, q (a i) (ys j))*H i ys))
    (fun ys => p (a 0)*K (a 0) ys)]
  congr 1
  · have hh (ys : J 0 → B) :
        (p (a 0)^Fintype.card (J 0) * ((∏ j, q (a 0) (ys j))*H 0 ys)) *
          (p (a 0)*K (a 0) ys) =
        p (a 0) ^ (Fintype.card (J 0)+1) *
          (((∏ j, q (a 0) (ys j))*H 0 ys)*K (a 0) ys) := by
      rw [pow_succ]
      ring
    simp_rw [hh, ENNReal.tsum_mul_left]
  · simp_rw [ENNReal.tsum_mul_left]
    exact Finset.prod_mul_distrib

end SphericalPerceptronFreeEnergy

end

end OAI
