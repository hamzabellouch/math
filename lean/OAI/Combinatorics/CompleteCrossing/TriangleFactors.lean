import OAI.Combinatorics.CompleteCrossing.Triangle
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Finset.Fin

namespace OAI

/-! Triangular evaluation indices, division, and determinant factorization. -/

section

noncomputable section
open scoped Classical
namespace Paper170

def triangleMiddleEmbedding (s : ℕ) (hs : 2≤s) (p : Fin (2*(s-1))) : Fin (2*s) :=
  ⟨if p.val<s-1 then p.val else p.val+2, by split_ifs <;> omega⟩

def triangleEndEmbedding (s : ℕ) (hs : 2≤s) (p : Fin (2*(s-1))) : Fin (2*s) :=
  ⟨p.val+1, by omega⟩

theorem triangleMiddleEmbedding_strictMono (s : ℕ) (hs : 2≤s) :
    StrictMono (triangleMiddleEmbedding s hs) := by
  intro p q hpq
  change (if p.val<s-1 then p.val else p.val+2) <
    (if q.val<s-1 then q.val else q.val+2)
  change p.val<q.val at hpq
  split_ifs <;> omega

theorem triangleEndEmbedding_strictMono (s : ℕ) (hs : 2≤s) :
    StrictMono (triangleEndEmbedding s hs) := by
  intro p q hpq
  change p.val+1<q.val+1
  exact Nat.add_lt_add_right hpq 1

theorem triangleMiddleEmbedding_avoids (s : ℕ) (hs : 2≤s) (p : Fin (2*(s-1))) :
    (triangleMiddleEmbedding s hs p).val ≠ s-1 ∧
      (triangleMiddleEmbedding s hs p).val ≠ s := by
  dsimp [triangleMiddleEmbedding]
  split_ifs <;> omega

theorem triangleEndEmbedding_avoids (s : ℕ) (hs : 2≤s) (p : Fin (2*(s-1))) :
    (triangleEndEmbedding s hs p).val ≠ 0 ∧
      (triangleEndEmbedding s hs p).val ≠ 2*s-1 := by
  dsimp [triangleEndEmbedding]
  omega

theorem evenTriangle_delete_middle (s : ℕ) (hs : 2≤s) (p q : Fin (2*(s-1))) :
    (triangleMiddleEmbedding s hs p,triangleMiddleEmbedding s hs q)∈evenTriangle s ↔
      (p,q)∈evenTriangle (s-1) := by
  simp only [mem_evenTriangle,triangleMiddleEmbedding,Fin.lt_def]
  split_ifs <;> omega

theorem evenTriangle_delete_ends (s : ℕ) (hs : 2≤s) (p q : Fin (2*(s-1))) :
    (triangleEndEmbedding s hs p,triangleEndEmbedding s hs q)∈evenTriangle s ↔
      (p,q)∈evenTriangle (s-1) := by
  simp only [mem_evenTriangle,triangleEndEmbedding,Fin.lt_def]
  omega

theorem evenTriangle_middle_left_row (s : ℕ) (hs : 2≤s) (q : Fin (2*s)) :
    (⟨s-1,by omega⟩,q)∈evenTriangle s ↔ q.val<s-1 := by
  simp only [mem_evenTriangle,Fin.lt_def]
  omega

theorem evenTriangle_middle_right_row (s : ℕ) (hs : 2≤s) (q : Fin (2*s)) :
    (⟨s,by omega⟩,q)∈evenTriangle s ↔ s<q.val := by
  simp only [mem_evenTriangle,Fin.lt_def]
  omega

theorem evenTriangle_first_column (s : ℕ) (hs : 2≤s) (p : Fin (2*s)) :
    (p,⟨0,by omega⟩)∈evenTriangle s ↔ 0<p.val ∧ p.val<s := by
  simp only [mem_evenTriangle,Fin.lt_def]
  omega

theorem evenTriangle_last_column (s : ℕ) (hs : 2≤s) (p : Fin (2*s)) :
    (p,⟨2*s-1,by omega⟩)∈evenTriangle s ↔ s≤p.val ∧ p.val<2*s-1 := by
  simp only [mem_evenTriangle,Fin.lt_def]
  omega

theorem triangleMiddleEmbedding_range (s : ℕ) (hs : 2≤s) (i : Fin (2*s)) :
    (∃p, triangleMiddleEmbedding s hs p=i) ↔ i.val≠s-1 ∧ i.val≠s := by
  constructor
  · rintro ⟨p,rfl⟩
    exact triangleMiddleEmbedding_avoids s hs p
  · intro h
    by_cases hi : i.val<s-1
    · refine ⟨⟨i.val,by omega⟩,?_⟩
      apply Fin.ext
      simp [triangleMiddleEmbedding,hi]
    · refine ⟨⟨i.val-2,by omega⟩,?_⟩
      apply Fin.ext
      simp only [triangleMiddleEmbedding]
      split_ifs <;> omega

theorem triangleEndEmbedding_range (s : ℕ) (hs : 2≤s) (i : Fin (2*s)) :
    (∃p, triangleEndEmbedding s hs p=i) ↔ i.val≠0 ∧ i.val≠2*s-1 := by
  constructor
  · rintro ⟨p,rfl⟩
    exact triangleEndEmbedding_avoids s hs p
  · intro h
    refine ⟨⟨i.val-1,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [triangleEndEmbedding]
    omega

theorem evenTriangle_middle_left_card (s : ℕ) (hs : 2≤s) :
    (Finset.univ.filter (fun q : Fin (2*s) => (⟨s-1,by omega⟩,q)∈evenTriangle s)).card=s-1 := by
  have he : Finset.univ.filter (fun q : Fin (2*s) => (⟨s-1,by omega⟩,q)∈evenTriangle s)=
      Finset.Iio (⟨s-1,by omega⟩ : Fin (2*s)) := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio,
      evenTriangle_middle_left_row s hs,Fin.lt_def]
  rw [he,Fin.card_Iio]

theorem evenTriangle_middle_right_card (s : ℕ) (hs : 2≤s) :
    (Finset.univ.filter (fun q : Fin (2*s) => (⟨s,by omega⟩,q)∈evenTriangle s)).card=s-1 := by
  have he : Finset.univ.filter (fun q : Fin (2*s) => (⟨s,by omega⟩,q)∈evenTriangle s)=
      Finset.Ioi (⟨s,by omega⟩ : Fin (2*s)) := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ioi,
      evenTriangle_middle_right_row s hs,Fin.lt_def]
  rw [he,Fin.card_Ioi]
  dsimp
  omega

theorem evenTriangle_first_column_card (s : ℕ) (hs : 2≤s) :
    (Finset.univ.filter (fun p : Fin (2*s) => (p,⟨0,by omega⟩)∈evenTriangle s)).card=s-1 := by
  have he : Finset.univ.filter (fun p : Fin (2*s) => (p,⟨0,by omega⟩)∈evenTriangle s)=
      Finset.Ioo (⟨0,by omega⟩ : Fin (2*s)) ⟨s,by omega⟩ := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ioo,
      evenTriangle_first_column s hs,Fin.lt_def]
  rw [he,Fin.card_Ioo]
  simp

theorem evenTriangle_last_column_card (s : ℕ) (hs : 2≤s) :
    (Finset.univ.filter (fun p : Fin (2*s) => (p,⟨2*s-1,by omega⟩)∈evenTriangle s)).card=s-1 := by
  have he : Finset.univ.filter (fun p : Fin (2*s) => (p,⟨2*s-1,by omega⟩)∈evenTriangle s)=
      Finset.Ico (⟨s,by omega⟩ : Fin (2*s)) ⟨2*s-1,by omega⟩ := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ico,
      evenTriangle_last_column s hs,Fin.le_def,Fin.lt_def]
  rw [he,Fin.card_Ico]
  dsimp
  omega

theorem evenTriangle_two : evenTriangle 2 = {((1 : Fin 4),0),(2,3)} := by
  ext ⟨p,q⟩
  fin_cases p <;> fin_cases q <;> decide

theorem evenTriangle_two_distinct_coordinates (node : Fin 4 → ℝ)
    (hn : Function.Injective node) : node 1≠node 2 ∧ node 0≠node 3 := by
  constructor <;> exact hn.ne (by decide)

end Paper170

end
end

section

/-! The literal row and column elimination used in the even-node proof. -/
noncomputable section
open PolynomialModule Zarankiewicz
namespace Paper170

theorem mem_rectangle_of_toBiPolynomial_bounded (a b : ℕ) (P : Poly2)
    (hP : BiBounded (a+1) (b+1) (toBiPolynomial P)) : P∈rectangle a b := by
  rw [rectangle_membership]
  constructor
  · rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    by_contra h
    have hz := hP.1 (m 0) (by omega)
    have hc : biCoeff (toBiPolynomial P) (m 0) (m 1)=0 := by
      simp [biCoeff,hz]
    rw [toBiPolynomial_coeff] at hc
    have he : exponentPair.symm (m 0,m 1)=m := exponentPair.symm_apply_apply m
    rw [he] at hc
    exact (MvPolynomial.mem_support_iff.mp hm) hc
  · rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    by_contra h
    have hc := hP.2 (m 0) (m 1) (by omega)
    change biCoeff (toBiPolynomial P) (m 0) (m 1)=0 at hc
    rw [toBiPolynomial_coeff] at hc
    have he : exponentPair.symm (m 0,m 1)=m := exponentPair.symm_apply_apply m
    rw [he] at hc
    exact (MvPolynomial.mem_support_iff.mp hm) hc

theorem bi_factor_two_rows (r s : ℕ) (P : BiPoly)
    (hP : BiBounded (r+2) s P) (a b : ℝ) (hab : a≠b)
    (ha : eval a P=0) (hb : eval b P=0) :
    ∃R : BiPoly, BiBounded r s R ∧ mulRoot a (mulRoot b R)=P := by
  obtain ⟨Q,hQ,hQP⟩ := bi_factor_row (r+1) s P hP a ha
  have hbQ : eval b Q=0 := by
    rw [←hQP,eval_mulRoot] at hb
    exact (smul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr hab.symm)
  obtain ⟨R,hR,hRQ⟩ := bi_factor_row r s Q hQ b hbQ
  exact ⟨R,hR,by rw [hRQ,hQP]⟩

theorem evenTriangle_middle_rows_zero (s : ℕ) (hs : 2≤s)
    (node : Fin (2*s)→ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded s (s-1) P)
    (hv : ∀p q, (p,q)∈evenTriangle s → biEval (node p) (node q) P=0) :
    eval (node ⟨s-1,by omega⟩) P=0 ∧ eval (node ⟨s,by omega⟩) P=0 := by
  constructor
  · let f : Fin (s-1)→Fin (2*s) := fun i => ⟨i.val,by omega⟩
    apply eq_zero_of_node_roots (node ∘ f) (hn.comp (by
      intro i j h
      exact Fin.ext (show i.val=j.val from congrArg (fun x : Fin (2*s) => x.val) h))) Finset.univ
    · simpa only [Finset.card_univ,Fintype.card_fin] using
        bounded_eval_outer hP (node ⟨s-1,by omega⟩)
    · intro i _
      apply hv
      rw [evenTriangle_middle_left_row s hs]
      exact i.isLt
  · let f : Fin (s-1)→Fin (2*s) := fun i => ⟨s+1+i.val,by omega⟩
    apply eq_zero_of_node_roots (node ∘ f) (hn.comp (by
      intro i j h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [f] at this
      omega)) Finset.univ
    · simpa only [Finset.card_univ,Fintype.card_fin] using
        bounded_eval_outer hP (node ⟨s,by omega⟩)
    · intro i _
      apply hv
      rw [evenTriangle_middle_right_row s hs]
      dsimp [f]
      omega

theorem evenTriangle_end_columns_zero (s : ℕ) (hs : 2≤s)
    (node : Fin (2*s)→ℝ) (hn : Function.Injective node)
    (P : BiPoly) (hP : BiBounded (s-1) s P)
    (hv : ∀p q, (p,q)∈evenTriangle s → biEval (node p) (node q) P=0) :
    eval (node ⟨0,by omega⟩) (swapBi P)=0 ∧
      eval (node ⟨2*s-1,by omega⟩) (swapBi P)=0 := by
  constructor
  · let f : Fin (s-1)→Fin (2*s) := fun i => ⟨i.val+1,by omega⟩
    apply eq_zero_of_node_roots (node ∘ f) (hn.comp (by
      intro i j h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [f] at this
      omega)) Finset.univ
    · simpa only [Finset.card_univ,Fintype.card_fin] using
        bounded_eval_outer (biBounded_swap hP) (node ⟨0,by omega⟩)
    · intro i _
      change biEval _ _ (swapBi P)=0
      rw [biEval_swap]
      apply hv
      rw [evenTriangle_first_column s hs]
      dsimp [f]
      omega
  · let f : Fin (s-1)→Fin (2*s) := fun i => ⟨s+i.val,by omega⟩
    apply eq_zero_of_node_roots (node ∘ f) (hn.comp (by
      intro i j h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp [f] at this
      omega)) Finset.univ
    · simpa only [Finset.card_univ,Fintype.card_fin] using
        bounded_eval_outer (biBounded_swap hP) (node ⟨2*s-1,by omega⟩)
    · intro i _
      change biEval _ _ (swapBi P)=0
      rw [biEval_swap]
      apply hv
      rw [evenTriangle_last_column s hs]
      dsimp [f]
      omega

end Paper170

end
end

section

noncomputable section
open PolynomialModule Zarankiewicz MvPolynomial
namespace Paper170

theorem evalTwo_ext {P Q : Poly2} (h : ∀u v, evalTwo u v P=evalTwo u v Q) : P=Q := by
  apply MvPolynomial.funext
  intro t
  have ht : t = ![t 0,t 1] := by ext i; fin_cases i <;> rfl
  rw [ht]
  exact h (t 0) (t 1)

theorem evenTriangle_row_factorization (s : ℕ) (hs : 3≤s)
    (node : Fin (2*s)→ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P∈rectangle (s-1) (s-2))
    (hv : ∀p q, (p,q)∈evenTriangle s → evalTwo (node p) (node q) P=0) :
    ∃R : Poly2, R∈rectangle (s-3) (s-2) ∧
      P=(X 0-C (node ⟨s-1,by omega⟩))*(X 0-C (node ⟨s,by omega⟩))*R ∧
      ∀p q, (p,q)∈evenTriangle (s-1) →
        evalTwo (node (triangleMiddleEmbedding s (by omega) p))
          (node (triangleMiddleEmbedding s (by omega) q)) R=0 := by
  have hB : BiBounded s (s-1) (toBiPolynomial P) := by
    convert toBiPolynomial_bounded (s-1) (s-2) P hP using 1 <;> omega
  have hV : ∀p q, (p,q)∈evenTriangle s →
      biEval (node p) (node q) (toBiPolynomial P)=0 := by
    simpa only [toBiPolynomial_eval] using hv
  obtain ⟨hleft,hright⟩ := evenTriangle_middle_rows_zero s (by omega) node hn _ hB hV
  obtain ⟨Q,hQ,hQP⟩ := bi_factor_two_rows (s-2) (s-1) (toBiPolynomial P)
    (by convert hB using 1; omega) (node ⟨s-1,by omega⟩) (node ⟨s,by omega⟩)
    (hn.ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)) hleft hright
  let R := toBiPolynomial.symm Q
  have hR : R∈rectangle (s-3) (s-2) := by
    apply mem_rectangle_of_toBiPolynomial_bounded
    dsimp [R]
    rw [LinearEquiv.apply_symm_apply]
    convert hQ using 1 <;> omega
  have hf : P=(X 0-C (node ⟨s-1,by omega⟩))*(X 0-C (node ⟨s,by omega⟩))*R := by
    apply evalTwo_ext
    intro u v
    rw [←toBiPolynomial_eval,hQP.symm,biEval_mulRoot,biEval_mulRoot]
    have hQR : biEval u v Q=evalTwo u v R := by
      rw [←toBiPolynomial_eval]
      simp only [R,LinearEquiv.apply_symm_apply]
    rw [hQR]
    simp [evalTwo,mul_assoc]
  refine ⟨R,hR,hf,?_⟩
  intro p q hpq
  have hzero := hv (triangleMiddleEmbedding s (by omega) p)
    (triangleMiddleEmbedding s (by omega) q)
    ((evenTriangle_delete_middle s (by omega) p q).mpr hpq)
  rw [hf] at hzero
  have ha := triangleMiddleEmbedding_avoids s (by omega) p
  have h₁ : node (triangleMiddleEmbedding s (by omega) p)-node ⟨s-1,by omega⟩≠0 :=
    sub_ne_zero.mpr (hn.ne (by intro h; exact ha.1 (congrArg Fin.val h)))
  have h₂ : node (triangleMiddleEmbedding s (by omega) p)-node ⟨s,by omega⟩≠0 :=
    sub_ne_zero.mpr (hn.ne (by intro h; exact ha.2 (congrArg Fin.val h)))
  change (MvPolynomial.aeval _ _) = 0 at hzero
  simp only [map_mul,map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
    Matrix.cons_val_zero,Algebra.algebraMap_self,RingHom.id_apply] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero h₁ h₂)

theorem evenTriangle_column_factorization (s : ℕ) (hs : 3≤s)
    (node : Fin (2*s)→ℝ) (hn : Function.Injective node)
    (P : Poly2) (hP : P∈rectangle (s-2) (s-1))
    (hv : ∀p q, (p,q)∈evenTriangle s → evalTwo (node p) (node q) P=0) :
    ∃R : Poly2, R∈rectangle (s-2) (s-3) ∧
      P=(X 1-C (node ⟨0,by omega⟩))*(X 1-C (node ⟨2*s-1,by omega⟩))*R ∧
      ∀p q, (p,q)∈evenTriangle (s-1) →
        evalTwo (node (triangleEndEmbedding s (by omega) p))
          (node (triangleEndEmbedding s (by omega) q)) R=0 := by
  have hB : BiBounded (s-1) s (toBiPolynomial P) := by
    convert toBiPolynomial_bounded (s-2) (s-1) P hP using 1 <;> omega
  have hV : ∀p q, (p,q)∈evenTriangle s →
      biEval (node p) (node q) (toBiPolynomial P)=0 := by
    simpa only [toBiPolynomial_eval] using hv
  obtain ⟨hleft,hright⟩ := evenTriangle_end_columns_zero s (by omega) node hn _ hB hV
  obtain ⟨Q,hQ,hQP⟩ := bi_factor_two_rows (s-2) (s-1) (swapBi (toBiPolynomial P))
    (by convert biBounded_swap hB using 1; omega)
    (node ⟨0,by omega⟩) (node ⟨2*s-1,by omega⟩)
    (hn.ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)) hleft hright
  let R := toBiPolynomial.symm (swapBi Q)
  have hR : R∈rectangle (s-2) (s-3) := by
    apply mem_rectangle_of_toBiPolynomial_bounded
    dsimp [R]
    rw [LinearEquiv.apply_symm_apply]
    convert biBounded_swap hQ using 1 <;> omega
  have hf : P=(X 1-C (node ⟨0,by omega⟩))*(X 1-C (node ⟨2*s-1,by omega⟩))*R := by
    apply evalTwo_ext
    intro u v
    rw [←toBiPolynomial_eval,←biEval_swap (toBiPolynomial P),hQP.symm,
      biEval_mulRoot,biEval_mulRoot]
    have hQR : biEval v u Q=evalTwo u v R := by
      rw [←toBiPolynomial_eval]
      simp only [R,LinearEquiv.apply_symm_apply,biEval_swap]
    rw [hQR]
    simp [evalTwo,mul_assoc]
  refine ⟨R,hR,hf,?_⟩
  intro p q hpq
  have hzero := hv (triangleEndEmbedding s (by omega) p)
    (triangleEndEmbedding s (by omega) q)
    ((evenTriangle_delete_ends s (by omega) p q).mpr hpq)
  rw [hf] at hzero
  have ha := triangleEndEmbedding_avoids s (by omega) q
  have h₁ : node (triangleEndEmbedding s (by omega) q)-node ⟨0,by omega⟩≠0 :=
    sub_ne_zero.mpr (hn.ne (by intro h; exact ha.1 (congrArg Fin.val h)))
  have h₂ : node (triangleEndEmbedding s (by omega) q)-node ⟨2*s-1,by omega⟩≠0 :=
    sub_ne_zero.mpr (hn.ne (by intro h; exact ha.2 (congrArg Fin.val h)))
  change (MvPolynomial.aeval _ _) = 0 at hzero
  simp only [map_mul,map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
    Matrix.cons_val_one,Matrix.cons_val_zero,Algebra.algebraMap_self,RingHom.id_apply] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero h₁ h₂)

end Paper170

end
end

end OAI
