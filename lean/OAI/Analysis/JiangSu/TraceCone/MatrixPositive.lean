import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.MatrixSums

namespace OAI

noncomputable section
open scoped NNReal ENNReal Topology

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem matrixLimit_positive_approximation (a : Positive (MatrixLimit A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (M : Positive (FinMatrix A n)),
      ‖a.1-(Positive.map (matrixLimitStage n) M).1‖ < ε := by
  have hc : Continuous (fun x : MatrixLimit A => star x*x) := continuous_star.mul continuous_id
  obtain ⟨δ,hδ,h⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := CFC.sqrt a.1)) ε hε
  obtain ⟨n,M,hM⟩ := matrixLimit_finite_approximation (CFC.sqrt a.1) hδ
  refine ⟨n,Positive.starMul M,?_⟩
  have hd : dist (matrixLimitStage n M) (CFC.sqrt a.1) < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hM
  have he : star (CFC.sqrt a.1)*CFC.sqrt a.1 = a.1 := by
    rw [(CFC.sqrt_nonneg a.1).star_eq, CFC.sqrt_mul_sqrt_self a.1 a.2]
  have hh := h hd
  rw [he, dist_eq_norm, norm_sub_rev] at hh
  simpa only [Positive.map, Positive.starMul, map_mul, map_star] using hh

theorem matrixLimit_cut_below_finite (a : Positive (MatrixLimit A)) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ (n : ℕ) (M : Positive (FinMatrix A n)),
      CuntzBelow (Positive.cut ε a) (Positive.map (matrixLimitStage n) M) := by
  obtain ⟨n,M,hM⟩ := matrixLimit_positive_approximation a (show (0 : ℝ) < ε from hε)
  exact ⟨n,M,cut_cuntzBelow_of_norm_sub_lt a _ ε hε hM⟩
end TraceCone
end

noncomputable section
open scoped CStarAlgebra

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixPermute {n : ℕ} (e : Equiv.Perm (Fin n)) : FinMatrix A n →⋆ₙₐ[ℂ] FinMatrix A n :=
  (CStarMatrix.reindexₐ ℂ A e).toNonUnitalStarAlgHom

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem matrixPermute_entry {n : ℕ} (e : Equiv.Perm (Fin n))
    (M : FinMatrix A n) (i j : Fin n) : matrixPermute e M (e i) (e j) = M i j := by
  rw [matrixPermute.eq_1]
  change M (e.symm (e i)) (e.symm (e j)) = M i j
  simp

private theorem positive_square_root {B : Type*} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] (a : Positive B) :
    ∃ b : B, star b = b ∧ b*b = a.1 :=
  ⟨CFC.sqrt a.1, (CFC.sqrt_nonneg a.1).star_eq, CFC.sqrt_mul_sqrt_self a.1 a.2⟩

theorem matrixPermute_factorization {n : ℕ} (e : Equiv.Perm (Fin n))
    (a : Positive (FinMatrix A n)) :
    ∃ x : FinMatrix A n, star x*x = a.1 ∧ x*star x = matrixPermute e a.1 := by
  obtain ⟨b, hb, hbb⟩ := positive_square_root a
  let x : FinMatrix A n := CStarMatrix.ofMatrix (fun i j => b (e.symm i) j)
  refine ⟨x, ?_, ?_⟩
  · apply CStarMatrix.ext; intro i j
    change (∑ k : Fin n, star (b (e.symm k) i) * b (e.symm k) j) = a.1 i j
    rw [e.symm.sum_comp (fun k => star (b k i)*b k j)]
    change (star b*b) i j = a.1 i j
    rw [hb,hbb]
  · apply CStarMatrix.ext; intro i j
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨j,rfl⟩ := e.surjective j
    rw [matrixPermute_entry]
    change (∑ k : Fin n, b (e.symm (e i)) k * star (b (e.symm (e j)) k)) = a.1 i j
    simp only [Equiv.symm_apply_apply]
    change (b*star b) i j = a.1 i j
    rw [hb,hbb]

theorem matrixPermute_cuntzClass {n : ℕ} (e : Equiv.Perm (Fin n))
    (a : Positive (FinMatrix A n)) :
    CuntzClass.mk (Positive.map (matrixPermute e) a) = CuntzClass.mk a := by
  obtain ⟨x,hx,hy⟩ := matrixPermute_factorization e a
  have hs : Positive.starMul x = a := Subtype.ext hx
  have ht : Positive.mulStar x = Positive.map (matrixPermute e) a := Subtype.ext hy
  apply (CuntzClass.mk_eq_mk_iff _ _).mpr
  rw [← ht,← hs]
  exact ⟨mulStar_cuntzBelow_starMul x,starMul_cuntzBelow_mulStar x⟩

omit [PartialOrder A] [StarOrderedRing A] in
theorem matrix_supported_permutation {ι : Type*} [Finite ι] {n : ℕ}
    (f g : ι ↪ Fin n) (M N : FinMatrix A n)
    (hentries : ∀ i j, M (f i) (f j) = N (g i) (g j))
    (hM : ∀ i j, i ∉ Set.range f ∨ j ∉ Set.range f → M i j = 0)
    (hN : ∀ i j, i ∉ Set.range g ∨ j ∉ Set.range g → N i j = 0) :
    ∃ e : Equiv.Perm (Fin n), matrixPermute e M = N := by
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair f g f.injective g.injective
  refine ⟨e,?_⟩
  apply CStarMatrix.ext; intro i j
  obtain ⟨p,rfl⟩ := e.surjective i
  obtain ⟨q,rfl⟩ := e.surjective j
  rw [matrixPermute_entry]
  have hout (p : Fin n) (hp : p ∉ Set.range f) : e p ∉ Set.range g := by
    rintro ⟨i,hi⟩
    exact hp ⟨i,e.injective ((he i).trans hi)⟩
  by_cases hp : p ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hp
    by_cases hq : q ∈ Set.range f
    · obtain ⟨b,rfl⟩ := hq
      rw [he,he,hentries]
    · rw [hM _ _ (Or.inr hq),hN _ _ (Or.inr (hout q hq))]
  · rw [hM _ _ (Or.inl hp),hN _ _ (Or.inl (hout p hp))]

theorem matrix_supported_cuntzClass {ι : Type*} [Finite ι] {n : ℕ}
    (f g : ι ↪ Fin n) (a b : Positive (FinMatrix A n))
    (hentries : ∀ i j, a.1 (f i) (f j) = b.1 (g i) (g j))
    (ha : ∀ i j, i ∉ Set.range f ∨ j ∉ Set.range f → a.1 i j = 0)
    (hb : ∀ i j, i ∉ Set.range g ∨ j ∉ Set.range g → b.1 i j = 0) :
    CuntzClass.mk a = CuntzClass.mk b := by
  obtain ⟨e,he⟩ := matrix_supported_permutation f g a.1 b.1 hentries ha hb
  have h : Positive.map (matrixPermute e) a = b := Subtype.ext he
  rw [← h,matrixPermute_cuntzClass]
end TraceCone

namespace TraceCone
variable {A : Type*} [NonUnitalCStarAlgebra A]

def matrixInterleaveRaw (n : ℕ) :
    (FinMatrix A n × FinMatrix A n) →⋆ₙₐ[ℂ] CStarMatrix (Fin n × Fin 2) (Fin n × Fin 2) A where
  toFun P := CStarMatrix.ofMatrix (fun i j =>
    if i.2 = j.2 then if i.2 = 0 then P.1 i.1 j.1 else P.2 i.1 j.1 else 0)
  map_zero' := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change (if r = s then if r = 0 then (0 : A) else 0 else 0) = 0
    simp
  map_add' P Q := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change (if r = s then if r = 0 then P.1 i j + Q.1 i j else P.2 i j + Q.2 i j else (0 : A)) =
      (if r = s then if r = 0 then P.1 i j else P.2 i j else (0 : A)) +
      (if r = s then if r = 0 then Q.1 i j else Q.2 i j else (0 : A))
    fin_cases r <;> fin_cases s <;> simp
  map_mul' P Q := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change (if r = s then if r = 0 then ∑ k : Fin n, P.1 i k * Q.1 k j
      else ∑ k : Fin n, P.2 i k * Q.2 k j else (0 : A)) =
      ∑ k : Fin n × Fin 2,
        (if r = k.2 then if r = 0 then P.1 i k.1 else P.2 i k.1 else (0 : A)) *
        (if k.2 = s then if k.2 = 0 then Q.1 k.1 j else Q.2 k.1 j else (0 : A))
    fin_cases r <;> fin_cases s <;> simp [Fintype.sum_prod_type]
  map_smul' c P := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change (if r = s then if r = 0 then c • P.1 i j else c • P.2 i j else (0 : A)) =
      c • (if r = s then if r = 0 then P.1 i j else P.2 i j else (0 : A))
    fin_cases r <;> fin_cases s <;> simp
  map_star' P := by
    apply CStarMatrix.ext; rintro ⟨i,r⟩ ⟨j,s⟩
    change (if r = s then if r = 0 then star (P.1 j i) else star (P.2 j i) else (0 : A)) =
      star (if s = r then if s = 0 then P.1 j i else P.2 j i else (0 : A))
    fin_cases r <;> fin_cases s <;> simp

lemma matrixInterleaveRaw_injective (n : ℕ) : Function.Injective (matrixInterleaveRaw (A := A) n) := by
  intro P Q h
  rw [matrixInterleaveRaw.eq_1] at h
  apply Prod.ext
  · apply CStarMatrix.ext; intro i j
    have hh := congrArg (fun M : CStarMatrix (Fin n × Fin 2) (Fin n × Fin 2) A => M (i,0) (j,0)) h
    change P.1 i j = Q.1 i j at hh
    exact hh
  · apply CStarMatrix.ext; intro i j
    have hh := congrArg (fun M : CStarMatrix (Fin n × Fin 2) (Fin n × Fin 2) A => M (i,1) (j,1)) h
    change P.2 i j = Q.2 i j at hh
    exact hh

def matrixInterleave (n : ℕ) : (FinMatrix A n × FinMatrix A n) →⋆ₙₐ[ℂ] FinMatrix A (n*2) :=
  (CStarMatrix.reindexₐ ℂ A finProdFinEquiv).toNonUnitalStarAlgHom.comp (matrixInterleaveRaw n)

lemma matrixInterleave_injective (n : ℕ) : Function.Injective (matrixInterleave (A := A) n) :=
  (CStarMatrix.reindexₐ ℂ A finProdFinEquiv).injective.comp (matrixInterleaveRaw_injective n)

variable [PartialOrder A] [StarOrderedRing A]

theorem matrixInterleave_isometry (n : ℕ) : Isometry (matrixInterleave (A := A) n) :=
  NonUnitalStarAlgHom.isometry _ (matrixInterleave_injective n)

@[simp] theorem matrixInterleave_norm (n : ℕ) (P : FinMatrix A n × FinMatrix A n) :
    ‖matrixInterleave n P‖ = max ‖P.1‖ ‖P.2‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixInterleave_injective n) P

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem matrixInterleave_entry (n : ℕ) (P : FinMatrix A n × FinMatrix A n)
    (i j : Fin n) (r s : Fin 2) :
    matrixInterleave n P (finProdFinEquiv (i,r)) (finProdFinEquiv (j,s)) =
      if r = s then if r = 0 then P.1 i j else P.2 i j else 0 := by
  have h (x y : Fin n × Fin 2) :
      matrixInterleave n P (finProdFinEquiv x) (finProdFinEquiv y) =
        matrixInterleaveRaw n P x y := by
    rw [matrixInterleave.eq_1]
    change matrixInterleaveRaw n P (finProdFinEquiv.symm (finProdFinEquiv x))
      (finProdFinEquiv.symm (finProdFinEquiv y)) = _
    simp only [Equiv.symm_apply_apply]
  exact h (i,r) (j,s)
end TraceCone
end

end OAI
