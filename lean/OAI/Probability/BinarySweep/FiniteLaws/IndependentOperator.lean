import Mathlib
import OAI.Probability.BinarySweep.Representations.FiniteUnitaryAverage

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma independent_reverse_product {R : Type*} [Semiring R] {n : ℕ}
    {X : Fin n → Type*} [∀j, Fintype (X j)] (A : (j : Fin n) → X j → R) :
    (List.ofFn (fun j => ∑a, A j a)).reverse.prod=
      ∑f : ∀j, X j, (List.ofFn (fun j => A j (f j))).reverse.prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton,ih]
    rw [←Equiv.sum_comp (Fin.consEquiv X),Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f _
    simp only [Fin.consEquiv,Equiv.coe_fn_mk,List.ofFn_succ,List.reverse_cons,
      List.prod_append,List.prod_singleton,Fin.cons_zero,Fin.cons_succ]

lemma weighted_reverse_product {R : Type*} [Semiring R] [Algebra ℂ R] {n : ℕ}
    (w : Fin n → ℂ) (A : Fin n → R) :
    (List.ofFn (fun j => w j • A j)).reverse.prod=
      (∏j,w j) • (List.ofFn A).reverse.prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton,
      Fin.prod_univ_succ]
    rw [ih,smul_mul_smul_comm,mul_comm (∏j : Fin n, w j.succ) (w 0)]

lemma independent_average_product {R : Type*} [Semiring R] [Algebra ℂ R] {n : ℕ}
    {X : Fin n → Type*} [∀j, Fintype (X j)]
    (w : (j : Fin n) → X j → ℂ) (A : (j : Fin n) → X j → R) :
    (∑f : ∀j, X j, (∏j,w j (f j)) •
      (List.ofFn (fun j => A j (f j))).reverse.prod)=
      (List.ofFn (fun j => ∑a, w j a • A j a)).reverse.prod := by
  rw [independent_reverse_product]
  exact Finset.sum_congr rfl (fun f _ => (weighted_reverse_product _ _).symm)

lemma reverse_product_norm_le_one {R : Type*} [NormedRing R] [NormOneClass R]
    {n : ℕ} (A : Fin n → R) (hA : ∀j, ‖A j‖≤1) :
    ‖(List.ofFn A).reverse.prod‖≤1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.reverse_cons,List.prod_append,List.prod_singleton]
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (ih _ (fun index => hA index.succ))).trans (hA 0))

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma pi_single_reverse {I G : Type*} [Fintype I] [DecidableEq I] [Group G]
    (f : I → G) (e : Fin (Fintype.card I) ≃ I) :
    (List.ofFn (fun j => Pi.mulSingle (e j) (f (e j)))).reverse.prod=f := by
  funext i
  have hh := List.prod_map_eq_pow_single (e.symm i)
    (fun j => (Pi.mulSingle (e j) (f (e j)) : I → G) i)
    (l := (List.ofFn (fun j : Fin (Fintype.card I) => j)).reverse) (by
      intro j hj _
      have hne : i ≠ e j := by
        intro he
        apply hj
        exact e.injective (he.symm.trans (e.apply_symm_apply i).symm)
      simp [Pi.mulSingle,hne])
  have hc : ((List.ofFn (fun j : Fin (Fintype.card I) => j)).reverse).count (e.symm i)=1 := by
    apply List.count_eq_one_of_mem
    · exact List.nodup_reverse.mpr (List.nodup_ofFn.mpr Function.injective_id)
    · simp
  rw [hc,pow_one,e.apply_symm_apply,Pi.mulSingle_eq_same] at hh
  simp only [List.map_reverse,List.map_ofFn,Function.comp_def] at hh
  change (Pi.evalMonoidHom (fun _ : I => G) i)
    ((List.ofFn (fun j => Pi.mulSingle (e j) (f (e j)))).reverse.prod)=f i
  rw [map_list_prod,List.map_reverse,List.map_ofFn]
  exact hh

variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def continuousRep (ρ : Representation ℂ G V) : G →* (V →L[ℂ] V) where
  toFun g := (ρ g).toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

lemma complexAverage_sum (ρ : Representation ℂ G V) (p : G → ℂ) :
    complexAverage ρ p=∑g,p g • continuousRep ρ g := by
  ext v
  simp [complexAverage_apply,continuousRep]

theorem pi_average_norm_le_one {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq G] [Nontrivial V]
    (ρ : Representation ℂ (I → G) V) (p : I → G → ℂ)
    (h : ∀i, ‖complexAverage (ρ.comp (MonoidHom.mulSingle (fun _ : I => G) i)) (p i)‖≤1) :
    ‖complexAverage ρ (fun f => ∏i,p i (f i))‖≤1 := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let E : (Fin (Fintype.card I) → G) ≃ (I → G) := Equiv.piCongrLeft (fun _ => G) e
  have he (f : Fin (Fintype.card I) → G) : ∀j, E f (e j)=f j := by
    intro j; simp [E,Equiv.piCongrLeft]
  have hf : complexAverage ρ (fun f => ∏i,p i (f i))=
      (List.ofFn (fun j => complexAverage
        (ρ.comp (MonoidHom.mulSingle (fun _ : I => G) (e j))) (p (e j)))).reverse.prod := by
    rw [complexAverage_sum,←Equiv.sum_comp E]
    simp_rw [←e.prod_comp (fun i => p i (E _ i))]
    have ht (f : Fin (Fintype.card I) → G) : continuousRep ρ (E f)=
        (List.ofFn (fun j => continuousRep ρ (Pi.mulSingle (e j) (f j)))).reverse.prod := by
      rw [←pi_single_reverse (E f) e,map_list_prod,List.map_reverse,List.map_ofFn]
      simp only [Function.comp_def,he]
    simp_rw [ht,he]
    rw [independent_average_product (X := fun _ => G)
      (fun j a => p (e j) a) (fun j a => continuousRep ρ (Pi.mulSingle (e j) a))]
    congr 3
    funext j
    rw [complexAverage_sum]
    rfl
  rw [hf]
  exact reverse_product_norm_le_one _ (fun j => h (e j))

lemma pi_comp_average_norm_le_one {I H : Type*} [Fintype I] [DecidableEq I] [DecidableEq G] [Group H] [Fintype H]
    [Nontrivial V] (ρ : Representation ℂ H V) (φ : (I → G) →* H)
    (p : G → ℂ) (hρ : ∀g v, ‖ρ g v‖=‖v‖)
    (hp : ∀σ : Representation ℂ G V, (∀g v, ‖σ g v‖=‖v‖) →
      ‖complexAverage σ p‖≤1) :
    ‖complexAverage (ρ.comp φ) (fun f => ∏i,p (f i))‖≤1 := by
  apply pi_average_norm_le_one
  intro i
  apply hp
  exact fun g v => hρ _ v

end BinaryCoordinateSweeps

end

end OAI
