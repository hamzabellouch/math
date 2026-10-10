import Mathlib
import OAI.NumberTheory.PrimePackets.InverseEntropy

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
namespace PrimeDegreePackets

 

lemma small_right_chart (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : X n,
      ∀ y ∈ (fun g => rightAction x g) '' matrixBall n δ,
      ∀ z ∈ (fun g => rightAction x g) '' matrixBall n δ,
      ∃ h ∈ matrixBall n r, rightAction y h = z := by
  obtain ⟨V,hV,_,hVi,hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset
    ((matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr))
  obtain ⟨δ,hδ,hδV⟩ := matrixBall_nhds_basis hV
  refine ⟨δ,hδ,?_⟩
  rintro x y ⟨u,hu,rfl⟩ z ⟨v,hv,rfl⟩
  refine ⟨u⁻¹*v,?_,?_⟩
  · apply hVV
    refine Set.mul_mem_mul ?_ (hδV hv)
    rw [← hVi]
    exact Set.inv_mem_inv.mpr (hδV hu)
  · simp only [rightAction_mul,mul_inv_cancel_left]

 

theorem compact_finite_observation {n : ℕ} (K : Set (X n)) (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) :
    ∃ k : ℕ, ∃ P : X n → (Fin k → Bool),
      (∀ a, MeasurableSet {x | P x = a}) ∧
      (∀ x, P x = (fun _ => false) ↔ x ∉ K) ∧
      ∀ a, a ≠ (fun _ => false) → ∀ x, P x = a → ∀ y, P y = a →
        x ∈ K ∧ y ∈ K ∧ ∃ h ∈ matrixBall n r, rightAction x h = y := by
  obtain ⟨δ,hδ,Hδ⟩ := small_right_chart n hr
  let U : X n → Set (X n) := fun x => (fun g => rightAction x g) '' matrixBall n δ
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U (fun x => right_ball_isOpen x δ) (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,1,one_mem_matrixBall n hδ,by simp [rightAction_one]⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm.trans
    (Equiv.refl s)
  let V : Fin (Fintype.card s) → Set (X n) := fun i => K ∩ U (e i)
  have hVm : ∀ i, MeasurableSet (V i) := fun i =>
    hK.isClosed.measurableSet.inter (right_ball_isOpen (e i).val δ).measurableSet
  have hVcov : K ⊆ ⋃ i, V i := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨y,hy⟩,hx,by simpa [V] using hxy⟩
  let P : X n → (Fin (Fintype.card s) → Bool) := fun x i => if x ∈ V i then true else false
  have hP : Measurable P := measurable_pi_iff.mpr fun i =>
    Measurable.ite (hVm i) measurable_const measurable_const
  have hbad (x : X n) : P x = (fun _ => false) ↔ x ∉ K := by
    constructor
    · intro hx hxK
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hVcov hxK)
      have H := congrFun hx i
      simp [P,hi] at H
    · intro hx
      funext i
      have H : x ∉ V i := fun h => hx h.1
      simp [P,H]
  refine ⟨Fintype.card s,P,fun a => hP (measurableSet_singleton a),hbad,?_⟩
  intro a ha x hx y hy
  have hxK : x ∈ K := by by_contra H; exact ha (hx.symm.trans ((hbad x).mpr H))
  have hyK : y ∈ K := by by_contra H; exact ha (hy.symm.trans ((hbad y).mpr H))
  refine ⟨hxK,hyK,?_⟩
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hVcov hxK)
  have Hxy := congrFun (hx.trans hy.symm) i
  have hiy : y ∈ V i := by
    by_contra H
    simp [P,hi,H] at Hxy
  exact Hδ (e i) x hi.2 y hiy.2

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem orbit_name_cover_of_reset {Y : Type*} {T : Y → Y} {R : Y → Y → Prop}
    {M : ℕ} (hM : 1 ≤ M) (hstep : StepCover T R M)
    (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad]
    (E : Set Y) (hinit : RelationDiameter R E)
    (hreset : ∀ k < N, ¬bad (k+1) → ∀ F ⊆ E,
      RelationDiameter R (T^[k] '' F) → RelationDiameter R (T^[k+1] '' F)) :
    ∃ s : Finset (Set Y), E ⊆ ⋃ F ∈ s, F ∧
      s.card ≤ M^(((Finset.range (N+1)).filter fun j => bad j).card) ∧
      ∀ F ∈ s, F ⊆ E ∧ ∀ j ≤ N, RelationDiameter R (T^[j] '' F) := by
  classical
  have hM0 : 0 < M := hM
  have aux : ∀ k ≤ N, ∃ s : Finset (Set Y), E ⊆ ⋃ F ∈ s, F ∧
      s.card ≤ M^((Finset.range (k+1)).filter fun j => bad j).card ∧
      ∀ F ∈ s, F ⊆ E ∧ ∀ j ≤ k, RelationDiameter R (T^[j] '' F) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨{E},by simp,?_,?_⟩
      · simp only [Finset.card_singleton]
        exact Nat.one_le_pow _ _ hM0
      · intro F hF
        have hFE : F = E := by simpa using hF
        subst F
        refine ⟨Set.Subset.refl _,?_⟩
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        simp only [Function.iterate_zero,Set.image_id]
        exact hinit
    | succ k ih =>
      obtain ⟨s,hcov,hcard,hs⟩ := ih (by omega)
      by_cases hb : bad (k+1)
      · choose F hFc hFp using fun C : s => stepCover_of_image hstep k C.val
          ((hs C.val C.property).2 k le_rfl)
        let t : Finset (Set Y) := s.attach.biUnion fun C => Finset.univ.image (F C)
        refine ⟨t,?_,?_,?_⟩
        · intro x hx
          obtain ⟨C,hC,hxC⟩ := Set.mem_iUnion₂.mp (hcov hx)
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hFc ⟨C,hC⟩ hxC)
          exact Set.mem_iUnion₂.mpr ⟨F ⟨C,hC⟩ i,
            Finset.mem_biUnion.mpr ⟨⟨C,hC⟩,by simp,Finset.mem_image.mpr ⟨i,by simp,rfl⟩⟩,hi⟩
        · have ht : t.card ≤ s.card*M := by
            calc
              t.card ≤ ∑ C ∈ s.attach, (Finset.univ.image (F C)).card := Finset.card_biUnion_le
              _ ≤ ∑ _C ∈ s.attach, M := Finset.sum_le_sum fun C _ =>
                (Finset.card_image_le).trans_eq (by simp)
              _ = s.card*M := by simp
          calc
            t.card ≤ s.card*M := ht
            _ ≤ M^((Finset.range (k+1)).filter fun j => bad j).card *M :=
              Nat.mul_le_mul_right M hcard
            _ = _ := by
              rw [Finset.range_add_one (n := k+1),Finset.filter_insert]
              simp only [hb,ite_true]
              rw [Finset.card_insert_of_notMem, pow_succ]
              simp only [Finset.mem_filter,Finset.mem_range,lt_self_iff_false,false_and,not_false_eq_true]
        · intro C hC
          obtain ⟨D,hD,hCi⟩ := Finset.mem_biUnion.mp hC
          obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hCi
          refine ⟨(hFp D i).1.trans (hs D.val D.property).1,?_⟩
          intro j hj
          by_cases heq : j = k+1
          · subst j
            exact (hFp D i).2
          · have hd := (hs D.val D.property).2 j (by omega)
            intro x hx y hy
            exact hd x (Set.image_mono (hFp D i).1 hx) y (Set.image_mono (hFp D i).1 hy)
      · refine ⟨s,hcov,?_,?_⟩
        · simpa only [Finset.range_add_one (n := k+1),Finset.filter_insert,hb,ite_false] using hcard
        · intro C hC
          refine ⟨(hs C hC).1,?_⟩
          intro j hj
          by_cases heq : j = k+1
          · subst j
            exact hreset k (by omega) hb C (hs C hC).1 ((hs C hC).2 k le_rfl)
          · exact (hs C hC).2 j (by omega)
  exact aux N le_rfl

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix
namespace PrimeDegreePackets

 

lemma stepCover_of_matrix_expansion {n : ℕ} (D : G n ≃* G n) {L : ℝ}
    (hL : 0 ≤ L) (hexpand : ∀ r : ℝ, 0 < r → D '' matrixBall n r ⊆ matrixBall n (L*r)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℝ, 0 < r → L*r ≤ 1 →
      StepCover D (fun g h => g⁻¹*h ∈ matrixBall n r) M := by
  obtain ⟨M,hM,HM⟩ := small_matrix_ball_cover n hL
  refine ⟨M,hM,?_⟩
  intro r hr hrL E hE
  by_cases hne : E.Nonempty
  · obtain ⟨g,hg⟩ := hne
    obtain ⟨F,hcov,hF⟩ := HM r hr hrL
    refine ⟨fun i => E ∩ (fun h => D (g⁻¹*h)) ⁻¹' F i,?_,?_⟩
    · intro h hh
      have Hin : D (g⁻¹*h) ∈ matrixBall n (L*r) := hexpand r hr ⟨_,hE g hg h hh,rfl⟩
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcov Hin)
      exact Set.mem_iUnion.mpr ⟨i,hh,hi⟩
    · intro i
      refine ⟨Set.inter_subset_left,?_⟩
      rintro u ⟨h,hh,rfl⟩ v ⟨k,hk,rfl⟩
      have H := (hF i).2 _ hh.2 _ hk.2
      simpa only [map_mul,map_inv,_root_.mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel_left,
        inv_mul_cancel_left] using H
  · refine ⟨fun _ => ∅,?_,?_⟩
    · simp only [Set.not_nonempty_iff_eq_empty] at hne
      simp [hne]
    · intro i
      simp [RelationDiameter]

lemma diagonalOneParameter_zero {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) :
    diagonalOneParameter ell hell 0 = 1 := by
  apply Subtype.ext
  ext i j
  simp [diagonalOneParameter]

lemma diagonalOneParameter_add {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (s t : ℝ) : diagonalOneParameter ell hell (s+t) =
      diagonalOneParameter ell hell s * diagonalOneParameter ell hell t := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_add,Real.exp_add]

lemma diagonalOneParameter_neg {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (t : ℝ) : diagonalOneParameter ell hell (-t) = (diagonalOneParameter ell hell t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← diagonalOneParameter_add,neg_add_cancel,diagonalOneParameter_zero]

lemma diagonalOneParameter_nat {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (k : ℕ) : diagonalOneParameter ell hell (k:ℝ) = (diagonalOneParameter ell hell 1)^k := by
  induction k with
  | zero => simp [diagonalOneParameter_zero]
  | succ k ih => rw [Nat.cast_add,Nat.cast_one,diagonalOneParameter_add,ih,pow_succ]

 

lemma diagonal_conjugation_expansion {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ r : ℝ, 0 < r →
      (MulAut.conj (diagonalOneParameter ell hell (-1))) '' matrixBall n r ⊆ matrixBall n (L*r) := by
  let L : ℝ := 1 + ∑ i : Fin n, ∑ j : Fin n, Real.exp (ell j-ell i)
  have hsum : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Real.exp (ell j-ell i) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
  refine ⟨L,by dsimp [L]; linarith,?_⟩
  rintro r hr g ⟨h,hh,rfl⟩ i j
  have he : (MulAut.conj (diagonalOneParameter ell hell (-1)) h).1 i j =
      Real.exp (ell j-ell i)*h.1 i j := by
    change (diagonalOneParameter ell hell (-1)*h*(diagonalOneParameter ell hell (-1))⁻¹).1 i j = _
    rw [← diagonalOneParameter_neg]
    convert conjugation_entry ell hell h (-1) i j using 1
    congr 2
    ring
  have hLij : Real.exp (ell j-ell i) ≤ L := by
    have H : Real.exp (ell j-ell i) ≤ ∑ i : Fin n, ∑ j : Fin n, Real.exp (ell j-ell i) :=
      (Finset.single_le_sum (f := fun k : Fin n => Real.exp (ell k-ell i))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n, Real.exp (ell l-ell k))
          (fun _ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
          (Finset.mem_univ i))
    dsimp [L]
    linarith
  change |(MulAut.conj (diagonalOneParameter ell hell (-1)) h).1 i j -
    (1 : Matrix (Fin n) (Fin n) ℝ) i j| < L*r
  rw [he]
  by_cases hij : i = j
  · subst j
    simpa only [sub_self,Real.exp_zero,one_mul] using (hh i i).trans_le
      (le_mul_of_one_le_left hr.le (by dsimp [L]; linarith))
  · have Hh : |h.1 i j| < r := by simpa only [Matrix.one_apply_ne hij,sub_zero] using hh i j
    simp only [Matrix.one_apply_ne hij,sub_zero]
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact (mul_lt_mul_of_pos_left Hh (Real.exp_pos _)).trans_le
      (mul_le_mul_of_nonneg_right hLij hr.le)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma rightAction_iterate {n : ℕ} (a : G n) (k : ℕ) (x : X n) :
    (fun y => rightAction y a)^[k] x = rightAction x (a^k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',ih,rightAction_mul,pow_succ]

lemma rightAction_conjugation {n : ℕ} (a : G n) (x : X n) (g : G n) :
    rightAction (rightAction x g) a =
      rightAction (rightAction x a) (MulAut.conj a⁻¹ g) := by
  simp only [rightAction_mul,MulAut.conj_apply,inv_inv]
  congr 1
  group

lemma rightAction_iterate_conjugation {n : ℕ} (a : G n) (x : X n) (g : G n) (k : ℕ) :
    (fun y => rightAction y a)^[k] (rightAction x g) =
      rightAction ((fun y => rightAction y a)^[k] x) ((MulAut.conj a⁻¹)^[k] g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,rightAction_conjugation]
    simp only [Function.iterate_succ_apply']

 

theorem homogeneous_lifted_name_cover {n : ℕ} (a : G n) {L r ρ : ℝ} {M : ℕ}
    (hL : 1 ≤ L) (hr : 0 < r) (hρr : ρ ≤ r) (hM : 1 ≤ M)
    (hexpand : (MulAut.conj a⁻¹) '' matrixBall n r ⊆ matrixBall n (L*r))
    (hstep : StepCover (MulAut.conj a⁻¹) (fun g h => g⁻¹*h ∈ matrixBall n r) M)
    (K : Set (X n))
    (hinj : ∀ y ∈ K, Set.InjOn (fun g => rightAction y g) (matrixBall n (L*r)))
    {α : Type*} (P : X n → α) (bad : α → Prop) [DecidablePred bad]
    (hfine : ∀ b, ¬bad b → ∀ y, P y = b → ∀ z, P z = b →
      y ∈ K ∧ z ∈ K ∧ ∃ h ∈ matrixBall n ρ, rightAction y h = z)
    (x : X n) (N : ℕ) (name : ℕ → α) (E : Set (G n))
    (hinit : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) E)
    (hname : ∀ g ∈ E, ∀ j ≤ N,
      P ((fun y => rightAction y a)^[j] (rightAction x g)) = name j) :
    ∃ s : Finset (Set (G n)), E ⊆ ⋃ F ∈ s, F ∧
      s.card ≤ M^((Finset.range (N+1)).filter fun j => bad (name j)).card ∧
      ∀ F ∈ s, F ⊆ E ∧ ∀ j ≤ N,
        RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r)
          ((MulAut.conj a⁻¹)^[j] '' F) := by
  apply orbit_name_cover_of_reset hM hstep N (fun j => bad (name j)) E hinit
  intro k hk hgood F hFE hF
  rintro u ⟨g,hg,rfl⟩ v ⟨h,hh,rfl⟩
  let D := MulAut.conj a⁻¹
  let T := fun y : X n => rightAction y a
  let u := D^[k+1] g
  let v := D^[k+1] h
  have huv : u⁻¹*v ∈ matrixBall n (L*r) := by
    have H := hexpand ⟨(D^[k] g)⁻¹*(D^[k] h),
      hF _ ⟨g,hg,rfl⟩ _ ⟨h,hh,rfl⟩,rfl⟩
    change D ((D^[k] g)⁻¹*(D^[k] h)) ∈ matrixBall n (L*r) at H
    rw [map_mul,map_inv] at H
    simpa only [u,v,Function.iterate_succ_apply'] using H
  have hgname : P (rightAction (T^[k+1] x) u) = name (k+1) := by
    rw [← rightAction_iterate_conjugation]
    exact hname g (hFE hg) (k+1) (by omega)
  have hhname : P (rightAction (T^[k+1] x) v) = name (k+1) := by
    rw [← rightAction_iterate_conjugation]
    exact hname h (hFE hh) (k+1) (by omega)
  obtain ⟨hyK,_,w,hw,hyw⟩ := hfine (name (k+1)) hgood _ hgname _ hhname
  have hrL : r ≤ L*r := le_mul_of_one_le_left hr.le hL
  have hwL := matrixBall_mono (hρr.trans hrL) hw
  have heq : u⁻¹*v = w := hinj _ hyK huv hwL (by
    change rightAction (rightAction (T^[k+1] x) u) (u⁻¹*v) =
      rightAction (rightAction (T^[k+1] x) u) w
    rw [hyw]
    simp only [rightAction_mul,mul_inv_cancel_left])
  change u⁻¹*v ∈ matrixBall n r
  rw [heq]
  exact matrixBall_mono hρr hw

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma conjugation_iterate {H : Type*} [Group H] (a g : H) (j : ℕ) :
    (MulAut.conj a⁻¹)^[j] g = (a^j)⁻¹*g*a^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [MulAut.conj_apply,inv_inv,pow_succ,_root_.mul_inv_rev]
    group

 

lemma branch_midpoint_tube {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (x : X n) (g h : G n) (t : ℕ) {r : ℝ}
    (h0 : g⁻¹*h ∈ matrixBall n r)
    (h2 : ((MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)^[2*t] g)⁻¹ *
      ((MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)^[2*t] h) ∈ matrixBall n r) :
    ∃ w ∈ twoSidedTube ell hell r (t:ℝ),
      rightAction ((fun y => rightAction y (diagonalOneParameter ell hell 1))^[t]
        (rightAction x g)) w =
        (fun y => rightAction y (diagonalOneParameter ell hell 1))^[t] (rightAction x h) := by
  let a := diagonalOneParameter ell hell 1
  let b := a^t
  let w := b⁻¹*(g⁻¹*h)*b
  refine ⟨w,?_,?_⟩
  · constructor
    · rw [diagonalOneParameter_neg,diagonalOneParameter_nat]
      have Hp : a^(2*t) = b*b := by dsimp [b]; rw [two_mul,pow_add]
      have He : (a^t)⁻¹*w*a^t =
          ((MulAut.conj a⁻¹)^[2*t] g)⁻¹*((MulAut.conj a⁻¹)^[2*t] h) := by
        simp only [conjugation_iterate,Hp]
        dsimp [w,b,a]
        group
      rw [He]
      exact h2
    · rw [diagonalOneParameter_neg,diagonalOneParameter_nat]
      have He : (diagonalOneParameter ell hell 1)^t*w*((diagonalOneParameter ell hell 1)^t)⁻¹ = g⁻¹*h := by
        dsimp [w,b,a]
        group
      rw [He]
      exact h0
  · rw [rightAction_iterate,rightAction_iterate,rightAction_mul,rightAction_mul,rightAction_mul]
    congr 1
    dsimp [w,b,a]
    group

 

lemma rightAction_iterate_measure_preimage {n : ℕ} (μ : Measure (X n)) (a : G n)
    (hT : MeasurePreserving (fun x => rightAction x a) μ μ) (t : ℕ) (S : Set (X n)) :
    μ ((fun x => (fun y => rightAction y a)^[t] x) ⁻¹' S) = μ S := by
  apply (hT.iterate t).measure_preimage_emb
  have heq : (fun x => rightAction x a)^[t] = fun x => rightAction x (a^t) :=
    funext (rightAction_iterate a t)
  rw [heq]
  exact (rightActionHomeomorph (a^t)).isOpenEmbedding.measurableEmbedding

 

theorem lifted_branch_mass {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X n))
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    (K : Set (X n)) {r : ℝ} (t : ℕ) (B : ℝ≥0∞)
    (hTube : ∀ y ∈ K, μ ((fun w => rightAction y w) '' twoSidedTube ell hell r t) ≤ B)
    (x : X n) (F : Set (G n))
    (hmid : ∀ g ∈ F, (fun y => rightAction y (diagonalOneParameter ell hell 1))^[t]
      (rightAction x g) ∈ K)
    (h0 : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) F)
    (h2 : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r)
      ((MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)^[2*t] '' F)) :
    μ ((fun g => rightAction x g) '' F) ≤ B := by
  by_cases hne : F.Nonempty
  · obtain ⟨g,hg⟩ := hne
    let T := fun y => rightAction y (diagonalOneParameter ell hell 1)
    let y := T^[t] (rightAction x g)
    have hsub : (fun g => rightAction x g) '' F ⊆
        (T^[t]) ⁻¹' ((fun w => rightAction y w) '' twoSidedTube ell hell r t) := by
      rintro z ⟨h,hh,rfl⟩
      exact branch_midpoint_tube ell hell x g h t (h0 g hg h hh)
        (h2 _ ⟨g,hg,rfl⟩ _ ⟨h,hh,rfl⟩)
    calc
      μ _ ≤ μ ((T^[t]) ⁻¹' ((fun w => rightAction y w) '' twoSidedTube ell hell r t)) := measure_mono hsub
      _ = μ ((fun w => rightAction y w) '' twoSidedTube ell hell r t) :=
        rightAction_iterate_measure_preimage μ _ hT t _
      _ ≤ B := hTube y (hmid g hg)
  · simp only [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

end PrimeDegreePackets
end
end

end OAI
