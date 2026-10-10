import OAI.NumberTheory.PowerFree.PointInterpolation

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
attribute [local instance] Classical.propDecidable

theorem totalDegree_int_map {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (p : MvPolynomial (Fin n) ℤ) :
    (MvPolynomial.map (Int.castRingHom K) p).totalDegree = p.totalDegree := by
  simp only [totalDegree, support_map_of_injective p (f := Int.castRingHom K)
    (Int.cast_injective (α := K))]

theorem eval_int_map {n : ℕ} {K : Type*} [Field K]
    (p : MvPolynomial (Fin n) ℤ) (z : Fin n → ℤ) :
    eval (fun l => (z l : K)) (MvPolynomial.map (Int.castRingHom K) p) = (eval z p : K) :=
  (map_eval (Int.castRingHom K) z p).symm

theorem integer_patch_step {n D : ℕ} {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (hD : affineDegree I ≤ D)
    (S : Finset (Fin n → ℤ)) (hSI : ∀ z ∈ S, PointOn I z)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ p : MvPolynomial (Fin n) K, p ∉ I ∧ p.totalDegree ≤ (n+1)*D ∧
      ∃ L : List (IntegerPatch n), L.length ≤ 1 ∧
        (∀ P ∈ L, P.On I ∧ P.Bounded D H ∧
          DeterminedInDegree I (fun z : S => z.val) D) ∧
        ∀ z ∈ S, eval (fun l => (z l : K)) p = 0 ∨
          ∃ P ∈ L, eval z P.minor ≠ 0 := by
  obtain hc | hd := bounded_cut_or_determined I (fun z : S => z.val)
    (fun p hp z => hSI z.val z.property p hp) D H hH (fun z => hz z.val z.property)
  · obtain ⟨G,hG,_,hvan,hnot⟩ := hc
    refine ⟨MvPolynomial.map (Int.castRingHom K) G,hnot,?_,[],by simp,by simp,?_⟩
    · rw [totalDegree_int_map]
      exact hG.trans (Nat.le_mul_of_pos_left D (Nat.succ_pos n))
    · intro z hzs
      left
      rw [eval_int_map, hvan ⟨z,hzs⟩, Int.cast_zero]
  · obtain ⟨P,hPI,hP⟩ := determined_integer_patch I hD (fun z : S => z.val) hd
      (fun z => hSI z.val z.property) H hH (fun z => hz z.val z.property)
    refine ⟨MvPolynomial.map (Int.castRingHom K) P.minor,hPI.2.2,?_,[P],by simp,?_,?_⟩
    · rw [totalDegree_int_map]
      exact (P.minor_degree_le hP).trans (Nat.mul_le_mul_right D (Nat.le_succ n))
    · simpa using And.intro hPI (And.intro hP hd)
    · intro z _
      by_cases h : eval z P.minor = 0
      · left
        rw [eval_int_map,h,Int.cast_zero]
      · exact Or.inr ⟨P,by simp,h⟩

end
section
open MvPolynomial
attribute [local instance] Classical.propDecidable

def EquationLock {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (S : Finset (Fin n → ℤ)) (D : ℕ) : Prop :=
  ∀ p : MvPolynomial (Fin n) K, p.totalDegree ≤ D →
    ((∀ z ∈ S, PointOn I z → eval (fun l => (z l : K)) p = 0) ↔ p ∈ I)

theorem PointOn.mono {n : ℕ} {K : Type*} [Field K]
    {I J : Ideal (MvPolynomial (Fin n) K)} (hIJ : I ≤ J) {z : Fin n → ℤ}
    (hz : PointOn J z) : PointOn I z := fun p hp => hz p (hIJ hp)

theorem equationLock_of_determined {n D E : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (S : Finset (Fin n → ℤ))
    (hS : ∀ z ∈ S, PointOn I z) (h : DeterminedInDegree I (fun z : S => z.val) D)
    (hED : E ≤ D) : EquationLock I S E := by
  intro p hp
  rw [← h p (hp.trans hED)]
  constructor
  · intro he z
    exact he z.val z.property (hS z.val z.property)
  · intro he z hz _
    exact he ⟨z,hz⟩

theorem EquationLock.of_filter {n D : ℕ} {K : Type*} [Field K]
    {I J : Ideal (MvPolynomial (Fin n) K)} (hIJ : I ≤ J)
    (S : Finset (Fin n → ℤ)) (h : EquationLock J (S.filter (PointOn I)) D) :
    EquationLock J S D := by
  intro p hp
  rw [← h p hp]
  constructor
  · intro he z hz hj
    exact he z (Finset.mem_filter.mp hz).1 hj
  · intro he z hz hj
    exact he z (Finset.mem_filter.mpr ⟨hz,hj.mono hIJ⟩) hj

def patchNextDegree (n D e : ℕ) : ℕ := ((n+1)*max e D)*e

def patchDegreeBudget (n D : ℕ) : ℕ → ℕ → ℕ
  | 0,e => max e D
  | h+1,e => max (max e D) (patchDegreeBudget n D h (patchNextDegree n D e))

def patchCountBudget (n D : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 1
  | h+1,e => 1+patchNextDegree n D e * patchCountBudget n D h (patchNextDegree n D e)

theorem le_patchDegreeBudget (n D h e : ℕ) : max e D ≤ patchDegreeBudget n D h e := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact Nat.le_max_left _ _

theorem one_le_patchCountBudget (n D h e : ℕ) : 1 ≤ patchCountBudget n D h e := by
  cases h <;> simp only [patchCountBudget] <;> omega

def GoodPatchPiece {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (S : Finset (Fin n → ℤ))
    (D h B : ℕ) (H : ℝ) (C : Ideal (MvPolynomial (Fin n) K) × IntegerPatch n) : Prop :=
  C.1.IsPrime ∧ I ≤ C.1 ∧ affineDimension C.1 ≤ h ∧ affineDegree C.1 ≤ B ∧
    C.2.On C.1 ∧ C.2.Bounded B H ∧ EquationLock C.1 S D

def PatchPieceCovers {n : ℕ} {K : Type*} [Field K]
    (C : Ideal (MvPolynomial (Fin n) K) × IntegerPatch n) (z : Fin n → ℤ) : Prop :=
  PointOn C.1 z ∧ eval z C.2.minor ≠ 0

theorem zeroDim_patch_cover {n D : ℕ} {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (hd : affineDimension I = 0)
    (hD : affineDegree I ≤ D) (S : Finset (Fin n → ℤ)) (hS : S.Nonempty)
    (hSI : ∀ z ∈ S, PointOn I z) (H : ℝ) (hH : 1 ≤ H)
    (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ P : IntegerPatch n, P.On I ∧ P.Bounded D H ∧
      EquationLock I S D ∧ ∀ z ∈ S, PatchPieceCovers (I,P) z := by
  let : Nonempty S := hS.to_subtype
  have hdet : DeterminedInDegree I (fun z : S => z.val) D :=
    zeroDim_determined I hd _ (fun p hp z => hSI z.val z.property p hp)
  obtain ⟨P,hPI,hP⟩ := determined_integer_patch I hD (fun z : S => z.val) hdet
    (fun z => hSI z.val z.property) H hH (fun z => hz z.val z.property)
  refine ⟨P,hPI,hP,equationLock_of_determined I S hSI hdet le_rfl,?_⟩
  intro z hzs
  refine ⟨hSI z hzs,?_⟩
  intro hzero
  apply hPI.2.2
  rw [zeroDim_eq_point I hd (fun l => (z l : K)) (hSI z hzs)]
  change eval (fun l => (z l : K)) (MvPolynomial.map (Int.castRingHom K) P.minor) = 0
  rw [eval_int_map,hzero,Int.cast_zero]

theorem list_flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length*B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem bounded_integer_patch_cover {n : ℕ} {K : Type u} [Field K] [CharZero K]
    (D h e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : affineDimension I ≤ h) (he : affineDegree I ≤ e)
    (S : Finset (Fin n → ℤ)) (hSI : ∀ z ∈ S, PointOn I z)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
      L.length ≤ patchCountBudget n D h e ∧
      (∀ C ∈ L, GoodPatchPiece I S D h (patchDegreeBudget n D h e) H C) ∧
      ∀ z ∈ S, ∃ C ∈ L, PatchPieceCovers C z := by
  classical
  induction h generalizing e I S with
  | zero =>
    by_cases hS : S.Nonempty
    · have hd : affineDimension I = 0 := Nat.eq_zero_of_le_zero hdim
      obtain ⟨P,hPI,hP,hl,hcov⟩ := zeroDim_patch_cover I hd
        (he.trans (by exact_mod_cast Nat.le_max_left e D)) S hS hSI H hH hz
      refine ⟨[(I,P)],by simp [patchCountBudget],?_,?_⟩
      · intro C hC
        have hC : C = (I,P) := by simpa using hC
        subst C
        refine ⟨inferInstance,le_rfl,hdim,?_,hPI,hP,?_⟩
        · exact he.trans (by exact_mod_cast Nat.le_max_left e D)
        · intro p hp
          exact hl p (hp.trans (Nat.le_max_right _ _))
      · intro z hzs
        exact ⟨(I,P),by simp,hcov z hzs⟩
    · refine ⟨[],by simp,by simp,?_⟩
      intro z hzs
      exact (hS ⟨z,hzs⟩).elim
  | succ h ih =>
    by_cases hS : S.Nonempty
    swap
    · refine ⟨[],by simp,by simp,?_⟩
      intro z hzs
      exact (hS ⟨z,hzs⟩).elim
    by_cases hd : affineDimension I = 0
    · obtain ⟨P,hPI,hP,hl,hcov⟩ := zeroDim_patch_cover I hd
        (he.trans (by exact_mod_cast Nat.le_max_left e D)) S hS hSI H hH hz
      have hB := le_patchDegreeBudget n D (h+1) e
      refine ⟨[(I,P)],?_,?_,?_⟩
      · simpa using one_le_patchCountBudget n D (h+1) e
      · intro C hC
        have hC : C = (I,P) := by simpa using hC
        subst C
        refine ⟨inferInstance,le_rfl,hdim,?_,hPI,hP.mono hB,?_⟩
        · exact he.trans (by exact_mod_cast (Nat.le_max_left e D).trans hB)
        · intro p hp
          exact hl p (hp.trans (Nat.le_max_right _ _))
      · intro z hzs
        exact ⟨(I,P),by simp,hcov z hzs⟩
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hd
    have hkh : k ≤ h := by omega
    obtain ⟨p,hp,hpD,L₀,hL₀,hgood₀,hcover₀⟩ := integer_patch_step I
      (he.trans (by exact_mod_cast Nat.le_max_left e D)) S hSI H hH hz
    let E := patchNextDegree n D e
    obtain ⟨Q,hcard,hQ,hcoverQ⟩ := bounded_cut_components I he p hp hpD hk
    let S' := fun q : Q => S.filter (PointOn q.val)
    have hc : ∀ q : Q, ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
        L.length ≤ patchCountBudget n D h E ∧
        (∀ C ∈ L, GoodPatchPiece q.val (S' q) D h (patchDegreeBudget n D h E) H C) ∧
        ∀ z ∈ S' q, ∃ C ∈ L, PatchPieceCovers C z := by
      intro q
      have hq := hQ q.val q.property
      let := hq.1
      apply ih E q.val (hq.2.2.1.le.trans hkh)
        (by simpa only [E,patchNextDegree,Nat.cast_mul] using hq.2.2.2) (S' q)
      · intro z hzs
        exact (Finset.mem_filter.mp hzs).2
      · intro z hzs
        exact hz z (Finset.mem_filter.mp hzs).1
    choose L hlen hgood hcover using hc
    let R := Q.attach.toList.flatMap L
    have hRlen : R.length ≤ Q.card * patchCountBudget n D h E := by
      simpa [R] using list_flatMap_length_le Q.attach.toList L (patchCountBudget n D h E)
        (fun q _ => hlen q)
    refine ⟨L₀.map (fun P => (I,P)) ++ R,?_,?_,?_⟩
    · simp only [List.length_append,List.length_map]
      exact (Nat.add_le_add hL₀ hRlen).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcard) 1)
    · intro C hC
      rcases List.mem_append.mp hC with hC | hC
      · obtain ⟨P,hPL,rfl⟩ := List.mem_map.mp hC
        obtain ⟨hPI,hP,hdet⟩ := hgood₀ P hPL
        have hB := le_patchDegreeBudget n D (h+1) e
        refine ⟨inferInstance,le_rfl,hdim,?_,hPI,hP.mono hB,?_⟩
        · exact he.trans (by exact_mod_cast (Nat.le_max_left e D).trans hB)
        · exact equationLock_of_determined I S hSI hdet (Nat.le_max_right _ _)
      · obtain ⟨q,_,hCL⟩ := List.mem_flatMap.mp hC
        obtain ⟨hpq,hIq,hdq,heq,hOn,hBound,hLock⟩ := hgood q C hCL
        have hB : patchDegreeBudget n D h E ≤ patchDegreeBudget n D (h+1) e := Nat.le_max_right _ _
        refine ⟨hpq,(hQ q.val q.property).2.1.trans hIq,hdq.trans (Nat.le_succ _),?_,
          hOn,hBound.mono hB,?_⟩
        · exact heq.trans (by exact_mod_cast hB)
        · exact hLock.of_filter hIq S
    · intro z hzs
      rcases hcover₀ z hzs with hpz | ⟨P,hPL,hPz⟩
      · obtain ⟨q,hq,hzq⟩ := hcoverQ (fun l => (z l : K)) (hSI z hzs) hpz
        obtain ⟨C,hCL,hCz⟩ := hcover ⟨q,hq⟩ z (Finset.mem_filter.mpr ⟨hzs,hzq⟩)
        refine ⟨C,List.mem_append_right _ ?_,hCz⟩
        exact List.mem_flatMap.mpr ⟨⟨q,hq⟩,by simp,hCL⟩
      · exact ⟨(I,P),List.mem_append_left _ (List.mem_map.mpr ⟨P,hPL,rfl⟩),hSI z hzs,hPz⟩

end
open MvPolynomial
attribute [local instance] Classical.propDecidable

def evaluationSpace {n : ℕ} (S : Finset (Fin n → ℤ)) (D : ℕ) :
    Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) D) where
  carrier := {p | ∀ z ∈ S, eval (fun l => (z l : ℂ)) p.val = 0}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq z hz; simpa using congrArg₂ (· + ·) (hp z hz) (hq z hz)
  smul_mem' := by intro a p hp z hz; simp [hp z hz]

noncomputable def evaluationCell {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) K))
    (z : Fin n → ℤ) (Q : Finset ℕ) : Finset (Fin n → ℤ) :=
  S.filter fun w => PointOn I w ∧ ∀ p ∈ Q, ∀ l, (p : ℤ) ∣ w l-z l

theorem evaluationSpace_antitone {n D : ℕ} {S T : Finset (Fin n → ℤ)}
    (hST : S ⊆ T) : evaluationSpace T D ≤ evaluationSpace S D := by
  intro p hp z hz
  exact hp z (hST hz)

theorem evaluationCell_antitone {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) K))
    (z : Fin n → ℤ) {Q R : Finset ℕ} (hQR : Q ⊆ R) :
    evaluationCell S I z R ⊆ evaluationCell S I z Q := by
  intro w hw
  obtain ⟨hw,hI,hres⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hw,hI,fun p hp l => hres p (hQR hp) l⟩

theorem evaluationCell_eq_of_congruent {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) K))
    (z w : Fin n → ℤ) (Q : Finset ℕ)
    (hzw : ∀ p ∈ Q, ∀ l, (p : ℤ) ∣ w l-z l) :
    evaluationCell S I z Q = evaluationCell S I w Q := by
  ext x
  simp only [evaluationCell,Finset.mem_filter]
  suffices (∀ p ∈ Q, ∀ l, (p : ℤ) ∣ x l-z l) ↔
      (∀ p ∈ Q, ∀ l, (p : ℤ) ∣ x l-w l) by tauto
  constructor
  · intro h p hp l
    have he : x l-w l = (x l-z l)-(w l-z l) := by ring
    rw [he]
    exact dvd_sub (h p hp l) (hzw p hp l)
  · intro h p hp l
    have he : x l-z l = (x l-w l)+(w l-z l) := by ring
    rw [he]
    exact dvd_add (h p hp l) (hzw p hp l)

theorem proper_cut_patch_cover {n h e D A : ℕ} {K : Type u}
    [Field K] [CharZero K] (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (he : affineDegree I ≤ e) (hd : affineDimension I = h+1)
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (hpD : p.totalDegree ≤ D)
    (S : Finset (Fin n → ℤ)) (H : ℝ) (hH : 1 ≤ H)
    (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
      L.length ≤ D*e*patchCountBudget n A h (D*e) ∧
      (∀ C ∈ L, GoodPatchPiece I S A h (patchDegreeBudget n A h (D*e)) H C) ∧
      ∀ z ∈ S, PointOn I z → eval (fun l => (z l : K)) p = 0 →
        ∃ C ∈ L, PatchPieceCovers C z := by
  classical
  obtain ⟨Q,hcard,hQ,hcoverQ⟩ := bounded_cut_components I he p hp hpD hd
  let S' := fun q : Q => S.filter (PointOn q.val)
  have hc : ∀ q : Q, ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
      L.length ≤ patchCountBudget n A h (D*e) ∧
      (∀ C ∈ L, GoodPatchPiece q.val (S' q) A h (patchDegreeBudget n A h (D*e)) H C) ∧
      ∀ z ∈ S' q, ∃ C ∈ L, PatchPieceCovers C z := by
    intro q
    have hq := hQ q.val q.property
    let := hq.1
    apply bounded_integer_patch_cover A h (D*e) q.val hq.2.2.1.le
      (by simpa only [Nat.cast_mul] using hq.2.2.2) (S' q)
    · intro z hzs; exact (Finset.mem_filter.mp hzs).2
    · exact hH
    · intro z hzs; exact hz z (Finset.mem_filter.mp hzs).1
  choose L hlen hgood hcover using hc
  let R := Q.attach.toList.flatMap L
  refine ⟨R,?_,?_,?_⟩
  · have hh := list_flatMap_length_le Q.attach.toList L (patchCountBudget n A h (D*e))
      (fun q _ => hlen q)
    have hh' : R.length ≤ Q.card * patchCountBudget n A h (D*e) := by
      simpa only [R,Finset.length_toList,Finset.card_attach] using hh
    exact hh'.trans (Nat.mul_le_mul_right _ hcard)
  · intro C hC
    obtain ⟨q,_,hCL⟩ := List.mem_flatMap.mp hC
    obtain ⟨hpq,hIq,hdq,heq,hOn,hBound,hLock⟩ := hgood q C hCL
    exact ⟨hpq,(hQ q.val q.property).2.1.trans hIq,hdq,heq,hOn,hBound,
      hLock.of_filter hIq S⟩
  · intro z hzs hIz hpz
    obtain ⟨q,hq,hzq⟩ := hcoverQ (fun l => (z l : K)) hIz hpz
    obtain ⟨C,hCL,hCz⟩ := hcover ⟨q,hq⟩ z (Finset.mem_filter.mpr ⟨hzs,hzq⟩)
    exact ⟨C,List.mem_flatMap.mpr ⟨⟨q,hq⟩,by simp,hCL⟩,hCz⟩

end QuarticPowerFree

end OAI
