import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ReverseRow

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def coordinateRow {n : ℕ} (i : Fin n) (c b : ℚ) : Row n :=
  ⟨fun j => if j=i then c else 0,b⟩

lemma coordinateRow_value {n : ℕ} (i : Fin n) (c b : ℚ) (x : Fin n → ℝ) :
    (coordinateRow i c b).realValue x=(c:ℝ)*x i := by
  simp [coordinateRow,Row.realValue,apply_ite]

def boxRows (n B : ℕ) : List (Row n) :=
  List.ofFn (fun i => coordinateRow i 1 B) ++ List.ofFn (fun i => coordinateRow i (-1) B)

lemma boxRows_holds {n B : ℕ} (x : Fin n → ℝ) :
    (∀ q∈boxRows n B, q.RealHolds x) ↔ ∀ j, |x j|≤(B:ℝ) := by
  have he (i : Fin n) (c : ℚ) : (coordinateRow i c B).RealHolds x ↔ (c:ℝ)*x i≤(B:ℝ) := by
    change (coordinateRow i c B).realValue x≤((B:ℚ):ℝ) ↔ _
    rw [coordinateRow_value,Rat.cast_natCast]
  simp only [boxRows,List.forall_mem_append,List.forall_mem_ofFn_iff,he]
  constructor
  · rintro ⟨hp,hm⟩ j
    have hpj : x j≤(B:ℝ) := by simpa using hp j
    have hmj : -x j≤(B:ℝ) := by simpa using hm j
    exact abs_le.mpr ⟨by linarith,hpj⟩
  · intro h
    constructor
    · intro j
      simpa using (abs_le.mp (h j)).2
    · intro j
      have hh := (abs_le.mp (h j)).1
      simpa using (show -x j≤(B:ℝ) by linarith)

def withBox {n : ℕ} (rows : List (Row n)) (B : ℕ) := rows++boxRows n B

def finalFace {n : ℕ} (rows : List (Row n)) (B : ℕ) : List (Row n) :=
  selectFace (withBox rows B) B (withBox rows B) []

def rowMatrix {n : ℕ} (rows : List (Row n)) : Matrix (Fin rows.length) (Fin n) ℚ :=
  fun i j => rows[i].coeff j

def rowBounds {n : ℕ} (rows : List (Row n)) : Fin rows.length → ℚ :=
  fun i => rows[i].bound

lemma rowMatrix_region {n : ℕ} (rows : List (Row n)) (x : Fin n → ℝ) :
    x∈region (fun i j => (rowMatrix rows i j:ℝ)) (fun i => (rowBounds rows i:ℝ)) ↔
      ∀ q∈rows, q.RealHolds x := by
  constructor
  · intro h q hq
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hq
    have hh : rows[i].RealHolds x := h ⟨i,hi⟩
    rwa [he] at hh
  · intro h i
    exact h _ (List.getElem_mem _)

lemma finalFace_feasible {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    ∃ x, Face (withBox rows B) (finalFace rows B) B x := by
  apply (selectFace_spec (withBox rows B) B (withBox rows B) [] ?_).2.1
  obtain ⟨x,hx,hb⟩ := hfeas
  refine ⟨x,⟨?_,by simp,hb⟩⟩
  exact List.forall_mem_append.mpr ⟨hx,(boxRows_holds x).mpr hb⟩

theorem finalFace_kernel {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ)))
    (u : Fin n → ℝ) (hu : ∀ q∈finalFace rows B, ∑ j, (q.coeff j:ℝ)*u j=0) : u=0 := by
  let base := withBox rows B
  let picked := finalFace rows B
  let all := faceRows base picked
  obtain ⟨x0,hx0⟩ := finalFace_feasible rows B hfeas
  have hbox (x : Fin n → ℝ) (hx : ∀ q∈all, q.RealHolds x) : ∀ j, |x j|≤(B:ℝ) := by
    have hh := (faceRows_holds base picked x).mp hx
    exact (boxRows_holds x).mp (fun q hq => hh.1 q (List.mem_append_right _ hq))
  obtain ⟨x,hx,hker⟩ := bounded_extreme (fun i j => (rowMatrix all i j:ℝ))
    (fun i => (rowBounds all i:ℝ)) B
    ⟨x0,(rowMatrix_region all x0).mpr ((faceRows_holds base picked x0).mpr ⟨hx0.1,hx0.2.1⟩)⟩
    (fun x hx j => abs_le.mp (hbox x ((rowMatrix_region all x).mp hx) j))
  have hxp : Face base picked B x := by
    have hh := (rowMatrix_region all x).mp hx
    have hf := (faceRows_holds base picked x).mp hh
    exact ⟨hf.1,hf.2,hbox x hh⟩
  have hf0 : ∃ y, Face base [] B y := ⟨x0,⟨hx0.1,by simp,hx0.2.2⟩⟩
  have hactive := (selectFace_spec base B base [] hf0).2.2 x hxp
  apply hker u
  intro i hi
  have hm : all[i]∈all := List.getElem_mem _
  change all[i].realValue x=(all[i].bound:ℝ) at hi
  change (∑ j, (all[i].coeff j:ℝ)*u j)=0
  rcases List.mem_append.mp hm with hm|hm
  · rcases List.mem_append.mp hm with hm|hm
    · exact hu _ (hactive _ hm hi)
    · exact hu _ hm
  · obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
    rw [←he]
    simp only [reverseRow,Rat.cast_neg,neg_mul,Finset.sum_neg_distrib,hu q hq,neg_zero]

end MetricKMedianRecovery.Ellipsoid

namespace MetricKMedianRecovery.PositiveSolve
open Matrix
open scoped BigOperators

def freezeVec {n : ℕ} (v : Fin n → ℚ) : Fin n → ℚ :=
  let a := Vector.ofFn v
  fun i => a[i]

def freezeMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  let a := Vector.ofFn (fun i => Vector.ofFn (M i))
  fun i j => a[i][j]

@[simp] lemma freezeVec_eq {n : ℕ} (v : Fin n → ℚ) : freezeVec v=v := by
  funext i
  simp [freezeVec]
@[simp] lemma freezeMat_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : freezeMat M=M := by
  funext i j
  simp [freezeMat]

def schur {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => M i.succ j.succ-M i.succ 0*M 0 j.succ/M 0 0

def rhs {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (b : Fin (n+1) → ℚ) : Fin n → ℚ :=
  fun i => b i.succ-M i.succ 0*b 0/M 0 0

def solve : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → (Fin n → ℚ) → (Fin n → ℚ)
  | 0,_,_ => Fin.elim0
  | n+1,M,b =>
    let S := freezeMat (schur M)
    let d := freezeVec (rhs M b)
    let x := freezeVec (solve n S d)
    freezeVec (Fin.cons ((b 0-∑ j, M 0 j.succ*x j)/M 0 0) x)

lemma schur_mulVec {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (x : Fin n → ℚ) (i : Fin n) :
    (schur M *ᵥ x) i = (∑ j, M i.succ j.succ*x j)-
      M i.succ 0*(∑ j, M 0 j.succ*x j)/M 0 0 := by
  simp only [mulVec,dotProduct,schur,sub_mul,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma schur_isHermitian {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hM : M.IsHermitian) : (schur M).IsHermitian := by
  have he (i j : Fin (n+1)) : M j i=M i j := by simpa using congrFun (congrFun hM i) j
  ext i j
  simp only [conjTranspose_apply,star_trivial,schur]
  rw [he j.succ i.succ,he 0 i.succ,he j.succ 0]
  ring

lemma schur_posDef {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hM : M.PosDef) : (schur M).PosDef := by
  apply posDef_iff_dotProduct_mulVec.mpr
  refine ⟨schur_isHermitian M hM.1,?_⟩
  intro x hx
  let z : Fin (n+1) → ℚ := Fin.cons (-(∑ j, M 0 j.succ*x j)/M 0 0) x
  have hz : z≠0 := by
    intro he
    apply hx
    funext j
    exact congrFun he j.succ
  have hd : M 0 0≠0 := hM.diag_pos.ne'
  have hh : (M *ᵥ z) 0=0 := by
    simp only [mulVec,dotProduct,Fin.sum_univ_succ,z,Fin.cons_zero,Fin.cons_succ]
    field_simp
    ring
  have ht (i : Fin n) : (M *ᵥ z) i.succ=(schur M *ᵥ x) i := by
    rw [schur_mulVec]
    simp only [mulVec,dotProduct,Fin.sum_univ_succ,z,Fin.cons_zero,Fin.cons_succ]
    ring
  have hp := hM.dotProduct_mulVec_pos hz
  simpa only [star_trivial,dotProduct,Fin.sum_univ_succ,hh,mul_zero,zero_add,z,Fin.cons_succ,ht] using hp

theorem solve_correct (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ)
    (hM : M.PosDef) : M *ᵥ solve n M b=b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have hd : M 0 0≠0 := hM.diag_pos.ne'
    have hx := ih (schur M) (rhs M b) (schur_posDef M hM)
    simp only [solve,freezeVec_eq,freezeMat_eq]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [mulVec,dotProduct,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
      field_simp
      ring
    · have hi := congrFun hx i
      rw [schur_mulVec] at hi
      simp only [mulVec,dotProduct,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
      dsimp [rhs] at hi
      linear_combination hi

end MetricKMedianRecovery.PositiveSolve

end OAI
