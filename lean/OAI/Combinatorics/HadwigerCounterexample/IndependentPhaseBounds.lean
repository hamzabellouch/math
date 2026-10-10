import OAI.Combinatorics.HadwigerCounterexample.ChannelFrameLaws
import OAI.Combinatorics.HadwigerCounterexample.PrimalChannelTests
import OAI.Combinatorics.HadwigerCounterexample.MatrixRankCounting

namespace OAI

/-! # Independent Phase Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {J K : Type} [Fintype J] [Fintype K]

abbrev PhasePair (p : Shape) (N : ℕ) := HCube p N × HCube p N
abbrev Party := Vec Bool

def uPhase (p : Shape) {N} (v : HCube p N) : Ambient p N →ₗ[F] F :=
  ∑ e : Comp p.g, mpair ((v e).2*(v e).1ᵀ) ∘ₗ LinearMap.proj e

def joinPhase (p : Shape) {N} (v : PhasePair p N) (o : Party) :=
  ∑ b : Bool, o b • uPhase p (onSide v b)

/-- Read the whole channel frames of a unit. -/
def listens (p : Shape) {n N} (x : UnitType p n N) : PhasePair p N :=
  Prod.map (hcube p) (hcube p) x

def tone (p : Shape) {n N} (x : UnitType p n N) (S : Party) (T : Ambient p N) :=
  joinPhase p (listens p x) S T

def pitch (p : Shape) {n N} (Δ : UnitType p n N → Ambient p N)
    (w : Wgt (UnitType p n N)) (S R : Party) :=
  avg (pairW w w) (fun x =>
    wsign (tone p x.1 R (Δ x.2)+tone p x.2 S (Δ x.1)))

theorem phase_actual (p : Shape) {n N} (x : Orient p n N) :
    uPhase p (hcube p x)=ufun x := by
  apply LinearMap.ext
  intro v
  simp only [uPhase,LinearMap.sum_apply]; rfl

private theorem perm_pair (A B : Mat J K) (M : Mat J J) :
    mpair (A*Bᵀ) M=mpair (M*B) A := by

  change (A*Bᵀ*Mᵀ).trace=(M*B*Aᵀ).trace

  rw [← Matrix.trace_transpose (M*B*Aᵀ),Matrix.transpose_mul,Matrix.transpose_mul,
    Matrix.transpose_transpose,Matrix.mul_assoc]

variable [DecidableEq J] [DecidableEq K]

private theorem iid_prodM (M : Mat J J) :
    avg (pairW (unif : Wgt (Mat J K)) unif) (fun x => wsign (mpair (x.2*x.1ᵀ) M)) =
      bp (- (M.rank:ℝ) * num K) := by
  classical
  rw [pairW_avg]
  obtain ⟨A,B,hA,hB,hM⟩ := rank_product M
  have he (y : Mat J K) :
      avg unif (fun a : Mat J K => wsign (mpair (a*yᵀ) M)) = ind (B*y=0) := by
    have ht : mpair (M*y)=0 ↔ B*y=0 := by
      rw [ show M*y=A*B*y from congrArg (·*y) hM.symm,Matrix.mul_assoc]
      constructor
      · intro h
        have he := mpair_nondeg _ h
        exact matrix_cancel_left hA (B*y) 0 (he.trans (Matrix.mul_zero A).symm)
      intro h
      rw [h,Matrix.mul_zero]
      exact LinearMap.ext fun x => by rw [mpair_comm,map_zero,LinearMap.zero_apply]
    simp_rw [perm_pair,wsign_lin]
    rw [ht]
  change avg unif (fun y => avg unif _) = _
  simp_rw [he]
  change pr unif _ = _
  have hf : pr unif (fun y : Mat J K => B*y=0)=bp (-num (Fin M.rank)*num K) := by
    have hx : Function.Injective Bᵀ.mulVec :=
      transpose_surj_iff.mp (by rw [transpose_transpose]; exact hB)
    simpa only [Matrix.transpose_transpose] using
      pr_gram_fixed hx (0:Mat (Fin M.rank) K)
  rw [hf,num,Fintype.card_fin]

omit [Fintype J] in
theorem wsign_sum (s : Finset J) (f : J → F) :
    wsign (∑ i∈s,f i)=∏ i∈s,wsign (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s h ih => rw [Finset.sum_insert h,Finset.prod_insert h,wsign_add,ih]

theorem lawH_law (p : Shape) (N : ℕ) : IsLaw (lawH p N) :=
  prodW_law (fun _ => pairW_law unif_law unif_law)

theorem lawH_phased (x : Ambient p N) :
    avg (lawH p N) (fun y => wsign (uPhase p y x)) = bp (- (p.h:ℝ) * epoch p x) := by
  classical
  let w (i : Comp p.g) := (pairW unif unif : Wgt (HFrame p N))
  let f (i : Comp p.g) (x' : HFrame p N) := wsign (mpair (x'.2*x'.1ᵀ) (x i))
  have hh y : wsign (uPhase p y x)= prodW f y := by
    rw [uPhase,LinearMap.sum_apply, wsign_sum]; rfl
  change avg (prodW w) _ = _
  simp_rw [hh]
  rw [prodW_avg]
  have hg i : avg (w i) (f i)=bp (- (p.h:ℝ)*(x i).rank) := by
    change avg (pairW unif unif) _ = _
    refine (iid_prodM (x i) (K:=Chan p)).trans ?_
    congr 1
    simp only [Chan,num,Fintype.card_fin]
    ring
  simp_rw [hg]
  rw [←bp_sum,←Finset.mul_sum,←Nat.cast_sum,epoch]

def freeH (p : Shape) (N : ℕ) := pairW (lawH p N) (lawH p N)

theorem freeH_law (p : Shape) (N : ℕ) : IsLaw (freeH p N) :=
  pairW_law (lawH_law p N) (lawH_law p N)

set_option maxHeartbeats 800000 in
theorem free_phase {S : Party} (x : Ambient p N) (h : S≠0) :
    let Q := avg (freeH p N) (fun y => wsign (joinPhase p y S x));
    0 ≤ Q ∧ Q ≤ bp (- (p.h:ℝ)* epoch p x) := by
  classical
  let T (b : F) := avg (lawH p N) (fun y => wsign (b*uPhase p y x))
  have he :
      avg (freeH p N) (fun y => wsign (joinPhase p y S x))=T (S true)*T (S false) := by
    have hh y :
        wsign (joinPhase p y S x)=
          wsign (S true*uPhase p y.1 x)*wsign (S false*uPhase p y.2 x) := by
      rw [joinPhase, Fintype.sum_bool,LinearMap.add_apply,wsign_add]
      rfl
    simp_rw [hh]
    exact pairW_separate (lawH p N) (fun y => wsign (S true*uPhase p y x))
      (lawH p N) (fun y => wsign (S false*uPhase p y x))
  rw [he]
  let B := bp (- (p.h:ℝ) * epoch p x)
  have h0 : T 0=1 := by
    unfold T; simp only [zero_mul,wsign_zero, (lawH_law p N).avg_const]
  have h1 : T 1=B := by unfold T; simp only [one_mul,lawH_phased,B]
  have hz : 0≤ B := (bp_pos _).le
  have hl : B ≤1 := by
    unfold B
    rw [←bp_zero]
    exact bp_le (mul_nonpos_of_nonpos_of_nonneg (by simp) (Nat.cast_nonneg _))
  rcases bit_cases (S true) with hT|hT <;>
    rcases bit_cases (S false) with hF|hF <;> rw [hT,hF]
  · exact (h (by funext i; cases i <;> assumption)).elim
  · rw [h0,h1,one_mul]; exact ⟨hz,le_rfl⟩
  · rw [h1,h0,mul_one]; exact ⟨hz,le_rfl⟩
  rw [h1]; exact ⟨mul_nonneg hz hz,(mul_le_mul_of_nonneg_left hl hz).trans_eq (mul_one B)⟩

/-- cap for channel cube pair from joint raw -/
theorem phase_cap {w : Wgt (UnitType p n N)} {c : ℝ} (hc : 0≤c)
    (m : Mixer p n)
    (h : ∀ x,w x≤c*pairW (raw m N) (raw m N) x)
    (hN : 2*num (Full p n)-N≤ -1) (y : PhasePair p N) :
    mapW w (listens p) y≤c*chanPrice p^2 * freeH p N y := by
  refine (mapW_cap h (listens p) _).trans ?_
  unfold listens
  simp only [map_pair_law]
  have hz (x) : 0≤mapW (raw m N) (hcube p) x := pr_nonneg (raw_nonneg m)
  calc c*pairW _ _ y
    _ ≤ c*((chanPrice p*lawH p N y.1)*(chanPrice p*lawH p N y.2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (hcube_cap m hN y.1) (hcube_cap m hN y.2)
        (hz _) ((hz _).trans (hcube_cap m hN y.1))) hc
    _ = _ := by unfold freeH pairW; ring

end HadwigerCounterexample

end

end OAI
