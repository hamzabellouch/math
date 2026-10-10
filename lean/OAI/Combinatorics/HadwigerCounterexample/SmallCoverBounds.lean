import OAI.Combinatorics.HadwigerCounterexample.RelativeInjectionBounds

namespace OAI

/-! # Small Cover Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A B V : Type} [Fintype A] [Fintype B]

def allSide : Party := fun _ => 1

def cutDown (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N))
    (x : UnitType p n N) : coverX p T :=
  open scoped Classical in
  if h : w x≠0 ∧ covered p T (Δ x) then ⟨_,h.2⟩ else 0

def juris (p : Shape) {n N} (T : Cov p N) (x : UnitType p n N) (S : Party) :
    Module.Dual F (coverX p T) :=
  joinPhase p (listens p x) S ∘ₗ (coverX p T).subtype

abbrev Daypair (p : Shape) {N} (T : Cov p N) :=
  coverX p T × (Bool → Module.Dual F (coverX p T))

def daypair (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N))
    (x : UnitType p n N) : Daypair p T :=
  (cutDown p T Δ w x,fun i => juris p T x (unary i))

def shadow (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N))
    (x y : UnitType p n N) (S : Party) :=
  juris p T y S (cutDown p T Δ w x)

theorem shadow_valid (p : Shape) {n N} (T : Cov p N)
    (Δ : UnitType p n N→Ambient p N) {w}
    (h : ∀ x,w x≠0 → covered p T (Δ x)) (x y : UnitType p n N) (S) (hx : w x≠0) :
    shadow p T Δ w x y S=tone p y S (Δ x) := by
  classical
  unfold shadow cutDown
  rw [dite_eq_left ⟨hx,h x hx⟩]; rfl

theorem tone_vec (p : Shape) {n N} (x : UnitType p n N) (S : Party) (Δ : Ambient p N) :
    tone p x S Δ=dotProduct S (fun i => tone p x (unary i) Δ) := by
  classical
  have hg (i) : tone p x (unary i) Δ=uPhase p (onSide (listens p x) i) Δ := by
    unfold tone joinPhase unary
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same,one_smul]
    · intro j _ hj; simp [hj]
    simp
  unfold dotProduct
  simp_rw [hg]
  unfold tone joinPhase
  simp

theorem shadow_day (p : Shape) {n N} (T : Cov p N)
    (Δ : UnitType p n N→Ambient p N) (w : Wgt (UnitType p n N))
    (x y) (S : Party) :
    shadow p T Δ w x y S =
    dotProduct S (fun i => (daypair p T Δ w y).2 i (daypair p T Δ w x).1) :=
  tone_vec p y _ (cutDown p T Δ w x).val

theorem day_named (p : Shape) {n N} (T : Cov p N)
    (Δ : UnitType p n N→Ambient p N)
    (w : Wgt (UnitType p n N)) (d : ℕ) (hT : cdim p T≤d)
    (P : Daypair p T × Daypair p T → Prop) :
    named (fun v => P (daypair p T Δ w v.1,daypair p T Δ w v.2)) (bp (3*d*(N:ℝ))) := by
  classical
  let A := (coverX p T)
  let : Finite (Module.Dual F (coverX p T)) := Finite.of_injective _ DFunLike.coe_injective
  let : Fintype (Module.Dual F (coverX p T)) := Fintype.ofFinite _
  have he : dim (Daypair p T) ≤ 3*d*N := by
    unfold Daypair dim
    rw [Module.finrank_prod, Module.finrank_pi_fintype,Fintype.sum_bool,
      Subspace.dual_finrank_eq]
    change dim A+(dim A+dim A)≤_
    have h : dim A≤N*d := (cover_dim p T).trans (Nat.mul_le_mul_left N hT)
    nlinarith
  refine named_at (fun y x => P (daypair p T Δ w x,y)) ?_ (fun y => ⟨daypair p T Δ w y,fun x => Iff.rfl⟩)
  rw [card_space]
  exact bp_le (by exact_mod_cast he)

variable [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem dual_matrix_rank (f : A→ V) (g : B→Module.Dual F V) :
    (Matrix.of (fun x : A => fun y : B => g y (f x))).rank ≤ dim V := by
  classical
  let M := Matrix.of (fun x : A => fun y : B => g y (f x))
  let L : V →ₗ[F] Vec B := LinearMap.pi g
  have hi : colSp Mᵀ ≤ LinearMap.range L := by
    rw [colSp, range_mulVecLin]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun x => ⟨f x,rfl⟩)
  have he : dim (colSp Mᵀ) ≤ dim V := (Submodule.finrank_mono hi).trans
    (LinearMap.finrank_range_le L)
  rw [colSp_dim,Matrix.rank_transpose] at he
  exact he

def circus (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N)) :
    Mat (UnitType p n N) (UnitType p n N) :=
  Matrix.of (fun x y => shadow p T Δ w x y allSide)

theorem circus_rank (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N)) :
    (circus p T Δ w).rank≤ N*cdim p T := (dual_matrix_rank (cutDown p T Δ w)
      (fun y => juris p T y allSide)).trans (cover_dim p T)

end HadwigerCounterexample

end

end OAI
