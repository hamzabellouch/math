import OAI.Algebra.AuslanderReiten.Cones.TwoConeFiltration
import OAI.Algebra.AuslanderReiten.Complete.TateKoszul

namespace OAI

noncomputable section
namespace ArExplicit
universe u
variable {k : Type u} [Field k]
variable {H B D E K W : ℤ → Type u}
variable [∀ n, AddCommGroup (H n)] [∀ n, Module k (H n)]
variable [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
variable [∀ n, AddCommGroup (D n)] [∀ n, Module k (D n)]
variable [∀ n, AddCommGroup (E n)] [∀ n, Module k (E n)]
variable [∀ n, AddCommGroup (K n)] [∀ n, Module k (K n)]
variable [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]
variable (F : TwoConeFiltration (k := k) B D E K W)
variable (x y : ∀ a : ℤ, H a →ₗ[k] H (a+3))

structure TwoConeKoszulCoordinates where
  bottom : ∀ n, B n ≃ₗ[k] H n
  middle : ∀ n, D n ≃ₗ[k] (H (n-2) × H (n-2))
  top : ∀ n, E n ≃ₗ[k] H (n-4)
  row_eq : ∀ n v, bottom (n+1) (F.row n v) =
    TateKoszul.degreeEquiv (k := k) H (show n-2+3=n+1 by omega)
      (TateKoszul.row (x := x) (y := y) (n-2) (middle n v))
  column_eq : ∀ n v, middle (n+1) (F.column n v) =
    ((TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega)).prodCongr
      (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega)))
      (TateKoszul.column (x := x) (y := y) (n-4) (top n v))

namespace TwoConeKoszulCoordinates
variable {F x y}
variable (C : TwoConeKoszulCoordinates F x y) (M : TateKoszul.Model x y)

private theorem row_zero_reindex {a b : ℤ} (h : a=b) (v : H a × H a) :
    TateKoszul.row (x := x) (y := y) a v = 0 ↔
      TateKoszul.row (x := x) (y := y) b
        (((TateKoszul.degreeEquiv (k := k) H h).prodCongr (TateKoszul.degreeEquiv (k := k) H h)) v) = 0 := by
  subst b
  rfl

include C M

theorem row_surjective (n : ℤ) (hn : n ≠ -1) : Function.Surjective (F.row n) := by
  intro v
  let e := TateKoszul.degreeEquiv (k := k) H (show n-2+3=n+1 by omega)
  obtain ⟨w, hw⟩ := TateKoszul.row_surjective M (n-2) (by omega) (e.symm (C.bottom (n+1) v))
  refine ⟨(C.middle n).symm w, (C.bottom (n+1)).injective ?_⟩
  rw [C.row_eq, LinearEquiv.apply_symm_apply, hw]
  exact e.apply_symm_apply _

theorem column_injective (n : ℤ) (hn : n ≠ 3) : Function.Injective (F.column n) := by
  intro v w h
  apply (C.top n).injective
  apply TateKoszul.column_injective M (n-4) (by omega)
  let e := (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega)).prodCongr
    (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega))
  apply e.injective
  rw [← C.column_eq, ← C.column_eq, h]

theorem range_column_eq_ker_row (n : ℤ) :
    LinearMap.range (F.column n) = LinearMap.ker (F.row (n+1)) := by
  let e := (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega)).prodCongr
    (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega))
  have hrow (w : D (n+1)) : F.row (n+1) w = 0 ↔
      TateKoszul.row (x := x) (y := y) (n-4+3) (e.symm (C.middle (n+1) w)) = 0 := by
    have h0 : F.row (n+1) w = 0 ↔
        TateKoszul.row (x := x) (y := y) (n+1-2) (C.middle (n+1) w) = 0 := by
      rw [← (C.bottom (n+1+1)).map_eq_zero_iff, C.row_eq,
        LinearEquiv.map_eq_zero_iff]
    rw [h0]
    have hr := row_zero_reindex (x := x) (y := y)
      (show n-4+3=n+1-2 by omega) (e.symm (C.middle (n+1) w))
    change _ = 0 ↔ _ = 0 at hr
    rw [e.apply_symm_apply] at hr
    exact hr.symm
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    change F.row (n+1) (F.column n v) = 0
    rw [hrow, C.column_eq, e.symm_apply_apply]
    have hv : TateKoszul.column (x := x) (y := y) (n-4) (C.top n v) ∈
        LinearMap.range (TateKoszul.column (x := x) (y := y) (n-4)) := ⟨_, rfl⟩
    rw [TateKoszul.range_column_eq_ker_row M] at hv
    exact hv
  · intro hw
    have hw' := (hrow w).1 hw
    change e.symm (C.middle (n+1) w) ∈
      LinearMap.ker (TateKoszul.row (x := x) (y := y) (n-4+3)) at hw'
    rw [← TateKoszul.range_column_eq_ker_row M] at hw'
    obtain ⟨v, hv⟩ := hw'
    refine ⟨(C.top n).symm v, (C.middle (n+1)).injective ?_⟩
    rw [C.column_eq, LinearEquiv.apply_symm_apply, hv]
    exact e.apply_symm_apply _

theorem subsingleton_of_ne (n : ℤ) (h0 : n ≠ 0) (h3 : n ≠ 3) : Subsingleton (W n) :=
  F.subsingleton_of_ne (C.row_surjective M) (C.column_injective M)
    (C.range_column_eq_ker_row M) n h0 h3

private theorem middle_four_subsingleton : Subsingleton (D 4) := by
  let : Subsingleton (H (4-2)) := M.outside _ (fun n h => by omega) (fun n h => by omega)
  exact (C.middle 4).injective.subsingleton

def topProjectionEquiv : W 3 ≃ₗ[k] E 3 := by
  letI := C.middle_four_subsingleton M
  exact F.topProjectionEquiv (C.row_surjective M) (C.range_column_eq_ker_row M)

@[simp]
theorem topProjectionEquiv_apply (w : W 3) : C.topProjectionEquiv M w = F.projection 3 w := rfl

private theorem middle_minus_one_subsingleton : Subsingleton (D (-1)) := by
  let : Subsingleton (H (-1-2)) := M.outside _ (fun n h => by omega) (fun n h => by omega)
  exact (C.middle (-1)).injective.subsingleton

private theorem middle_zero_subsingleton : Subsingleton (D 0) := by
  let : Subsingleton (H (0-2)) := M.outside _ (fun n h => by omega) (fun n h => by omega)
  exact (C.middle 0).injective.subsingleton

private theorem top_minus_one_subsingleton : Subsingleton (E (-1)) := by
  let : Subsingleton (H (-1-4)) := M.outside _ (fun n h => by omega) (fun n h => by omega)
  exact (C.top (-1)).injective.subsingleton

def bottomInclusionEquiv : B 0 ≃ₗ[k] W 0 := by
  letI := C.middle_minus_one_subsingleton M
  letI := C.middle_zero_subsingleton M
  letI := C.top_minus_one_subsingleton M
  exact F.bottomInclusionEquiv (C.column_injective M)

@[simp]
theorem bottomInclusionEquiv_apply (v : B 0) :
    C.bottomInclusionEquiv M v = F.inclusion 0 (F.bottom 0 v) := rfl

def bottomCoordinateEquiv : W 0 ≃ₗ[k] H 0 :=
  (C.bottomInclusionEquiv M).symm.trans (C.bottom 0)

def topCoordinateEquiv : W 3 ≃ₗ[k] H (-1) :=
  (C.topProjectionEquiv M).trans (C.top 3)

@[simp]
theorem topCoordinateEquiv_apply (w : W 3) :
    C.topCoordinateEquiv M w = C.top 3 (F.projection 3 w) := rfl

end TwoConeKoszulCoordinates
end ArExplicit

end

end OAI
