import Mathlib.LinearAlgebra.Quotient.Basic

namespace OAI

namespace ArExplicit

universe u

variable {k : Type u} [Field k]
variable (B D E K W : ℤ → Type u)
variable [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
variable [∀ n, AddCommGroup (D n)] [∀ n, Module k (D n)]
variable [∀ n, AddCommGroup (E n)] [∀ n, Module k (E n)]
variable [∀ n, AddCommGroup (K n)] [∀ n, Module k (K n)]
variable [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]

structure TwoConeFiltration where
  row : ∀ n, D n →ₗ[k] B (n + 1)
  column : ∀ n, E n →ₗ[k] D (n + 1)
  bottom : ∀ n, B n →ₗ[k] K n
  middle : ∀ n, K n →ₗ[k] D n
  attach : ∀ n, E n →ₗ[k] K (n + 1)
  inclusion : ∀ n, K n →ₗ[k] W n
  projection : ∀ n, W n →ₗ[k] E n
  row_bottom : ∀ n, LinearMap.range (row n) = LinearMap.ker (bottom (n + 1))
  bottom_middle : ∀ n, LinearMap.range (bottom n) = LinearMap.ker (middle n)
  middle_row : ∀ n, LinearMap.range (middle n) = LinearMap.ker (row n)
  attach_inclusion : ∀ n, LinearMap.range (attach n) = LinearMap.ker (inclusion (n + 1))
  inclusion_projection : ∀ n, LinearMap.range (inclusion n) = LinearMap.ker (projection n)
  projection_attach : ∀ n, LinearMap.range (projection n) = LinearMap.ker (attach n)
  adjacent : ∀ n, (middle (n + 1)).comp (attach n) = column n

namespace TwoConeFiltration

variable {B D E K W}
variable (F : TwoConeFiltration (k := k) B D E K W)

theorem middle_injective (n : ℤ) (hrow : Function.Surjective (F.row n)) :
    Function.Injective (F.middle (n + 1)) := by
  have hb : F.bottom (n + 1) = 0 := by
    apply LinearMap.ext
    intro x
    have hx : x ∈ LinearMap.range (F.row n) := hrow x
    rw [F.row_bottom] at hx
    exact hx
  rw [← LinearMap.ker_eq_bot, ← F.bottom_middle, hb, LinearMap.range_zero]

theorem attach_surjective (n : ℤ) (hrow : Function.Surjective (F.row n))
    (hKoszul : LinearMap.range (F.column n) = LinearMap.ker (F.row (n + 1))) :
    Function.Surjective (F.attach n) := by
  intro x
  have hx : F.middle (n + 1) x ∈ LinearMap.ker (F.row (n + 1)) := by
    rw [← F.middle_row]
    exact LinearMap.mem_range_self _ x
  rw [← hKoszul] at hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, F.middle_injective n hrow ?_⟩
  change (F.middle (n + 1)).comp (F.attach n) z = _
  rw [F.adjacent, hz]

theorem attach_injective (n : ℤ) (hcolumn : Function.Injective (F.column n)) :
    Function.Injective (F.attach n) := by
  intro x y h
  apply hcolumn
  have h' := congrArg (F.middle (n + 1)) h
  change (F.middle (n + 1)).comp (F.attach n) x =
    (F.middle (n + 1)).comp (F.attach n) y at h'
  simpa only [F.adjacent] using h'

theorem inclusion_zero_next (n : ℤ) (h : Function.Surjective (F.attach n)) :
    F.inclusion (n + 1) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ LinearMap.range (F.attach n) := h x
  rw [F.attach_inclusion] at hx
  exact hx

variable (hrow : ∀ n : ℤ, n ≠ -1 → Function.Surjective (F.row n))
variable (hcolumn : ∀ n : ℤ, n ≠ 3 → Function.Injective (F.column n))
variable (hKoszul : ∀ n : ℤ,
  LinearMap.range (F.column n) = LinearMap.ker (F.row (n + 1)))

include hrow hKoszul in

theorem inclusion_zero (n : ℤ) (hn : n ≠ 0) : F.inclusion n = 0 := by
  have hp : n - 1 ≠ -1 := by omega
  have h := F.inclusion_zero_next (n - 1)
    (F.attach_surjective (n - 1) (hrow _ hp) (hKoszul _))
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at h
  exact h

include hrow hcolumn hKoszul in

theorem subsingleton_of_ne (n : ℤ) (h0 : n ≠ 0) (h3 : n ≠ 3) :
    Subsingleton (W n) := by
  apply subsingleton_of_forall_eq 0
  intro w
  have hp : F.projection n w ∈ LinearMap.ker (F.attach n) := by
    rw [← F.projection_attach]
    exact LinearMap.mem_range_self _ w
  have hp0 : F.projection n w = 0 := (F.attach_injective n (hcolumn n h3)).eq_iff.mp
    (by change F.attach n (F.projection n w) = 0 at hp; simpa only [map_zero] using hp)
  have hw : w ∈ LinearMap.range (F.inclusion n) := by
    rw [F.inclusion_projection]
    exact hp0
  obtain ⟨x, rfl⟩ := hw
  rw [F.inclusion_zero hrow hKoszul n h0]
  rfl

include hrow in

theorem first_degree_four_subsingleton [Subsingleton (D 4)] : Subsingleton (K 4) := by
  have h : Function.Injective (F.middle 4) := by
    convert F.middle_injective 3 (hrow 3 (by decide)) using 1 <;> norm_num
  exact h.subsingleton

include hrow hKoszul in

theorem top_projection_bijective [Subsingleton (D 4)] :
    Function.Bijective (F.projection 3) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, ← F.inclusion_projection,
      F.inclusion_zero hrow hKoszul 3 (by decide), LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top, F.projection_attach]
    let := F.first_degree_four_subsingleton hrow
    apply top_unique
    intro x _
    have hz : (3 : ℤ) + 1 = 4 := by decide
    have : Subsingleton (K (3 + 1)) := hz.symm ▸ F.first_degree_four_subsingleton hrow
    exact Subsingleton.elim _ _

include hrow hKoszul in

noncomputable def topProjectionEquiv [Subsingleton (D 4)] : W 3 ≃ₗ[k] E 3 :=
  LinearEquiv.ofBijective (F.projection 3) (F.top_projection_bijective hrow hKoszul)

theorem bottom_zero_bijective [Subsingleton (D (-1))] [Subsingleton (D 0)] :
    Function.Bijective (F.bottom 0) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    have h := F.row_bottom (-1)
    change LinearMap.range (F.row (-1)) = LinearMap.ker (F.bottom 0) at h
    rw [← h]
    exact LinearMap.range_eq_bot.mpr (Subsingleton.elim _ _)
  · rw [← LinearMap.range_eq_top, F.bottom_middle]
    apply top_unique
    intro x _
    exact Subsingleton.elim _ _

include hcolumn in

theorem inclusion_zero_bijective [Subsingleton (E (-1))] :
    Function.Bijective (F.inclusion 0) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    have h := F.attach_inclusion (-1)
    change LinearMap.range (F.attach (-1)) = LinearMap.ker (F.inclusion 0) at h
    rw [← h]
    exact LinearMap.range_eq_bot.mpr (Subsingleton.elim _ _)
  · rw [← LinearMap.range_eq_top, F.inclusion_projection]
    apply top_unique
    intro x _
    have hx : F.projection 0 x ∈ LinearMap.ker (F.attach 0) := by
      rw [← F.projection_attach]
      exact LinearMap.mem_range_self _ x
    exact (F.attach_injective 0 (hcolumn 0 (by decide))).eq_iff.mp
      (by change F.attach 0 (F.projection 0 x) = 0 at hx; simpa only [map_zero] using hx)

include hcolumn in

noncomputable def bottomInclusionEquiv
    [Subsingleton (D (-1))] [Subsingleton (D 0)] [Subsingleton (E (-1))] :
    B 0 ≃ₗ[k] W 0 :=
  (LinearEquiv.ofBijective (F.bottom 0) F.bottom_zero_bijective).trans
    (LinearEquiv.ofBijective (F.inclusion 0) (F.inclusion_zero_bijective hcolumn))

end TwoConeFiltration
end ArExplicit

end OAI
