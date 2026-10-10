import OAI.Combinatorics.BalancedRyser.Local.LocalAnchorExclusion
import OAI.Combinatorics.BalancedRyser.Local.LocalPrescribedGeometry

namespace OAI

namespace Balanced.Local.ParentMap

noncomputable section
open scoped Classical

def endpointIndex (r : Fin 4) (σ t : Bool) : Fin 4 :=
  if t = σ then r else r - 1

theorem endpointIndex_injective (r : Fin 4) (σ : Bool) :
    Function.Injective (endpointIndex r σ) := by
  intro t u h
  fin_cases r <;> cases σ <;> cases t <;> cases u <;>
    simp_all [endpointIndex]

theorem endpointIndex_eq_or (r : Fin 4) (σ t : Bool) :
    endpointIndex r σ t = r ∨ endpointIndex r σ t = r - 1 := by
  unfold endpointIndex
  split_ifs <;> simp

variable {b : ℕ}

def dependent (child : Fin b) (s : Fin 4) : Finset (Fin b × Fin 4) :=
  {(child, s), (child, s - 1)}

def underlying (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    (ij : Fin b × Fin 4) : Fin b × Fin 4 :=
  if ij = (child, s) then (root, endpointIndex r σ τ)
  else if ij = (child, s - 1) then (root, endpointIndex r σ (!τ)) else ij

theorem sub_one_ne (s : Fin 4) : s - 1 ≠ s := by
  fin_cases s <;> decide

theorem underlying_first (root child : Fin b) (r s : Fin 4) (σ τ : Bool) :
    underlying root child r s σ τ (child, s) = (root, endpointIndex r σ τ) := by
  simp [underlying]

theorem underlying_second (root child : Fin b) (r s : Fin 4) (σ τ : Bool) :
    underlying root child r s σ τ (child, s - 1) =
      (root, endpointIndex r σ (!τ)) := by
  simp [underlying]

theorem underlying_fixed (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    {ij : Fin b × Fin 4} (h : ij ∉ dependent child s) :
    underlying root child r s σ τ ij = ij := by
  simp only [dependent, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  simp [underlying, h.1, h.2]

theorem underlying_not_dependent (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    (hne : root ≠ child) (ij : Fin b × Fin 4) :
    underlying root child r s σ τ ij ∉ dependent child s := by
  by_cases hfirst : ij = (child, s)
  · subst ij
    simp [underlying_first, dependent, hne]
  · by_cases hsecond : ij = (child, s - 1)
    · subst ij
      simp [underlying_second, dependent, hne]
    · simp [underlying, hfirst, hsecond, dependent]

theorem underlying_idempotent (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    (hne : root ≠ child) (ij : Fin b × Fin 4) :
    underlying root child r s σ τ (underlying root child r s σ τ ij) =
      underlying root child r s σ τ ij :=
  underlying_fixed root child r s σ τ
    (underlying_not_dependent root child r s σ τ hne ij)

theorem underlying_injective_on_dependent (root child : Fin b) (r s : Fin 4)
    (σ τ : Bool) : Set.InjOn (underlying root child r s σ τ) (dependent child s) := by
  intro ij hij kl hkl heq
  simp only [dependent, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hij hkl
  rcases hij with rfl | rfl <;> rcases hkl with rfl | rfl
  · rfl
  · rw [underlying_first, underlying_second] at heq
    have h := endpointIndex_injective r σ (congrArg Prod.snd heq)
    cases τ <;> contradiction
  · rw [underlying_first, underlying_second] at heq
    have h := endpointIndex_injective r σ (congrArg Prod.snd heq)
    cases τ <;> contradiction
  · rfl

theorem two_anchors_not_both_self (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    {v x y : Fin b × Fin 4}
    (hx : x ≠ v) (hy : y ≠ v) (hxy : x ≠ y) :
    underlying root child r s σ τ x ≠ v ∨
      underlying root child r s σ τ y ≠ v := by
  by_contra h
  simp only [not_or, not_not] at h
  have hxd : x ∈ dependent child s := by
    by_contra hxd
    exact hx ((underlying_fixed root child r s σ τ hxd).symm.trans h.1)
  have hyd : y ∈ dependent child s := by
    by_contra hyd
    exact hy ((underlying_fixed root child r s σ τ hyd).symm.trans h.2)
  exact hxy (underlying_injective_on_dependent root child r s σ τ hxd hyd
    (h.1.trans h.2.symm))

theorem underlying_fiber_card_le_two (root child : Fin b) (r s : Fin 4) (σ τ : Bool)
    (v : Fin b × Fin 4) :
    (Finset.univ.filter (fun x => underlying root child r s σ τ x = v)).card ≤ 2 := by
  let f : (Fin b × Fin 4) → Bool := fun x => decide (x ∈ dependent child s)
  have h := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset Bool)) f
    (by intro x _; exact Finset.mem_univ _)
    (show Set.InjOn f (Finset.univ.filter
      (fun x => underlying root child r s σ τ x = v)) from by
      intro x hx y hy hxy
      have hxv := (Finset.mem_filter.mp hx).2
      have hyv := (Finset.mem_filter.mp hy).2
      by_cases hxd : x ∈ dependent child s
      · have hyd : y ∈ dependent child s := by
          by_contra hyd
          simp [f, hxd, hyd] at hxy
        exact underlying_injective_on_dependent root child r s σ τ hxd hyd
          (hxv.trans hyv.symm)
      · have hyd : y ∉ dependent child s := by
          intro hyd
          simp [f, hxd, hyd] at hxy
        rw [underlying_fixed root child r s σ τ hxd] at hxv
        rw [underlying_fixed root child r s σ τ hyd] at hyv
        exact hxv.trans hyv.symm)
  simpa only [Finset.card_univ, Fintype.card_bool] using h

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)

omit [Fintype F] [DecidableEq F] in

theorem endpoint_on_constituent (ha : Eligible P a) (i : Fin b) (r : Fin 4)
    (t : Bool) :
    OnLine (prescribedPoint P a bits M (i, endpointIndex r (bits i r) t))
      (constituent M (a.2 (P.classOf i r)) t) := by
  by_cases ht : t = bits i r
  · simpa [endpointIndex, ht] using
      PrescribedGeometry.prescribedPoint_on_left (M := M) ha i r
  · have ht' : t = !(bits i r) := by
      cases t <;> cases h : bits i r <;> simp_all
    rw [endpointIndex, ite_eq_right ht]
    simpa only [sub_add_cancel, ht'] using
      PrescribedGeometry.prescribedPoint_on_right (bits := bits) (M := M) ha i (r - 1)

theorem endpoint_purposeful (i : Fin b) (r : Fin 4) (t : Bool) :
    AnchorExclusion.Purposeful P (P.classOf i r)
      (i, endpointIndex r (bits i r) t) := by
  rcases endpointIndex_eq_or r (bits i r) t with h | h
  · left
    simp only [h]
  · right
    simp only [h, sub_add_cancel]

omit [Fintype F] [DecidableEq F] in

theorem child_endpoint_eq_projection (ha : Eligible P a) (p : Point F)
    (hA : Aligned P a bits p M) (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s) (t : Bool) :
    prescribedPoint P a bits M (child, endpointIndex s (bits child s) t) =
      lineIntersection
        (lineThrough (a.2 (P.classOf root r))
          (prescribedPoint P a bits M (root, endpointIndex r (bits root r) t)))
        (lineThrough (a.1 child) p) := by
  have hroot := endpoint_on_constituent P a bits M ha root r t
  have hchild : OnLine
      (prescribedPoint P a bits M (child, endpointIndex s (bits child s) t))
      (constituent M (a.2 (P.classOf root r)) t) := by
    simpa only [hshared] using endpoint_on_constituent P a bits M ha child s t
  have hline : lineThrough (a.2 (P.classOf root r))
      (prescribedPoint P a bits M (root, endpointIndex r (bits root r) t)) =
        constituent M (a.2 (P.classOf root r)) t :=
    (line_eq_lineThrough _ _ hroot).symm
  rw [hline]
  have hd : a.2 (P.classOf root r) ≠ a.1 child := by
    simpa only [hshared] using ha.2.2 child s
  apply common_point_eq_of_lines_ne
    (constituent M (a.2 (P.classOf root r)) t) (lineThrough (a.1 child) p)
    (fun h => hd (congrArg Prod.fst h))
  · exact hchild
  · exact hA _
  · exact onLine_lineIntersection_left _ _ hd
  · exact onLine_lineIntersection_right _ _ hd

omit [Fintype F] [DecidableEq F] in

theorem same_underlying_shared_constituent (ha : Eligible P a)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    {v x : Fin b × Fin 4} (hv : v ∉ dependent child s) (hx : x ≠ v)
    (hm : underlying root child r s (bits root r) (bits child s) x = v) :
    AnchorExclusion.Purposeful P (P.classOf root r) v ∧
      ∃ t : Bool,
        OnLine (prescribedPoint P a bits M v)
          (constituent M (a.2 (P.classOf root r)) t) ∧
        OnLine (prescribedPoint P a bits M x)
          (constituent M (a.2 (P.classOf root r)) t) := by
  have hxd : x ∈ dependent child s := by
    by_contra hxd
    exact hx ((underlying_fixed root child r s (bits root r) (bits child s) hxd).symm.trans hm)
  simp only [dependent, Finset.mem_insert, Finset.mem_singleton] at hxd
  rcases hxd with rfl | rfl
  · rw [underlying_first] at hm
    subst v
    refine ⟨endpoint_purposeful P bits root r (bits child s), bits child s,
      endpoint_on_constituent P a bits M ha root r (bits child s), ?_⟩
    simpa only [hshared] using
      PrescribedGeometry.prescribedPoint_on_left (M := M) ha child s
  · rw [underlying_second] at hm
    subst v
    refine ⟨endpoint_purposeful P bits root r (!(bits child s)), !(bits child s),
      endpoint_on_constituent P a bits M ha root r (!(bits child s)), ?_⟩
    simpa only [sub_add_cancel, hshared] using
      PrescribedGeometry.prescribedPoint_on_right (M := M) ha child (s - 1)

theorem ordinary_anchor_not_self (ha : Eligible P a) (p : Point F)
    (hA : Admissible P a bits p M) (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    {v x : Fin b × Fin 4} (hv : v ∉ dependent child s) (hx : x ≠ v)
    (l : Line F) (hl : AllowedPiece a p M (Sum.inr (Sum.inl l)))
    (hvl : OnLine (prescribedPoint P a bits M v) l)
    (hxl : OnLine (prescribedPoint P a bits M x) l) :
    underlying root child r s (bits root r) (bits child s) x ≠ v := by
  intro hm
  obtain ⟨_, t, hvt, hxt⟩ :=
    same_underlying_shared_constituent P a bits M ha root child r s hshared hv hx hm
  exact AnchorExclusion.ordinary_line_no_shared_constituent P a bits M p hA l hl
    hx.symm (a.2 (P.classOf root r)) t hvt hxt ⟨hvl, hxl⟩

theorem used_pair_anchor_not_self (ha : Eligible P a) (p : Point F)
    (hA : Admissible P a bits p M) (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    {v x : Fin b × Fin 4} (hv : v ∉ dependent child s) (hx : x ≠ v)
    (c : Fin (4 * b - κ)) (t : Bool)
    (hnc : ¬ AnchorExclusion.Purposeful P c v)
    (hvc : OnLine (prescribedPoint P a bits M v) (constituent M (a.2 c) t))
    (hxc : OnLine (prescribedPoint P a bits M x) (constituent M (a.2 c) t)) :
    underlying root child r s (bits root r) (bits child s) x ≠ v := by
  intro hm
  obtain ⟨he, u, hvu, hxu⟩ :=
    same_underlying_shared_constituent P a bits M ha root child r s hshared hv hx hm
  exact AnchorExclusion.used_pair_no_self_anchor P a bits M ha p hA hx.symm
    c (P.classOf root r) t u hnc he hvu hxu ⟨hvc, hxc⟩

end
end Balanced.Local.ParentMap

end OAI
