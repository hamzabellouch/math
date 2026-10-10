import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRationalLocal
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRealization

namespace OAI

/-! The rational local gadgets are glued through the exact final-graph
permutation. All old lattice sites remain fixed; all nineteen edges per
source edge retain a controlled error and all nonedges retain the margin. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalGlobal
open ContactMediator MediatorIteration

def localPoints (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) : LocalSite → ContactPoint :=
  ContactRationalLocal.point P (edgeNegative d.bonds e) (fun a => ℓ (encodeEdge d.edges e a))

def point (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    GlobalSite d → ContactPoint := globalPosition d (localPoints d P ℓ)

theorem local_start (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (e : Fin d.edges) : localPoints d P ℓ e (localOld 0) = contactPoint 0 0 :=
  (ContactRationalLocal.exists_link_approximation P (edgeNegative d.bonds e)
    (fun a => ℓ (encodeEdge d.edges e a)) (fun _ => hℓ _)).1

theorem local_end (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (e : Fin d.edges) : localPoints d P ℓ e (localOld 1) = contactPoint 17 0 :=
  (ContactRationalLocal.exists_link_approximation P (edgeNegative d.bonds e)
    (fun a => ℓ (encodeEdge d.edges e a)) (fun _ => hℓ _)).2.1

theorem edge_error (d : SquareLatticeHeisenberg) (W G P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (a : GlobalEdge d) :
    |dist (point d P ℓ ((finalGraph d.bonds W G).left a))
      (point d P ℓ ((finalGraph d.bonds W G).right a)) - (ℓ a : ℝ)| ≤
        72 * ((P : ℝ) + 1)⁻¹ := by
  obtain ⟨⟨e, a⟩, rfl⟩ := (edgeEquiv d.edges).surjective a
  change |dist (globalPosition d (localPoints d P ℓ)
      ((finalGraph d.bonds W G).left (encodeEdge d.edges e a)))
    (globalPosition d (localPoints d P ℓ)
      ((finalGraph d.bonds W G).right (encodeEdge d.edges e a))) -
        (ℓ (encodeEdge d.edges e a) : ℝ)| ≤ _
  rw [finalGraph_left, finalGraph_right]
  change |dist (globalPosition d (localPoints d P ℓ)
      (localVertex (d.left e) (d.right e) e (localLeft (member (d.coefficient e)) a)))
    (globalPosition d (localPoints d P ℓ)
      (localVertex (d.left e) (d.right e) e (localRight a))) -
        (ℓ (encodeEdge d.edges e a) : ℝ)| ≤ _
  rw [globalPosition_local d _ (local_start d P ℓ hℓ) (local_end d P ℓ hℓ),
    globalPosition_local d _ (local_start d P ℓ hℓ) (local_end d P ℓ hℓ),
    ContactGridEdge.place_dist]
  have hm : member (d.coefficient e) = if edgeNegative d.bonds e then 0 else 1 :=
    member_edgeNegative d.bonds e
  rw [hm]
  exact (ContactRationalLocal.exists_link_approximation P (edgeNegative d.bonds e)
    (fun a => ℓ (encodeEdge d.edges e a)) (fun a => hℓ _)).2.2.1 a

theorem nonedge_separation (d : SquareLatticeHeisenberg) (W G P : ℕ)
    (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (x y : GlobalSite d) (hne : x ≠ y) (hn : Nonedge d W G x y) :
    6 / 5 < dist (point d P ℓ x) (point d P ℓ y) := by
  apply globalPosition_nonedge d W G (localPoints d P ℓ)
    (local_start d P ℓ hℓ) (local_end d P ℓ hℓ) _ _ x y hne hn
  · intro e s t hst hnon
    exact ContactRationalLocal.nonedge_separation P (edgeNegative d.bonds e)
      (fun a => ℓ (encodeEdge d.edges e a)) (by omega) (fun a => hℓ _) s t hst
      (finalGraph_nonedge_contactNonlink d.bonds W G e s t hnon)
  · intro e s
    exact ContactRationalLocal.near_base P (edgeNegative d.bonds e)
      (fun a => ℓ (encodeEdge d.edges e a)) hP (fun a => hℓ _) s

theorem separation (d : SquareLatticeHeisenberg) (W G P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (x y : GlobalSite d) (hne : x ≠ y) :
    9 / 10 ≤ dist (point d P ℓ x) (point d P ℓ y) := by
  by_cases hn : Nonedge d W G x y
  · exact (by norm_num : (9 / 10 : ℝ) ≤ 6 / 5).trans
      (nonedge_separation d W G P ℓ hP hℓ x y hne hn).le
  · simp only [Nonedge, not_not] at hn
    obtain ⟨a, ha⟩ := hn
    have he := (abs_le.mp (edge_error d W G P ℓ hℓ a)).1
    have hsmall : 72 * ((P : ℝ) + 1)⁻¹ ≤ 1 / 50 := by
      apply (mul_inv_le_iff₀ (by positivity)).mpr
      have hPR : (7200 : ℝ) ≤ P := by exact_mod_cast hP
      linarith
    have hl := (hℓ a).1
    unfold contactLengthTolerance at hl
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith
    · rw [dist_comm]
      linarith

theorem coordinate_bound (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    {M : ℝ} (hcoord : ∀ j k, |(contactGridAxis (d.coordinate j) k : ℝ)| ≤ M)
    (x : GlobalSite d) (i : Fin 2) : |point d P ℓ x i| ≤ 17 * M + 17 :=
  globalPosition_coordinate_bound d (localPoints d P ℓ) hcoord
    (fun e s => ContactRationalLocal.near_base P (edgeNegative d.bonds e)
      (fun a => ℓ (encodeEdge d.edges e a)) hP (fun _ => hℓ _) s) x i

def rationalPlace (e : ContactGridEdge) (p : ℚ × ℚ) : ℚ × ℚ :=
  let q := if e.reversed then (17 - p.1, p.2) else p
  if e.vertical then (17 * e.anchor.1 - q.2, 17 * e.anchor.2 + q.1)
  else (17 * e.anchor.1 + q.1, 17 * e.anchor.2 + q.2)

theorem rationalPlace_cast (e : ContactGridEdge) (p : ℚ × ℚ) :
    contactPoint (rationalPlace e p).1 (rationalPlace e p).2 =
      e.place (contactPoint p.1 p.2) := by
  cases hv : e.vertical <;> cases hr : e.reversed <;> ext i <;> fin_cases i <;>
    simp [rationalPlace, ContactGridEdge.place, hv, hr, contactReflect,
      contactVertical, contactHorizontal, contactPoint, Rat.cast_sub, Rat.cast_add, Rat.cast_mul]

def position (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (x : GlobalSite d) : ℚ × ℚ :=
  match (siteEquiv d.vertices d.edges).symm x with
  | Sum.inl i => (17 * (d.coordinate i).1, 17 * (d.coordinate i).2)
  | Sum.inr (e, u) => rationalPlace (d.contactEdge e)
      (ContactRationalLocal.position P (edgeNegative d.bonds e)
        (fun a => ℓ (encodeEdge d.edges e a)) (Sum.inr u))

theorem position_cast (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (x : GlobalSite d) : contactPoint (position d P ℓ x).1 (position d P ℓ x).2 = point d P ℓ x := by
  obtain ⟨x, rfl⟩ := (siteEquiv d.vertices d.edges).surjective x
  cases x with
  | inl i =>
    simp [position, point, contactGridPoint, Rat.cast_mul]
  | inr eu =>
    rcases eu with ⟨e, u⟩
    simp only [position, Equiv.symm_apply_apply, rationalPlace_cast, point,
      globalPosition_internal]
    rfl

end ContinuumCoulomb.ContactRationalGlobal

end

end OAI
