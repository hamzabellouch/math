import OAI.Algebra.AuslanderReiten.Homology.TBoundaryCochain
import OAI.Algebra.AuslanderReiten.Homology.ProjectiveNullhomotopyAbove

namespace OAI

noncomputable section

namespace ArExplicit.T

variable {k : Type*} [Field k] [CharP k 2] (q : k)
local notation "R" => T k q
local notation "Ae" => AbsoluteBar.Enveloping k R

def pB (H : kˣ) (n : ℕ) :
    AbsoluteBar.twistedObject k R (TrivialExtension.twist H) (n + 3) →ₗ[Ae]
      AbsoluteBar.moduleObject k R (n + 1) :=
  (P q n).comp (B q H (n + 3))

private theorem B_comm (H : kˣ) (n : ℕ) :
    (AbsoluteBar.differential k R (n + 1)).comp (B q H (n + 1)) =
      (B q H n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) n) := by
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun (B_differential q H n) x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hh
  exact add_right_cancel (hh.trans
    (SparseParity.module_add_self_eq_zero (k := k) (B q H n
      (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) n x))).symm)

private theorem P_comm (n : ℕ) :
    (AbsoluteBar.differential k R (n + 1)).comp (P q (n + 1)) =
      (P q n).comp (AbsoluteBar.differential k R (n + 4)) := by
  apply LinearMap.ext
  intro x
  exact P_differential q (n + 1) x

theorem pB_comm (H : kˣ) (n : ℕ) :
    (AbsoluteBar.differential k R (n + 1)).comp (pB q H (n + 1)) =
      (pB q H n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n + 3)) := by
  unfold pB
  rw [← LinearMap.comp_assoc, P_comm, LinearMap.comp_assoc, B_comm, ← LinearMap.comp_assoc]

theorem exists_G (H : kˣ) :
    ∃ G : (n : ℕ) →
      AbsoluteBar.twistedObject k R (TrivialExtension.twist H) (n + 2) →ₗ[Ae]
        AbsoluteBar.moduleObject k R (n + 1),
      (AbsoluteBar.differential k R 0).comp (G 0) = Z q H ∧
      ∀ n, pB q H n = (AbsoluteBar.differential k R (n + 1)).comp (G (n + 1)) +
        (G n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n + 2)) := by
  apply ProjectiveNullhomotopyAbove.exists_homotopy
    (P := fun n => AbsoluteBar.moduleObject k R (n + 1))
    (Q := fun n => AbsoluteBar.twistedObject k R (TrivialExtension.twist H) (n + 1))
    (fun n => AbsoluteBar.differential k R (n + 1))
    (fun n => AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n + 1))
    (pB q H) (fun n => AbsoluteBar.twistedProjective k R (TrivialExtension.twist H) n)
  · intro n
    apply LinearMap.ext
    exact AbsoluteBar.boundary_squared k R (n + 1)
  · intro n
    exact AbsoluteBar.differential_exact k R (n + 1)
  · exact pB_comm q H
  · intro x
    exact ⟨AbsoluteBar.contraction k R 0 x, AbsoluteBar.augmentation_contraction k R x⟩
  · exact AbsoluteBar.differential_exact k R 0
  · change (AbsoluteBar.differential k R 0).comp ((P q 0).comp (B q H 3)) = _
    rw [← LinearMap.comp_assoc, P_augmentation, pB_bottom]

def G (H : kˣ) (n : ℕ) :
    AbsoluteBar.twistedObject k R (TrivialExtension.twist H) (n + 2) →ₗ[Ae]
      AbsoluteBar.moduleObject k R (n + 1) :=
  Classical.choose (exists_G q H) n

theorem G_augmentation (H : kˣ) :
    (AbsoluteBar.differential k R 0).comp (G q H 0) = Z q H :=
  (Classical.choose_spec (exists_G q H)).1

theorem G_equation (H : kˣ) (n : ℕ) :
    pB q H n = (AbsoluteBar.differential k R (n + 1)).comp (G q H (n + 1)) +
      (G q H n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n + 2)) :=
  (Classical.choose_spec (exists_G q H)).2 n

end ArExplicit.T

end

end OAI
