import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakAddLemmas

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def realSecondScalarForcing {n : ℕ} (B w : Coord n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (k l : Fin n) (x : Coord n) : ℝ :=
  B x*H k l x+coordPartial B x l*U k x+
    coordPartial B x k*U l x+coordPartial (fun y ↦ coordPartial B y k) x l*w x

theorem real_weak_second_scalar_forcing {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (B w : Coord n → ℝ) (U : Fin n → Coord n → ℝ)
    (H : Fin n → Fin n → Coord n → ℝ)
    (hB : ContDiff ℝ ∞ B) (hw : MemLp w 2 (volume.restrict K))
    (hU : ∀ a, MemLp (U a) 2 (volume.restrict K))
    (hH : ∀ a b, MemLp (H a b) 2 (volume.restrict K))
    (hfirst : ∀ a psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, w x*coordPartial psi x a)=-(∫ x in K, U a x*psi x))
    (hsecond : ∀ a b psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, U a x*coordPartial psi x b)=-(∫ x in K, H a b x*psi x))
    (k l : Fin n) :
    MemLp (fun x ↦ B x*U k x+coordPartial B x k*w x) 2 (volume.restrict K) ∧
    MemLp (realSecondScalarForcing B w U H k l) 2 (volume.restrict K) ∧
    ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ (B x*U k x+coordPartial B x k*w x)*coordPartial psi x l) K ∧
      IntegrableOn (fun x ↦ realSecondScalarForcing B w U H k l x*psi x) K ∧
      (∫ x in K, (B x*U k x+coordPartial B x k*w x)*coordPartial psi x l) =
        -(∫ x in K, realSecondScalarForcing B w U H k l x*psi x) := by
  have h1 := real_interior_weak_product hK (U k) (H k l) B
    (hU k) (hH k l) hB l (hsecond k l)
  have h2 := real_interior_weak_product hK w (U l) (fun x ↦ coordPartial B x k)
    hw (hU l) (real_coordPartial_smooth B hB k) l (hfirst l)
  have h := real_interior_weak_add hK _ _ _ _ h1.1 h2.1 h1.2.1 h2.2.1 l
    (fun psi hp hc hs ↦ (h1.2.2 psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ (h2.2.2 psi hp hc hs).2.2)
  unfold realSecondScalarForcing
  simpa only [add_assoc] using h

end
end Yau

end OAI
