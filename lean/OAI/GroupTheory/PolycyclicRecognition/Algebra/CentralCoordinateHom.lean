import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularBilinearFactor

namespace OAI

/-! # A homomorphism from collected central coordinates -/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type*} [Group G] {d e : ℕ}

def centralCoordinateHom (z : Multiplicative (Fin e → ℤ) →* G)
    (hz : ∀ v, z v ∈ Subgroup.center G) (a : Fin d → G)
    (c : Fin d → Fin d → Fin e → ℤ)
    (hc : ∀ i j, ⁅a i, a j⁆ = z (Multiplicative.ofAdd (c i j))) :
    BilinearCentralGroup (triangularBilinear c) →* G where
  toFun p := z (Multiplicative.ofAdd p.2) * orderedWord a p.1
  map_one' := by
    change z (Multiplicative.ofAdd 0) * orderedWord a 0 = 1
    rw [orderedWord_zero]
    exact mul_one (z 1) |>.trans (map_one z)
  map_mul' p q := by
    change z (Multiplicative.ofAdd (p.2 + q.2 + triangularBilinear c p.1 q.1)) *
      orderedWord a (p.1 + q.1) =
        (z (Multiplicative.ofAdd p.2) * orderedWord a p.1) *
          (z (Multiplicative.ofAdd q.2) * orderedWord a q.1)
    have hw := orderedWord_mul z hz a (fun i j => Multiplicative.ofAdd (c i j)) hc p.1 q.1
    rw [triangularFactor_ofAdd] at hw
    have hcomm : z (Multiplicative.ofAdd q.2) * orderedWord a p.1 =
        orderedWord a p.1 * z (Multiplicative.ofAdd q.2) :=
      (Subgroup.mem_center_iff.mp (hz _) _).symm
    calc
      _ = (z (Multiplicative.ofAdd p.2) * z (Multiplicative.ofAdd q.2)) *
          (z (Multiplicative.ofAdd (triangularBilinear c p.1 q.1)) *
            orderedWord a (p.1 + q.1)) := by
        rw [ofAdd_add, ofAdd_add, map_mul, map_mul]
        simp only [mul_assoc]
      _ = (z (Multiplicative.ofAdd p.2) * z (Multiplicative.ofAdd q.2)) *
          (orderedWord a p.1 * orderedWord a q.1) := by rw [← hw]
      _ = z (Multiplicative.ofAdd p.2) *
          (z (Multiplicative.ofAdd q.2) * orderedWord a p.1) * orderedWord a q.1 := by
        simp only [mul_assoc]
      _ = z (Multiplicative.ofAdd p.2) *
          (orderedWord a p.1 * z (Multiplicative.ofAdd q.2)) * orderedWord a q.1 := by
        rw [hcomm]
      _ = _ := by simp only [mul_assoc]

end PolycyclicRecognition

end

end OAI
