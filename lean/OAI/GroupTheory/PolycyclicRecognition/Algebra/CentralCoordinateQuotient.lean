import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralCoordinateHom

namespace OAI

/-! # Detecting the noncentral coordinates in an abelian quotient -/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type*} [Group G] {d e : ℕ}

theorem orderedWord_map_standard (q : G →* Multiplicative (Fin d → ℤ))
    (a : Fin d → G)
    (ha : ∀ i, q (a i) = Multiplicative.ofAdd (Pi.basisFun ℤ (Fin d) i))
    (x : Fin d → ℤ) : q (orderedWord a x) = Multiplicative.ofAdd x := by
  simp only [orderedWord, map_list_prod, List.map_ofFn, Function.comp_def,
    map_zpow, ha, ← ofAdd_zsmul, List.prod_ofFn, ← ofAdd_sum]
  congr 1
  exact (Pi.basisFun ℤ (Fin d)).sum_equivFun x

theorem centralCoordinateHom_quotient (z : Multiplicative (Fin e → ℤ) →* G)
    (hz : ∀ v, z v ∈ Subgroup.center G) (a : Fin d → G)
    (c : Fin d → Fin d → Fin e → ℤ)
    (hc : ∀ i j, ⁅a i, a j⁆ = z (Multiplicative.ofAdd (c i j)))
    (q : G →* Multiplicative (Fin d → ℤ)) (hqz : ∀ v, q (z v) = 1)
    (ha : ∀ i, q (a i) = Multiplicative.ofAdd (Pi.basisFun ℤ (Fin d) i))
    (p : BilinearCentralGroup (triangularBilinear c)) :
    q (centralCoordinateHom z hz a c hc p) = Multiplicative.ofAdd p.1 := by
  change q (z (Multiplicative.ofAdd p.2) * orderedWord a p.1) = _
  rw [map_mul, hqz, one_mul, orderedWord_map_standard q a ha]

theorem centralCoordinateHom_bijective (z : Multiplicative (Fin e → ℤ) →* G)
    (hz : ∀ v, z v ∈ Subgroup.center G) (a : Fin d → G)
    (c : Fin d → Fin d → Fin e → ℤ)
    (hc : ∀ i j, ⁅a i, a j⁆ = z (Multiplicative.ofAdd (c i j)))
    (q : G →* Multiplicative (Fin d → ℤ)) (hqz : ∀ v, q (z v) = 1)
    (ha : ∀ i, q (a i) = Multiplicative.ofAdd (Pi.basisFun ℤ (Fin d) i))
    (hz_inj : Function.Injective z) (hz_range : z.range = q.ker) :
    Function.Bijective (centralCoordinateHom z hz a c hc) := by
  constructor
  · intro p r h
    have hx : p.1 = r.1 := by
      have hh := congrArg q h
      rw [centralCoordinateHom_quotient z hz a c hc q hqz ha,
        centralCoordinateHom_quotient z hz a c hc q hqz ha] at hh
      exact Multiplicative.ofAdd.injective hh
    have hy : p.2 = r.2 := by
      change z (Multiplicative.ofAdd p.2) * orderedWord a p.1 =
        z (Multiplicative.ofAdd r.2) * orderedWord a r.1 at h
      rw [hx] at h
      exact Multiplicative.ofAdd.injective (hz_inj (mul_right_cancel h))
    exact Prod.ext hx hy
  · intro g
    let x := (q g).toAdd
    have hk : g * (orderedWord a x)⁻¹ ∈ q.ker := by
      change q (g * (orderedWord a x)⁻¹) = 1
      rw [map_mul, map_inv, orderedWord_map_standard q a ha]
      exact mul_inv_cancel (q g)
    have hr : g * (orderedWord a x)⁻¹ ∈ z.range := by rw [hz_range]; exact hk
    obtain ⟨u, hu⟩ := hr
    refine ⟨(x, u.toAdd), ?_⟩
    change z u * orderedWord a x = g
    rw [hu, inv_mul_cancel_right]

end PolycyclicRecognition

end

end OAI
