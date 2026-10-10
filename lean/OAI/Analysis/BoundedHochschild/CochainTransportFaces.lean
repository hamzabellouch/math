import OAI.Analysis.BoundedHochschild.FiniteGroupCochainAverages

namespace OAI

/-! Interaction of independent unitary transports with Hochschild faces.
Deleting a boundary unitary gives the transport of the corresponding face. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma cochainUnitaryTransport_leftCoboundary {n : ℕ}
    (u : Fin (n + 2) → unitary M) (f : Cochain M n) :
    cochainUnitaryTransport u (leftCoboundary f) =
      leftCoboundary (cochainUnitaryTransport (Fin.tail u) f) := by
  ext x
  have ht : (fun i : Fin n => cochainUnitaryTuple u x i.succ) =
      cochainUnitaryTuple (Fin.tail u) (Fin.tail x) := by
    ext i
    simp only [cochainUnitaryTuple, Fin.tail, Fin.castSucc_succ]
  simp only [cochainUnitaryTransport_apply, leftCoboundary_apply]
  rw [ht]
  change star (u 0 : M) *
      (((u 0 : M) * x 0 * star (u (0 : Fin (n + 1)).succ : M)) *
        f (cochainUnitaryTuple (Fin.tail u) (Fin.tail x))) * (u (Fin.last (n + 1)) : M) =
    x 0 * (star (u (0 : Fin (n + 1)).succ : M) *
      f (cochainUnitaryTuple (Fin.tail u) (Fin.tail x)) * (u (Fin.last (n + 1)) : M))
  calc
    _ = (star (u 0 : M) * (u 0 : M)) * (x 0 *
        (star (u (0 : Fin (n + 1)).succ : M) *
          f (cochainUnitaryTuple (Fin.tail u) (Fin.tail x)) * (u (Fin.last (n + 1)) : M))) := by
      simp only [mul_assoc]
    _ = _ := by rw [Unitary.star_mul_self_of_mem (u 0).property, one_mul]

lemma cochainUnitaryTransport_rightCoboundary {n : ℕ}
    (u : Fin (n + 2) → unitary M) (f : Cochain M n) :
    cochainUnitaryTransport u (rightCoboundary f) =
      rightCoboundary (cochainUnitaryTransport (fun i => u i.castSucc) f) := by
  ext x
  have ht : (fun i : Fin n => cochainUnitaryTuple u x i.castSucc) =
      cochainUnitaryTuple (fun i => u i.castSucc) (fun i => x i.castSucc) := by
    ext i
    simp only [cochainUnitaryTuple, Fin.castSucc_succ]
  simp only [cochainUnitaryTransport_apply, rightCoboundary_apply]
  rw [ht]
  change star (u 0 : M) *
      (f (cochainUnitaryTuple (fun i => u i.castSucc) (fun i => x i.castSucc)) *
        ((u (Fin.last n).castSucc : M) * x (Fin.last n) * star (u (Fin.last (n + 1)) : M))) *
          (u (Fin.last (n + 1)) : M) =
    (star (u 0 : M) * f (cochainUnitaryTuple (fun i => u i.castSucc) (fun i => x i.castSucc)) *
      (u (Fin.last n).castSucc : M)) * x (Fin.last n)
  simp only [mul_assoc, Unitary.star_mul_self_of_mem (u (Fin.last (n + 1))).property, mul_one]

end BoundedHochschild.KadisonRingrose

end

end OAI
