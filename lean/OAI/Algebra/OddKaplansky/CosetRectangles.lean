import OAI.Algebra.OddKaplansky.IdempotentFree

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4

section
namespace OddKaplansky.CosetMatrix
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G] [Fintype G] (T : Subgroup G)
variable [IsMulCommutative T]
local instance cosetRectangularCommGroup : CommGroup T := { (inferInstance : Group T) with mul_comm := mul_comm' }
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hexp : ∀ t : T, t^p=1)
include hexp in
lemma representation_rectangular (e : MonoidAlgebra K G) (he : e*e=e)
    {W : Type portUniverse3} {N : Type portUniverse4} [Fintype W] [Fintype N]
    (hw : Fintype.card W = Fintype.card G)
    (hn : Fintype.card N = Module.finrank K (LinearMap.range (Algebra.lmul K (MonoidAlgebra K G) e))) :
    ∃ (J : Matrix W N (Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T)))
      (Y : Matrix N W (Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T))),
      Y*J=1 ∧ J*Y=Matrix.diagonal (fun _ : W => representation T e) := by
  let : IsLocalRing (D (K := K) T) := LocalAlgebra.isLocal p hexp
  have hv : Module.finrank K ((G ⧸ T) → D (K := K) T) = Fintype.card G := by
    rw [(unpack (K := K) T).finrank_eq,Module.finrank_eq_card_basis (MonoidAlgebra.basis G K)]
  obtain ⟨J,Y,hYJ,hJY⟩ := IdempotentFree.rectangular (K := K) (endomorphism T e)
    (endomorphism_idempotent T e he) (hw.trans hv.symm) (hn.trans (endomorphism_rank T e).symm)
  let φ := (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm
  refine ⟨fun w n => φ (J w n),fun n w => φ (Y n w),?_,?_⟩
  · funext n n'
    change (∑ x, φ (Y n x) * φ (J x n')) = (1 : Matrix N N (Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T))) n n'
    have hh := congrArg (fun F => φ (F n n')) hYJ
    simpa only [Matrix.mul_apply,map_sum,map_mul,Matrix.one_apply,apply_ite,map_one,map_zero] using hh
  · funext w w'
    change (∑ x, φ (J w x) * φ (Y x w')) = (Matrix.diagonal (fun _ : W => representation T e)) w w'
    have hh := congrArg (fun F => φ (F w w')) hJY
    have hφ : φ (endomorphism T e) = representation T e := by
      exact (Matrix.toLinAlgEquiv' (R := D (K := K) T) (n := G ⧸ T)).symm_apply_apply _
    simpa only [Matrix.mul_apply,map_sum,map_mul,Matrix.diagonal_apply,apply_ite,map_zero,hφ] using hh
end
end OddKaplansky.CosetMatrix

end

end OAI
