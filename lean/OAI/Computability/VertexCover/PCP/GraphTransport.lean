import Mathlib
import OAI.Computability.VertexCover.PCP.SpectralReturn

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]

variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

omit [Fintype V] [Fintype W] in
theorem operator_reindex (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (f : W → ℝ) (w : W) :
    averagingOperator (reindex G vertices ports) f w =
      averagingOperator G (fun v => f (vertices v)) (vertices.symm w) := by
  unfold averagingOperator
  apply Fintype.expect_equiv ports.symm
  intro e
  rfl

theorem energy_reindex (vertices : V ≃ W) (f : W → ℝ) :
    energy (fun v => f (vertices v)) = energy f :=
  mean_equiv vertices (fun w => f w ^ 2)

theorem reindex_spectralCertificate (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (lambda : ℝ) (certificate : SpectralCertificate G lambda) :
    SpectralCertificate (reindex G vertices ports) lambda where
  nonnegative := certificate.nonnegative
  lt_one := certificate.lt_one
  contraction := by
    intro f hf
    have hf' : mean (fun v => f (vertices v)) = 0 :=
      (mean_equiv vertices f).trans hf
    have h := certificate.contraction (fun v => f (vertices v)) hf'
    have hout : energy (averagingOperator (reindex G vertices ports) f) =
        energy (averagingOperator G (fun v => f (vertices v))) := by
      rw [← energy_reindex vertices]
      congr 1
      funext v
      rw [operator_reindex, vertices.symm_apply_apply]
    rw [hout, ← energy_reindex vertices f]
    exact h

end UniqueGames.Foundations.PCP.GraphTransport

end OAI
