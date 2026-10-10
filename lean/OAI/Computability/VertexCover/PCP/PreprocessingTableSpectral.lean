import Mathlib
import OAI.Computability.VertexCover.PCP.PreprocessingOverlayTables
import OAI.Computability.VertexCover.PCP.LazySpectral

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

private theorem portGraph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

theorem materialize_portGraph {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) :
    PortTables.portGraph (PreprocessingOverlayTables.materialize G ports) =
      GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports := by
  apply portGraph_ext
  intro x
  rw [PortTables.portGraph_rot, PreprocessingOverlayTables.rotation_materialize]
  rfl

theorem overlay_portGraph {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.portGraph (PreprocessingOverlayTables.overlay G H) =
      GraphTransport.reindex
        (Overlay.portGraph (PortTables.portGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (PreprocessingOverlayTables.overlayPorts d e) := by
  unfold PreprocessingOverlayTables.overlay
  rw [materialize_portGraph]
  rfl

theorem overlay_rotation_eq {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (x : Fin n × Fin (d + e)) :
    PortTables.rotation (PreprocessingOverlayTables.overlay G H) x =
      (GraphTransport.reindex
        (Overlay.portGraph (PortTables.portGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (PreprocessingOverlayTables.overlayPorts d e)).rot x := by
  change (PortTables.portGraph (PreprocessingOverlayTables.overlay G H)).rot x = _
  rw [overlay_portGraph]

theorem lazy_portGraph {n d : Nat} (G : PortTables.Table n d) :
    PortTables.portGraph (PreprocessingOverlayTables.lazy G) =
      GraphTransport.reindex (lazyGraph (PortTables.portGraph G))
        (Equiv.refl _) (PreprocessingOverlayTables.lazyPorts d) := by
  unfold PreprocessingOverlayTables.lazy
  rw [materialize_portGraph]
  rfl

theorem lazy_rotation_eq {n d : Nat} (G : PortTables.Table n d)
    (x : Fin n × Fin (2 * d)) :
    PortTables.rotation (PreprocessingOverlayTables.lazy G) x =
      (GraphTransport.reindex (lazyGraph (PortTables.portGraph G))
        (Equiv.refl _) (PreprocessingOverlayTables.lazyPorts d)).rot x := by
  change (PortTables.portGraph (PreprocessingOverlayTables.lazy G)).rot x = _
  rw [lazy_portGraph]

theorem overlay_certificate_seven_eighths {n d e : Nat}
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (hn : 0 < n) (hdegree : d = e + 1) (he : 8 ≤ e)
    (hH : SpectralCertificate (ExpanderTables.graph H) (1 / 2 : ℝ)) :
    SpectralCertificate (PortTables.portGraph (PreprocessingOverlayTables.overlay G H))
      (7 / 8 : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [overlay_portGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply Overlay.spectralCertificate_seven_eighths
    (PortTables.portGraph G) (ExpanderTables.graph H)
  · simpa only [Fintype.card_fin] using hdegree
  · simp only [Fintype.card_fin]
    omega
  · exact hH

theorem lazy_certificate_31_32 {n d : Nat} (G : PortTables.Table n d)
    (hd : 0 < d) (hG : SpectralCertificate (PortTables.portGraph G) (7 / 8 : ℝ)) :
    SpectralCertificate (PortTables.portGraph (PreprocessingOverlayTables.lazy G))
      (31 / 32 : ℝ) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [lazy_portGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (LazySpectral.lazy_certificate_31_32 (PortTables.portGraph G) hG)

end UniqueGames.Foundations.PCP.PreprocessingTableSpectral

end OAI
