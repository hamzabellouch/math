import Mathlib.Tactic.NormNum
import OAI.Computability.BinPacking.PCP.PreprocessingLazyWords

namespace OAI

namespace BinPackingGames.Foundations.PCP.LazySpectral

open PoweringWalks SpectralReturn

noncomputable section

variable {V D : Type*}

theorem half_sum_sq_le (a b : ℝ) : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem lazy_energy_le_average [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) :
    energy (averagingOperator (lazyGraph G) f) ≤
      (energy f + energy (averagingOperator G f)) / 2 := by
  calc
    energy (averagingOperator (lazyGraph G) f) =
        mean (fun v => ((f v + averagingOperator G f v) / 2) ^ 2) := by
      unfold energy
      congr 1
      funext v
      rw [PoweringLazy.averagingOperator_lazy]
    _ ≤ mean (fun v => (f v ^ 2 + averagingOperator G f v ^ 2) / 2) :=
      mean_mono (fun v => half_sum_sq_le _ _)
    _ = mean (fun v => (1 / 2 : ℝ) * (f v ^ 2 + averagingOperator G f v ^ 2)) := by
      congr 1
      funext v
      ring
    _ = (1 / 2 : ℝ) * (energy f + energy (averagingOperator G f)) := by
      rw [mean_mul_left, mean_add]
      rfl
    _ = (energy f + energy (averagingOperator G f)) / 2 := by ring

theorem lazy_energy_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (lazyGraph G) f) ≤
      ((1 + lambda ^ 2) / 2) * energy f := by
  calc
    energy (averagingOperator (lazyGraph G) f) ≤
        (energy f + energy (averagingOperator G f)) / 2 := lazy_energy_le_average G f
    _ ≤ (energy f + lambda ^ 2 * energy f) / 2 := by
      have h := hG.contraction f hf
      linarith
    _ = ((1 + lambda ^ 2) / 2) * energy f := by ring

theorem lazy_certificate_31_32 [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (hG : SpectralCertificate G (7 / 8)) :
    SpectralCertificate (lazyGraph G) (31 / 32) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := lazy_energy_bound G (7 / 8) hG f hf
    have hcoef : ((1 + (7 / 8 : ℝ) ^ 2) / 2) ≤ (31 / 32 : ℝ) ^ 2 := by norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end BinPackingGames.Foundations.PCP.LazySpectral

namespace BinPackingGames.Foundations.PCP.PreprocessingTableSpectral

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

end BinPackingGames.Foundations.PCP.PreprocessingTableSpectral

end OAI
