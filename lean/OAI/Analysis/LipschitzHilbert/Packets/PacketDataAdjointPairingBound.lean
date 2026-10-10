import OAI.Analysis.LipschitzHilbert.Trees.SourceAdjointPairingBound
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAdjoint

namespace OAI

/-! Forward-adjoint duality for the unrestricted physical packet data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem ordinary_adjoint_pairing_bound (P : PacketLatticeData N κ Label Item)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (hgm : Measurable g) (hgb : ∀ z, ‖g z‖≤1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (hgs : ∀ z, z∉E → g z=0)
    (hint : IntegrableOn (P.ordinaryForwardSum S b u f) E (volume.prod volume)) :
    Integrable (fun z => inner ℂ (P.ordinaryAdjointSum S b u g z) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume‖≤
        ∫ z in E, ‖P.ordinaryForwardSum S b u f z‖ ∂volume.prod volume := by
  refine ⟨integrable_euclidean_inner _ (P.ordinaryAdjointSum_memLp S b u g) hf,?_⟩
  have h := P.ordinary_forward_adjoint_pairing S b hb hb1 u hu f g hf hg
  have hn := congrArg norm h
  rw [RCLike.norm_conj] at hn
  rw [←hn]
  exact (supported_inner_integral_le (volume.prod volume) E hE _ g hint hgm hgb hgs).2

end LipschitzHilbert.PacketLatticeData

end

end OAI
