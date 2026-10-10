import OAI.Analysis.LipschitzHilbert.Fourier.FiniteNormalizedKernelForm
import OAI.Analysis.LipschitzHilbert.Packets.JointVectorPacketAverage

namespace OAI

/-! The complete finite scale/direction convolution sum follows from
the bounds on its actual normalized finite packet models. Every carrier
shares each spatial lattice, before taking the probability average. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

theorem normalized_lattice_average_bound
    (F G : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (topLength width scale ratioBound C : ℝ) (order : ℕ)
    (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
    (hratio : 1≤ratioBound) (hscale : |scale/width|≤ratioBound)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order)≤C)
    (hG : planarProfileConstant (analysisProfile G q nu) (2*order)≤C)
    (b : ∀ j, labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume))
    (hf1 : ∀ k, Integrable (fun z => f z k) (volume.prod volume))
    (hg : ∀ k, Measurable (fun z => g z k)) (hg1 : ∀ k z, ‖g z k‖≤1)
    (B : ℝ)
    (hFinite : ∀ (origin : ∀ j, labels j → ℝ×ℝ) (S : Finset (LatticeSiteIndex labels)),
      let P := finiteNormalizedPacketLattice F q nu topLength width scale ratioBound C order
        htop hwidth hC horder hratio hscale labels origin theta center S hprofile
      let alt := fun (j : Fin N) (l : P.labels j)
        (_a : finiteSiteFiber labels S j l.val) (_k : κ) => analysisProfile G q nu
      let hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound :=
        fun _ _ _ _ => hG
      ‖∫ z, inner ℂ (∑ a : P.PacketIndex,
        P.crossPacketValue alt hAlt 0 b u g z a) (f z) ∂volume.prod volume‖≤B) :
    let length := fun i : LatticeRow labels => topLength/(2:ℝ)^i.1.val
    let KA := fun (i : LatticeRow labels) (k : κ) => horizontalFrequencyKernel
      (scaledFrequencyWindow F (length i) width (theta i.1 i.2) (2*Real.pi*center k)
        (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne') nu q (length i) (theta i.1 i.2)
    let KB := fun (i : LatticeRow labels) (k : κ) => verticalFrequencyKernel
      (scaledFrequencyWindow G (length i) width (theta i.1 i.2) (2*Real.pi*center k)
        (div_pos htop (pow_pos (by norm_num) _)).ne' hwidth.ne') nu q width (center k)
    ‖∑ i : LatticeRow labels, ∑ k, ∫ x, b i.1 i.2 k (u x)*
      kernelConvolution (KA i k) (kernelConvolution (KB i k) (fun z => f z k)) x*
      star (g x k) ∂volume.prod volume‖≤B := by
  intro length KA KB
  apply joint_vector_convolution_packet_bound
    (fun i k z => KA i k z) (fun i k z => KB i k z)
    (fun _ k z => f z k) (fun i k z => b i.1 i.2 k (u z)) (fun _ k z => g z k)
    (fun i k => (KA i k).integrable) (fun i k => (KB i k).integrable)
    (fun _ k => hf1 k) (fun i k => (hb i.1 i.2 k).comp hu) (fun _ k => hg k)
    (fun _ _ => 1) (fun _ _ => 1) (fun i k z => hb1 i.1 i.2 k (u z))
    (fun _ k z => hg1 k z) length (fun _ => width) (fun i => theta i.1 i.2)
    (fun i => div_pos htop (pow_pos (by norm_num) i.1.val)) (fun _ => hwidth) B
  intro origin S
  let R := S.map (latticeSiteProductEquiv labels).symm.toEmbedding
  let O := fun j l => origin (⟨j,l⟩ : LatticeRow labels)
  have hm := hFinite O R
  have heq := finite_normalized_kernel_form F q nu topLength width scale ratioBound C order
    htop hwidth hC horder hratio hscale labels O theta center R hprofile G hG b u g f hf
  dsimp only at hm heq
  rw [heq] at hm
  dsimp only [R] at hm
  rw [sum_joint_lattice_sites] at hm
  exact hm

end LipschitzHilbert.PacketRepresentation

end

end OAI
