import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedGram
import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingCoefficients

namespace OAI

/-! Actual analyzing coefficients and L2 duality for a selected packet
set. Only the synthesis estimate for those same coefficients is needed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

 theorem l2_self_pairing_energy_le {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (mu : Measure X) (F g : X → E) (S A : ℝ) (hS : 0≤S) (hA : 0≤A)
    (hF : MemLp F 2 mu) (hg : MemLp g 2 mu)
    (hp : (S : ℂ)=∫ x, inner ℂ (F x) (g x) ∂mu)
    (hbound : (∫ x, ‖F x‖^2 ∂mu)≤A*S) :
    S≤A*∫ x, ‖g x‖^2 ∂mu := by
  have hcs : S≤‖hF.toLp F‖*‖hg.toLp g‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (hF.toLp F) (hg.toLp g)
    rw [memLp_inner_integral mu F g hF hg,←hp,Complex.norm_real,Real.norm_of_nonneg hS] at h
    exact h
  have hsq := pow_le_pow_left₀ hS hcs 2
  rw [mul_pow,memLp_toL2_norm_sq mu F hF,memLp_toL2_norm_sq mu g hg] at hsq
  have hnonneg : 0≤∫ x, ‖g x‖^2 ∂mu := integral_nonneg fun _ => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_right hbound hnonneg
  by_cases hz : S=0
  · rw [hz]
    exact mul_nonneg hA hnonneg
  · have hs : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
    apply le_of_mul_le_mul_left (a := S) _ hs
    nlinarith

 theorem finite_analyzing_self_pairing {X I K : Type*} [MeasurableSpace X]
    [Fintype K] (mu : Measure X) (area : I → ℝ) (wave : I → K → X → ℂ)
    (g : X → EuclideanSpace ℂ K) (S : Finset I)
    (ha : ∀ i∈S, area i≠0)
    (hint : ∀ i∈S, ∀ k, Integrable (fun x => g x k*conj (wave i k x)) mu) :
    ((∑ i∈S, area i*‖analyzingCoefficient mu area wave g i‖^2 : ℝ) : ℂ)=
      ∫ x, inner ℂ
        (∑ i∈S, WithLp.toLp 2 (fun k => analyzingCoefficient mu area wave g i k*wave i k x))
        (g x) ∂mu := by
  classical
  have hp := analyzingCoefficient_self_pairing mu (fun i : S => area i)
    (fun i : S => wave i) g (fun i => ha i i.property) (fun i k => hint i i.property k)
  change ((∑ i : S, area i*‖analyzingCoefficient mu area wave g i‖^2 : ℝ) : ℂ)=_ at hp
  have he : (∑ i : S, area i*‖analyzingCoefficient mu area wave g i‖^2)=
      ∑ i∈S, area i*‖analyzingCoefficient mu area wave g i‖^2 :=
    Finset.sum_coe_sort S (fun i : I => area i*‖analyzingCoefficient mu area wave g i‖^2)
  rw [he] at hp
  rw [hp]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  ext k
  simp only [diagonalSynthesis,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp,
    ]
  change (∑ i : S, analyzingCoefficient mu area wave g i k*wave i k x)=_
  exact Finset.sum_coe_sort S (fun i : I => analyzingCoefficient mu area wave g i k*wave i k x)

namespace SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- Coefficients of the original physical packets, before selector masks. -/
def ordinaryCoefficient (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun q : P.PacketIndex => P.length q.1*P.width)
    (fun q k => P.physicalPacket 0 q.1 q.2.1 q.2.2 k) g ⟨j,⟨l,u⟩⟩

 theorem selected_ordinary_coefficient_energy (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hg : MemLp g 2 (volume.prod volume)) (S : Finset P.PacketIndex)
    (A : ℝ) (hA : 0≤A)
    (hbound : (∫ z, ‖∑ q∈S, P.packetVector (P.ordinaryCoefficient g) q z‖^2
      ∂volume.prod volume)≤A*P.packetEnergySum (P.ordinaryCoefficient g) S) :
    P.packetEnergySum (P.ordinaryCoefficient g) S≤A*∫ z, ‖g z‖^2 ∂volume.prod volume := by
  have he : P.packetEnergySum (P.ordinaryCoefficient g) S=
      ∑ q∈S, (P.length q.1*P.width)*‖P.ordinaryCoefficient g q.1 q.2.1 q.2.2‖^2 := by
    apply Finset.sum_congr rfl
    intro q _
    ring
  apply l2_self_pairing_energy_le (volume.prod volume) _ g _ A _ hA
    (memLp_finsetSum S (fun q _ => P.packetVector_memLp (P.ordinaryCoefficient g) q)) hg _ hbound
  · exact Finset.sum_nonneg fun q _ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  · rw [he]
    apply finite_analyzing_self_pairing
    · intro q _
      exact (mul_pos (P.length_pos q.1) P.width_pos).ne'
    · intro q _ k
      have hgk : MemLp (fun z => g z k) 2 (volume.prod volume) := (memLp_piLp_iff.mp hg) k
      exact hgk.integrable_mul ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2
        (volume.prod volume)).star

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
