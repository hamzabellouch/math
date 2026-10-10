import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityPowerForest
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient

namespace OAI

/-! Convert the actual density-forest radial assignment into the two
coordinate bounds required by original-packet concentration. -/
noncomputable section
namespace LipschitzHilbert

theorem SlopeBox.coordinates_of_radius_le (T : SlopeBox) {z : ℝ×ℝ} {K : ℝ}
    (h : T.radius z ≤ K) :
    |z.1-T.x| ≤ K*T.length ∧ |(z.2-T.y)-T.slope*(z.1-T.x)| ≤ K*T.width := by
  have hx : |T.horizontal z| ≤ K :=
    (le_add_of_nonneg_right (abs_nonneg (T.transverse z))).trans h
  have hy : |T.transverse z| ≤ K :=
    (le_add_of_nonneg_left (abs_nonneg (T.horizontal z))).trans h
  change |(z.1-T.x)/T.length| ≤ K at hx
  change |((z.2-T.y)-T.slope*(z.1-T.x))/T.width| ≤ K at hy
  rw [abs_div,abs_of_pos T.length_pos] at hx
  rw [abs_div,abs_of_pos T.width_pos] at hy
  exact ⟨(div_le_iff₀ T.length_pos).mp hx,(div_le_iff₀ T.width_pos).mp hy⟩

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assigned_packet_geometry_of_density {τ : Type*}
    (P : SourceLabeledLattice N κ Label Item) (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (T : τ → SlopeBox) (oldSlope L a : ℝ)
    (hL : 2 ≤ L) (ha : 0 ≤ a)
    (hshort : ∀ q ∈ packets, P.length q.1 ≤ (T (assigned q)).length)
    (hwidth : ∀ q ∈ packets, P.width ≤ (T (assigned q)).width)
    (hrad : ∀ q ∈ packets, (T (assigned q)).radius
      (P.actualX q.1 q.2.1 q.2.2,
        P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2) ≤ L^a) :
    (∀ q ∈ packets,
      |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
        L^(a+1)*(T (assigned q)).length) ∧
    (∀ q ∈ packets,
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
        P.actualX q.1 q.2.1 q.2.2-
        ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
          L^(a+1)*(T (assigned q)).width) := by
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hp : 1 ≤ L^a := Real.one_le_rpow hL1 ha
  have hpow : L^a+1 ≤ L^(a+1) := by
    rw [Real.rpow_add hLp,Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hLp.le a)]
  constructor
  · intro q hq
    have hx := ((T (assigned q)).coordinates_of_radius_le (hrad q hq)).1
    change |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x| ≤
      L^a*(T (assigned q)).length at hx
    have hh := mul_le_mul_of_nonneg_right hpow (T (assigned q)).length_pos.le
    linarith [hshort q hq]
  · intro q hq
    have hy := ((T (assigned q)).coordinates_of_radius_le (hrad q hq)).2
    have heq :
        (P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2-
          (T (assigned q)).y)-(T (assigned q)).slope*
            (P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x) =
        P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
          P.actualX q.1 q.2.1 q.2.2-
          ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x) := by ring
    change |(P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2-
      (T (assigned q)).y)-(T (assigned q)).slope*
        (P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x)| ≤ L^a*(T (assigned q)).width at hy
    rw [heq] at hy
    have hh := mul_le_mul_of_nonneg_right hpow (T (assigned q)).width_pos.le
    linarith [hwidth q hq]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
