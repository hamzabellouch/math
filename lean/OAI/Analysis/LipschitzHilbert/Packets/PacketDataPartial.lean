import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensity
import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedTreeMaximal

namespace OAI

/-! Physical scale partial sums and their continuous interval maximum
for unrestricted packet data. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

private theorem continuous_interval_max {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => intervalOscillation (fun n => F n x) N 0 N) := by
  classical
  let v := fun (q : Fin (N+1)×Fin (N+1)) (x : X) =>
    if 0≤q.1.val ∧ q.1.val≤q.2.val ∧ q.2.val≤N then ‖F q.2 x-F q.1 x‖ else 0
  have hv (q) : Continuous (v q) := by
    by_cases hq : 0≤q.1.val ∧ q.1.val≤q.2.val ∧ q.2.val≤N
    · simpa only [v,ite_eq_left hq,Pi.sub_apply] using ((hF q.2).sub (hF q.1)).norm
    · simp only [v,ite_eq_right hq]; exact continuous_const
  have h := Continuous.finset_sup' Finset.univ_nonempty (fun q _ => hv q)
  convert h using 1
  funext x
  simp only [intervalOscillation,v,Finset.sup'_apply]


def physicalTreePartial (P : PacketLatticeData N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (n : ℕ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  packetPartialSum (fun j => planarFixedSynthesis
    (fun q : Σ l : P.labels j, Item j l => c j q.1 q.2)
    (fun q k => P.physicalPacket t j q.1 q.2 k) z) n

def physicalTreeMaximal (P : PacketLatticeData N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  intervalOscillation (fun n => P.physicalTreePartial t c n z) N 0 N

theorem physicalTreePartial_continuous (P : PacketLatticeData N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) :
    Continuous (P.physicalTreePartial t c n) := by
  classical
  unfold physicalTreePartial packetPartialSum
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val<n
  · simp only [ite_eq_left hj]
    unfold planarFixedSynthesis
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k => continuous_finsetSum _ fun u _ =>
      continuous_const.mul (P.physicalPacket t j u.1 u.2 k).continuous
  · simp only [ite_eq_right hj]; exact continuous_const

theorem physicalTreeMaximal_continuous (P : PacketLatticeData N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    Continuous (P.physicalTreeMaximal t c) :=
  continuous_interval_max _ (P.physicalTreePartial_continuous t c) N

end LipschitzHilbert.PacketLatticeData

end

end OAI
