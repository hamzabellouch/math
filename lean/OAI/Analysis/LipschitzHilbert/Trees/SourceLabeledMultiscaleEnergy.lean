import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeMultiscaleEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedLattice

namespace OAI

/-! The original finitely labeled family inherits multiscale synthesis
through its exact slot partition. The only additional factor is the
explicit fixed label bound, with no scale or vector-dimension loss. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def physicalLabeledSynthesis (P : SourceLabeledLattice N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ j, planarFixedSynthesis (fun p : Σ l : P.labels j, Item j l => c j p.1 p.2)
    (fun p k => P.physicalPacket t j p.1 p.2 k) z

theorem physicalLabeledSynthesis_memLp (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    MemLp (P.physicalLabeledSynthesis t c) 2 (volume.prod volume) :=
  memLp_finsetSum _ (fun _ _ => planarFixedSynthesis_memLp _ _)

theorem physicalLabeledSynthesis_eq_slots (P : SourceLabeledLattice N κ Label Item)
    {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    (∑ s : Fin B, ∑ j, planarFixedSynthesis
      (fun u : P.SlotItem hcard s j => c j u.1.1 u.1.2)
      ((P.slotted hcard s).physicalPacket t j) z) = P.physicalLabeledSynthesis t c z := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  ext k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,planarFixedSynthesis,WithLp.ofLp_toLp,
    P.slotted_physicalPacket hcard]
  simpa only [Fintype.sum_sigma] using P.sum_slotted hcard j
    (fun l u => c j l u k*P.physicalPacket t j l u k z)

/-- The annular constant is chosen before every packet family and label
bound. Only nonzero coefficient coordinates need be separated. -/
theorem exists_physical_labeled_multiscale_energy
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card ≤ B) → ∀ (t w : ℝ), 0 < w →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j l u k ξ η, planarAngularFourier (P.physicalPacket t j l u k) (ξ,η) ≠ 0 →
        |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta) →
      (∀ j l u k, c j l u k ≠ 0 → cb*w/P.length j ≤ |P.rowSlope j l| ∧
        |P.rowSlope j l| ≤ Cb*w/P.length j) →
      (∫ z, ‖P.physicalLabeledSynthesis t c z‖^2 ∂volume.prod volume) ≤
        (B:ℝ)*C*P.profileBound^2*∑ j, ∑ l : P.labels j, ∑ u : Item j l,
          ‖c j l u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,henergy⟩ := exists_physical_lattice_multiscale_energy
    cStar cEta CEta cb Cb hcEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w hw c hspectrum hselector
  let F := fun s : Fin B => fun z => ∑ j, planarFixedSynthesis
    (fun u : P.SlotItem hcard s j => c j u.1.1 u.1.2)
    ((P.slotted hcard s).physicalPacket t j) z
  let mass := fun s : Fin B => ∑ j, ∑ u : P.SlotItem hcard s j,
    ‖c j u.1.1 u.1.2‖^2*P.length j*P.width
  have hF (s : Fin B) : MemLp (F s) 2 (volume.prod volume) :=
    (P.slotted hcard s).physicalMultiscaleSynthesis_memLp t _
  have hcost := weighted_integral_sum_square (volume.prod volume) F hF
    (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcost
  have heq (z : ℝ×ℝ) : (∑ s, F s z) = P.physicalLabeledSynthesis t c z :=
    P.physicalLabeledSynthesis_eq_slots hcard t c z
  simp only [heq] at hcost
  have hslot (s : Fin B) :
      (∫ z, ‖F s z‖^2 ∂volume.prod volume) ≤ C*P.profileBound^2*mass s := by
    apply henergy N κ (P.SlotItem hcard s) (P.slotted hcard s) t w hw
      (fun j u => c j u.1.1 u.1.2)
    · exact P.slotted_spectrum hcard t w cStar cEta CEta hspectrum s
    · intro j u k hc
      simpa only [P.slotted_length hcard,P.slotted_rowSlope hcard s j u] using
        hselector j u.1.1 u.1.2 k hc
  have hmass : (∑ s, mass s) =
      ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
    dsimp only [mass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact P.sum_slotted hcard j (fun l u => ‖c j l u‖^2*P.length j*P.width)
  calc
    _ ≤ (B:ℝ)*∑ s, ∫ z, ‖F s z‖^2 ∂volume.prod volume := hcost
    _ ≤ (B:ℝ)*∑ s, C*P.profileBound^2*mass s :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => hslot s) (Nat.cast_nonneg B)
    _ = _ := by rw [← Finset.mul_sum,hmass]; ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
