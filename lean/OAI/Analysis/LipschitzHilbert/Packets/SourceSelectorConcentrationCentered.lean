import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationJets
import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenCenteredCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalTail

namespace OAI

/-! Exact centered coefficients for all covariant synthesis jets. The
original frozen analyzing coefficient is split into its two monotone
cutoffs and constant term, with no boundary-nullity premise. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (t : ℝ)

def physicalJetBand (i : Fin 3) (j : Fin N) (y x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (conj (c j u k)*P.physicalCoefficient t d v g j u k)*
      (P.withProfile alt hAlt).raw i j u k y x)

def physicalJetVariation (i : Fin 3) (y x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum
    (fun j => P.physicalJetBand c alt hAlt d v g t i j y x)) N

def physicalCenteredJetBand (i : Fin 3) (j : Fin N) (y x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (conj (c j u k)*P.physicalCenteredCoefficient t t d v g j u k)*
      (P.withProfile alt hAlt).raw i j u k y x)

def physicalCenteredJetVariation (i : Fin 3) (y x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum
    (fun j => P.physicalCenteredJetBand c alt hAlt d v g t i j y x)) N

theorem physicalJetBand_continuous (i : Fin 3) (j : Fin N) (y : ℝ) :
    Continuous (P.physicalJetBand c alt hAlt d v g t i j y) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro u _
  exact continuous_const.mul ((P.withProfile alt hAlt).raw i j u k y).continuous

theorem physicalJetVariation_continuous (i : Fin 3) (y : ℝ) :
    Continuous (P.physicalJetVariation c alt hAlt d v g t i y) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using P.physicalJetBand_continuous c alt hAlt d v g t i j y
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem physicalCenteredJetBand_continuous (i : Fin 3) (j : Fin N) (y : ℝ) :
    Continuous (P.physicalCenteredJetBand c alt hAlt d v g t i j y) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro u _
  exact continuous_const.mul ((P.withProfile alt hAlt).raw i j u k y).continuous

theorem physicalCenteredJetVariation_continuous (i : Fin 3) (y : ℝ) :
    Continuous (P.physicalCenteredJetVariation c alt hAlt d v g t i y) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using
      P.physicalCenteredJetBand_continuous c alt hAlt d v g t i j y
  · simp only [ite_eq_right hj]
    exact continuous_const

variable (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

theorem physicalJetBand_eq_reference (i : Fin 3) (j : Fin N) (y x : ℝ) :
    P.physicalJetBand c alt hAlt d v g t i j y x =
      P.mixedReferenceJetBand c hc alt hAlt d
        (fun z => v (sourceReferenceToPhysical t z))
        (fun z => g (sourceReferenceToPhysical t z)) i j y x := by
  ext k
  simp only [physicalJetBand,mixedReferenceJetBand,WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro u _
  rw [(P.frozenProfile c hc).family_mainCoefficient_physical,
    P.frozenProfile_physicalCoefficient]

theorem physicalJetVariation_normalization
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (y x : ℝ) :
    P.physicalJetVariation c alt hAlt d v g t i y (P.topLength*x) =
      (P.constant*Real.pi^2)*
        (P.mixedReferenceJetLine c hc alt hAlt d
          (fun z => v (sourceReferenceToPhysical t z))
          (hv.comp (sourceReferenceToPhysical t).measurable)
          (fun z => g (sourceReferenceToPhysical t z))
          (hg.comp (sourceReferenceToPhysical t).measurable)
          (fun z => hg1 (sourceReferenceToPhysical t z)) i y).variation x := by
  unfold physicalJetVariation
  simp_rw [P.physicalJetBand_eq_reference c alt hAlt d v g t hc]
  exact P.mixedReferenceJetBand_variation c hc alt hAlt d _
    (hv.comp (sourceReferenceToPhysical t).measurable) _
    (hg.comp (sourceReferenceToPhysical t).measurable)
    (fun z => hg1 (sourceReferenceToPhysical t z)) i y x

theorem physicalCenteredJetBand_eq (hd : ∀ j, 0 ≤ d j)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (j : Fin N) (y x : ℝ) :
    P.physicalCenteredJetBand c alt hAlt d v g t i j y x =
      P.physicalJetBand c alt hAlt (fun j => t+d j) v g t i j y x+
      P.physicalJetBand c alt hAlt (fun j => d j-t) (fun z => -v z) g t i j y x-
      P.physicalJetBand c alt hAlt (fun _ => 0) (fun _ => 0) g t i j y x := by
  ext k
  simp only [physicalCenteredJetBand,physicalJetBand,WithLp.ofLp_toLp,
    PiLp.add_apply,PiLp.sub_apply]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [P.physicalCenteredCoefficient_eq t t d hd v hv g hg hg1]
  simp only [PiLp.add_apply,PiLp.sub_apply]
  ring

private theorem jetPartial_add_sub {E : Type*} [AddCommGroup E]
    (F G H : Fin N → E) (n : ℕ) :
    packetPartialSum (fun j => F j+G j-H j) n =
      packetPartialSum F n+packetPartialSum G n-packetPartialSum H n := by
  unfold packetPartialSum
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem physicalCenteredJetPartial_eq (hd : ∀ j, 0 ≤ d j)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (y x : ℝ) (n : ℕ) :
    packetPartialSum (fun j => P.physicalCenteredJetBand c alt hAlt d v g t i j y x) n =
      packetPartialSum (fun j => P.physicalJetBand c alt hAlt (fun j => t+d j) v g t i j y x) n+
      packetPartialSum (fun j => P.physicalJetBand c alt hAlt (fun j => d j-t)
        (fun z => -v z) g t i j y x) n-
      packetPartialSum (fun j => P.physicalJetBand c alt hAlt (fun _ => 0)
        (fun _ => 0) g t i j y x) n := by
  have hband : (fun j => P.physicalCenteredJetBand c alt hAlt d v g t i j y x) =
      fun j => P.physicalJetBand c alt hAlt (fun j => t+d j) v g t i j y x+
        P.physicalJetBand c alt hAlt (fun j => d j-t) (fun z => -v z) g t i j y x-
        P.physicalJetBand c alt hAlt (fun _ => 0) (fun _ => 0) g t i j y x := by
    funext j
    exact P.physicalCenteredJetBand_eq c alt hAlt d v g t hd hv hg hg1 i j y x
  rw [hband]
  exact jetPartial_add_sub _ _ _ n

theorem physicalCenteredJetVariation_le (hd : ∀ j, 0 ≤ d j)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (y x : ℝ) :
    P.physicalCenteredJetVariation c alt hAlt d v g t i y x ≤
      P.physicalJetVariation c alt hAlt (fun j => t+d j) v g t i y x+
      P.physicalJetVariation c alt hAlt (fun j => d j-t) (fun z => -v z) g t i y x+
      P.physicalJetVariation c alt hAlt (fun _ => 0) (fun _ => 0) g t i y x := by
  have heq := funext (P.physicalCenteredJetPartial_eq c alt hAlt d v g t hd hv hg hg1 i y x)
  unfold physicalCenteredJetVariation
  rw [heq]
  have heq' : (fun n => packetPartialSum
      (fun j => P.physicalJetBand c alt hAlt (fun j => t+d j) v g t i j y x) n+
      packetPartialSum (fun j => P.physicalJetBand c alt hAlt (fun j => d j-t)
        (fun z => -v z) g t i j y x) n-
      packetPartialSum (fun j => P.physicalJetBand c alt hAlt (fun _ => 0)
        (fun _ => 0) g t i j y x) n) =
    fun n => (packetPartialSum
      (fun j => P.physicalJetBand c alt hAlt (fun j => t+d j) v g t i j y x) n+
      packetPartialSum (fun j => P.physicalJetBand c alt hAlt (fun j => d j-t)
        (fun z => -v z) g t i j y x) n)+
      -(packetPartialSum (fun j => P.physicalJetBand c alt hAlt (fun _ => 0)
        (fun _ => 0) g t i j y x) n) := by
    funext n
    exact sub_eq_add_neg _ _
  rw [heq']
  apply (cubicVariation_add_le _ _ N).trans
  rw [cubicVariation_neg]
  exact add_le_add (cubicVariation_add_le _ _ N) le_rfl

end LipschitzHilbert.SourceLatticePacket

end

end OAI
