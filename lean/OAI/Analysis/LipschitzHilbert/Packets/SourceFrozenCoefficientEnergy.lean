import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMultiscaleEnergy
import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingCoefficients
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledCoefficientSplit
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! Bessel duality for the original physical packets with fixed selector
values. Both the synthesis and analyzing energies use the actual packet
area. The constant is independent of vector dimension and scale count. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert

/-- Finite weighted Bessel duality, applied to the exact analyzing
integrals rather than an assumed coefficient estimate. -/
theorem analyzingCoefficient_l2_energy_le
    {X I K : Type*} [MeasurableSpace X] [Fintype I] [Fintype K]
    (μ : Measure X) (area : I → ℝ) (wave : I → K → X → ℂ)
    (g : X → EuclideanSpace ℂ K) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ i, 0 < area i)
    (hg : MemLp g 2 μ)
    (hint : ∀ i k, Integrable (fun x => g x k * conj (wave i k x)) μ)
    (hsyn : ∀ c, MemLp (diagonalSynthesis wave c) 2 μ)
    (hbound : ∀ c, (∫ x, ‖diagonalSynthesis wave c x‖^2 ∂μ) ≤
      A * ∑ i, area i * ‖c i‖^2) :
    (∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2) ≤
      A * ∫ x, ‖g x‖^2 ∂μ := by
  let a := analyzingCoefficient μ area wave g
  let S := ∑ i, area i * ‖a i‖^2
  let F := diagonalSynthesis wave a
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (ha i).le (sq_nonneg _)
  have hF : MemLp F 2 μ := hsyn a
  have hp : (S : ℂ) = ∫ x, inner ℂ (F x) (g x) ∂μ :=
    analyzingCoefficient_self_pairing μ area wave g (fun i => (ha i).ne') hint
  have hprod : Integrable (fun x => ‖F x‖*‖g x‖) μ := hF.norm.integrable_mul hg.norm
  have hcs : S ≤ Real.sqrt (∫ x, ‖F x‖^2 ∂μ) * Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
    calc
      S = ‖∫ x, inner ℂ (F x) (g x) ∂μ‖ := by
        rw [← hp,Complex.norm_real,Real.norm_of_nonneg hS]
      _ ≤ ∫ x, ‖inner ℂ (F x) (g x)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖F x‖*‖g x‖ ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hprod
          (Filter.Eventually.of_forall fun x => norm_inner_le_norm (F x) (g x))
      _ ≤ _ := by
        simpa only [Real.rpow_two,← Real.sqrt_eq_rpow] using
          integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
            (by simpa using hF) (by simpa using hg)
  have hF0 : 0 ≤ ∫ x, ‖F x‖^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hg0 : 0 ≤ ∫ x, ‖g x‖^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hsquare := pow_le_pow_left₀ hS hcs 2
  rw [mul_pow,Real.sq_sqrt hF0,Real.sq_sqrt hg0] at hsquare
  have henergy : (∫ x, ‖F x‖^2 ∂μ) ≤ A*S := hbound a
  have hmul := mul_le_mul_of_nonneg_right henergy hg0
  change S ≤ A * ∫ x, ‖g x‖^2 ∂μ
  by_cases hzero : S = 0
  · simpa only [hzero] using mul_nonneg hA hg0
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    apply le_of_mul_le_mul_left (a := S) _ hSpos
    nlinarith [hsquare,hmul]


namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

def physicalFrozenCoefficient (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (beta : P.PacketIndex → κ → ℂ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun p : P.PacketIndex => P.length p.1*P.width)
    (fun p k z => beta p k * P.physicalPacket t p.1 p.2.1 p.2.2 k z) g q

theorem physicalFrozenCoefficient_apply_eq_zero (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (beta : P.PacketIndex → κ → ℂ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (q : P.PacketIndex) (k : κ) (hbeta : beta q k = 0) :
    P.physicalFrozenCoefficient t beta g q k = 0 := by
  simp [physicalFrozenCoefficient,analyzingCoefficient,hbeta]

theorem physicalFrozenCoefficient_eq_multiplier (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (l : P.labels j) (u : Item j l) :
    P.physicalFrozenCoefficient t (fun q k => b q.1 q.2.1 k t) g ⟨j,⟨l,u⟩⟩ =
      P.physicalMultiplierCoefficient t b (fun _ => t) g j l u := rfl

/-- Frozen selector values have a dimension-free Bessel bound on every
finite selected packet family. Empty and zero-coefficient fibers need no
selector separation. -/
theorem exists_physical_frozen_coefficient_energy
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card ≤ B) → ∀ (t w : ℝ), 0 < w →
    ∀ (beta : P.PacketIndex → κ → ℂ) (packets : Finset P.PacketIndex)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ q ∈ packets, ∀ k, ‖beta q k‖ ≤ 1) → MemLp g 2 (volume.prod volume) →
      (∀ j l u k ξ η, planarAngularFourier (P.physicalPacket t j l u k) (ξ,η) ≠ 0 →
        |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta) →
      (∀ q ∈ packets, ∀ k, beta q k ≠ 0 →
        cb*w/P.length q.1 ≤ |P.rowSlope q.1 q.2.1| ∧
          |P.rowSlope q.1 q.2.1| ≤ Cb*w/P.length q.1) →
      (∑ q ∈ packets, P.length q.1*P.width*‖P.physicalFrozenCoefficient t beta g q‖^2) ≤
        ((B:ℝ)*C*P.profileBound^2) * ∫ z, ‖g z‖^2 ∂volume.prod volume := by
  obtain ⟨C,hC,henergy⟩ := exists_physical_labeled_multiscale_energy
    cStar cEta CEta cb Cb hcEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w hw beta packets g hbeta hg hspectrum hselector
  let m := fun q : P.PacketIndex => fun k => if q ∈ packets then beta q k else 0
  let wave := fun q : P.PacketIndex => fun k z => m q k * P.physicalPacket t q.1 q.2.1 q.2.2 k z
  let area := fun q : P.PacketIndex => P.length q.1*P.width
  let d := fun c : P.PacketIndex → EuclideanSpace ℂ κ =>
    fun j (l : P.labels j) (u : Item j l) =>
      WithLp.toLp 2 (fun k => c ⟨j,⟨l,u⟩⟩ k * m ⟨j,⟨l,u⟩⟩ k)
  have hm (q : P.PacketIndex) (k : κ) : ‖m q k‖ ≤ 1 := by
    by_cases hq : q ∈ packets
    · simpa only [m,hq,ite_true] using hbeta q hq k
    · simp only [m,hq,ite_false,norm_zero,zero_le_one]
  have hdiag (c : P.PacketIndex → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
      diagonalSynthesis wave c z = P.physicalLabeledSynthesis t (d c) z := by
    ext k
    simp only [diagonalSynthesis,physicalLabeledSynthesis,planarFixedSynthesis,wave,d,
      WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp,Fintype.sum_sigma,mul_assoc]
  have hsyn (c : P.PacketIndex → EuclideanSpace ℂ κ) :
      MemLp (diagonalSynthesis wave c) 2 (volume.prod volume) := by
    have heq : diagonalSynthesis wave c = P.physicalLabeledSynthesis t (d c) := funext (hdiag c)
    rw [heq]
    exact P.physicalLabeledSynthesis_memLp t (d c)
  have hsynth (c : P.PacketIndex → EuclideanSpace ℂ κ) :
      (∫ z, ‖diagonalSynthesis wave c z‖^2 ∂volume.prod volume) ≤
        ((B:ℝ)*C*P.profileBound^2) * ∑ q, area q*‖c q‖^2 := by
    have hs (j) (l : P.labels j) (u : Item j l) (k : κ) (hc : d c j l u k ≠ 0) :
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j := by
      have hq : (⟨j,⟨l,u⟩⟩ : P.PacketIndex) ∈ packets := by
        by_contra hn
        exact hc (by simp only [d,m,hn,ite_false,mul_zero])
      apply hselector _ hq k
      intro hb
      exact hc (by simp only [d,m,hq,ite_true,hb,mul_zero])
    have h := henergy N κ Label Item P B hcard t w hw (d c) hspectrum hs
    simp_rw [← hdiag] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hn (j) (l : P.labels j) (u : Item j l) : ‖d c j l u‖ ≤ ‖c ⟨j,⟨l,u⟩⟩‖ := by
      simpa only [d,one_mul] using diagonal_packet_norm (c ⟨j,⟨l,u⟩⟩) (m ⟨j,⟨l,u⟩⟩)
        (show (0:ℝ) ≤ 1 by norm_num) (hm ⟨j,⟨l,u⟩⟩)
    simp only [Fintype.sum_sigma,area]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum
    intro u _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hn j l u) 2
    convert mul_le_mul_of_nonneg_right hsq
      (mul_nonneg (P.length_pos j).le P.width_pos.le) using 1 <;> ring
  have hint (q : P.PacketIndex) (k : κ) :
      Integrable (fun z => g z k * conj (wave q k z)) (volume.prod volume) := by
    have hgk : MemLp (fun z => g z k) 2 (volume.prod volume) := (memLp_piLp_iff.mp hg) k
    have hwave : MemLp (wave q k) 2 (volume.prod volume) :=
      (P.physicalPacket t q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume) |>.const_mul (m q k)
    apply (hgk.integrable_mul hwave.star).congr
    filter_upwards [] with z
    rfl
  have h := analyzingCoefficient_l2_energy_le (volume.prod volume) area wave g
    ((B:ℝ)*C*P.profileBound^2) (by positivity)
    (fun q => mul_pos (P.length_pos q.1) P.width_pos) hg hint hsyn hsynth
  have ha (q : P.PacketIndex) : analyzingCoefficient (volume.prod volume) area wave g q =
      if q ∈ packets then P.physicalFrozenCoefficient t beta g q else 0 := by
    ext k
    by_cases hq : q ∈ packets <;>
      simp [analyzingCoefficient,physicalFrozenCoefficient,wave,m,area,hq]
  simp_rw [ha] at h
  have hsum : (∑ q : P.PacketIndex, area q *
      ‖if q ∈ packets then P.physicalFrozenCoefficient t beta g q else 0‖^2) =
      ∑ q ∈ packets, P.length q.1*P.width*‖P.physicalFrozenCoefficient t beta g q‖^2 := by
    calc
      _ = ∑ q : P.PacketIndex, if q ∈ packets then
          P.length q.1*P.width*‖P.physicalFrozenCoefficient t beta g q‖^2 else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hq : q ∈ packets <;> simp [hq,area]
      _ = _ := Finset.sum_ite_mem_eq _ _
  rwa [hsum] at h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
