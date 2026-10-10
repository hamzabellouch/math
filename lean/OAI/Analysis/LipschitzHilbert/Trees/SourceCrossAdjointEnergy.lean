import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledAdjointPolarization
import OAI.Analysis.LipschitzHilbert.Trees.SourceOrdinaryAdjointEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceOriginalIntegrability

namespace OAI

/-! Cross-profile adjoint energy from four genuine ordinary packet families. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem four_polarization_norm_sq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (v a b c d : V) (h : (4:ℂ) • v=a-b-Complex.I • c+Complex.I • d) :
    ‖v‖^2≤‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2 := by
  have hn : 4*‖v‖≤‖a‖+‖b‖+‖c‖+‖d‖ := by
    calc
      _ = ‖(4:ℂ) • v‖ := by rw [norm_smul]; norm_num
      _ = ‖a-b-Complex.I • c+Complex.I • d‖ := congrArg norm h
      _ ≤ ‖a-b-Complex.I • c‖+‖Complex.I • d‖ := norm_add_le _ _
      _ ≤ (‖a-b‖+‖Complex.I • c‖)+‖Complex.I • d‖ :=
        add_le_add (norm_sub_le (a-b) (Complex.I • c)) le_rfl
      _ ≤ ((‖a‖+‖b‖)+‖Complex.I • c‖)+‖Complex.I • d‖ :=
        add_le_add (add_le_add (norm_sub_le a b) le_rfl) le_rfl
      _ = _ := by simp only [norm_smul,Complex.norm_I,one_mul]
  have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤4) (norm_nonneg v)) hn 2
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖c‖-‖d‖),sq_nonneg (‖a‖+‖b‖-‖c‖-‖d‖)]

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem exists_cross_adjoint_energy (hL : LepingleInput)
    (P : SourceLabeledLattice N κ Label Item) (initial : Finset P.PacketIndex)
    (d : OrdinaryModelConfig P initial)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width) :
    ∃ C : ℝ, 0<C ∧ ∀ S : Finset P.PacketIndex, S⊆initial →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ E : Set (ℝ×ℝ), MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉E → g z=0) → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∫ z, ‖∑ q∈S, P.physicalCrossPacketValue alt hAlt 0 d.selector u g 0 z q‖^2
        ∂volume.prod volume)≤C*(volume.prod volume).real E := by
  let Q := fun (c : ℂ) (hc : ‖c‖=1) => P.polarize alt hAlt c hc
  have hFor (c : ℂ) (hc : ‖c‖=1) := exists_ordinary_adjoint_energy hL (Q c hc) initial
    (d.polarize alt hAlt c hc hSpectrum hMargin hBin)
  obtain ⟨C₁,hC₁,h₁⟩ := hFor 1 (by simp)
  obtain ⟨C₂,hC₂,h₂⟩ := hFor (-1) (by simp)
  obtain ⟨C₃,hC₃,h₃⟩ := hFor Complex.I (by simp)
  obtain ⟨C₄,hC₄,h₄⟩ := hFor (-Complex.I) (by simp)
  refine ⟨C₁+C₂+C₃+C₄,by positivity,?_⟩
  intro S hS g hg hg1 E hE hEfin hgs u hu
  let A := (Q 1 (by simp)).ordinaryAdjointSum S d.selector u g
  let B := (Q (-1) (by simp)).ordinaryAdjointSum S d.selector u g
  let C := (Q Complex.I (by simp)).ordinaryAdjointSum S d.selector u g
  let D := (Q (-Complex.I) (by simp)).ordinaryAdjointSum S d.selector u g
  let X := fun z => ∑ q∈S, P.physicalCrossPacketValue alt hAlt 0 d.selector u g 0 z q
  have hA := ((Q 1 (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hB := ((Q (-1) (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hC := ((Q Complex.I (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hD := ((Q (-Complex.I) (by simp)).ordinaryAdjointSum_memLp S d.selector u g).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hX := (P.physicalCrossSum_memLp alt hAlt 0 d.selector u g 2 S).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hp (z : ℝ×ℝ) : ‖X z‖^2≤‖A z‖^2+‖B z‖^2+‖C z‖^2+‖D z‖^2 :=
    four_polarization_norm_sq _ _ _ _ _ (P.cross_adjoint_polarization alt hAlt S d.selector
      d.measurable d.bounded u hu g hg hg1 z)
  calc
    _ ≤ ∫ z, ‖A z‖^2+‖B z‖^2+‖C z‖^2+‖D z‖^2 ∂volume.prod volume :=
      integral_mono hX (((hA.add hB).add hC).add hD) hp
    _ = (∫ z, ‖A z‖^2 ∂volume.prod volume)+(∫ z, ‖B z‖^2 ∂volume.prod volume)+
        (∫ z, ‖C z‖^2 ∂volume.prod volume)+(∫ z, ‖D z‖^2 ∂volume.prod volume) := by
      have hab : (∫ z, ‖A z‖^2+‖B z‖^2 ∂volume.prod volume)=
          (∫ z, ‖A z‖^2 ∂volume.prod volume)+(∫ z, ‖B z‖^2 ∂volume.prod volume) := integral_add hA hB
      have habc : (∫ z, ‖A z‖^2+‖B z‖^2+‖C z‖^2 ∂volume.prod volume)=
          (∫ z, ‖A z‖^2+‖B z‖^2 ∂volume.prod volume)+(∫ z, ‖C z‖^2 ∂volume.prod volume) :=
        integral_add (hA.add hB) hC
      calc
        _ = (∫ z, ‖A z‖^2+‖B z‖^2+‖C z‖^2 ∂volume.prod volume)+
            (∫ z, ‖D z‖^2 ∂volume.prod volume) := integral_add ((hA.add hB).add hC) hD
        _ = _ := by rw [habc,hab]
    _ ≤ C₁*(volume.prod volume).real E+C₂*(volume.prod volume).real E+
        C₃*(volume.prod volume).real E+C₄*(volume.prod volume).real E :=
      add_le_add (add_le_add (add_le_add (h₁ S hS g hg hg1 E hE hEfin hgs u hu)
        (h₂ S hS g hg hg1 E hE hEfin hgs u hu))
        (h₃ S hS g hg hg1 E hE hEfin hgs u hu)) (h₄ S hS g hg hg1 E hE hEfin hgs u hu)
    _ = _ := by ring

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
