import Mathlib
import OAI.Analysis.CoulombRadii.RadialBounds.AtomicMasterError
import OAI.Analysis.CoulombRadii.FieldAnalysis.FreshTransferScale

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma master_relative_deficit {a w θ : ℝ} (ha : 0<a) (hθ : 0≤θ) (hw : 0≤w)
    (hwidth : w≤θ*a) :
    Coulomb.atomicNearConstant*a^(-21/5:ℝ)*(4*w)^(1/5:ℝ)≤
      Coulomb.atomicNearConstant*(4*θ)^(1/5:ℝ)*a^(-4:ℝ) := by
  calc
    _≤Coulomb.atomicNearConstant*a^(-21/5:ℝ)*((4*θ)*a)^(1/5:ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
      · positivity [Coulomb.atomicNearConstant_nonneg]
    _=_ := by
      rw [Real.mul_rpow (by positivity : 0≤4*θ) ha.le]
      calc
        _=Coulomb.atomicNearConstant*(4*θ)^(1/5:ℝ)*(a^(-21/5:ℝ)*a^(1/5:ℝ)) := by ring
        _=_ := by rw [←Real.rpow_add ha]; norm_num

theorem exists_atomic_master_fresh_relative_transfer : ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1 ∧
    ∀ {J N : ℕ} (S : Coulomb.Nuclei J) (hatom : ∀ i,S.position i=0)
    (u : Coulomb.H1Vector (N+1)), Coulomb.Antisymmetric u → Coulomb.mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom S → Coulomb.form S u≤E+δ → 0≤δ →
    ∀ (y : Position) (hy : y≠0), Coulomb.atomicCellScale y<s₀ → δ≤(Coulomb.atomicCellScale y)^(-349/50:ℝ) →
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*Coulomb.atomicCellScale y) (6*Coulomb.atomicCellScale y),
    ∃ T : Coulomb.AtomicBudgetHistory S u (Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm S≤Coulomb.form S u+Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(Coulomb.atomicCellScale y)^(6/5:ℝ))) ∧
      Coulomb.atomicPatchTFGap S hatom T.ensemble y hy ((Coulomb.atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2≤2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))≤
        (72*Coulomb.atomicPatchCountFactor*Coulomb.atomicCountConstant)*(Coulomb.atomicCellScale y)^(-29/5:ℝ) ∧
      ∀ (g : 𝓢(Position,ℝ)), (∫ w,g w^2)=1 →
      (∀ w,g w=g (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g w=0) →
      ∀ {c r₀ s θ : ℝ}, 0<c → 0<r₀ → 0<s → c*(1+packetExponent)*s^packetExponent≤1/2 →
      0≤θ → θ≤1 → packetWidth c r₀ s y≤θ*Coulomb.atomicCellScale y →
      |(Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y)-
        Coulomb.atomicPatchMeanField S hatom T.ensemble y hy ((Coulomb.atomicCellScale y)^(6/5:ℝ))
          (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2|≤
        (Coulomb.atomicTransferConstant*(Coulomb.atomicCellScale y)^(1/500:ℝ)+
          Coulomb.atomicNearConstant*(4*θ)^(1/5:ℝ))*(Coulomb.atomicCellScale y)^(-4:ℝ) := by
  obtain ⟨s₀,hs₀,hs₀1,Hfresh⟩ := Coulomb.exists_atomic_fresh_field_transfer
  obtain ⟨s₁,hs₁,hs₁1,Hmaster⟩ := exists_atomic_master_error_scale
  refine ⟨min s₀ s₁,lt_min hs₀ hs₁,(min_le_left _ _).trans hs₀1,?_⟩
  intro J N S hatom u hu hm E δ hE he hδ y hy hys hd
  have ha := Coulomb.atomicCellScale_pos hy
  have hay₀ := hys.trans_le (min_le_left _ _)
  have hay₁ := hys.trans_le (min_le_right _ _)
  obtain ⟨t,ht,T,hT,ho,hcs,hos,hG,hD,hF⟩ := Hfresh S hatom u hu hm hE he hδ y hy hay₀ hd
  refine ⟨t,ht,T,hT,ho,hcs,hos,hG,hD,?_⟩
  intro g hgm hrad hgs c r₀ s θ hc hr hs hq hθ hθ1 hw
  have ha1 : Coulomb.atomicCellScale y≤1 := hay₀.le.trans hs₀1
  have hwa : packetWidth c r₀ s y≤Coulomb.atomicCellScale y := hw.trans (by nlinarith)
  have HM := Hmaster S hatom u hu hm hE he hδ y hy hay₁ hd g hgm hrad hgs hc hr hs hq hwa
  have HB := HM.2.trans (master_relative_deficit ha hθ (packetWidth_pos hc hr hs y).le hw)
  have HT := abs_sub_le (Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y)
    (Coulomb.coreScreenedField S u y) (Coulomb.atomicPatchMeanField S hatom T.ensemble y hy
      ((Coulomb.atomicCellScale y)^(6/5:ℝ)) (Real.rpow_pos_of_pos ha _) t ht.2)
  have hEq : (Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y)-
      Coulomb.coreScreenedField S u y=Coulomb.coreCoulombPotential u y-
        potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y := by unfold Coulomb.coreScreenedField; ring
  rw [hEq,abs_of_nonneg HM.1] at HT
  have hp : (Coulomb.atomicCellScale y)^(-1999/500:ℝ)=
      (Coulomb.atomicCellScale y)^(1/500:ℝ)*(Coulomb.atomicCellScale y)^(-4:ℝ) := by
    rw [←Real.rpow_add ha]
    norm_num
  rw [hp] at hF
  nlinarith
end NeutralAtom
end

end
end

end OAI
