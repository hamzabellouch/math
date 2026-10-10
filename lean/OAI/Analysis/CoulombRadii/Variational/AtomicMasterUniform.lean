import Mathlib
import OAI.Analysis.CoulombRadii.Screening.AtomicMasterRelative

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma exists_atomic_master_uniform_error {c A ε : ℝ} (hc : 0<c) (hA : 0<A)
    (hε : 0<ε) : ∃ s₀ : ℝ, 0<s₀ ∧ ∀ {s : ℝ}, 0<s → s<s₀ →
      c*(1+packetExponent)*s^packetExponent≤1/2 ∧
      100000*c*s^packetExponent≤1 ∧
      ∀ {a : ℝ}, 0<a → a≤A*s →
      Coulomb.atomicTransferConstant*a^(1/500:ℝ)+
        Coulomb.atomicNearConstant*(4*(100000*c*s^packetExponent))^(1/5:ℝ)≤ε := by
  have hw : 0<packetExponent := by norm_num [packetExponent]
  have ht := (tendsto_positive_rpow_zero hw).const_mul (c*(1+packetExponent))
  have hu := (tendsto_positive_rpow_zero hw).const_mul (100000*c)
  have he := ((tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/500)).const_mul
    (Coulomb.atomicTransferConstant*A^(1/500:ℝ))).add
    ((tendsto_positive_rpow_zero (div_pos hw (by norm_num : (0:ℝ)<5))).const_mul
      (Coulomb.atomicNearConstant*(400000*c)^(1/5:ℝ)))
  simp only [mul_zero,add_zero] at ht hu he
  have HH : ∀ᶠ s : ℝ in 𝓝[>] 0,
      c*(1+packetExponent)*s^packetExponent<1/2 ∧
      100000*c*s^packetExponent<1 ∧
      Coulomb.atomicTransferConstant*A^(1/500:ℝ)*s^(1/500:ℝ)+
        Coulomb.atomicNearConstant*(400000*c)^(1/5:ℝ)*s^(packetExponent/5)<ε := by
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      hu.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),he.eventually (gt_mem_nhds hε)] with s hs₁ hs₂ hs₃
    exact ⟨hs₁,hs₂,hs₃⟩
  obtain ⟨s₀,hs₀,Hs₀⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp HH
  refine ⟨s₀,hs₀,?_⟩
  intro s hs hss
  obtain ⟨hq,hθ,herr⟩ := Hs₀ ⟨hs,hss⟩
  refine ⟨hq.le,hθ.le,?_⟩
  intro a ha hsa
  have hca : 0≤Coulomb.atomicTransferConstant := Coulomb.atomicTransferConstant_nonneg
  have hfirst := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow ha.le hsa (by norm_num : (0:ℝ)≤1/500)) hca
  have hpow : (4*(100000*c*s^packetExponent))^(1/5:ℝ)=
      (400000*c)^(1/5:ℝ)*s^(packetExponent/5) := by
    rw [show 4*(100000*c*s^packetExponent)=(400000*c)*s^packetExponent by ring,
      Real.mul_rpow (by positivity : 0≤400000*c) (Real.rpow_nonneg hs.le _),
      ←Real.rpow_mul hs.le]
    congr 2
    ring
  rw [Real.mul_rpow hA.le hs.le] at hfirst
  rw [hpow]
  nlinarith

theorem exists_atomic_master_fresh_uniform_transfer {c A ε : ℝ}
    (hc : 0<c) (hA : 0<A) (hε : 0<ε) :
    ∃ s₀ : ℝ, 0<s₀ ∧ ∀ {J N : ℕ} (S : Coulomb.Nuclei J)
    (hatom : ∀ i,S.position i=0) (u : Coulomb.H1Vector (N+1)),
    Coulomb.Antisymmetric u → Coulomb.mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom S → Coulomb.form S u≤E+δ → 0≤δ →
    ∀ {r₀ s : ℝ}, 0<r₀ → 0<s → s<s₀ →
    ∀ (y : Position) (hy : y≠0), r₀≤‖y‖ → Coulomb.atomicCellScale y≤A*s →
    δ≤(Coulomb.atomicCellScale y)^(-349/50:ℝ) →
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
      |(Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y)-
        Coulomb.atomicPatchMeanField S hatom T.ensemble y hy ((Coulomb.atomicCellScale y)^(6/5:ℝ))
          (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2|≤
        ε*(Coulomb.atomicCellScale y)^(-4:ℝ) := by
  obtain ⟨s₁,hs₁,_,H⟩ := exists_atomic_master_fresh_relative_transfer
  obtain ⟨s₂,hs₂,Herr⟩ := exists_atomic_master_uniform_error hc hA hε
  refine ⟨min s₂ (s₁/A),lt_min hs₂ (div_pos hs₁ hA),?_⟩
  intro J N S hatom u hu hm E δ hE he hδ r₀ s hr hs hss y hy hry hya hd
  have has : Coulomb.atomicCellScale y<s₁ := hya.trans_lt (by
    have h := (lt_div_iff₀ hA).mp (hss.trans_le (min_le_right _ _))
    simpa only [mul_comm] using h)
  obtain ⟨hq,hθ,herr⟩ := Herr hs (hss.trans_le (min_le_left _ _))
  obtain ⟨t,ht,T,hTf,ho,hcs,hos,hG,hD,hF⟩ := H S hatom u hu hm hE he hδ y hy has hd
  refine ⟨t,ht,T,hTf,ho,hcs,hos,hG,hD,?_⟩
  intro g hgm hrad hgs
  have hwidth : packetWidth c r₀ s y≤(100000*c*s^packetExponent)*Coulomb.atomicCellScale y := by
    have hw := packetWidth_le c r₀ s hc.le hr hs y
    rw [max_eq_left hry,←Coulomb.atomicCellScale_norm y] at hw
    nlinarith
  have HF := hF g hgm hrad hgs hc hr hs hq (by positivity) hθ hwidth
  exact HF.trans (mul_le_mul_of_nonneg_right (herr (Coulomb.atomicCellScale_pos hy) hya)
    (Real.rpow_nonneg (Coulomb.atomicCellScale_nonneg y) _))
end NeutralAtom
end

end
end

end OAI
