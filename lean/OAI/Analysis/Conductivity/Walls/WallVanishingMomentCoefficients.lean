import Mathlib
import OAI.Analysis.Conductivity.Sources.CriticalWallGap
import OAI.Analysis.Conductivity.Variational.VanishingMomentChoice
import OAI.Analysis.Conductivity.Walls.WallTransferParametric

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma wall_vanishing_moment_coefficients
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {l t a b σ lam : ℝ} (hlt : l<t) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    (hlim : ∀ z : ℝ×ℝ,v (p,(z,0))=σ*Real.exp (-lam*z.1))
    {V : Set P} (hV : IsOpen V) (hp : p∈V)
    {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    (hrz : ∀ j x,r j (p,x)=0) (δ : ℝ) :
    ∃ θ η : ℝ → ℝ, ContDiff ℝ (↑(⊤:ℕ∞)) θ ∧ ContDiff ℝ (↑(⊤:ℕ∞)) η ∧
      HasCompactSupport θ ∧ HasCompactSupport η ∧ tsupport θ⊆Icc l t ∧ tsupport η⊆Ioo a b ∧
      ∃ c : P → Coord3,Tendsto c (𝓝 p) (𝓝 0) ∧ ∀ᶠ q in 𝓝 p,∀ i,
        (∫ z,wallMomentAmplitude θ η σ lam (c q) z*wallActualMoment (fun y => v (q,y)) z i)=
        -physicalSourceMoment (wallCoordinatePair (fun y => v (q,y)))
          (fun j => wallPositiveCut δ (fun x => r j (q,x))) i := by
  have hvq (q : P) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨θ,η,hθ,hη,hθc,hηc,hθs,hηs,C,hC,hinv⟩ :=
    actual_wall_moment_uniform_inverse (v:=fun q y => v (q,y)) (p₀:=p) hlt hab hσ hlam
      (hvq p) hv.continuous (wallAlong_parametric_smooth (1,0) hv).continuous hlim
  let u : P×Coord3 → Fin 2 → ℝ := fun q => wallCoordinatePair (fun y => v (q.1,y)) q.2
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) u := wallCoordinatePair_parametric_smooth hv
  let rp : Fin 2 → P×Coord3 → ℝ := fun j q => wallPositiveCut δ (fun x => r j (q.1,x)) q.2
  have hrp (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (rp j) (V×ˢuniv) :=
    ((Real.smoothTransition.contDiff.comp
      (((contDiff_apply ℝ ℝ (2:Fin 3)).comp contDiff_snd).div_const δ)).contDiffOn).mul (hr j)
  let m : P → Coord3 := fun q => physicalSourceMoment (fun x => u (q,x)) (fun j x => rp j (q,x))
  have hm : Tendsto m (𝓝 p) (𝓝 0) := physicalSourceMoment_family_tendsto_zero hu.continuous hV hp
    hrp hK (hs.mono (fun q hq => hq.wallPositiveCut δ))
    (fun j x => by simp [rp,wallPositiveCut,hrz])
  have hchoose : ∀ᶠ q in 𝓝 p,∃ c : Coord3,‖c‖≤C*‖m q‖ ∧
      (∀ i,(∫ z,wallMomentAmplitude θ η σ lam c z*wallActualMoment (fun y => v (q,y)) z i)= -m q i) := by
    filter_upwards [hinv] with q hq
    obtain ⟨c,hcb,_,_,_,hcm⟩ := hq (-m q)
    refine ⟨c,?_,hcm⟩
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le (norm_nonneg _))).mpr
    intro i
    simpa only [norm_neg] using hcb i
  obtain ⟨c,hc,hcm⟩ := exists_vanishing_moment_selection hm hchoose
  exact ⟨θ,η,hθ,hη,hθc,hηc,hθs,hηs,c,hc,hcm⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

lemma wall_transfer_finishes
    {χ v : Box3 → ℝ} {a : ℝ×ℝ → ℝ} {U : Set Coord3}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a)
    (hz : ∀ z,wallDerivative v (z,0)=0)
    (hne : ∀ z∈tsupport χ,wallQuotient (wallDerivative v) z≠0)
    (hcut : ∀ z,χ (z,0)*a z=a z)
    {δ : ℝ} (hδ : 0<δ)
    (hgap : ∀ j x,x∈tsupport (symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) j) → δ≤|x 2|)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r)
    (hm : physicalSourceMoment (wallCoordinatePair v) r=0)
    (hp : ∀ i,(∫ z,a z*wallActualMoment v z i)=
      -physicalSourceMoment (wallCoordinatePair v) (fun j => wallPositiveCut δ (r j)) i)
    {ε : ℝ} (hsmall : ∀ x,‖wallHomogeneousTensor χ v a x‖≤ε/2)
    (hsolve : physicalSourceMoment (wallCoordinatePair v)
        (r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v))=0 →
      physicalSourceMoment (wallCoordinatePair v)
        (fun j => wallPositiveCut δ ((r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v)) j))=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair v) U
        (r-symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v)) (ε/2)) :
    BoundedPhysicallyCorrectable (wallCoordinatePair v) U r ε := by
  let H := wallHomogeneousTensor χ v a
  let u := wallCoordinatePair v
  have hH : ContDiff ℝ (↑(⊤:ℕ∞)) H := wallHomogeneousTensor_smooth hχ hv ha hne
  have hc := wallHomogeneousTensor_compact (χ:=χ) (v:=v) (a:=a) hχc
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) u := wallCoordinatePair_smooth hv
  have hbal := wall_transfer_balanced_residual hχ hχc hv ha hz hne hcut hδ hgap hr hm hp
  have hcor : BoundedPhysicallyCorrectable u U (symmetricSource H u) (ε/2) :=
    ⟨H,hH,hc.1,hc.2.trans hχU,wallMatrix_symmetric _ _,fun _ => rfl,hsmall⟩
  have hh := hcor.add hu (hsolve hbal.1 hbal.2)
  rw [add_sub_cancel] at hh
  convert hh using 1
  ring

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem critical_wall_vanishing_transfer_correction
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {U : Set Coord3} (hU : IsOpen U)
    (hcp : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcn : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hD : ∀ x∈U,x 2≠0 → Function.Surjective
      (fderiv ℝ (wallCoordinatePair (fun y => v (p,y))) x))
    {χ : Box3 → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hχU : boxCoordinates ⁻¹' tsupport χ⊆U)
    {l t a b σ lam : ℝ} (hlt : l<t) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    (hcore : ∀ z∈Icc l t×ˢIcc a b,χ =ᶠ[𝓝 (z,0)] (fun _ => 1))
    (hlim : ∀ z : ℝ×ℝ,v (p,(z,0))=σ*Real.exp (-lam*z.1))
    {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hz : ∀ q∈V,∀ z,wallDerivative (fun y => v (q,y)) (z,0)=0)
    (hne : ∀ q∈V,∀ z∈tsupport χ,wallQuotient (wallDerivative (fun y => v (q,y))) z≠0)
    {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U)
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    {δr : ℝ} (hδr : 0<δr)
    (hgap : ∀ᶠ q in 𝓝 p,∀ j x,x∈tsupport (fun y => r j (q,y)) → δr≤|x 2|)
    (hrz : ∀ j x,r j (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,
      physicalSourceMoment (wallCoordinatePair (fun y => v (q,y))) (fun j x => r j (q,x))=0 →
      BoundedPhysicallyCorrectable (wallCoordinatePair (fun y => v (q,y))) U
        (fun j x => r j (q,x)) ε := by
  have hvq (q : P) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => v (q,y)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨δh,hδh,hsourcegap⟩ := exists_uniform_wall_source_gap hχ hχc
    (isClosed_Icc.prod isClosed_Icc) hcore
  let δ := min δr δh
  have hδ : 0<δ := lt_min hδr hδh
  obtain ⟨θ,η,hθ,hη,hθc,hηc,hθs,hηs,c,hc,hcm⟩ :=
    wall_vanishing_moment_coefficients hv p hlt hab hσ hlam hlim hV hp hr hK hs hrz δ
  have haSmooth (c : Coord3) : ContDiff ℝ (↑(⊤:ℕ∞)) (wallMomentAmplitude θ η σ lam c) :=
    (wallMomentAmplitude_parametric_smooth σ lam hθ hη).comp (contDiff_const.prodMk contDiff_id)
  have haSupp (c : Coord3) : tsupport (wallMomentAmplitude θ η σ lam c)⊆Icc l t×ˢIcc a b :=
    (wallMomentAmplitude_compact σ lam hθc hηc c).2.trans
      (prod_mono hθs (hηs.trans Ioo_subset_Icc_self))
  have hG (q : P) (hq : q∈V) (c : Coord3) (j : Fin 2) (x : Coord3)
      (hx : x∈tsupport (fun y => wallTransferSource χ v θ η σ lam j ((q,c),y))) :
      δ≤|x 2| :=
    (min_le_right δr δh).trans (hsourcegap (fun y => v (q,y))
      (wallMomentAmplitude θ η σ lam c) (hvq q) (haSmooth c) (hz q hq) (hne q hq)
      (haSupp c) j x hx)
  have hRsolve := wall_transfer_residual_solver hv p hU hcp hcn hD hχ hχc hχU
    hθ hη σ lam hV hp hne hr hK hKU hs hδ
    (hgap.mono (fun q hq j x hx => (min_le_left δr δh).trans (hq j x hx))) hG hrz
    (by linarith : 0<ε/2)
  have hHsmall := wallTransferFamily_small σ lam hχ hχc hv hθ hη hV hp hne (by linarith : 0<ε/2)
  have hqc : Tendsto (fun q => (q,c q)) (𝓝 p) (𝓝 (p,0)) := tendsto_id.prodMk_nhds hc
  filter_upwards [hqc.eventually hRsolve,hqc.eventually hHsmall,hcm,hs,hV.mem_nhds hp]
    with q hsolve hsmall hcmq hsq hq hmom
  have hrc : CompactSmoothPair (fun j x => r j (q,x)) := by
    intro j
    refine ⟨?_,hK.of_isClosed_subset (isClosed_tsupport _) (hsq j)⟩
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((hr j).contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hcut (z) : χ (z,0)*wallMomentAmplitude θ η σ lam (c q) z=
      wallMomentAmplitude θ η σ lam (c q) z := by
    by_cases hn : wallMomentAmplitude θ η σ lam (c q) z=0
    · simp only [hn,mul_zero]
    · rw [(hcore z (haSupp (c q) (subset_tsupport _ hn))).eq_of_nhds,one_mul]
  exact wall_transfer_finishes hχ hχc hχU (hvq q) (haSmooth (c q))
    (hz q hq) (hne q hq) hcut hδ (hG q hq (c q)) hrc hmom hcmq hsmall hsolve

end ScalarConductivity

end
end

end OAI
