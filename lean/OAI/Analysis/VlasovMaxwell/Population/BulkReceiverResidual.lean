import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.UpperTimeCut
import OAI.Analysis.VlasovMaxwell.Continuation.PrefixMomentumForce
import OAI.Analysis.VlasovMaxwell.Population.BulkTestWeight
import OAI.Analysis.VlasovMaxwell.Population.UnselectedCover

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.force_bulk_receiver_residual_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
      ENNReal.ofReal ((4*Real.pi)⁻¹) *
        (ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) := by
  obtain ⟨Cs,hCs,hselected⟩ := hd.selected_force_residual_uniform T₀ D hD
  obtain ⟨Cu,hCu,hunselected⟩ := hd.unselected_label_uniform T₀
  refine ⟨Cu+Cs,add_nonneg hCu hCs,?_⟩
  intro M A hM hA
  filter_upwards [hselected M A hM (zero_lt_one.trans_le hA),hunselected M A hM hA] with P hsel hun
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  have hc := hsel hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  have hu := hun hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ hψ.continuous.measurable hψ1 hout
  apply hc.trans
  apply mul_le_mul' le_rfl
  apply add_le_add
  · apply (add_le_add hu le_rfl).trans_eq
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  · apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCu)
      (Real.rpow_nonneg (zero_le_one.trans hw) _)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.force_bulk_retarded_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cr,hCr,hresidual⟩ := hd.force_bulk_receiver_residual_uniform T₀ D hD
  obtain ⟨Ca,hCa,habsolute⟩ := hd.direct_lorentz_uniform T₀
  refine ⟨(4*Real.pi)⁻¹*(Cr+Cr*Ca),by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hresidual M A hM hA] with P hres
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  have hr := hres hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  have ha' := habsolute M A P hM hA hP hL s T F hs hT hTT zX a b I w
    hzX ha hb hab hI hI1 hJI hw hwP hIP hphysical hband HZ
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hc : w^(-1/2:ℝ)*Real.sqrt w=1 := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hw0]
    norm_num
  apply hr.trans
  apply (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl ha'))).trans_eq
  rw [←ENNReal.ofReal_mul (by positivity : 0≤Cr*w^(-1/2:ℝ)),
    ←ENNReal.ofReal_add (by positivity : 0≤Cr*B) (by positivity),
    ←ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹)]
  congr 1
  change (4*Real.pi)⁻¹*(Cr*B+Cr*w^(-1/2:ℝ)*(Ca*Real.sqrt w*B))=_
  calc
    _=(4*Real.pi)⁻¹*(Cr*B+Cr*Ca*(w^(-1/2:ℝ)*Real.sqrt w)*B) := by ring
    _=_ := by rw [hc]; ring

lemma Admissible.force_bulk_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1)))‖ ≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cr,hCr,hretarded⟩ := hd.force_bulk_retarded_uniform T₀ D hD
  obtain ⟨Cb,hCb,hdatum⟩ := hd.supported_boundary_force_uniform T₀
  refine ⟨Cr+Cb,add_nonneg hCr hCb,?_⟩
  intro M A hM hA
  filter_upwards [hretarded M A hM hA] with P hret
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let K := fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))
  let G := fun t=>boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)
  have hB : 0≤B := by dsimp [B]; positivity
  have hIB : I≤B := by
    have hi : I≤Real.sqrt I := by nlinarith [Real.sq_sqrt hI.le,Real.sqrt_nonneg I]
    exact hi.trans ((le_mul_of_one_le_left (Real.sqrt_nonneg I) hP).trans
      (show P*Real.sqrt I≤B from le_add_of_nonneg_right (by positivity)))
  have hiK : IntegrableOn (fun t=>ψ t • K t) (Ioo (0:ℝ) T) := by
    have hi := ((hψ.continuous.smul (F.continuous_prefixMomentumForce hs.energyPrefix hT zX)).continuousOn.integrableOn_Icc
      (μ:=volume) (a:=0) (b:=T)).mono_set Ioo_subset_Icc_self
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change ψ t • prefixMomentumForce s F.flow T zX t=ψ t • K t
    simp only [K,prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht),lorentzField,lorentzPhase]
  have hiR : IntegrableOn (fun t=>ψ t • (K t-G t)) (Ioo (0:ℝ) T) := by
    let W := fun t=>ψ t • ContinuousLinearMap.id ℝ Vec
    have hW : Continuous W := hψ.continuous.smul continuous_const
    simpa only [W,smul_apply,ContinuousLinearMap.id_apply] using
      hs.multiplier_retarded_force_integrable hT F zX hW.continuousOn
  have hiG : IntegrableOn (fun t=>ψ t • G t) (Ioo (0:ℝ) T) := by
    apply (hiK.sub hiR).congr
    exact ae_of_all _ (fun t=>by simp only [Pi.sub_apply,smul_sub,sub_sub_cancel])
  have hG : ‖∫t in Ioo (0:ℝ) T,ψ t • G t‖≤Cb*B := by
    apply le_trans (b:=Cb*(∫t in Ioo (0:ℝ) T,|ψ t|))
    · rw [←integral_const_mul]
      apply norm_integral_le_of_norm_le
        (((hψ.continuous.norm.const_mul Cb).continuousOn.integrableOn_Icc (a:=0) (b:=T)).mono_set Ioo_subset_Icc_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [norm_smul,Real.norm_eq_abs,mul_comm Cb]
      exact mul_le_mul_of_nonneg_left (hdatum T hT hTT s.E s.B F zX hzX t ⟨ht.1,ht.2.le⟩) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left
        ((bounded_supported_test_mass hab hψ.continuous hψ1 hout).trans (hJI.trans hIB)) hCb
  have he : (∫t in Ioo (0:ℝ) T,ψ t • K t)=
      (∫t in Ioo (0:ℝ) T,ψ t • (K t-G t))+(∫t in Ioo (0:ℝ) T,ψ t • G t) := by
    simp_rw [smul_sub]
    rw [integral_sub hiK hiG,sub_add_cancel]
  have hr := hret hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  change ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t • K t‖≤_
  rw [he]
  apply (ENNReal.ofReal_le_ofReal (norm_add_le _ _)).trans
  rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  apply (add_le_add hr (ENNReal.ofReal_le_ofReal hG)).trans_eq
  rw [←ENNReal.ofReal_add (mul_nonneg hCr hB) (mul_nonneg hCb hB)]
  congr 1
  change Cr*B+Cb*B=(Cr+Cb)*B
  ring

end RVM

end

end OAI
