import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.BranchIntegral
import OAI.Analysis.VlasovMaxwell.Geometry.UpperTimeCut
import OAI.Analysis.VlasovMaxwell.Continuation.PrefixMomentumForce
import OAI.Analysis.VlasovMaxwell.Retarded.DirectMixedCover

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.supported_boundary_force_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀(T : ℝ),0≤T → T≤T₀ →
      ∀(E B : Field) (F : PhaseFlowOn E B T) (zX : Phase), zX∈tsupport d.f₀ →
      ∀t∈Ioc (0:ℝ) T,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
        (velocity (F.flow zX t).2)‖≤C := by
  obtain ⟨R,hR⟩ := hd.2.1.bddAbove_image
    (show ContinuousOn (fun z : Phase=>‖z.1‖) (tsupport d.f₀) from continuous_fst.norm.continuousOn)
  obtain ⟨C,hC,hb⟩ := boundaryLorentzForce_datum_bound hd (max 1 T₀) (R+max 1 T₀)
  refine ⟨C,hC,?_⟩
  intro T hT hTT E B F zX hz t ht
  have hx0 : ‖zX.1‖≤R := hR ⟨zX,hz,rfl⟩
  have hh := (F.position_lipschitz zX).dist_le_mul t ⟨ht.1.le,ht.2⟩ 0 ⟨le_rfl,hT⟩
  simp only [F.initial,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1.le] at hh
  apply hb t ⟨ht.1,ht.2.trans (hTT.trans (le_max_right _ _))⟩ (F.flow zX t).1 _ _ (norm_velocity_lt_one _).le
  rw [mem_closedBall,dist_zero_right]
  calc
    ‖(F.flow zX t).1‖=‖((F.flow zX t).1-zX.1)+zX.1‖ := by rw [sub_add_cancel]
    _≤‖(F.flow zX t).1-zX.1‖+‖zX.1‖ := norm_add_le _ _
    _≤t+R := add_le_add (by simpa only [dist_eq_norm] using hh) hx0
    _≤R+max 1 T₀ := by linarith only [ht.2,hTT,le_max_right (1:ℝ) T₀]

lemma Admissible.direct_lorentz_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) →
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀(zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)≤
      ENNReal.ofReal (C*Real.sqrt w*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cb,hCb,hdatum⟩ := hd.supported_boundary_force_uniform T₀
  obtain ⟨Ct,hCt,htrans⟩ := hd.direct_transport_uniform T₀
  obtain ⟨Cs,hCs,hsource⟩ := hd.direct_source_absolute_uniform T₀
  refine ⟨Cb+(4*Real.pi)⁻¹*(Ct+Cs),by positivity,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hphysical hband HZ
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hsw : 1≤Real.sqrt w := by simpa using Real.sqrt_le_sqrt hw
  have hIB : I≤B := by
    have hIs : I≤Real.sqrt I := by nlinarith [Real.sq_sqrt hI.le,Real.sqrt_nonneg I]
    exact hIs.trans ((le_mul_of_one_le_left (Real.sqrt_nonneg I) hP).trans
      (show P*Real.sqrt I≤B from le_add_of_nonneg_right (by positivity)))
  have hJB : b-a≤Real.sqrt w*B := hJI.trans (hIB.trans (by nlinarith))
  have hcon := (F.continuous_prefixFlow hs.energyPrefix hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hX : Measurable X := hcon.fst.measurable
  have hV : Measurable V := hcon.snd.measurable
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hDb : ∀t∈Ioo 0 T∩Icc a b,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖≤Cb := by
    intro t ht
    dsimp only [X,V,prefixFlow]
    rw [prefixClamp_eq (hJ ht.2)]
    exact hdatum T hT hTT s.E s.B F zX hzX t ⟨ht.1.1,ht.1.2.le⟩
  have hraw : (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)=
      ∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))‖ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [prefixMomentumForce,lorentzField,lorentzPhase,X,V,prefixFlow,prefixClamp_eq (hJ ht)]
  rw [hraw]
  apply (hs.direct_lorentz_triangle_bound hT X V hX hV measurableSet_Icc hJ Cb hCb hDb).trans
  have hD : ENNReal.ofReal Cb*volume (Icc a b)≤ENNReal.ofReal (Cb*Real.sqrt w*B) := by
    rw [Real.volume_Icc,←ENNReal.ofReal_mul hCb]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hJB hCb
  have ht := htrans M A P hM (zero_le_one.trans hA) hP hL s T F hs hT hTT zX a b I w
    hzX ha hb hI hI1 hJI (zero_lt_one.trans_le hw) hwP hphysical hband HZ
  have hs' := hsource M A P hM hA hP hL s T F hs hT hTT zX a b I w
    hzX ha hb hab hI hI1 hJI hw hwP hIP hphysical hband HZ
  have ht' := ht.trans (show ENNReal.ofReal (Ct*B)≤ENNReal.ofReal (Ct*Real.sqrt w*B) from
    ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsw hCt) hB
      simpa only [mul_one] using hh))
  apply (add_le_add hD (mul_le_mul' le_rfl (add_le_add ht' hs'))).trans_eq
  rw [←ENNReal.ofReal_add (by positivity : 0≤Ct*Real.sqrt w*B) (by positivity : 0≤Cs*Real.sqrt w*B),
    ←ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹),
    ←ENNReal.ofReal_add (by positivity : 0≤Cb*Real.sqrt w*B) (by positivity)]
  congr 1
  ring

end RVM

end

end OAI
