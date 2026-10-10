import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.RepresentativeClosedBinSourceIndices
import OAI.Analysis.VlasovMaxwell.Flow.ClosedEulerianTimeBudget

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def sourceMajorantKernel (r : ℝ) (n W v E B : Vec) : ℝ :=
  (10*Real.sqrt (2*(1-dot n (velocity W)))/(r*q v))*
    (goodField E B n/(1-dot n (velocity v))+‖B‖)

lemma sourceMajorantKernel_nonneg {r : ℝ} {n W v E B : Vec}
    (hr : 0<r) (hn : ‖n‖=1) : 0≤ sourceMajorantKernel r n W v E B := by
  have hd := cone_denom_pos v n hn
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hq := q_pos v
  unfold sourceMajorantKernel
  positivity

lemma forceSourceKernel_le_majorant {r : ℝ} (n W v E B : Vec)
    (hr : 0<r) (hn : ‖n‖=1) :
    ‖forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤ sourceMajorantKernel r n W v E B := by
  have hd := cone_denom_pos v n hn
  apply (forceSourceKernel_bound r n W v E B hr hn).trans_eq
  unfold sourceMajorantKernel
  field_simp

lemma sourceMajorantKernel_bin_bound {r p θ φ : ℝ} (n W v E B : Vec)
    (hr : 0<r) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ) (hn : ‖n‖=1)
    (hq : p≤q v) (hdlo : θ^2/2≤1-dot n (velocity v))
    (hDhi : 1-dot n (velocity W)≤8*φ^2) :
    sourceMajorantKernel r n W v E B≤
      (80*φ/(r*p))*(goodField E B n/θ^2+‖B‖) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsφ : Real.sqrt (2*D)≤4*φ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hc : 10*Real.sqrt (2*D)/(r*q v)≤40*φ/(r*p) := by
    calc
      _ ≤ 10*(4*φ)/(r*p) := by gcongr
      _ = _ := by ring
  have hg : goodField E B n/d≤2*(goodField E B n/θ^2) := by
    calc
      _ ≤ goodField E B n/(θ^2/2) := by gcongr
      _ = _ := by ring
  calc
    _ = (10*Real.sqrt (2*D)/(r*q v))*(goodField E B n/d+‖B‖) := rfl
    _ ≤ (40*φ/(r*p))*(2*(goodField E B n/θ^2+‖B‖)) := by
      apply mul_le_mul hc _ (by positivity) (by positivity)
      linarith [norm_nonneg B]
    _ = _ := by ring

def physicalSourceMajorantDensity (s : Solution) (X V : ℝ→Vec)
    (C : ClosedConeBin) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
      let r := z.1-z.2.1
      let n := z.2.2.1
      let W := V z.1
      let y := X z.1-r • n
      ENNReal.ofReal (s.f (z.2.1,(y,v))*sourceMajorantKernel r n W v
        (s.E (z.2.1,y)) (s.B (z.2.1,y)))

lemma physicalSourceMajorantDensity_bound {s : Solution} {X V : ℝ→Vec}
    {C : ClosedConeBin} {p θ φ : ℝ} {z : ConeCoordinate}
    (hr : 0<z.1-z.2.1) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ)
    (hq : p≤C.qmin) (hd : θ^2/2≤C.dmin)
    (hD : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalSourceMajorantDensity s X V C z ≤
      ENNReal.ofReal ((80*φ/p)*(z.1-z.2.1)*
        (goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
          (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1/θ^2+
          ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖))*
        physicalBinDensity s X V C z.1 z.2.1 z.2.2 := by
  let G := goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
    (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1
  let b := ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖
  have hG : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb : 0≤b := norm_nonneg _
  unfold physicalSourceMajorantDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2) *
        ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal ((80*φ/((z.1-z.2.1)*p))*(G/θ^2+b))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
      intro v hv
      rw [←ENNReal.ofReal_mul (by positivity : 0≤(80*φ/((z.1-z.2.1)*p))*(G/θ^2+b))]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            ((80*φ/((z.1-z.2.1)*p))*(G/θ^2+b)) :=
          mul_le_mul_of_nonneg_left
            (sourceMajorantKernel_bin_bound _ _ _ _ _ hr hp hθ hφ (sphere_norm _)
              (hq.trans hv.1.1) (hd.trans hv.2.1.1) hD) (hf v)
        _ = _ := mul_comm _ _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      congr 1
      field_simp [hr.ne']
      rfl

lemma physicalSourceMajorant_integral_bound {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec}
    (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {p θ φ : ℝ} (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hr : 0<B.rmin) (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin)
    (hDhi : B.Dmax≤8*φ^2)
    :
    (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z ∂physicalBinMeasure V B J)≤
      ENNReal.ofReal (80*φ/(p*θ^2))*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeGood s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)+
      ENNReal.ofReal (80/p)*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*ENNReal.ofReal (prefixConeMagnetic s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) := by
  have hN := physicalBinDensity_aemeasurable hs hT hX hV B hJ hJT
  have hG := hs.measurable_prefixConeGood hT hX
  have hR : Measurable (fun z : ConeCoordinate=>ENNReal.ofReal (z.1-z.2.1)) :=
    (measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal
  have hb : (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,
        ENNReal.ofReal (80*φ/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)+
        ENNReal.ofReal (80/p)*(ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
          ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)
          ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    have hrz : 0<z.1-z.2.1 := hr.trans_le hz.2.2.1.1
    have hb := physicalSourceMajorantDensity_bound (X:=X)
      hrz hp hθ hφ.le hq hdlo (hz.2.2.2.2.2.trans hDhi)
      (fun v=>hs.nonnegative _ hzT _)
    apply hb.trans_eq
    let G := prefixConeGood s T X z
    let b := prefixConeMagnetic s T X z
    have hG0 : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
    have hb0 : 0≤b := norm_nonneg _
    have heG : goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
        (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1=G := by
      simp [G,prefixConeGood,prefixField,prefixClamp_eq hzT]
    have heb : ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖=b := by
      simp [b,prefixConeMagnetic,coneFoot,prefixField,prefixClamp_eq hzT]
    rw [heG,heb]
    have he : (80*φ/p)*(z.1-z.2.1)*(G/θ^2+b)=
        (80*φ/(p*θ^2))*((z.1-z.2.1)*G)+
          (80/p)*((z.1-z.2.1)*φ*b) := by ring
    rw [he,ENNReal.ofReal_add (by positivity) (by positivity),add_mul]
    simp only [ENNReal.ofReal_mul (by positivity : 0≤80*φ/(p*θ^2)),
      ENNReal.ofReal_mul (by positivity : 0≤80/p),
      ENNReal.ofReal_mul (mul_nonneg hrz.le hφ.le),ENNReal.ofReal_mul hrz.le]
    dsimp only [G,b]
    ac_rfl
  refine hb.trans_eq ?_
  have hMG : AEMeasurable (fun z : ConeCoordinate=>
      ENNReal.ofReal (80*φ/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2))
      (physicalBinMeasure V B J) := by
    simpa only [Pi.mul_apply] using (((hR.mul hG.ennreal_ofReal).aemeasurable.mul hN).const_mul
      (ENNReal.ofReal (80*φ/(p*θ^2))))
  rw [lintegral_add_left' hMG,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma Admissible.source_majorant_two_budget_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (B : ClosedConeBin) (S : Set Phase)
      (a b I p P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z=>s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
      0<I → 0<p → 0<P → 0<θ → 0<φ → 0≤σ → 0<B.rmin → 0<B.Dmin →
      p≤B.qmin → B.qmax≤P → θ^2/2≤B.dmin → B.dmax≤8*θ^2 →
      φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.emax≤8*σ^2 →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let M := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
          ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*P^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*P^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/(p*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*M))^(1/2:ℝ))+
        ENNReal.ofReal (80/p)*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*M))^(1/2:ℝ)) := by
  obtain ⟨Cg,hCg,hgood⟩ := hd₀.uniform_actual_bin_Cauchy
  obtain ⟨Cb,hCb,hmag⟩ := hd₀.uniform_actual_magnetic_Cauchy
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX B S a b I p P θ φ σ k j hS hS0 hJ hI hp hP hθ hφ hσ
    hR hD hqlo hqhi hdlo hdhi hDlo hDhi he hangle
  dsimp only
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hb := physicalSourceMajorant_integral_bound hs hT hα.fst.measurable hα.snd.measurable B
    measurableSet_Icc hJ hp hθ hφ hR hqlo hdlo hDhi
  exact hb.trans (add_le_add
    (mul_le_mul' le_rfl (hgood s T F hs hT h0 zX B S a b I P θ φ σ k j hS hS0 hJ
      hI hP hθ.le hφ.le hσ hR hD hqhi hdhi hDhi he hangle))
    (mul_le_mul' le_rfl (hmag s T F hs hT h0 zX B S a b I P θ φ σ k j hS hS0 hJ
      hI hP hθ.le hφ.le hσ hR hD hDlo hqhi hdhi hDhi he hangle)))

lemma Admissible.source_majorant_relative_budget {d : Datum} (hd₀ : Admissible d) :
    ∃Cg Cb : ℝ,0 ≤ Cg ∧ 0 ≤ Cb ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (B : ClosedConeBin) (S : Set Phase)
        (M A P L a b massScale φ θ σ Cs p len I : ℝ) (k j : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < p → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale →
      0 < φ → 0 < θ → 0 < σ → σ ≤ 1 → 128 ≤ Cs →
      2*len ≤ (Cs*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 →
      p/128 ≤ B.qmin → B.qmax ≤ p/32 → massScale ≤ B.qmin → massScale ≤ B.wmin →
      0 < B.rmin → 0 ≤ B.rmax → 0 < B.Dmin →
      θ^2/2 ≤ B.dmin → B.dmax ≤ 8*θ^2 → φ^2/2 ≤ B.Dmin → B.Dmax ≤ 8*φ^2 →
      σ^2/2 ≤ B.emin → B.emax ≤ 8*σ^2 → 4 ≤ σ*B.qmin → 4 ≤ σ*B.wmin →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let O := (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
        ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/((p/128)*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
        ENNReal.ofReal (80/(p/128))*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hforce⟩ := hd₀.source_majorant_two_budget_bound
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX B S M A P L a b massScale φ θ σ Cs p len I k j
    hS hS0 ha hb hab hp hlen hlenI hJI hM hA hP hL hm hφ hθ hσ hσ1 hCs hstable
    hqmin hqmax hmq hmw hr hrmax hD hdlo hdhi hDlo hDhi helo hehi hq hw hangle HX HZ
  dsimp only
  have hI : 0<I := hlen.trans_le hlenI
  have hpq : B.qmax≤p := hqmax.trans (by linarith)
  have hforceBound := hforce s T F hs hT h0 zX B S a b I (p/128) p θ φ σ k j
    hS hS0 (Icc_subset_Icc ha hb) hI (by positivity) hp hθ hφ hσ.le hr hD
    hqmin hpq hdlo hdhi hDlo hDhi hehi hangle
  have ho := F.relative_closedEulerian_baseline hs hT zX B hS ha hb hab hp hlen hlenI hJI
    hM hA hP hL hm hφ hσ hσ1 hCs hstable hqmin hqmax hmq hmw hr hrmax
    hDhi helo hehi hq hw HX HZ
  have hod : coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) ≤
      (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) := by
    simpa only [div_eq_mul_inv] using mul_le_mul' ho (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))
  apply hforceBound.trans
  gcongr

lemma Admissible.source_majorant_time_budget {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (B : ClosedConeBin) (S : Set Phase)
      (a b I p P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z=>s.f (0,z))⊆S → Icc a b⊆Icc 0 T → b-a≤I →
      0<I → 0<p → 0<P → 0<θ → 0<φ → 0≤σ → 0<B.rmin → 0<B.Dmin → 0<B.Dmax →
      p≤B.qmin → B.qmax≤P → θ^2/2≤B.dmin → B.dmax≤8*θ^2 →
      φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.emax≤8*σ^2 →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let O := (ENNReal.ofReal (16*I*φ^2/θ^2)*
        ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x))) / ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*P^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*P^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/(p*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
        ENNReal.ofReal (80/p)*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hforce⟩ := hd₀.source_majorant_two_budget_bound
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX B S a b I p P θ φ σ k j hS hS0 hJ hJI hI hp hP hθ hφ hσ
    hR hD hDmax hqlo hqhi hdlo hdhi hDlo hDhi he hangle
  dsimp only
  have hforceBound := hforce s T F hs hT h0 zX B S a b I p P θ φ σ k j hS hS0 hJ
    hI hp hP hθ hφ hσ hR hD hqlo hqhi hdlo hdhi hDlo hDhi he hangle
  have hC : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T := by
    intro r hr
    exact ⟨(le_max_left _ _).trans hr.1,hr.2.trans (min_le_left _ _)⟩
  have ho := F.closedEulerian_angular_time_budget hs hT zX B hS hJ hC hR hθ hφ hI.le hJI hdlo hDmax hDhi
  have hod : coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) ≤
      (ENNReal.ofReal (16*I*φ^2/θ^2)*ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) := by
    simpa only [div_eq_mul_inv] using mul_le_mul' ho (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))
  apply hforceBound.trans
  gcongr

lemma projected_source_combined_le_majorant {C T r f w : ℝ} {n v W E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0<r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    ‖f • angularMultiplierCLM w W (forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B)))‖+
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      (64+5880000*C)*(f*sourceMajorantKernel r n W v E B) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  let G := goodField E B n
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hD2 : D≤2 := cone_denom_le_two W n hn
  have hq := q_pos v
  have hG : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hroot : D≤Real.sqrt (2*D) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith
  have hroot10 : D≤10*Real.sqrt (2*D) := by
    nlinarith [Real.sqrt_nonneg (2*D)]
  have hmajor := sourceMajorantKernel_nonneg (n:=n) (W:=W) (v:=v) (E:=E) (B:=B) hr hn
  have hop := angularMultiplierCLM_norm_le hw (show w/64≤‖W‖ by linarith)
  have hdir : ‖f • angularMultiplierCLM w W (forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B)))‖≤
      64*(f*sourceMajorantKernel r n W v E B) := by
    rw [norm_smul,Real.norm_of_nonneg hf]
    calc
      _ ≤ f*(64*‖forceSourceKernel r n (velocity W) v
          (fderiv ℝ velocity v (E+cross (velocity v) B))‖) := by
        apply mul_le_mul_of_nonneg_left _ hf
        exact ((angularMultiplierCLM w W).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
      _ ≤ f*(64*sourceMajorantKernel r n W v E B) := by
        gcongr
        exact forceSourceKernel_le_majorant n W v E B hr hn
      _ = _ := by ring
  have hcut := projected_source_cutoff_cost (T:=T) (E:=E) (B:=B) hC0 hC hn hw hW hr hf hsmall Q
  change _≤5880000*C*(f/r)*((Real.sqrt (D/2))^2/q v)*
    (G/(Real.sqrt (d/2))^2+‖B‖) at hcut
  rw [Real.sq_sqrt (by positivity : 0≤D/2),Real.sq_sqrt (by positivity : 0≤d/2)] at hcut
  have hcut' : ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖≤
      (5880000*C)*(f*sourceMajorantKernel r n W v E B) := by
    calc
      _ ≤ 5880000*C*(f/r)*((D/2)/q v)*(G/(d/2)+‖B‖) := hcut
      _ = 5880000*C*(f/r)*(D/q v)*(G/d+‖B‖/2) := by ring_nf
      _ ≤ 5880000*C*(f/r)*((10*Real.sqrt (2*D))/q v)*(G/d+‖B‖) := by gcongr; linarith [norm_nonneg B]
      _ = _ := by unfold sourceMajorantKernel; dsimp only [d,D,G]; ring
  exact (add_le_add hdir hcut').trans_eq (by ring)

lemma physicalProjectedSourceDensity_le_majorant {s : Solution} {X V : ℝ→Vec}
    {C : ClosedConeBin} {T w c : ℝ} {z : ConeCoordinate} (Q : Set (Fin 4→ℕ))
    (hc : 0≤c) (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤c)
    (hw : 0<w) (hW : w/16≤‖V z.1‖) (hr : 0<z.1-z.2.1)
    (hsmall : C.dmax≤1-dot z.2.2.1 (velocity (V z.1)))
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalProjectedSourceDensity s X V C T w Q z ≤
      ENNReal.ofReal (64+5880000*c)*physicalSourceMajorantDensity s X V C z := by
  unfold physicalProjectedSourceDensity physicalSourceMajorantDensity
  conv_rhs => rw [mul_left_comm]
  apply mul_le_mul' le_rfl
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
  intro v hv
  rw [←ENNReal.ofReal_mul (by positivity : 0≤64+5880000*c)]
  apply ENNReal.ofReal_le_ofReal
  exact projected_source_combined_le_majorant hc hcut (sphere_norm _) hw hW hr (hf v)
    (hv.2.1.2.trans hsmall) Q

lemma physicalProjectedSourceIntegral_le_majorant {s : Solution} {T w c : ℝ}
    (hs : EnergyPrefix s T) {X V : ℝ→Vec} (hV : Measurable V)
    (C : ClosedConeBin) (Q : Set (Fin 4→ℕ)) {J : Set ℝ}
    (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hc : 0≤c) (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤c)
    (hw : 0<w) (hW : ∀t∈J,w/16≤‖V t‖) (hr : 0<C.rmin)
    (hsmall : C.dmax≤C.Dmin) :
    (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V C T w Q z
      ∂physicalBinMeasure V C J) ≤
    ENNReal.ofReal (64+5880000*c)*
      ∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V C z
        ∂physicalBinMeasure V C J := by
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV C hJ)] with z hz
  exact physicalProjectedSourceDensity_le_majorant Q hc hcut hw (hW z.1 hz.1)
    (hr.trans_le hz.2.2.1.1) (hsmall.trans hz.2.2.2.2.1)
    (fun v=>hs.nonnegative _ ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _)

lemma Admissible.source_majorant_relative_radius_budget {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ)
      (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      512 ≤ cappedRepresentative j*sourceRepresentative (k 0) →
      32 ≤ cappedRepresentative j*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
        Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let O := ENNReal.ofReal (491520*E*(1+φ/σ)*(1+I/len)/(p*r*φ^2))
      let H := ENNReal.ofReal (576*I*r*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (10240*φ/(p*θ^2))*
        ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*(min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
      ENNReal.ofReal (10240/p)*
        ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*(min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.source_majorant_relative_budget
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let B := relativeRepresentativeClosedBin T w k j
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,relativeRepresentativeClosedBin,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hI : 0<I := hlen.trans_le hlenI
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hn := hsource s T F hs hT h0 zX B S M A P L a b massScale φ θ σ Cs p len I 1 (k 2)
    hS hS0 ha hb hab hp hlen hlenI hJI hM hA hP hL hm hφ hθ hσ
    (cappedRepresentative_le_one _) hCs hstable le_rfl le_rfl hmq hmw
    (by rw [hBmin]; positivity) (by rw [hBmax]; positivity) (by rw [hBDmin]; positivity)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    (by change 4≤σ*(p/128); dsimp [σ,p] at *; nlinarith only [hqσ])
    (by change 4≤σ*(w/8); dsimp [σ] at *; nlinarith only [hwσ]) hangle HX HZ
  dsimp only at hn
  have hmass : (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
      ENNReal.ofReal (B.rmin^2*B.Dmin) =
      ENNReal.ofReal (491520*E*(1+φ/σ)*(1+I/len)/(p*r*φ^2)) := by
    rw [hBmax,hBmin,hBDmin,←ENNReal.ofReal_mul (by positivity : 0≤30720*(2*r)/p*(1+φ/σ)*(1+I/len)),
      ←ENNReal.ofReal_div_of_pos (by positivity : 0<(r/2)^2*(φ^2/2))]
    congr 1
    field_simp [hp.ne',hr.ne',hφ.ne',hσ.ne',hlen.ne']
    ring
  have hvolume : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) ≤
      ENNReal.ofReal (576*I*r*φ^2) := by
    rw [Real.volume_Icc,hBmax,hBmin]
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r-r/2)*ENNReal.ofReal (384*φ^2) := by gcongr
      _ = _ := by
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le (by linarith : 0≤2*r-r/2))]
        congr 1
        ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2) ≤
      ENNReal.ofReal (20*I*E) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hJI)
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*E)) := mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal I*(5*ENNReal.ofReal (4*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤ ENNReal.ofReal (40*(I+2*r)*E) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hh : min T (b-B.rmin)-max 0 (a-B.rmax) ≤ (1+2*r/I)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      have he : (1+2*r/I)*I=I+2*r := by field_simp
      rw [hBmin,hBmax,he]
      linarith only [hJI,hb',ha',hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0≤1+2*r/I) hh)
    calc
      _ ≤ ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal (2*I)*(10*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
          ←ENNReal.ofReal_mul (by positivity : 0≤10*(1+2*r/I)),
          ←ENNReal.ofReal_mul (by positivity : 0≤2*I)]
        congr 1
        field_simp [hI.ne']
        ring
  have heG : 80*φ/(p/128*θ^2)=10240*φ/(p*θ^2) := by ring
  have heB : 80/(p/128)=10240/p := by ring
  rw [heG,heB,hmass] at hn
  apply hn.trans
  apply add_le_add
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) le_rfl
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hmag (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) le_rfl

def majorant_relativeCauchyConstant (C E Z : ℝ) : ℝ :=
  31457280*C*Real.sqrt Z+10240*Real.sqrt Z*Real.sqrt (62914560*C*E)

lemma majorant_relativeCauchyConstant_nonneg {C E Z : ℝ} (hC : 0≤C) :
    0≤ majorant_relativeCauchyConstant C E Z := by unfold majorant_relativeCauchyConstant; positivity

lemma majorant_relative_density_near_sqrt {C I p ν r φ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hp : 0≤p) (_hν : 0≤ν) (hr : 0≤r) (hφ : 0≤φ) :
    Real.sqrt ((128*C*p^3*ν^2)^2*(576*I*r*φ^2)) =
      3072*C*p^3*ν^2*Real.sqrt I*Real.sqrt r*φ := by
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity),
    show 576*I*r*φ^2=576*((I*r)*φ^2) by ring,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤576),Real.sqrt_mul (mul_nonneg hI hr),
    Real.sqrt_mul hI,Real.sqrt_sq hφ]
  norm_num
  ring

lemma majorant_relative_density_far_sqrt {C E p ν R r φ κ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hp : 0<p) (hν : 0<ν) (hR : 0≤R)
    (hr : 0<r) (hφ : 0<φ) (hκ : 0≤κ) :
    Real.sqrt ((128*C*p^3*ν^2)*(491520*E*κ*R^2/(p*r*φ^2))) =
      Real.sqrt (62914560*C*E)*Real.sqrt κ*p*ν*R/(Real.sqrt r*φ) := by
  have he : (128*C*p^3*ν^2)*(491520*E*κ*R^2/(p*r*φ^2))=
      (62914560*C*E*κ)*p^2*ν^2*R^2/(r*φ^2) := by
    field_simp [hp.ne',hr.ne',hφ.ne']
    ring
  rw [he,source_far_sqrt_mass (by positivity) hp hν hR hr hφ,
    Real.sqrt_mul (by positivity : 0≤62914560*C*E)]

lemma majorant_relative_radius_cauchy_scalar {C E Z I p ν R r φ κ γ : ℝ}
    (hC : 0≤C) (hE : 0≤E) (hZ : 0≤Z) (hI : 0<I) (hp : 0<p)
    (hν : 0<ν) (hR : 0≤R) (hr : 0<r) (hφ : 0<φ) (hκ : 0≤κ) (hγ : 0≤γ) :
    let D := ENNReal.ofReal (128*C*p^3*ν^2)
    let H := ENNReal.ofReal (576*I*r*φ^2)
    let O := ENNReal.ofReal (491520*E*κ*R^2/(p*r*φ^2))
    ENNReal.ofReal (10240*γ/p)*
      ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*(min (D^2*H) (D*O))^(1/2:ℝ)) ≤
    ENNReal.ofReal (majorant_relativeCauchyConstant C E Z*
      min ((I*p^2*ν^2*φ*γ)*Real.sqrt r)
        ((Real.sqrt I*R*ν*Real.sqrt κ*γ/φ)/Real.sqrt r)) := by
  dsimp only
  let K := majorant_relativeCauchyConstant C E Z
  have hK : 0≤K := majorant_relativeCauchyConstant_nonneg hC
  rw [mul_min_of_nonneg _ _ hK,ENNReal.ofReal_min]
  apply le_min
  · calc
      _ ≤ ENNReal.ofReal (10240*γ/p)*
          ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*
            ((ENNReal.ofReal (128*C*p^3*ν^2))^2*ENNReal.ofReal (576*I*r*φ^2))^(1/2:ℝ)) := by
        gcongr
        exact min_le_left _ _
      _ = ENNReal.ofReal ((31457280*C*Real.sqrt Z)*
          ((I*p^2*ν^2*φ*γ)*Real.sqrt r)) := by
        rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*ν^2),
          ←ENNReal.ofReal_mul (sq_nonneg _),
          ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
          majorant_relative_density_near_sqrt hC hI.le hp.le hν.le hr.le hφ.le,
          Real.sqrt_mul hZ,
          ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt I),
          ←ENNReal.ofReal_mul (by positivity : 0≤10240*γ/p)]
        congr 1
        have hIsq : Real.sqrt I*Real.sqrt I=I := Real.mul_self_sqrt hI.le
        calc
          _ = 31457280*C*Real.sqrt Z*(Real.sqrt I*Real.sqrt I)*p^2*ν^2*φ*γ*Real.sqrt r := by
            field_simp [hp.ne']
            ring
          _ = _ := by rw [hIsq]; ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact le_add_of_nonneg_right (by positivity)
  · calc
      _ ≤ ENNReal.ofReal (10240*γ/p)*
          ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*
            ((ENNReal.ofReal (128*C*p^3*ν^2))*
              ENNReal.ofReal (491520*E*κ*R^2/(p*r*φ^2)))^(1/2:ℝ)) := by
        gcongr
        exact min_le_right _ _
      _ = ENNReal.ofReal ((10240*Real.sqrt Z*Real.sqrt (62914560*C*E))*
          ((Real.sqrt I*R*ν*Real.sqrt κ*γ/φ)/Real.sqrt r)) := by
        rw [←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*ν^2),
          ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
          majorant_relative_density_far_sqrt hC hE hp hν hR hr hφ hκ,Real.sqrt_mul hZ,
          ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt I),
          ←ENNReal.ofReal_mul (by positivity : 0≤10240*γ/p)]
        congr 1
        field_simp [hp.ne',hφ.ne',(Real.sqrt_pos.mpr hr).ne']
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact le_add_of_nonneg_left (by positivity)

lemma Admissible.source_majorant_relative_short_radius {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ)
      (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      512 ≤ cappedRepresentative j*sourceRepresentative (k 0) →
      32 ≤ cappedRepresentative j*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
        Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
      max 1 T*cappedRepresentative (k 3) ≤ I →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let R := Real.sqrt (1+I/len)
      let ν := min θ σ
      let κ := 1+φ/σ
      let Kg := majorant_relativeCauchyConstant Cg E (20*E)
      let Kb := majorant_relativeCauchyConstant Cb E (120*E)
      (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (Kg*min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
        ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r)+
      Kb*min ((I*p^2*ν^2*φ)*Real.sqrt r)
        ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.source_majorant_relative_radius_budget
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable hrI HX HZ
  have hn := hsource s T F hs hT h0 zX S k j a b I len w M A P L massScale Cs
    hS hS0 ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
  dsimp only at hn ⊢
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let ν := min θ σ
  let κ := 1+φ/σ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let R := Real.sqrt (1+I/len)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hν : 0<ν := lt_min hθ hσ
  have hκ : 0≤κ := by dsimp [κ]; positivity
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hI : 0<I := hlen.trans_le hlenI
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hR : 0≤R := Real.sqrt_nonneg _
  have hRsq : R^2=1+I/len := Real.sq_sqrt (by positivity)
  have hg := majorant_relative_radius_cauchy_scalar hCg hE (show 0≤20*E by positivity) hI hp hν hR hr hφ hκ
    (show 0≤φ/θ^2 by positivity)
  dsimp only at hg
  have heγ : 10240*(φ/θ^2)/p=10240*φ/(p*θ^2) := by ring
  have hea : I*p^2*ν^2*φ*(φ/θ^2)=I*p^2*ν^2*φ^2/θ^2 := by ring
  have heb : Real.sqrt I*R*ν*Real.sqrt κ*(φ/θ^2)/φ=Real.sqrt I*R*ν*Real.sqrt κ/θ^2 := by
    field_simp [hφ.ne']
  rw [heγ,hea,heb,show (20*E)*I=20*I*E by ring,hRsq] at hg
  have hbnd := majorant_relative_radius_cauchy_scalar hCb hE (show 0≤120*E by positivity) hI hp hν hR hr hφ hκ
    (show 0≤(1:ℝ) by norm_num)
  dsimp only at hbnd
  simp only [mul_one] at hbnd
  rw [show (120*E)*I=120*I*E by ring,hRsq] at hbnd
  have hmag : ENNReal.ofReal (40*(I+2*r)*E) ≤ ENNReal.ofReal (120*I*E) := by
    apply ENNReal.ofReal_le_ofReal
    have hrI' : r≤I := hrI
    nlinarith only [mul_nonneg (sub_nonneg.mpr hrI') hE]
  apply hn.trans
  calc
    _ ≤ ENNReal.ofReal (majorant_relativeCauchyConstant Cg E (20*E)*
          min ((I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)
            ((Real.sqrt I*R*ν*Real.sqrt κ/θ^2)/Real.sqrt r))+
        ENNReal.ofReal (majorant_relativeCauchyConstant Cb E (120*E)*
          min ((I*p^2*ν^2*φ)*Real.sqrt r)
            ((Real.sqrt I*R*ν*Real.sqrt κ/φ)/Real.sqrt r)) := by
      apply add_le_add hg
      refine le_trans ?_ hbnd
      apply mul_le_mul' le_rfl
      apply mul_le_mul' (ENNReal.rpow_le_rpow hmag (by norm_num)) le_rfl
    _ = _ := by
      rw [←ENNReal.ofReal_add
        (mul_nonneg (majorant_relativeCauchyConstant_nonneg hCg) (by positivity))
        (mul_nonneg (majorant_relativeCauchyConstant_nonneg hCb) (by positivity))]

lemma majorant_capped_sqrt_radius_ennreal_sum {a b H K : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hH : 0<H) (hK : 0≤K) :
    (∑'n : ℕ, ENNReal.ofReal (K*min (a*Real.sqrt (H*cappedRepresentative n))
      (b/Real.sqrt (H*cappedRepresentative n)))) ≤
      ENNReal.ofReal (K*dyadicBalanceConstant (1/2) (1/2)*Real.sqrt (a*b)) := by
  let g : ℤ→ℝ := fun k=>min (a*Real.sqrt (H*(2:ℝ)^k)) (b/Real.sqrt (H*(2:ℝ)^k))
  have hg0 (k : ℤ) : 0≤g k := by dsimp [g]; positivity
  have hg := dyadic_sqrt_radius_balance ha hb hH
  have he (n : ℕ) : cappedRepresentative n=(2:ℝ)^(-(n:ℤ)) := by
    simp only [cappedRepresentative,zpow_neg,zpow_natCast,inv_pow]
  have hinj : Function.Injective (fun n : ℕ=>-(n:ℤ)) := by
    intro a b hab
    exact_mod_cast neg_injective hab
  calc
    _ = ∑'n : ℕ,ENNReal.ofReal (K*g (-(n:ℤ))) := by
      apply tsum_congr
      intro n
      rw [he]
    _ ≤ ∑'k : ℤ,ENNReal.ofReal (K*g k) :=
      ENNReal.tsum_comp_le_tsum_of_injective hinj (fun k=>ENNReal.ofReal (K*g k))
    _ = ENNReal.ofReal (K*∑'k : ℤ,g k) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun k=>mul_nonneg hK (hg0 k)) (hg.1.mul_left K),tsum_mul_left]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left hg.2 hK

lemma Admissible.source_majorant_relative_short_radial_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ)
      (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative np/128 → massScale ≤ w/8 →
      512 ≤ cappedRepresentative j*sourceRepresentative np →
      32 ≤ cappedRepresentative j*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative j+
        Real.sqrt (A*L/cappedRepresentative j)))⁻¹^2 →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative np
      let θ := cappedRepresentative nθ
      let φ := cappedRepresentative nφ
      let σ := cappedRepresentative j
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let R := Real.sqrt (1+I/len)
      let ν := min θ σ
      let κ := 1+φ/σ
      let Kg := majorant_relativeCauchyConstant Cg E (20*E)
      let Kb := majorant_relativeCauchyConstant Cb E (120*E)
      let D := dyadicBalanceConstant (1/2) (1/2)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤I then
        ∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal (Kg*D*Real.sqrt
        ((I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt κ/θ^2))+
        Kb*D*Real.sqrt ((I*p^2*ν^2*φ)*(Real.sqrt I*R*ν*Real.sqrt κ/φ))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.source_majorant_relative_short_radius
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L massScale Cs hS hS0
    ha hb hab hlen hlenI hJI hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable HX HZ
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let ν := min θ σ
  let κ := 1+φ/σ
  let E := ∫x : Vec,totalEnergy s (0,x)
  let R := Real.sqrt (1+I/len)
  let Kg := majorant_relativeCauchyConstant Cg E (20*E)
  let Kb := majorant_relativeCauchyConstant Cb E (120*E)
  let ag := I*p^2*ν^2*φ^2/θ^2
  let bg := Real.sqrt I*R*ν*Real.sqrt κ/θ^2
  let ab := I*p^2*ν^2*φ
  let bb := Real.sqrt I*R*ν*Real.sqrt κ/φ
  let D := dyadicBalanceConstant (1/2) (1/2)
  have hI : 0<I := hlen.trans_le hlenI
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hν : 0≤ν := (lt_min hθ hσ).le
  have hag : 0≤ag := by dsimp [ag]; positivity
  have hbg : 0≤bg := by dsimp [bg,R,κ]; positivity
  have hab' : 0≤ab := by dsimp [ab]; positivity
  have hbb : 0≤bb := by dsimp [bb,R,κ]; positivity
  have hKg : 0≤Kg := majorant_relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := majorant_relativeCauchyConstant_nonneg hCb
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hH : 0 < max 1 T := zero_lt_one.trans_le (le_max_left _ _)
  have hpoint (nr : ℕ) := hsource s T F hs hT h0 zX S ![np,nθ,nφ,nr] j
    a b I len w M A P L massScale Cs hS hS0 ha hb hab hlen hlenI hJI
    hM hA hP hL hm hw hCs hmq hmw hqσ hwσ hstable
  calc
    _ ≤ ∑'nr : ℕ, (ENNReal.ofReal (Kg*min (ag*Real.sqrt (max 1 T*cappedRepresentative nr))
        (bg/Real.sqrt (max 1 T*cappedRepresentative nr)))+
      ENNReal.ofReal (Kb*min (ab*Real.sqrt (max 1 T*cappedRepresentative nr))
        (bb/Real.sqrt (max 1 T*cappedRepresentative nr)))) := by
      apply ENNReal.tsum_le_tsum
      intro nr
      split_ifs with hnr
      · have hn := hpoint nr hnr HX HZ
        dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
          Matrix.cons_val,Fin.reduceFinMk] at hn
        refine hn.trans_eq ?_
        exact ENNReal.ofReal_add (mul_nonneg hKg (by positivity)) (mul_nonneg hKb (by positivity))
      · exact bot_le
    _ ≤ ENNReal.ofReal (Kg*D*Real.sqrt (ag*bg))+
        ENNReal.ofReal (Kb*D*Real.sqrt (ab*bb)) := by
      rw [ENNReal.tsum_add]
      exact add_le_add (majorant_capped_sqrt_radius_ennreal_sum hag hbg hH hKg)
        (majorant_capped_sqrt_radius_ennreal_sum hab' hbb hH hKb)
    _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

lemma Admissible.source_majorant_remaining_short_sum {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 0 < w → w≤P →
      sourceRepresentative np≤128*P →
      cappedRepresentative nφ≤16384*cappedRepresentative nθ →
      512 ≤ cappedRepresentative j*sourceRepresentative np →
      32 ≤ cappedRepresentative j*w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := majorant_relativeCauchyConstant Cg E (20*E)
      let Kb := majorant_relativeCauchyConstant Cb E (120*E)
      (∑'nr : ℕ,if max 1 T*cappedRepresentative nr≤(w/P)^2 then
        ∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V (B nr) z
          ∂physicalBinMeasure V (B nr) (Icc a b) else 0) ≤
      ENNReal.ofReal ((16384*Kg+Kb)*dyadicBalanceConstant (1/2) (1/2)*
        Real.sqrt (32768*16385*(1+16384*(M+Real.sqrt A))*w^2*Real.sqrt (Real.log (2+P)))) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.source_majorant_relative_short_radial_sum
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
    hM hA hP hL hw hwP hpP hφθ hpσ hwσ HX HZ
  dsimp only
  let p := sourceRepresentative np
  let θ := cappedRepresentative nθ
  let φ := cappedRepresentative nφ
  let σ := cappedRepresentative j
  let L := Real.log (2+P)
  let I := (w/P)^2
  let lam := stabilityLength P 16384 M A p w σ
  let len := min I (lam/2)
  let m := min p w/128
  let E := ∫x : Vec,totalEnergy s (0,x)
  let R := Real.sqrt (1+I/len)
  let ν := min θ σ
  let Kg := majorant_relativeCauchyConstant Cg E (20*E)
  let Kb := majorant_relativeCauchyConstant Cb E (120*E)
  let D := dyadicBalanceConstant (1/2) (1/2)
  let U := 32768*16385*(1+16384*(M+Real.sqrt A))*w^2*Real.sqrt L
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hI : 0<I := sq_pos_of_pos (div_pos hw hP)
  have hlam : 0<lam := stabilityLength_pos hP (by norm_num) hM hp hw hσ
  have hlen : 0<len := lt_min hI (by positivity)
  have hlenI : len≤I := min_le_left _ _
  have hlenlam : 2*len≤lam := by
    have hh : len≤lam/2 := min_le_right _ _
    linarith only [hh]
  have hm : 0 < m := div_pos (lt_min hp hw) (by norm_num)
  have hmq : m≤p/128 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hmw : m≤w/8 := by
    have hh : min p w≤w := min_le_right _ _
    dsimp [m]
    linarith only [hh,hw]
  have hstable : 2*len≤(128*(P/m)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 := by
    dsimp only [m,L]
    rw [stability_massScale_identity]
    convert hlenlam using 1; norm_num [lam]
  have hn := hsource s T F hs hT h0 zX S np nθ nφ j a b I len w M A P L m 128
    hS hS0 ha hb hab hlen hlenI hJI hM hA hP (by dsimp [L]; linarith only [hL]) hm hw
    (by norm_num) hmq hmw hpσ hwσ hstable HX HZ
  have hg := remaining_good_balance_coefficient hP hL (show (0:ℝ)<16384 by norm_num)
    hM hA hp hw hθ hφ.le hσ (cappedRepresentative_le_one _) (by norm_num : (0:ℝ)≤16384) hφθ hpP hwP
  have hb' := remaining_magnetic_balance_coefficient hP hL (show (0:ℝ)<16384 by norm_num)
    hM hA hp hw hθ.le (cappedRepresentative_le_one _) hφ.le hσ
    (cappedRepresentative_le_one _) (by norm_num : (0:ℝ)≤16384) hφθ hpP hwP
  have hg' : (I*p^2*ν^2*φ^2/θ^2)*(Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/θ^2)≤268435456*U := by
    convert hg using 1 <;> dsimp [I,R,ν,len,lam,U,L] <;> ring
  have hb'' : (I*p^2*ν^2*φ)*(Real.sqrt I*R*ν*Real.sqrt (1+φ/σ)/φ)≤U := by
    convert hb' using 1
    · dsimp [I,R,ν,len,lam]
      field_simp [hφ.ne']
    · dsimp [U,L]
      ring
  have hKg : 0≤Kg := majorant_relativeCauchyConstant_nonneg hCg
  have hKb : 0≤Kb := majorant_relativeCauchyConstant_nonneg hCb
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have hr : Real.sqrt (268435456*U)=16384*Real.sqrt U := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤268435456)]; norm_num
  apply hn.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Kg*D*Real.sqrt (268435456*U)+Kb*D*Real.sqrt U :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg') (mul_nonneg hKg hD))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb'') (mul_nonneg hKb hD))
    _ = _ := by rw [hr]; dsimp [Kg,Kb,D,U,E,L]; ring

lemma Admissible.source_majorant_large_radius_budget {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      I ≤ max 1 T*cappedRepresentative (k 3) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Og := ENNReal.ofReal (491520*E/(p*r*φ^2))
      let Ob := ENNReal.ofReal (491520*I*E/(r^2*θ^2))
      let H := ENNReal.ofReal (576*I*r*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (10240*φ/(p*θ^2))*
        ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*(min (Dg^2*H) (Dg*Og))^(1/2:ℝ))+
      ENNReal.ofReal (10240/p)*
        ((ENNReal.ofReal (120*r*E))^(1/2:ℝ)*(min (Db^2*H) (Db*Ob))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.source_majorant_two_budget_bound
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I w hS hS0 ha hb hJI hI hIr
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let B := relativeRepresentativeClosedBin T w k j
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,relativeRepresentativeClosedBin,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hqlo : B.qmin=p/128 := rfl
  have hqhi : B.qmax≤p := by change p/32≤p; linarith only [hp]
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hC : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hR : 0<B.rmin := by rw [hBmin]; positivity
  have hD : 0<B.Dmin := by rw [hBDmin]; positivity
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hn := hsource s T F hs hT h0 zX B S a b I (p/128) p θ φ σ 1 (k 2)
    hS hS0 hJ hI (by positivity) hp hθ hφ hσ.le hR hD le_rfl hqhi
    le_rfl le_rfl le_rfl le_rfl le_rfl hangle
  let O := coneOccupation F.flow zX T s.f
    (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
      ENNReal.ofReal (B.rmin^2*B.Dmin)
  have hgO : O≤ENNReal.ofReal (491520*E/(p*r*φ^2)) := by
    have ho := F.closedEulerian_crude_budget hs hT zX B hS hJ hJI hR.le (by rw [hqlo]; positivity)
    have hc : ENNReal.ofReal (I+B.rmax)/ENNReal.ofReal B.qmin≤ENNReal.ofReal (384*r/p) := by
      rw [hBmax,hqlo,←ENNReal.ofReal_div_of_pos (by positivity : 0<p/128)]
      apply ENNReal.ofReal_le_ofReal
      calc
        (I+2*r)/(p/128)≤(3*r)/(p/128) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have hIr' : I≤r := hIr
          linarith only [hIr']
        _ = _ := by ring
    have ho' := ho.trans (mul_le_mul' hc le_rfl)
    calc
      O ≤ (ENNReal.ofReal (384*r/p)*ENNReal.ofReal E)/ENNReal.ofReal (B.rmin^2*B.Dmin) := by
        simpa only [O,div_eq_mul_inv] using mul_le_mul' ho' (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))
      _ = ENNReal.ofReal (3072*E/(p*r*φ^2)) := by
        rw [hBmin,hBDmin,←ENNReal.ofReal_mul (by positivity : 0≤384*r/p),
          ←ENNReal.ofReal_div_of_pos (by positivity : 0<(r/2)^2*(φ^2/2))]
        congr 1
        field_simp [hp.ne',hr.ne',hφ.ne']
        ring
      _ ≤ _ := by apply ENNReal.ofReal_le_ofReal; gcongr; norm_num
  have hbO : O≤ENNReal.ofReal (491520*I*E/(r^2*θ^2)) := by
    have ho := F.closedEulerian_angular_time_budget hs hT zX B hS hJ hC hR hθ hφ hI.le hJI
      le_rfl (by change 0<8*φ^2; positivity) le_rfl
    calc
      O ≤ (ENNReal.ofReal (16*I*φ^2/θ^2)*ENNReal.ofReal E)/ENNReal.ofReal (B.rmin^2*B.Dmin) := by
        simpa only [O,div_eq_mul_inv] using mul_le_mul' ho (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))
      _ = ENNReal.ofReal (128*I*E/(r^2*θ^2)) := by
        rw [hBmin,hBDmin,←ENNReal.ofReal_mul (by positivity : 0≤16*I*φ^2/θ^2),
          ←ENNReal.ofReal_div_of_pos (by positivity : 0<(r/2)^2*(φ^2/2))]
        congr 1
        field_simp [hr.ne',hφ.ne',hθ.ne']
        ring
      _ ≤ _ := by apply ENNReal.ofReal_le_ofReal; gcongr; norm_num
  have hvolume : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) ≤
      ENNReal.ofReal (576*I*r*φ^2) := by
    rw [Real.volume_Icc,hBmax,hBmin]
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r-r/2)*ENNReal.ofReal (384*φ^2) := by gcongr
      _ = _ := by
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le (by linarith : 0≤2*r-r/2))]
        congr 1
        ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2) ≤
      ENNReal.ofReal (20*I*E) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hJI)
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*E)) := mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal I*(5*ENNReal.ofReal (4*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤ ENNReal.ofReal (40*(I+2*r)*E) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hh : min T (b-B.rmin)-max 0 (a-B.rmax) ≤ (1+2*r/I)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      have he : (1+2*r/I)*I=I+2*r := by field_simp
      rw [hBmin,hBmax,he]
      linarith only [hJI,hb',ha',hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0≤1+2*r/I) hh)
    calc
      _ ≤ ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal (2*I)*(10*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
          ←ENNReal.ofReal_mul (by positivity : 0≤10*(1+2*r/I)),
          ←ENNReal.ofReal_mul (by positivity : 0≤2*I)]
        congr 1
        field_simp [hI.ne']
        ring

  have hmag' : ENNReal.ofReal (40*(I+2*r)*E)≤ENNReal.ofReal (120*r*E) := by
    apply ENNReal.ofReal_le_ofReal
    have hIr' : I≤r := hIr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hIr') hE]
  have heG : 80*φ/(p/128*θ^2)=10240*φ/(p*θ^2) := by ring
  have heB : 80/(p/128)=10240/p := by ring
  dsimp only at hn
  rw [heG,heB] at hn
  apply hn.trans
  apply add_le_add
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) (mul_le_mul' le_rfl hgO)
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow (hmag.trans hmag') (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact min_le_min (mul_le_mul' le_rfl hvolume) (mul_le_mul' le_rfl hbO)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma majorant_relative_radius_cauchy_near {C E Z I p ν r φ γ : ℝ}
    (hC : 0≤C) (hZ : 0≤Z) (hI : 0<I) (hp : 0<p)
    (hν : 0≤ν) (hr : 0≤r) (hφ : 0≤φ) (hγ : 0≤γ) :
    ENNReal.ofReal (10240*γ/p)*
      ((ENNReal.ofReal (Z*I))^(1/2:ℝ)*
        ((ENNReal.ofReal (128*C*p^3*ν^2))^2*ENNReal.ofReal (576*I*r*φ^2))^(1/2:ℝ)) ≤
    ENNReal.ofReal (majorant_relativeCauchyConstant C E Z*(I*p^2*ν^2*φ*γ)*Real.sqrt r) := by
  calc
    _ = ENNReal.ofReal ((31457280*C*Real.sqrt Z)*(I*p^2*ν^2*φ*γ)*Real.sqrt r) := by
      rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*ν^2),
        ←ENNReal.ofReal_mul (sq_nonneg _),
        ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
        majorant_relative_density_near_sqrt hC hI.le hp.le hν hr hφ,
        Real.sqrt_mul hZ,
        ←ENNReal.ofReal_mul (by positivity : 0≤Real.sqrt Z*Real.sqrt I),
        ←ENNReal.ofReal_mul (by positivity : 0≤10240*γ/p)]
      congr 1
      have hIsq : Real.sqrt I*Real.sqrt I=I := Real.mul_self_sqrt hI.le
      calc
        _ = 31457280*C*Real.sqrt Z*(Real.sqrt I*Real.sqrt I)*p^2*ν^2*φ*γ*Real.sqrt r := by
          field_simp [hp.ne']
          ring
        _ = _ := by rw [hIsq]; ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact le_add_of_nonneg_right (by positivity)

lemma Admissible.source_majorant_short_near {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0 ≤ Cg ∧ 0 ≤ Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (k : Fin 4→ℕ) (j : ℕ) (a b I w : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I →
      max 1 T*cappedRepresentative (k 3)≤I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let σ := cappedRepresentative j
      let ν := min θ σ
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := relativeRepresentativeClosedBin T w k j
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Kg := majorant_relativeCauchyConstant Cg E (20*E)
      let Kb := majorant_relativeCauchyConstant Cb E (120*E)
      (∫⁻z : ConeCoordinate,physicalSourceMajorantDensity s X V B z
        ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal ((Kg*(I*p^2*ν^2*φ^2/θ^2)+Kb*(I*p^2*ν^2*φ))*Real.sqrt r) := by
  obtain ⟨Cg,Cb,hCg,hCb,hsource⟩ := hd₀.source_majorant_two_budget_bound
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX S k j a b I w hS hS0 ha hb hJI hI hrI
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let σ := cappedRepresentative j
  let r := max 1 T*cappedRepresentative (k 3)
  let B := relativeRepresentativeClosedBin T w k j
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hσ : 0<σ := cappedRepresentative_pos _
  have hr : 0<r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,relativeRepresentativeClosedBin,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hqlo : B.qmin=p/128 := rfl
  have hqhi : B.qmax≤p := by change p/32≤p; linarith only [hp]
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hC : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hR : 0<B.rmin := by rw [hBmin]; positivity
  have hD : 0<B.Dmin := by rw [hBDmin]; positivity
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,relativeRepresentativeClosedBin,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hn := hsource s T F hs hT h0 zX B S a b I (p/128) p θ φ σ 1 (k 2)
    hS hS0 hJ hI (by positivity) hp hθ hφ hσ.le hR hD le_rfl hqhi
    le_rfl le_rfl le_rfl le_rfl le_rfl hangle
  have hvolume : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) ≤
      ENNReal.ofReal (576*I*r*φ^2) := by
    rw [Real.volume_Icc,hBmax,hBmin]
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r-r/2)*ENNReal.ofReal (384*φ^2) := by gcongr
      _ = _ := by
        rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le (by linarith : 0≤2*r-r/2))]
        congr 1
        ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2) ≤
      ENNReal.ofReal (20*I*E) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hJI)
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*E)) := mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal I*(5*ENNReal.ofReal (4*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2) ≤ ENNReal.ofReal (40*(I+2*r)*E) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hh : min T (b-B.rmin)-max 0 (a-B.rmax) ≤ (1+2*r/I)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      have he : (1+2*r/I)*I=I+2*r := by field_simp
      rw [hBmin,hBmax,he]
      linarith only [hJI,hb',ha',hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0≤1+2*r/I) hh)
    calc
      _ ≤ ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal (2*I)*(10*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
          ←ENNReal.ofReal_mul (by positivity : 0≤10*(1+2*r/I)),
          ←ENNReal.ofReal_mul (by positivity : 0≤2*I)]
        congr 1
        field_simp [hI.ne']
        ring

  have hmag' : ENNReal.ofReal (40*(I+2*r)*E)≤ENNReal.ofReal (120*I*E) := by
    apply ENNReal.ofReal_le_ofReal
    have hrI' : r≤I := hrI
    nlinarith only [mul_nonneg (sub_nonneg.mpr hrI') hE]
  have heG : 80*φ/(p/128*θ^2)=10240*φ/(p*θ^2) := by ring
  have heB : 80/(p/128)=10240/p := by ring
  dsimp only at hn
  rw [heG,heB] at hn
  have hnear := hn.trans (add_le_add
    (mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
      (ENNReal.rpow_le_rpow ((min_le_left _ _).trans (mul_le_mul' le_rfl hvolume)) (by norm_num))))
    (mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow (hmag.trans hmag') (by norm_num))
      (ENNReal.rpow_le_rpow ((min_le_left _ _).trans (mul_le_mul' le_rfl hvolume)) (by norm_num)))))
  let ν := min θ σ
  have hν : 0≤ν := (lt_min hθ hσ).le
  have hg := majorant_relative_radius_cauchy_near (E:=E) hCg (show 0≤20*E by positivity)
    hI hp hν hr.le hφ.le (show 0≤φ/θ^2 by positivity)
  have hm := majorant_relative_radius_cauchy_near (E:=E) hCb (show 0≤120*E by positivity)
    hI hp hν hr.le hφ.le (show 0≤(1:ℝ) by norm_num)
  have heγ : 10240*(φ/θ^2)/p=10240*φ/(p*θ^2) := by ring
  have hea : I*p^2*ν^2*φ*(φ/θ^2)=I*p^2*ν^2*φ^2/θ^2 := by ring
  rw [heγ,hea,show (20*E)*I=20*I*E by ring] at hg
  simp only [mul_one] at hm
  rw [show (120*E)*I=120*I*E by ring] at hm
  have hG0 : 0≤ majorant_relativeCauchyConstant Cg E (20*E)*(I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r :=
    mul_nonneg (mul_nonneg (majorant_relativeCauchyConstant_nonneg hCg) (by positivity)) (Real.sqrt_nonneg _)
  have hB0 : 0≤ majorant_relativeCauchyConstant Cb E (120*E)*(I*p^2*ν^2*φ)*Real.sqrt r :=
    mul_nonneg (mul_nonneg (majorant_relativeCauchyConstant_nonneg hCb) (by positivity)) (Real.sqrt_nonneg _)
  apply hnear.trans
  calc
    _ ≤ ENNReal.ofReal (majorant_relativeCauchyConstant Cg E (20*E)*(I*p^2*ν^2*φ^2/θ^2)*Real.sqrt r)+
        ENNReal.ofReal (majorant_relativeCauchyConstant Cb E (120*E)*(I*p^2*ν^2*φ)*Real.sqrt r) := add_le_add hg hm
    _ = _ := by rw [←ENNReal.ofReal_add hG0 hB0]; congr 1; ring

end RVM

end

end OAI
