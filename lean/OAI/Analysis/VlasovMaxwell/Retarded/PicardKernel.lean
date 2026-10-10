import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.NullConeFlux
import OAI.Analysis.VlasovMaxwell.Geometry.ShiftedRho
import OAI.Analysis.VlasovMaxwell.Geometry.CrossCLM

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma compact_parameter_lipschitz
    {U W Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {K : Set U} {S : Set W} {g : U × W → Z}
    (hK : IsCompact K) (hS : IsCompact S) (hconv : Convex ℝ S)
    (hg : ∀ q∈K ×ˢ S, ContDiffAt ℝ 1 g q) :
    ∃ C : ℝ, 0≤C ∧ ∀ p∈K, ∀ x∈S, ∀ y∈S, ‖g (p,y)-g (p,x)‖≤C*‖y-x‖ := by
  have hd : ContinuousOn (fderiv ℝ g) (K ×ˢ S) :=
    fun q hq => ((hg q hq).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨D,hD⟩ := ((hK.prod hS).image_of_continuousOn hd).isBounded.exists_norm_le
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro p hp x hx y hy
  apply hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => ((hg (p,z) ⟨hp,hz⟩).differentiableAt (by norm_num)).comp z
      ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z)).differentiableAt) _ hx hy
  intro z hz
  have hf := ((hg (p,z) ⟨hp,hz⟩).differentiableAt (by norm_num)).hasFDerivAt.comp z
    ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z))
  rw [hf.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _)
  intro v
  change ‖fderiv ℝ g (p,z) (0,v)‖≤ max D 0*‖v‖
  have hh := (fderiv ℝ g (p,z)).le_opNorm (0,v)
  simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg v)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    ((hD _ ⟨(p,z),⟨hp,hz⟩,rfl⟩).trans (le_max_left _ _)) (norm_nonneg v))

lemma contDiffAt_normalisedElectricKernel {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] {k : ℕ∞ω}
    {r : H → ℝ} {n u b : H → Vec} {z : H}
    (hr : ContDiffAt ℝ k r z) (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hb : ContDiffAt ℝ k b z) (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun p => normalisedElectricKernel (r p) (n p) (u p) (b p)) z := by
  have hdot (f g : H → Vec) (hf : ContDiffAt ℝ k f z) (hg : ContDiffAt ℝ k g z) :
      ContDiffAt ℝ k (fun p => dot (f p) (g p)) z :=
    contDiff_dot_pair.contDiffAt.comp z (hf.prodMk hg)
  have hD : ContDiffAt ℝ k (fun p => 1-dot (n p) (u p)) z :=
    contDiffAt_const.sub (hdot n u hn hu)
  exact (((contDiffAt_const.sub (hdot u u hu hu)).div (hD.pow 3) (pow_ne_zero 3 hd)).smul
      (hn.sub hu)).add ((hr.div (hD.pow 3) (pow_ne_zero 3 hd)).smul
      (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

def normalisedPhysicalIntegrand (p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec)) : Vec :=
  (p.2.1*(1-dot p.1.2.1 (velocity p.1.2.2))) •
    normalisedElectricKernel p.1.1 p.1.2.1 (velocity p.1.2.2)
      (fderiv ℝ velocity p.1.2.2 (p.2.2.1+cross (velocity p.1.2.2) p.2.2.2))

lemma normalisedPhysicalIntegrand_smoothAt {p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec)}
    (hd : 1-dot p.1.2.1 (velocity p.1.2.2)≠0) :
    ContDiffAt ℝ ∞ normalisedPhysicalIntegrand p := by
  let v : ((ℝ × Vec × Vec) × (ℝ × Vec × Vec)) → Vec := fun p => p.1.2.2
  have hv : ContDiff ℝ ∞ v := contDiff_fst.snd.snd
  have hu : ContDiff ℝ ∞ (fun p => velocity (v p)) := contDiff_velocity.comp hv
  have hb : ContDiff ℝ ∞ (fun p => fderiv ℝ velocity (v p)
      (p.2.2.1+cross (velocity (v p)) p.2.2.2)) :=
    (((contDiff_velocity (k:=∞)).fderiv_right (by simp)).comp hv).clm_apply
      (contDiff_snd.snd.fst.add (contDiff_cross.comp (hu.prodMk contDiff_snd.snd.snd)))
  have hD : ContDiff ℝ ∞ (fun p => 1-dot p.1.2.1 (velocity (v p))) :=
    contDiff_const.sub (contDiff_dot_pair.comp (contDiff_fst.snd.fst.prodMk hu))
  exact (contDiffAt_snd.fst.mul hD.contDiffAt).smul
    (contDiffAt_normalisedElectricKernel contDiffAt_fst.fst contDiffAt_fst.snd.fst
      hu.contDiffAt hb.contDiffAt hd)

lemma uniform_normalised_integrand_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a b : ℝ, |a|≤A → |b|≤A →
      ∀ E B E' B' : Vec, ‖E‖≤L → ‖B‖≤L → ‖E'‖≤L → ‖B'‖≤L →
      ‖normalisedPhysicalIntegrand ((r,n,v),(a,E,B))-
        normalisedPhysicalIntegrand ((r,n,v),(b,E',B'))‖≤
          C*max |a-b| (max ‖E-E'‖ ‖B-B'‖) := by
  let K : Set (ℝ × Vec × Vec) := Icc (0:ℝ) 1 ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  let S : Set (ℝ × Vec × Vec) := closedBall (0:ℝ) A ×ˢ closedBall (0:Vec) L ×ˢ closedBall (0:Vec) L
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere _ _).prod (isCompact_closedBall _ _))
  have hS : IsCompact S := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : Convex ℝ S := (convex_closedBall _ _).prod ((convex_closedBall _ _).prod (convex_closedBall _ _))
  obtain ⟨C,hC,hb⟩ := compact_parameter_lipschitz hK hS hc (g:=normalisedPhysicalIntegrand) (by
    intro p hp
    apply (normalisedPhysicalIntegrand_smoothAt ?_).of_le (by simp)
    exact (cone_denom_pos p.1.2.2 p.1.2.1
      (by simpa only [mem_sphere,dist_zero_right] using hp.1.2.1)).ne')
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a b ha hb' E B E' B' hE hB hE' hB'
  have hh := hb (r,n,v) ⟨hr,by simpa only [mem_sphere,dist_zero_right] using hn,
      by simpa only [mem_closedBall_zero_iff] using hv⟩
    (b,E',B') ⟨by simpa only [mem_closedBall_zero_iff,Real.norm_eq_abs] using hb',
      by simpa only [mem_closedBall_zero_iff] using hE',by simpa only [mem_closedBall_zero_iff] using hB'⟩
    (a,E,B) ⟨by simpa only [mem_closedBall_zero_iff,Real.norm_eq_abs] using ha,
      by simpa only [mem_closedBall_zero_iff] using hE,by simpa only [mem_closedBall_zero_iff] using hB⟩
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] using hh

lemma normalisedPhysicalIntegrand_eq {r : ℝ} (hr : r≠0) (n v : Vec) (a : ℝ) (E B : Vec) :
    normalisedPhysicalIntegrand ((r,n,v),(a,E,B)) = r^2 •
      ((a*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  simp only [normalisedPhysicalIntegrand,normalisedElectricKernel_eq hr]
  exact smul_comm _ _ _

lemma uniform_physical_integrand_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a b : ℝ, |a|≤A → |b|≤A →
      ∀ E B E' B' : Vec, ‖E‖≤L → ‖B‖≤L → ‖E'‖≤L → ‖B'‖≤L →
      ‖(a*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B))-
        (b*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E'+cross (velocity v) B'))‖≤
          (C/r^2)*max |a-b| (max ‖E-E'‖ ‖B-B'‖) := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_integrand_lipschitz A P L
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a b ha hb' E B E' B' hE hB hE' hB'
  have hh := hb r ⟨hr.1.le,hr.2⟩ n hn v hv a b ha hb' E B E' B' hE hB hE' hB'
  rw [normalisedPhysicalIntegrand_eq hr.1.ne',normalisedPhysicalIntegrand_eq hr.1.ne',
    ← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (by simpa only [mul_comm] using hh)

lemma integrable_physical_integrand {f : Vec → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) {r : ℝ} (hr : r≠0) {n : Vec} (hn : ‖n‖=1) (E B : Vec) :
    Integrable (fun v : Vec => (f v*(1-dot n (velocity v))) •
      physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  have hd : Continuous (fun v => 1-dot n (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
      (continuous_const.prodMk (contDiff_velocity (k:=1)).continuous))
  exact ((hf.mul hd).smul (continuous_physicalElectricKernel_velocity hr hn E B)).integrable_of_hasCompactSupport
    (hc.mul_right.smul_right)

lemma uniform_physical_integral_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ f g : Vec → ℝ, Continuous f → Continuous g → HasCompactSupport f → HasCompactSupport g →
      (∀ v, |f v|≤A ∧ |g v|≤A) → (∀ v, P<‖v‖ → f v=0 ∧ g v=0) →
      ∀ E B E' B' : Vec, ‖E‖≤L → ‖B‖≤L → ‖E'‖≤L → ‖B'‖≤L →
      ∀ D : ℝ, (∀ v, |f v-g v|≤D) → ‖E-E'‖≤D → ‖B-B'‖≤D →
      ‖(∫ v : Vec, (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B)))-
        (∫ v : Vec, (g v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E'+cross (velocity v) B')))‖≤ C*D/r^2 := by
  obtain ⟨K,hK,hk⟩ := uniform_physical_integrand_lipschitz A P L
  refine ⟨K*volume.real (closedBall (0:Vec) P),by positivity,?_⟩
  intro r hr n hn f g hf hg hfc hgc hab hs E B E' B' hE hB hE' hB' D hD hEd hBd
  rw [← integral_sub (integrable_physical_integrand hf hfc hr.1.ne' hn E B)
    (integrable_physical_integrand hg hgc hr.1.ne' hn E' B')]
  let H : Vec → Vec := fun v =>
    (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B))-
    (g v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E'+cross (velocity v) B'))
  change ‖∫ v, H v‖≤_
  have he : (∫ v in closedBall (0:Vec) P, H v)=∫ v, H v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    obtain ⟨hvf,hvg⟩ := hs v (by simpa only [mem_closedBall_zero_iff,not_le] using hv)
    simp only [H,hvf,hvg,zero_mul,zero_smul,sub_self]
  rw [← he]
  have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume)
    (isCompact_closedBall (0:Vec) P).measure_lt_top (C:=(K/r^2)*D) (f:=H) (by
      intro v hv
      exact (hk r hr n hn v (mem_closedBall_zero_iff.mp hv) (f v) (g v) (hab v).1 (hab v).2
        E B E' B' hE hB hE' hB').trans
          (mul_le_mul_of_nonneg_left (max_le (hD v) (max_le hEd hBd)) (by positivity)))
  exact hh.trans_eq (by ring)

lemma uniform_retarded_density_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s s' : Solution) (T : ℝ), T≤1 →
      ContDiff ℝ ∞ s.f → ContDiff ℝ ∞ s'.f →
      CompactOnFiniteHorizons s → CompactOnFiniteHorizons s' →
      (∀ t∈Icc 0 T, ∀ x v, |s.f (t,x,v)|≤A ∧ |s'.f (t,x,v)|≤A) →
      (∀ t∈Icc 0 T, ∀ x v, P<‖v‖ → s.f (t,x,v)=0 ∧ s'.f (t,x,v)=0) →
      (∀ t∈Icc 0 T, ∀ x, ‖s.E (t,x)‖≤L ∧ ‖s.B (t,x)‖≤L ∧
        ‖s'.E (t,x)‖≤L ∧ ‖s'.B (t,x)‖≤L) →
      ∀ t∈Icc 0 T, ∀ x x' z : Vec, 0<‖z‖ → ‖z‖≤t → ∀ D : ℝ,
      (∀ v, |s.f (t-‖z‖,x+z,v)-s'.f (t-‖z‖,x'+z,v)|≤D) →
      ‖s.E (t-‖z‖,x+z)-s'.E (t-‖z‖,x'+z)‖≤D →
      ‖s.B (t-‖z‖,x+z)-s'.B (t-‖z‖,x'+z)‖≤D →
        ‖retardedElectricDensity s t x (x+z)-retardedElectricDensity s' t x' (x'+z)‖≤C*D/‖z‖^2 ∧
        ‖retardedMagneticDensity s t x (x+z)-retardedMagneticDensity s' t x' (x'+z)‖≤C*D/‖z‖^2 := by
  obtain ⟨C,hC,hk⟩ := uniform_physical_integral_lipschitz A P L
  refine ⟨C,hC,?_⟩
  intro s s' T hT hf hf' hc hc' hab hs hEB t ht x x' z hz hzt D hD hEd hBd
  have htime : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  have hxy : x≠x+z := by
    intro he
    have hh : z=0 := add_left_cancel (show x+z=x+0 by simpa using he.symm)
    exact (norm_pos_iff.mp hz) hh
  have hn : ‖-(‖z‖⁻¹ • z)‖=1 := by simpa only [coneDirection_add] using coneDirection_norm hxy
  obtain ⟨hfc,hcomp⟩ := (show RegularParticle s.f from ⟨(hf.of_le (by simp)).contDiffOn,hc⟩).slice htime.1 (x+z)
  obtain ⟨hgc,hcomp'⟩ := (show RegularParticle s'.f from ⟨(hf'.of_le (by simp)).contDiffOn,hc'⟩).slice htime.1 (x'+z)
  have he : ‖retardedElectricDensity s t x (x+z)-retardedElectricDensity s' t x' (x'+z)‖≤C*D/‖z‖^2 := by
    simp only [retardedElectricDensity,coneRadius_add,coneDirection_add]
    exact hk ‖z‖ ⟨hz,hzt.trans (ht.2.trans hT)⟩ _ hn _ _ hfc.continuous hgc.continuous hcomp hcomp'
      (fun v => ⟨(hab _ htime (x+z) v).1,(hab _ htime (x'+z) v).2⟩)
      (fun v hv => ⟨(hs _ htime (x+z) v hv).1,(hs _ htime (x'+z) v hv).2⟩)
      _ _ _ _ (hEB _ htime (x+z)).1 (hEB _ htime (x+z)).2.1
      (hEB _ htime (x'+z)).2.2.1 (hEB _ htime (x'+z)).2.2.2 D hD hEd hBd
  refine ⟨he,?_⟩
  simp only [retardedMagneticDensity,coneDirection_add,← cross_sub_right]
  exact (norm_cross_le _ _).trans (by simpa only [hn,one_mul] using he)

end RVM
end

end OAI
