import OAI.Combinatorics.HalvingLines.Noncollapse

namespace OAI

open Filter Topology

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

abbrev UnitSphere := {u : Point // ‖u‖=1}
instance : Nonempty UnitSphere := ⟨⟨(1,0),by simp [Prod.norm_def]⟩⟩
instance : CompactSpace UnitSphere := by
  have hc : IsCompact (sphere (0:Point) 1) := isCompact_sphere _ _
  have he : sphere (0:Point) 1 = {u | ‖u‖=1} := by ext x; simp
  rw [he] at hc
  exact isCompact_iff_compactSpace.mp hc

noncomputable def radialU (f : Point → Point) (p : Point) (h : ℝ) : ℝ :=
  sSup (range fun u : UnitSphere => dist (f (p+h • (u:Point))) (f p))
noncomputable def radialV (f : Point → Point) (p : Point) (h : ℝ) : ℝ :=
  sInf (range fun u : UnitSphere => dist (f (p+h • (u:Point))) (f p))

lemma unitSphere_param {p : Point} {h : ℝ} (hh : 0≤h) (u : UnitSphere) :
    p+h • (u:Point)∈sphere p h := by
  simp only [mem_sphere,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg hh,u.property,mul_one]

lemma sphere_representation {p x : Point} {h : ℝ} (hh : 0<h) (hx : x∈sphere p h) :
    ∃ u : UnitSphere, x=p+h • (u:Point) := by
  have hn : ‖x-p‖=h := hx
  refine ⟨⟨h⁻¹ • (x-p),?_⟩,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),hn,inv_mul_cancel₀ hh.ne']
  · simp only [smul_smul,mul_inv_cancel₀ hh.ne',one_smul,add_sub_cancel]

lemma continuous_sphereValue {f : Point → Point} {p : Point} {h : ℝ} (hh : 0≤h)
    (hf : ContinuousOn f (closedBall p h)) :
    Continuous (fun u : UnitSphere => dist (f (p+h • (u:Point))) (f p)) := by
  have hc : Continuous (fun u : UnitSphere => p+h • (u:Point)) := by fun_prop
  exact (hf.comp_continuous hc
    (fun u => sphere_subset_closedBall (unitSphere_param (p:=p) hh u))).dist continuous_const

lemma radialU_attained {f : Point → Point} {p : Point} {h : ℝ} (hh : 0<h)
    (hf : ContinuousOn f (closedBall p h)) :
    ∃ x ∈ sphere p h, dist (f x) (f p)=radialU f p h ∧
      ∀ y∈sphere p h, dist (f y) (f p)≤radialU f p h := by
  obtain ⟨u,_,he,hu⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    (Set.univ_nonempty : (univ:Set UnitSphere).Nonempty) (continuous_sphereValue hh.le hf).continuousOn
  have he' : radialU f p h=dist (f (p+h • (u:Point))) (f p) := by
    simpa only [image_univ,radialU] using he
  refine ⟨_,unitSphere_param hh.le u,he'.symm,?_⟩
  intro y hy
  obtain ⟨v,rfl⟩ := sphere_representation hh hy
  rw [he']
  exact hu v (mem_univ _)

lemma radialV_attained {f : Point → Point} {p : Point} {h : ℝ} (hh : 0<h)
    (hf : ContinuousOn f (closedBall p h)) :
    ∃ x ∈ sphere p h, dist (f x) (f p)=radialV f p h ∧
      ∀ y∈sphere p h, radialV f p h≤dist (f y) (f p) := by
  obtain ⟨u,_,he,hu⟩ := isCompact_univ.exists_sInf_image_eq_and_le
    (Set.univ_nonempty : (univ:Set UnitSphere).Nonempty) (continuous_sphereValue hh.le hf).continuousOn
  have he' : radialV f p h=dist (f (p+h • (u:Point))) (f p) := by
    simpa only [image_univ,radialV] using he
  refine ⟨_,unitSphere_param hh.le u,he'.symm,?_⟩
  intro y hy
  obtain ⟨v,rfl⟩ := sphere_representation hh hy
  rw [he']
  exact hu v (mem_univ _)

lemma radial_extrema_bounds {f : Point → Point} {p : Point} {h : ℝ} (hh : 0<h)
    (hf : ContinuousOn f (closedBall p h)) :
    0≤radialV f p h ∧ radialV f p h≤radialU f p h ∧
      ∀ x∈sphere p h, radialV f p h≤dist (f x) (f p) ∧ dist (f x) (f p)≤radialU f p h := by
  obtain ⟨x,hx,he,hlo⟩ := radialV_attained hh hf
  obtain ⟨y,hy,he',hup⟩ := radialU_attained hh hf
  refine ⟨he ▸ dist_nonneg,?_,fun z hz => ⟨hlo z hz,hup z hz⟩⟩
  rw [← he']; exact hlo y hy

lemma radialV_pos {f : Point → Point} {p : Point} {h : ℝ} (hh : 0<h)
    (hf : ContinuousOn f (closedBall p h)) (hinj : InjOn f (closedBall p h)) :
    0<radialV f p h := by
  obtain ⟨x,hx,he,_⟩ := radialV_attained hh hf
  rw [← he,dist_pos]
  intro hf'
  have hxp := hinj (sphere_subset_closedBall hx) (mem_closedBall_self hh.le) hf'
  have hh' : h=0 := by simpa only [hxp,dist_self,eq_comm,mem_sphere] using hx
  exact hh.ne' hh'

lemma continuousOn_radialU {f : Point → Point} {D P : Set Point} {h : ℝ} (hh : 0≤h)
    (hf : ContinuousOn f D) (hP : ∀ p∈P, closedBall p h ⊆ D) :
    ContinuousOn (fun p => radialU f p h) P := by
  rw [continuousOn_iff_continuous_domRestrict]
  let a : P × UnitSphere → Point := fun q => (q.1:Point)+h • (q.2:Point)
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hfa : Continuous (f ∘ a) := hf.comp_continuous ha
    (fun q => hP q.1 q.1.property (sphere_subset_closedBall (unitSphere_param hh q.2)))
  have hfb : Continuous (fun q : P × UnitSphere => f q.1) := hf.comp_continuous
    (continuous_subtype_val.comp continuous_fst) (fun q => hP q.1 q.1.property (mem_closedBall_self hh))
  have ht := isCompact_univ.continuous_sSup
    (f:=fun p : P => fun u : UnitSphere => dist (f ((p:Point)+h • (u:Point))) (f p)) (hfa.dist hfb)
  change Continuous (fun p : P => sSup (range fun u : UnitSphere => dist (f ((p:Point)+h • (u:Point))) (f p)))
  simpa only [image_univ] using ht

lemma continuousOn_radialV {f : Point → Point} {D P : Set Point} {h : ℝ} (hh : 0≤h)
    (hf : ContinuousOn f D) (hP : ∀ p∈P, closedBall p h ⊆ D) :
    ContinuousOn (fun p => radialV f p h) P := by
  rw [continuousOn_iff_continuous_domRestrict]
  let a : P × UnitSphere → Point := fun q => (q.1:Point)+h • (q.2:Point)
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hfa : Continuous (f ∘ a) := hf.comp_continuous ha
    (fun q => hP q.1 q.1.property (sphere_subset_closedBall (unitSphere_param hh q.2)))
  have hfb : Continuous (fun q : P × UnitSphere => f q.1) := hf.comp_continuous
    (continuous_subtype_val.comp continuous_fst) (fun q => hP q.1 q.1.property (mem_closedBall_self hh))
  have ht := isCompact_univ.continuous_sInf
    (f:=fun p : P => fun u : UnitSphere => dist (f ((p:Point)+h • (u:Point))) (f p)) (hfa.dist hfb)
  change Continuous (fun p : P => sInf (range fun u : UnitSphere => dist (f ((p:Point)+h • (u:Point))) (f p)))
  simpa only [image_univ] using ht

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Metric Zoom
open scoped Topology

noncomputable def rankCore (h : ℝ) : Set Point :=
  Icc (2*h) (1-2*h) ×ˢ Icc (-1+2*h) (-2*h)

lemma rankCore_closed (h : ℝ) : IsClosed (rankCore h) := isClosed_Icc.prod isClosed_Icc

lemma rankCore_ball {h : ℝ} (hh : 0<h) {p : Point} (hp : p∈rankCore h) :
    closedBall p h ⊆ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := by
  intro x hx
  rw [mem_closedBall,Prod.dist_eq] at hx
  have hx1 : |x.1-p.1|≤h := (le_max_left _ _).trans hx
  have hx2 : |x.2-p.2|≤h := (le_max_right _ _).trans hx
  rcases abs_le.mp hx1 with ⟨hx11,hx12⟩
  rcases abs_le.mp hx2 with ⟨hx21,hx22⟩
  rcases hp with ⟨⟨hp11,hp12⟩,⟨hp21,hp22⟩⟩
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma rankCore_small {p : Point} (hp : p∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0) :
    ∃ δ>0, ∀ h, h≤δ → p∈rankCore h := by
  let d := min p.1 (min (1-p.1) (min (p.2+1) (-p.2)))
  have hd : 0<d := by dsimp [d]; exact lt_min hp.1.1 (lt_min (by linarith [hp.1.2]) (lt_min (by linarith [hp.2.1]) (by linarith [hp.2.2])))
  have h1 : d≤p.1 := min_le_left _ _
  have h2 : d≤1-p.1 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : d≤p.2+1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : d≤-p.2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨d/4,by positivity,fun h hh => ?_⟩
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma radialCompare_extrema {f : Point → Point} {p : Point} {h C M T : ℝ}
    (hh : 0<h) (hT : 1≤T) (hM : 0<M) (hCM : C≤M)
    (hf : ContinuousOn f (closedBall p h)) (hc : RadialCompare f p h C T) :
    (1/(M*T))*radialU f p h ≤ radialV f p (h/T) ∧
      radialU f p (h/T)≤(M/T)*radialV f p h := by
  have hTp : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hhT : 0<h/T := div_pos hh hTp
  have hsmall : h/T≤h := (div_le_iff₀ hTp).mpr (by nlinarith)
  have hf' := hf.mono (closedBall_subset_closedBall hsmall)
  obtain ⟨u,hu,heu,_⟩ := radialV_attained hhT hf'
  obtain ⟨v,hv,hev,_⟩ := radialU_attained hh hf
  have h1 := hc.1 u v hu hv
  change dist (f v) (f p) ≤ C*T*dist (f u) (f p) at h1
  rw [heu,hev] at h1
  have hlow : 0≤radialV f p (h/T) := (radial_extrema_bounds hhT hf').1
  have h1' : radialU f p h ≤ M*T*radialV f p (h/T) :=
    h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM hTp.le) hlow)
  obtain ⟨u',hu',heu',_⟩ := radialU_attained hhT hf'
  obtain ⟨v',hv',hev',_⟩ := radialV_attained hh hf
  have h2 := hc.2 u' v' hu' hv'
  change T*dist (f u') (f p) ≤ C*dist (f v') (f p) at h2
  rw [heu',hev'] at h2
  have hv0 := (radial_extrema_bounds hh hf).1
  constructor
  · rw [one_div,inv_mul_eq_div]
    exact (div_le_iff₀ (mul_pos hM hTp)).mpr (by nlinarith [h1'])
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hTp).mpr
    have h2' := h2.trans (mul_le_mul_of_nonneg_right hCM hv0)
    convert h2' using 1; ring

def ScaleGood (f : ℕ → Point → Point) (h q α β : ℝ) : Set Point :=
  {p | p∈rankCore h ∧ ∀ j : ℕ, ∀ᶠ n in atTop,
    α*radialU (f n) p (h*q^j)≤radialV (f n) p (h*q^(j+1)) ∧
    radialU (f n) p (h*q^(j+1))≤β*radialV (f n) p (h*q^j)}

lemma scaleGood_measurable (f : ℕ → Point → Point) {h q α β : ℝ}
    (hh : 0<h) (hq : 0≤q) (hq1 : q≤1)
    (hf : ∀ n, ContinuousOn (f n) (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)) :
    MeasurableSet (ScaleGood f h q α β) := by
  let P := rankCore h
  have hcU (n j : ℕ) : Continuous (fun p : P => radialU (f n) p (h*q^j)) := by
    have hc : ContinuousOn (fun p => radialU (f n) p (h*q^j)) P := by
      apply continuousOn_radialU (by positivity) (hf n)
      intro p hp
      exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le (pow_le_one₀ hq hq1))).trans
        (rankCore_ball hh hp)
    exact hc.domRestrict
  have hcV (n j : ℕ) : Continuous (fun p : P => radialV (f n) p (h*q^j)) := by
    have hc : ContinuousOn (fun p => radialV (f n) p (h*q^j)) P := by
      apply continuousOn_radialV (by positivity) (hf n)
      intro p hp
      exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le (pow_le_one₀ hq hq1))).trans
        (rankCore_ball hh hp)
    exact hc.domRestrict
  have hm : MeasurableSet {p : P | ∀ j : ℕ, ∀ᶠ n in atTop,
      α*radialU (f n) p (h*q^j)≤radialV (f n) p (h*q^(j+1)) ∧
      radialU (f n) p (h*q^(j+1))≤β*radialV (f n) p (h*q^j)} := by
    simp only [eventually_atTop]
    rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    rw [ofPred_exists]
    apply MeasurableSet.iUnion
    intro N
    rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    by_cases hn : N≤n
    · simp only [hn,true_implies]
      exact (measurableSet_le ((hcU n j).measurable.const_mul α) (hcV n (j+1)).measurable).inter
        (measurableSet_le (hcU n (j+1)).measurable ((hcV n j).measurable.const_mul β))
    · simp only [hn,false_implies,ofPred_true]; exact MeasurableSet.univ
  have hi := (MeasurableEmbedding.subtype_coe (rankCore_closed h).measurableSet).measurableSet_image.mpr hm
  convert hi using 1
  ext p
  simp only [ScaleGood,mem_ofPred_eq,mem_image,Subtype.exists]
  aesop

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Metric Zoom
open scoped Topology

lemma exists_scaleGood (f : ℕ → Point → Point) {p : Point}
    (hp : p∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hf : ∀ n, ContinuousOn (f n) (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0))
    {C M T : ℝ} (hCM : C≤M) (hM : 0<M) (hT : 1<T)
    (hc : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop, RadialCompare (f n) p h C T) :
    ∃ m : ℕ, p∈ScaleGood f ((1/T)^m) (1/T) (1/(M*T)) (M/T) := by
  obtain ⟨δ,hδ,hδc⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hc
  obtain ⟨d,hd,hcore⟩ := rankCore_small hp
  have hTp : 0<T := lt_trans zero_lt_one hT
  have hq : 0<1/T := div_pos zero_lt_one hTp
  have hq1 : 1/T<1 := (div_lt_one hTp).mpr hT
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1
  obtain ⟨m,hm⟩ := ((tendsto_order.mp hlim).2 (min δ d) (lt_min hδ hd)).exists
  have hmd : (1/T)^m<d := hm.trans_le (min_le_right _ _)
  have hmδ : (1/T)^m<δ := hm.trans_le (min_le_left _ _)
  have hmc := hcore _ hmd.le
  refine ⟨m,hmc,fun j => ?_⟩
  have hr : 0<(1/T)^m*(1/T)^j := mul_pos (pow_pos hq _) (pow_pos hq _)
  have hrm : (1/T)^m*(1/T)^j≤(1/T)^m := mul_le_of_le_one_right
    (pow_nonneg hq.le _) (pow_le_one₀ hq.le hq1.le)
  have hrc := hδc ⟨hr,hrm.trans_lt hmδ⟩
  filter_upwards [hrc] with n hn
  have hball := (closedBall_subset_closedBall hrm (x:=p)).trans
    (rankCore_ball (pow_pos hq _) hmc)
  have hb := radialCompare_extrema hr hT.le hM hCM ((hf n).mono hball) hn
  have he : (1/T)^m*(1/T)^j/T=(1/T)^m*(1/T)^(j+1) := by rw [pow_succ]; ring
  rwa [he] at hb

lemma exists_dyadicExponent_scaleGood (f : ℕ → Point → Point) {p : Point}
    (hp : p∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hf : ∀ n, ContinuousOn (f n) (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0))
    (hc : ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ),
      ∀ᶠ n in atTop, RadialCompare (f n) p h C T) :
    ∃ M m : ℕ, 2≤M ∧ p∈ScaleGood f ((1/(M:ℝ)^16)^m) (1/(M:ℝ)^16)
      (1/((M:ℝ)*(M:ℝ)^16)) ((M:ℝ)/(M:ℝ)^16) := by
  obtain ⟨C,_,hC⟩ := hc
  obtain ⟨N,hN⟩ := exists_nat_gt C
  let M := max N 2
  have hM2 : 2≤M := le_max_right _ _
  have hMp : 0<(M:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) hM2)
  have hM1 : 1<(M:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hM2)
  have hCM : C≤(M:ℝ) := hN.le.trans (by exact_mod_cast le_max_left N 2)
  have hT : 1<(M:ℝ)^16 := one_lt_pow₀ hM1 (by decide)
  obtain ⟨m,hm⟩ := exists_scaleGood f hp hf hCM hMp hT (hC _ hT.le)
  exact ⟨M,m,hM2,hm⟩

lemma positive_scaleGood {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (hE : MeasurableSet E) (hpos : μ E≠0)
    (π : X → Point) (hπ : Measurable π) (f : ℕ → Point → Point)
    (hf : ∀ n, ContinuousOn (f n) (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0))
    (hc : ∀ᵐ x ∂μ.restrict E, π x∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 ∧
      ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ),
        ∀ᶠ n in atTop, RadialCompare (f n) (π x) h C T) :
    ∃ M m : ℕ, 2≤M ∧ MeasurableSet (E∩π ⁻¹' ScaleGood f ((1/(M:ℝ)^16)^m)
      (1/(M:ℝ)^16) (1/((M:ℝ)*(M:ℝ)^16)) ((M:ℝ)/(M:ℝ)^16)) ∧
      μ (E∩π ⁻¹' ScaleGood f ((1/(M:ℝ)^16)^m)
      (1/(M:ℝ)^16) (1/((M:ℝ)*(M:ℝ)^16)) ((M:ℝ)/(M:ℝ)^16))≠0 := by
  let A := fun q : ℕ×ℕ => {x | 2≤q.1 ∧ π x∈ScaleGood f ((1/(q.1:ℝ)^16)^q.2)
      (1/(q.1:ℝ)^16) (1/((q.1:ℝ)*(q.1:ℝ)^16)) ((q.1:ℝ)/(q.1:ℝ)^16)}
  obtain ⟨q,hq⟩ := Limits.positive_countable_selection μ E hE hpos A (by
    filter_upwards [hc] with x hx
    obtain ⟨M,m,hM,hm⟩ := exists_dyadicExponent_scaleGood f hx.1 hf hx.2
    exact ⟨(M,m),hM,hm⟩)
  obtain ⟨x,_,hM,_⟩ := nonempty_of_measure_ne_zero hq
  have hM2 : 2≤q.1 := hM
  have hMp : 0<(q.1:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) hM2)
  have hM1 : 1≤(q.1:ℝ) := by exact_mod_cast (le_trans (by decide : 1≤2) hM2)
  have hT : 1≤(q.1:ℝ)^16 := one_le_pow₀ hM1
  have hTp : 0<(q.1:ℝ)^16 := pow_pos hMp _
  have hm := scaleGood_measurable f (h:=(1/(q.1:ℝ)^16)^q.2)
    (α:=1/((q.1:ℝ)*(q.1:ℝ)^16)) (β:=(q.1:ℝ)/(q.1:ℝ)^16)
    (pow_pos (div_pos zero_lt_one hTp) q.2)
    (div_nonneg zero_le_one hTp.le) ((div_le_one hTp).mpr hT) hf
  refine ⟨q.1,q.2,hM2,hE.inter (hm.preimage hπ),?_⟩
  exact ne_of_gt ((pos_iff_ne_zero.mpr hq).trans_le (measure_mono (by
    intro x hx
    exact ⟨hx.1,hx.2.2⟩)))

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma radius_le_of_ball_subset_closedBall {a b : Point} {r R : ℝ}
    (hr : 0≤r) (hR : 0≤R) (hb : ball a r ⊆ closedBall b R) : r≤R := by
  have hh := diam_mono hb isBounded_closedBall
  rw [diam_ball_eq a hr,diam_closedBall_eq b hR] at hh
  linarith

lemma normalized_local_bounds (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) {p₀ p : Point} {h q : ℝ}
    (hh : 0<h) (hq : 0<q) (hq2 : q≤1/2)
    (hb₀ : closedBall p₀ h ⊆ f.target) (hb : closedBall p h ⊆ f.target)
    (hp : dist p p₀<h/4) (hz : f.symm p₀=0) (hU : radialU f.symm p₀ h=1) :
    ‖f.symm p‖≤1 ∧ radialU f.symm p (h*q)≤2 ∧
      ∀ α : ℝ, 0≤α → α≤radialV f.symm p₀ (h*q) → α≤radialU f.symm p h := by
  have hqh : h*q≤h := mul_le_of_le_one_right hh.le (by linarith)
  have hqhp : 0<h*q := mul_pos hh hq
  have hcont₀ := f.continuousOn_symm.mono hb₀
  have hcont := f.continuousOn_symm.mono hb
  have hcont₁ := hcont.mono (closedBall_subset_closedBall hqh)
  have hcont₀₁ := hcont₀.mono (closedBall_subset_closedBall hqh)
  have hby : closedBall p (h*q) ⊆ closedBall p₀ h := by
    intro x hx
    have ht := dist_triangle x p p₀
    have hx' : dist x p≤h*q := hx
    have hm : h*q≤h/2 := by nlinarith
    change dist x p₀≤h
    linarith
  have hby' : ball p₀ (h*q) ⊆ closedBall p h := by
    intro x hx
    have ht := dist_triangle x p₀ p
    have hx' : dist x p₀<h*q := hx
    rw [dist_comm p₀ p] at ht
    have hm : h*q≤h/2 := by nlinarith
    change dist x p≤h
    linarith
  have hupper : ∀ x∈closedBall p₀ h, ‖f.symm x‖≤1 := by
    have hr := radial_upper_enclosure f hs (hU:=zero_le_one) hb₀ (fun x hx => by
      have hhx := (radial_extrema_bounds hh hcont₀).2.2 x hx
      simpa only [hU] using hhx.2)
    simpa only [hz,dist_zero_right] using hr
  have hnp : ‖f.symm p‖≤1 := hupper p (by change dist p p₀≤h; linarith)
  refine ⟨hnp,?_,?_⟩
  · obtain ⟨x,hx,he,_⟩ := radialU_attained hqhp hcont₁
    have hnx := hupper x (hby (sphere_subset_closedBall hx))
    rw [← he]
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  · intro α hα hαV
    have hinner := radial_inner_enclosure f hs (hb₀ (mem_closedBall_self hh.le))
      hqhp.le (fun x hx => hαV.trans ((radial_extrema_bounds hqhp hcont₀₁).2.2 x hx).1)
    rw [hz] at hinner
    have hu0 := (radial_extrema_bounds hh hcont).1.trans (radial_extrema_bounds hh hcont).2.1
    apply radius_le_of_ball_subset_closedBall hα hu0
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hinner hy
    exact radial_upper_enclosure f hs hu0 hb
      (fun x hx => ((radial_extrema_bounds hh hcont).2.2 x hx).2) x (hby' hx)

lemma scaleGood_iteration (f : ℕ → OpenPartialHomeomorph Point Point)
    (hs : ∀ n, (f n).source=univ)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    {p₀ p : Point} {h q α β : ℝ} (hh : 0<h) (hq : 0<q) (hq2 : q≤1/2)
    (hα : 0≤α) (hβ : 0≤β)
    (h₀ : p₀∈ScaleGood (fun n => (f n).symm) h q α β)
    (hp : p∈ScaleGood (fun n => (f n).symm) h q α β) (hd : dist p p₀<h/4)
    (hz : ∀ n, (f n).symm p₀=0) (hU : ∀ n, radialU (f n).symm p₀ h=1) :
    (∀ n, ‖(f n).symm p‖≤1) ∧ ∀ j : ℕ, ∀ᶠ n in atTop,
      α^(j+2)≤radialV (f n).symm p (h*q^(j+1)) ∧
      radialU (f n).symm p (h*q^(j+1))≤2*β^j := by
  have hb (n : ℕ) : closedBall p h ⊆ (f n).target := by rw [ht n]; exact rankCore_ball hh hp.1
  have hb₀ (n : ℕ) : closedBall p₀ h ⊆ (f n).target := by rw [ht n]; exact rankCore_ball hh h₀.1
  have hlocal := fun n => normalized_local_bounds (f n) (hs n) hh hq hq2 (hb₀ n) (hb n) hd (hz n) (hU n)
  refine ⟨fun n => (hlocal n).1,?_⟩
  have hlow : ∀ᶠ n in atTop, α≤radialU (f n).symm p h := by
    filter_upwards [h₀.2 0] with n hn
    apply (hlocal n).2.2 α hα
    simpa only [Nat.zero_add,pow_zero,pow_one,mul_one,hU n] using hn.1
  intro j
  induction j with
  | zero =>
    filter_upwards [hlow,hp.2 0] with n hn hn'
    constructor
    · have hh' := mul_le_mul_of_nonneg_left hn hα
      simp only [Nat.zero_add,pow_zero,pow_one,mul_one] at hn'
      simpa only [Nat.zero_add,pow_one,pow_two] using hh'.trans hn'.1
    · simpa only [Nat.zero_add,pow_zero,pow_one,mul_one] using (hlocal n).2.1
  | succ j ih =>
    filter_upwards [ih,hp.2 (j+1)] with n hn hn'
    have hjh : h*q^(j+1)≤h := mul_le_of_le_one_right hh.le (pow_le_one₀ hq.le (by linarith))
    have hc := (f n).continuousOn_symm.mono ((closedBall_subset_closedBall hjh).trans (hb n))
    have hvu := (radial_extrema_bounds (mul_pos hh (pow_pos hq _)) hc).2.1
    constructor
    · have he := (mul_le_mul_of_nonneg_left (hn.1.trans hvu) hα).trans hn'.1
      calc
        α^(j.succ+2) = α*α^(j+2) := by
          rw [show j.succ+2=j+2+1 by omega,pow_succ,mul_comm]
        _ ≤ _ := he
    · have he := hn'.2.trans (mul_le_mul_of_nonneg_left (hvu.trans hn.2) hβ)
      calc
        _ ≤ β*(2*β^j) := he
        _ = 2*β^j.succ := by rw [pow_succ]; ring

end PlanarHalving.Spatial

end OAI
