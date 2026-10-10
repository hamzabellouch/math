import OAI.Combinatorics.HalvingLines.SpatialMass

namespace OAI

open Filter Topology

namespace PlanarHalving.Spatial
open Set Filter Metric Zoom
open scoped Topology

lemma radial_extrema_scale {f g : Point → Point} {p : Point} {h c : ℝ}
    (hh : 0<h) (hc : 0≤c)
    (hf : ContinuousOn f (closedBall p h)) (hg : ContinuousOn g (closedBall p h))
    (he : ∀ x∈sphere p h, dist (g x) (g p)=c*dist (f x) (f p)) :
    radialU g p h=c*radialU f p h ∧ radialV g p h=c*radialV f p h := by
  obtain ⟨x,hx,hex,hfx⟩ := radialU_attained hh hf
  obtain ⟨y,hy,hey,hgy⟩ := radialU_attained hh hg
  have hU : radialU g p h=c*radialU f p h := by
    apply le_antisymm
    · rw [← hey,he y hy]
      exact mul_le_mul_of_nonneg_left (hfx y hy) hc
    · rw [← hex,← he x hx]
      exact hgy x hx
  obtain ⟨x,hx,hex,hfx⟩ := radialV_attained hh hf
  obtain ⟨y,hy,hey,hgy⟩ := radialV_attained hh hg
  refine ⟨hU,le_antisymm ?_ ?_⟩
  · rw [← hex,← he x hx]
    exact hgy x hx
  · rw [← hey,he y hy]
    exact mul_le_mul_of_nonneg_left (hfx y hy) hc

noncomputable def normalizeChart (f : OpenPartialHomeomorph Point Point)
    (p : Point) (U : ℝ) (hU : U≠0) : OpenPartialHomeomorph Point Point :=
  (affineHomeomorph (f.symm p) U hU (ContinuousLinearEquiv.refl ℝ Point)).transOpenPartialHomeomorph f

@[simp] lemma normalizeChart_symm (f : OpenPartialHomeomorph Point Point)
    (p : Point) (U : ℝ) (hU : U≠0) (x : Point) :
    (normalizeChart f p U hU).symm x=U⁻¹ • (f.symm x-f.symm p) := rfl

lemma normalizeChart_source (f : OpenPartialHomeomorph Point Point) (hs : f.source=univ)
    (p : Point) (U : ℝ) (hU : U≠0) : (normalizeChart f p U hU).source=univ := by
  ext x
  change (f.symm p+U • x∈f.source) ↔ x∈univ
  rw [hs]; simp

@[simp] lemma normalizeChart_target (f : OpenPartialHomeomorph Point Point)
    (p : Point) (U : ℝ) (hU : U≠0) : (normalizeChart f p U hU).target=f.target := rfl

lemma normalizeChart_radial (f : OpenPartialHomeomorph Point Point)
    (p₀ : Point) {U : ℝ} (hU : 0<U) {p : Point} {h : ℝ} (hh : 0<h)
    (hb : closedBall p h ⊆ f.target) :
    radialU (normalizeChart f p₀ U hU.ne').symm p h=U⁻¹*radialU f.symm p h ∧
    radialV (normalizeChart f p₀ U hU.ne').symm p h=U⁻¹*radialV f.symm p h := by
  apply radial_extrema_scale hh (inv_nonneg.mpr hU.le)
    (f.continuousOn_symm.mono hb) ((normalizeChart f p₀ U hU.ne').continuousOn_symm.mono hb)
  intro x _
  rw [normalizeChart_symm,normalizeChart_symm,dist_eq_norm,← smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hU)]
  congr 1
  rw [dist_eq_norm]
  congr 1
  abel

lemma normalizeChart_scaleGood (f : ℕ → OpenPartialHomeomorph Point Point)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (p₀ : Point) (U : ℕ → ℝ) (hU : ∀ n, 0<U n)
    {p : Point} {h q α β : ℝ} (hh : 0<h) (hq : 0<q) (hq1 : q≤1)
    (hp : p∈ScaleGood (fun n => (f n).symm) h q α β) :
    p∈ScaleGood (fun n => (normalizeChart (f n) p₀ (U n) (hU n).ne').symm) h q α β := by
  refine ⟨hp.1,fun j => ?_⟩
  have hb (n j : ℕ) : closedBall p (h*q^j) ⊆ (f n).target := by
    rw [ht n]
    exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le (pow_le_one₀ hq.le hq1))).trans
      (rankCore_ball hh hp.1)
  filter_upwards [hp.2 j] with n hn
  have he := normalizeChart_radial (f n) p₀ (hU n) (mul_pos hh (pow_pos hq j)) (hb n j)
  have he' := normalizeChart_radial (f n) p₀ (hU n) (mul_pos hh (pow_pos hq (j+1))) (hb n (j+1))
  rw [he.1,he.2,he'.1,he'.2]
  constructor
  · calc
      _ = (U n)⁻¹*(α*radialU (f n).symm p (h*q^j)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn.1 (inv_nonneg.mpr (hU n).le)
  · calc
      _ ≤ (U n)⁻¹*(β*radialV (f n).symm p (h*q^j)) :=
        mul_le_mul_of_nonneg_left hn.2 (inv_nonneg.mpr (hU n).le)
      _ = _ := by ring

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma normalized_spatial_limit (f : ℕ → OpenPartialHomeomorph Point Point)
    (hs : ∀ n, (f n).source=univ)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (G : Set Point) (p₀ : Point) (hp₀ : p₀∈G)
    {h q s β : ℝ} (hh : 0<h) (hq : 0<q) (hq2 : q≤1/2) (hspos : 0<s)
    (hβ : 0≤β) (hβ1 : β<1)
    (hgood : G ⊆ ScaleGood (fun n => (f n).symm) h q (q^s) β)
    (hlocal : ∀ p∈G, dist p p₀<h/4)
    (hz : ∀ n, (f n).symm p₀=0) (hU : ∀ n, radialU (f n).symm p₀ h=1) :
    ∃ (φ : ℕ → ℕ) (l : G → Point), StrictMono φ ∧ (∀ p, ‖l p‖≤1) ∧
      (∀ p : G, ∀ u : ℕ → Point, Tendsto u atTop (𝓝 (p:Point)) →
        Tendsto (fun n => (f (φ n)).symm (u n)) atTop (𝓝 (l p))) ∧
      ∀ p p' : G, (q^s*(q/h)^s)*dist (p:Point) p'^s ≤ dist (l p) (l p') := by
  have hq1 : q<1 := by linarith
  have hiter := fun p hp => scaleGood_iteration f hs ht hh hq hq2
    (Real.rpow_nonneg hq.le s) hβ (hgood hp₀) (hgood hp) (hlocal p hp) hz hU
  have hball (n : ℕ) (p : Point) (hp : p∈G) (j : ℕ) :
      closedBall p (h*q^j) ⊆ (f n).target := by
    rw [ht n]
    exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le (pow_le_one₀ hq.le hq1.le))).trans
      (rankCore_ball hh (hgood hp).1)
  have hcont : ∀ p∈G, ∀ ε>0, ∃ r>0, ∀ᶠ n in atTop, ∀ x,
      dist x p<r → dist ((f n).symm x) ((f n).symm p)≤ε := by
    apply asymptotic_continuity_of_radial (fun n => (f n).symm) G
      (fun j => h*q^(j+1)) (fun j => 2*β^j)
      (fun j => mul_pos hh (pow_pos hq _))
    · simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).const_mul 2
    · intro p hp j
      filter_upwards [(hiter p hp).2 j] with n hn x hx
      have hc := (f n).continuousOn_symm.mono (hball n p hp (j+1))
      have he := radial_extrema_bounds (mul_pos hh (pow_pos hq (j+1))) hc
      apply le_trans (b:=radialU (f n).symm p (h*q^(j+1))) ?_ hn.2
      exact radial_upper_enclosure (f n) (hs n) (he.1.trans he.2.1) (hball n p hp (j+1))
        (fun x hx => (he.2.2 x hx).2) x hx.le
  obtain ⟨φ,l,hφ,hl,hmoving⟩ := subsequence_of_asymptotic_continuity
    (fun n => (f n).symm) G ⟨p₀,hp₀⟩ (closedBall (0:Point) 1) (isCompact_closedBall _ _)
    (fun n p hp => by simpa only [mem_closedBall,dist_zero_right] using (hiter p hp).1 n) hcont
  refine ⟨φ,l,hφ,fun p => by simpa only [mem_closedBall,dist_zero_right] using hl p,hmoving,?_⟩
  apply inverse_holder_of_radial_limits (fun n => (f n).symm) φ hφ G l
    (fun p => hmoving p (fun _ => p) tendsto_const_nhds) hq hq1 hh hspos
  · intro p p'
    have hd := dist_triangle (p:Point) p₀ (p':Point)
    rw [dist_comm p₀ (p':Point)] at hd
    have h1 := hlocal p p.property
    have h2 := hlocal p' p'.property
    linarith
  · intro p j hj
    cases j with
    | zero => omega
    | succ j =>
      filter_upwards [(hiter p p.property).2 j] with n hn p' hdist
      have hc := (f n).continuousOn_symm.mono (hball n p p.property (j+1))
      apply hn.1.trans
      rw [dist_comm ((f n).symm p) ((f n).symm p')]
      apply radial_lower_exterior (f n) (hs n)
        (hball n p p.property 0 (by simpa only [pow_zero,mul_one] using mem_closedBall_self hh.le))
        (mul_nonneg hh.le (pow_nonneg hq.le _))
        (fun x hx => ((radial_extrema_bounds (mul_pos hh (pow_pos hq _)) hc).2.2 x hx).1)
        p' (hball n p' p'.property 0 (by simpa only [pow_zero,mul_one] using mem_closedBall_self hh.le))
      simpa only [dist_comm] using hdist.le

end PlanarHalving.Spatial

namespace PlanarHalving.Limits
open Set Filter MeasureTheory
open scoped ENNReal

lemma exists_bounded_density_piece {X : Type*} [MeasurableSpace X]
    (ν β γ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure γ] [SigmaFinite β]
    (hac : γ ≪ β) (hpos : γ univ≠0) :
    ∃ (m : ℕ) (A : Set X), MeasurableSet A ∧ γ A≠0 ∧ ν.restrict A≤(m:ℝ≥0∞) • β := by
  obtain ⟨S,hS,hνS,hβS⟩ := Measure.mutuallySingular_singularPart ν β
  let A : ℕ → Set X := fun m => S∩{x | ν.rnDeriv β x≤(m:ℝ≥0∞)}
  have hA (m : ℕ) : MeasurableSet (A m) := hS.inter
    (measurableSet_le (Measure.measurable_rnDeriv ν β) measurable_const)
  have hSae : ∀ᵐ x ∂β, x∈S := by exact hβS
  have hcover : ∀ᵐ x ∂γ, ∃ m : ℕ, x∈A m := by
    filter_upwards [hac.ae_le hSae,hac.ae_le (Measure.rnDeriv_lt_top ν β)] with x hx hf
    obtain ⟨m,hm⟩ := exists_nat_gt (ν.rnDeriv β x).toReal
    refine ⟨m,hx,?_⟩
    apply (ENNReal.toReal_le_toReal hf.ne (by simp)).mp
    simpa only [ENNReal.toReal_natCast] using hm.le
  obtain ⟨m,hm⟩ := positive_countable_selection γ univ MeasurableSet.univ hpos A
    (by simpa only [Measure.restrict_univ] using hcover)
  have hm' : γ (A m)≠0 := by simpa only [univ_inter] using hm
  refine ⟨m,A m,hA m,hm',?_⟩
  have hsing : (ν.singularPart β).restrict (A m)=0 := by
    apply Measure.restrict_eq_zero.mpr
    exact measure_mono_null inter_subset_left hνS
  rw [ν.haveLebesgueDecomposition_add β,Measure.restrict_add,hsing,zero_add,
    restrict_withDensity (hA m)]
  have hd : (ν.rnDeriv β)≤ᵐ[β.restrict (A m)] fun _ => (m:ℝ≥0∞) := by
    filter_upwards [ae_restrict_mem (hA m)] with x hx
    exact hx.2
  exact (withDensity_mono hd).trans (by
    rw [withDensity_const]
    apply Measure.le_iff.mpr
    intro B hB
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul' le_rfl (Measure.restrict_le_self B))

lemma positive_bounded_projection {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ θ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure θ]
    (β : Measure Y) [SigmaFinite β] (π : X → Y) (hπ : Measurable π)
    (E : Set X) (hE : MeasurableSet E) (hpos : θ E≠0)
    (hac : (θ.restrict E).map π ≪ β) :
    ∃ (m : ℕ) (G : Set X), MeasurableSet G ∧ G⊆E ∧ θ G≠0 ∧
      (μ.restrict G).map π≤(m:ℝ≥0∞) • β := by
  obtain ⟨m,A,hA,hm,hb⟩ := exists_bounded_density_piece (μ.map π) β ((θ.restrict E).map π) hac (by
    simpa only [Measure.map_apply hπ MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ] using hpos)
  let G := π ⁻¹' A ∩ E
  have hG : MeasurableSet G := (hA.preimage hπ).inter hE
  refine ⟨m,G,hG,inter_subset_right,?_,?_⟩
  · simpa only [Measure.map_apply hπ hA,Measure.restrict_apply (hA.preimage hπ)] using hm
  · apply le_trans (b:= (μ.map π).restrict A) ?_ hb
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.map_apply hπ hB,Measure.restrict_apply (hB.preimage hπ),
      Measure.restrict_apply hB,Measure.map_apply hπ (hB.inter hA)]
    apply measure_mono
    intro x hx
    exact ⟨hx.1,hx.2.1⟩

end PlanarHalving.Limits

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma joint_of_asymptotic_continuity {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) {p : X} {v : Y}
    (hl : Tendsto (fun n => f n p) atTop (𝓝 v))
    (hc : ∀ ε>0, ∃ r>0, ∀ᶠ n in atTop, ∀ x, dist x p<r → dist (f n x) (f n p)≤ε) :
    Tendsto (fun q : ℕ × X => f q.1 q.2) (atTop ×ˢ 𝓝 p) (𝓝 v) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r,hr,hrc⟩ := hc (ε/2) (half_pos hε)
  have hl' := (Metric.tendsto_nhds.mp hl) (ε/2) (half_pos hε)
  have hp : ∀ᶠ x in 𝓝 p, dist x p<r := ball_mem_nhds p hr
  filter_upwards [hrc.prod_inl (𝓝 p),hl'.prod_inl (𝓝 p),hp.prod_inr atTop] with q hq hq' hqp
  have hh := hq q.2 hqp
  have ht := dist_triangle (f q.1 q.2) (f q.1 p) v
  linarith

lemma scaleGood_joint (f : ℕ → OpenPartialHomeomorph Point Point)
    (hs : ∀ n, (f n).source=univ)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    {p₀ p : Point} {h q α β : ℝ} (hh : 0<h) (hq : 0<q) (hq2 : q≤1/2)
    (hα : 0≤α) (hβ : 0≤β) (hβ1 : β<1)
    (h₀ : p₀∈ScaleGood (fun n => (f n).symm) h q α β)
    (hp : p∈ScaleGood (fun n => (f n).symm) h q α β) (hd : dist p p₀<h/4)
    (hz : ∀ n, (f n).symm p₀=0) (hU : ∀ n, radialU (f n).symm p₀ h=1)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (v : Point)
    (hl : Tendsto (fun n => (f (φ n)).symm p) atTop (𝓝 v)) :
    Tendsto (fun z : ℕ × Point => (f (φ z.1)).symm z.2) (atTop ×ˢ 𝓝 p) (𝓝 v) := by
  apply joint_of_asymptotic_continuity _ hl
  have hi := scaleGood_iteration f hs ht hh hq hq2 hα hβ h₀ hp hd hz hU
  have hb (n j : ℕ) : closedBall p (h*q^j) ⊆ (f n).target := by
    rw [ht n]
    exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le
      (pow_le_one₀ hq.le (by linarith)))).trans (rankCore_ball hh hp.1)
  intro ε hε
  have he : Tendsto (fun j : ℕ => 2*β^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).const_mul 2
  obtain ⟨j,hj⟩ := ((tendsto_order.mp he).2 ε hε).exists
  refine ⟨h*q^(j+1),mul_pos hh (pow_pos hq _),?_⟩
  filter_upwards [hφ.tendsto_atTop.eventually (hi.2 j)] with n hn x hx
  have hdisk := radial_upper_enclosure (f (φ n)) (hs (φ n))
    (by positivity : 0≤2*β^j) (hb (φ n) (j+1)) (fun y hy =>
      ((radial_extrema_bounds (mul_pos hh (pow_pos hq _))
        ((f (φ n)).continuousOn_symm.mono (hb (φ n) (j+1)))).2.2 y hy).2.trans hn.2)
  exact (hdisk x hx.le).trans hj.le

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

lemma positive_localization {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (hE : MeasurableSet E) (hpos : μ E≠0)
    (π : X → Point) (hπ : Measurable π) {r : ℝ} (hr : 0<r) :
    ∃ (G : Set X) (x₀ : X), MeasurableSet G ∧ G⊆E ∧ μ G≠0 ∧ x₀∈G ∧
      ∀ x∈G, dist (π x) (π x₀)<r := by
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq Point
  let A : ℕ → Set X := fun j => π ⁻¹' ball (a j) (r/2)
  obtain ⟨j,hj⟩ := Limits.positive_countable_selection μ E hE hpos A (by
    apply Eventually.of_forall
    intro x
    obtain ⟨j,hj⟩ := ha.exists_dist_lt (π x) (half_pos hr)
    exact ⟨j,by simpa only [A,mem_preimage,mem_ball,dist_comm] using hj⟩)
  let G := E∩A j
  obtain ⟨x₀,hx₀⟩ := nonempty_of_measure_ne_zero hj
  refine ⟨G,x₀,hE.inter (measurableSet_ball.preimage hπ),inter_subset_left,hj,hx₀,?_⟩
  intro x hx
  have h1 : dist (π x) (a j)<r/2 := hx.2
  have h2 : dist (π x₀) (a j)<r/2 := hx₀.2
  have ht := dist_triangle (π x) (a j) (π x₀)
  rw [dist_comm (a j) (π x₀)] at ht
  linarith

lemma integer_scale_parameters {M : ℕ} (hM : 2≤M) :
    0<1/(M:ℝ)^16 ∧ 1/(M:ℝ)^16≤1/2 ∧
      0≤(M:ℝ)/(M:ℝ)^16 ∧ (M:ℝ)/(M:ℝ)^16<1 ∧
      (1/(M:ℝ)^16)^((17:ℝ)/16)=1/((M:ℝ)*(M:ℝ)^16) := by
  have hMp : 0<(M:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) hM)
  have hM2 : (2:ℝ)≤M := by exact_mod_cast hM
  have hM1 : 1<(M:ℝ) := by linarith
  have hp : 0<(M:ℝ)^16 := pow_pos hMp _
  have hpow : (M:ℝ)<(M:ℝ)^16 := lt_self_pow₀ hM1 (by decide)
  refine ⟨by positivity,?_,by positivity,(div_lt_one hp).mpr hpow,?_⟩
  · apply (div_le_iff₀ hp).mpr
    linarith
  · calc
      (1/(M:ℝ)^16)^((17:ℝ)/16) = (((M:ℝ)⁻¹)^16)^((17:ℝ)/16) := by rw [inv_pow,one_div]
      _ = ((M:ℝ)⁻¹)^(17:ℝ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (inv_nonneg.mpr hMp.le)]
        norm_num
      _ = 1/((M:ℝ)*(M:ℝ)^16) := by
        rw [show (17:ℝ)=(17:ℕ) by norm_num,Real.rpow_natCast,pow_succ,inv_pow]
        field_simp

lemma positive_spatial_witness {X : Type*} [MeasurableSpace X]
    (μ θ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure θ]
    (E : Set X) (hE : MeasurableSet E) (hpos : θ E≠0)
    (π : X → Point) (hπ : Measurable π)
    (hac : (θ.restrict E).map π ≪ volume)
    (f : ℕ → OpenPartialHomeomorph Point Point)
    (hs : ∀ n, (f n).source=univ)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hc : ∀ᵐ x ∂θ.restrict E, π x∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 ∧
      ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ),
        ∀ᶠ n in atTop, Zoom.RadialCompare (f n).symm (π x) h C T) :
    ∃ (G : Set X), MeasurableSet G ∧ G⊆E ∧ θ G≠0 ∧
      ∃ (m : ℕ), (μ.restrict G).map π≤(m:ℝ≥0∞) • volume ∧
        ∃ (p₀ : Point) (U : ℕ → ℝ) (hU : ∀ n, 0<U n)
          (φ : ℕ → ℕ) (l : (π '' G) → Point) (c : ℝ),
          0<c ∧ StrictMono φ ∧ (∀ p, ‖l p‖≤1) ∧
          (∀ p : (π '' G), Tendsto (fun z : ℕ × Point =>
            (normalizeChart (f (φ z.1)) p₀ (U (φ z.1)) (hU (φ z.1)).ne').symm z.2)
              (atTop ×ˢ 𝓝 (p:Point)) (𝓝 (l p))) ∧
          ∀ p p' : (π '' G), c*dist (p:Point) p'^((17:ℝ)/16)≤dist (l p) (l p') := by
  have hcont (n : ℕ) : ContinuousOn (f n).symm (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0) := by
    rw [← ht n]; exact (f n).continuousOn_symm
  obtain ⟨M,k,hM,hAmeas,hApos⟩ := positive_scaleGood θ E hE hpos π hπ
    (fun n => (f n).symm) hcont hc
  obtain ⟨hq,hq2,hβ,hβ1,hα⟩ := integer_scale_parameters hM
  let q : ℝ := 1/(M:ℝ)^16
  let h : ℝ := q^k
  let β : ℝ := (M:ℝ)/(M:ℝ)^16
  have hh : 0<h := pow_pos hq k
  let A : Set X := E ∩ π ⁻¹' ScaleGood (fun n => (f n).symm) h q (q^((17:ℝ)/16)) β
  have hAm : MeasurableSet A := by simpa only [A,h,q,β,hα] using hAmeas
  have hAp : θ A≠0 := by simpa only [A,h,q,β,hα] using hApos
  have hAE : A⊆E := inter_subset_left
  have hacA : (θ.restrict A).map π ≪ volume := by
    exact (Measure.absolutelyContinuous_of_le (Measure.map_mono (Measure.restrict_mono_set θ hAE) hπ)).trans hac
  obtain ⟨m,B,hBm,hBA,hBp,hBd⟩ := Limits.positive_bounded_projection μ θ volume π hπ A hAm hAp hacA
  obtain ⟨G,x₀,hGm,hGB,hGp,hx₀,hloc⟩ := positive_localization θ B hBm hBp π hπ (by positivity : 0<h/4)
  have hGA : G⊆A := hGB.trans hBA
  have hgood : π '' G ⊆ ScaleGood (fun n => (f n).symm) h q (q^((17:ℝ)/16)) β := by
    rintro p ⟨x,hx,rfl⟩; exact (hGA hx).2
  let p₀ := π x₀
  have hp₀ : p₀∈π '' G := mem_image_of_mem π hx₀
  have hb₀ (n : ℕ) : closedBall p₀ h ⊆ (f n).target := by
    rw [ht n]; exact rankCore_ball hh (hgood hp₀).1
  let U : ℕ → ℝ := fun n => radialU (f n).symm p₀ h
  have hU (n : ℕ) : 0<U n := by
    have hv := radialV_pos hh ((f n).continuousOn_symm.mono (hb₀ n))
      ((f n).symm.injOn.mono (hb₀ n))
    exact hv.trans_le (radial_extrema_bounds hh ((f n).continuousOn_symm.mono (hb₀ n))).2.1
  let g : ℕ → OpenPartialHomeomorph Point Point := fun n => normalizeChart (f n) p₀ (U n) (hU n).ne'
  have hgs (n : ℕ) : (g n).source=univ := normalizeChart_source _ (hs n) _ _ _
  have hgt (n : ℕ) : (g n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := ht n
  have hg : π '' G ⊆ ScaleGood (fun n => (g n).symm) h q (q^((17:ℝ)/16)) β := by
    intro p hp
    exact normalizeChart_scaleGood f ht p₀ U hU hh hq (by linarith) (hgood hp)
  have hz (n : ℕ) : (g n).symm p₀=0 := by simp [g]
  have hgU (n : ℕ) : radialU (g n).symm p₀ h=1 := by
    rw [(normalizeChart_radial (f n) p₀ (hU n) hh (hb₀ n)).1]
    exact inv_mul_cancel₀ (hU n).ne'
  obtain ⟨φ,l,hφ,hl,hmov,hsep⟩ := normalized_spatial_limit g hgs hgt (π '' G) p₀ hp₀
    hh hq hq2 (by norm_num : (0:ℝ)<17/16) hβ hβ1 hg
    (by rintro p ⟨x,hx,rfl⟩; exact hloc x hx) hz hgU
  refine ⟨G,hGm,hGA.trans hAE,hGp,m,?_,p₀,U,hU,φ,l,q^((17:ℝ)/16)*(q/h)^((17:ℝ)/16),
    by positivity,hφ,hl,?_,hsep⟩
  · exact (Measure.map_mono (Measure.restrict_mono_set μ hGB) hπ).trans hBd
  · intro p
    apply scaleGood_joint g hgs hgt hh hq hq2 (by positivity) hβ hβ1
      (hg hp₀) (hg p.property) _ hz hgU φ hφ (l p)
    · exact hmov p (fun _ => (p:Point)) tendsto_const_nhds
    · obtain ⟨x,hx,he⟩ := p.property
      rw [← he]; exact hloc x hx

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal unitInterval

abbrev Cube := I × I
noncomputable def encode (p : Point) : Cube := (unitInterval.sigmoid p.1,unitInterval.sigmoid p.2)
noncomputable def decode (p : Cube) : Point :=
  (-Real.log ((p.1:ℝ)⁻¹-1),-Real.log ((p.2:ℝ)⁻¹-1))

lemma continuous_encode : Continuous encode := by
  exact (unitInterval.continuous_sigmoid.comp continuous_fst).prodMk
    (unitInterval.continuous_sigmoid.comp continuous_snd)

lemma measurable_decode : Measurable decode := by
  exact ((Real.measurable_log.comp ((measurable_subtype_coe.comp measurable_fst).inv.sub measurable_const)).neg).prodMk
    ((Real.measurable_log.comp ((measurable_subtype_coe.comp measurable_snd).inv.sub measurable_const)).neg)

@[simp] lemma decode_encode (p : Point) : decode (encode p)=p := by
  have hn (t : ℝ) : -Real.log ((unitInterval.sigmoid t:ℝ)⁻¹-1)=t := by
    change -Real.log (((1+Real.exp (-t))⁻¹)⁻¹-1)=t
    simp
  exact Prod.ext (hn p.1) (hn p.2)

lemma encode_injective : Function.Injective encode := by
  intro p q he
  simpa only [decode_encode] using congrArg decode he

lemma support_spatial_graph {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μs : ℕ → FiniteMeasure (X × Cube)} {μ : FiniteMeasure (X × Cube)}
    (hμ : Tendsto μs atTop (𝓝 μ)) (π : X → Point) (hπ : Continuous π)
    (f : ℕ → Point → Point)
    (hid : ∀ᶠ n in atTop, ∀ᵐ z ∂(μs n : Measure (X × Cube)), z.2=encode (f n (π z.1)))
    (G : Set X) (l : (π '' G) → Point)
    (hjoint : ∀ p : (π '' G), Tendsto (fun q : ℕ × Point => f q.1 q.2)
      (atTop ×ˢ 𝓝 (p:Point)) (𝓝 (l p)))
    {z : X × Cube} (hz : z∈(μ : Measure (X × Cube)).support) (hG : z.1∈G) :
    z.2=encode (l ⟨π z.1,mem_image_of_mem π hG⟩) := by
  exact Limits.support_coordinate_identity hμ (fun z => π z.1) (hπ.comp continuous_fst)
    Prod.snd continuous_snd (fun n p => encode (f n p)) hid hz
    ((continuous_encode.tendsto _).comp (hjoint ⟨π z.1,mem_image_of_mem π hG⟩))

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped ENNReal

lemma volume_closedBall_point (p : Point) {r : ℝ} (hr : 0≤r) :
    volume (closedBall p r)=ENNReal.ofReal (4*r^2) := by
  rw [← closedBall_prod_same]
  change (volume.prod volume) (closedBall p.1 r ×ˢ closedBall p.2 r)=_
  rw [Measure.prod_prod,Real.volume_closedBall,Real.volume_closedBall,← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma disk_bound_of_inverse_holder {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : Set X) (hG : MeasurableSet G)
    (π ψ : X → Point) (hπ : Measurable π) (hψ : Measurable ψ)
    {M : ℝ≥0∞} {c s : ℝ} (hc : 0<c) (hs : 0<s)
    (hdensity : (μ.restrict G).map π≤M • volume)
    (hsep : ∀ x∈G, ∀ y∈G, c*dist (π x) (π y)^s≤dist (ψ x) (ψ y))
    (x : Point) {r : ℝ} (hr : 0<r) :
    (μ.restrict G).map ψ (closedBall x r) ≤
      M*ENNReal.ofReal (4*(2/c)^(2/s))*ENNReal.ofReal (r^(2/s)) := by
  let A := ψ ⁻¹' closedBall x r ∩ G
  have hA : MeasurableSet A := (measurableSet_closedBall.preimage hψ).inter hG
  rw [Measure.map_apply hψ measurableSet_closedBall,Measure.restrict_apply (measurableSet_closedBall.preimage hψ)]
  change μ A≤_
  by_cases hzero : μ A=0
  · rw [hzero]; exact zero_le
  obtain ⟨a,ha⟩ := nonempty_of_measure_ne_zero hzero
  let R : ℝ := (2*r/c)^(s⁻¹)
  have hR : 0≤R := Real.rpow_nonneg (by positivity) _
  have hsub : A ⊆ π ⁻¹' closedBall (π a) R ∩ G := by
    intro b hb
    refine ⟨?_,hb.2⟩
    change dist (π b) (π a)≤(2*r/c)^(s⁻¹)
    apply (Real.le_rpow_inv_iff_of_pos dist_nonneg (by positivity) hs).mpr
    apply (le_div_iff₀ hc).mpr
    have he := hsep b hb.2 a ha.2
    have ht := dist_triangle (ψ b) x (ψ a)
    have hb' : dist (ψ b) x≤r := hb.1
    have ha' : dist (ψ a) x≤r := ha.1
    rw [dist_comm x (ψ a)] at ht
    linarith
  calc
    μ A ≤ μ (π ⁻¹' closedBall (π a) R ∩ G) := measure_mono hsub
    _ = (μ.restrict G).map π (closedBall (π a) R) := by
      rw [Measure.map_apply hπ measurableSet_closedBall,Measure.restrict_apply (measurableSet_closedBall.preimage hπ)]
    _ ≤ (M • volume) (closedBall (π a) R) := hdensity _
    _ = M*ENNReal.ofReal (4*R^2) := by rw [Measure.smul_apply,smul_eq_mul,volume_closedBall_point _ hR]
    _ = M*ENNReal.ofReal (4*(2/c)^(2/s))*ENNReal.ofReal (r^(2/s)) := by
      have hpow : R^2=(2/c)^(2/s)*r^(2/s) := by
        dsimp [R]
        rw [← Real.rpow_mul_natCast (by positivity : 0≤2*r/c)]
        rw [show s⁻¹*(2:ℕ)=2/s by simp only [Nat.cast_ofNat]; ring]
        rw [show 2*r/c=(2/c)*r by ring,Real.mul_rpow (by positivity) hr.le]
      rw [hpow,← mul_assoc (4:ℝ),ENNReal.ofReal_mul (by positivity),mul_assoc]

end PlanarHalving.Spatial

end OAI
