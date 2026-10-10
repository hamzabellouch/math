import Mathlib
import OAI.Geometry.CubicTorus.Estimates.SliceJensenWeight

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_one_vertex_position {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<N x i)
    (hv : ∀ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    ∃ X : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) X ∧
      (∀ m x,X (x+latticeVector m)=X x) ∧
      ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        fderiv ℝ X x=ContinuousLinearMap.id ℝ Cover ∧ 0<⟪N x,X x⟫ := by
  have hsgc : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i := by
    intro x hx i
    exact (hsg x i ⟨hx.1,mem_iInter.mp hx.2 i⟩).le
  have hgap := fun i => isMinimizerAt_chamber_face_gap hV hE hm hμ ha hsgc hs i (hv i)
  choose d hd hgap using hgap
  let δ := min (1/4 : ℝ) (min (d 0) (min (d 1) (d 2)))
  have hδ : 0<δ := lt_min (by norm_num) (lt_min (hd 0) (lt_min (hd 1) (hd 2)))
  have hδq : δ≤1/4 := min_le_left _ _
  have hδd : ∀ i : Fin 3,δ≤d i := by
    intro i
    fin_cases i
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let r := 1/2-δ/2
  have hr : 0<r := by dsimp [r]; linarith
  have hr' : r<1/2 := by dsimp [r]; linarith
  obtain ⟨X,hX,hXp,hXe⟩ := exists_periodic_position_box (chamberCorner s) hr hr'
  have hsF := fun i => openRepresentative_reflection_invariant hE i (hs i)
  have hcorner := (isMinimizerAt_chamber_vertex_order hV hE hm hμ ha hsgc hs).1
  rw [chamberVertex_bottom] at hcorner
  refine ⟨X,hX,hXp,?_⟩
  intro x hx
  let a := quotientMap x
  let y := shortestLift (a-quotientMap (chamberCorner s))+chamberCorner s
  have hyq : quotientMap y=quotientMap x := by
    change quotientMap (shortestLift (a-quotientMap (chamberCorner s))+chamberCorner s)=a
    rw [quotientMap_add,quotientMap_shortestLift,sub_add_cancel]
  have hyb : ∀ i : Fin 3,|y i-chamberCorner s i|≤r := by
    intro i
    have hclosed : quotientMap (chamberFoldLift s a)∈closure (openRepresentative E) :=
      (chamberFoldLift_mem_iff (reflection_invariant_closure hsF) s a).mpr (frontier_subset_closure hx)
    have hgi := hgap i (chamberFoldLift s a) (chamberFoldLift_mem s a) hclosed
    rw [chamberFoldLift_apply] at hgi
    change |shortestLift (a-quotientMap (chamberCorner s)) i+chamberCorner s i-chamberCorner s i|≤r
    simp only [add_sub_cancel_right]
    dsimp [r]
    linarith [hδd i]
  have hyS : quotientMap y∈frontier (openRepresentative E) := by rwa [hyq]
  have hyne : y≠chamberCorner s := by
    intro he
    rw [he,frontier,(isOpen_openRepresentative E).interior_eq] at hyS
    exact hyS.2 hcorner
  have hnxy : N x=N y := by
    rw [← periodic_representative hp x,← periodic_representative hp y,hyq]
  have hXxy : X x=X y := by
    rw [← periodic_representative hXp x,← periodic_representative hXp y,hyq]
  have hDxy : fderiv ℝ X x=fderiv ℝ X y := by
    rw [← periodic_representative (fderiv_periodic hXp) x,
      ← periodic_representative (fderiv_periodic hXp) y,hyq]
  have he := hXe y hyb
  constructor
  · rw [hDxy,he.fderiv_eq]
    exact ((hasFDerivAt_id y).sub_const (chamberCorner s)).fderiv
  · rw [hnxy,hXxy,he.eq_of_nhds]
    exact isMinimizerAt_chamber_support_positive hV hE hm hμ hN hp ha hs hsg hyS
      (fun i => (hyb i).trans_lt hr') hyne

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_full_jacobi_system {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      (∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
        (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0) := by
  obtain ⟨μ,H,hμ,hCMC,hs⟩ := isMinimizerAt_boundary_stability hV hE hm
  obtain ⟨N,hN,hp,hn⟩ := isMinimizerAt_global_normal hV hE hm hμ
  have hdiv := weakCMC_normal_extension hCMC hN hp hn
  let R := regularizedNormal N
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := regularizedNormal_contDiff hN
  have hRp : ∀ m x,R (x+latticeVector m)=R x := regularizedNormal_periodic hp
  have he : ∀ᵐ z ∂(μ : Measure NormalBundle),R=ᶠ[𝓝 (z.1 : Cover)]N :=
    hn.mono fun z hz => regularizedNormal_eventuallyEq hz.2
  have hRa : ∀ᵐ z ∂(μ : Measure NormalBundle),R z.1=(z.2 : Cover) := by
    filter_upwards [hn,he] with z hz hez
    exact hez.eq_of_nhds.trans hz.1
  have hRu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖R y‖=1 := by
    intro x hx
    have hnorm : ‖N x‖=1 := by
      apply isMinimizerAt_periodic_ae_eq_boundary hV hE hm hμ hN.continuous.norm continuous_const
        (fun m x => by rw [hp]) (fun _ _ => rfl) _ x hx
      filter_upwards [hn] with z hz
      rw [hz.1,z.2.property]
    exact regularizedNormal_unit_near hN.continuous (by rw [hnorm]; norm_num)
  have hRd : ∀ᵐ z ∂(μ : Measure NormalBundle),divergence R z.1=H := by
    filter_upwards [he,hdiv] with z hz hdz
    simpa only [divergence_eq_coverTrace,hz.fderiv_eq] using hdz
  have hRd' : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → divergence R x=H :=
    isMinimizerAt_periodic_ae_eq_boundary hV hE hm hμ (continuous_divergence hR) continuous_const
      (divergence_periodic hRp) (fun _ _ => rfl) hRd
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hstab : ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ m x,f (x+latticeVector m)=f x) →
      (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 → 0≤normalExtensionJacobi μ f R := by
    intro f hf hfp hz
    have hgeom : ∀ᵐ z ∂(μ : Measure NormalBundle),z.1∈tsupport f →
        R z.1=(z.2 : Cover) ∧ (∀ᶠ y in 𝓝 (z.1 : Cover),‖R y‖=1) ∧ divergence R z.1=H := by
      filter_upwards [hRa,hbd,hRd] with z ha hb hd
      exact fun _ => ⟨ha,hRu z.1 hb,hd⟩
    rw [← boundaryQuadratic_eq_normalExtension hf hR hgeom]
    apply hs (fun y => f y • R y) (hf.smul hR)
    · intro m x
      simp only [hfp,hRp]
    · rw [← hz]
      apply integral_congr_ae
      filter_upwards [hRa] with z ha
      rw [ha,real_inner_smul_right,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
  have hmass : (μ : Measure NormalBundle).real univ≠0 := by
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)≠0
    rw [hμ.1]
    exact (ENNReal.toReal_pos (perimeter_pos_of_volume hV hm.1.1 hm.2.1).ne' hm.1.2.ne).ne'
  have hH1 : ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
      0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ R hR) u u :=
    fun u hu hz => surfaceH1_stability_of_smooth μ hmass R hR hstab hu hz
  exact ⟨μ,H,R,hR,hRp,hμ,hRa,fun x hx => ⟨hRu x hx,hRd' x hx⟩,hCMC,hH1,
    fun i => normalComponentScalar_global_jacobi hV hE hm hμ hR hRp hRa hRu hH1 i⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tangentialDivergence_id_derivative {X : Cover → Cover} {x n : Cover}
    (hd : fderiv ℝ X x=ContinuousLinearMap.id ℝ Cover) (hn : ‖n‖=1) :
    tangentialDivergence X x n=2 := by
  simp only [tangentialDivergence,divergence_eq_coverTrace,hd,coverTrace,
    ContinuousLinearMap.id_apply,PiLp.single_apply,ite_true,
    Finset.sum_const,Finset.card_fin,real_inner_self_eq_norm_sq,hn,one_pow]
  norm_num

lemma tangentialDivergence_unit_normal {N : Cover → Cover} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hu : ∀ᶠ y in 𝓝 x,‖N y‖=1) :
    tangentialDivergence N x (N x)=divergence N x := by
  have hz := smooth_unit_normal_derivative hN hu
  rw [tangentialDivergence,← ContinuousLinearMap.adjoint_inner_left,hz,inner_zero_left,sub_zero]

theorem isMinimizerAt_positive_position_spherical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hpN : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hpN i)) w=0)
    {X : Cover → Cover} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hpX : ∀ m x,X (x+latticeVector m)=X x)
    (hDX : ∀ᵐ z ∂(μ : Measure NormalBundle),fderiv ℝ X z.1=ContinuousLinearMap.id ℝ Cover)
    (hpos : ∀ᵐ z ∂(μ : Measure NormalBundle),0<⟪N z.1,X z.1⟫) :
    ∃ (c : Cover) (r : ℝ),0<r ∧ r<1/2 ∧
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c r := by
  let q : NormalBundle → ℝ := fun z => coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
  let u : NormalBundle → ℝ := fun z => ⟪N z.1,X z.1⟫
  let A := (μ : Measure NormalBundle).real univ
  have hqc : Continuous q := (normal_curvature_continuous hN).comp normalEmbedding_continuous.fst
  have huc : Continuous u := (hN.continuous.comp normalEmbedding_continuous.fst).inner (𝕜 := ℝ)
    (hX.continuous.comp normalEmbedding_continuous.fst)
  have hqi := hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace q) (μ := (μ : Measure NormalBundle))
  have hui := huc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace u) (μ := (μ : Measure NormalBundle))
  have hqui := (hqc.mul huc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure NormalBundle))
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hdiv : ∀ᵐ z ∂(μ : Measure NormalBundle),divergence N z.1=H :=
    hbd.mono fun z hz => (hb z.1 hz).2
  have hunit : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) := by
    filter_upwards [ha,hbd] with z haz hbz
    exact ⟨haz,(hb z.1 hbz).1⟩
  have htN : ∀ᵐ z ∂(μ : Measure NormalBundle),tangentialDivergence N z.1 z.2=H := by
    filter_upwards [hunit,hdiv] with z hz hdz
    rw [← hz.1,tangentialDivergence_unit_normal (hN.differentiable (by simp) _) hz.2,hdz]
  have hQ : (∫ z,q z*u z ∂(μ : Measure NormalBundle))=H*A := by
    rw [translation_jacobi_position_identity hN hX hpN hpX hj hDX,integral_congr_ae htN,
      integral_const,smul_eq_mul,mul_comm]
  have hM : H*(∫ z,u z ∂(μ : Measure NormalBundle))=2*A := by
    have hh := hCMC X hX hpX
    have hleft : (∫ z,tangentialDivergence X z.1 z.2 ∂(μ : Measure NormalBundle))=2*A := by
      calc
        _ = ∫ _ : NormalBundle,(2 : ℝ) ∂(μ : Measure NormalBundle) := integral_congr_ae
          (hDX.mono fun z hz => tangentialDivergence_id_derivative hz z.2.property)
        _ = _ := by rw [integral_const,smul_eq_mul,mul_comm]
    rw [hleft] at hh
    rw [hh]
    congr 1
    apply integral_congr_ae
    filter_upwards [ha] with z hz
    exact congrArg (fun n : Cover => ⟪n,X z.1⟫) hz
  have hA : 0<A := by
    change 0<(μ : Measure NormalBundle).real univ
    rw [Measure.real,← FiniteMeasure.ennreal_mass]
    change 0<(μ.mass : ℝ)
    rw [hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hm.1.1 hm.2.1).ne' hm.1.2.ne
  have hH : H≠0 := by intro hz; rw [hz,zero_mul] at hM; linarith
  have hbound : ∀ᵐ z ∂(μ : Measure NormalBundle),0≤2*q z-H^2 := by
    filter_upwards [hbd,hunit,hdiv] with z hbz huz hdz
    have hh := isMinimizerAt_mean_curvature_bound hV hE hm hμ hN hpN ha z.1 hbz huz.2
    rw [hdz] at hh
    exact sub_nonneg.mpr hh
  have hip : Integrable (fun z => (2*q z-H^2)*u z) (μ : Measure NormalBundle) :=
    (((continuous_const.mul hqc).sub continuous_const).mul huc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hzero : (∫ z,(2*q z-H^2)*u z ∂(μ : Measure NormalBundle))=0 := by
    simp_rw [sub_mul,mul_assoc]
    have hiq : Integrable (fun z => 2*(q z*u z)) (μ : Measure NormalBundle) := hqui.const_mul 2
    have hiu : Integrable (fun z => H^2*u z) (μ : Measure NormalBundle) := hui.const_mul _
    rw [integral_sub hiq hiu,integral_const_mul,integral_const_mul,hQ]
    nlinarith [congrArg (fun t : ℝ => H*t) hM]
  have hzp := (integral_eq_zero_iff_of_nonneg_ae (by
    filter_upwards [hbound,hpos] with z hz hpz
    exact mul_nonneg hz hpz.le) hip).mp hzero
  have hqeq : ∀ᵐ z ∂(μ : Measure NormalBundle),q z=H^2/2 := by
    filter_upwards [hzp,hpos] with z hz hpz
    have he := (mul_eq_zero.mp hz).resolve_right hpz.ne'
    linarith
  have hint : (∫ z,q z ∂(μ : Measure NormalBundle))=H^2*isoperimetricProfile V := by
    rw [integral_congr_ae hqeq,integral_const,smul_eq_mul]
    have hmA : A=2*isoperimetricProfile V := by
      change (μ : Measure NormalBundle).real univ=_
      rw [Measure.real,← FiniteMeasure.ennreal_mass]
      change (μ.mass : ℝ)=_
      rw [hμ.1,isoperimetricProfile_eq_of_isMinimizerAt hm]
      ring
    change A*(H^2/2)=_
    rw [hmA]; ring
  obtain ⟨hr,hr',c,hc'⟩ := isMinimizerAt_mean_square_equality_spherical hV hE hm hc hμ hN hpN
    hunit hH hdiv hint
  exact ⟨c,|2/H|,hr,hr',hc'⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_one_vertex_spherical {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<N x i)
    (hv : ∀ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    ∃ (c : Cover) (r : ℝ),0<r ∧ r<1/2 ∧
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c r := by
  obtain ⟨ν,H,M,hM,hpM,hν,haM,hb,hCMC,_,hj⟩ :=
    Periodic.isMinimizerAt_full_jacobi_system hV hE hm
  have he : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → N x=M x := by
    intro x hx
    exact isMinimizerAt_normal_local_ae_eq hV hV hE hE hm hm isOpen_univ (Filter.EventuallyEq.rfl)
      hμ hν hN hM hp hpM ha haM x ⟨hx,mem_univ _⟩
  have hsgM : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<M x i := by
    intro x i hx
    rw [← he x hx.1]
    exact hsg x i hx
  obtain ⟨X,hX,hpX,hXb⟩ := isMinimizerAt_one_vertex_position hV hE hm hν hM hpM haM hs hsgM hv
  have hνU := hν.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hνU
  exact isMinimizerAt_positive_position_spherical hV hE hm hc hν hM hpM haM hb hCMC hj hX hpX
    (hbd.mono fun z hz => (hXb z.1 hz).1) (hbd.mono fun z hz => (hXb z.1 hz).2)

theorem isMinimizerAt_one_vertex_standard_ball {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →
        0<N x i)
    (hv : ∀ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    V≤4*Real.pi/81 ∧ CongruentAE E (canonicalBall V) := by
  obtain ⟨c,r,hr,hr',hbd⟩ := isMinimizerAt_one_vertex_spherical
    ⟨hV.1,by linarith [hV.2]⟩ hE hm hc hμ hN hp ha hs hsg hv
  exact isMinimizerAt_spherical_standard_ball hV hE hm hr hr' hbd

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_coordinate_multiplier {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ H : ℝ,∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function := by
  obtain ⟨i,f,hf,hp,hflux⟩ := exists_positive_directionalFlux
    (perimeter_pos_of_volume hV hm.1.1 hm.2.1)
  obtain ⟨D,hi,hfD⟩ := Periodic.exists_variation_of_function i hf hp
  have hD : directionalFlux E D.coordinate D.function≠0 := by
    rw [hi,hfD]; exact hflux.ne'
  exact Periodic.isMinimizerAt_exists_coordinate_multiplier hm hE hμ D hD

theorem isMinimizerAt_nonstandard_section_system {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmE : IsMinimizerAt V E) (hnstd : ¬SmallStandardRegion V E) :
    ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x)
      (s : Fin 3 → Bool) (H : ℝ),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧ IsNormalMeasure F μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ i : Fin 3,coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ (x : Cover) (i : Fin 3),
        quotientMap x∈frontier (openRepresentative F)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i) ∧
      (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
        H*directionalFlux F D.coordinate D.function) ∧
      (0<(μ.mass : ℝ)) ∧ (∑ i : Fin 3,axialFluxWeight μ i)=2 ∧
      (∀ i : Fin 3,0≤axialFluxWeight μ i ∧ axialFluxWeight μ i<1) ∧
      (∃ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∈closure (openRepresentative F)) ∧
      (∀ i : Fin 3,Continuous (axialSectionArea (openRepresentative F) i) ∧
        AntitoneOn (axialSectionArea (openRepresentative F) i)
          (Icc (chamberCorner s i) (chamberCorner s i+1/2))) ∧
      (∀ i : Fin 3,
        2*(axialSectionArea (openRepresentative F) i (chamberCorner s i)-
          axialSectionArea (openRepresentative F) i (chamberCorner s i+1/2))≤
          (μ.mass : ℝ)*Real.sqrt (1-axialFluxWeight μ i)) ∧
      (∀ (i : Fin 3) (a : Bool),
        axialSlicePerimeter (openRepresentative F) i (if a then 1/2 else 0)=
          ENNReal.ofReal ((μ.mass : ℝ)*axialFluxWeight μ i+
            H*(axialSectionArea (openRepresentative F) i (if a then 1/2 else 0)-V))) := by
  classical
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  obtain ⟨b,F,μ,N,hN,hp,hF,he,hmF,hc,hμ,ha,hs,_,hsg⟩ :=
    (isMinimizerAt_standard_or_strict_reflection hV hmE).resolve_left hnstd
  obtain ⟨s,hsg'⟩ := isMinimizerAt_exists_positive_sides hV' hF hmF hμ hN hp ha hs hsg
  obtain ⟨H,hH⟩ := isMinimizerAt_coordinate_multiplier hV' hF hmF hμ
  have hmass : 0<(μ.mass : ℝ) := by
    rw [hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV' hmF.1.1 hmF.2.1).ne' hmF.1.2.ne
  have hzero : ∀ i : Fin 3,∃ a∈frontier (openRepresentative F),N (representative a) i≠0 := by
    intro i
    by_contra hn
    push Not at hn
    obtain ⟨c,r,hr0,hr,hbd⟩ := isMinimizerAt_zero_coordinate_cylindrical hV' hF hmF hc hμ hN hp ha i hn
    obtain ⟨hl,hu,hcong⟩ := isMinimizerAt_cylindrical_standard_tube hV hF hmF i hr0 hr hbd
    exact hnstd (Or.inr (Or.inl ⟨hl,hu,congruentAE_of_translated he hcong⟩))
  have hv : ∃ i : Fin 3,quotientMap (chamberVertex s (fun j => decide (j=i)))∈closure (openRepresentative F) := by
    by_contra hn
    push Not at hn
    obtain ⟨hsmall,hcong⟩ := isMinimizerAt_one_vertex_standard_ball hV hF hmF hc hμ hN hp ha hs hsg' hn
    exact hnstd (Or.inl ⟨hsmall,congruentAE_of_translated he hcong⟩)
  refine ⟨b,F,μ,N,hN,hp,s,H,hF,he,hmF,hc,hμ,ha,hs,hsg',hH,hmass,
    sum_axialFluxWeight μ hmass.ne',?_,hv,?_,?_,?_⟩
  · intro i
    exact ⟨axialFluxWeight_nonneg μ i,
      (axialFluxWeight_lt_one_iff hV' hF hmF hμ hN.continuous hp ha hmass i).mpr (hzero i)⟩
  · intro i
    exact ⟨isMinimizerAt_continuous_axial_sections hV' hF hmF hμ hN hp ha hs hsg' i,
      isMinimizerAt_antitoneOn_axialSectionArea hV' hF hmF hμ hN hp ha hs hsg' i⟩
  · intro i
    rw [← isMinimizerAt_axial_endFlux hV' hF hmF hμ hN hp ha hs hsg' hH i]
    exact axialProjection_bound μ i
  · exact isMinimizerAt_axial_endpoint_perimeter hV' hF hmF hμ hN hp ha hs hsg' hH

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_axial_bv_coarea {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) :
    Measurable (axialCirclePerimeter (openRepresentative E) i) ∧
    (∀ᵐ t,axialCirclePerimeter (openRepresentative E) i t≠∞) ∧
    Integrable (fun t => (axialCirclePerimeter (openRepresentative E) i t).toReal) ∧
    ∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f →
      (∫ t,(axialCirclePerimeter (openRepresentative E) i t).toReal*f t)=
        ∫ z,axialTangentialSpeed i z*f (axialBundleHeight i z) ∂(μ : Measure NormalBundle) := by
  obtain ⟨H,hH⟩ := isMinimizerAt_coordinate_multiplier hV hE hm hμ
  exact axial_bv_coarea (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm) hN hp ha i
    (isMinimizerAt_axial_boundary_null hV hE hm hμ hN hp ha hs hsg i)
    (isMinimizerAt_axialHeight_absolutelyContinuous hV hE hm hμ hN hp ha hs hsg hH i)

theorem isMinimizerAt_nonstandard_actual_coarea {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmE : IsMinimizerAt V E) (hnstd : ¬SmallStandardRegion V E) :
    ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧ IsNormalMeasure F μ ∧
      ∀ i : Fin 3,Measurable (axialCirclePerimeter (openRepresentative F) i) ∧
        (∀ᵐ t,axialCirclePerimeter (openRepresentative F) i t≠∞) ∧
        Integrable (fun t => (axialCirclePerimeter (openRepresentative F) i t).toReal) ∧
        ∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f →
          (∫ t,(axialCirclePerimeter (openRepresentative F) i t).toReal*f t)=
            ∫ z,axialTangentialSpeed i z*f (axialBundleHeight i z) ∂(μ : Measure NormalBundle) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  obtain ⟨b,F,μ,N,hN,hp,s,H,hF,he,hmF,hc,hμ,ha,hs,hsg,rest⟩ :=
    isMinimizerAt_nonstandard_section_system hV hmE hnstd
  refine ⟨b,F,μ,hF,he,hmF,hc,hμ,?_⟩
  intro i
  exact isMinimizerAt_axial_bv_coarea hV' hF hmF hμ hN hp ha hs hsg i

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_integrated_jensen {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    let J : ℝ → ℝ := fun t => sliceJensenG (axialJensenFlux (openRepresentative E) μ H V i t/
        (axialCirclePerimeter (openRepresentative E) i t).toReal)
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      0≤-deriv (axialSectionArea (openRepresentative E) i) t*chamberHeightSign (s i) t) ∧
    IntervalIntegrable (fun t => J t*(-deriv (axialSectionArea (openRepresentative E) i) t*
      chamberHeightSign (s i) t)) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1,J t*(-deriv (axialSectionArea (openRepresentative E) i) t*
      chamberHeightSign (s i) t))≤
      (μ.mass : ℝ)-(49/50 : ℝ)*(μ.mass : ℝ)*axialFluxWeight μ i := by
  dsimp only
  have hae := isMinimizerAt_openRepresentative_ae hV hE hm
  have hμo := hμ.congr_ae hae.symm
  have hvol : torusVolume.real (openRepresentative E)=V := by
    rw [Measure.real,measure_congr hae,hm.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hHo : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux (openRepresentative E) D.coordinate D.function := by
    intro D
    rw [directionalFlux_congr_ae hae,hH]
  have hc := isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i
  have hac := isMinimizerAt_axialHeight_absolutelyContinuous hV hE hm hμ hN hp ha hs hsg hH i
  obtain ⟨r,hr,hr0,hrm,hJi,hJ⟩ := axial_integrated_jensen
    (isOpen_openRepresentative E).measurableSet hvol hμo hHo hN hp ha i hc
    (isMinimizerAt_axial_boundary_null hV hE hm hμ hN hp ha hs hsg i) hac
  obtain ⟨g,hg,hgm,hgd⟩ := axial_section_derivative_density
    (isOpen_openRepresentative E).measurableSet hμo i hac hc
  have hfront := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμo
  have hsign : ∀ᵐ z ∂(μ : Measure NormalBundle),
      ((z.2 : Cover) i)*chamberHeightSign (s i) (axialBundleHeight i z)=|((z.2 : Cover) i)| := by
    filter_upwards [hfront,ha] with z hz hzn
    have he := isMinimizerAt_normal_chamberHeightSign hV hE hm hμ hN hp ha hs hsg hz i
    rw [hzn] at he
    exact he
  have hrg := circle_unsigned_normal_density i (s i) hr hg hrm hgm hsign
  have hrgr := (AddCircle.measurePreserving_mk (1 : ℝ) 0).quasiMeasurePreserving.ae hrg
  simp only [zero_add] at hrgr
  rw [← restrict_Ioo_eq_restrict_Ioc] at hrgr
  have heq : (fun t : ℝ => sliceJensenG (axialJensenFlux (openRepresentative E) μ H V i t/
      (axialCirclePerimeter (openRepresentative E) i t).toReal)*r t) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
    (fun t => sliceJensenG (axialJensenFlux (openRepresentative E) μ H V i t/
      (axialCirclePerimeter (openRepresentative E) i t).toReal)*
      (-deriv (axialSectionArea (openRepresentative E) i) t*chamberHeightSign (s i) t)) := by
    filter_upwards [hrgr,hgd] with t ht htd
    rw [ht,htd]
  have hI : IntervalIntegrable (fun t : ℝ => sliceJensenG (axialJensenFlux (openRepresentative E) μ H V i t/
      (axialCirclePerimeter (openRepresentative E) i t).toReal)*r t) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ)≤1)]
    exact (circle_integrable_preimage_Icc hJi 0).mono_set (by simpa only [zero_add] using Ioo_subset_Icc_self)
  have heqi : _ = _ := intervalIntegral.integral_congr_ae_restrict
    (f := fun t : ℝ => sliceJensenG (axialJensenFlux (openRepresentative E) μ H V i t/
      (axialCirclePerimeter (openRepresentative E) i t).toReal)*r t)
    (g := fun t : ℝ => sliceJensenG (axialJensenFlux (openRepresentative E) μ H V i t/
      (axialCirclePerimeter (openRepresentative E) i t).toReal)*
      (-deriv (axialSectionArea (openRepresentative E) i) t*chamberHeightSign (s i) t))
    (μ := volume) (a := 0) (b := 1) (by rwa [uIoc_of_le (by norm_num : (0 : ℝ)≤1),← restrict_Ioo_eq_restrict_Ioc])
  refine ⟨?_,?_,?_⟩
  · filter_upwards [hrgr,hgd] with t ht htd
    rw [htd]
    exact (hr0 (t : AddCircle (1 : ℝ))).trans_eq ht
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ)≤1)] at hI ⊢
    exact hI.congr heq
  · rw [← heqi]
    rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0] at hJ
    simpa only [zero_add] using hJ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace CubicTorus

lemma absolutelyContinuous_comp_lipschitz {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) {G : ℝ → ℝ} {K : ℝ≥0}
    (hG : LipschitzWith K G) : AbsolutelyContinuousOnInterval (G ∘ f) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  have hK : 0<(K : ℝ)+1 := by positivity
  obtain ⟨δ,hδ,hd⟩ := hf (ε/((K : ℝ)+1)) (div_pos hε hK)
  refine ⟨δ,hδ,?_⟩
  intro E hE he
  have hsum := hd E hE he
  calc
    _≤∑ i∈Finset.range E.1,((K : ℝ)+1)*dist (f (E.2 i).1) (f (E.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hG.dist_le_mul _ _).trans (by nlinarith [(dist_nonneg : 0≤dist (f (E.2 i).1) (f (E.2 i).2))])
    _=((K : ℝ)+1)*(∑ i∈Finset.range E.1,dist (f (E.2 i).1) (f (E.2 i).2)) := by
      rw [Finset.mul_sum]
    _<ε := by simpa only [mul_comm] using (lt_div_iff₀ hK).mp hsum

theorem ac_substitution_boundedContinuous {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (γ : ℝ →ᵇ ℝ) :
    (∫ t in a..b,γ (f t)*deriv f t)=∫ w in f a..f b,γ w := by
  let G : ℝ → ℝ := fun x => ∫ w in f a..x,γ w
  have hG (x : ℝ) : HasDerivAt G (γ x) x :=
    (γ.continuous.integral_hasStrictDerivAt (f a) x).hasDerivAt
  have hl : LipschitzWith ‖γ‖₊ G := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hG x).differentiableAt)
    intro x
    rw [(hG x).deriv]
    exact γ.nnnorm_coe_le_nnnorm x
  have hcomp := absolutelyContinuous_comp_lipschitz hf hl
  have hd : ∀ᵐ t : ℝ,t∈uIcc a b → deriv (G ∘ f) t=γ (f t)*deriv f t := by
    filter_upwards [hf.ae_differentiableAt] with t ht htab
    exact ((hG (f t)).comp t (ht htab).hasDerivAt).deriv
  calc
    _=∫ t in a..b,deriv (G ∘ f) t := by
      apply intervalIntegral.integral_congr_ae
      exact hd.mono fun t ht hh => (ht (uIoc_subset_uIcc hh)).symm
    _=G (f b)-G (f a) := hcomp.integral_deriv_eq_sub
    _=_ := by simp [G]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace CubicTorus

lemma chamber_sign_integral_substitution {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1) (hp : f 1=f 0)
    (b : Bool) (γ : ℝ →ᵇ ℝ) :
    (∫ t in (0 : ℝ)..1,γ (f t)*(-deriv f t*chamberHeightSign b t))=
      2*(∫ w in f ((if b then 1/2 else 0)+1/2)..f (if b then 1/2 else 0),γ w) := by
  let a : ℝ := if b then 1/2 else 0
  let G : ℝ → ℝ := fun x => ∫ w in f (a+1/2)..x,γ w
  have hG (x : ℝ) : HasDerivAt G (γ x) x :=
    (γ.continuous.integral_hasStrictDerivAt (f (a+1/2)) x).hasDerivAt
  have hl : LipschitzWith ‖γ‖₊ G := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hG x).differentiableAt)
    intro x
    rw [(hG x).deriv]
    exact γ.nnnorm_coe_le_nnnorm x
  have hcomp := absolutelyContinuous_comp_lipschitz hf hl
  have hd : ∀ᵐ t : ℝ,t∈uIcc (0 : ℝ) 1 →
      deriv (G ∘ f) t=γ (f t)*deriv f t := by
    filter_upwards [hf.ae_differentiableAt] with t ht htab
    exact ((hG (f t)).comp t (ht htab).hasDerivAt).deriv
  have hsub := chamberSign_integral_deriv hcomp (congrArg G hp) b
  calc
    _=-(∫ t in (0 : ℝ)..1,deriv (G ∘ f) t*chamberHeightSign b t) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with t ht htab
      rw [ht (uIoc_subset_uIcc htab)]
      ring
    _=_ := by rw [hsub]; simp [G,a]

theorem chamber_ac_area_measure {f : ℝ → ℝ} (hc : Continuous f)
    (hf : AbsolutelyContinuousOnInterval f 0 1) (hp : f 1=f 0) (b : Bool)
    (hends : f ((if b then 1/2 else 0)+1/2)≤f (if b then 1/2 else 0))
    (hn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),0≤-deriv f t*chamberHeightSign b t) :
    Measure.map f ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity
      (fun t => ENNReal.ofReal (-deriv f t*chamberHeightSign b t)))=
      (2 : ℝ≥0∞) • volume.restrict
        (Ioo (f ((if b then 1/2 else 0)+1/2)) (f (if b then 1/2 else 0))) := by
  have hi : Integrable (fun t : ℝ => -deriv f t*chamberHeightSign b t)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (hf.intervalIntegrable_deriv.1.mono_set Ioo_subset_Ioc_self).neg.mul_bdd
      ((measurable_chamberHeightSign b).comp (AddCircle.continuous_mk' (1 : ℝ)).measurable).aestronglyMeasurable
      (Eventually.of_forall fun t => (norm_chamberHeightSign b t).le)
  let := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  have hwd : Measurable (fun t : ℝ => ENNReal.ofReal (-deriv f t*chamberHeightSign b t)) :=
    ((measurable_deriv f).neg.mul ((measurable_chamberHeightSign b).comp
      (AddCircle.continuous_mk' (1 : ℝ)).measurable)).ennreal_ofReal
  let : IsFiniteMeasure ((2 : ℝ≥0∞) • volume.restrict
      (Ioo (f ((if b then 1/2 else 0)+1/2)) (f (if b then 1/2 else 0)))) :=
    Measure.smul_finite _ (by norm_num)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro γ
  rw [integral_map hc.measurable.aemeasurable γ.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hwd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have he : (∫ t in Ioo (0 : ℝ) 1,
      (ENNReal.ofReal (-deriv f t*chamberHeightSign b t)).toReal • γ (f t))=
      ∫ t in (0 : ℝ)..1,γ (f t)*(-deriv f t*chamberHeightSign b t) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),← restrict_Ioo_eq_restrict_Ioc]
    apply integral_congr_ae
    filter_upwards [hn] with t ht
    rw [ENNReal.toReal_ofReal ht,smul_eq_mul,mul_comm]
  rw [he,chamber_sign_integral_substitution hf hp b γ,
    intervalIntegral.integral_of_le hends,integral_smul_measure]
  simp only [ENNReal.toReal_ofNat,smul_eq_mul]
  rw [← restrict_Ioo_eq_restrict_Ioc]

lemma chamber_ac_area_substitution {f : ℝ → ℝ} (hc : Continuous f)
    (hf : AbsolutelyContinuousOnInterval f 0 1) (hp : f 1=f 0) (b : Bool)
    (hends : f ((if b then 1/2 else 0)+1/2)≤f (if b then 1/2 else 0))
    (hn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),0≤-deriv f t*chamberHeightSign b t)
    {γ : ℝ → ℝ≥0∞} (hγ : Measurable γ) :
    (∫⁻ t in Ioo (0 : ℝ) 1,γ (f t)*ENNReal.ofReal (-deriv f t*chamberHeightSign b t))=
      2*(∫⁻ w in Ioo (f ((if b then 1/2 else 0)+1/2)) (f (if b then 1/2 else 0)),γ w) := by
  have hwd : Measurable (fun t : ℝ => ENNReal.ofReal (-deriv f t*chamberHeightSign b t)) :=
    ((measurable_deriv f).neg.mul ((measurable_chamberHeightSign b).comp
      (AddCircle.continuous_mk' (1 : ℝ)).measurable)).ennreal_ofReal
  have he := congrArg (fun ν : Measure ℝ => ∫⁻ w,γ w ∂ν)
    (chamber_ac_area_measure hc hf hp b hends hn)
  rw [lintegral_map hγ hc.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hwd (show Measurable (fun t => γ (f t)) from hγ.comp hc.measurable),lintegral_smul_measure] at he
  simpa only [Pi.mul_apply,smul_eq_mul,mul_comm] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace CubicTorus

theorem chamber_area_lower_bound {f : ℝ → ℝ} (hc : Continuous f)
    (hf : AbsolutelyContinuousOnInterval f 0 1) (hp : f 1=f 0) (b : Bool)
    (hends : f ((if b then 1/2 else 0)+1/2)≤f (if b then 1/2 else 0))
    (hn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),0≤-deriv f t*chamberHeightSign b t)
    {J : ℝ → ℝ}
    (hJi : IntegrableOn (fun t => J t*(-deriv f t*chamberHeightSign b t)) (Ioo (0 : ℝ) 1))
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγ0 : ∀ v,0≤γ v)
    (hγJ : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),γ (f t)≤J t) :
    IntegrableOn γ (Ioo (f ((if b then 1/2 else 0)+1/2)) (f (if b then 1/2 else 0))) ∧
      2*(∫ v in Ioo (f ((if b then 1/2 else 0)+1/2)) (f (if b then 1/2 else 0)),γ v)≤
        ∫ t in Ioo (0 : ℝ) 1,J t*(-deriv f t*chamberHeightSign b t) := by
  let w : ℝ → ℝ := fun t => -deriv f t*chamberHeightSign b t
  have hwm : Measurable w := (measurable_deriv f).neg.mul
    ((measurable_chamberHeightSign b).comp (AddCircle.continuous_mk' (1 : ℝ)).measurable)
  have hle : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),γ (f t)*w t≤J t*w t := by
    filter_upwards [hn,hγJ] with t ht hj
    exact mul_le_mul_of_nonneg_right hj ht
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),0≤γ (f t)*w t :=
    hn.mono fun t ht => mul_nonneg (hγ0 _) ht
  have hgi : Integrable (fun t => γ (f t)*w t) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    hJi.mono_nonneg ((hγ.comp hc.measurable).mul hwm).aestronglyMeasurable hnonneg hle
  have hgid : Integrable (γ ∘ f) ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity
      (fun t => ENNReal.ofReal (w t))) := by
    apply (integrable_withDensity_iff_integrable_smul' hwm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    apply hgi.congr
    filter_upwards [hn] with t ht
    rw [ENNReal.toReal_ofReal ht,smul_eq_mul]
    exact mul_comm _ _
  have hmeas := chamber_ac_area_measure hc hf hp b hends hn
  have hmapInt : Integrable γ (Measure.map f ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity
      (fun t => ENNReal.ofReal (w t)))) :=
    (integrable_map_measure hγ.aestronglyMeasurable hc.measurable.aemeasurable).mpr hgid
  change Integrable γ (Measure.map f ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity
      (fun t => ENNReal.ofReal (-deriv f t*chamberHeightSign b t)))) at hmapInt
  rw [hmeas] at hmapInt
  have hga := (integrable_smul_measure (by norm_num : (2 : ℝ≥0∞)≠0)
    (by norm_num : (2 : ℝ≥0∞)≠∞)).mp hmapInt
  refine ⟨hga,?_⟩
  have he := congrArg (fun ν : Measure ℝ => ∫ v,γ v ∂ν) hmeas
  rw [integral_map hc.measurable.aemeasurable hγ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),integral_smul_measure] at he
  simp only [ENNReal.toReal_ofNat,smul_eq_mul] at he
  have hex : (∫ t in Ioo (0 : ℝ) 1,(ENNReal.ofReal (w t)).toReal*γ (f t))=
      ∫ t in Ioo (0 : ℝ) 1,γ (f t)*w t := by
    apply integral_congr_ae
    filter_upwards [hn] with t ht
    rw [ENNReal.toReal_ofReal ht,mul_comm]
  change (∫ t in Ioo (0 : ℝ) 1,(ENNReal.ofReal (w t)).toReal*γ (f t))=_ at he
  rw [hex] at he
  rw [← he]
  exact integral_mono_ae hgi hJi hle

end CubicTorus

end
end

end OAI
