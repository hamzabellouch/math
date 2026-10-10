import Mathlib
import OAI.Geometry.CubicTorus.Reflection.NormalMeasureCoordinateReflection

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volumeSupport_coordinateReflection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    volumeSupport (coordinateReflection i ⁻¹' E)=coordinateReflection i ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : (coordinateReflection i ⁻¹' E)∩Metric.ball a r=
      coordinateReflection i ⁻¹' (E∩Metric.ball (coordinateReflection i a) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,(coordinateReflection_isometry i).dist_eq]
  rw [he,Measure.real_def,Measure.real_def,
    (coordinateReflection_measurePreserving i).measure_preimage
      (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_coordinateReflection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    openRepresentative (coordinateReflection i ⁻¹' E)=coordinateReflection i ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_coordinateReflection hE.compl]
  rfl

lemma frontier_openRepresentative_coordinateReflection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    frontier (openRepresentative (coordinateReflection i ⁻¹' E))=
      coordinateReflection i ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_coordinateReflection hE i]
  exact (coordinateReflectionEquiv i).toHomeomorph.preimage_frontier _ |>.symm

lemma frontier_reflection_invariant {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    coordinateReflection i ⁻¹' frontier (openRepresentative E)=frontier (openRepresentative E) := by
  rw [← frontier_openRepresentative_coordinateReflection hE i,openRepresentative_congr_ae hs]

lemma coordinateReflection_fixed_of_sine_zero (i : Fin 3) {a : Torus}
    (ha : coordinateSine i (representative a)=0) : coordinateReflection i a=a := by
  ext j
  by_cases hji : j=i
  · subst j
    simp only [coordinateReflection_apply,ite_true]
    change -a i=a i
    have hz : Real.sin (Real.pi*(2*representative a i))=0 := by
      simpa only [coordinateSine,mul_assoc,mul_left_comm,mul_comm] using ha
    obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp hz
    have he : (2 : ℝ)*representative a i=(k : ℝ) := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      exact hk.symm.trans (mul_comm _ _)
    have hh : ((2*representative a i : ℝ) : AddCircle (1 : ℝ))=0 := by
      rw [he]
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k,by simp⟩
    have haa : a i+a i=0 := by
      rw [← quotientMap_representative a]
      change ((representative a i : ℝ) : AddCircle (1 : ℝ))+((representative a i : ℝ) : AddCircle (1 : ℝ))=0
      rw [← AddCircle.coe_add,← two_mul]
      exact hh
    exact (neg_eq_iff_add_eq_zero).mpr haa
  · simp [hji]

theorem isMinimizerAt_normal_coordinate_seam_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) {a : Torus}
    (ha : a∈frontier (openRepresentative E)) (hz : coordinateSine i (representative a)=0) :
    N (representative a) i=0 := by
  have hh := congrArg (fun x : Cover => x i) (isMinimizerAt_normal_reflection hV hE hmE hμ hN hp hae i hs
    (representative a) (by rwa [quotientMap_representative]))
  simp only [coverCoordinateReflection_apply,ite_true] at hh
  have he : N (coverCoordinateReflection i (representative a))=N (representative a) := by
    rw [← periodic_representative hp (coverCoordinateReflection i (representative a)),
      quotientMap_coordinateReflection,quotientMap_representative,coordinateReflection_fixed_of_sine_zero i hz]
  rw [he] at hh
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma HasDerivAt.eq_zero_of_right_zero {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (h0 : f 0=0)
    (hf : ∀ᶠ t in 𝓝[>] (0 : ℝ),f t=0) : d=0 := by
  have hp := deriv_nonneg_of_right_min hd (hf.mono fun t ht => by rw [h0,ht])
  have hn := deriv_nonneg_of_right_min hd.neg (hf.mono fun t ht => by
    simp only [Pi.neg_apply,h0,ht,neg_zero,le_refl])
  linarith

lemma HasDerivAt.neg_right_of_neg {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (h0 : f 0=0) (hd0 : d<0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),f t<0 := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi 0⊆{0}ᶜ from fun t ht => ne_of_gt ht))
  filter_upwards [ht.eventually (eventually_lt_nhds hd0),self_mem_nhdsWithin] with t hs ht
  rw [slope_def_field,h0,sub_zero,sub_zero] at hs
  simpa only [zero_mul] using (div_lt_iff₀ ht).mp hs

lemma plane_hasDerivAt_line {F : Plane → ℝ} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (v : Plane) :
    HasDerivAt (fun t : ℝ => F (y+t • v)) (fderiv ℝ F y v) 0 := by
  have hh : HasFDerivAt F (fderiv ℝ F y) (y+id (0 : ℝ) • v) := by
    simpa only [id_eq,zero_smul,add_zero] using hF.hasFDerivAt
  simpa only [Function.comp_def,id_eq,one_smul] using
    hh.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add y)

theorem not_differentiable_nodal_splice
    {u F : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {c y : Plane} {R k : ℝ} (hR : 0<R) (hk : k≠0)
    (hy : ‖y-c‖=R) (huy : u y=0)
    (hhopf : 0<fderiv ℝ u y (c-y))
    (hin : ∀ x,‖x-c‖<R → F x=k*u x)
    (hout : ∀ᶠ x in 𝓝 y,u x≤0 → F x=0) :
    ¬DifferentiableAt ℝ F y := by
  intro hF
  let v := c-y
  have hn (t : ℝ) : ‖y+t • v-c‖=|1-t| * R := by
    rw [show y+t • v-c=(1-t) • (y-c) by dsimp [v]; module,
      norm_smul,Real.norm_eq_abs,hy]
  have huin := plane_hasDerivAt_line (hu.differentiable (by simp) y) v
  have hFin := plane_hasDerivAt_line hF v
  have hFy : F y=0 := (hout.self_of_nhds) huy.le
  have hi : ∀ᶠ t in 𝓝[>] (0 : ℝ),F (y+t • v)-k*u (y+t • v)=0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
    have ht0 : 0<t := ht
    rw [hin,sub_self]
    rw [hn,abs_of_pos (sub_pos.mpr ht1)]
    nlinarith
  have hid := HasDerivAt.eq_zero_of_right_zero (hFin.sub (huin.const_mul k)) (by
    simp only [Pi.sub_apply,zero_smul,add_zero,hFy,huy,mul_zero,sub_self]) hi
  have huout : HasDerivAt (fun t : ℝ => u (y+t • (-v))) (-fderiv ℝ u y v) 0 := by
    simpa only [map_neg] using plane_hasDerivAt_line (hu.differentiable (by simp) y) (-v)
  have hFout : HasDerivAt (fun t : ℝ => F (y+t • (-v))) (-fderiv ℝ F y v) 0 := by
    simpa only [map_neg] using plane_hasDerivAt_line hF (-v)
  have ho := HasDerivAt.neg_right_of_neg huout (by simp [huy]) (neg_neg_of_pos hhopf)
  have ht : Tendsto (fun t : ℝ => y+t • (-v)) (𝓝 0) (𝓝 y) := by
    convert (show Continuous (fun t : ℝ => y+t • (-v)) from
      continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ) using 1
    simp
  have hfo : ∀ᶠ t in 𝓝[>] (0 : ℝ),F (y+t • (-v))=0 := by
    filter_upwards [ho,(ht.eventually hout).filter_mono nhdsWithin_le_nhds] with t ht hf
    exact hf ht.le
  have hod := HasDerivAt.eq_zero_of_right_zero hFout (by simp [hFy]) hfo
  have hm : k*fderiv ℝ u y v=0 := by linarith
  exact (mul_ne_zero hk (ne_of_gt hhopf)) hm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.no_nodal_splice_frontier
    {g u F : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) {D : Set Plane} (hD : IsOpen D)
    {a : Plane} {ε k : ℝ} (hε : 0<ε) (hk : k≠0)
    (hp : ∀ x∈Metric.ball a ε,‖gradient g x‖≤1)
    (hw : LinearCMCEquation u (gradient g) (fun _ => 0) (Metric.ball a ε))
    (hpos : ∀ x∈D∩Metric.ball a ε,0<u x)
    (hz : ∀ x∈frontier D∩Metric.ball a ε,u x=0)
    (hin : ∀ x∈D∩Metric.ball a ε,F x=k*u x)
    (hout : ∀ x∈Metric.ball a ε,u x≤0 → F x=0)
    (hF : DifferentiableOn ℝ F (Metric.ball a ε)) : a∉frontier D := by
  intro ha
  obtain ⟨c,y,R,hR,hball,hy,hyD,hsub⟩ := plane_interior_ball_at_frontier hD ha hε
  have hb : Metric.ball c R⊆Metric.ball a ε := Metric.ball_subset_closedBall.trans hsub
  have hyb : y∈Metric.ball a ε := hsub (by
    simpa only [Metric.mem_closedBall,dist_eq_norm,hy] using (le_refl R))
  have huy := hz y ⟨hyD,hyb⟩
  have hh := (hw.mono hb).hopf hg hu hR (fun x hx => hp x (hsub hx))
    (fun x hx => hpos x ⟨hball hx,hb hx⟩) hy huy
  apply not_differentiable_nodal_splice hu hR hk hy huy hh ?_ ?_
    (hF.differentiableAt (Metric.isOpen_ball.mem_nhds hyb))
  · intro x hx
    have hx' : x∈Metric.ball c R := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    exact hin x ⟨hball hx',hb hx'⟩
  · filter_upwards [Metric.isOpen_ball.mem_nhds hyb] with x hx
    exact hout x hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nodal_splice_closed {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (hFu : (u.1 : NormalBundle → ℝ)=ᵐ[(μ : Measure NormalBundle)] F ∘ normalProjection)
    (v : Cover) {D : Set Torus}
    (hD : IsPositiveNodalPiece (directionalNormalScalar N hN hp v)
      (frontier (openRepresentative E)) D)
    {k : ℝ} (hk : k≠0)
    (hFD : ∀ a∈D,F a=k*⟪v,N (representative a)⟫)
    (hFzero : ∀ a∈frontier (openRepresentative E),⟪v,N (representative a)⟫≤0 → F a=0) :
    IsClosed D := by
  let S := frontier (openRepresentative E)
  let t := directionalNormalScalar N hN hp v
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  have hDS : D⊆S := by
    intro a ha; rw [hDU] at ha; exact ha.1.1
  apply isClosed_of_closure_subset
  intro a ha
  by_contra haD
  have haS : a∈S := closure_minimal hDS isClosed_frontier ha
  let x := representative a
  have hxa : quotientMap x=a := quotientMap_representative a
  have hx : quotientMap x∈S := by rwa [hxa]
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hm,hcover,r,hr,hgrad,hlin⟩ :=
    isMinimizerAt_normal_linear_chart hV hE hmin hμ hN hp hae x hx
  let G := normalGraph n g
  let φ : Plane → Torus := fun y => quotientMap (x+G y)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (normalPlaneLinearIsometry n).contDiff.add (hg.smul contDiff_const)
  have hφ : Continuous φ := continuous_quotientMap.comp (continuous_const.add hG.continuous)
  have hG0 : G 0=0 := by
    simp only [G,normalGraph,hg0,zero_smul,add_zero]
    exact (normalPlaneLinearIsometry n).map_zero
  have hφ0 : φ 0=a := by simp only [φ,hG0,add_zero,hxa]
  obtain ⟨ρ,hρ,hρm⟩ := Metric.mem_nhds_iff.mp hm
  let ε := min r ρ
  have hε : 0<ε := lt_min hr hρ
  have hεr : ε≤r := min_le_left _ _
  have hερ : ε≤ρ := min_le_right _ _
  have hb (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      N (x+G y)=σ • graphSlopeNormal n (gradient g y) ∧ φ y∈S :=
    hρm (Metric.ball_subset_ball hερ hy)
  let w := normalTranslationNumerator n g v σ
  let W : Plane → ℝ := fun y => cmcWeight (gradient g y)
  let B : Plane → ℝ := fun y => W y*F (φ y)
  have hW (y : Plane) : 0<W y := cmcWeight_pos _
  have hws (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      w y=W y*⟪v,N (representative (φ y))⟫ := by
    rw [show N (representative (φ y))=N (x+G y) from periodic_representative hp _]
    rw [(hb y hy).1]
    exact normalTranslationNumerator_weight hn g v σ y
  have ht (b : Torus) : t.val (representative b)=⟪v,N (representative b)⟫ :=
    directionalNormalScalar_apply N hN hp v _
  let A : Set Plane := {y | 0<w y}∩φ ⁻¹' U∩Metric.ball 0 ε
  have hwo : ContDiff ℝ (⊤ : ℕ∞) w := normalTranslationNumerator_contDiff n hg v σ
  have hAo : IsOpen A := ((isOpen_lt continuous_const hwo.continuous).inter
    (hU.preimage hφ)).inter Metric.isOpen_ball
  have hAD (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) : y∈A ↔ φ y∈D := by
    rw [hDU]
    change (0<w y ∧ φ y∈U) ∧ y∈Metric.ball 0 ε ↔
      (φ y∈S ∧ 0<t.val (representative (φ y))) ∧ φ y∈U
    rw [ht,hws y hy,mul_pos_iff_of_pos_left (hW y)]
    exact ⟨fun h => ⟨⟨(hb y hy).2,h.1.1⟩,h.1.2⟩,
      fun h => ⟨⟨h.1.2,h.2⟩,hy⟩⟩
  have hAC (y : Plane) (hy : y∈Metric.ball (0 : Plane) ε) :
      y∈A ↔ 0<w y ∧ φ y∈C := by
    rw [hAD y hy,hDC]
    change (φ y∈S ∧ 0<t.val (representative (φ y))) ∧ φ y∈C ↔ _
    rw [ht,hws y hy,mul_pos_iff_of_pos_left (hW y)]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨(hb y hy).2,h.1⟩,h.2⟩⟩
  have hAcl : (0 : Plane)∈closure A := by
    have hpc : (0 : Plane)∈closure (φ ⁻¹' D) := quotient_graph_closure hDS
      (hcover.mono fun z hz => hz.mp) (by rwa [hxa])
    rw [Metric.mem_closure_iff] at hpc ⊢
    intro δ hδ
    obtain ⟨y,hy,hyd⟩ := hpc (min δ ε) (lt_min hδ hε)
    have hye : y∈Metric.ball (0 : Plane) ε := by
      rw [Metric.mem_ball,dist_comm]
      exact hyd.trans_le (min_le_right _ _)
    exact ⟨y,(hAD y hye).mpr hy,hyd.trans_le (min_le_left _ _)⟩
  have hAf : (0 : Plane)∈frontier A := by
    rw [hAo.frontier_eq]
    refine ⟨hAcl,?_⟩
    intro hz
    have ha' := (hAD 0 (Metric.mem_ball_self hε)).mp hz
    rw [hφ0] at ha'
    exact haD ha'
  have hδ : 0<ε/2 := half_pos hε
  have hδs : Metric.ball (0 : Plane) (ε/2)⊆Metric.ball 0 ε :=
    Metric.ball_subset_ball (by linarith)
  have hB : DifferentiableOn ℝ B (Metric.ball (0 : Plane) (ε/2)) := by
    intro y hy
    have hnear : ∀ᶠ z in 𝓝 y,φ z∈S := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hδs hy)] with z hz
      exact (hb z hz).2
    have hf := isMinimizerAt_H1_jacobi_parametric_smooth hV hE hmin hμ
      N hN hp hae hNu hu hhom hFm hF hFu x (hG.contDiffAt (x := y)) hnear
    exact ((cmcWeight_contDiff.comp (plane_gradient_contDiff hg)).contDiffAt.mul hf).differentiableAt
      (by simp) |>.differentiableWithinAt
  apply (normalTranslationNumerator_linear n hg v σ hlin |>.mono
    (hδs.trans (Metric.ball_subset_ball hεr))).no_nodal_splice_frontier
      hg hwo hAo hδ hk (fun y hy => hgrad y (Metric.ball_subset_ball hεr (hδs hy)))
      (fun y hy => hy.1.1.1) ?_ ?_ ?_ hB hAf
  · intro y hy
    apply planar_positive_piece_frontier_zero hwo.continuous hAo (hC.preimage hφ) ?_ ?_ hy.1 hy.2
    · intro z hz
      exact (hAC z hz.2).mp hz
    · intro z hz hw hc
      exact (hAC z (hδs hz)).mpr ⟨hw,hc⟩
  · intro y hy
    have hyε := hδs hy.2
    have hd := (hAD y hyε).mp hy.1
    change W y*F (φ y)=k*w y
    rw [hFD _ hd,hws y hyε]
    ring
  · intro y hy hwy
    have hyε := hδs hy
    have hnv : ⟪v,N (representative (φ y))⟫≤0 := by
      rw [hws y hyε] at hwy
      exact nonpos_of_mul_nonpos_right hwy (hW y)
    change W y*F (φ y)=0
    rw [hFzero _ (hb y hyε).2 hnv,mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma directionalNormalScalar_mean_zero {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover) :
    surfaceMean μ (surfaceSmoothJet μ (directionalNormalScalar N hN hp v))=0 := by
  simp only [directionalNormalScalar,map_sum,map_smul,
    normalComponentScalar_mean_zero hμ hN hp hae,smul_zero,Finset.sum_const_zero]

theorem isMinimizerAt_translation_negative_point {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (v : Cover) {D : Set Torus} (hDm : MeasurableSet D)
    (hD : IsPositiveNodalPiece (directionalNormalScalar N hN hp v)
      (frontier (openRepresentative E)) D) (hDn : D.Nonempty) :
    ∃ a∈frontier (openRepresentative E),⟪v,N (representative a)⟫<0 := by
  classical
  let f := directionalNormalScalar N hN hp v
  by_contra! hn
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hpos := isMinimizerAt_nodal_mean_pos hV hE hmin hμ f hDm hD hDn
  have hzero := directionalNormalScalar_mean_zero hμ hN hp hae v
  rw [surfaceMean_nodal] at hpos
  rw [surfaceMean_of_smooth] at hzero
  have hle : (∫ z,nodalSurfaceValue f D z ∂(μ : Measure NormalBundle)) ≤
      ∫ z,f.val z.1 ∂(μ : Measure NormalBundle) := by
    apply integral_mono_ae ((nodalSurfaceValue_memLp μ f D hDm).integrable (by norm_num))
      ((smoothScalarValue f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    filter_upwards [hbd] with z hz
    by_cases hd : normalProjection z∈D
    · simp only [nodalSurfaceValue,indicator_of_mem (show z∈normalProjection ⁻¹' D from hd),
        smoothScalarValue,ContinuousMap.coe_mk,le_refl]
    · have hv : N (representative (normalProjection z))=N z.1 := periodic_representative hp _
      simpa only [nodalSurfaceValue,indicator_of_notMem (show z∉normalProjection ⁻¹' D from hd),
        smoothScalarValue,ContinuousMap.coe_mk,f,directionalNormalScalar_apply,hv] using hn (normalProjection z) hz
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def surfaceNodalBalanceValue (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A)
    (x : Torus) : ℝ :=
  surfaceMean μ (nodalSurfaceJet μ g A hA) * D.indicator (fun a => f.val (representative a)) x +
    (-surfaceMean μ (nodalSurfaceJet μ f D hD)) * A.indicator (fun a => g.val (representative a)) x

lemma surfaceNodalBalanceValue_measurable (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A) :
    Measurable (surfaceNodalBalanceValue μ f g D A hD hA) :=
  ((continuous_periodic_descent f.property.1.continuous f.property.2).measurable.indicator hD).const_mul _ |>.add
    (((continuous_periodic_descent g.property.1.continuous g.property.2).measurable.indicator hA).const_mul _)

lemma surfaceNodalBalanceValue_continuousOn (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) {S D A : Set Torus} (hD : MeasurableSet D) (hA : MeasurableSet A)
    (hd : IsPositiveNodalPiece f S D) (ha : IsPositiveNodalPiece g S A) :
    ContinuousOn (surfaceNodalBalanceValue μ f g D A hD hA) S :=
  ((hd.continuous_value f).const_mul _).add ((ha.continuous_value g).const_mul _)

lemma surfaceNodalBalanceValue_ae (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A) :
    ((surfaceNodalBalance μ (nodalSurfaceJet μ f D hD) (nodalSurfaceJet μ g A hA)).1 :
      NormalBundle → ℝ) =ᵐ[(μ : Measure NormalBundle)] surfaceNodalBalanceValue μ f g D A hD hA ∘ normalProjection := by
  let d := nodalSurfaceJet μ f D hD
  let a := nodalSurfaceJet μ g A hA
  filter_upwards [Lp.coeFn_add (surfaceMean μ a • d.1) ((-surfaceMean μ d) • a.1),
    Lp.coeFn_smul (surfaceMean μ a) d.1,Lp.coeFn_smul (-surfaceMean μ d) a.1,
    (nodalSurfaceValue_memLp μ f D hD).coeFn_toLp,
    (nodalSurfaceValue_memLp μ g A hA).coeFn_toLp] with z h1 h2 h3 h4 h5
  change d.1 z=nodalSurfaceValue f D z at h4
  change a.1 z=nodalSurfaceValue g A z at h5
  change (surfaceMean μ a • d.1+(-surfaceMean μ d) • a.1) z=_
  rw [h1]
  simp only [Pi.add_apply,h2,h3,Pi.smul_apply,smul_eq_mul,h4,h5,nodalSurfaceValue_descent]
  rfl

lemma surfaceNodalBalanceValue_on_left (μ : FiniteMeasure NormalBundle)
    (f g : smoothPeriodicScalars) (D A : Set Torus) (hD : MeasurableSet D) (hA : MeasurableSet A)
    (hDA : Disjoint D A) {x : Torus} (hx : x∈D) :
    surfaceNodalBalanceValue μ f g D A hD hA x=
      surfaceMean μ (nodalSurfaceJet μ g A hA)*f.val (representative x) := by
  have hn : x∉A := fun ha => Set.disjoint_left.mp hDA hx ha
  simp [surfaceNodalBalanceValue,hx,hn]

lemma surfaceNodalBalanceValue_nonpos (μ : FiniteMeasure NormalBundle)
    (f : smoothPeriodicScalars) {S D A : Set Torus} (hD : MeasurableSet D) (hA : MeasurableSet A)
    (hd : IsPositiveNodalPiece f S D) (ha : IsPositiveNodalPiece f S A)
    {x : Torus} (hx : f.val (representative x)≤0) :
    surfaceNodalBalanceValue μ f f D A hD hA x=0 := by
  have hdx : x∉D := by
    intro h
    obtain ⟨U,_,he⟩ := hd.1
    rw [he] at h
    exact (not_lt_of_ge hx) h.1.2
  have hax : x∉A := by
    intro h
    obtain ⟨U,_,he⟩ := ha.1
    rw [he] at h
    exact (not_lt_of_ge hx) h.1.2
  simp [surfaceNodalBalanceValue,hdx,hax]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma IsPositiveNodalPiece.eq_inter_open (f : smoothPeriodicScalars)
    {S D : Set Torus} (hD : IsPositiveNodalPiece f S D) :
    ∃ W : Set Torus,IsOpen W ∧ D=S∩W := by
  obtain ⟨U,hU,hDU⟩ := hD.1
  refine ⟨{a | 0<f.val (representative a)}∩U,
    (isOpen_lt continuous_const (continuous_periodic_descent f.property.1.continuous f.property.2)).inter hU,?_⟩
  rw [hDU]
  ext a
  simp only [mem_inter_iff,mem_ofPred_eq,and_assoc]

lemma IsPositiveNodalPiece.subset (f : smoothPeriodicScalars)
    {S D : Set Torus} (hD : IsPositiveNodalPiece f S D) : D⊆S := by
  obtain ⟨W,_,he⟩ := hD.eq_inter_open f
  rw [he]
  exact inter_subset_left

theorem isMinimizerAt_positive_nodal_not_disjoint {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hNu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1)
    (hs : ∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
      0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u)
    (v : Cover)
    (hj : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp v)) z=0)
    {D A : Set Torus}
    (hD : IsPositiveNodalPiece (directionalNormalScalar N hN hp v)
      (frontier (openRepresentative E)) D)
    (hA : IsPositiveNodalPiece (directionalNormalScalar N hN hp v)
      (frontier (openRepresentative E)) A)
    (hDn : D.Nonempty) (hAn : A.Nonempty) : ¬Disjoint D A := by
  intro hDA
  let f := directionalNormalScalar N hN hp v
  obtain ⟨hDm,hdmem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hD
  obtain ⟨hAm,hamem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hA
  let d := nodalSurfaceJet μ f D hDm
  let a := nodalSurfaceJet μ f A hAm
  let u := surfaceNodalBalance μ d a
  have hdnull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f D hDm hdmem hj
  have hanull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f A hAm hamem hj
  have hnull : surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 :=
    surfaceNodalBalance_null μ _ hdnull hanull (surfaceJacobiB_disjoint_nodal μ _ f f D A hDm hAm hDA)
  have humem : u∈surfaceH1 μ := surfaceNodalBalance_mem μ hdmem hamem
  have hmean : surfaceMean μ u=0 := surfaceNodalBalance_mean μ d a
  have hapos : 0<surfaceMean μ a := isMinimizerAt_nodal_mean_pos hV hE hmin hμ f hAm hA hAn
  obtain ⟨b,hbS,hbneg⟩ := isMinimizerAt_translation_negative_point hV hE hmin hμ hN hp hae v hDm hD hDn
  let U : Set Torus := {b | f.val (representative b)<0}
  have hU : IsOpen U := isOpen_lt (continuous_periodic_descent f.property.1.continuous f.property.2) continuous_const
  have hbU : b∈U := by change f.val (representative b)<0; simpa only [f,directionalNormalScalar_apply] using hbneg
  have hUD : Disjoint U D := by
    rw [Set.disjoint_left]
    intro x hx hd
    have hh := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1 x hd
    exact (not_lt_of_ge hh.le) hx
  have hUA : Disjoint U A := by
    rw [Set.disjoint_left]
    intro x hx ha
    have hh := (positiveNodalPiece_superlevels f isClosed_frontier hA).2.1 x ha
    exact (not_lt_of_ge hh.le) hx
  have hhom : ∀ z∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u z=0 :=
    isMinimizerAt_H1_unused_patch_homogeneous hV hE hmin hμ _ hs humem hmean hnull
      hU ⟨b,hbU,hbS⟩ (surfaceNodalBalance_zero_patch μ
        (nodalSurfaceJet_zero_outside μ f D U hDm hUD)
        (nodalSurfaceJet_zero_outside μ f A U hAm hUA))
  have hcl : IsClosed D := isMinimizerAt_nodal_splice_closed hV hE hmin hμ N hN hp hae hNu
    humem hhom (surfaceNodalBalanceValue_measurable μ f f D A hDm hAm)
    (surfaceNodalBalanceValue_continuousOn μ f f hDm hAm hD hA)
    (surfaceNodalBalanceValue_ae μ f f D A hDm hAm) v hD hapos.ne'
    (fun x hx => by
      rw [surfaceNodalBalanceValue_on_left μ f f D A hDm hAm hDA hx]
      exact congrArg (surfaceMean μ a * ·) (directionalNormalScalar_apply N hN hp v _))
    (fun x hx hz => surfaceNodalBalanceValue_nonpos μ f hDm hAm hD hA
      (by simpa only [f,directionalNormalScalar_apply] using hz))
  obtain ⟨W,hW,hDW⟩ := hD.eq_inter_open f
  have hcover : frontier (openRepresentative E)⊆W∪Dᶜ := by
    intro x hx
    by_cases hd : x∈D
    · left; rw [hDW] at hd; exact hd.2
    · exact Or.inr hd
  have hSW : (frontier (openRepresentative E)∩W).Nonempty := by rwa [← hDW]
  have hSc : (frontier (openRepresentative E)∩Dᶜ).Nonempty := by
    obtain ⟨x,hx⟩ := hAn
    exact ⟨x,hA.subset f hx,fun hd => Set.disjoint_left.mp hDA hd hx⟩
  obtain ⟨x,hxS,hxW,hxn⟩ := hS W Dᶜ hW hcl.isOpen_compl hcover hSW hSc
  apply hxn
  rw [hDW]
  exact ⟨hxS,hxW⟩

namespace Periodic

theorem isMinimizerAt_positive_nodal_unique {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ (v : Cover) (D A : Set Torus),
        IsPositiveNodalPiece (directionalNormalScalar N hN hp v) (frontier (openRepresentative E)) D →
        IsPositiveNodalPiece (directionalNormalScalar N hN hp v) (frontier (openRepresentative E)) A →
        D.Nonempty → A.Nonempty → ¬Disjoint D A := by
  obtain ⟨μ,H,N,hN,hp,hμ,hae,hb,hs,hj⟩ := isMinimizerAt_translation_positive_nodal hV hE hmin
  refine ⟨μ,N,hN,hp,hμ,hae,?_⟩
  intro v D A hD hA hDn hAn
  exact isMinimizerAt_positive_nodal_not_disjoint hV hE hmin hS hμ N hN hp hae
    (fun x hx => (hb x hx).1) hs v (hj v).2.1 hD hA hDn hAn
end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveBoundaryLocus_preconnected (f : smoothPeriodicScalars) (S : Set Torus)
    [LocallyConnectedSpace S]
    (h : ∀ D A : Set Torus,IsPositiveNodalPiece f S D → IsPositiveNodalPiece f S A →
      D.Nonempty → A.Nonempty → ¬Disjoint D A) :
    PreconnectedSpace (positiveBoundaryLocus f S) := by
  have he (a b : positiveBoundaryLocus f S) : connectedComponent a=connectedComponent b := by
    by_contra hn
    have hd := connectedComponent_disjoint hn
    apply h (positiveBoundaryDomain f S a) (positiveBoundaryDomain f S b)
      (positiveBoundaryDomain_isPositiveNodalPiece f S a)
      (positiveBoundaryDomain_isPositiveNodalPiece f S b)
      (positiveBoundaryDomain_nonempty f S a) (positiveBoundaryDomain_nonempty f S b)
    rw [Set.disjoint_left]
    rintro x ⟨c,hc,hcx⟩ ⟨d,hd',hdx⟩
    have hcd : c=d := Subtype.ext (Subtype.ext (hcx.trans hdx.symm))
    exact Set.disjoint_left.mp hd hc (hcd ▸ hd')
  rw [preconnectedSpace_iff_connectedComponent]
  intro a
  apply Set.eq_univ_of_forall
  intro b
  rw [he a b]
  exact mem_connectedComponent

namespace Periodic

theorem isMinimizerAt_translation_nodal_count {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hS : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ v : Cover,PreconnectedSpace
        (positiveBoundaryLocus (directionalNormalScalar N hN hp v)
          (frontier (openRepresentative E))) := by
  let F := toMeasurable torusVolume E
  have hae : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hae).mpr hmin
  have he : frontier (openRepresentative F)=frontier (openRepresentative E) :=
    congrArg frontier (openRepresentative_congr_ae hae)
  have hSF : IsPreconnected (frontier (openRepresentative F)) := by rwa [he]
  obtain ⟨μ,N,hN,hp,hμ,hNa,hunique⟩ := isMinimizerAt_positive_nodal_unique hV hF hmF hSF
  refine ⟨μ,N,hN,hp,hμ.congr_ae hae,hNa,?_⟩
  intro v
  rw [← he]
  let := isMinimizerAt_boundary_locallyConnected hV hF hmF
  exact positiveBoundaryLocus_preconnected _ _ (hunique v)

theorem isMinimizerAt_standard_slab_or_translation_nodal_count {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    (perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E) ∨
    (IsPreconnected (frontier (openRepresentative E)) ∧
      ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
        (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
        IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
        ∀ v : Cover,PreconnectedSpace
          (positiveBoundaryLocus (directionalNormalScalar N hN hp v)
            (frontier (openRepresentative E)))) := by
  obtain hc | hs := isMinimizerAt_connected_or_standard_slab hV hmin
  · exact Or.inr ⟨hc,isMinimizerAt_translation_nodal_count hV hmin hc⟩
  · exact Or.inl hs
end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma reflection_nodal_weak_sign {X : Type*} [TopologicalSpace X]
    (S : Set X) (r : X → X) (f s : X → ℝ)
    (hc : IsPreconnected {a | a∈S ∧ 0<f a}) (hs : Continuous s)
    (hr : ∀ a∈S,r a∈S) (hfo : ∀ a∈S,f (r a)= -f a)
    (hso : ∀ a,s (r a)= -s a) (hz : ∀ a∈S,s a=0 → f a=0) :
    (∀ a∈S,s a<0 → 0≤f a) ∨ (∀ a∈S,s a<0 → f a≤0) := by
  by_cases hpos : ∃ a∈S,s a<0 ∧ 0<f a
  · obtain ⟨a,ha,hsa,hfa⟩ := hpos
    left
    intro b hb hsb
    by_contra hn
    have hfb : f b<0 := lt_of_not_ge hn
    have hrb : 0<f (r b) := by rw [hfo b hb]; linarith
    have hsrb : 0<s (r b) := by rw [hso]; linarith
    obtain ⟨c,hcS,hcs⟩ := hc.intermediate_value ⟨ha,hfa⟩ ⟨hr b hb,hrb⟩ hs.continuousOn
      (show (0 : ℝ)∈Icc (s a) (s (r b)) from ⟨hsa.le,hsrb.le⟩)
    have hcf := hz c hcS.1 hcs
    exact (ne_of_gt hcS.2) hcf
  · right
    intro a ha hsa
    by_contra hn
    exact hpos ⟨a,ha,hsa,lt_of_not_ge hn⟩

lemma descent_coordinateSine_reflection (i : Fin 3) (a : Torus) :
    coordinateSine i (representative (coordinateReflection i a))= -coordinateSine i (representative a) := by
  rw [← quotientMap_representative a,← quotientMap_coordinateReflection,
    periodic_representative (coordinateSine_periodic i)]
  simp only [coordinateSine,coverCoordinateReflection_apply,ite_true,mul_neg,Real.sin_neg]
  rw [quotientMap_representative]

lemma positiveNormal_preconnected {E : Set Torus} {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (i : Fin 3)
    [PreconnectedSpace (positiveBoundaryLocus (directionalNormalScalar N hN hp (EuclideanSpace.single i 1))
      (frontier (openRepresentative E)))] :
    IsPreconnected {a | a∈frontier (openRepresentative E) ∧ 0<N (representative a) i} := by
  let f := directionalNormalScalar N hN hp (EuclideanSpace.single i 1)
  let S := frontier (openRepresentative E)
  let g : positiveBoundaryLocus f S → Torus := fun a => a.val.val
  have hg : Continuous g := continuous_subtype_val.comp continuous_subtype_val
  have he : Set.range g={a | a∈S ∧ 0<N (representative a) i} := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      refine ⟨b.val.property,?_⟩
      have hh := b.property
      simpa only [f,positiveBoundaryLocus,mem_ofPred_eq,directionalNormalScalar_apply,
        EuclideanSpace.inner_single_left,map_one,one_mul,g] using hh
    · rintro ⟨ha,hp'⟩
      refine ⟨⟨⟨a,ha⟩,?_⟩,rfl⟩
      simpa only [f,positiveBoundaryLocus,mem_ofPred_eq,directionalNormalScalar_apply,
        EuclideanSpace.inner_single_left,map_one,one_mul,g] using hp'
  rw [← he]
  exact isPreconnected_range hg

theorem isMinimizerAt_normal_coordinate_weak_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    [PreconnectedSpace (positiveBoundaryLocus (directionalNormalScalar N hN hp (EuclideanSpace.single i 1))
      (frontier (openRepresentative E)))] :
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,0≤N (representative a) i) ∨
    (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,N (representative a) i≤0) := by
  have hr : ∀ a∈frontier (openRepresentative E),coordinateReflection i a∈frontier (openRepresentative E) := by
    intro a ha
    change a∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
    rwa [frontier_reflection_invariant hE i hs]
  have hfo : ∀ a∈frontier (openRepresentative E),
      N (representative (coordinateReflection i a)) i= -N (representative a) i := by
    intro a ha
    have hh := congrArg (fun x : Cover => x i) (isMinimizerAt_normal_reflection hV hE hmE hμ hN hp hae i hs
      (representative a) (by rwa [quotientMap_representative]))
    simp only [coverCoordinateReflection_apply,ite_true] at hh
    rw [← periodic_representative hp (coverCoordinateReflection i (representative a)),
      quotientMap_coordinateReflection,quotientMap_representative] at hh
    linarith
  have hz : ∀ a∈frontier (openRepresentative E),coordinateSine i (representative a)=0 →
      N (representative a) i=0 := fun a ha hz =>
        isMinimizerAt_normal_coordinate_seam_zero hV hE hmE hμ hN hp hae i hs ha hz
  obtain h|h := reflection_nodal_weak_sign (frontier (openRepresentative E)) (coordinateReflection i)
    (fun a => N (representative a) i) (fun a => coordinateSine i (representative a))
    (positiveNormal_preconnected hN hp i)
    (continuous_periodic_descent (coordinateSine_contDiff i).continuous (coordinateSine_periodic i))
    hr hfo (descent_coordinateSine_reflection i) hz
  · left; intro a ha; exact h a ha.1 (by simpa only [coordinateHalf_zero,sublevelRegion,mem_ofPred_eq] using ha.2)
  · right; intro a ha; exact h a ha.1 (by simpa only [coordinateHalf_zero,sublevelRegion,mem_ofPred_eq] using ha.2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.nonneg_zero {g u : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {U : Set Plane} (hU : IsOpen U) (hc : IsPreconnected U)
    (hp : ∀ x∈U,‖gradient g x‖≤1) (hw : LinearCMCEquation u (gradient g) (fun _ => 0) U)
    (hn : ∀ x∈U,0≤u x) {a : Plane} (ha : a∈U) (hz : u a=0) :
    ∀ x∈U,u x=0 := by
  let D := {x : Plane | 0<u x}
  have hD : IsOpen D := isOpen_lt continuous_const hu.continuous
  have hfr : Disjoint U (frontier D) := by
    rw [disjoint_left]
    intro z hzU hzD
    obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU z hzU
    apply (hw.mono hεU).no_nodal_splice_frontier hg hu hD hε (by norm_num : (1 : ℝ)≠0)
      (fun x hx => hp x (hεU hx)) (fun x hx => hx.1) ?_ ?_ ?_
      (hu.differentiable (by simp)).differentiableOn hzD
    · intro x hx
      have h₁ : 0≤u x := hn x (hεU hx.2)
      have h₂ : ¬0<u x := by
        have hh : x∉D := by
          have ht := hx.1.2
          simpa only [hD.interior_eq] using ht
        exact hh
      exact le_antisymm (le_of_not_gt h₂) h₁
    · intro x _; simp only [one_mul]
    · intro x hx hux
      exact le_antisymm hux (hn x (hεU hx))
  intro x hx
  by_contra hnz
  have hpos : 0<u x := lt_of_le_of_ne (hn x hx) (Ne.symm hnz)
  obtain ⟨z,hzU,hzD⟩ := preconnected_crosses_frontier hc hD ⟨x,hx,hpos⟩ ⟨a,ha,by
    change ¬0<u a
    rw [hz]
    exact lt_irrefl _⟩
  exact disjoint_left.mp hfr hzU hzD

end CubicTorus

end
end

end OAI
