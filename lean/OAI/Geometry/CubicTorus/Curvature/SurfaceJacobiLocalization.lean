import Mathlib
import OAI.Geometry.CubicTorus.Profiles.MinimizerFirstTransitionTube

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma complex_eq_norm_smul_unitAngle (z : ℂ) :
    z=‖z‖ • unitAngle (Complex.arg z/(2*Real.pi)) := by
  have he : 2*Real.pi*(Complex.arg z/(2*Real.pi))=Complex.arg z := by
    field_simp [Real.pi_ne_zero]
  simp only [unitAngle,he,Complex.real_smul]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

lemma quotientMap_transverse_square (c : Cover) (q : Torus) :
    ∃ (t : ℝ) (z : ℂ),complexSquareGauge z≤1/2 ∧
      quotientMap (coordinateSectionPoint c t z)=q := by
  obtain ⟨x,rfl⟩ := quotientMap_surjective q
  let m : Fin 3 → ℤ := fun i => ⌊x i-c i+1/2⌋
  let y := x-latticeVector m
  let z : ℂ := ⟨y 1-c 1,y 2-c 2⟩
  have hb (i : Fin 3) : |y i-c i|≤1/2 := by
    have hl := Int.floor_le (x i-c i+1/2)
    have hu := Int.lt_floor_add_one (x i-c i+1/2)
    change |x i-(⌊x i-c i+1/2⌋ : ℝ)-c i|≤1/2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have he : coordinateSectionPoint c (y 0) z=y := by
    ext i
    fin_cases i <;> simp [z]
  refine ⟨y 0,z,max_le (hb 1) (hb 2),?_⟩
  rw [he]
  change quotientMap (x-latticeVector m)=quotientMap x
  rw [quotientMap_sub,quotientMap_latticeVector,sub_zero]

lemma norm_le_unitSquareScale_of_gauge {z : ℂ} (hz : complexSquareGauge z≤1/2) :
    ‖z‖≤unitSquareScale (Complex.arg z/(2*Real.pi)) := by
  let a := Complex.arg z/(2*Real.pi)
  have he := complex_eq_norm_smul_unitAngle z
  have hg : complexSquareGauge z=‖z‖*complexSquareGauge (unitAngle a) := by
    conv_lhs => rw [he]
    exact complexSquareGauge_smul (norm_nonneg _) _
  rw [hg] at hz
  change ‖z‖≤1/(2*complexSquareGauge (unitAngle a))
  apply (le_div_iff₀ (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero a)))).mpr
  nlinarith

theorem TrueRadialTube.boundary_range {E : Set Torus} {c : Cover} {r : ℝ × ℝ → ℝ}
    (hr : TrueRadialTube E c r) :
    Set.range (fun p : ℝ × ℝ => quotientMap (coordinateSectionPoint c p.1
      (r p • unitAngle p.2)))=frontier (openRepresentative E) := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    exact hr.2.2.2.2.1 p
  · intro hq
    obtain ⟨t,z,hz,he⟩ := quotientMap_transverse_square c q
    let a := Complex.arg z/(2*Real.pi)
    have hpolar : z=‖z‖ • unitAngle a := complex_eq_norm_smul_unitAngle z
    have hbound : ‖z‖≤unitSquareScale a := norm_le_unitSquareScale_of_gauge hz
    have hb : quotientMap (coordinateSectionPoint c t (‖z‖ • unitAngle a))∈
        frontier (openRepresentative E) := by rwa [← hpolar,he]
    rw [(isOpen_openRepresentative E).frontier_eq] at hb
    have hle : ‖z‖≤r (t,a) := (hr.2.2.2.2.2.2.1 (t,a) ‖z‖ (norm_nonneg _) hbound).mp hb.1
    have hge : r (t,a)≤‖z‖ := le_of_not_gt (fun hh =>
      hb.2 ((hr.2.2.2.2.2.1 (t,a) ‖z‖ (norm_nonneg _) hbound).mpr hh))
    have hn : r (t,a)=‖z‖ := le_antisymm hge hle
    exact ⟨(t,a),by simpa only [hn,← hpolar] using he⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma pair_periodic_descend {X : Type*} [TopologicalSpace X] {f : ℝ × ℝ → X}
    (hf : Continuous f) (hp1 : ∀ t a,f (t+1,a)=f (t,a))
    (hp2 : ∀ t a,f (t,a+1)=f (t,a)) :
    ∃ F : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → X,Continuous F ∧
      ∀ (t a : ℝ),F ((t : AddCircle (1 : ℝ)),(a : AddCircle (1 : ℝ)))=f (t,a) := by
  let g : ℝ → AddCircle (1 : ℝ) → X := fun t => (show Function.Periodic (fun a => f (t,a)) 1 from hp2 t).lift
  have hgp : Function.Periodic g 1 := by
    intro t
    funext a
    induction a using QuotientAddGroup.induction_on with | H a =>
      exact hp1 t a
  let F : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → X := fun p => hgp.lift p.1 p.2
  have he (t a : ℝ) : F ((t : AddCircle (1 : ℝ)),(a : AddCircle (1 : ℝ)))=f (t,a) := rfl
  refine ⟨F,?_,he⟩
  have hq : IsOpenQuotientMap (fun t : ℝ => (t : AddCircle (1 : ℝ))) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  apply (hq.prodMap hq).isQuotientMap.continuous_iff.mpr
  exact hf

lemma transverse_square_quotient_injective {c : Cover} {t u : ℝ} {z w : ℂ}
    (hz : complexSquareGauge z<1/2) (hw : complexSquareGauge w<1/2)
    (he : quotientMap (coordinateSectionPoint c t z)=
      quotientMap (coordinateSectionPoint c u w)) : z=w := by
  have hz1 : |z.re|<1/2 := (le_max_left _ _).trans_lt hz
  have hz2 : |z.im|<1/2 := (le_max_right _ _).trans_lt hz
  have hw1 : |w.re|<1/2 := (le_max_left _ _).trans_lt hw
  have hw2 : |w.im|<1/2 := (le_max_right _ _).trans_lt hw
  have hc (b x y : ℝ) (hx : |x|<1/2) (hy : |y|<1/2)
      (he : ((b+x : ℝ) : AddCircle (1 : ℝ))=((b+y : ℝ) : AddCircle (1 : ℝ))) : x=y := by
    have hxi : b+x∈Ico (b-1/2) (b-1/2+1) :=
      ⟨by linarith [(abs_lt.mp hx).1],by linarith [(abs_lt.mp hx).2]⟩
    have hyi : b+y∈Ico (b-1/2) (b-1/2+1) :=
      ⟨by linarith [(abs_lt.mp hy).1],by linarith [(abs_lt.mp hy).2]⟩
    have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico hxi hyi).mp he
    linarith
  apply Complex.ext
  · apply hc (c 1) z.re w.re hz1 hw1
    have hh := congrArg (fun x : Torus => x 1) he
    simpa [quotientMap] using hh
  · apply hc (c 2) z.im w.im hz2 hw2
    have hh := congrArg (fun x : Torus => x 2) he
    simpa [quotientMap] using hh

lemma radial_point_gauge_lt {r a : ℝ} (hr : 0<r) (hrs : r<unitSquareScale a) :
    complexSquareGauge (r • unitAngle a)<1/2 := by
  rw [complexSquareGauge_smul hr.le]
  have hd : 0<complexSquareGauge (unitAngle a) := complexSquareGauge_pos (unitAngle_ne_zero a)
  change r<1/(2*complexSquareGauge (unitAngle a)) at hrs
  have hh := (lt_div_iff₀ (mul_pos (by norm_num) hd)).mp hrs
  nlinarith

lemma unitAngle_eq_iff_addCircle (a b : ℝ) :
    unitAngle a=unitAngle b ↔ (a : AddCircle (1 : ℝ))=(b : AddCircle (1 : ℝ)) := by
  constructor
  · intro he
    apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ)≠0)
    apply Subtype.ext
    simpa [AddCircle.toCircle_apply_mk,Circle.coe_exp,unitAngle] using he
  · intro he
    have hh := congrArg (fun q : AddCircle (1 : ℝ) => (AddCircle.toCircle q : ℂ)) he
    simpa [AddCircle.toCircle_apply_mk,Circle.coe_exp,unitAngle] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem TrueRadialTube.homeomorphic_torus {E : Set Torus} {c : Cover} {r : ℝ × ℝ → ℝ}
    (hr : TrueRadialTube E c r) :
    Nonempty ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₜ
      ↥(frontier (openRepresentative E))) := by
  let f : ℝ × ℝ → Torus := fun p => quotientMap
    (coordinateSectionPoint c p.1 (r p • unitAngle p.2))
  have hfc : Continuous f := continuous_quotientMap.comp
    ((coordinateSectionPoint_continuous_pair c).comp
      (continuous_fst.prodMk (hr.1.continuous.smul (unitAngle_continuous.comp continuous_snd))))
  have hfp1 (t a : ℝ) : f (t+1,a)=f (t,a) := by
    dsimp only [f]
    rw [hr.2.1 t a]
    simpa using quotientMap_coordinateSectionPoint_int c t (r (t,a) • unitAngle a) 1
  have hfp2 (t a : ℝ) : f (t,a+1)=f (t,a) := by
    dsimp only [f]
    rw [hr.2.2.1 t a,unitAngle_periodic a]
  obtain ⟨F,hFc,hFe⟩ := pair_periodic_descend hfc hfp1 hfp2
  have hmem (p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :
      F p∈frontier (openRepresentative E) := by
    rcases p with ⟨t,a⟩
    induction t using QuotientAddGroup.induction_on with | H t =>
      induction a using QuotientAddGroup.induction_on with | H a =>
        rw [hFe]
        exact hr.2.2.2.2.1 (t,a)
  let g : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → ↥(frontier (openRepresentative E)) :=
    fun p => ⟨F p,hmem p⟩
  have hgc : Continuous g := hFc.subtype_mk hmem
  have hgi : Function.Injective g := by
    rintro ⟨t,a⟩ ⟨u,b⟩
    induction t using QuotientAddGroup.induction_on with | H t =>
      induction a using QuotientAddGroup.induction_on with | H a =>
        induction u using QuotientAddGroup.induction_on with | H u =>
          induction b using QuotientAddGroup.induction_on with | H b =>
            intro he
            have hf : f (t,a)=f (u,b) := by
              have hh := congrArg Subtype.val he
              change F (↑t,↑a)=F (↑u,↑b) at hh
              simpa only [hFe] using hh
            have ht : (t : AddCircle (1 : ℝ))=(u : AddCircle (1 : ℝ)) := by
              have hh := congrArg (fun q : Torus => q 0) hf
              simpa [f,quotientMap] using hh
            have hz : r (t,a) • unitAngle a=r (u,b) • unitAngle b :=
              transverse_square_quotient_injective
                (radial_point_gauge_lt (hr.2.2.2.1 (t,a)).1 (hr.2.2.2.1 (t,a)).2)
                (radial_point_gauge_lt (hr.2.2.2.1 (u,b)).1 (hr.2.2.2.1 (u,b)).2) hf
            have hrad : r (t,a)=r (u,b) := by
              have hn := congrArg norm hz
              simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (hr.2.2.2.1 (t,a)).1,
                abs_of_pos (hr.2.2.2.1 (u,b)).1,unitAngle_norm,mul_one] using hn
            have huangle : unitAngle a=unitAngle b := by
              rw [hrad] at hz
              have hh := congrArg (fun z : ℂ => (r (u,b))⁻¹ • z) hz
              simpa only [smul_smul,inv_mul_cancel₀ (hr.2.2.2.1 (u,b)).1.ne',one_smul] using hh
            exact Prod.ext ht ((unitAngle_eq_iff_addCircle a b).mp huangle)
  have hgs : Function.Surjective g := by
    intro q
    have hh : q.val∈range f := by
      rw [show range f=frontier (openRepresentative E) from hr.boundary_range]
      exact q.property
    obtain ⟨p,hp⟩ := hh
    refine ⟨(↑p.1,↑p.2),Subtype.ext ?_⟩
    exact (hFe p.1 p.2).trans hp
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hgi,hgs⟩) hgc⟩

theorem isMinimizerAt_first_transition_nonstandard_torus
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (v : Torus) (F : Set Torus) (e : Fin 3 ≃ Fin 3) (c : Cover) (r : ℝ × ℝ → ℝ),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+v) ⁻¹' E) ∧
      IsMinimizerAt (4*Real.pi/81) (torusCoordinatePermute e ⁻¹' F) ∧
      TrueRadialTube (torusCoordinatePermute e ⁻¹' F) c r ∧
      Nonempty ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₜ
        ↥(frontier (openRepresentative (torusCoordinatePermute e ⁻¹' F)))) := by
  obtain ⟨v,F,e,c,r,hF,he,hm,hr⟩ := isMinimizerAt_first_transition_nonstandard_smooth_tube hmE hnstd
  exact ⟨v,F,e,c,r,hF,he,hm,hr,hr.homeomorphic_torus⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma congruentAE_of_coordinatePermute {E C : Set Torus} (e : Fin 3 ≃ Fin 3)
    (hc : CongruentAE (torusCoordinatePermute e ⁻¹' E) C) : CongruentAE E C := by
  obtain ⟨φ,hφ⟩ := hc
  refine ⟨φ.trans (torusCoordinatePermute e),?_⟩
  have hh := (torusCoordinatePermute_measurePreserving e.symm).quasiMeasurePreserving.preimage_ae_eq hφ
  filter_upwards [hh] with x hx
  change (torusCoordinatePermute e (torusCoordinatePermute e.symm x)∈E)=
    (torusCoordinatePermute e.symm x∈φ '' C) at hx
  rw [torusCoordinatePermute_inverse] at hx
  rw [hx]
  apply propext
  constructor
  · rintro ⟨y,hy,he⟩
    refine ⟨y,hy,?_⟩
    change torusCoordinatePermute e (φ y)=x
    rw [he,torusCoordinatePermute_inverse]
  · rintro ⟨y,hy,he⟩
    refine ⟨y,hy,?_⟩
    change torusCoordinatePermute e (φ y)=x at he
    rw [← he]
    simpa only [Equiv.symm_symm] using (torusCoordinatePermute_inverse e.symm (φ y)).symm

lemma smallStandardRegion_of_coordinatePermute {V : ℝ} {E : Set Torus}
    (e : Fin 3 ≃ Fin 3) (h : SmallStandardRegion V (torusCoordinatePermute e ⁻¹' E)) :
    SmallStandardRegion V E := by
  rcases h with ⟨hV,h⟩|⟨hV,hW,h⟩|⟨hV,h⟩
  · exact Or.inl ⟨hV,congruentAE_of_coordinatePermute e h⟩
  · exact Or.inr (Or.inl ⟨hV,hW,congruentAE_of_coordinatePermute e h⟩)
  · exact Or.inr (Or.inr ⟨hV,congruentAE_of_coordinatePermute e h⟩)

lemma smallStandardRegion_of_translated {V : ℝ} {E F : Set Torus} {v : Torus}
    (he : F =ᵐ[torusVolume] ((fun z => z+v) ⁻¹' E))
    (h : SmallStandardRegion V F) : SmallStandardRegion V E := by
  rcases h with ⟨hV,h⟩|⟨hV,hW,h⟩|⟨hV,h⟩
  · exact Or.inl ⟨hV,congruentAE_of_translated he h⟩
  · exact Or.inr (Or.inl ⟨hV,hW,congruentAE_of_translated he h⟩)
  · exact Or.inr (Or.inr ⟨hV,congruentAE_of_translated he h⟩)

theorem isMinimizerAt_first_transition_nonstandard_toroidal_reduction
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (G : Set Torus) (c : Cover) (r : ℝ × ℝ → ℝ),
      MeasurableSet G ∧ IsMinimizerAt (4*Real.pi/81) G ∧
      ¬SmallStandardRegion (4*Real.pi/81) G ∧ TrueRadialTube G c r ∧
      Nonempty ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₜ
        ↥(frontier (openRepresentative G))) := by
  obtain ⟨v,F,e,c,r,hF,he,hm,hr,ht⟩ :=
    isMinimizerAt_first_transition_nonstandard_torus hmE hnstd
  refine ⟨torusCoordinatePermute e ⁻¹' F,c,r,
    (torusCoordinatePermute e).continuous.measurable hF,hm,?_,hr,ht⟩
  intro hs
  exact hnstd (smallStandardRegion_of_translated he (smallStandardRegion_of_coordinatePermute e hs))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def surfaceCutoffError (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (u : SurfaceJet μ) : Lp Cover 2 (μ : Measure NormalBundle) :=
  surfaceGradientMultiplier μ
    (ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarGradient f)) u.1

lemma surfaceCutoffError_ae (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars)
    (u : SurfaceJet μ) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),
      surfaceCutoffError μ f u z = u.1 z • smoothScalarGradient f z := by
  let g := ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarGradient f)
  filter_upwards [Lp.coeFn_lpSMul (r := 2) u.1 g,
    (smoothScalarGradient f).coeFn_toLp (p := ∞) (𝕜 := ℝ) (μ : Measure NormalBundle)]
    with z hz hg
  change (u.1 • g : Lp Cover 2 (μ : Measure NormalBundle)) z = _
  rw [hz]
  change u.1 z • g z = _
  change g z = smoothScalarGradient f z at hg
  rw [hg]

theorem surfaceJacobiB_cutoff_identity (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (u : SurfaceJet μ) :
    surfaceJacobiB μ q (surfaceCutoffJet μ f u) (surfaceCutoffJet μ f u) =
      surfaceJacobiB μ q u (surfaceCutoffJet μ (smoothScalarMul f f) u) +
        ‖surfaceCutoffError μ f u‖^2 := by
  let v := surfaceCutoffJet μ f u
  let w := surfaceCutoffJet μ (smoothScalarMul f f) u
  let e := surfaceCutoffError μ f u
  have hp : ⟪surfaceMultiplier μ q v.1, v.1⟫ =
      ⟪surfaceMultiplier μ q u.1, w.1⟫ := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [surfaceCutoffJet_ae μ f u,
      surfaceCutoffJet_ae μ (smoothScalarMul f f) u,
      Lp.coeFn_lpSMul (r := 2) q v.1, Lp.coeFn_lpSMul (r := 2) q u.1]
      with z hv hw hqv hqu
    change ⟪(q • v.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z, v.1 z⟫ =
      ⟪(q • u.1 : Lp ℝ 2 (μ : Measure NormalBundle)) z, w.1 z⟫
    rw [hqv, hqu]
    change (v.1 z) * (q z * v.1 z) = (w.1 z) * (q z * u.1 z)
    obtain ⟨hv, -⟩ := hv
    obtain ⟨hw, -⟩ := hw
    change v.1 z = f.val z.1 * u.1 z at hv
    change w.1 z = (f.val z.1 * f.val z.1) * u.1 z at hw
    rw [hv, hw]
    ring
  have hg : ⟪v.2, v.2⟫ = ⟪u.2, w.2⟫ + ⟪e,e⟫ := by
    rw [L2.inner_def, L2.inner_def, L2.inner_def,
      ← integral_add (L2.integrable_inner u.2 w.2) (L2.integrable_inner e e)]
    apply integral_congr_ae
    filter_upwards [surfaceCutoffJet_ae μ f u,
      surfaceCutoffJet_ae μ (smoothScalarMul f f) u,
      surfaceCutoffError_ae μ f u] with z hv hw he
    obtain ⟨-, hv⟩ := hv
    obtain ⟨-, hw⟩ := hw
    change v.2 z = _ at hv
    change w.2 z = _ at hw
    change e z = _ at he
    rw [hv, hw, he, smoothScalarGradient_mul]
    simp only [smoothScalarMul, Pi.mul_apply, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm (smoothScalarGradient f z) (u.2 z)]
    ring
  change ⟪v.2,v.2⟫ - ⟪surfaceMultiplier μ q v.1,v.1⟫ =
    (⟪u.2,w.2⟫ - ⟪surfaceMultiplier μ q u.1,w.1⟫) + ‖e‖^2
  rw [hp, hg, real_inner_self_eq_norm_sq]
  ring

theorem surfaceH1_jacobi_cutoff_energy (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ}
    (hu : u ∈ surfaceH1 μ)
    (hweak : ∀ v ∈ surfaceH1 μ, surfaceJacobiB μ q u v = 0)
    (f : smoothPeriodicScalars) :
    ‖(surfaceCutoffJet μ f u).2‖^2 ≤
      ‖q‖ * ‖(surfaceCutoffJet μ f u).1‖^2 + ‖surfaceCutoffError μ f u‖^2 := by
  have h := surfaceJacobiB_cutoff_identity μ q f u
  rw [hweak _ (surfaceCutoffJet_mem_surfaceH1 μ (smoothScalarMul f f) hu), zero_add] at h
  have hp : ⟪surfaceMultiplier μ q (surfaceCutoffJet μ f u).1,
      (surfaceCutoffJet μ f u).1⟫ ≤ ‖q‖ * ‖(surfaceCutoffJet μ f u).1‖^2 := by
    calc
      _ ≤ ‖surfaceMultiplier μ q (surfaceCutoffJet μ f u).1‖ *
          ‖(surfaceCutoffJet μ f u).1‖ := real_inner_le_norm _ _
      _ ≤ (‖q‖ * ‖(surfaceCutoffJet μ f u).1‖) *
          ‖(surfaceCutoffJet μ f u).1‖ :=
        mul_le_mul_of_nonneg_right (Lp.norm_smul_le q _) (norm_nonneg _)
      _ = _ := by ring
  unfold surfaceJacobiB at h
  rw [real_inner_self_eq_norm_sq] at h
  linarith

theorem surfaceH1_jacobi_caccioppoli (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) {u : SurfaceJet μ}
    (hu : u ∈ surfaceH1 μ)
    (hweak : ∀ v ∈ surfaceH1 μ, surfaceJacobiB μ q u v = 0)
    (f : smoothPeriodicScalars) :
    ‖surfaceVectorMultiplier μ
      (ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarValue f)) u.2‖^2 ≤
      2 * ‖q‖ * ‖(surfaceCutoffJet μ f u).1‖^2 + 4 * ‖surfaceCutoffError μ f u‖^2 := by
  let a := surfaceVectorMultiplier μ
    (ContinuousMap.toLp ∞ (μ : Measure NormalBundle) ℝ (smoothScalarValue f)) u.2
  let e := surfaceCutoffError μ f u
  let v := surfaceCutoffJet μ f u
  have hv : v.2 = a + e := rfl
  have ht : ‖a‖ ≤ ‖v.2‖ + ‖e‖ := by
    calc
      ‖a‖ = ‖v.2 - e‖ := by rw [hv, add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  have hs : ‖a‖^2 ≤ (‖v.2‖ + ‖e‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) ht 2
  have he := surfaceH1_jacobi_cutoff_energy μ q hu hweak f
  change ‖v.2‖^2 ≤ ‖q‖ * ‖v.1‖^2 + ‖e‖^2 at he
  change ‖a‖^2 ≤ 2 * ‖q‖ * ‖v.1‖^2 + 4 * ‖e‖^2
  nlinarith [sq_nonneg (‖v.2‖ - ‖e‖)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceJacobiB_cutoff_commutator (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (u v : SurfaceJet μ) :
    surfaceJacobiB μ q (surfaceCutoffJet μ f u) v -
      surfaceJacobiB μ q u (surfaceCutoffJet μ f v) =
        ⟪surfaceCutoffError μ f u,v.2⟫ - ⟪u.2,surfaceCutoffError μ f v⟫ := by
  let a := surfaceCutoffJet μ f u
  let b := surfaceCutoffJet μ f v
  let e := surfaceCutoffError μ f u
  let d := surfaceCutoffError μ f v
  have hp : ⟪surfaceMultiplier μ q a.1,v.1⟫ =
      ⟪surfaceMultiplier μ q u.1,b.1⟫ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [surfaceCutoffJet_ae μ f u,surfaceCutoffJet_ae μ f v,
      Lp.coeFn_lpSMul (r := 2) q a.1,Lp.coeFn_lpSMul (r := 2) q u.1]
      with z ha hb hqa hqu
    change (surfaceMultiplier μ q a.1) z=(q z)*(a.1 z) at hqa
    change (surfaceMultiplier μ q u.1) z=(q z)*(u.1 z) at hqu
    change (v.1 z)*((surfaceMultiplier μ q a.1) z)=
      (b.1 z)*((surfaceMultiplier μ q u.1) z)
    rw [hqa,hqu]
    have ha' : a.1 z=f.val z.1*u.1 z := ha.1
    have hb' : b.1 z=f.val z.1*v.1 z := hb.1
    rw [ha',hb']
    ring
  have hg : ⟪a.2,v.2⟫ - ⟪u.2,b.2⟫ = ⟪e,v.2⟫ - ⟪u.2,d⟫ := by
    rw [L2.inner_def,L2.inner_def,L2.inner_def,L2.inner_def,
      ← integral_sub (L2.integrable_inner a.2 v.2) (L2.integrable_inner u.2 b.2),
      ← integral_sub (L2.integrable_inner e v.2) (L2.integrable_inner u.2 d)]
    apply integral_congr_ae
    filter_upwards [surfaceCutoffJet_ae μ f u,surfaceCutoffJet_ae μ f v,
      surfaceCutoffError_ae μ f u,surfaceCutoffError_ae μ f v]
      with z ha hb he hd
    have ha' : a.2 z=f.val z.1 • u.2 z+u.1 z • smoothScalarGradient f z := ha.2
    have hb' : b.2 z=f.val z.1 • v.2 z+v.1 z • smoothScalarGradient f z := hb.2
    change e z=_ at he
    change d z=_ at hd
    rw [ha',hb',he,hd]
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
    ring
  change (⟪a.2,v.2⟫-⟪surfaceMultiplier μ q a.1,v.1⟫)-
    (⟪u.2,b.2⟫-⟪surfaceMultiplier μ q u.1,b.1⟫)=⟪e,v.2⟫-⟪u.2,d⟫
  rw [hp]
  linarith only [hg]

theorem surfaceH1_jacobi_cutoff_commutator (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    {u : SurfaceJet μ} (hu : ∀ w∈surfaceH1 μ,surfaceJacobiB μ q u w=0)
    {v : SurfaceJet μ} (hv : v∈surfaceH1 μ) :
    surfaceJacobiB μ q (surfaceCutoffJet μ f u) v =
      ⟪surfaceCutoffError μ f u,v.2⟫-⟪u.2,surfaceCutoffError μ f v⟫ := by
  have h := surfaceJacobiB_cutoff_commutator μ q f u v
  rw [hu _ (surfaceCutoffJet_mem_surfaceH1 μ f hv),sub_zero] at h
  exact h

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem exists_periodic_local_identity {R : ℝ} (hR : 0≤R) (hR' : R<1/2) :
    ∃ g : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧
      ∀ x,|x|≤R → g =ᶠ[𝓝 x] id := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨(R+1/2)/2,((R+1/2)/2+1/2)/2,by linarith,by linarith⟩
  let f : ℝ → ℝ := fun x => b x*x
  have hc : HasCompactSupport f := b.hasCompactSupport.mul_right
  have hs : tsupport f ⊆ Ioo ((0 : ℝ)-1/2) (0+1/2) := by
    intro x hx
    have hh : x∈tsupport (b : ℝ → ℝ) := tsupport_mul_subset_left hx
    rw [b.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
    change |x|≤((R+1/2)/2+1/2)/2 at hh
    exact ⟨by linarith [(abs_le.mp hh).1],by linarith [(abs_le.mp hh).2]⟩
  refine ⟨circlePeriodize f,circlePeriodize_contDiff (b.contDiff.mul contDiff_id) hc,
    circlePeriodize_periodic f,?_⟩
  intro x hx
  have hb : (b : ℝ → ℝ) =ᶠ[𝓝 x] 1 := b.eventuallyEq_one_of_mem_ball (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    change |x|<(R+1/2)/2
    linarith)
  have hp := circlePeriodize_eventuallyEq hc hs (x := x)
    (show x∈Icc ((0 : ℝ)-1/2) (0+1/2) from
      ⟨by linarith [(abs_le.mp hx).1],by linarith [(abs_le.mp hx).2]⟩)
  filter_upwards [hp,hb] with y hy hby
  simpa [f,hby] using hy

theorem TrueRadialTube.uniform_square_gap {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ R : ℝ,0≤R ∧ R<1/2 ∧
      ∀ p,complexSquareGauge (r p • unitAngle p.2)≤R := by
  let f : ℝ × ℝ → ℝ := fun p => complexSquareGauge (r p • unitAngle p.2)
  have hf : Continuous f := complexSquareGauge_continuous.comp
    (hr.1.continuous.smul (unitAngle_continuous.comp continuous_snd))
  obtain ⟨F,hF,he⟩ := pair_periodic_descend hf (by
    intro t a
    change complexSquareGauge (r (t+1,a) • unitAngle a)=_
    rw [hr.2.1]) (by
    intro t a
    change complexSquareGauge (r (t,a+1) • unitAngle (a+1))=_
    rw [hr.2.2.1,unitAngle_periodic])
  have hb (p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) : 0≤F p ∧ F p<1/2 := by
    rcases p with ⟨t,a⟩
    induction t using QuotientAddGroup.induction_on with | H t =>
      induction a using QuotientAddGroup.induction_on with | H a =>
        rw [he]
        refine ⟨(abs_nonneg _).trans (le_max_left _ _),?_⟩
        exact radial_point_gauge_lt (hr.2.2.2.1 (t,a)).1 (hr.2.2.2.1 (t,a)).2
  obtain ⟨p,_,hp⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hF.continuousOn
  refine ⟨F p,(hb p).1,(hb p).2,?_⟩
  intro q
  change f (q.1,q.2)≤F p
  rw [← he q.1 q.2]
  exact hp (Set.mem_univ _)

theorem TrueRadialTube.periodic_transverse_germs {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ g : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.Periodic g 1 ∧
      ∀ p,(g =ᶠ[𝓝 (r p • unitAngle p.2).re] id) ∧
        (g =ᶠ[𝓝 (r p • unitAngle p.2).im] id) := by
  obtain ⟨R,hR,hR',hb⟩ := hr.uniform_square_gap
  obtain ⟨g,hg,hp,he⟩ := exists_periodic_local_identity hR hR'
  refine ⟨g,hg,hp,fun p => ⟨he _ ?_,he _ ?_⟩⟩
  · exact (le_max_left _ _).trans (hb p)
  · exact (le_max_right _ _).trans (hb p)

def periodicCoordinate (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (j : Fin 3) : smoothPeriodicScalars := by
  refine ⟨fun x => g (x j-c j),hg.comp ((EuclideanSpace.proj j : Cover →L[ℝ] ℝ).contDiff.sub contDiff_const),?_⟩
  intro m x
  change g (x j+(m j : ℝ)-c j)=g (x j-c j)
  convert hp.int_mul (m j) (x j-c j) using 1; congr 1; ring

lemma periodicCoordinate_germ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (j : Fin 3) (x : Cover) (m : ℤ)
    (he : g =ᶠ[𝓝 (x j-c j-m)] id) :
    (periodicCoordinate g hg hp c j).val =ᶠ[𝓝 x] (fun y => y j-c j-m) := by
  have ht : Continuous (fun y : Cover => y j-c j-(m : ℝ)) :=
    (EuclideanSpace.proj j).continuous.sub continuous_const |>.sub continuous_const
  have hh := he.comp_tendsto ht.continuousAt
  filter_upwards [hh] with y hy
  change g (y j-c j-m)=y j-c j-m at hy
  change g (y j-c j)=y j-c j-m
  have hp' := hp.sub_int_mul_eq (x := y j-c j) m
  simp only [mul_one] at hp'
  rw [hp'] at hy
  exact hy

theorem TrueRadialTube.ambient_transverse_germs {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ f₁ f₂ : smoothPeriodicScalars,∀ x : Cover,
      quotientMap x∈frontier (openRepresentative E) → ∃ m : Fin 3 → ℤ,
        (f₁.val =ᶠ[𝓝 x] (fun y => y 1-c 1-m 1)) ∧
        (f₂.val =ᶠ[𝓝 x] (fun y => y 2-c 2-m 2)) := by
  obtain ⟨g,hg,hp,he⟩ := hr.periodic_transverse_germs
  refine ⟨periodicCoordinate g hg hp c 1,periodicCoordinate g hg hp c 2,?_⟩
  intro x hx
  rw [← hr.boundary_range] at hx
  obtain ⟨p,hpx⟩ := hx
  obtain ⟨m,hm⟩ := same_quotient_lattice hpx.symm
  have h₁ : x 1-c 1-(m 1 : ℝ)=(r p • unitAngle p.2).re := by
    rw [hm]
    simp [latticeVector]
    ring
  have h₂ : x 2-c 2-(m 2 : ℝ)=(r p • unitAngle p.2).im := by
    rw [hm]
    simp [latticeVector]
    ring
  exact ⟨m,periodicCoordinate_germ g hg hp c 1 x (m 1) (by rw [h₁]; exact (he p).1),
    periodicCoordinate_germ g hg hp c 2 x (m 2) (by rw [h₂]; exact (he p).2)⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodicCoordinate_cross_derivative (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1)
    (c x : Cover) {i j : Fin 3} (hij : i≠j) :
    fderiv ℝ (periodicCoordinate g hg hp c j).val x (EuclideanSpace.single i 1)=0 := by
  have hd := ((hg.differentiable (by simp) (x j-c j)).hasFDerivAt).comp x
    ((EuclideanSpace.proj j : Cover →L[ℝ] ℝ).hasFDerivAt.sub_const (c j))
  change HasFDerivAt (periodicCoordinate g hg hp c j).val
    ((fderiv ℝ g (x j-c j)).comp (EuclideanSpace.proj j)) x at hd
  rw [hd.fderiv]
  simp [Ne.symm hij]

def periodicRotation (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (x : Cover) : Cover :=
  (periodicCoordinate g hg hp c 1).val x • EuclideanSpace.single 2 1-
    (periodicCoordinate g hg hp c 2).val x • EuclideanSpace.single 1 1

lemma periodicRotation_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicRotation g hg hp c) :=
  ((periodicCoordinate g hg hp c 1).property.1.smul contDiff_const).sub
    ((periodicCoordinate g hg hp c 2).property.1.smul contDiff_const)

lemma periodicRotation_periodic (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (m : Fin 3 → ℤ) (x : Cover) :
    periodicRotation g hg hp c (x+latticeVector m)=periodicRotation g hg hp c x := by
  simp only [periodicRotation,(periodicCoordinate g hg hp c 1).property.2 m x,
    (periodicCoordinate g hg hp c 2).property.2 m x]

lemma periodicRotation_divergence (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c x : Cover) :
    divergence (periodicRotation g hg hp c) x=0 := by
  have h₁ := (periodicCoordinate g hg hp c 1).property.1.differentiable (by simp) x
  have h₂ := (periodicCoordinate g hg hp c 2).property.1.differentiable (by simp) x
  unfold periodicRotation
  rw [divergence_sub_fields (h₁.smul_const _) (h₂.smul_const _),
    divergence_smul_const h₁,divergence_smul_const h₂,
    periodicCoordinate_cross_derivative g hg hp c x (by decide : (2 : Fin 3)≠1),
    periodicCoordinate_cross_derivative g hg hp c x (by decide : (1 : Fin 3)≠2),sub_self]

theorem periodicRotation_normal_flux_zero {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1) (c : Cover) :
    (∫ z,⟪(z.2 : Cover),periodicRotation g hg hp c z.1⟫ ∂(μ : Measure NormalBundle))=0 := by
  have hF := periodicRotation_contDiff g hg hp c
  have hFp := periodicRotation_periodic g hg hp c
  obtain ⟨k,hk,hb⟩ := periodic_bounded hF.continuous hFp
  have hh := normalMeasure_flux hμ hF hFp (show 0<k+1 by linarith)
    (fun x => (hb x).trans (by linarith : k≤k+1))
  simpa only [normalTest,ContinuousMap.coe_mk,periodicRotation_divergence,integral_zero] using hh

def periodicRotationNormalScalar (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : Function.Periodic g 1) (c : Cover) (N : Cover → Cover)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hNp : ∀ m x,N (x+latticeVector m)=N x) :
    smoothPeriodicScalars := by
  refine ⟨fun x => ⟪N x,periodicRotation g hg hp c x⟫,
    hN.inner ℝ (periodicRotation_contDiff g hg hp c),?_⟩
  intro m x
  dsimp only
  rw [hNp,periodicRotation_periodic]

theorem periodicRotationNormalScalar_mean_zero {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1)
    (c : Cover) (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hNp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    surfaceMean μ (surfaceSmoothJet μ (periodicRotationNormalScalar g hg hp c N hN hNp))=0 := by
  rw [surfaceMean_of_smooth,← periodicRotation_normal_flux_zero hμ g hg hp c]
  apply integral_congr_ae
  filter_upwards [ha] with z hz
  change ⟪N z.1,periodicRotation g hg hp c z.1⟫=⟪(z.2 : Cover),periodicRotation g hg hp c z.1⟫
  rw [hz]

theorem TrueRadialTube.periodic_rotation_germs {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r) :
    ∃ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hp : Function.Periodic g 1),
      ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ∃ m : Fin 3 → ℤ,
        periodicRotation g hg hp c =ᶠ[𝓝 x] (fun y =>
          (y 1-c 1-m 1) • EuclideanSpace.single 2 1-
            (y 2-c 2-m 2) • EuclideanSpace.single 1 1) := by
  obtain ⟨g,hg,hp,he⟩ := hr.periodic_transverse_germs
  refine ⟨g,hg,hp,?_⟩
  intro x hx
  rw [← hr.boundary_range] at hx
  obtain ⟨p,hpx⟩ := hx
  obtain ⟨m,hm⟩ := same_quotient_lattice hpx.symm
  have h₁ : x 1-c 1-(m 1 : ℝ)=(r p • unitAngle p.2).re := by
    rw [hm]
    simp [latticeVector]
    ring
  have h₂ : x 2-c 2-(m 2 : ℝ)=(r p • unitAngle p.2).im := by
    rw [hm]
    simp [latticeVector]
    ring
  have he₁ := periodicCoordinate_germ g hg hp c 1 x (m 1) (by rw [h₁]; exact (he p).1)
  have he₂ := periodicCoordinate_germ g hg hp c 2 x (m 2) (by rw [h₂]; exact (he p).2)
  refine ⟨m,?_⟩
  filter_upwards [he₁,he₂] with y hy₁ hy₂
  simp only [periodicRotation,hy₁,hy₂]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalTangentRotation (N : Cover → Cover) (x : Cover) : Cover :=
  N x 2 • EuclideanSpace.single 1 1-N x 1 • EuclideanSpace.single 2 1

lemma normalTangentRotation_orthogonal (N : Cover → Cover) (x : Cover) :
    ⟪N x,normalTangentRotation N x⟫=0 := by
  simp only [normalTangentRotation,inner_sub_right,real_inner_smul_right,
    EuclideanSpace.inner_single_right,conj_trivial]
  ring

lemma tangent_shape_cross {n : Cover} (hn : ‖n‖=1) (D : Cover →L[ℝ] Cover)
    (hD : ∀ v,⟪n,D v⟫=0)
    (hs : ∀ v w,⟪n,v⟫=0 → ⟪n,w⟫=0 → ⟪D v,w⟫=⟪v,D w⟫) :
    D (tangentPart n (EuclideanSpace.single 1 1)) 2=
      D (tangentPart n (EuclideanSpace.single 2 1)) 1 := by
  have ht (v : Cover) : ⟪n,tangentPart n v⟫=0 := by
    simp only [tangentPart,inner_sub_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq,hn,one_pow,mul_one,sub_self]
  have hp (v w : Cover) : ⟪D v,tangentPart n w⟫=⟪D v,w⟫ := by
    rw [tangentPart,inner_sub_right,real_inner_smul_right,real_inner_comm n (D v),
      hD,mul_zero,sub_zero]
  have hq (v w : Cover) : ⟪tangentPart n v,D w⟫=⟪v,D w⟫ := by
    simp only [tangentPart,inner_sub_left,real_inner_smul_left,hD,mul_zero,sub_zero]
  have hh := hs (tangentPart n (EuclideanSpace.single 1 1))
    (tangentPart n (EuclideanSpace.single 2 1)) (ht _) (ht _)
  rw [hp,hq] at hh
  simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
    conj_trivial,mul_one,one_mul] using hh

lemma tangentialDivergence_sub_fields {F G : Cover → Cover} {x n : Cover}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    tangentialDivergence (fun y => F y-G y) x n=
      tangentialDivergence F x n-tangentialDivergence G x n := by
  have hd := (hF.hasFDerivAt.sub hG.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => F y-G y) x=fderiv ℝ F x-fderiv ℝ G x at hd
  simp only [tangentialDivergence,divergence_sub_fields hF hG,hd,
    sub_apply,inner_sub_right]
  ring

lemma normalTangentRotation_divergence {N : Cover → Cover} {x : Cover}
    (hN : DifferentiableAt ℝ N x) (hn : ‖N x‖=1)
    (hD : ∀ v,⟪N x,fderiv ℝ N x v⟫=0)
    (hs : ∀ v w,⟪N x,v⟫=0 → ⟪N x,w⟫=0 →
      ⟪fderiv ℝ N x v,w⟫=⟪v,fderiv ℝ N x w⟫) :
    tangentialDivergence (normalTangentRotation N) x (N x)=0 := by
  have h₁ := (EuclideanSpace.proj 1 : Cover →L[ℝ] ℝ).hasFDerivAt.comp x hN.hasFDerivAt
  have h₂ := (EuclideanSpace.proj 2 : Cover →L[ℝ] ℝ).hasFDerivAt.comp x hN.hasFDerivAt
  change HasFDerivAt (fun y => N y 1) _ x at h₁
  change HasFDerivAt (fun y => N y 2) _ x at h₂
  unfold normalTangentRotation
  rw [tangentialDivergence_sub_fields (h₂.differentiableAt.smul_const _)
    (h₁.differentiableAt.smul_const _),tangentialDivergence_smul_const h₂.differentiableAt,
    tangentialDivergence_smul_const h₁.differentiableAt,h₁.fderiv,h₂.fderiv]
  change (fderiv ℝ N x (tangentPart (N x) (EuclideanSpace.single 1 1))) 2-
    (fderiv ℝ N x (tangentPart (N x) (EuclideanSpace.single 2 1))) 1=0
  exact sub_eq_zero.mpr (tangent_shape_cross hn (fderiv ℝ N x) hD hs)

theorem isMinimizerAt_normalTangentRotation_divergence {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hu : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      ∀ᶠ y in 𝓝 x,‖N y‖=1) (x : Cover)
    (hx : quotientMap x∈frontier (openRepresentative E)) :
    tangentialDivergence (normalTangentRotation N) x (N x)=0 := by
  apply normalTangentRotation_divergence (hN.differentiable (by simp) x) (hu x hx).self_of_nhds
  · intro v
    rw [← ContinuousLinearMap.adjoint_inner_left,
      smooth_unit_normal_derivative (hN.differentiable (by simp) x) (hu x hx),inner_zero_left]
  · exact isMinimizerAt_shape_tangent_symmetric hV hE hm hμ hN hp ha x hx

end CubicTorus

end
end

end OAI
