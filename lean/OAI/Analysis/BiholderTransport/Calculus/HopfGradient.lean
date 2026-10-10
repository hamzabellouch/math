import Mathlib
import OAI.Analysis.BiholderTransport.Contact.HopfSupports

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M] in
lemma cost_divided_triangle_two_times (x y z : M) {s t : ℝ} (hs : 0<s) (ht : 0<t) :
    cost x z/(s+t) ≤ cost x y/s+cost y z/t := by
  have hst : 0<s+t := add_pos hs ht
  have ha : 0<s/(s+t) := div_pos hs hst
  have ha1 : s/(s+t)<1 := (div_lt_one hst).mpr (lt_add_of_pos_right s ht)
  have H := div_le_div_of_nonneg_right (divided_cost_triangle x y z ha ha1) hst.le
  calc
    _ ≤ _ := H
    _ = _ := by
      have he : 1-s/(s+t)=t/(s+t) := by field_simp; ring
      rw [he]
      field_simp

omit [CompactSpace M] [Nonempty M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma mdifferentiableAt_of_chart_differentiable {f : M → ℝ} {x : M}
    (hd : DifferentiableAt ℝ (fun y => f ((extChartAt 𝓘(ℝ,Model n) x).symm y))
      (extChartAt 𝓘(ℝ,Model n) x x)) :
    MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x := by
  have H := hd.hasFDerivAt.hasMFDerivAt.comp x
    (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,Model n))
      (show x∈(chartAt (Model n) x).source from mem_chart_source _ _)).hasMFDerivAt
  apply (H.congr_of_eventuallyEq ?_).mdifferentiableAt
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) x] with y hy
  simp only [Function.comp_apply,(extChartAt 𝓘(ℝ,Model n) x).left_inv hy]

lemma WeakMTW.mdifferentiable_hopfLax (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    MDifferentiable 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u) := by
  intro z
  obtain ⟨B,hB,r,hr,_,H⟩ := hmtw.uniform_hopfLax_C11 z
  apply mdifferentiableAt_of_chart_differentiable
  exact (H t ht ht1 u v hu hv hdual).1 _ (mem_ball_self hr)

lemma hopfLax_derivative_of_minimizer {u : M → ℝ} (hu : Continuous u)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1)
    (heq : hopfLax t u (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 =
      u x+cost x (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1/t)
    (hd : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      (innerSL ℝ (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2) := by
  let w : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let z := sprayFlow t w
  obtain ⟨ε,hε,hεt,_,_,Hε⟩ := exists_two_short_legs x p ht
    (show t<t+1 by linarith) zero_lt_one
  have hshort := (Filter.Eventually.self_of_nhds Hε).2.2.2
  let a := (sprayFlow (t-ε) w).1
  let G : M → ℝ := fun y => u x+cost x a/(t-ε)+cost a y/ε
  have hG : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) G z.1 (innerSL ℝ z.2) := by
    have H := (hasMFDerivAt_const (I := 𝓘(ℝ,Model n)) (I' := 𝓘(ℝ,ℝ))
      (u x+cost x a/(t-ε)) z.1).add (hshort.const_smul ε⁻¹)
    have heD : 0+ε⁻¹ • innerSL ℝ (ε • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2) =
        innerSL ℝ z.2 := by
      ext v
      simp only [zero_add,_root_.smul_apply,smul_eq_mul,innerSL_apply_apply,
        real_inner_smul_left]
      dsimp [z,w]
      field_simp
    replace H := H.congr_mfderiv heD
    have heG : G = ((fun _ => u x+cost x a/(t-ε)) +
        ε⁻¹ • fun y => dist (sprayFlow (t-ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 y^2/2) := by
      funext y
      dsimp [G,cost,a,w]
      ring
    rw [heG]
    exact H
  have hmin : dist x z.1=t*‖p‖ := by
    dsimp [z,w]
    rw [←riemannianExp_smul,minimizingVectors_smul hp ht.le ht1,norm_smul,
      Real.norm_eq_abs,abs_of_pos ht]
  have hleft : dist x a=(t-ε)*‖p‖ :=
    sprayFlow_minimizing_prefix w (sub_pos.mpr hεt).le (by linarith) hmin
  have hright : dist a z.1=ε*‖p‖ := by
    have H := sprayFlow_minimizing_subinterval w (sub_pos.mpr hεt).le (by linarith) hmin
    simpa only [sub_sub_cancel] using H
  have hcontact : hopfLax t u z.1=G z.1 := by
    rw [heq]
    dsimp [G,cost]
    rw [hmin,hleft,hright]
    field_simp
    ring
  have hle : ∀ y, hopfLax t u y≤G y := by
    intro y
    have H := cost_divided_triangle_two_times x a y (sub_pos.mpr hεt) hε
    rw [sub_add_cancel] at H
    exact (hopfLax_le hu t y x).trans (by dsimp [G]; linarith)
  exact hd.hasMFDerivAt.congr_mfderiv
    ((upper_contact_mfderiv hd hG.mdifferentiableAt (Filter.Eventually.of_forall hle) hcontact).trans hG.mfderiv)

def riemannianGradient (f : M → ℝ) (x : M) : TangentSpace 𝓘(ℝ,Model n) x := by
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  exact (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,Model n) x)).symm
    (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x)

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma riemannianGradient_eq_of_derivative {f : M → ℝ} {x : M}
    {v : TangentSpace 𝓘(ℝ,Model n) x}
    (h : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x (innerSL ℝ v)) :
    riemannianGradient (n := n) f x=v := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  rw [riemannianGradient,h.mfderiv]
  exact (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,Model n) x)).symm_apply_apply v

lemma WeakMTW.hopfLax_backward_flow (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : subgradientGraph (n := n) (cTransform v)) :
    sprayFlow (-t)
      (⟨graphProjection (cTransform v) t q,
        riemannianGradient (hopfLax t (cTransform v)) (graphProjection (cTransform v) t q)⟩ :
          TangentBundle 𝓘(ℝ,Model n) M) = q.1 := by
  have hdual : IsCostDualPair (cTransform v) (cTransform (cTransform v)) :=
    ⟨(cTransform_triple hv).symm,rfl⟩
  have hu := continuous_cTransform hv
  have hp := (hmtw.global_support hv q.2).1
  have hbase : graphProjection (cTransform v) t q=(sprayFlow t q.1).1 :=
    riemannianExp_smul _ _ _
  have hd := hmtw.mdifferentiable_hopfLax hu (continuous_cTransform hu) hdual ht ht1
  have hval := hmtw.hopfLax_graph_value hv ht ht1 q
  rw [hbase] at hval
  have hder := hopfLax_derivative_of_minimizer hu hp ht ht1.le hval (hd _)
  rw [hbase,riemannianGradient_eq_of_derivative hder]
  change sprayFlow (-t) (sprayFlow t q.1)=q.1
  rw [←sprayFlow_add,neg_add_cancel,sprayFlow_zero]

end WeakMTWTransport

end

end OAI
