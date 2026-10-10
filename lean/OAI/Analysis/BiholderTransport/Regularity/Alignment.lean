import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.PoleCoordinates
import OAI.Analysis.BiholderTransport.Regularity.HopfApproximation

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
lemma hopfLax_derivative_of_scaled_minimizer {u : M → ℝ} (hu : Continuous u)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (hp : t • p∈minimizingVectors x)
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
    rw [←riemannianExp_smul,hp,norm_smul,
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

lemma hopfLax_backward_minimizer {u : M → ℝ} (hu : Continuous u)
    {t : ℝ} (ht : 0<t) {x z : M}
    (hval : hopfLax t u z=u x+cost x z/t)
    (hd : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax t u) z) :
    (sprayFlow (-t) (⟨z,riemannianGradient (hopfLax t u) z⟩ :
      TangentBundle 𝓘(ℝ,Model n) M)).1=x := by
  obtain ⟨p,hp,hpz⟩ := exists_minimizing_vector (n := n) x z
  let q := t⁻¹ • p
  have hq : t • q∈minimizingVectors x := by
    simpa only [q,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hp
  have hz : (sprayFlow t (⟨x,q⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=z := by
    rw [←riemannianExp_smul]
    simpa only [q,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hpz
  have H := hopfLax_derivative_of_scaled_minimizer hu ht hq (hz ▸ hval) (hz ▸ hd)
  have HG := riemannianGradient_eq_of_derivative H
  have HB : (⟨z,riemannianGradient (hopfLax t u) z⟩ : TangentBundle 𝓘(ℝ,Model n) M)=
      sprayFlow t (⟨x,q⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    rw [←hz,HG]
  rw [HB,←sprayFlow_add,neg_add_cancel,sprayFlow_zero]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma gradients_cancel_at_local_max {f g : M → ℝ} {z : M}
    (hf : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z)
    (hg : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) g z)
    (hmax : ∀ᶠ a in 𝓝 z,f a+g a≤f z+g z) :
    riemannianGradient g z= -riemannianGradient (n := n) f z := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) z) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  have H := upper_contact_mfderiv (hf.add hg)
    (mdifferentiableAt_const (I := 𝓘(ℝ,Model n)) (I' := 𝓘(ℝ,ℝ))) hmax rfl
  rw [(hasMFDerivAt_riemannianGradient hf).add
    (hasMFDerivAt_riemannianGradient hg) |>.mfderiv,
    (hasMFDerivAt_const (I := 𝓘(ℝ,Model n)) (I' := 𝓘(ℝ,ℝ)) (f z+g z) z).mfderiv] at H
  have HE : riemannianGradient (n := n) f z+riemannianGradient (n := n) g z=0 := by
    apply ext_inner_right ℝ
    intro u
    have H0 := congrArg (fun L => L u) H
    change inner ℝ (riemannianGradient f z) u+inner ℝ (riemannianGradient g z) u=0 at H0
    simpa only [inner_add_left,inner_zero_left] using H0
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using HE)

lemma WeakMTW.hopf_maximum_aligned (hmtw : WeakMTW (n := n) (M := M))
    {w v : M → ℝ} (hw : Continuous w) (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {x y z : M}
    (hx : hopfLax t (cTransform w) z=cTransform w x+cost x z/t)
    (hy : hopfLax (1-t) v z=v y+cost y z/(1-t))
    (hdy : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (hopfLax (1-t) v) z)
    (hmax : ∀ᶠ a in 𝓝 z,hopfLax t (cTransform w) a+hopfLax (1-t) v a≤
      hopfLax t (cTransform w) z+hopfLax (1-t) v z) :
    ∃ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈normalSubdifferential (cTransform w) x ∧ p∈minimizingVectors x ∧
      z=riemannianExp x (t • p) ∧ y=riemannianExp x p ∧
      hopfLax t (cTransform w) z+hopfLax (1-t) v z=v y-cTransform (cTransform w) y := by
  let g := cTransform w
  have hg : Continuous g := continuous_cTransform hw
  obtain ⟨q,hq,hqz⟩ := exists_minimizing_vector (n := n) x z
  let p := t⁻¹ • q
  have hps : p∈normalSubdifferential g x := by
    apply global_min_divided_cost_subgradient hq ht
    intro a
    rw [hqz,←hx]
    exact hopfLax_le hg t z a
  obtain ⟨hp,hfull⟩ := hmtw.global_support hw hps
  have hpz : riemannianExp x (t • p)=z := by
    simpa only [p,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hqz
  have hPz : (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=z := by
    rwa [←riemannianExp_smul]
  have hdg := hmtw.mdifferentiable_hopfLax hg (continuous_cTransform hg)
    (show IsCostDualPair g (cTransform g) from ⟨(cTransform_triple hw).symm,rfl⟩) ht ht1 z
  have hneg := gradients_cancel_at_local_max hdg hdy hmax
  have hder := hopfLax_derivative_of_minimizer hg hp ht ht1.le (hPz ▸ hx) (hPz ▸ hdg)
  have HG := riemannianGradient_eq_of_derivative hder
  have HU : (⟨z,riemannianGradient (hopfLax t g) z⟩ : TangentBundle 𝓘(ℝ,Model n) M)=
      sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    rw [←hPz,HG]
  have HV : (⟨z,riemannianGradient (hopfLax (1-t) v) z⟩ : TangentBundle 𝓘(ℝ,Model n) M)=
      tangentScale (-1) (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) := by
    rw [←HU]
    simp only [tangentScale,neg_one_smul,hneg]
  have hback := hopfLax_backward_minimizer hv (sub_pos.mpr ht1) hy hdy
  rw [HV,sprayFlow_scale] at hback
  change (sprayFlow ((-1)*(-(1-t))) (sprayFlow t
    (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M))).1=y at hback
  rw [←sprayFlow_add,show (-1)*(-(1-t))+t=1 by ring,←riemannianExp_eq_sprayFlow] at hback
  have hpy : y=riemannianExp x p := hback.symm
  refine ⟨p,hps,hp,hpz.symm,hpy,?_⟩
  have hright : dist z y=(1-t)*‖p‖ := by
    rw [←hpz,hpy,riemannianExp_smul,riemannianExp_eq_sprayFlow]
    exact sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)
      ht.le ht1.le (by rw [one_mul,←riemannianExp_eq_sprayFlow]; exact hp)
  have hcost : cost y z/(1-t)=(1-t)*‖p‖^2/2 := by
    rw [cost,dist_comm,hright]
    field_simp
  have hsum := minimizing_split_contact hp ht ht1
  rw [hpz,←hpy] at hsum
  have hval1 : -cTransform g y=g x+cost x y := by
    have H := hopfLax_eq_of_min hg 1 y x (by simpa only [hpy,div_one] using hfull)
    simpa only [hopfLax_one _ hg,div_one] using H
  rw [hx,hy,hcost]
  change g x+cost x z/t+(v y+(1-t)*‖p‖^2/2)=v y-cTransform g y
  linarith only [hsum,hval1]

end WeakMTWTransport
end

end OAI
