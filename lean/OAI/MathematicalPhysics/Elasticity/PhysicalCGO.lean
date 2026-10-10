import OAI.MathematicalPhysics.Elasticity.CommonExterior
import OAI.MathematicalPhysics.Elasticity.Recovery

namespace OAI

noncomputable section

namespace ElasticityAugmented

section
open scoped BigOperators

def smoothOfReal (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Smooth :=
  ⟨fun x => (f x : ℂ),Complex.ofRealCLM.contDiff.comp hf⟩
lemma smoothOfReal_apply (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    (smoothOfReal f hf : X → ℂ) x=(f x : ℂ) := rfl
lemma coord_ofReal (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) (x : X) :
    (coord i (smoothOfReal f hf) : X → ℂ) x=(fderiv ℝ f x (e i) : ℂ) := by
  have hh := Complex.ofRealCLM.hasFDerivAt.comp x ((hf.differentiable (by simp)) x).hasFDerivAt
  exact congrArg (fun L : X →L[ℝ] ℂ => L (e i)) hh.fderiv
lemma recovery_basis (i : Fin 3) : ElasticityRecovery.basis i=e i := by
  simp [ElasticityRecovery.basis,e,EuclideanSpace.basisFun_apply]
lemma coord_ofReal_grad (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) (x : X) :
    (coord i (smoothOfReal f hf) : X → ℂ) x=(ElasticityRecovery.grad f x i : ℂ) := by
  rw [coord_ofReal]
  simp only [ElasticityRecovery.grad,ElasticityFiniteType.D,recovery_basis]

def positiveRoot (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hp : ∀ x,0 < m x) : Smooth :=
  smoothOfReal (fun x => Real.sqrt (m x)) (hm.sqrt (fun x => (hp x).ne'))
lemma positiveRoot_nonzero (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hp : ∀ x,0 < m x) (x : X) :
    (positiveRoot m hm hp : X → ℂ) x≠0 := by
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp x)).ne'
lemma positiveRoot_square (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hp : ∀ x,0 < m x) :
    positiveRoot m hm hp*positiveRoot m hm hp=smoothOfReal m hm := by
  apply Subtype.ext
  funext x
  change (Real.sqrt (m x) : ℂ)*(Real.sqrt (m x) : ℂ)=(m x : ℂ)
  norm_cast
  exact Real.mul_self_sqrt (hp x).le

def smoothLog (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ x,0 < f x) : Smooth :=
  smoothOfReal (fun x => Real.log (f x)) (hf.log (fun x => (hp x).ne'))
lemma coord_real_log (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ x,0 < f x) (i : Fin 3) :
    coord i (smoothLog f hf hp)=
      smoothInv (smoothOfReal f hf) (fun x => Complex.ofReal_ne_zero.mpr (hp x).ne')*
        coord i (smoothOfReal f hf) := by
  apply Subtype.ext
  funext x
  rw [smoothLog,coord_ofReal]
  rw [fderiv.log ((hf.differentiable (by simp)) x) (hp x).ne']
  simp only [smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_inv]
  change (f x : ℂ)⁻¹*(fderiv ℝ f x (e i) : ℂ)=_
  change _ = (f x : ℂ)⁻¹ * (coord i (smoothOfReal f hf) : X → ℂ) x
  rw [coord_ofReal]
lemma direction_real_log (θ : Fin 3 → ℂ) (f : X → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ x,0 < f x) :
    direction (A := Smooth) coord θ (smoothLog f hf hp)=
      smoothInv (smoothOfReal f hf) (fun x => Complex.ofReal_ne_zero.mpr (hp x).ne')*
        direction (A := Smooth) coord θ (smoothOfReal f hf) := by
  simp only [direction,coord_real_log,Finset.mul_sum,Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma logarithmicGrad_root (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hp : ∀ x,0 < m x) (i : Fin 3) :
    logarithmicGrad (positiveRoot m hm hp) (positiveRoot_nonzero m hm hp) i=coord i (smoothLog m hm hp) := by
  rw [coord_real_log]
  have hderiv := congrArg (coord i) (positiveRoot_square m hm hp)
  rw [partial_mul] at hderiv
  apply Subtype.ext
  funext point
  have hvalue := congrArg (fun value : Smooth => (value : X → ℂ) point) hderiv
  change (coord i (positiveRoot m hm hp) : X → ℂ) point * (Real.sqrt (m point) : ℂ) +
    (Real.sqrt (m point) : ℂ) * (coord i (positiveRoot m hm hp) : X → ℂ) point =
      (coord i (smoothOfReal m hm) : X → ℂ) point at hvalue
  change 2 * (Real.sqrt (m point) : ℂ)⁻¹ *
    (coord i (positiveRoot m hm hp) : X → ℂ) point =
      (m point : ℂ)⁻¹ * (coord i (smoothOfReal m hm) : X → ℂ) point
  have hroot : (Real.sqrt (m point) : ℂ)^2=(m point : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (hp point).le
  have hzero : (Real.sqrt (m point) : ℂ)≠0 := positiveRoot_nonzero m hm hp point
  rw [← hvalue,← hroot]
  field_simp [hzero]
  ring

lemma ofReal_direction (θ : Fin 3 → ℂ) (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    (direction (A := Smooth) coord θ (smoothOfReal f hf) : X → ℂ) x=ElasticityRecovery.dir θ f x := by
  simp only [direction,ElasticityRecovery.dir,dotProduct,Fin.sum_univ_three,
    Subalgebra.coe_add,Subalgebra.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,coord_ofReal_grad]

lemma smoothOfReal_add (f g : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    smoothOfReal f hf+smoothOfReal g hg=smoothOfReal (fun x => f x+g x) (hf.add hg) := by
  apply Subtype.ext
  funext x
  exact (Complex.ofReal_add _ _).symm
lemma smoothLog_div (f g : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hp : ∀ x,0 < f x) (hq : ∀ x,0 < g x) :
    smoothLog (fun x => f x/g x) (hf.div hg (fun x => (hq x).ne')) (fun x => div_pos (hp x) (hq x))=
      smoothLog f hf hp-smoothLog g hg hq := by
  apply Subtype.ext
  funext x
  change (Real.log (f x/g x) : ℂ)=(Real.log (f x) : ℂ)-(Real.log (g x) : ℂ)
  exact_mod_cast Real.log_div (hp x).ne' (hq x).ne'
lemma real_sum_nonzero (m k : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hmp : ∀ x,0 < m x) (hkp : ∀ x,0 < k x) (x : X) :
    ((smoothOfReal k hk+positiveRoot m hm hmp*positiveRoot m hm hmp : Smooth) : X → ℂ) x≠0 := by
  rw [positiveRoot_square,smoothOfReal_add,smoothOfReal_apply]
  exact Complex.ofReal_ne_zero.mpr (add_pos (hkp x) (hmp x)).ne'

lemma direction_sub (θ : Fin 3 → ℂ) (f g : Smooth) :
    direction (A := Smooth) coord θ (f-g)=direction (A := Smooth) coord θ f-direction (A := Smooth) coord θ g :=
  map_sub (thetaDerivation θ) f g

lemma transportT_real (θ : Fin 3 → ℂ) (m k : X → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hmp : ∀ x,0 < m x) (hkp : ∀ x,0 < k x) (x : X) :
    (transportT θ (smoothOfReal k hk) (positiveRoot m hm hmp)
      (fun x => Complex.ofReal_ne_zero.mpr (hkp x).ne') (real_sum_nonzero m k hm hk hmp hkp) : X → ℂ) x=
      ElasticityRecovery.T m k x θ := by
  have hlog := smoothLog_div k (fun x => k x+m x) hk (hk.add hm) hkp (fun x => add_pos (hkp x) (hmp x))
  have hd := congrArg (direction (A := Smooth) coord θ) hlog
  rw [direction_sub] at hd
  conv_rhs at hd => rw [direction_real_log θ k hk hkp,
    direction_real_log θ (fun x => k x+m x) (hk.add hm) (fun x => add_pos (hkp x) (hmp x))]
  have hleft : (direction (A := Smooth) coord θ
      (smoothLog (fun x => k x/(k x+m x))
        (hk.div (hk.add hm) (fun x => (add_pos (hkp x) (hmp x)).ne'))
        (fun x => div_pos (hkp x) (add_pos (hkp x) (hmp x)))) : X → ℂ) x=
      ElasticityRecovery.T m k x θ := by
    exact ofReal_direction θ _ _ x
  rw [← hleft]
  change _ = (direction (A := Smooth) coord θ _ : X → ℂ) x
  rw [hd]
  unfold transportT
  simp only [positiveRoot_square,smoothOfReal_add]

lemma grad_contDiff (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ElasticityRecovery.grad f x i) :=
  ElasticityFiniteType.contDiff_D hf _
lemma coord_real_grad (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    coord i (smoothOfReal f hf)=smoothOfReal (fun x => ElasticityRecovery.grad f x i)
      (grad_contDiff f hf i) := by
  apply Subtype.ext
  funext x
  exact coord_ofReal_grad f hf i x
lemma direction_coord_real (θ : Fin 3 → ℂ) (f : X → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) (x : X) :
    (direction (A := Smooth) coord θ (coord i (smoothOfReal f hf)) : X → ℂ) x=
      ∑ j,θ j*(ElasticityRecovery.hessian f x i j : ℂ) := by
  rw [coord_real_grad,ofReal_direction]
  rfl
lemma thetaGamma_real (θ : Fin 3 → ℂ) (m : X → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hp : ∀ x,0 < m x) (x : X) :
    (thetaGamma θ (positiveRoot m hm hp) (positiveRoot_nonzero m hm hp) : X → ℂ) x=
      ElasticityRecovery.dir θ (fun x => Real.log (m x)) x := by
  simp only [thetaGamma,logarithmicGrad_root]
  exact ofReal_direction θ _ _ x
lemma transportQ_real (θ : Fin 3 → ℂ) (m k : X → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hmp : ∀ x,0 < m x) (hkp : ∀ x,0 < k x) (x : X) (i : Fin 3) :
    (transportQ θ (smoothOfReal k hk) (positiveRoot m hm hmp)
      (positiveRoot_nonzero m hm hmp) (fun x => Complex.ofReal_ne_zero.mpr (hkp x).ne')
      (real_sum_nonzero m k hm hk hmp hkp) i : X → ℂ) x=ElasticityRecovery.Q m k x θ i := by
  unfold transportQ
  simp only [positiveRoot_square,logarithmicGrad_root]
  rw [mul_assoc,← direction_real_log θ k hk hkp]
  simp only [Subalgebra.coe_sub,Subalgebra.coe_mul,Subalgebra.coe_smul,Pi.sub_apply,Pi.mul_apply,
    Pi.smul_apply,smul_eq_mul]
  rw [thetaGamma_real]
  have hdlog : (direction (A := Smooth) coord θ (smoothLog k hk hkp) : X → ℂ) x=
      ElasticityRecovery.dir θ (fun x => Real.log (k x)) x := ofReal_direction θ _ _ x
  rw [hdlog]
  change (1/2 : ℂ)*(((m x : ℂ)*((k x : ℂ)+(m x : ℂ))⁻¹*
      ElasticityRecovery.dir θ (fun x => Real.log (k x)) x-
      (1/2 : ℂ)*ElasticityRecovery.dir θ (fun x => Real.log (m x)) x)*
      (coord i (smoothLog m hm hmp) : X → ℂ) x-
      (m x : ℂ)*((k x : ℂ)+(m x : ℂ))⁻¹*
      (direction (A := Smooth) coord θ (coord i (smoothLog m hm hmp)) : X → ℂ) x)=_
  rw [smoothLog,coord_ofReal_grad,direction_coord_real]
  simp only [ElasticityRecovery.Q,ElasticityRecovery.QMatrix,ElasticityRecovery.dir,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_ofNat,Complex.ofReal_one]
  ring
end
open Set
open scoped BigOperators
lemma real_k_positive (lam m : X → ℝ) (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) (x : X) :
    0<lam x+m x := by have hh := hp x; linarith
lemma real_longitudinal_positive (lam m : X → ℝ) (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) (x : X) :
    0<lam x+m x+m x := by have hh := hp x; linarith

/-- Actual real strongly convex Lamé pairs develop to a full independent
physical amplitude frame and all its compatible recursion orders. -/
theorem exists_real_physical_series {U : Set X} (hU : IsOpen U) (hC : IsCompact (closure U))
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (lam m : X → ℝ) (hl : ContDiff ℝ (⊤ : ℕ∞) lam) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) :
    let l := smoothOfReal lam hl
    let μ := smoothOfReal m hm
    let r := positiveRoot m hm (fun x => (hp x).1)
    let hr := positiveRoot_nonzero m hm (fun x => (hp x).1)
    ∃ a : Fin 3 → ℕ → Amplitude Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ ν,normal θ (a ν 0).1=0) ∧
      (∀ ν,leadingR (localCoord hU) θ (restrictSmooth U l) (restrictSmooth U μ)
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0 ∧
        leadingS (localCoord hU) θ (restrictSmooth U l) (restrictSmooth U μ)
          (localAmp U (a ν 0)).1 (localAmp U (a ν 0)).2=0) ∧
      (∀ ν j,RecursOn hU θ l μ (a ν j) (a ν (j+1))) ∧
      ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (changeP r (a ν 0).1 i : X → ℂ) x),
          (changeS (l+μ) r hr (a ν 0).1 (a ν 0).2 : X → ℂ) x) := by
  intro l μ r hr
  have hr2 : r*r=μ := positiveRoot_square m hm (fun x => (hp x).1)
  have hk : ∀ x,((l+μ : Smooth) : X → ℂ) x≠0 := by
    intro x
    change (lam x : ℂ)+(m x : ℂ)≠0
    exact_mod_cast (real_k_positive lam m hp x).ne'
  have hsum : ∀ x,((l+μ+r*r : Smooth) : X → ℂ) x≠0 := by
    intro x
    rw [hr2]
    change (lam x : ℂ)+(m x : ℂ)+(m x : ℂ)≠0
    exact_mod_cast (real_longitudinal_positive lam m hp x).ne'
  obtain ⟨a,B,hn,he,hrec,hB⟩ := exists_physical_formal_frame hU hC θ hθ hne (l+μ) r hr hk hsum
  refine ⟨a,B,hn,?_,?_,hB⟩
  · simpa only [hr2,add_sub_cancel_right] using he
  · simpa only [hr2,add_sub_cancel_right] using hrec
end ElasticityAugmented
namespace Elasticity
open Set MeasureTheory
open scoped BigOperators SchwartzMap
open ElasticityAugmented (Smooth smoothOfReal smooth_coe)
open ElasticityCoeffBounds
open ElasticityDistribution (Coeff eval)
open ElasticityPhysicalAlgebra (physical)
open ElasticityCGO (expCut)

/-- Actual DN equality yields a shifted physical solution with a compact
amplitude difference. This uses the common-exterior coefficients from the
boundary reduction; it does not assume normalized-system transfer. The two
cutoffs are ordinary compact smooth cutoffs on nested open domains. -/
theorem extended_dn_amplitude_transfer {Ω B B' : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
    (z : Fin 3 → ℂ) (u : Fin 3 → SchwartzMap X ℂ)
    (hu : ∀ i,EqOn (physical z (fun x => (lam 0 x : ℂ)) (fun x => (m 0 x : ℂ)) u i : X → ℂ) 0 B) :
    ∃ v : Fin 3 → SchwartzMap X ℂ,
      (∀ i,tsupport (v i-u i : SchwartzMap X ℂ)⊆closure Ω) ∧
      (∀ i,EqOn (physical z (fun x => (lam 1 x : ℂ)) (fun x => (m 1 x : ℂ)) v i : X → ℂ) 0 B') := by
  let l := fun q => smoothOfReal (lam q) (hl q)
  let μ := fun q => smoothOfReal (m q) (hm q)
  have hn0 (x) : (μ 1 : X → ℂ) x≠0 := Complex.ofReal_ne_zero.mpr (hp 1 x).1.ne'
  have ho0 (x) : ((l 1+μ 1+μ 1 : Smooth) : X → ℂ) x≠0 := by
    change (lam 1 x : ℂ)+(m 1 x : ℂ)+(m 1 x : ℂ)≠0
    exact_mod_cast (ElasticityAugmented.real_longitudinal_positive (lam 1) (m 1) (hp 1) x).ne'
  let n := reciprocal (μ 1) hn0
  let o := reciprocal (l 1+μ 1+μ 1) ho0
  have hn : ExteriorConstant n := (hclm 1).reciprocal hn0
  have ho : ExteriorConstant o := (((hcll 1).add (hclm 1)).add (hclm 1)).reciprocal ho0
  let L : Fin 2 → Coeff := fun q => ⟨l q,(hcll q).growth⟩
  let M : Fin 2 → Coeff := fun q => ⟨μ q,(hclm q).growth⟩
  let N : Coeff := ⟨n,hn.growth⟩
  let O : Coeff := ⟨o,ho.growth⟩
  have hiN : N*M 1=1 := by apply Subtype.ext; exact reciprocal_mul (μ 1) hn0
  have hiO : O*(L 1+M 1+M 1)=1 := by apply Subtype.ext; exact reciprocal_mul (l 1+μ 1+μ 1) ho0
  have ha (q) : Admissible Ω (lam q) (m q) := admissible_of_global (hl q) (hm q) (hp q)
  have hbl (q) : BoundedCoefficient B (lam q) :=
    SmoothUpTo.boundedCoefficient ⟨univ,isOpen_univ,subset_univ _,(hl q).contDiffOn⟩ hB hBB
  have hbm (q) : BoundedCoefficient B (m q) :=
    SmoothUpTo.boundedCoefficient ⟨univ,isOpen_univ,subset_univ _,(hm q).contDiffOn⟩ hB hBB
  let F := fun i => expCut χ hcχ z (u i)
  have hF : ∀ i,EqOn (physical 0 (eval (L 0)) (eval (M 0)) F i : X → ℂ) 0 B :=
    ElasticityCGO.expCut_solution hB (l 0) (μ 0) χ (hcll 0).growth (hclm 0).growth hcχ hχ z u hu
  obtain ⟨H,hH,hsol,_⟩ := physical_supported_transfer (ha 0) (ha 1) hΩ hOB
    (subset_closure.trans (hcl.trans hsub)) hB hB' hsub hcl
    (hbl 0) (hbm 0) (hbl 1) (hbm 1) he hDN (L 0) (M 0) (L 1) (M 1) N O hiN hiO
    (Filter.Eventually.of_forall (fun _ => rfl)) (Filter.Eventually.of_forall (fun _ => rfl))
    (Filter.Eventually.of_forall (fun _ => rfl)) (Filter.Eventually.of_forall (fun _ => rfl))
    (smooth_coe g) hc hs hg F hF
  obtain ⟨v,hv,hp',_⟩ := ElasticityCGO.transferred_amplitude hB' (l 1) (μ 1) χ
    (hcll 1).growth (hclm 1).growth hcχ (hχ.mono hsub) z u F H
    (fun i x hx => by
      change expCut χ hcχ z (u i) x=_
      rw [ElasticityCGO.expCut_apply,hχ (hsub hx),Pi.one_apply,one_mul]) hH hsol
  exact ⟨v,hv,hp'⟩

open ElasticityPhysicalEstimate (physicalAug)
open ElasticityPhysicalAlgebra (phase)
open ElasticityNegativeOrder (sobNorm)

/-- The actual physical DN equality gives the uniform compact comparison bound.
The Cauchy-data transfer, normalized forcing, and coefficient bounds are all
proved dependencies. This theorem still starts at the common-exterior stage;
it does not replace the missing original-boundary jet determination. -/
theorem extended_dn_compact_comparison {Ω B B' : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (R : ℝ) (hR : 1≤R) (hKR : closure Ω⊆Metric.closedBall 0 R)
    (α β : X) (hα : α≠0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B') :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∀ u : Fin 3 → SchwartzMap X ℂ,
      (∀ i,EqOn (physical (phase h α β) (fun x => (lam 0 x : ℂ))
        (fun x => (m 0 x : ℂ)) u i : X → ℂ) 0 B) →
      ∃ v : Fin 3 → SchwartzMap X ℂ,
        (∀ i,tsupport (v i-u i : SchwartzMap X ℂ)⊆closure Ω) ∧
        (∀ i,EqOn (physical (phase h α β) (fun x => (lam 1 x : ℂ))
          (fun x => (m 1 x : ℂ)) v i : X → ℂ) 0 B') ∧
        sobNorm h 1 (physicalAug (phase h α β) (v-u))≤
          C*sobNorm h 1 (physicalAug (phase h α β) u) := by
  let l := fun q => smoothOfReal (lam q) (hl q)
  let μ := fun q => smoothOfReal (m q) (hm q)
  have hn0 (q x) : (μ q : X → ℂ) x≠0 := Complex.ofReal_ne_zero.mpr (hp q x).1.ne'
  have ho0 (q x) : ((l q+μ q+μ q : Smooth) : X → ℂ) x≠0 := by
    change (lam q x : ℂ)+(m q x : ℂ)+(m q x : ℂ)≠0
    exact_mod_cast (ElasticityAugmented.real_longitudinal_positive (lam q) (m q) (hp q) x).ne'
  have hel : EqOn (l 0 : X → ℂ) (l 1) (closure Ω)ᶜ := by
    intro x hx
    exact congrArg Complex.ofReal (he x (fun hh => hx (subset_closure hh))).1
  have hem : EqOn (μ 0 : X → ℂ) (μ 1) (closure Ω)ᶜ := by
    intro x hx
    exact congrArg Complex.ofReal (he x (fun hh => hx (subset_closure hh))).2
  obtain ⟨C,h₀,hC,hh₀,hest⟩ := ElasticityPhysicalEstimate.physical_compact_comparison
    hB' isClosed_closure hcl R hR hKR α β hα l μ hcll hclm hn0 ho0 hel hem
  refine ⟨C,h₀,hC,hh₀,fun h hh hsmall u hu => ?_⟩
  obtain ⟨v,hv,hsol⟩ := extended_dn_amplitude_transfer hΩ hOB hB hBB hB' hsub hcl
    lam m hl hm hp hcll hclm he hDN χ g hcχ hc hs hχ hg (phase h α β) u hu
  exact ⟨v,hv,hsol,hest h hh hsmall u v hv (fun i => (hu i).mono hsub) hsol⟩
end Elasticity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
local notation "X" => ElasticityBessel.X

lemma sobolevInjection_zero (q : Lp ℂ 2 (volume : Measure X)) :
    sobolevInjection 0 q=(q : 𝓢'(X,ℂ)) := by
  simp only [sobolevInjection,neg_zero,besselPotential_zero,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply]

/-- A standard Sobolev H1 representative controls the actual semiclassical
Fourier norm uniformly for h in (0,1]. The two Bessel conventions are not
identified: this follows from their concrete L2 derivative realizations. -/
theorem standard_H1_controls_semiclassical :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0≤h → h≤1 → ∀ f : S,
      ∀ q : Lp ℂ 2 (volume : Measure X),sobolevInjection 1 q=(f : 𝓢'(X,ℂ)) →
        norm2 (J h 1 f)≤C*‖q‖ := by
  obtain ⟨L₀,hL₀⟩ := exists_bounded_sobolev_inclusion (E := X) (s := 1) (t := 0) (by norm_num)
  have hd (i : Fin 3) := exists_bounded_sobolev_derivative (E := X) 1 (e i)
  choose L hL using hd
  let A := 1+‖L₀‖+∑ i,‖L i‖
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨2*A,by positivity,fun h hh hh1 f q hq => ?_⟩
  have hzero : L₀ q=L2 f := by
    apply lp_distribution_injective
    change (L₀ q : 𝓢'(X,ℂ))=(L2 f : 𝓢'(X,ℂ))
    rw [← sobolevInjection_zero,hL₀,hq]
    exact (Lp.toTemperedDistribution_toLp_eq f).symm
  have hder (i : Fin 3) : L i q=L2 (d (e i) f) := by
    apply lp_distribution_injective
    have hd := hL i q
    norm_num only [sub_self] at hd
    rw [sobolevInjection_zero,hq,
      lineDerivOp_toTemperedDistributionCLM_eq] at hd
    exact hd.trans (Lp.toTemperedDistribution_toLp_eq (d (e i) f)).symm
  have ha₀ : ‖L₀‖≤A := by
    have hs : 0≤∑ i,‖L i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (L i))
    dsimp [A]
    linarith
  have ha (i : Fin 3) : ‖L i‖≤A := by
    have hs := Finset.single_le_sum (fun j _ => norm_nonneg (L j)) (Finset.mem_univ i)
    dsimp [A]
    linarith [norm_nonneg L₀]
  have hf : norm2 f≤A*‖q‖ := by
    change ‖L2 f‖≤_
    rw [← hzero]
    exact (L₀.le_opNorm q).trans (mul_le_mul_of_nonneg_right ha₀ (norm_nonneg q))
  have hdf (i : Fin 3) : norm2 (d (e i) f)≤A*‖q‖ := by
    change ‖L2 (d (e i) f)‖≤_
    rw [← hder i]
    exact ((L i).le_opNorm q).trans (mul_le_mul_of_nonneg_right (ha i) (norm_nonneg q))
  have hf₂ := pow_le_pow_left₀ (norm2_nonneg f) hf 2
  have hd₂ (i : Fin 3) := pow_le_pow_left₀ (norm2_nonneg (d (e i) f)) (hdf i) 2
  have hg : gradientMass f≤3*(A*‖q‖)^2 := by
    simp only [gradientMass,Fin.sum_univ_three,← norm2_sq_mass]
    nlinarith only [hd₂ 0,hd₂ 1,hd₂ 2]
  have hh₂ : h^2≤1 := by nlinarith
  have he := H1_energy h f
  have hgm := mul_le_mul_of_nonneg_right hh₂ (gradientMass_nonneg f)
  rw [← norm2_sq_mass] at he
  have hb : norm2 (J h 1 f)^2≤4*(A*‖q‖)^2 := by nlinarith only [he,hgm,hg,hf₂]
  have hpos : 0≤2*A*‖q‖ := by positivity
  nlinarith only [hb,norm2_nonneg (J h 1 f),hpos]
/-- The same uniform bound after a compact cutoff, when only a local
standard-H1 representative is available. This is the localization needed
for the actual augmented CGO corrections. -/
theorem local_standard_H1_controls_semiclassical {U : Set X} {g : X → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (hs : tsupport g⊆U) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0≤h → h≤1 → ∀ f : S,
      ∀ q : Lp ℂ 2 (volume : Measure X),
      LocalEqual U (sobolevInjection 1 q) (f : 𝓢'(X,ℂ)) →
        norm2 (J h 1 (mult g f))≤C*‖q‖ := by
  have hmult (u : 𝓢'(X,ℂ)) (hu : MemSobolev 1 2 u) :
      MemSobolev 1 2 (smulLeftCLM ℂ g u) := by
    have hb : OrthonormalBasis (Fin 3) ℝ X := EuclideanSpace.basisFun (Fin 3) ℝ
    have ht := sobolev_nat_product (F := ℂ) hb 1 (g := g) hg hc (u := u)
    simpa only [Nat.cast_one] using ht (by simpa only [Nat.cast_one] using hu)
  obtain ⟨L,hL⟩ := exists_sobolev_realization (E := X) 1 1 (smulLeftCLM ℂ g) hmult
  obtain ⟨C,hC,hest⟩ := standard_H1_controls_semiclassical
  refine ⟨C*(1+‖L‖),by positivity,fun h hh hh1 f q hq => ?_⟩
  have he : sobolevInjection 1 (L q)=(mult g f : 𝓢'(X,ℂ)) := by
    rw [hL,hq.cutoff hg hc hs]
    exact distribution_schwartz_product (hc.hasTemperateGrowth hg) f
  have hb := hest h hh hh1 (mult g f) (L q) he
  have hn := L.le_opNorm q
  calc
    _ ≤ C*‖L q‖ := hb
    _ ≤ C*(‖L‖*‖q‖) := mul_le_mul_of_nonneg_left hn hC.le
    _ ≤ (C*(1+‖L‖))*‖q‖ := by nlinarith [mul_nonneg hC.le (norm_nonneg q)]
end ElasticityRegularity
namespace ElasticityCGO

section
open MeasureTheory Set TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityRegularity (sobolevInjection)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityDistribution (HV Dist divd)

/-- A genuinely compatible finite amplitude series gives exact smooth physical
CGO fields. The correction is the same estimated L2 solution, and its full
physical divergence is H1-small. Neither a physical-solvability statement nor
convergence of a formal infinite series is assumed. -/
theorem physical_cgo_from_recursion (R : ℝ) (hR : 1≤R)
    (Ω U : Set X) (hΩ : Ω⊆Metric.closedBall 0 R) (hU : IsOpen U) (hsub : U⊆Ω)
    (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x,star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x,star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x,(m : X → ℂ) x≠0)
    (he0 : ∀ x,((lam+m+m : Smooth) : X → ℂ) x≠0)
    (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
    (hcχ : ∀ i,HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4,EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i,tsupport (χ i)⊆Ω) (h1 : EqOn (χ 0) 1 U)
    (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord hU) (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (restrictSmooth U lam) (restrictSmooth U m) (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
    (hn₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,RecursOn hU (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m (a j) (a (j+1))) :
    ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
        (∀ i,∀ᵐ x ∂(volume : Measure X),x∈U → w i x=v i x) ∧
        (∀ i,EqOn (physical (phase h α β) lam m
          ((fun j => cut ⟨χ 0,hχ 0⟩ (hcχ 0) ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 U) ∧
        (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖≤C*h^7 ∧ ‖q‖≤C*h := by
  let θ : Fin 3 → ℂ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
  let f₀ : Fin 3 → S := fun i => cut ⟨χ 0,hχ 0⟩ (hcχ 0) (residual0 lam m (a 8) i)
  let f₁ : Fin 3 → S := fun i => cut ⟨χ 0,hχ 0⟩ (hcχ 0) (residual1 θ lam m (a 8) i)
  obtain ⟨C,h₀,hC,hh₀,hsol⟩ := ElasticityDistribution.finite_classical_correction R hR Ω U hΩ hU hsub
    α β hα lam m hl hm hrl hrm hm0 he0 χ hχ hcχ hnest hs h1 f₀ f₁
  refine ⟨C,h₀,hC,hh₀,fun h hh hsmall => ?_⟩
  obtain ⟨w,q,v,hv,hphys,hq,hw,hqn⟩ := hsol h hh hsmall
  refine ⟨w,q,v,hv,?_,hq,hw,hqn⟩
  apply ElasticityDistribution.correction_cancels_residual U (phase h α β) lam m
    (fun j => cut ⟨χ 0,hχ 0⟩ (hcχ 0) ((truncation (h : ℂ) 8 a).1 j)) v
    (ElasticityDistribution.finiteResidual h f₀ f₁) _ hphys
  intro i
  rw [phase_eq]
  exact cut_truncation_residual hU θ hθ lam m ⟨χ 0,hχ 0⟩ hl.growth hm.growth
    (hcχ 0) h1 h (ne_of_gt hh) a hR₀ hn₀ hrec i
end
open Set
open ElasticityAugmented
open ElasticityNegativeOrder (cutoff)

def fiveCutoff (R : ℝ) (hR : 1≤R) (i : Fin 5) (x : X) : ℂ :=
  (cutoff (R+(i.val : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith) x : ℂ)
lemma fiveCutoff_smooth (R : ℝ) (hR : 1≤R) (i : Fin 5) :
    ContDiff ℝ (⊤ : ℕ∞) (fiveCutoff R hR i) :=
  Complex.ofRealCLM.contDiff.comp (cutoff _ _).contDiff
lemma fiveCutoff_compact (R : ℝ) (hR : 1≤R) (i : Fin 5) :
    HasCompactSupport (fiveCutoff R hR i) :=
  (cutoff _ _).hasCompactSupport.comp_left Complex.ofReal_zero
lemma fiveCutoff_support (R : ℝ) (hR : 1≤R) (i : Fin 5) :
    tsupport (fiveCutoff R hR i)⊆Metric.closedBall 0 (R+(i.val : ℝ)+2) := by
  let b := cutoff (R+(i.val : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith)
  have hs : tsupport (fiveCutoff R hR i)⊆tsupport b := by
    apply closure_mono
    intro x hx
    exact fun hh => hx (by change (b x : ℂ)=0; rw [hh,Complex.ofReal_zero])
  simpa only [b,ContDiffBump.tsupport_eq,cutoff] using hs
lemma fiveCutoff_one (R : ℝ) (hR : 1≤R) (i : Fin 5) {x : X}
    (hx : x∈Metric.closedBall 0 (R+(i.val : ℝ)+1)) : fiveCutoff R hR i x=1 := by
  have hh := (cutoff (R+(i.val : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith)).one_of_mem_closedBall hx
  unfold fiveCutoff
  rw [hh,Complex.ofReal_one]
lemma fiveCutoff_nested (R : ℝ) (hR : 1≤R) (i : Fin 4) :
    EqOn (fiveCutoff R hR i.succ) 1 (tsupport (fiveCutoff R hR i.castSucc)) := by
  intro x hx
  apply fiveCutoff_one
  have hh := fiveCutoff_support R hR i.castSucc hx
  simp only [Metric.mem_closedBall,Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one] at hh ⊢
  linarith
lemma fiveCutoff_inside (R : ℝ) (hR : 1≤R) (i : Fin 5) :
    tsupport (fiveCutoff R hR i)⊆Metric.ball 0 (R+7) := by
  intro x hx
  have hh := fiveCutoff_support R hR i hx
  have hi : (i.val : ℝ)<5 := by exact_mod_cast i.isLt
  simp only [Metric.mem_closedBall] at hh
  rw [Metric.mem_ball]
  linarith
lemma fiveCutoff_initial (R : ℝ) (hR : 1≤R) :
    EqOn (fiveCutoff R hR 0) 1 (Metric.ball 0 R) := by
  intro x hx
  apply fiveCutoff_one
  simp only [Fin.val_zero,Nat.cast_zero,add_zero,Metric.mem_closedBall]
  have hh := Metric.mem_ball.mp hx
  linarith
end ElasticityCGO
namespace ElasticityCGO
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityRegularity (sobolevInjection)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityDistribution (HV Dist divd)

/-- Quantified actual physical CGO corrections on the ball, with the full
physical divergence in H1. This is a conclusion, never an input assumption. -/
def PhysicalColumn (R : ℝ) (hR : 1≤R) (α β : X) (lam m : Smooth)
    (a : ℕ → Amplitude Smooth) : Prop :=
  ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
    ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
      (∀ i,∀ᵐ x ∂(volume : Measure X),x∈Metric.ball 0 R → w i x=v i x) ∧
      (∀ i,EqOn (physical (phase h α β) lam m
        ((fun j => cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
          ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 (Metric.ball 0 R)) ∧
      (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (fiveCutoff R hR 0)
        ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
          (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
      ‖w‖≤C*h^7 ∧ ‖q‖≤C*h

theorem physical_column_of_recursion (R : ℝ) (hR : 1≤R) (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x,star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x,star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x,(m : X → ℂ) x≠0) (he0 : ∀ x,((lam+m+m : Smooth) : X → ℂ) x≠0)
    (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord Metric.isOpen_ball) (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (restrictSmooth (Metric.ball 0 R) lam) (restrictSmooth (Metric.ball 0 R) m)
      (localAmp (Metric.ball 0 R) (a 0)).1 (localAmp (Metric.ball 0 R) (a 0)).2=0)
    (hn₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,RecursOn (U := Metric.ball 0 R) Metric.isOpen_ball
      (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m (a j) (a (j+1))) :
    PhysicalColumn R hR α β lam m a := by
  exact physical_cgo_from_recursion (R+7) (by linarith) (Metric.ball 0 (R+7)) (Metric.ball 0 R)
    Metric.ball_subset_closedBall Metric.isOpen_ball (Metric.ball_subset_ball (by linarith))
    α β hα hθ lam m hl hm hrl hrm hm0 he0 (fiveCutoff R hR) (fiveCutoff_smooth R hR)
    (fiveCutoff_compact R hR) (fiveCutoff_nested R hR) (fiveCutoff_inside R hR)
    (fiveCutoff_initial R hR) a hR₀ hn₀ hrec

/-- A full genuine rank-three constrained frame of actual physical CGO
columns for every smooth, constant-exterior, strongly convex real Lamé pair.
The amplitudes and all corrections are constructed, not postulated. -/
theorem exists_real_physical_cgo_frame (R : ℝ) (hR : 1≤R) (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : X → ℝ) (hl : ContDiff ℝ (⊤ : ℕ∞) lam) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x)
    (hcl : ExteriorConstant (smoothOfReal lam hl)) (hcm : ExteriorConstant (smoothOfReal m hm)) :
    let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
    let l := smoothOfReal lam hl
    let μ := smoothOfReal m hm
    let r := positiveRoot m hm (fun x => (hp x).1)
    let hr := positiveRoot_nonzero m hm (fun x => (hp x).1)
    ∃ a : Fin 3 → ℕ → Amplitude Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ ν,normal θ (a ν 0).1=0) ∧
      (∀ ν,PhysicalColumn R hR α β l μ (a ν)) ∧
      ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (changeP r (a ν 0).1 i : X → ℂ) x),
          (changeS (l+μ) r hr (a ν 0).1 (a ν 0).2 : X → ℂ) x) := by
  intro θ l μ r hr
  have hne : θ≠0 := by
    intro hz
    apply hα
    ext i
    change α i=0
    have hi := congrArg Complex.re (congrFun hz i)
    simpa only [θ,Pi.zero_apply,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,one_mul,sub_zero,add_zero,Complex.zero_re] using hi
  have hC : IsCompact (closure (Metric.ball (0 : X) R)) :=
    (isCompact_closedBall (0 : X) R).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  obtain ⟨a,B,hn,he,hrec,hB⟩ := exists_real_physical_series Metric.isOpen_ball hC θ hθ hne lam m hl hm hp
  refine ⟨a,B,hn,fun ν => ?_,hB⟩
  apply physical_column_of_recursion R hR α β hα hθ l μ hcl hcm
    (fun x => Complex.conj_ofReal _) (fun x => Complex.conj_ofReal _)
    (fun x => Complex.ofReal_ne_zero.mpr (hp x).1.ne') (fun x => ?_)
    (a ν) (he ν).1 (hn ν) (fun j _ => hrec ν j)
  change (lam x : ℂ)+(m x : ℂ)+(m x : ℂ)≠0
  exact_mod_cast (real_longitudinal_positive lam m hp x).ne'
end ElasticityCGO
namespace ElasticityCGO
open Set MeasureTheory TemperedDistribution

section
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityRegularity (sobolevInjection)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityCarleman (phaseCLM)
open ElasticityDistribution (HV Dist divd)

def cgoField (R : ℝ) (hR : 1≤R) (h : ℝ) (α β : X)
    (a : ℕ → Amplitude Smooth) (v : Fin 3 → S) (i : Fin 3) : S :=
  expCut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
    (phase h α β)
    (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
      ((truncation (h : ℂ) 8 a).1 i)-v i)

theorem cgoField_apply_on (R : ℝ) (hR : 1≤R) (h : ℝ) (α β : X)
    (a : ℕ → Amplitude Smooth) (v : Fin 3 → S) (i : Fin 3) {x : X}
    (hx : x∈Metric.ball 0 R) :
    cgoField R hR h α β a v i x=Complex.exp (phaseCLM (phase h α β) x)*
      (((truncation (h : ℂ) 8 a).1 i : X → ℂ) x-v i x) := by
  change expCut _ _ _ _ x=_
  rw [expCut_apply]
  change fiveCutoff R hR 0 x*Complex.exp (phaseCLM (phase h α β) x)*
    (fiveCutoff R hR 0 x*(((truncation (h : ℂ) 8 a).1 i : X → ℂ) x)-v i x)=_
  rw [fiveCutoff_initial R hR hx]
  simp only [Pi.one_apply,one_mul]

/-- Realization of the constructed physical column by a literal exponential
solution of the original (not augmented) elasticity equation. -/
theorem physical_column_realization (R : ℝ) (hR : 1≤R) (α β : X) (lam m : Smooth)
    (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a) :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
        (∀ i,∀ᵐ x ∂(volume : Measure X),x∈Metric.ball 0 R → w i x=v i x) ∧
        (∀ i,EqOn (physical 0 lam m (cgoField R hR h α β a v) i : X → ℂ) 0 (Metric.ball 0 R)) ∧
        (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (fiveCutoff R hR 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖≤C*h^7 ∧ ‖q‖≤C*h := by
  obtain ⟨C,h₀,hC,hh₀,hsol⟩ := ha
  refine ⟨C,h₀,hC,hh₀,fun h hh hsmall => ?_⟩
  obtain ⟨w,q,v,hv,hp,hq,hw,hn⟩ := hsol h hh hsmall
  refine ⟨w,q,v,hv,?_,hq,hw,hn⟩
  exact expCut_solution Metric.isOpen_ball lam m
    ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ hl.growth hm.growth
    (fiveCutoff_compact R hR 0) (fiveCutoff_initial R hR) (phase h α β)
    ((fun j => cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
      ((truncation (h : ℂ) 8 a).1 j))-v) hp
end
open scoped SchwartzMap LineDeriv BigOperators ENNReal
open ElasticityRegularity ElasticityAugmented
open ElasticityBessel (norm2 J)
open ElasticityNegativeOrder (mult sobNorm sumNorm)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityDistribution (HV Dist divd)

lemma local_lp_schwartz_of_ae {U : Set X} (w : Lp ℂ 2 (volume : Measure X)) (v : S)
    (hv : ∀ᵐ x ∂(volume : Measure X),x∈U → w x=v x) :
    LocalEqual U (w : Dist) (v : Dist) := by
  intro φ _ hs
  calc
    _ = ∫ x,φ x • w x := Lp.toTemperedDistribution_apply w φ
    _ = ∫ x,φ x • v x := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      by_cases hφ : φ x=0
      · rw [hφ,zero_smul,zero_smul]
      · rw [hx (hs (subset_tsupport _ hφ))]
    _ = _ := (SchwartzMap.coe_apply v φ).symm

/-- The local standard-H1 representative controls the SAME physical
correction and its actual shifted divergence. -/
lemma actual_augmented_local_representative {U : Set X} (z : Fin 3 → ℂ)
    (χ : X → ℂ) (hχ : χ.HasTemperateGrowth) (h1 : EqOn χ 1 U)
    (w : ElasticityPhysicalDual.H) (q : HV) (v : Fin 3 → S)
    (hv : ∀ i,∀ᵐ x ∂(volume : Measure X),x∈U → w i x=v i x)
    (hq : ∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ χ
      ((Fin.cons (divd z (fun j => (w j : Dist))) (fun j => (w j : Dist)) : Fin 4 → Dist) i)) :
    ∀ i,LocalEqual U (sobolevInjection 1 (q i)) (physicalAug z v i : Dist) := by
  have hl (i : Fin 3) := local_lp_schwartz_of_ae (w i) (v i) (hv i)
  intro i
  rw [hq i]
  apply (LocalEqual.cutoff_one _ hχ h1).trans
  refine Fin.cases ?_ (fun i => hl i) i
  have hd := ElasticityDistribution.LocalEq.divergence hl z
  rw [ElasticityDistribution.divd_schwartz] at hd
  exact hd

/-- Uniform compactly localized augmented correction bound; the scalar
component is not independent of the displacement. -/
theorem actual_augmented_cutoff_bound {U : Set X} {g : X → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (hs : tsupport g⊆U) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0≤h → h≤1 → ∀ z : Fin 3 → ℂ,
      ∀ χ : X → ℂ,χ.HasTemperateGrowth → EqOn χ 1 U →
      ∀ w : ElasticityPhysicalDual.H,∀ q : HV,∀ v : Fin 3 → S,
      (∀ i,∀ᵐ x ∂(volume : Measure X),x∈U → w i x=v i x) →
      (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ χ
        ((Fin.cons (divd z (fun j => (w j : Dist))) (fun j => (w j : Dist)) : Fin 4 → Dist) i)) →
      sobNorm h 1 (fun i => mult g (physicalAug z v i))≤C*‖q‖ := by
  obtain ⟨C,hC,hest⟩ := local_standard_H1_controls_semiclassical hg hc hs
  refine ⟨4*C,by positivity,fun h hh hh1 z χ hχ h1 w q v hv hq => ?_⟩
  have hl := actual_augmented_local_representative z χ hχ h1 w q v hv hq
  have hb (i : Fin 4) : norm2 (J h 1 (mult g (physicalAug z v i)))≤C*‖q‖ := by
    exact (hest h hh hh1 _ (q i) (hl i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm q i) hC.le)
  apply (ElasticityNegativeOrder.sobNorm_le_sumNorm h 1 _).trans
  calc
    sumNorm h 1 (fun i => mult g (physicalAug z v i))≤∑ i : Fin 4,C*‖q‖ :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = (4*C)*‖q‖ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma divShift_mult (z : Fin 3 → ℂ) (g : X → ℂ) (hg : g.HasTemperateGrowth)
    (v : Fin 3 → S) :
    ElasticityPhysicalAlgebra.divShift z (fun i => mult g (v i))=
      mult g (ElasticityPhysicalAlgebra.divShift z v)+
        ∑ i,mult (fun x => fderiv ℝ g x (e i)) (v i) := by
  have hd (i : Fin 3) : (fun x => fderiv ℝ g x (e i)).HasTemperateGrowth :=
    ElasticityPhysicalAlgebra.temperate_partial g hg (e i)
  ext x
  simp only [ElasticityPhysicalAlgebra.divShift,sum_apply,
    ElasticityPhysicalAlgebra.shiftD_apply,add_apply,smul_apply,
    ElasticityNegativeOrder.d_mult_apply g hg,
    ElasticityNegativeOrder.mult_apply g hg,
    ElasticityNegativeOrder.mult_apply _ (hd _),smul_eq_mul,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [ElasticitySchwartzCarleman.e,ElasticityAugmented.e]
  ring

/-- Cutting off the displacement itself retains a uniformly controlled
ACTUAL augmented field. The derivative of the cutoff has no phase loss. -/
theorem cut_actual_augmented_bound {U : Set X} {g : X → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (hs : tsupport g⊆U) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0≤h → h≤1 → ∀ z : Fin 3 → ℂ,
      ∀ q : HV,∀ v : Fin 3 → S,
      (∀ i,LocalEqual U (sobolevInjection 1 (q i)) (physicalAug z v i : Dist)) →
      sobNorm h 1 (physicalAug z (fun i => mult g (v i)))≤C*‖q‖ := by
  obtain ⟨C,hC,hest⟩ := local_standard_H1_controls_semiclassical hg hc hs
  have hed (i : Fin 3) := local_standard_H1_controls_semiclassical
    (smooth_derivative hg (e i)) (compact_derivative hc (e i))
    ((tsupport_fderiv_apply_subset ℝ (e i)).trans hs)
  choose D hD hdest using hed
  have hDsum : 0≤∑ i,D i := Finset.sum_nonneg (fun i _ => (hD i).le)
  refine ⟨4*C+∑ i,D i,by positivity,fun h hh hh1 z q v hq => ?_⟩
  have hbase (i : Fin 4) : norm2 (J h 1 (mult g (physicalAug z v i)))≤C*‖q‖ :=
    (hest h hh hh1 _ (q i) (hq i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm q i) hC.le)
  have hder (i : Fin 3) :
      norm2 (J h 1 (mult (fun x => fderiv ℝ g x (e i)) (v i)))≤D i*‖q‖ :=
    (hdest i h hh hh1 _ (q i.succ) (hq i.succ)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm q i.succ) (hD i).le)
  have hsc : norm2 (J h 1 (ElasticityPhysicalAlgebra.divShift z (fun i => mult g (v i))))≤
      C*‖q‖+(∑ i,D i)*‖q‖ := by
    rw [divShift_mult z g (hc.hasTemperateGrowth hg),ElasticityBessel.J_add,
      ElasticityPhysicalEstimate.J_sum]
    calc
      _ ≤ norm2 (J h 1 (mult g (ElasticityPhysicalAlgebra.divShift z v)))+
        norm2 (∑ i,J h 1 (mult (fun x => fderiv ℝ g x (e i)) (v i))) :=
          ElasticityBessel.norm2_add_le _ _
      _ ≤ C*‖q‖+∑ i,D i*‖q‖ := add_le_add (hbase 0)
        ((ElasticityNegativeOrder.norm2_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hder i)))
      _ = _ := by rw [Finset.sum_mul]
  apply (ElasticityNegativeOrder.sobNorm_le_sumNorm h 1 _).trans
  change (∑ i : Fin 4,norm2 (J h 1 (physicalAug z (fun i => mult g (v i)) i)))≤_
  rw [Fin.sum_univ_succ]
  change norm2 (J h 1 (ElasticityPhysicalAlgebra.divShift z (fun i => mult g (v i))))+
    (∑ i : Fin 3,norm2 (J h 1 (mult g (v i))))≤_
  calc
    _ ≤ (C*‖q‖+(∑ i,D i)*‖q‖)+∑ _i : Fin 3,C*‖q‖ :=
      add_le_add hsc (Finset.sum_le_sum (fun i _ => hbase i.succ))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
end ElasticityCGO
namespace ElasticityCGO
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityRegularity (sobolevInjection)
open ElasticityDistribution (HV Dist divd)

/-- The actual physical CGO corrections have a uniform localized augmented
semiclassical H1 bound. Localize the displacement and then take its actual
shifted divergence: the scalar is not a separately prescribed amplitude. -/
theorem physical_column_localized_realization (R : ℝ) (hR : 1≤R) (α β : X)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Metric.ball 0 R) :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ h₀≤1 ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
        (∀ i,∀ᵐ x ∂(volume : Measure X),x∈Metric.ball 0 R → w i x=v i x) ∧
        (∀ i,EqOn (physical 0 lam m (cgoField R hR h α β a v) i : X → ℂ) 0 (Metric.ball 0 R)) ∧
        (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (fiveCutoff R hR 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖≤C*h^7 ∧ ‖q‖≤C*h ∧
        sobNorm h 1 (physicalAug (phase h α β) (fun i => mult g (v i)))≤C*h := by
  obtain ⟨C₀,h₀,hC₀,hh₀,hsol⟩ := physical_column_realization R hR α β lam m hl hm a ha
  obtain ⟨D,hD,hest⟩ := cut_actual_augmented_bound hg hc hs
  let C := C₀*(1+D)
  have hC : 0<C := by dsimp [C]; positivity
  have hle : C₀≤C := by dsimp [C]; nlinarith
  have hmul : D*C₀≤C := by dsimp [C]; nlinarith
  refine ⟨C,min h₀ 1,hC,lt_min hh₀ (by norm_num),min_le_right _ _,fun h hh hsml => ?_⟩
  have hhh₀ : h≤h₀ := hsml.trans (min_le_left _ _)
  have hh1 : h≤1 := hsml.trans (min_le_right _ _)
  obtain ⟨w,q,v,hv,hp,hq,hw,hn⟩ := hsol h hh hhh₀
  refine ⟨w,q,v,hv,hp,hq,hw.trans (mul_le_mul_of_nonneg_right hle (by positivity)),
    hn.trans (mul_le_mul_of_nonneg_right hle hh.le),?_⟩
  have hloc := actual_augmented_local_representative (phase h α β) (fiveCutoff R hR 0)
    ((fiveCutoff_compact R hR 0).hasTemperateGrowth (fiveCutoff_smooth R hR 0))
    (fiveCutoff_initial R hR) w q v hv hq
  calc
    _ ≤ D*‖q‖ := hest h hh.le hh1 (phase h α β) q v hloc
    _ ≤ D*(C₀*h) := mul_le_mul_of_nonneg_left hn hD.le
    _ = (D*C₀)*h := by ring
    _ ≤ C*h := mul_le_mul_of_nonneg_right hmul hh.le

/-- The actual physical CGO corrections have a uniform localized augmented
semiclassical H1 bound. Localize the displacement and then take its actual
shifted divergence: the scalar is not a separately prescribed amplitude. -/
theorem physical_column_shifted_realization (R : ℝ) (hR : 1≤R) (α β : X)
    (lam m : Smooth)
    (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Metric.ball 0 R) :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ h₀≤1 ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
        (∀ i,∀ᵐ x ∂(volume : Measure X),x∈Metric.ball 0 R → w i x=v i x) ∧
        (∀ i,EqOn (physical (phase h α β) lam m
          ((fun j => cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
            ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 (Metric.ball 0 R)) ∧
        (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (fiveCutoff R hR 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖≤C*h^7 ∧ ‖q‖≤C*h ∧
        sobNorm h 1 (physicalAug (phase h α β) (fun i => mult g (v i)))≤C*h := by
  obtain ⟨C₀,h₀,hC₀,hh₀,hsol⟩ := ha
  obtain ⟨D,hD,hest⟩ := cut_actual_augmented_bound hg hc hs
  let C := C₀*(1+D)
  have hC : 0<C := by dsimp [C]; positivity
  have hle : C₀≤C := by dsimp [C]; nlinarith
  have hmul : D*C₀≤C := by dsimp [C]; nlinarith
  refine ⟨C,min h₀ 1,hC,lt_min hh₀ (by norm_num),min_le_right _ _,fun h hh hsml => ?_⟩
  have hhh₀ : h≤h₀ := hsml.trans (min_le_left _ _)
  have hh1 : h≤1 := hsml.trans (min_le_right _ _)
  obtain ⟨w,q,v,hv,hp,hq,hw,hn⟩ := hsol h hh hhh₀
  refine ⟨w,q,v,hv,hp,hq,hw.trans (mul_le_mul_of_nonneg_right hle (by positivity)),
    hn.trans (mul_le_mul_of_nonneg_right hle hh.le),?_⟩
  have hloc := actual_augmented_local_representative (phase h α β) (fiveCutoff R hR 0)
    ((fiveCutoff_compact R hR 0).hasTemperateGrowth (fiveCutoff_smooth R hR 0))
    (fiveCutoff_initial R hR) w q v hv hq
  calc
    _ ≤ D*‖q‖ := hest h hh.le hh1 (phase h α β) q v hloc
    _ ≤ D*(C₀*h) := mul_le_mul_of_nonneg_left hn hD.le
    _ = (D*C₀)*h := by ring
    _ ≤ C*h := mul_le_mul_of_nonneg_right hmul hh.le
end ElasticityCGO
section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityAugmented
lemma restrict_divT {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (a : Fin 3 → Smooth) :
    restrictSmooth U (divT (shifted coord z) a)=
      divT (shifted (localCoord hU) z) (fun j => restrictSmooth U (a j)) := by
  simp only [divT,map_sum,restrict_shifted hU]

/-- The actual finite divergence constraint on an open physical region. -/
theorem truncation_divergence_on {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (h : ℂ) (hh : h≠0) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U) :
    EqOn ((divT (shifted coord (h⁻¹ • θ)) (truncation h N a).1 : Smooth) : X → ℂ)
      (((truncation h N a).2+h^N • (div coord (a N).1-(a N).2) : Smooth) : X → ℂ) U := by
  have hn₀ : normal θ (localAmp U (a 0)).1=0 := by
    simp only [localAmp,← restrict_normal,h₀,map_zero]
  have hn (j) (hj : j<N) : normal θ (localAmp U (a (j+1))).1=
      -(div (localCoord hU) (localAmp U (a j)).1-(localAmp U (a j)).2) := by
    have he := (restrictSmooth_eq_iff U _ _).mpr (hrec j hj)
    simpa only [restrict_normal,map_neg,map_sub,restrict_div hU,localAmp] using he
  have ht := truncated_divergence (localCoord hU) θ h hh N (fun j => localAmp U (a j)) hn₀ hn
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [restrict_divT hU]
  change divT (shifted (localCoord hU) (h⁻¹ • θ)) (localAmp U (truncation h N a)).1=_
  rw [localAmp_truncation,ht]
  simp only [map_add,map_smul,map_sub,restrict_div hU]
  congr 1
  exact congrArg Prod.snd (localAmp_truncation U h N a).symm
end ElasticityAugmented

namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply toSmooth_divShift divShift)
lemma divShift_cut_local {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 U) (u : Fin 3 → Smooth) :
    EqOn (divShift z (fun j => cut χ hc (u j)) : X → ℂ)
      ((divT (shifted coord z) u : Smooth) : X → ℂ) U := by
  change EqOn ((toSmooth (divShift z (fun j => cut χ hc (u j))) : Smooth) : X → ℂ) _ U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_divShift,restrict_divT hU,restrict_divT hU]
  congr 1
  funext j
  exact cut_local χ hc hχ (u j)

/-- The exact scalar augmented amplitude has the same eight-order truncation
plus a single h^8 defect. No unjustified differentiation of small L2 errors. -/
theorem cut_truncation_divergence {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (h : ℂ) (hh : h≠0) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U) :
    EqOn (divShift (h⁻¹ • θ) (fun j => cut χ hc ((truncation h N a).1 j)) : X → ℂ)
      (cut χ hc ((truncation h N a).2+h^N • (div coord (a N).1-(a N).2))) U := by
  intro x hx
  rw [divShift_cut_local hU _ χ hc hχ _ hx,truncation_divergence_on hU θ h hh N a h₀ hrec hx,
    cut_apply,hχ hx]
  exact (one_mul _).symm
end ElasticityCGO

end
namespace ElasticityCGO

section
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2 norm2_nonneg J_smul norm2_const_smul)
open ElasticityNegativeOrder (H1_energy)
open ElasticitySchwartzCarleman (gradientMass_nonneg)

lemma semiclassical_H1_le_H1 (h : ℝ) (hh : 0≤h) (hh1 : h≤1) (f : S) :
    norm2 (J h 1 f)≤norm2 (J 1 1 f) := by
  have hsq : h^2≤1 := by nlinarith
  have he := H1_energy h f
  have he1 := H1_energy 1 f
  have hm := mul_le_mul_of_nonneg_right hsq (gradientMass_nonneg f)
  norm_num only [one_pow,one_mul] at he1 hm
  nlinarith only [he,he1,hm,norm2_nonneg (J h 1 f),norm2_nonneg (J 1 1 f)]

/-- A literal finite Schwartz amplitude polynomial is uniformly bounded
in the semiclassical H1 norm. There is no h-dependent Sobolev constant. -/
theorem finite_polynomial_H1_bound (N : ℕ) (f : ℕ → S) (h : ℝ)
    (hh : 0≤h) (hh1 : h≤1) :
    norm2 (J h 1 (truncation (h : ℂ) N f))≤
      ∑ j ∈ Finset.range (N+1),norm2 (J 1 1 (f j)) := by
  rw [truncation,ElasticityPhysicalEstimate.J_sum]
  apply (ElasticityNegativeOrder.norm2_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [J_smul,norm2_const_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh]
  calc
    _ ≤ 1*norm2 (J h 1 (f j)) :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hh hh1) (norm2_nonneg _)
    _ ≤ norm2 (J 1 1 (f j)) := by simpa only [one_mul] using semiclassical_H1_le_H1 h hh hh1 (f j)

lemma cut_truncation (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (h : ℂ) (N : ℕ) (a : ℕ → Smooth) :
    cut χ hc (truncation h N a)=truncation h N (fun j => cut χ hc (a j)) := by
  simp only [truncation,map_sum,map_smul]

/-- The formal smooth amplitudes need no global growth hypothesis: after
the actual compact cutoff, their finite order-eight truncations have a
uniform H_h^1 bound. -/
theorem cut_polynomial_H1_bound (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (N : ℕ) (a : ℕ → Smooth) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0≤h → h≤1 →
      norm2 (J h 1 (cut χ hc (truncation (h : ℂ) N a)))≤C := by
  let C := 1+∑ j ∈ Finset.range (N+1),norm2 (J 1 1 (cut χ hc (a j)))
  have hs : 0≤∑ j ∈ Finset.range (N+1),norm2 (J 1 1 (cut χ hc (a j))) :=
    Finset.sum_nonneg (fun j _ => norm2_nonneg _)
  refine ⟨C,by dsimp [C]; linarith,fun h hh hh1 => ?_⟩
  rw [cut_truncation]
  exact (finite_polynomial_H1_bound N _ h hh hh1).trans (by dsimp [C]; linarith)
end
open Set
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2 norm2_nonneg J_smul norm2_const_smul)
open ElasticityNegativeOrder (mult mult_apply)
open ElasticityPhysicalAlgebra (divShift)

lemma truncation_scalar (h : ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth) :
    (truncation h N a).2=truncation h N (fun j => (a j).2) := by
  induction N with
  | zero => simp only [truncation_zero]
  | succ N ih =>
    rw [truncation_succ,truncation_succ]
    change (truncation h N a).2+h^(N+1) • (a (N+1)).2=_
    rw [ih]
lemma truncation_vector (h : ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth) (i : Fin 3) :
    (truncation h N a).1 i=truncation h N (fun j => (a j).1 i) := by
  induction N with
  | zero => simp only [truncation_zero]
  | succ N ih =>
    rw [truncation_succ,truncation_succ]
    change (truncation h N a).1 i+h^(N+1) • (a (N+1)).1 i=_
    rw [ih]

lemma mult_eq_of_local {U : Set X} {g : X → ℂ} (hg : g.HasTemperateGrowth)
    (hs : tsupport g⊆U) {f k : S} (hf : EqOn (f : X → ℂ) k U) :
    mult g f=mult g k := by
  ext x
  rw [mult_apply g hg,mult_apply g hg]
  by_cases h : g x=0
  · simp only [h,zero_mul]
  · rw [hf (hs (subset_tsupport _ h))]

lemma H1_monomial_bound (h : ℝ) (hh : 0≤h) (hh1 : h≤1) (N : ℕ) (f : S) :
    norm2 (J h 1 ((h : ℂ)^N • f))≤norm2 (J 1 1 f) := by
  rw [J_smul,norm2_const_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hh hh1) (norm2_nonneg _)).trans
    (by simpa only [one_mul] using semiclassical_H1_le_H1 h hh hh1 f)

/-- The formal divergence, localized strictly inside the physical region,
is uniformly H_h^1 bounded. The apparent h⁻¹ term is removed by the actual
finite divergence recurrence, not by estimating an independent scalar. -/
theorem localized_formal_divergence_H1_bound {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆U) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0<h → h≤1 →
      norm2 (J h 1 (mult g (divShift ((h : ℂ)⁻¹ • θ)
        (fun j => cut χ hc ((truncation (h : ℂ) N a).1 j)))))≤C := by
  let b : ℕ → S := fun j => mult g (cut χ hc (a j).2)
  let d : S := mult g (cut χ hc (div coord (a N).1-(a N).2))
  let B := ∑ j ∈ Finset.range (N+1),norm2 (J 1 1 (b j))
  let D := norm2 (J 1 1 d)
  have hB : 0≤B := Finset.sum_nonneg (fun j _ => norm2_nonneg _)
  have hD : 0≤D := norm2_nonneg _
  refine ⟨1+B+D,by linarith only [hB,hD],fun h hh hh1 => ?_⟩
  have he := cut_truncation_divergence hU θ (h : ℂ) (Complex.ofReal_ne_zero.mpr hh.ne')
    N a h₀ hrec χ hc hχ
  rw [mult_eq_of_local hg hs he]
  have hp : mult g (cut χ hc ((truncation (h : ℂ) N a).2+
      (h : ℂ)^N • (div coord (a N).1-(a N).2)))=
      truncation (h : ℂ) N b+(h : ℂ)^N • d := by
    rw [truncation_scalar]
    simp only [map_add,map_smul,cut_truncation]
    simp only [truncation,map_sum,map_smul,b,d]
  rw [hp,ElasticityBessel.J_add]
  calc
    _ ≤ norm2 (J h 1 (truncation (h : ℂ) N b))+norm2 (J h 1 ((h : ℂ)^N • d)) :=
      ElasticityBessel.norm2_add_le _ _
    _ ≤ B+D := add_le_add (finite_polynomial_H1_bound N b h hh.le hh1)
      (H1_monomial_bound h hh.le hh1 N d)
    _ ≤ 1+B+D := by linarith
end ElasticityCGO
namespace ElasticityCGO
open Set
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2 norm2_nonneg)
open ElasticityNegativeOrder (mult sobNorm sumNorm)
open ElasticityPhysicalAlgebra (divShift)
open ElasticityPhysicalEstimate (physicalAug)

lemma mult_cut_truncation_vector (g : X → ℂ) (χ : Smooth)
    (hc : HasCompactSupport (χ : X → ℂ)) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h : ℂ) (i : Fin 3) :
    mult g (cut χ hc ((truncation h N a).1 i))=
      truncation h N (fun j => mult g (cut χ hc ((a j).1 i))) := by
  rw [truncation_vector,cut_truncation]
  simp only [truncation,map_sum,map_smul]

/-- Fixed interior localization of the whole formal physical displacement
has a uniformly bounded ACTUAL four-component H_h^1 amplitude. The singular
phase is cancelled by the actual divergence recurrence. -/
theorem localized_formal_augmented_H1_bound {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆U) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0<h → h≤1 →
      sobNorm h 1 (physicalAug ((h : ℂ)⁻¹ • θ)
        (fun i => mult g (cut χ hc ((truncation (h : ℂ) N a).1 i))))≤C := by
  obtain ⟨C,hC,hscalar⟩ := localized_formal_divergence_H1_bound hU θ N a h₀ hrec χ hc hχ hg hs
  let dg : Fin 3 → X → ℂ := fun i x => fderiv ℝ g x (e i)
  let B : Fin 3 → ℝ := fun i => ∑ j ∈ Finset.range (N+1),
    norm2 (J 1 1 (mult g (cut χ hc ((a j).1 i))))
  let D : Fin 3 → ℝ := fun i => ∑ j ∈ Finset.range (N+1),
    norm2 (J 1 1 (mult (dg i) (cut χ hc ((a j).1 i))))
  have hB (i) : 0≤B i := Finset.sum_nonneg (fun j _ => norm2_nonneg _)
  have hD (i) : 0≤D i := Finset.sum_nonneg (fun j _ => norm2_nonneg _)
  have hBs : 0≤∑ i,B i := Finset.sum_nonneg (fun i _ => hB i)
  have hDs : 0≤∑ i,D i := Finset.sum_nonneg (fun i _ => hD i)
  refine ⟨C+(∑ i,D i)+(∑ i,B i),by linarith only [hC,hBs,hDs],fun h hh hh1 => ?_⟩
  let u : Fin 3 → S := fun i => cut χ hc ((truncation (h : ℂ) N a).1 i)
  have hv (i : Fin 3) : norm2 (J h 1 (mult g (u i)))≤B i := by
    dsimp only [u]
    rw [mult_cut_truncation_vector]
    exact finite_polynomial_H1_bound N _ h hh.le hh1
  have hd (i : Fin 3) : norm2 (J h 1 (mult (dg i) (u i)))≤D i := by
    dsimp only [u]
    rw [mult_cut_truncation_vector]
    exact finite_polynomial_H1_bound N _ h hh.le hh1
  have hsc : norm2 (J h 1 (divShift ((h : ℂ)⁻¹ • θ) (fun i => mult g (u i))))≤C+∑ i,D i := by
    rw [divShift_mult _ g hg,ElasticityBessel.J_add,ElasticityPhysicalEstimate.J_sum]
    apply (ElasticityBessel.norm2_add_le _ _).trans
    exact add_le_add (hscalar h hh hh1)
      ((ElasticityNegativeOrder.norm2_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hd i)))
  apply (ElasticityNegativeOrder.sobNorm_le_sumNorm h 1 _).trans
  change (∑ i : Fin 4,norm2 (J h 1 (physicalAug ((h : ℂ)⁻¹ • θ)
    (fun j => mult g (u j)) i)))≤_
  rw [Fin.sum_univ_succ]
  exact add_le_add hsc (Finset.sum_le_sum (fun i _ => hv i))
end ElasticityCGO
namespace ElasticityCGO
open Set
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2)
open ElasticityNegativeOrder (mult sobNorm sumNorm)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityCoeffBounds (ExteriorConstant)

lemma sobNorm_sub_four (h s : ℝ) (u v : Fin 4 → S) :
    sobNorm h s (u-v)≤2*(sobNorm h s u+sobNorm h s v) := by
  apply (ElasticityNegativeOrder.sobNorm_le_sumNorm h s _).trans
  have hs : sumNorm h s (u-v)≤ sumNorm h s u+sumNorm h s v := by
    simp only [sumNorm,Pi.sub_apply,ElasticityNegativeOrder.J_sub,← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => ElasticityNegativeOrder.norm2_sub_le _ _)
  have hu := ElasticityNegativeOrder.sumNorm_four_le h s u
  have hv := ElasticityNegativeOrder.sumNorm_four_le h s v
  linarith only [hs,hu,hv]

/-- Literal original-PDE CGO solutions can be chosen with a uniformly
bounded actual compact augmented amplitude. Both the formal divergence and
the correction divergence are proved bounds, not additional assumptions. -/
theorem localized_actual_amplitude_bound (R : ℝ) (hR : 1≤R) (α β : X)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn
      (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Metric.ball 0 R) :
    ∃ C h₁ : ℝ,0<C ∧ 0<h₁ ∧ ∀ h : ℝ,0<h → h≤h₁ → ∃ v : Fin 3 → S,
      (∀ i,EqOn (physical 0 lam m (cgoField R hR h α β a v) i : X → ℂ) 0 (Metric.ball 0 R)) ∧
      sobNorm h 1 (physicalAug (phase h α β) (fun i => mult g
        (cut ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
          ((truncation (h : ℂ) 8 a).1 i)-v i)))≤C := by
  let χ : Smooth := ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩
  have hcχ : HasCompactSupport (χ : X → ℂ) := fiveCutoff_compact R hR 0
  obtain ⟨A,hA,hformal⟩ := localized_formal_augmented_H1_bound Metric.isOpen_ball
    (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) 8 a h₀ hrec χ hcχ
    (fiveCutoff_initial R hR) (hc.hasTemperateGrowth hg) hs
  obtain ⟨D,h₁,hD,hh₁,hh₁1,hsol⟩ := physical_column_localized_realization
    R hR α β lam m hl hm a ha hg hc hs
  refine ⟨2*(A+D),h₁,by linarith only [hA,hD],hh₁,fun h hh hsmall => ?_⟩
  obtain ⟨w,q,v,_hv,hp,_hq,_hw,_hn,hbound⟩ := hsol h hh hsmall
  refine ⟨v,hp,?_⟩
  have hh1 : h≤1 := hsmall.trans hh₁1
  have hf := hformal h hh hh1
  rw [← phase_eq] at hf
  let u : Fin 3 → S := fun i => mult g (cut χ hcχ ((truncation (h : ℂ) 8 a).1 i))
  let v' : Fin 3 → S := fun i => mult g (v i)
  have he : (fun i => mult g (cut χ hcχ ((truncation (h : ℂ) 8 a).1 i)-v i))=u-v' := by
    funext i
    exact map_sub (mult g) _ _
  change sobNorm h 1 (physicalAug (phase h α β)
    (fun i => mult g (cut χ hcχ ((truncation (h : ℂ) 8 a).1 i)-v i)))≤_
  rw [he,ElasticityPhysicalEstimate.physicalAug_sub]
  have hn := sobNorm_sub_four h 1 (physicalAug (phase h α β) u) (physicalAug (phase h α β) v')
  change sobNorm h 1 (physicalAug (phase h α β) u)≤A at hf
  change sobNorm h 1 (physicalAug (phase h α β) v')≤D*h at hbound
  have hDh : D*h≤D := by nlinarith only [hD,hh1]
  linarith only [hn,hf,hbound,hDh]
end ElasticityCGO

end

end OAI
