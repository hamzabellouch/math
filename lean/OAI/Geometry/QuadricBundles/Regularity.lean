import OAI.Geometry.QuadricBundles.Charts

namespace OAI

namespace QuadricCounterexample
open Set Filter Topology MvPolynomial
noncomputable section

@[simp] lemma baseEval_add (p q : BasePolynomial) (z : BaseCoordinates) :
    baseEval (p+q) z=baseEval p z+baseEval q z := by simp [baseEval]
@[simp] lemma baseEval_neg (p : BasePolynomial) (z : BaseCoordinates) :
    baseEval (-p) z= -baseEval p z := by simp [baseEval]
@[simp] lemma baseEval_sub (p q : BasePolynomial) (z : BaseCoordinates) :
    baseEval (p-q) z=baseEval p z-baseEval q z := by simp [baseEval]
@[simp] lemma baseEval_C (a : ℂ) (z : BaseCoordinates) : baseEval (C a) z=a := by simp [baseEval]

lemma AlgebraicallyRegularOn.add {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (hg : AlgebraicallyRegularOn U g) :
    AlgebraicallyRegularOn U (fun z ↦ f z+g z) := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf z hz
  obtain ⟨r,s,hs,k⟩ := hg z hz
  refine ⟨p*s+r*q,q*s,by simpa using mul_ne_zero hq hs,?_⟩
  intro w hw hqw
  have hh : baseEval q w ≠ 0 ∧ baseEval s w ≠ 0 := by simpa using hqw
  dsimp only
  rw [h w hw hh.1,k w hw hh.2]
  simp only [baseEval_add,baseEval_mul]
  simpa only [mul_comm] using (div_add_div (baseEval p w) (baseEval r w) hh.1 hh.2)

lemma AlgebraicallyRegularOn.neg {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) : AlgebraicallyRegularOn U (fun z ↦ -f z) := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf z hz
  exact ⟨-p,q,hq,fun w hw hqw ↦ by dsimp only; rw [h w hw hqw,baseEval_neg,neg_div]⟩
lemma AlgebraicallyRegularOn.sub {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (hg : AlgebraicallyRegularOn U g) :
    AlgebraicallyRegularOn U (fun z ↦ f z-g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma AlgebraicallyRegularOn.inv {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (hn : ∀ z ∈ U, f z ≠ 0) :
    AlgebraicallyRegularOn U (fun z ↦ (f z)⁻¹) := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf z hz
  have hp : baseEval p z ≠ 0 := by
    intro hp
    specialize hn z hz
    rw [h z hz hq,hp,zero_div] at hn
    exact hn rfl
  refine ⟨q*q,p*q,by simpa using mul_ne_zero hp hq,?_⟩
  intro w hw hqw
  have hnw : baseEval p w ≠ 0 ∧ baseEval q w ≠ 0 := by simpa using hqw
  dsimp only
  rw [h w hw hnw.2,baseEval_mul,baseEval_mul]
  field_simp

lemma analytic_baseEval (p : BasePolynomial) : AnalyticOnNhd ℂ (baseEval p) univ := by
  intro z _
  have hf : ∀ i : Fin 2, AnalyticAt ℂ (fun w : BaseCoordinates ↦ (![w.1,w.2] : Fin 2 → ℂ) i) z := by
    intro i
    fin_cases i
    · exact (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt z
    · exact (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt z
  have hh := AnalyticAt.aeval_mvPolynomial hf p
  simp only [aeval_eq_eval] at hh
  convert hh using 1
  rfl

lemma AlgebraicallyRegularOn.analyticOnNhd {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : AlgebraicallyRegularOn U f) (hU : IsOpen U) : AnalyticOnNhd ℂ f U := by
  intro z hz
  obtain ⟨p,q,hq,h⟩ := hf z hz
  have ha := (analytic_baseEval p z (mem_univ _)).div (analytic_baseEval q z (mem_univ _)) hq
  apply ha.congr
  filter_upwards [hU.mem_nhds hz, (analytic_baseEval q z (mem_univ _)).continuousAt.eventually_ne hq]
    with w hw hqw
  exact (h w hw hqw).symm

lemma dense_polynomial_nonzero {p : BasePolynomial} (hp : p ≠ 0) :
    Dense {z | baseEval p z ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU ⟨z,hz⟩
  by_contra! h
  have he : baseEval p =ᶠ[𝓝 z] fun _ ↦ 0 := by
    filter_upwards [hU.mem_nhds hz] with w hw
    by_contra hn
    have : w ∈ U ∩ {z | baseEval p z ≠ 0} := ⟨hw,hn⟩
    rw [h] at this
    exact this
  have hall := (analytic_baseEval p).eq_of_eventuallyEq analyticOnNhd_const he
  apply hp
  apply MvPolynomial.funext
  intro x
  have hx : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx,map_zero]
  simpa only [baseEval] using congrFun hall (x 0,x 1)

lemma continuous_cancel_polynomial {U : Set BaseCoordinates} (hU : IsOpen U)
    {f g : BaseCoordinates → ℂ} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    {p : BasePolynomial} (hp : p ≠ 0)
    (he : ∀ z ∈ U, baseEval p z*f z=baseEval p z*g z) : EqOn f g U := by
  intro z hz
  by_contra hne
  have hat : ContinuousAt (fun w ↦ f w-g w) z :=
    ((hf z hz).continuousAt (hU.mem_nhds hz)).sub ((hg z hz).continuousAt (hU.mem_nhds hz))
  have hn : ∀ᶠ w in 𝓝 z, w ∈ U ∧ f w ≠ g w := by
    filter_upwards [hU.mem_nhds hz,hat.eventually_ne (sub_ne_zero.mpr hne)] with w hw hnw
    exact ⟨hw,sub_ne_zero.mp hnw⟩
  obtain ⟨w,hw,hpw⟩ := mem_closure_iff_nhds.mp (dense_polynomial_nonzero hp z) _ hn
  exact hw.2 (mul_left_cancel₀ hpw (he w hw.1))

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial
noncomputable section

def UniformlyRegularOn (U : Set BaseCoordinates) (f : BaseCoordinates → ℂ) : Prop :=
  ∃ p q : BasePolynomial, (∀ z ∈ U, baseEval q z ≠ 0) ∧
    ∀ z ∈ U, f z=baseEval p z/baseEval q z

lemma UniformlyRegularOn.regular {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (h : UniformlyRegularOn U f) : AlgebraicallyRegularOn U f := by
  obtain ⟨p,q,hq,h⟩ := h
  exact fun z hz ↦ ⟨p,q,hq z hz,fun w hw _ ↦ h w hw⟩

lemma UniformlyRegularOn.congr {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (h : UniformlyRegularOn U f) (he : EqOn f g U) : UniformlyRegularOn U g := by
  obtain ⟨p,q,hq,h⟩ := h
  exact ⟨p,q,hq,fun z hz ↦ (he hz).symm.trans (h z hz)⟩

lemma UniformlyRegularOn.mono {U V : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (h : UniformlyRegularOn U f) (hVU : V ⊆ U) : UniformlyRegularOn V f := by
  obtain ⟨p,q,hq,h⟩ := h
  exact ⟨p,q,fun z hz ↦ hq z (hVU hz),fun z hz ↦ h z (hVU hz)⟩

lemma uniformlyRegular_polynomial (U : Set BaseCoordinates) (p : BasePolynomial) :
    UniformlyRegularOn U (baseEval p) := by
  exact ⟨p,1,fun _ _ ↦ by simp,fun _ _ ↦ by simp⟩
lemma uniformlyRegular_const (U : Set BaseCoordinates) (c : ℂ) :
    UniformlyRegularOn U (fun _ ↦ c) := by
  exact ⟨C c,1,fun _ _ ↦ by simp,fun _ _ ↦ by simp⟩

lemma UniformlyRegularOn.add {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (hg : UniformlyRegularOn U g) :
    UniformlyRegularOn U (fun z ↦ f z+g z) := by
  obtain ⟨p,q,hq,h⟩ := hf
  obtain ⟨r,s,hs,k⟩ := hg
  refine ⟨p*s+q*r,q*s, fun z hz ↦ by simpa using mul_ne_zero (hq z hz) (hs z hz),?_⟩
  intro z hz
  dsimp only
  rw [h z hz,k z hz]
  simp only [baseEval_add,baseEval_mul]
  exact div_add_div _ _ (hq z hz) (hs z hz)

lemma UniformlyRegularOn.neg {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) : UniformlyRegularOn U (fun z ↦ - f z) := by
  obtain ⟨p,q,hq,h⟩ := hf
  exact ⟨-p,q,hq,fun z hz ↦ by dsimp only; rw [h z hz,baseEval_neg,neg_div]⟩
lemma UniformlyRegularOn.sub {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (hg : UniformlyRegularOn U g) :
    UniformlyRegularOn U (fun z ↦ f z-g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma UniformlyRegularOn.mul {U : Set BaseCoordinates} {f g : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (hg : UniformlyRegularOn U g) :
    UniformlyRegularOn U (fun z ↦ f z*g z) := by
  obtain ⟨p,q,hq,h⟩ := hf
  obtain ⟨r,s,hs,k⟩ := hg
  refine ⟨p*r,q*s, fun z hz ↦ by simpa using mul_ne_zero (hq z hz) (hs z hz),?_⟩
  intro z hz
  dsimp only
  rw [h z hz,k z hz]
  simp only [baseEval_mul,mul_div_mul_comm]
lemma UniformlyRegularOn.inv {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (hn : ∀ z ∈ U, f z ≠ 0) :
    UniformlyRegularOn U (fun z ↦ (f z)⁻¹) := by
  obtain ⟨p,q,hq,h⟩ := hf
  refine ⟨q,p,?_,?_⟩
  · intro z hz he
    apply hn z hz
    rw [h z hz,he,zero_div]
  · intro z hz
    dsimp only
    rw [h z hz,inv_div]
lemma UniformlyRegularOn.pow {U : Set BaseCoordinates} {f : BaseCoordinates → ℂ}
    (hf : UniformlyRegularOn U f) (n : ℕ) : UniformlyRegularOn U (fun z ↦ f z^n) := by
  induction n with
  | zero => simpa using uniformlyRegular_const U 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma UniformlyRegularOn.eval {U : Set BaseCoordinates} {f : Fin 2 → BaseCoordinates → ℂ}
    (hf : ∀ i, UniformlyRegularOn U (f i)) (p : BasePolynomial) :
    UniformlyRegularOn U (fun z ↦ MvPolynomial.eval (fun i ↦ f i z) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using uniformlyRegular_const U c
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul,eval_X] using hp.mul (hf i)

lemma squarefree_dvd_of_baseEval_zero {d p : BasePolynomial} (hd : Squarefree d)
    (he : ∀ z, baseEval d z=0 → baseEval p z=0) : d ∣ p := by
  let J : Ideal BasePolynomial := Ideal.span {d}
  have hJ : J.IsRadical := isRadical_iff_span_singleton.mp hd.isRadical
  apply Ideal.mem_span_singleton.mp
  change p ∈ J
  rw [← hJ.radical,← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro z hz
  rw [MvPolynomial.zeroLocus_span] at hz
  have hh := hz _ (Set.mem_singleton _)
  have hz' : z=![z 0,z 1] := by ext i; fin_cases i <;> rfl
  rw [hz'] at hh ⊢
  simpa only [aeval_eq_eval,baseEval] using he (z 0,z 1) (by simpa [baseEval,aeval_eq_eval] using hh)

lemma exists_uniformlyRegular_division (r d : BasePolynomial) (hd : Squarefree d)
    (f : BaseCoordinates → ℂ) (hf : UniformlyRegularOn {z | baseEval r z ≠ 0} f)
    (he : ∀ z, baseEval r z ≠ 0 → baseEval d z=0 → f z=0) :
    ∃ k : BaseCoordinates → ℂ, UniformlyRegularOn {z | baseEval r z ≠ 0} k ∧
      ∀ z, baseEval r z ≠ 0 → baseEval d z*k z=f z := by
  obtain ⟨p,q,hq,h⟩ := hf
  have hdiv : d ∣ r*p := by
    apply squarefree_dvd_of_baseEval_zero hd
    intro z hz
    by_cases hr : baseEval r z=0
    · simp [hr]
    · have hv := he z hr hz
      rw [h z hr] at hv
      have hp : baseEval p z=0 := (div_eq_zero_iff).mp hv |>.resolve_right (hq z hr)
      simp [hp]
  obtain ⟨a,ha⟩ := hdiv
  refine ⟨fun z ↦ baseEval a z/baseEval (r*q) z,⟨a,r*q,?_,fun _ _ ↦ rfl⟩,?_⟩
  · intro z hz
    simpa using mul_ne_zero hz (hq z hz)
  · intro z hz
    have hqa := hq z hz
    have heq := congrArg (fun p ↦ baseEval p z) ha
    simp only [baseEval_mul] at heq
    dsimp only
    rw [baseEval_mul,h z hz]
    field_simp
    linear_combination -heq

end
end QuadricCounterexample

end OAI
