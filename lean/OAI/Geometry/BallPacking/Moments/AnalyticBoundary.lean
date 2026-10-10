import Mathlib
import OAI.Geometry.BallPacking.Moser.PlanarCorrection
import OAI.Geometry.BallPacking.Moments.RadialSwap

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

theorem centered_contDiff_analytic (k : ι → ℕ × ℕ) :
    ContDiff ℝ ω (fun q : ((ι → ℝ) × Plane) × Plane => centered k q.1.1 q.1.2 q.2) := by
  apply ContDiff.prodMk <;> apply ContDiff.sum <;> intro i _ <;> dsimp [monomial] <;> fun_prop

theorem exists_analytic_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (0,t))=(0,t) ∧
      ContDiffAt ℝ ω f (a,moment k a (0,t)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (0,t)),centered k q.1 q.2 (f q)=0 := by
  let q := (a,moment k a (0,t))
  let r : Plane := (0,t)
  let F : ((ι → ℝ) × Plane) × Plane → Plane := fun s => centered k s.1.1 s.1.2 s.2
  have hF : ContDiff ℝ ω F := centered_contDiff_analytic k
  have hpartial : (fderiv ℝ F (q,r)).comp (ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane)=
      centeredDerivative k a (moment k a (0,t)) r := by
    have hc := ((hF.differentiable (by simp) (q,r)).hasFDerivAt.comp r
      ((hasFDerivAt_const q r).prodMk (hasFDerivAt_id r)))
    exact hc.unique (centered_hasFDerivAt k a (moment k a (0,t)) r)
  have hinv : (fderiv ℝ F (q,r) ∘L ContinuousLinearMap.inr ℝ ((ι → ℝ) × Plane) Plane).IsInvertible := by
    rw [hpartial]
    exact centeredDerivative_axis_isInvertible ha hzero he0 he1 ht
  have hz : F (q,r)=0 := centered_moment (polynomial_pos (r := (0,t)) ha hzero ⟨le_rfl,ht⟩).ne'
  refine ⟨hF.contDiffAt.implicitFunction (by simp) hinv,?_,
    hF.contDiffAt.contDiffAt_implicitFunction (by simp) hinv,?_⟩
  · exact hF.contDiffAt.implicitFunction_apply_self (by simp) hinv
  · simpa only [hz] using hF.contDiffAt.eventually_apply_implicitFunction (by simp) hinv

theorem exists_analytic_other_axis_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {t : ℝ} (ht : 0≤t) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a (t,0))=(t,0) ∧
      ContDiffAt ℝ ω f (a,moment k a (t,0)) ∧
      ∀ᶠ q in 𝓝 (a,moment k a (t,0)),centered k q.1 q.2 (f q)=0 := by
  have hzero' : ∃ i,(k i).swap=(0,0) := by
    obtain ⟨i,hi⟩ := hzero
    exact ⟨i,by simp [hi]⟩
  have he0' : ∃ i,(k i).swap=(1,0) := by
    obtain ⟨i,hi⟩ := he1
    exact ⟨i,by simp [hi]⟩
  have he1' : ∃ i,(k i).swap=(0,1) := by
    obtain ⟨i,hi⟩ := he0
    exact ⟨i,by simp [hi]⟩
  obtain ⟨f,hf,hfs,hfe⟩ := exists_analytic_axis_radial_solution ha hzero' he0' he1' ht
  have hm : moment (fun i => (k i).swap) a (0,t)=(moment k a (t,0)).swap :=
    moment_swap k a (t,0)
  rw [hm] at hf hfs hfe
  let F : (ι → ℝ) × Plane → Plane := fun q => (f (q.1,q.2.swap)).swap
  have hswap : ContDiff ℝ ω (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap)) := by
    change ContDiff ℝ ω (fun q : (ι → ℝ) × Plane => (q.1,(q.2.2,q.2.1)))
    fun_prop
  refine ⟨F,?_,?_,?_⟩
  · dsimp [F]
    rw [hf]
    rfl
  · have hc : ContDiffAt ℝ ω (fun q : (ι → ℝ) × Plane => f (q.1,q.2.swap))
        (a,moment k a (t,0)) := hfs.comp (a,moment k a (t,0)) hswap.contDiffAt
    exact hc.snd.prodMk hc.fst
  · have htend : Tendsto (fun q : (ι → ℝ) × Plane => (q.1,q.2.swap))
        (𝓝 (a,moment k a (t,0))) (𝓝 (a,(moment k a (t,0)).swap)) :=
      hswap.continuous.continuousAt
    have he := htend.eventually hfe
    filter_upwards [he] with q hq
    have h := congrArg Prod.swap hq
    have hr : centered k q.1 q.2 (F q)=
        (centered (fun i => (k i).swap) q.1 q.2.swap (f (q.1,q.2.swap))).swap := by
      have hh := centered_swap k q.1 q.2 (F q)
      simp only [F,Prod.swap_swap] at hh
      exact (congrArg Prod.swap hh).symm
    rw [hr,h]
    rfl

theorem exists_analytic_boundary_radial_solution {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0≤r.1 ∧ 0≤r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ω f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),centered k q.1 q.2 (f q)=0 := by
  rcases r with ⟨s,t⟩
  rcases hb with hs|ht
  · change s=0 at hs
    subst s
    exact exists_analytic_axis_radial_solution ha hzero he0 he1 hr.2
  · change t=0 at ht
    subst t
    exact exists_analytic_other_axis_radial_solution ha hzero he0 he1 hr.1

theorem exists_analytic_boundary_moment_inverse {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (hzero : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {r : Plane}
    (hr : 0≤r.1 ∧ 0≤r.2) (hb : r.1=0 ∨ r.2=0) :
    ∃ f : ((ι → ℝ) × Plane) → Plane,
      f (a,moment k a r)=r ∧ ContDiffAt ℝ ω f (a,moment k a r) ∧
      ∀ᶠ q in 𝓝 (a,moment k a r),
        moment k q.1 (f q)=q.2 ∧
        (0≤(f q).1 ↔ 0≤q.2.1) ∧ (0≤(f q).2 ↔ 0≤q.2.2) ∧
        (0<(f q).1 ↔ 0<q.2.1) ∧ (0<(f q).2 ↔ 0<q.2.2) := by
  obtain ⟨f,hf,hfs,hfe⟩ := exists_analytic_boundary_radial_solution ha hzero he0 he1 hr hb
  let q0 := (a,moment k a r)
  have hc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => (q.1,f q)) q0 :=
    contDiffAt_fst.prodMk (hfs.of_le (by simp))
  have hP := polynomial_pos ha hzero hr
  have hPc : ContinuousAt (fun q : (ι → ℝ) × Plane => polynomial k q.1 (f q)) q0 :=
    (polynomial_contDiff k).continuous.continuousAt.comp hc.continuousAt
  have hPe : ∀ᶠ q in 𝓝 q0,0<polynomial k q.1 (f q) := by
    apply hPc.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hP)
  have hsc : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => slope k q.1 (f q)) q0 := by
    have hs := slope_contDiffAt hP.ne'
    have hh : (a,r)=(q0.1,f q0) := by simp [q0,hf]
    rw [hh] at hs
    exact hs.comp q0 hc
  have hs := slope_pos ha hzero he0 he1 hr
  have hse0 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).1 := by
    apply hsc.continuousAt.fst.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.1)
  have hse1 : ∀ᶠ q in 𝓝 q0,0<(slope k q.1 (f q)).2 := by
    apply hsc.continuousAt.snd.tendsto.eventually
    exact eventually_gt_nhds (by simpa only [q0,hf] using hs.2)
  refine ⟨f,hf,hfs,?_⟩
  filter_upwards [hfe,hPe,hse0,hse1] with q hq hPq hs0 hs1
  have hm := moment_eq_of_centered hPq.ne' hq
  refine ⟨hm,?_,?_,?_,?_⟩
  all_goals
    have he := moment_eq_radius_slope k q.1 (f q)
    rw [hm] at he
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_nonneg_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_nonneg_iff_of_pos_right hs1).symm
  · rw [show q.2.1=(f q).1*(slope k q.1 (f q)).1 from congrArg Prod.fst he]
    exact (mul_pos_iff_of_pos_right hs0).symm
  · rw [show q.2.2=(f q).2*(slope k q.1 (f q)).2 from congrArg Prod.snd he]
    exact (mul_pos_iff_of_pos_right hs1).symm

theorem trapezoid_inverse_open_representative {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∃ U : Set ((TrapezoidWeight A B → ℝ) × Plane), ∃ f : ((TrapezoidWeight A B → ℝ) × Plane) → Plane,
      IsOpen U ∧ (a,p)∈U ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ q∈U,(∀ i,0<q.1 i) → q.2∈lowerTrapezoid A B →
        f q=nonnegativeInverse latticeIndex q.1 q.2 := by
  by_cases hb : p.1=0 ∨ p.2=0
  · let r := nonnegativeInverse (latticeIndex (A:=A) (B:=B)) a p
    have hr := nonnegativeInverse_nonneg (latticeIndex (A:=A) (B:=B)) a p
    have he : moment latticeIndex a r=p := trapezoid_inverse_spec hAB ha hp
    have hz := moment_zero_coordinates ha (lattice_zero A B) (lattice_unit_fst hA hAB)
      (lattice_unit_snd hA hAB) hr
    have hbr : r.1=0 ∨ r.2=0 := by
      rw [he] at hz
      exact hb.elim (fun h => Or.inl (hz.1.mp h)) (fun h => Or.inr (hz.2.mp h))
    obtain ⟨f,hf,hfs,hfe⟩ := exists_analytic_boundary_moment_inverse ha (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr hbr
    rw [he] at hf hfs hfe
    obtain ⟨V,hV,hfV⟩ := hfs.contDiffOn (m := ∞) (by simp) (fun _ => rfl)
    obtain ⟨U,hUV,hU,hpU⟩ := mem_nhds_iff.mp (inter_mem hV hfe)
    refine ⟨U,f,hU,hpU,hfV.mono (fun q hq => (hUV hq).1),?_⟩
    intro q hq hqa hqp
    have hqf := (hUV hq).2
    exact (nonnegativeInverse_eq_of_moment hqa (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
      ⟨hqf.2.1.mpr hqp.1,hqf.2.2.1.mpr hqp.2.2.1⟩ hqf.1).symm
  · let U : Set ((TrapezoidWeight A B → ℝ) × Plane) :=
      {q | (∀ i,0<q.1 i) ∧ 0<q.2.1 ∧ q.2.1<A ∧ 0<q.2.2 ∧ q.2.1+q.2.2<B}
    have hU : IsOpen U := (positiveCoefficients_isOpen.preimage continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd.fst).inter
        ((isOpen_lt continuous_snd.fst continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd.snd).inter
            (isOpen_lt (continuous_snd.fst.add continuous_snd.snd) continuous_const))))
    have hp0 : 0<p.1 := lt_of_le_of_ne hp.1 (Ne.symm (fun h => hb (Or.inl h)))
    have hp1 : 0<p.2 := lt_of_le_of_ne hp.2.2.1 (Ne.symm (fun h => hb (Or.inr h)))
    refine ⟨U,fun q => nonnegativeInverse latticeIndex q.1 q.2,hU,⟨ha,hp0,hp.2.1,hp1,hp.2.2.2⟩,?_,?_⟩
    · intro q hq
      exact (nonnegativeInverse_interior_contDiffAt hq.1 (lattice_zero A B)
        (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
        (trapezoidWeight_surrounds hAB hq.2)).contDiffWithinAt
    · intros
      rfl

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 def gibbs (w : ι → E) (a : ι → ℝ) (x : E) (i : ι) : ℝ :=
  a i*Real.exp (inner ℝ (w i) x)/partition w a x

 theorem gibbs_pos {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) (i : ι) :
    0<gibbs w a x i := div_pos (mul_pos (ha i) (Real.exp_pos _)) (partition_pos ha x)

 theorem sum_gibbs {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) :
    ∑ i,gibbs w a x i=1 := by
  simp only [gibbs,←Finset.sum_div]
  change partition w a x / partition w a x = 1
  exact div_self (partition_pos ha x).ne'

 omit [Nonempty ι] in
 theorem gibbs_mean {w : ι → E} {a : ι → ℝ} (x : E) :
    ∑ i,gibbs w a x i • w i=moment w a x := by
  simp only [gibbs,moment,gradient,Finset.smul_sum,smul_smul,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

 theorem gibbs_log {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (x : E) (i : ι) :
    Real.log (gibbs w a x i)=Real.log (a i)+inner ℝ (w i) x-Real.log (partition w a x) := by
  rw [gibbs,Real.log_div (mul_pos (ha i) (Real.exp_pos _)).ne' (partition_pos ha x).ne',
    Real.log_mul (ha i).ne' (Real.exp_ne_zero _),Real.log_exp]

 theorem scalar_relative_log {h q : ℝ} (hh : 0≤h) (hq : 0<q) :
    h*(Real.log q-Real.log h)≤q-h := by
  by_cases hz : h=0
  · simp [hz,hq.le]
  have hp : 0<h := lt_of_le_of_ne hh (Ne.symm hz)
  have he := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at he
  have hm := mul_le_mul_of_nonneg_left he hh
  have hcalc : h*(q/h-1)=q-h := by field_simp
  rwa [hcalc] at hm

 omit [Nonempty ι] in
 theorem relative_log_sum_le {h q : ι → ℝ} (hh : ∀ i,0≤h i) (hq : ∀ i,0<q i)
    (hhs : ∑ i,h i=1) (hqs : ∑ i,q i=1) :
    ∑ i,h i*(Real.log (q i)-Real.log (h i))≤0 := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => scalar_relative_log (hh i) (hq i))
  simpa only [Finset.sum_sub_distrib,hhs,hqs,sub_self] using hb

 omit [Nonempty ι] in
 theorem probability_log_sum_nonpos {h : ι → ℝ} (hh : ∀ i,0≤h i) (hs : ∑ i,h i=1) :
    ∑ i,h i*Real.log (h i)≤0 := by
  classical
  apply Finset.sum_nonpos
  intro i _
  have hi : h i≤1 := by
    rw [←hs]
    exact Finset.single_le_sum (fun j _ => hh j) (Finset.mem_univ i)
  by_cases hz : h i=0
  · simp [hz]
  · exact mul_nonpos_of_nonneg_of_nonpos (hh i)
      (Real.log_nonpos (lt_of_le_of_ne (hh i) (Ne.symm hz)).le hi)

 omit [Nonempty ι] in
 theorem probability_log_sum_lower {q : ι → ℝ} (hq : ∀ i,0<q i) (hs : ∑ i,q i=1) :
    -(Fintype.card ι : ℝ)≤∑ i,q i*Real.log (q i) := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => scalar_relative_log (hq i).le (q := 1) zero_lt_one)
  simp only [Real.log_one,zero_sub,mul_neg,Finset.sum_neg_distrib,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hs] at hb
  linarith

end
section

variable {ι : Type*} [Fintype ι]

 theorem probability_weighted_le {q f : ι → ℝ} {M : ℝ}
    (hq : ∀ i,0≤q i) (hs : ∑ i,q i=1) (hf : ∀ i,f i≤M) :
    ∑ i,q i*f i≤M := by
  calc
    _≤∑ i,q i*M := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hq i))
    _=M := by rw [←Finset.sum_mul,hs,one_mul]

 theorem probability_weighted_ge {q f : ι → ℝ} {M : ℝ}
    (hq : ∀ i,0≤q i) (hs : ∑ i,q i=1) (hf : ∀ i,M≤f i) :
    M≤∑ i,q i*f i := by
  calc
    M=∑ i,q i*M := by rw [←Finset.sum_mul,hs,one_mul]
    _≤_ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hq i))

 theorem finite_log_height_bound {q h a b m : ι → ℝ} {l C M : ℝ}
    (hq : ∀ i,0<q i) (hqs : ∑ i,q i=1)
    (hh : ∀ i,0≤h i) (hhs : ∑ i,h i=1)
    (hlog : ∀ i,Real.log (q i)=Real.log (a i)+b i+l*m i-C)
    (hmean : ∑ i,q i*b i=∑ i,h i*b i)
    (ha : ∀ i,|Real.log (a i)|≤M) :
    (-l)*((∑ i,q i*m i)-(∑ i,h i*m i))≤2*M+Fintype.card ι := by
  have hrelative := relative_log_sum_le hh hq hhs hqs
  simp only [mul_sub,Finset.sum_sub_distrib] at hrelative
  have hentq := probability_log_sum_lower hq hqs
  have henth := probability_log_sum_nonpos hh hhs
  have hqlog : ∑ i,q i*Real.log (a i)≤M :=
    probability_weighted_le (fun i => (hq i).le) hqs (fun i => (abs_le.mp (ha i)).2)
  have hhlog : -M≤∑ i,h i*Real.log (a i) :=
    probability_weighted_ge hh hhs (fun i => (abs_le.mp (ha i)).1)
  have expand (t : ι → ℝ) (ht : ∑ i,t i=1) :
      ∑ i,t i*Real.log (q i)=(∑ i,t i*Real.log (a i))+(∑ i,t i*b i)+
        l*(∑ i,t i*m i)-C := by
    simp only [hlog,mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [←Finset.sum_mul,ht,one_mul,Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [expand h hhs] at hrelative
  rw [expand q hqs,hmean] at hentq
  nlinarith

 variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nonempty ι]

 theorem gibbs_tilt_log {w : ι → E} {a m : ι → ℝ} (ha : ∀ i,0<a i)
    (l : ℝ) (x : E) (i : ι) :
    Real.log (gibbs w (fun j => a j*Real.exp (l*m j)) x i)=
      Real.log (a i)+inner ℝ (w i) x+l*m i-
        Real.log (partition w (fun j => a j*Real.exp (l*m j)) x) := by
  rw [gibbs_log (fun j => mul_pos (ha j) (Real.exp_pos _)),
    Real.log_mul (ha i).ne' (Real.exp_ne_zero _),Real.log_exp]
  ring

 theorem gibbs_tilt_height_bound {w : ι → E} {a m h : ι → ℝ} {M : ℝ}
    (ha : ∀ i,0<a i) (hloga : ∀ i,|Real.log (a i)|≤M)
    (hh : ∀ i,0≤h i) (hhs : ∑ i,h i=1) (l : ℝ) (x : E)
    (hmean : ∑ i,h i • w i=moment w (fun j => a j*Real.exp (l*m j)) x) :
    (-l)*((∑ i,gibbs w (fun j => a j*Real.exp (l*m j)) x i*m i)-(∑ i,h i*m i))
      ≤2*M+Fintype.card ι := by
  have hpos (i : ι) : 0<a i*Real.exp (l*m i) := mul_pos (ha i) (Real.exp_pos _)
  apply finite_log_height_bound (gibbs_pos hpos x) (sum_gibbs hpos x) hh hhs
    (gibbs_tilt_log ha l x) _ hloga
  have he := congrArg (fun p : E => inner ℝ p x) ((gibbs_mean (w := w)
    (a := fun j => a j*Real.exp (l*m j)) x).trans hmean.symm)
  simpa only [sum_inner,real_inner_smul_left] using he

end
section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 omit [Nonempty ι] in
 theorem partition_scale_translate (w : ι → E) (a : ι → ℝ) (C : ℝ) (x z : E) :
    partition w (fun i => C*a i*Real.exp (inner ℝ (w i) z)) x=
      C*partition w a (x+z) := by
  simp only [partition,inner_add_right,Real.exp_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

 omit [Nonempty ι] in
 theorem gibbs_scale_translate (w : ι → E) (a : ι → ℝ) {C : ℝ} (hC : C≠0)
    (x z : E) (i : ι) :
    gibbs w (fun j => C*a j*Real.exp (inner ℝ (w j) z)) x i=gibbs w a (x+z) i := by
  unfold gibbs
  rw [partition_scale_translate]
  simp only [inner_add_right,Real.exp_add]
  have hn : C*a i*Real.exp (inner ℝ (w i) z)*Real.exp (inner ℝ (w i) x)=
      C*(a i*(Real.exp (inner ℝ (w i) x)*Real.exp (inner ℝ (w i) z))) := by ring
  rw [hn,mul_div_mul_left _ _ hC]

 omit [Nonempty ι] in
 theorem moment_scale_translate (w : ι → E) (a : ι → ℝ) {C : ℝ} (hC : C≠0)
    (x z : E) : moment w (fun j => C*a j*Real.exp (inner ℝ (w j) z)) x=
      moment w a (x+z) := by
  rw [←gibbs_mean,←gibbs_mean]
  simp only [gibbs_scale_translate w a hC]

 omit [Nonempty ι] in
 theorem probability_nonneg_bound {q : ι → ℝ} (hq : ∀ i,0≤q i) (hs : ∑ i,q i=1)
    (i : ι) : q i≤1 := by
  classical
  rw [←hs]
  exact Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i)

end

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 def selected (w : ι → E) (a : ι → ℝ) (p : E) (i : ι) : ℝ :=
  gibbs w a (inverse w a p) i

 omit [FiniteDimensional ℝ E] in
 theorem selected_pos {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (p : E) (i : ι) :
    0<selected w a p i := gibbs_pos ha _ _

 omit [FiniteDimensional ℝ E] in
 theorem selected_sum {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) (p : E) :
    ∑ i,selected w a p i=1 := sum_gibbs ha _

 theorem selected_mean {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) : ∑ i,selected w a p i • w i=p :=
  (gibbs_mean _).trans (inverse_spec ha hp)

 theorem selected_contDiffAt {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i) {p : E}
    (hp : Surrounds w p) (i : ι) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × E => selected w q.1 q.2 i) (a,p) := by
  have hx := inverse_contDiffAt ha hp
  have hnum (j : ι) : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × E =>
      q.1 j*Real.exp (inner ℝ (w j) (inverse w q.1 q.2))) (a,p) :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × E => q.1 j) (a,p)).mul
      ((contDiffAt_const.inner ℝ hx).exp)
  exact (hnum i).div (ContDiffAt.sum (fun j _ => hnum j)) (partition_pos ha _).ne'

 theorem selected_gauge {w : ι → E} {a : ι → ℝ} (ha : ∀ i,0<a i)
    {C : ℝ} (hC : 0<C) {p : E} (hp : Surrounds w p) (z : E) (i : ι) :
    selected w (fun j => C*a j*Real.exp (inner ℝ (w j) z)) p i=selected w a p i := by
  have hb (j : ι) : 0<C*a j*Real.exp (inner ℝ (w j) z) :=
    mul_pos (mul_pos hC (ha j)) (Real.exp_pos _)
  have hm : moment w a (inverse w (fun j => C*a j*Real.exp (inner ℝ (w j) z)) p+z)=p := by
    rw [←moment_scale_translate w a hC.ne']
    exact inverse_spec hb hp
  unfold selected
  rw [gibbs_scale_translate w a hC.ne',inverse_unique ha hp hm]

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function
section

variable {ι : Type*} [Fintype ι]

def probability (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) (i : ι) : ℝ :=
  a i*monomial (k i) r/polynomial k a r

def selected (k : ι → ℕ × ℕ) (a : ι → ℝ) (p : Plane) (i : ι) : ℝ :=
  probability k a (nonnegativeInverse k a p) i

theorem probability_nonneg {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) {r : Plane} (hr : 0≤r.1 ∧ 0≤r.2) (i : ι) :
    0≤probability k a r i := div_nonneg (mul_nonneg (ha i).le (monomial_nonneg _ hr))
      (polynomial_pos ha h0 hr).le

theorem probability_sum {k : ι → ℕ × ℕ} {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) : ∑ i,probability k a r i=1 := by
  simp only [probability,← Finset.sum_div]
  exact div_self hP

theorem probability_mean (k : ι → ℕ × ℕ) (a : ι → ℝ) (r : Plane) :
    (∑ i,probability k a r i*((k i).1:ℝ),∑ i,probability k a r i*((k i).2:ℝ))=moment k a r := by
  apply Prod.ext
  · change (∑ i,probability k a r i*((k i).1:ℝ))=
      (polynomial k a r)⁻¹*(∑ i,((k i).1:ℝ)*a i*monomial (k i) r)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [probability]
    ring
  · change (∑ i,probability k a r i*((k i).2:ℝ))=
      (polynomial k a r)⁻¹*(∑ i,((k i).2:ℝ)*a i*monomial (k i) r)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [probability]
    ring

theorem probability_contDiffAt (k : ι → ℕ × ℕ) {a : ι → ℝ} {r : Plane}
    (hP : polynomial k a r≠0) (i : ι) :
    ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × Plane => probability k q.1 q.2 i) (a,r) := by
  apply ContDiffAt.div _ (polynomial_contDiff k).contDiffAt hP
  dsimp [monomial]
  fun_prop

theorem probability_expRadius (k : ι → ℕ × ℕ) (a : ι → ℝ) (x : MomentPlane) (i : ι) :
    probability k a (expRadius x) i=gibbs (weight k) a x i := by
  simp only [probability,monomial_expRadius,polynomial_expRadius,gibbs,weight]

theorem selected_nonneg {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) (p : Plane) (i : ι) : 0 ≤ selected k a p i :=
  probability_nonneg ha h0 (nonnegativeInverse_nonneg _ _ _) i

theorem selected_sum {k : ι → ℕ × ℕ} {a : ι → ℝ} (ha : ∀ i,0<a i)
    (h0 : ∃ i,k i=(0,0)) (p : Plane) : ∑ i,selected k a p i=1 :=
  probability_sum (polynomial_pos ha h0 (nonnegativeInverse_nonneg _ _ _)).ne'

theorem selected_eq_exponential [Nonempty ι] {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {p : Plane}
    (hp : Surrounds (weight k) (planeVector p.1 p.2)) (i : ι) :
    selected k a p i=FiniteMoment.selected (weight k) a (planeVector p.1 p.2) i := by
  unfold selected
  rw [nonnegativeInverse_exp ha h0 he0 he1 hp,probability_expRadius]
  rfl

end

theorem trapezoid_selected_contDiffWithinAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) (i : TrapezoidWeight A B) :
    ContDiffWithinAt ℝ ∞
      (fun q : (TrapezoidWeight A B → ℝ) × Plane => selected latticeIndex q.1 q.2 i)
      {q | (∀ j,0<q.1 j) ∧ q.2∈lowerTrapezoid A B} (a,p) := by
  have hi := trapezoid_inverse_contDiffWithinAt hA hAB ha hp
  have hs := probability_contDiffAt latticeIndex
    (polynomial_pos ha (lattice_zero A B) (nonnegativeInverse_nonneg latticeIndex a p)).ne' i
  have hmap := contDiffWithinAt_fst.prodMk hi
  have hc := hs.comp_contDiffWithinAt (a,p) hmap
  exact hc

theorem trapezoid_selected_coeff_contDiffAt {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) (i : TrapezoidWeight A B) :
    ContDiffAt ℝ ∞ (fun b : TrapezoidWeight A B → ℝ => selected latticeIndex b p i) a := by
  have hi := trapezoid_inverse_coeff_contDiffAt hA hAB ha hp
  have hs := probability_contDiffAt latticeIndex
    (polynomial_pos ha (lattice_zero A B) (nonnegativeInverse_nonneg latticeIndex a p)).ne' i
  have hmap := contDiffAt_id.prodMk hi
  have hc := hs.comp a hmap
  exact hc

theorem trapezoid_selected_mean {A B : ℕ} (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∑ i,selected latticeIndex a p i • trapezoidWeight A B i=planeVector p.1 p.2 := by
  have he := (probability_mean latticeIndex a (nonnegativeInverse latticeIndex a p)).trans
    (trapezoid_inverse_spec hAB ha hp)
  ext j
  fin_cases j
  · simpa [trapezoidWeight,planeVector,latticeIndex,selected] using congrArg Prod.fst he
  · simpa [trapezoidWeight,planeVector,latticeIndex,selected] using congrArg Prod.snd he

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_smooth_extension {K S : Set E} (hK : IsCompact K) (g : E → F)
    (hlocal : ∀ x∈K, ∃ U : Set E, ∃ f : E → F,
      IsOpen U ∧ x∈U ∧ ContDiffOn ℝ ∞ f U ∧ ∀ y∈U,y∈S → f y=g y) :
    ∃ f : E → F, ContDiff ℝ ∞ f ∧ ∀ᶠ y in 𝓝ˢ K,y∈S → f y=g y := by
  classical
  choose U f hU hmem hf he using (fun x : K => hlocal x.val x.property)
  have hKU : K⊆⋃ x : K,U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK (isOpen_iUnion hU) hKU
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,E) hL.isClosed U hU hLU
  refine ⟨fun y => ∑ᶠ i,ρ i y • f i y,
    (hρ.contMDiff_finsum_smul hU (fun i => (hf i).contMDiffOn)).contDiff,?_⟩
  filter_upwards [isOpen_interior.mem_nhdsSet.mpr hKL] with y hy hyS
  have ht : (fun i : K => ρ i y • f i y)=(fun i : K => ρ i y • g y) := by
    funext i
    by_cases hi : ρ i y=0
    · simp [hi]
    · rw [he i y (hρ i (subset_closure hi)) hyS]
  rw [ht,← finsum_smul,ρ.sum_eq_one (interior_subset hy),one_smul]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

theorem trapezoid_selected_open_representative {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {a : TrapezoidWeight A B → ℝ} (ha : ∀ i,0<a i) {p : Plane}
    (hp : p∈lowerTrapezoid A B) :
    ∃ U : Set ((TrapezoidWeight A B → ℝ) × Plane),
      ∃ f : ((TrapezoidWeight A B → ℝ) × Plane) → (TrapezoidWeight A B → ℝ),
      IsOpen U ∧ (a,p)∈U ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ q∈U,(∀ i,0<q.1 i) → q.2∈lowerTrapezoid A B →
        f q=selected latticeIndex q.1 q.2 := by
  obtain ⟨U,f,hU,hqU,hf,he⟩ := trapezoid_inverse_open_representative hA hAB ha hp
  have hs : ContDiffAt ℝ ∞ (fun q => (q.1,f q)) (a,p) :=
    contDiffAt_fst.prodMk ((hf (a,p) hqU).contDiffAt (hU.mem_nhds hqU))
  have hP : 0<polynomial latticeIndex a (f (a,p)) := by
    rw [he (a,p) hqU ha hp]
    exact polynomial_pos ha (lattice_zero A B) (nonnegativeInverse_nonneg _ _ _)
  have hPe : ∀ᶠ q in 𝓝 (a,p),0<polynomial latticeIndex q.1 (f q) :=
    ((polynomial_contDiff latticeIndex).continuous.continuousAt.comp hs.continuousAt).eventually
      (eventually_gt_nhds hP)
  obtain ⟨V,hVU,hV,hqV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hqU) hPe)
  refine ⟨V,fun q => probability latticeIndex q.1 (f q),hV,hqV,?_,?_⟩
  · rw [contDiffOn_pi]
    intro i q hq
    exact ((probability_contDiffAt latticeIndex ((hVU hq).2.ne') i).comp_contDiffWithinAt q
      (contDiffWithinAt_fst.prodMk ((hf q (hVU hq).1).mono (fun z hz => (hVU hz).1))))
  · intro q hq hqa hqp
    dsimp only
    rw [he q (hVU hq).1 hqa hqp]
    rfl

theorem trapezoid_selected_compact_extension {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {K : Set ((TrapezoidWeight A B → ℝ) × Plane)} (hK : IsCompact K)
    (hKS : ∀ q∈K,(∀ i,0<q.1 i) ∧ q.2∈lowerTrapezoid A B) :
    ∃ f : ((TrapezoidWeight A B → ℝ) × Plane) → (TrapezoidWeight A B → ℝ),
      ContDiff ℝ ∞ f ∧ ∃ U : Set ((TrapezoidWeight A B → ℝ) × Plane),
        IsOpen U ∧ K⊆U ∧ ∀ q∈U,(∀ i,0<q.1 i) → q.2∈lowerTrapezoid A B →
          f q=selected latticeIndex q.1 q.2 := by
  obtain ⟨f,hf,he⟩ := Hamiltonian.compact_local_smooth_extension
    (S := {q | (∀ i,0<q.1 i) ∧ q.2∈lowerTrapezoid A B}) hK
    (fun q => selected latticeIndex q.1 q.2) (by
      intro q hq
      obtain ⟨U,f,hU,hqU,hf,he⟩ := trapezoid_selected_open_representative hA hAB (hKS q hq).1 (hKS q hq).2
      exact ⟨U,f,hU,hqU,hf,fun y hy hys => he y hy hys.1 hys.2⟩)
  obtain ⟨U,hU,hKU,hUS⟩ := mem_nhdsSet_iff_exists.mp he
  exact ⟨f,hf,U,hU,hKU,fun q hq hqa hqp => hUS hq ⟨hqa,hqp⟩⟩

end PackingSufficiencySupport.FiniteMoment.Radial
end

end OAI
