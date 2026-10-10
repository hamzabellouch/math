import Mathlib
import OAI.Probability.SLE.FiniteRadiusStop

namespace OAI

/-! Swallow Lyapunov for chordal SLE. -/

section
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def radialLogPower (κ β : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  Real.exp ((β/2)*Real.log (greenLogNormSq κ q x))
noncomputable def heightLogPower (β : ℝ) (q : ℂ × ℝ) : ℝ := Real.exp (β*q.1.im)
noncomputable def swallowLyapunov (κ β C : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  radialLogPower κ β q x + C*heightLogPower β q

lemma radialLogPower_contDiff (κ β : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => radialLogPower κ β zz.1 zz.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => zz.1.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst.fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => zz.1.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst.fst
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => greenLogNormSq κ zz.1 zz.2) :=
    ((hre.sub (contDiff_const.mul contDiff_snd)).pow 2).add ((contDiff_const.mul him).exp)
  exact (contDiff_const.mul (hN.log (fun zz => (greenLogNormSq_pos κ zz.1 zz.2).ne'))).exp

lemma heightLogPower_contDiff (β : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => heightLogPower β zz.1) :=
  (contDiff_const.mul (Complex.imCLM.contDiff.comp contDiff_fst.fst)).exp

lemma swallowLyapunov_contDiff (κ β C : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => swallowLyapunov κ β C zz.1 zz.2) :=
  (radialLogPower_contDiff κ β).add (contDiff_const.mul (heightLogPower_contDiff β))

lemma radialLogPower_directional (κ β : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q v =
      radialLogPower κ β q x * β *
        ((q.1.re-Real.sqrt κ*x)*v.1.re + Real.exp (2*q.1.im)*v.1.im) /
          greenLogNormSq κ q x := by
  have hzre : HasDerivAt (fun t : ℝ => (q+t • v).1.re) v.1.re 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_re, Complex.smul_re, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.re).const_add q.1.re
  have hzim : HasDerivAt (fun t : ℝ => (q+t • v).1.im) v.1.im 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_im, Complex.smul_im, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.im).const_add q.1.im
  have hN : HasDerivAt (fun t : ℝ => greenLogNormSq κ (q+t • v) x)
      (2*(q.1.re-Real.sqrt κ*x)*v.1.re + 2*Real.exp (2*q.1.im)*v.1.im) 0 := by
    convert ((hzre.sub_const (Real.sqrt κ*x)).pow 2).add ((hzim.const_mul 2).exp) using 1 <;> try rfl
    simp only [zero_smul, add_zero, Nat.cast_ofNat]
    ring
  have hcalc := ((hN.log (by simpa only [zero_smul, add_zero] using
    (greenLogNormSq_pos κ q x).ne')).const_mul (β/2)).exp
  have hline : HasDerivAt (fun t : ℝ => radialLogPower κ β (q+t • v) x)
      (radialLogPower κ β q x * β *
        ((q.1.re-Real.sqrt κ*x)*v.1.re+Real.exp (2*q.1.im)*v.1.im)/greenLogNormSq κ q x) 0 := by
    convert hcalc using 1 <;> try rfl
    simp only [zero_smul, add_zero]
    dsimp only [radialLogPower]
    ring
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => radialLogPower κ β r x) :=
    (radialLogPower_contDiff κ β).comp (contDiff_id.prodMk contDiff_const)
  have haff : HasDerivAt (fun t : ℝ => q+t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (fun r : ℂ × ℝ => radialLogPower κ β r x)
      (fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q) (q+(0 : ℝ) • v) := by
    simpa using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hchain := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hchain.unique hline

lemma radialLogPower_spatial_deriv (κ β : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    HasDerivAt (radialLogPower κ β q)
      (-radialLogPower κ β q x*β*Real.sqrt κ*(q.1.re-Real.sqrt κ*x)/greenLogNormSq κ q x) x := by
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2*(q.1.re-Real.sqrt κ*x)*(-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2*q.1.im)) using 1 <;> try rfl
    simp
  convert ((hN.log (greenLogNormSq_pos κ q x).ne').const_mul (β/2)).exp using 1 <;> try rfl
  dsimp only [radialLogPower]
  ring

lemma radialLogPower_spatial_second (κ β : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    iteratedDeriv 2 (radialLogPower κ β q) x =
      radialLogPower κ β q x*κ*β*
        ((β-1)*(q.1.re-Real.sqrt κ*x)^2+Real.exp (2*q.1.im))/(greenLogNormSq κ q x)^2 := by
  have hd : deriv (radialLogPower κ β q) = fun x =>
      -radialLogPower κ β q x*β*Real.sqrt κ*(q.1.re-Real.sqrt κ*x)/greenLogNormSq κ q x :=
    funext fun x => (radialLogPower_spatial_deriv κ β q x).deriv
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2*(q.1.re-Real.sqrt κ*x)*(-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2*q.1.im)) using 1 <;> try rfl
    simp
  have hs := ((((radialLogPower_spatial_deriv κ β q x).neg.mul_const β).mul_const (Real.sqrt κ)).mul hX).div hN
    (greenLogNormSq_pos κ q x).ne'
  rw [show (2 : ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.neg_apply, id_eq] at hs
  change HasDerivAt (fun y => -radialLogPower κ β q y * β * Real.sqrt κ *
    (q.1.re-Real.sqrt κ*y)/greenLogNormSq κ q y) _ x at hs
  rw [hs.deriv]
  have hn := (greenLogNormSq_pos κ q x).ne'
  dsimp only [greenLogNormSq] at hn ⊢
  generalize radialLogPower κ β q x = f
  generalize q.1.re-Real.sqrt κ*x = X at hn ⊢
  generalize Real.exp (2*q.1.im) = Y at hn ⊢
  have hk := Real.sq_sqrt hκ
  generalize Real.sqrt κ = r at *
  rw [← hk]
  field_simp [hn]
  ring

lemma radialLogPower_generator (κ β : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q
        (physicalLogLoewnerField (Real.sqrt κ*x) q) +
      (1/2 : ℝ)*iteratedDeriv 2 (radialLogPower κ β q) x =
      β*radialLogPower κ β q x*
        ((2+κ*(β-1)/2)*(q.1.re-Real.sqrt κ*x)^2+(κ/2-2)*Real.exp (2*q.1.im)) /
          (greenLogNormSq κ q x)^2 := by
  rw [radialLogPower_directional, radialLogPower_spatial_second κ β hκ]
  obtain ⟨hre,him,_⟩ := physicalLogLoewnerField_components κ q x
  rw [hre,him]
  ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma heightLogPower_directional (β : ℝ) (q v : ℂ × ℝ) :
    fderiv ℝ (heightLogPower β) q v = heightLogPower β q * β * v.1.im := by
  have hzim : HasDerivAt (fun t : ℝ => (q+t • v).1.im) v.1.im 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_im, Complex.smul_im,
      smul_eq_mul, id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const v.1.im).const_add q.1.im
  have hline : HasDerivAt (fun t : ℝ => heightLogPower β (q+t • v))
      (heightLogPower β q*β*v.1.im) 0 := by
    convert (hzim.const_mul β).exp using 1 <;> try rfl
    simp only [zero_smul, add_zero, heightLogPower]
    ring
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (heightLogPower β) :=
    (contDiff_const.mul (Complex.imCLM.contDiff.comp contDiff_fst)).exp
  have haff : HasDerivAt (fun t : ℝ => q+t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (heightLogPower β) (fderiv ℝ (heightLogPower β) q)
      (q+(0 : ℝ) • v) := by
    simpa using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hc := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hc.unique hline

noncomputable def swallowGenerator (κ β C : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  β*radialLogPower κ β q x*
    ((2+κ*(β-1)/2)*(q.1.re-Real.sqrt κ*x)^2+(κ/2-2)*Real.exp (2*q.1.im)) /
      (greenLogNormSq κ q x)^2 - 2*C*β*heightLogPower β q/greenLogNormSq κ q x

lemma swallowLyapunov_generator (κ β C : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => swallowLyapunov κ β C r x) q
        (physicalLogLoewnerField (Real.sqrt κ*x) q) +
      (1/2 : ℝ)*iteratedDeriv 2 (swallowLyapunov κ β C q) x =
      swallowGenerator κ β C q x := by
  have hr : DifferentiableAt ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q :=
    (((radialLogPower_contDiff κ β).comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp)) q
  have hh : DifferentiableAt ℝ (heightLogPower β) q :=
    ((show ContDiff ℝ (⊤ : ℕ∞) (heightLogPower β) from
      (contDiff_const.mul (Complex.imCLM.contDiff.comp contDiff_fst)).exp).differentiable (by simp)) q
  have hd : fderiv ℝ (fun r : ℂ × ℝ => swallowLyapunov κ β C r x) q =
      fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q +
        C • fderiv ℝ (heightLogPower β) q := by
    exact (hr.hasFDerivAt.add (hh.hasFDerivAt.const_mul C)).fderiv
  have h2 : iteratedDeriv 2 (swallowLyapunov κ β C q) x =
      iteratedDeriv 2 (radialLogPower κ β q) x := by
    unfold swallowLyapunov
    simp_rw [add_comm]
    exact iteratedDeriv_const_add (by decide) _
  rw [hd, h2, add_apply, smul_apply,
    smul_eq_mul, heightLogPower_directional]
  have he := radialLogPower_generator κ β hκ q x
  obtain ⟨_, him, _⟩ := physicalLogLoewnerField_components κ q x
  rw [him]
  unfold swallowGenerator
  calc
    _ = (fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q
        (physicalLogLoewnerField (Real.sqrt κ*x) q) +
        (1/2 : ℝ)*iteratedDeriv 2 (radialLogPower κ β q) x) -
        2*C*β*heightLogPower β q/greenLogNormSq κ q x := by ring
    _ = _ := by rw [he]

lemma radialLogPower_pos (κ β : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0 < radialLogPower κ β q x := Real.exp_pos _
lemma heightLogPower_pos (β : ℝ) (q : ℂ × ℝ) :
    0 < heightLogPower β q := Real.exp_pos _

 

lemma height_radial_ratio (κ β : ℝ) (_hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (q : ℂ × ℝ) (x : ℝ) :
    radialLogPower κ β q x * Real.exp (2*q.1.im) ≤
      heightLogPower β q * greenLogNormSq κ q x := by
  have hN := greenLogNormSq_pos κ q x
  have hle : Real.exp (2*q.1.im) ≤ greenLogNormSq κ q x := by
    unfold greenLogNormSq
    nlinarith [sq_nonneg (q.1.re-Real.sqrt κ*x)]
  have hlog : 2*q.1.im ≤ Real.log (greenLogNormSq κ q x) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hle
  unfold radialLogPower heightLogPower
  rw [← Real.exp_add, ← Real.exp_log hN, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Real.log_exp]
  nlinarith [mul_nonneg (sub_nonneg.mpr hβ2) (sub_nonneg.mpr hlog)]

lemma swallowGenerator_negative (κ : ℝ) (hκ : 4 < κ) (q : ℂ × ℝ) (x : ℝ) :
    swallowGenerator κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q x ≤
      -((κ-4)/(2*κ))*((κ-4)/4)*radialLogPower κ ((κ-4)/(2*κ)) q x /
        greenLogNormSq κ q x := by
  let β := (κ-4)/(2*κ)
  have hk : 0 < κ := by linarith
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ2 : β ≤ 2 := by dsimp [β]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hratio := height_radial_ratio κ β hβ.le hβ2 q x
  have hn := greenLogNormSq_pos κ q x
  have hc : 2+κ*(β-1)/2 = -(κ-4)/4 := by dsimp [β]; field_simp; ring
  change swallowGenerator κ β (3*(κ-4)/8) q x ≤ -β*((κ-4)/4)*radialLogPower κ β q x /
    greenLogNormSq κ q x
  unfold swallowGenerator
  rw [hc]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hn)).mp
  field_simp [hn.ne']
  dsimp only [greenLogNormSq] at hratio ⊢
  nlinarith [mul_nonneg (mul_nonneg hβ.le (sub_nonneg.mpr hκ.le)) (sub_nonneg.mpr hratio)]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

structure RadialLocalization
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (R : ℝ) (T : ℝ≥0) where
  τ : Ω → ℝ≥0
  stopping : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω : WithTop ℝ≥0))
  bounded : ∀ ω, τ ω ≤ T
  inside : ∀ ω t, t ≤ τ ω → greenLogNormSq κ (c.Q t ω) (B t ω) ≤ R^2 ∧ lo ≤ (c.Q t ω).1.im
  before : ∀ ω t, t < τ ω → greenLogNormSq κ (c.Q t ω) (B t ω) < R^2 ∧ lo < (c.Q t ω).1.im
  boundary : ∀ ω, τ ω < T → greenLogNormSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = R^2 ∨
    (c.Q (τ ω) ω).1.im = lo

lemma greenLogNormSq_continuous (κ : ℝ) :
    Continuous (fun v : (ℂ × ℝ) × ℝ => greenLogNormSq κ v.1 v.2) := by
  unfold greenLogNormSq
  fun_prop

lemma exists_radialLocalization
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (R : ℝ) (T : ℝ≥0)
    (hN : greenLogNormSq κ q₀ 0 ≤ R^2) (hlo : lo ≤ q₀.1.im) :
    Nonempty (RadialLocalization c R T) := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let D (t : ℝ≥0) (ω : Ω) := min (R^2-greenLogNormSq κ (c.Q t ω) (B t ω)) ((c.Q t ω).1.im-lo)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hDa : Adapted f D := by
    intro t
    have hQ := c.adapted t
    let : MeasurableSpace Ω := f t
    exact (measurable_const.sub ((greenLogNormSq_continuous κ).measurable.comp
      (hQ.prodMk (hBa t)))).min ((Complex.continuous_im.measurable.comp hQ.fst).sub_const lo)
  have hDc (ω : Ω) : Continuous (fun t => D t ω) := by
    have hQ := (c.lipschitz ω).continuous.comp NNReal.continuous_coe
    exact (continuous_const.sub ((greenLogNormSq_continuous κ).comp (hQ.prodMk (hBc ω)))).min
      ((Complex.continuous_im.comp hQ.fst).sub continuous_const)
  have hD0 (ω : Ω) : 0 ≤ D 0 ω := by
    simpa only [D, NNReal.coe_zero, c.initial, hB0, le_min_iff, sub_nonneg] using And.intro hN hlo
  obtain ⟨τ,hτ,hb,hin,hpre,hbd⟩ := first_margin_stopping f D hDa hDc hD0 T
  refine ⟨⟨τ,hτ,hb,?_,?_,?_⟩⟩
  · intro ω t ht
    simpa only [D, le_min_iff, sub_nonneg] using hin ω t ht
  · intro ω t ht
    simpa only [D, lt_min_iff, sub_pos] using hpre ω t ht
  · intro ω ht
    have hh := hbd ω ht
    dsimp only [D] at hh
    rw [min_eq_iff] at hh
    rcases hh with ⟨h,_⟩ | ⟨h,_⟩
    · exact Or.inl (sub_eq_zero.mp h).symm
    · exact Or.inr (sub_eq_zero.mp h)

namespace RadialLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    {c : ClippedLogSolution B hm κ lo hi hle q₀} {R : ℝ} {T : ℝ≥0}
lemma height_le_initial (a : RadialLocalization c R T) (ω : Ω) (t : ℝ≥0) (ht : t ≤ a.τ ω) :
    (c.Q t ω).1.im ≤ q₀.1.im := by
  have hd : ∀ s ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => c.Q s ω)
      (clippedLogLoewnerField lo hi hle (Real.sqrt κ*B s.toNNReal ω) (c.Q s ω))
      (Icc 0 (T : ℝ)) s := by
    intro s hs
    exact (c.derivative ω s hs.1).mono (fun s hs => hs.1)
  have hanti : AntitoneOn (fun s : ℝ => (c.Q s ω).1.im) (Icc 0 (T : ℝ)) :=
    clipped_log_height_antitone (U := fun u => Real.sqrt κ*B u ω)
      (Q := fun s => c.Q s ω) T hd
  have htT : (t : ℝ) ≤ T := NNReal.coe_le_coe.mpr (ht.trans (a.bounded ω))
  have hh : (c.Q t ω).1.im ≤ (c.Q 0 ω).1.im :=
    hanti ⟨le_rfl,T.coe_nonneg⟩ ⟨t.coe_nonneg,htT⟩ t.coe_nonneg
  rw [c.initial ω] at hh
  exact hh

lemma chart_identification (a : RadialLocalization c R T)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) {z : ℂ} (hz : z ∈ upperHalfPlane)
    (hq : q₀ = initialLogCoordinates z) (hhi : q₀.1.im ≤ hi)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) γ G F) :
    z ∈ survivingDomain γ (a.τ ω) ∧
      ∀ t : ℝ≥0, t ≤ a.τ ω → c.Q t ω = logLoewnerCoordinates G z t := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 (a.τ ω : ℝ)) := (c.derivative ω s hs.1).mono
    (show Icc (0 : ℝ) (a.τ ω : ℝ) ⊆ Ici 0 from fun s hs => hs.1)
  obtain ⟨hl,he⟩ := clipped_log_identification_of_endpoint ((hBc ω).const_mul _) hw
    (a.τ ω) z hz lo hi hle (fun t => c.Q t ω) ((c.initial ω).trans hq) hd
    (a.inside ω (a.τ ω) le_rfl).2
    (by simpa [hq, initialLogCoordinates] using hhi)
  exact ⟨hl,fun t ht => he ⟨t.coe_nonneg,by exact_mod_cast ht⟩⟩
end RadialLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma radialLogPower_le (κ β : ℝ) (hβ : 0 ≤ β) (q : ℂ × ℝ) (x R : ℝ)
    (_hR : 0 < R) (hN : greenLogNormSq κ q x ≤ R^2) :
    radialLogPower κ β q x ≤ Real.exp (β*Real.log R) := by
  have hl := Real.log_le_log (greenLogNormSq_pos κ q x) hN
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  unfold radialLogPower
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hl)]

lemma heightLogPower_le (κ β : ℝ) (hβ : 0 ≤ β) (q : ℂ × ℝ) (x R : ℝ)
    (_hR : 0 < R) (hN : greenLogNormSq κ q x ≤ R^2) :
    heightLogPower β q ≤ Real.exp (β*Real.log R) := by
  have hy : Real.exp (2*q.1.im) ≤ R^2 := by
    unfold greenLogNormSq at hN
    nlinarith [sq_nonneg (q.1.re-Real.sqrt κ*x)]
  have hl := Real.log_le_log (Real.exp_pos _) hy
  rw [Real.log_exp,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  unfold heightLogPower
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hl)]

lemma radialLogPower_div_lower (κ β : ℝ) (hβ : β ≤ 2) (q : ℂ × ℝ) (x R : ℝ)
    (_hR : 0 < R) (hN : greenLogNormSq κ q x ≤ R^2) :
    Real.exp ((β-2)*Real.log R) ≤ radialLogPower κ β q x/greenLogNormSq κ q x := by
  have hl := Real.log_le_log (greenLogNormSq_pos κ q x) hN
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have he : radialLogPower κ β q x/greenLogNormSq κ q x =
      Real.exp ((β/2-1)*Real.log (greenLogNormSq κ q x)) := by
    unfold radialLogPower
    conv_lhs => rhs; rw [← Real.exp_log (greenLogNormSq_pos κ q x)]
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr hl)]

lemma swallowGenerator_uniform_negative (κ : ℝ) (hκ : 4 < κ) (q : ℂ × ℝ) (x R : ℝ)
    (hR : 0 < R) (hN : greenLogNormSq κ q x ≤ R^2) :
    swallowGenerator κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q x ≤
      -(((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) := by
  let β := (κ-4)/(2*κ)
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ2 : β ≤ 2 := by dsimp [β]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hr := radialLogPower_div_lower κ β hβ2 q x R hR hN
  have ha : 0 ≤ β*((κ-4)/4) := by positivity
  have hm := mul_le_mul_of_nonneg_left hr ha
  have hg := swallowGenerator_negative κ hκ q x
  change swallowGenerator κ β (3*(κ-4)/8) q x ≤ -(β*((κ-4)/4)*Real.exp ((β-2)*Real.log R))
  dsimp only [β] at hm ⊢
  apply hg.trans
  convert neg_le_neg hm using 1
  ring

lemma norm_driver_of_radial_bound (κ R K : ℝ) (hκ : 0 < κ) (hR : 0 ≤ R)
    (q : ℂ × ℝ) (x : ℝ) (hq : ‖q‖ ≤ K) (hN : greenLogNormSq κ q x ≤ R^2) :
    |x| ≤ (K+R)/Real.sqrt κ := by
  have hX : |q.1.re-Real.sqrt κ*x| ≤ R := by
    rw [abs_le]
    have hp := Real.exp_pos (2*q.1.im)
    unfold greenLogNormSq at hN
    constructor <;> nlinarith
  have hqre : |q.1.re| ≤ K := (Complex.abs_re_le_norm _).trans ((norm_fst_le q).trans hq)
  have hx : |Real.sqrt κ*x| ≤ K+R := by
    calc
      _ = |q.1.re-(q.1.re-Real.sqrt κ*x)| := by congr 1; ring
      _ ≤ |q.1.re|+|q.1.re-Real.sqrt κ*x| := abs_sub _ _
      _ ≤ K+R := add_le_add hqre hX
  rw [abs_mul,abs_of_pos (Real.sqrt_pos.2 hκ)] at hx
  exact (le_div_iff₀ (Real.sqrt_pos.2 hκ)).mpr (by simpa only [mul_comm] using hx)

lemma swallowLyapunov_nonneg (κ β C : ℝ) (hC : 0 ≤ C) (q : ℂ × ℝ) (x : ℝ) :
    0 ≤ swallowLyapunov κ β C q x := by
  exact add_nonneg (radialLogPower_pos κ β q x).le (mul_nonneg hC (heightLogPower_pos β q).le)

lemma radialLogPower_at_boundary (κ β : ℝ) (q : ℂ × ℝ) (x R : ℝ)
    (hN : greenLogNormSq κ q x = R^2) :
    radialLogPower κ β q x = Real.exp (β*Real.log R) := by
  unfold radialLogPower
  rw [hN, Real.log_pow]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

lemma continuous_swallowGenerator (κ β C : ℝ) :
    Continuous (fun v : (ℂ × ℝ) × ℝ => swallowGenerator κ β C v.1 v.2) := by
  have hN : Continuous (fun v : (ℂ × ℝ) × ℝ => greenLogNormSq κ v.1 v.2) := by
    unfold greenLogNormSq
    fun_prop
  have hf := (radialLogPower_contDiff κ β).continuous
  have hh := (heightLogPower_contDiff β).continuous
  unfold swallowGenerator
  apply Continuous.sub
  · apply Continuous.div
    · exact (continuous_const.mul hf).mul (by fun_prop)
    · exact hN.pow 2
    · intro v; exact pow_ne_zero 2 (greenLogNormSq_pos κ v.1 v.2).ne'
  · exact (continuous_const.mul hh).div hN (fun v => (greenLogNormSq_pos κ v.1 v.2).ne')

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma swallowLyapunov_pair_directional (κ p a : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun zz : (ℂ × ℝ) × ℝ => swallowLyapunov κ p a zz.1 zz.2) (q, x) (v, 0) =
      fderiv ℝ (fun r : ℂ × ℝ => swallowLyapunov κ p a r x) q v := by
  have hd := ((swallowLyapunov_contDiff κ p a).differentiable (by simp)) (q, x)
  have hp := (hasFDerivAt_id (𝕜 := ℝ) q).prodMk (hasFDerivAt_const (𝕜 := ℝ) (E := ℂ × ℝ) x q)
  have hc := (hd.hasFDerivAt.comp q hp).fderiv
  have he := congrArg (fun D : (ℂ × ℝ) →L[ℝ] ℝ => D v) hc
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, id_eq, zero_apply] using he.symm

 

lemma exists_compact_swallow_field (κ p a R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : (ℂ × ℝ) × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ q x, ‖(q, x)‖ ≤ R → φ (q, x) = swallowLyapunov κ p a q x) ∧
      (∀ q x, ‖(q, x)‖ ≤ R →
        fderiv ℝ φ (q, x) = fderiv ℝ (fun zz : (ℂ × ℝ) × ℝ => swallowLyapunov κ p a zz.1 zz.2) (q, x)) ∧
      (∀ q x, ‖(q, x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (q, y)) x =
        iteratedDeriv 2 (swallowLyapunov κ p a q) x) := by
  let b : ContDiffBump (0 : (ℂ × ℝ) × ℝ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let φ (zz : (ℂ × ℝ) × ℝ) : ℝ := b zz * swallowLyapunov κ p a zz.1 zz.2
  have hnear (zz : (ℂ × ℝ) × ℝ) (hp : ‖zz‖ ≤ R) :
      φ =ᶠ[𝓝 zz] (fun r : (ℂ × ℝ) × ℝ => swallowLyapunov κ p a r.1 r.2) := by
    have hball : zz ∈ Metric.ball (0 : (ℂ × ℝ) × ℝ) b.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      change ‖zz‖ < R + 1
      linarith
    filter_upwards [b.eventuallyEq_one_of_mem_ball hball] with r hr
    simp only [φ, hr, Pi.one_apply, one_mul]
  refine ⟨φ, b.contDiff.mul (swallowLyapunov_contDiff κ p a), b.hasCompactSupport.mul_right,
    (fun q x h => (hnear (q, x) h).eq_of_nhds), ?_, ?_⟩
  · intro q x h
    exact (hnear (q, x) h).fderiv_eq
  · intro q x h
    have he := (hnear (q, x) h).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)
    exact he.iteratedDeriv_eq 2

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma bounded_cumulative_grid_error
    {Ω : Type*} [MeasurableSpace Ω] (G : ℝ → Ω → ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ u ω, |G u ω| ≤ C) (τ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    |(∫ u in (0 : ℝ)..(stopGrid n (τ ω) : ℝ), G u ω) -
       (∫ u in (0 : ℝ)..(τ ω : ℝ), G u ω)| ≤ C * (1 / ((n : ℝ) + 1)) := by
  have hle : (τ ω : ℝ) ≤ stopGrid n (τ ω) := (stopGrid_bounds n (τ ω)).1
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (bounded_time_section_intervalIntegrable 0 (τ ω) (τ ω).coe_nonneg G hG C hb ω)
    (bounded_time_section_intervalIntegrable (τ ω) (stopGrid n (τ ω)) hle G hG C hb ω)
  rw [← hs, add_sub_cancel_left]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (τ ω : ℝ)) (b := (stopGrid n (τ ω) : ℝ)) (C := C) (f := fun u => G u ω)
    (fun u _ => by simpa only [Real.norm_eq_abs] using hb u ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] at hh
  refine hh.trans (mul_le_mul_of_nonneg_left ?_ hC)
  have hu : (stopGrid n (τ ω) : ℝ) ≤ (τ ω : ℝ) + 1 / ((n : ℝ) + 1) := by
    exact_mod_cast (stopGrid_bounds n (τ ω)).2
  linarith

 

theorem brownian_time_field_stopped_dynkin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (K : ℝ≥0) (F a : ℝ≥0 → Ω → ℝ → ℝ)
    (hF : SmoothTimeBrownianField B hm K F a)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) :
    (∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P) = (∫ ω, F 0 ω (B 0 ω) ∂P) +
      ∫ ω, (∫ u in (0 : ℝ)..(τ ω : ℝ), brownianFieldDrift B F a u ω) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hτm := stopping_time_measurable_nnreal hτ
  let V (n : ℕ) (ω : Ω) := F (stopGrid n (τ ω)) ω (B (stopGrid n (τ ω)) ω)
  let H (n : ℕ) (ω : Ω) := ∫ u in (0 : ℝ)..(stopGrid n (τ ω) : ℝ), brownianFieldDrift B F a u ω
  let H₀ (ω : Ω) := ∫ u in (0 : ℝ)..(τ ω : ℝ), brownianFieldDrift B F a u ω
  have hVm (n : ℕ) : Measurable (V n) :=
    measurable_discrete_eval (fun k ω => F (stopGridTime n k) ω (B (stopGridTime n k) ω))
      (fun k => hF.eval_measurable _ 0 (by decide) (hm _)) (stopGridIndex_measurable hτm n)
  have hVb (n : ℕ) (ω : Ω) : |V n ω| ≤ (K : ℝ) := hF.bound _ ω _ 0 (by decide)
  have hVi (n : ℕ) : Integrable (V n) P :=
    Integrable.of_bound (hVm n).aestronglyMeasurable (K : ℝ)
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hVb n ω)
  have hGm := hF.generator_measurable hBm
  have hHjoint := cumulative_integral_measurable _ hGm
  have hHm (n : ℕ) : Measurable (H n) :=
    measurable_discrete_eval (fun k ω => ∫ u in (0 : ℝ)..(stopGridTime n k : ℝ), brownianFieldDrift B F a u ω)
      (fun k => hHjoint.comp measurable_prodMk_left) (stopGridIndex_measurable hτm n)
  have hH₀m : Measurable H₀ := hHjoint.comp (hτm.prodMk measurable_id)
  have hH₀b (ω : Ω) : |H₀ ω| ≤ 2 * (K : ℝ) * T := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (τ ω : ℝ)) (C := 2 * (K : ℝ))
      (f := fun u => brownianFieldDrift B F a u ω)
      (fun u _ => by simpa only [Real.norm_eq_abs] using hF.generator_bound u ω)
    simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg (τ ω).coe_nonneg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hb ω) (by positivity))
  have hH₀i : Integrable H₀ P := Integrable.of_bound hH₀m.aestronglyMeasurable _
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hH₀b ω)
  have hdiff (n : ℕ) (ω : Ω) : |H n ω - H₀ ω| ≤ (2 * (K : ℝ)) * (1 / ((n : ℝ) + 1)) :=
    bounded_cumulative_grid_error _ hGm _ (by positivity) hF.generator_bound τ n ω
  have hHb (n : ℕ) (ω : Ω) : |H n ω| ≤ 2 * (K : ℝ) * (T + 1) := by
    have hr : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hd := (hdiff n ω).trans (mul_le_mul_of_nonneg_left hr (by positivity))
    have ht : |H n ω| ≤ |H n ω - H₀ ω| + |H₀ ω| := by
      calc _ = |(H n ω - H₀ ω) + H₀ ω| := by rw [sub_add_cancel]
           _ ≤ _ := abs_add_le _ _
    nlinarith [hH₀b ω]
  have hHi (n : ℕ) : Integrable (H n) P := Integrable.of_bound (hHm n).aestronglyMeasurable _
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hHb n ω)
  have hmean (n : ℕ) : (∫ ω, V n ω ∂P) = (∫ ω, F 0 ω (B 0 ω) ∂P) + ∫ ω, H n ω ∂P := by
    have hh := brownian_compensated_grid_integral hB hm hBm hF τ hτ T hb n
    change (∫ ω, V n ω - H n ω ∂P) = _ at hh
    rw [integral_sub (hVi n) (hHi n)] at hh
    linarith
  have hlimV : Tendsto (fun n => ∫ ω, V n ω ∂P) atTop
      (𝓝 (∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (K : ℝ))
      (fun n => (hVm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hVb n ω)
    exact Eventually.of_forall fun ω => (hF.path_continuous hBc ω).continuousAt.tendsto.comp (stopGrid_tendsto (τ ω))
  have hlimH : Tendsto (fun n => ∫ ω, H n ω ∂P) atTop (𝓝 (∫ ω, H₀ ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 2 * (K : ℝ) * (T + 1))
      (fun n => (hHm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hHb n ω)
    apply Eventually.of_forall
    intro ω
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) (fun n => by simpa only [Real.dist_eq] using hdiff n ω)
    simpa only [mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (K : ℝ))
  have he := hlimH.const_add (∫ ω, F 0 ω (B 0 ω) ∂P)
  simp_rw [← hmean] at he
  exact tendsto_nhds_unique hlimV he

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma compact_swallow_drift
    (κ p α : ℝ) (hκ : 0 ≤ κ) (lo hi : ℝ) (hle : lo ≤ hi)
    (φ : (ℂ × ℝ) × ℝ → ℝ) (q : ℂ × ℝ) (x : ℝ)
    (hφD : fderiv ℝ φ (q, x) =
      fderiv ℝ (fun r : (ℂ × ℝ) × ℝ => swallowLyapunov κ p α r.1 r.2) (q, x))
    (hφ2 : iteratedDeriv 2 (fun y => φ (q, y)) x =
      iteratedDeriv 2 (swallowLyapunov κ p α q) x)
    (hq : q.1.im ∈ Icc lo hi) :
    fderiv ℝ φ (q, x)
        (clippedLogLoewnerField lo hi hle (Real.sqrt κ * x) q, 0) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (fun y => φ (q, y)) x =
        swallowGenerator κ p α q x := by
  rw [hφD, hφ2, swallowLyapunov_pair_directional,
    clippedLogLoewnerField_eq_physical lo hi hle _ _ hq]
  exact swallowLyapunov_generator κ p α hκ q x

 

theorem ClippedLogSolution.stopped_swallow_dynkin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 ≤ κ) (p α : ℝ)
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) :
    Integrable (fun ω => swallowLyapunov κ p α (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, swallowLyapunov κ p α (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
        swallowLyapunov κ p α q₀ 0 +
        ∫ ω, (∫ t in (0 : ℝ)..(τ ω : ℝ),
          swallowGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_swallow_field κ p α R hR
  obtain ⟨L₀, K₀, hL₀, _⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) :=
    clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)
  have hBr : Measurable (fun p : ℝ × Ω => Real.sqrt κ * B p.1.toNNReal p.2) :=
    (hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      measurable_snd)).const_mul _
  have hpair : Measurable (fun p : ℝ × Ω =>
      (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)) := hBr.prodMk c.measurable
  have hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun p : ℝ × Ω => (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)))
    exact (continuous_clippedLogLoewnerField lo hi hle).measurable.comp hpair
  have hVb (t : ℝ) (ω : Ω) : ‖V t ω‖ ≤ (max c.L L₀ : ℝ≥0) :=
    (hL₀ _ _).trans (by exact_mod_cast le_max_right c.L L₀)
  obtain ⟨K, hfield⟩ := compact_state_smooth_brownian_field B hm c.Q V (max c.L L₀)
    c.measurable c.adapted (fun ω => (c.lipschitz ω).weaken (le_max_left _ _)) hVm hVb
    (fun t ω ht => c.derivative ω t ht) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (c.Q t ω, x)
  let a (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (c.Q t ω, x) (V t ω, 0)
  have hgen (ω : Ω) (t : ℝ) (ht : t ∈ Icc 0 (τ ω : ℝ)) :
      brownianFieldDrift B F a t ω =
        swallowGenerator κ p α (c.Q t ω) (B t.toNNReal ω) := by
    have ht' : t.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr ht.2
    obtain ⟨hball, hlo, hhi⟩ := hinside ω t.toNNReal ht'
    have he : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.1
    change fderiv ℝ φ (c.Q (t.toNNReal : ℝ) ω, B t.toNNReal ω)
      (V (t.toNNReal : ℝ) ω, 0) + _ = _
    dsimp only [V]
    rw [Real.toNNReal_coe]
    have hh := compact_swallow_drift κ p α hκ lo hi hle φ _ _
      (hφD _ _ hball) (hφ2 _ _ hball) ⟨hlo, hhi⟩
    simpa only [F, he] using hh
  have hopt := brownian_time_field_stopped_dynkin hB hm hBm hBc K F a hfield τ hτ T hb
  have hτm := stopping_time_measurable_nnreal hτ
  have hBmτ : Measurable (fun ω => B (τ ω) ω) := hBm.comp (hτm.prodMk measurable_id)
  have hQmτ : Measurable (fun ω => c.Q (τ ω) ω) :=
    c.measurable.comp ((NNReal.continuous_coe.measurable.comp hτm).prodMk measurable_id)
  have hfm : Measurable (fun ω => F (τ ω) ω (B (τ ω) ω)) :=
    hφ.continuous.measurable.comp (hQmτ.prodMk hBmτ)
  have hfi : Integrable (fun ω => F (τ ω) ω (B (τ ω) ω)) P := by
    apply Integrable.of_bound hfm.aestronglyMeasurable (K : ℝ)
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, iteratedDeriv_zero] using
        hfield.bound (τ ω) ω (B (τ ω) ω) 0 (by decide)
  have hfeq (ω : Ω) : F (τ ω) ω (B (τ ω) ω) =
      swallowLyapunov κ p α (c.Q (τ ω) ω) (B (τ ω) ω) :=
    hφeq _ _ (hinside ω (τ ω) le_rfl).1
  refine ⟨hfi.congr (Eventually.of_forall hfeq), ?_⟩
  calc
    _ = ∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (hfeq ω).symm)
    _ = (∫ ω, F 0 ω (B 0 ω) ∂P) +
        ∫ ω, (∫ t in (0 : ℝ)..(τ ω : ℝ), brownianFieldDrift B F a t ω) ∂P := hopt
    _ = _ := by
      congr 1
      · calc
          _ = ∫ _, swallowLyapunov κ p α q₀ 0 ∂P := by
            apply integral_congr_ae
            filter_upwards [hB.eval_zero_ae_eq_zero] with ω hB0
            change φ (c.Q 0 ω, B 0 ω) = _
            have hh : ‖(c.Q 0 ω, B 0 ω)‖ ≤ R := by
              simpa only [NNReal.coe_zero] using (hinside ω 0 zero_le).1
            rw [hφeq _ _ hh, c.initial ω, hB0]
          _ = _ := by simp
      · apply integral_congr_ae
        exact Eventually.of_forall fun ω => intervalIntegral.integral_congr
          (fun t ht => hgen ω t (by simpa only [uIcc_of_le (τ ω).coe_nonneg] using ht))

end SLEExactGauge
end

 
end

end OAI
