import Mathlib
import OAI.Probability.SKFluctuations.ScalarFiniteInvariant

namespace OAI

/-! Scalar Planted Energy. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Scalar
open scoped Topology NNReal

 
noncomputable def scalarPlantedEnergy {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (q : ℝ) : ℝ :=
  (scalarTailJet hT α q).square.nonnegativeProfileTest (rescaledMassProfile α hT)
    0 (Real.toNNReal (T*q)) 0

 theorem scalarTailJet_F_tendsto {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    {q : ℕ → ℝ} {r : ℝ} (hq : Tendsto q atTop (𝓝 r)) :
    TendstoUniformly (fun k => (scalarTailJet hT α (q k)).F) (scalarTailJet hT α r).F atTop := by
  have hl := hq.const_mul T
  have ht := continuous_real_toNNReal.tendsto (T*(1-r)) |>.comp ((tendsto_const_nhds.sub hq).const_mul T)
  have hh := scalarProfileJet_window_tendsto (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) hl ht 0
  rw [Metric.tendstoUniformly_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with k hk x
  exact hk (x 0)

 theorem scalarTailJet_square_tendsto {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles)
    {q : ℕ → ℝ} {r : ℝ} (hq : Tendsto q atTop (𝓝 r)) :
    TendstoUniformly (fun k => (scalarTailJet hT α (q k)).square.A)
      (scalarTailJet hT α r).square.A atTop := by
  have hl := hq.const_mul T
  have ht := continuous_real_toNNReal.tendsto (T*(1-r)) |>.comp ((tendsto_const_nhds.sub hq).const_mul T)
  have hh := scalarProfileJet_window_tendsto (rescaledMassProfile α hT)
    (fun s => (α.property.1 (s/T)).2) hl ht 1
  rw [Metric.tendstoUniformly_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh (ε/2) (by positivity)] with k hk x
  have hd : |(scalarTailJet hT α (q k)).G 0 x-(scalarTailJet hT α r).G 0 x| < ε/2 := by
    simpa only [Real.dist_eq,abs_sub_comm,scalarTailJet,scalarProfileHeatJet,Function.comp_apply] using hk (x 0)
  have ha := abs_le.mp (scalarTailJet_G_bound hT α (q k) 0 x)
  have hb := abs_le.mp (scalarTailJet_G_bound hT α r 0 x)
  have he : |(scalarTailJet hT α (q k)).G 0 x+(scalarTailJet hT α r).G 0 x| ≤ 2 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  rw [Real.dist_eq,abs_sub_comm]
  change |((scalarTailJet hT α (q k)).G 0 x)^2-((scalarTailJet hT α r).G 0 x)^2| < ε
  rw [sq_sub_sq,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg ((scalarTailJet hT α (q k)).G 0 x-(scalarTailJet hT α r).G 0 x))]

 theorem scalarPlantedEnergy_continuous {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) :
    Continuous (scalarPlantedEnergy hT α) := by
  rw [continuous_iff_seqContinuous]
  intro q r hq
  let A := rescaledMassProfile α hT
  have hA (s : ℝ) : A.mass s ≤ 1 := (α.property.1 (s/T)).2
  have hm := HeatJet.nonnegativeProfileTest_terminal_tendsto
    (fun k => (scalarTailJet hT α (q k)).square) (scalarTailJet hT α r).square
    (scalarTailJet_F_tendsto hT α hq) (scalarTailJet_square_tendsto hT α hq)
    (fun _ => A) (fun _ => hA) (fun _ => 0) (fun k => Real.toNNReal (T*q k))
  have hl := ((scalarTailJet hT α r).square.nonnegativeProfileTest_window_continuous A hA 0).tendsto
    (0,Real.toNNReal (T*r)) |>.comp
      (tendsto_const_nhds.prodMk_nhds (continuous_real_toNNReal.tendsto (T*r) |>.comp (hq.const_mul T)))
  have hh := (hm.tendsto_at 0).add hl
  simpa only [Function.comp_def,sub_add_cancel,zero_add,scalarPlantedEnergy,A] using hh

 theorem scalarPlantedEnergy_bounds {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) (q : ℝ) :
    0 ≤ scalarPlantedEnergy hT α q ∧ scalarPlantedEnergy hT α q ≤ 1 := by
  constructor
  · exact (scalarTailJet hT α q).square.nonnegativeProfileTest_nonneg
      (fun y => sq_nonneg _) (rescaledMassProfile α hT) (fun s => (α.property.1 (s/T)).2) 0 _ 0
  · exact (le_abs_self _).trans ((scalarTailJet hT α q).square.nonnegativeProfileTest_abs_le
      (scalarTailJet_square_bound hT α q) (rescaledMassProfile α hT)
      (fun s => (α.property.1 (s/T)).2) 0 _ 0)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 theorem scalarTailJet_plateau_evolve {T p r m : ℝ} (hT : 0 < T)
    (hpr : p < r) (hr : r ≤ 1) (α : boundedMassProfiles) (hm : 0 < m)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    (scalarTailJet hT α p).F=((scalarTailJet hT α r).evolve hm (T*(r-p))).F := by
  rw [scalarTailJet_restart hT hpr.le hr α]
  funext x
  have hd : 0 < T*(r-p) := mul_pos hT (sub_pos.mpr hpr)
  have hh := (scalarTailJet hT α r).nonnegativeProfileValue_constant_Ioo
    (rescaledMassProfile α hT) hm (T*p) (Real.toNNReal (T*(r-p)))
    (by rwa [Real.coe_toNNReal _ hd.le]) (by
      intro s hs
      change α.val (s/T)=m
      apply hf
      rw [Real.coe_toNNReal _ hd.le] at hs
      exact ⟨(lt_div_iff₀ hT).mpr (by nlinarith [hs.1]),
        (div_lt_iff₀ hT).mpr (by nlinarith [hs.2])⟩) x
  change _ = clockContinuation m (scalarTailJet hT α r).F (T*(r-p)) x
  simpa only [Real.coe_toNNReal _ hd.le] using hh

 theorem scalarPlantedEnergy_plateau {T p q r m : ℝ} (hT : 0 < T)
    (hp : 0 ≤ p) (hpq : p < q) (hqr : q < r) (hr : r ≤ 1)
    (α : boundedMassProfiles) (hm : 0 < m) (hm1 : m ≤ 1)
    (hf : ∀ u ∈ Ioo p r, α.val u=m) :
    scalarPlantedEnergy hT α q=
      ((scalarTailJet hT α r).profileGapSquareJet (scalarTailJet_G_smooth hT α r)
        hm (scalarTailJet_gradientTest hT α r).1 (T*(r-p)) (T*(q-p))).nonnegativeProfileTest
        (rescaledMassProfile α hT) 0 (Real.toNNReal (T*p)) 0 := by
  let J := scalarTailJet hT α r
  let K := scalarTailJet hT α q
  have hs : 0 < T*(q-p) := mul_pos hT (sub_pos.mpr hpq)
  have ht : 0 ≤ T*p := mul_nonneg hT.le hp
  have hq : 0 ≤ T*q := mul_nonneg hT.le (hp.trans hpq.le)
  have hd : 0 ≤ T*(r-q) := mul_nonneg hT.le (sub_nonneg.mpr hqr.le)
  have he : Real.toNNReal (T*p)+Real.toNNReal (T*(q-p))=Real.toNNReal (T*q) := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ ht,Real.coe_toNNReal _ hs.le,Real.coe_toNNReal _ hq]
    ring
  have hh := K.square.nonnegativeProfileTest_clock_concat (rescaledMassProfile α hT)
    (fun u => (α.property.1 (u/T)).2) hm hm1 0
    (Real.toNNReal (T*p)) (Real.toNNReal (T*(q-p))) (by rwa [Real.coe_toNNReal _ hs.le]) (by
      intro u hu
      change α.val (u/T)=m
      apply hf
      simp only [zero_add,Real.coe_toNNReal _ ht,Real.coe_toNNReal _ hs.le] at hu
      exact ⟨(lt_div_iff₀ hT).mpr (by nlinarith [hu.1]),
        (div_lt_iff₀ hT).mpr (by nlinarith [hu.2])⟩) 0
  rw [he] at hh
  change scalarPlantedEnergy hT α q = _ at hh
  rw [hh]
  have hF : K.F=(J.evolve hm (T*(r-q))).F :=
    scalarTailJet_plateau_evolve hT hqr hr α hm (fun u hu => hf u ⟨hpq.trans hu.1,hu.2⟩)
  have hA : K.A=(J.evolve hm (T*(r-q))).A := by
    rw [(scalarTailJet_gradientTest hT α q).1,
      ((scalarTailJet_gradientTest hT α r).evolve hm (T*(r-q))).1]
    exact HeatJet.G_congr_F hF
  have hdiff : T*(r-p)-T*(q-p)=T*(r-q) := by ring
  apply congrFun (HeatJet.nonnegativeProfileTest_congr _ _ ?_ ?_ _ _ _) 0
  · rw [HeatJet.profileGapSquareJet_F]
    change clockContinuation m K.F (Real.toNNReal (T*(q-p)))=
      clockContinuation m J.F (T*(r-p))
    rw [Real.coe_toNNReal _ hs.le,hF]
    funext x
    change clockContinuation m (clockContinuation m J.F (T*(r-q))) (T*(q-p)) x = _
    rw [clockContinuation_add J.lipschitz hm.ne' hs.le hd]
    congr 1
    ring
  · rw [HeatJet.profileGapSquareJet_A]
    change clockTest m K.F (fun y => (K.A y)^2) (Real.toNNReal (T*(q-p)))=
      J.filledSquare hm (T*(r-p)) (T*(q-p))
    rw [Real.coe_toNNReal _ hs.le,hF,hA]
    unfold HeatJet.filledSquare
    rw [hdiff]
    rfl

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

structure ResidualJet where
  jet : ℕ → ℝ → ℝ
  derivative : ∀ n x, HasDerivAt (jet n) (jet (n+1) x) x
  bounded : ∀ n, AbsBounded (jet (n+1))

namespace ResidualJet

theorem continuous (J : ResidualJet) (n : ℕ) : Continuous (J.jet n) :=
  continuous_iff_continuousAt.mpr fun x => (J.derivative n x).continuousAt

theorem bddSmooth (J : ResidualJet) (r n : ℕ) :
    BddSmooth r (fun x : Fin 1 → ℝ => J.jet (n+1) (x 0)) := by
  exact bddSmooth_of_uniform_real_chain (u := fun n p => J.jet (n+1) p.2)
    (fun n => (J.continuous (n+1)).comp continuous_snd)
    (fun n => by
      obtain ⟨K,hK,hb⟩ := J.bounded n
      exact ⟨K,hK,fun p => hb p.2⟩)
    (fun n _ x => J.derivative (n+1) x) r n 0

theorem lipschitz (J : ResidualJet) : ∃ C : ℝ≥0, LipschitzWith C (J.jet 0) := by
  obtain ⟨C,hC,hB⟩ := J.bounded 0
  refine ⟨⟨C,hC⟩,lipschitzWith_of_nnnorm_deriv_le (fun x => (J.derivative 0 x).differentiableAt) ?_⟩
  intro x
  rw [(J.derivative 0 x).deriv]
  exact hB x

theorem line (J : ResidualJet) (n : ℕ) (x v : Fin 1 → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => J.jet n ((x+r • v) 0))
      (∑ i : Fin 1, v i*J.jet (n+1) ((x+s • v) 0)) s := by
  have hh := (J.derivative n (x 0+s*v 0)).comp s
    ((hasDerivAt_const s (x 0)).add ((hasDerivAt_id s).mul_const (v 0)))
  convert! hh using 1
  simp only [Fin.sum_univ_one,Pi.add_apply,Pi.smul_apply,smul_eq_mul,zero_add,one_mul]
  ring

theorem coord (J : ResidualJet) (n : ℕ) (i : Fin 1) (x : Fin 1 → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => J.jet n ((x+r • (Pi.single i (1:ℝ) : Fin 1 → ℝ)) 0))
      (J.jet (n+1) ((x+s • (Pi.single i (1:ℝ) : Fin 1 → ℝ)) 0)) s := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa only [Fin.sum_univ_one,Pi.single_eq_same,one_mul] using J.line n x (Pi.single 0 1) s

noncomputable def heatJet (J : ResidualJet) : HeatJet 0 where
  F x := J.jet 0 (x 0)
  A _ := 0
  G _ x := J.jet 1 (x 0)
  H _ x := J.jet 2 (x 0)
  A₁ _ _ := 0
  A₂ _ _ := 0
  C := J.lipschitz.choose
  lipschitz := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    exact (J.lipschitz.choose_spec.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y 0) J.lipschitz.choose.coe_nonneg)
  smoothA := BddSmooth.const 0 0
  smoothG _ := J.bddSmooth 0 0
  smoothH _ := J.bddSmooth 0 1
  smoothA₁ _ := BddSmooth.const 0 0
  smoothA₂ _ := BddSmooth.const 0 0
  derivF := J.line 0
  derivG := J.coord 1
  derivA := by intro x v t; simpa only [mul_zero,Finset.sum_const_zero] using hasDerivAt_const t (0:ℝ)
  derivA₁ := by intro i x t; exact hasDerivAt_const t 0

noncomputable def zero : ResidualJet where
  jet _ _ := 0
  derivative _ x := hasDerivAt_const x 0
  bounded _ := ⟨0,le_rfl,by intro x; simp⟩

noncomputable def add (J K : ResidualJet) : ResidualJet where
  jet n x := J.jet n x+K.jet n x
  derivative n x := (J.derivative n x).add (K.derivative n x)
  bounded n := (J.bounded n).add (K.bounded n)

noncomputable def scale (c : ℝ) (J : ResidualJet) : ResidualJet where
  jet n x := c*J.jet n x
  derivative n x := (J.derivative n x).const_mul c
  bounded n := (J.bounded n).const_mul c

 
noncomputable def heat (J : ResidualJet) (t a : ℝ) : ResidualJet where
  jet n x := a^n*realSpatialJet (J.heatJet.scalarClockPlane 1) n (t,a*x)
  derivative n x := by
    have hr := J.heatJet.scalarClockPlane_spatialRegular (fun r _ => J.bddSmooth r 0) (by norm_num : (0:ℝ)<1)
    have hh := ((realSpatialJet_hasDerivAt hr n t (a*x)).comp x
      ((hasDerivAt_id x).const_mul a)).const_mul (a^n)
    convert hh using 1 <;> first | rfl | (rw [pow_succ]; ring)
  bounded n := by
    obtain ⟨K,hK,hb⟩ := J.heatJet.scalarClockPlane_positiveJets_uniformBounded
      (fun r _ => J.bddSmooth r 0) (by norm_num : (0:ℝ)<1) n
    refine ⟨|a^(n+1)| * K,mul_nonneg (abs_nonneg _) hK,?_⟩
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb (t,a*x)) (abs_nonneg _)

end ResidualJet
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology

private theorem ParabolicBounded_quadratic_add_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (a x : ℝ) :
    deriv (fun y => f y+a*(1+y^2)) x = deriv f x+a*(2*x) := by
  have hh := (hf x).hasDerivAt.add ((((hasDerivAt_id x).pow 2).const_add 1).const_mul a)
  convert hh.deriv using 1
  · congr 1
  · norm_num

private theorem ParabolicBounded_quadratic_add_second {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (a x : ℝ) :
    deriv (deriv (fun y => f y+a*(1+y^2))) x = deriv (deriv f) x+2*a := by
  have he : deriv (fun y => f y+a*(1+y^2)) = fun y => deriv f y+a*(2*y) :=
    funext (ParabolicBounded_quadratic_add_deriv hf a)
  rw [he]
  have hh := (hf' x).hasDerivAt.add (((hasDerivAt_id x).const_mul 2).const_mul a)
  convert hh.deriv using 1 <;> first | rfl | ring

private theorem ParabolicBounded_quadratic_barrier_forcing {b c M B x : ℝ}
    (hb : |b| ≤ B) (hc : c ≤ M) :
    0 ≤ (M+1+B)*(1+x^2)-(1+2*b*x+c*(1+x^2)) := by
  have hB := (abs_nonneg b).trans hb
  have hbx : 2*b*x ≤ B*(1+x^2) := by
    have h1 : b*x ≤ B*|x| := (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg x))
    have h2 : 2*|x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
    nlinarith [mul_le_mul_of_nonneg_left h2 hB]
  nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ 1+x^2 by positivity),sq_nonneg x]

private theorem ParabolicBounded_quadratic_barrier_tail {v : ℝ → ℝ → ℝ} {R L K ε : ℝ}
    (_hL : 0 ≤ L) (hv : ∀ t ∈ Icc 0 R, ∀ x, |v t x| ≤ L)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ A : ℝ, ∀ t ∈ Icc 0 R, ∀ x, A ≤ |x| →
      0 ≤ v t x+ε*Real.exp (K*t)*(1+x^2) := by
  refine ⟨max 1 (L/ε),?_⟩
  intro t ht x hx
  have h1 : 1 ≤ |x| := (le_max_left _ _).trans hx
  have h2 : L ≤ ε*|x| := by
    have hh := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hx)
    nlinarith
  have hsq : |x| ≤ x^2 := by nlinarith [sq_abs x]
  have he : 1 ≤ Real.exp (K*t) := Real.one_le_exp_iff.mpr (mul_nonneg hK ht.1)
  have hz : 0 ≤ 1+x^2 := by positivity
  have hm := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hε.le he) hz
  have hlow := (abs_le.mp (hv t ht x)).1
  nlinarith

 

theorem parabolic_nonneg_bounded_real {v b c F : ℝ → ℝ → ℝ} {R M B L : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Icc 0 R ×ˢ univ))
    (hdx : ∀ t ∈ Ioc 0 R, Differentiable ℝ (v t))
    (hdxx : ∀ t ∈ Ioc 0 R, Differentiable ℝ (deriv (v t)))
    (hpde : ∀ t ∈ Ioc 0 R, ∀ x,
      HasDerivAt (fun s => v s x)
        ((1/2:ℝ)*deriv (deriv (v t)) x+b t x*deriv (v t) x+c t x*v t x+F t x) t)
    (hb : ∀ t ∈ Ioc 0 R, ∀ x, |b t x| ≤ B)
    (hM : ∀ t ∈ Ioc 0 R, ∀ x, c t x ≤ M)
    (hF : ∀ t ∈ Ioc 0 R, ∀ x, 0 ≤ F t x)
    (hL : 0 ≤ L) (hv : ∀ t ∈ Icc 0 R, ∀ x, |v t x| ≤ L)
    (hinit : ∀ x, 0 ≤ v 0 x) :
    ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ v t x := by
  let K := max (M+1+B) 0
  have hK : 0 ≤ K := le_max_right _ _
  have barrier (ε : ℝ) (hε : 0 < ε) :
      ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ v t x+ε*Real.exp (K*t)*(1+x^2) := by
    let E : ℝ → ℝ := fun s => ε*Real.exp (K*s)
    have hEd (s : ℝ) : HasDerivAt E (K*E s) s := by
      have hh := (((hasDerivAt_id s).const_mul K).exp).const_mul ε
      convert hh using 1 <;> first | rfl | (dsimp only [E,id]; ring)
    have hEc : Continuous E := continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hEpos (s : ℝ) : 0 ≤ E s := mul_nonneg hε.le (Real.exp_nonneg _)
    have hforce (s : ℝ) (hs : s ∈ Ioc 0 R) (y : ℝ) :
        0 ≤ K*(1+y^2)-(1+2*b s y*y+c s y*(1+y^2)) := by
      have hh := ParabolicBounded_quadratic_barrier_forcing (x := y) (hb s hs y) (hM s hs y)
      have hk := mul_le_mul_of_nonneg_right (le_max_left (M+1+B) 0) (show 0 ≤ 1+y^2 by positivity)
      linarith
    apply parabolic_nonneg_real (d := fun _ _ => 1/2) (b := b) (c := c)
      (F := fun s y => F s y+E s*(K*(1+y^2)-(1+2*b s y*y+c s y*(1+y^2)))) (M := M)
    · exact hc.add ((hEc.comp continuous_fst).mul (continuous_const.add (continuous_snd.pow 2))).continuousOn
    · intro s hs y
      have hh := (hpde s hs y).add ((hEd s).mul_const (1+y^2))
      rw [ParabolicBounded_quadratic_add_second (hdx s hs) (hdxx s hs),ParabolicBounded_quadratic_add_deriv (hdx s hs)]
      convert hh using 1
      first | rfl | ring
    · intro _ _ _; norm_num
    · exact hM
    · intro s hs y
      exact add_nonneg (hF s hs y) (mul_nonneg (hEpos s) (hforce s hs y))
    · intro y
      exact add_nonneg (hinit y) (mul_nonneg (hEpos 0) (by positivity))
    · intro δ hδ
      obtain ⟨A,hA⟩ := ParabolicBounded_quadratic_barrier_tail hL hv hK hε
      exact ⟨A,fun s hs y hy => (neg_nonpos.mpr hδ.le).trans (hA s hs y hy)⟩
  intro t ht x
  by_contra hh
  have hn : v t x < 0 := lt_of_not_ge hh
  let ε := -v t x/(2*(Real.exp (K*t)*(1+x^2)))
  have hp : 0 < Real.exp (K*t)*(1+x^2) := mul_pos (Real.exp_pos _) (by positivity)
  have hε : 0 < ε := div_pos (neg_pos.mpr hn) (mul_pos (by norm_num) hp)
  have hb := barrier ε hε t ht x
  have he : ε*Real.exp (K*t)*(1+x^2) = -v t x/2 := by
    dsimp only [ε]
    field_simp
  nlinarith

 

theorem parabolic_nonneg_bounded_halfline {v b c F : ℝ → ℝ → ℝ} {R M B L : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Icc 0 R ×ˢ Ici 0))
    (hdx : ∀ t ∈ Ioc 0 R, Differentiable ℝ (v t))
    (hdxx : ∀ t ∈ Ioc 0 R, Differentiable ℝ (deriv (v t)))
    (hpde : ∀ t ∈ Ioc 0 R, ∀ x,
      HasDerivAt (fun s => v s x)
        ((1/2:ℝ)*deriv (deriv (v t)) x+b t x*deriv (v t) x+c t x*v t x+F t x) t)
    (hb : ∀ t ∈ Ioc 0 R, ∀ x, |b t x| ≤ B)
    (hM : ∀ t ∈ Ioc 0 R, ∀ x, c t x ≤ M)
    (hF : ∀ t ∈ Ioc 0 R, ∀ x, 0 ≤ F t x)
    (hL : 0 ≤ L) (hv : ∀ t ∈ Icc 0 R, ∀ x, |v t x| ≤ L)
    (hinit : ∀ x, 0 ≤ x → 0 ≤ v 0 x)
    (hleft : ∀ t ∈ Icc 0 R, 0 ≤ v t 0) :
    ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ x → 0 ≤ v t x := by
  let K := max (M+1+B) 0
  have hK : 0 ≤ K := le_max_right _ _
  have barrier (ε : ℝ) (hε : 0 < ε) :
      ∀ t ∈ Icc 0 R, ∀ x, 0 ≤ x → 0 ≤ v t x+ε*Real.exp (K*t)*(1+x^2) := by
    let E : ℝ → ℝ := fun s => ε*Real.exp (K*s)
    have hEd (s : ℝ) : HasDerivAt E (K*E s) s := by
      have hh := (((hasDerivAt_id s).const_mul K).exp).const_mul ε
      convert hh using 1 <;> first | rfl | (dsimp only [E,id]; ring)
    have hEc : Continuous E := continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hEpos (s : ℝ) : 0 ≤ E s := mul_nonneg hε.le (Real.exp_nonneg _)
    have hforce (s : ℝ) (hs : s ∈ Ioc 0 R) (y : ℝ) :
        0 ≤ K*(1+y^2)-(1+2*b s y*y+c s y*(1+y^2)) := by
      have hh := ParabolicBounded_quadratic_barrier_forcing (x := y) (hb s hs y) (hM s hs y)
      have hk := mul_le_mul_of_nonneg_right (le_max_left (M+1+B) 0) (show 0 ≤ 1+y^2 by positivity)
      linarith
    apply parabolic_nonneg_halfline (d := fun _ _ => 1/2) (b := b) (c := c)
      (F := fun s y => F s y+E s*(K*(1+y^2)-(1+2*b s y*y+c s y*(1+y^2)))) (M := M)
    · exact hc.add ((hEc.comp continuous_fst).mul (continuous_const.add (continuous_snd.pow 2))).continuousOn
    · intro s hs y _
      have hh := (hpde s hs y).add ((hEd s).mul_const (1+y^2))
      rw [ParabolicBounded_quadratic_add_second (hdx s hs) (hdxx s hs),ParabolicBounded_quadratic_add_deriv (hdx s hs)]
      convert hh using 1
      first | rfl | ring
    · intro _ _ _ _; norm_num
    · exact fun s hs y _ => hM s hs y
    · intro s hs y _
      exact add_nonneg (hF s hs y) (mul_nonneg (hEpos s) (hforce s hs y))
    · intro y hy
      exact add_nonneg (hinit y hy) (mul_nonneg (hEpos 0) (by positivity))
    · intro s hs
      exact add_nonneg (hleft s hs) (mul_nonneg (hEpos s) (by positivity))
    · intro δ hδ
      obtain ⟨A,hA⟩ := ParabolicBounded_quadratic_barrier_tail hL hv hK hε
      exact ⟨A,fun s hs y hy => (neg_nonpos.mpr hδ.le).trans (hA s hs y (hy.trans (le_abs_self y)))⟩
  intro t ht x hx
  by_contra hh
  have hn : v t x < 0 := lt_of_not_ge hh
  let ε := -v t x/(2*(Real.exp (K*t)*(1+x^2)))
  have hp : 0 < Real.exp (K*t)*(1+x^2) := mul_pos (Real.exp_pos _) (by positivity)
  have hε : 0 < ε := div_pos (neg_pos.mpr hn) (mul_pos (by norm_num) hp)
  have hb := barrier ε hε t ht x hx
  have he : ε*Real.exp (K*t)*(1+x^2) = -v t x/2 := by
    dsimp only [ε]
    field_simp
  nlinarith

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

section
variable (J : HeatJet 0) (hG : ∀ k i, BddSmooth k (J.G i))
  (hH : ∀ k i, BddSmooth k (J.H i)) {m : ℝ} (hm : 0 < m)
include hG hH hm

omit hG hH in
private theorem TransformedHeatCone_initial_realJet_two (x : ℝ) :
    realSpatialJet (J.scalarClockPlane m) 2 (0,x) = J.H 0 (fun _ => x) := by
  change J.scalarClockJet m 2 0 (fun _ => x) = _
  rw [J.scalarClockJet_two hm]
  simp only [HeatJet.evolve,clockGradient,clockTest_zero]
  ring

omit hG hH in
private theorem TransformedHeatCone_initial_realJet_three (x : ℝ) :
    realSpatialJet (J.scalarClockPlane m) 3 (0,x) =
      deriv (fun y => J.H 0 (fun _ => y)) x := by
  change deriv (fun y => realSpatialJet (J.scalarClockPlane m) 2 (0,y)) x = _
  simp_rw [TransformedHeatCone_initial_realJet_two J hm]

 

theorem HeatJet.scalarClockPlane_concave (hneg : ∀ x, J.H 0 (fun _ => x) ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    realSpatialJet (J.scalarClockPlane m) 2 (t,x) ≤ 0 := by
  let u := J.scalarClockPlane m
  let j := realSpatialJet u
  have hr := J.scalarClockPlane_spatialRegular hG hm
  have hd (k : ℕ) (s y : ℝ) := realSpatialJet_hasDerivAt hr k s y
  have hdif := J.scalarClockPlane_contDiffOn hG hH hm
  have hpde (s y : ℝ) (hs : 0 < s) := J.scalarClockPlane_timePDE hG hH hm hs y
  obtain ⟨B,hB,hb⟩ := J.scalarClockPlane_positiveJets_uniformBounded hG hm 0
  obtain ⟨L,hL,hl⟩ := J.scalarClockPlane_positiveJets_uniformBounded hG hm 1
  have hvx (s y : ℝ) : deriv (fun z => -j 2 (s,z)) y = -j 3 (s,y) := (hd 2 s y).neg.deriv
  have hvxx (s y : ℝ) : deriv (deriv (fun z => -j 2 (s,z))) y = -j 4 (s,y) := by
    rw [show deriv (fun z => -j 2 (s,z)) = _ from funext (hvx s)]
    exact (hd 3 s y).neg.deriv
  have hh := parabolic_nonneg_bounded_real
    (v := fun s y => -j 2 (s,y)) (b := fun s y => m*j 1 (s,y))
    (c := fun s y => m*j 2 (s,y)) (F := fun _ _ => 0) (R := t)
    (M := m*L) (B := m*B) (L := L)
    (realSpatialJet_continuous hr 2).neg.continuousOn
    (fun s _ y => (hd 2 s y).neg.differentiableAt)
    (fun s _ => by
      rw [show deriv (fun z => -j 2 (s,z)) = _ from funext (hvx s)]
      exact fun y => (hd 3 s y).neg.differentiableAt)
    (by
      intro s hs y
      rw [hvxx,hvx]
      have hh := (realJet_two_time hdif hpde (x := y) hs.1).neg
      convert hh using 1
      first | rfl | (dsimp only [j,u]; ring))
    (by
      intro s _ y
      rw [abs_mul,abs_of_pos hm]
      exact mul_le_mul_of_nonneg_left (hb (s,y)) hm.le)
    (fun s _ y => mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hl (s,y))) hm.le)
    (fun _ _ _ => le_rfl) hL (by intro s _ y; simpa only [abs_neg] using hl (s,y))
    (fun y => neg_nonneg.mpr (by
      change realSpatialJet (J.scalarClockPlane m) 2 (0,y) ≤ 0
      rw [TransformedHeatCone_initial_realJet_two J hm]
      exact hneg y)) t ⟨ht,le_rfl⟩ x
  exact neg_nonneg.mp hh

 

theorem HeatJet.scalarClockPlane_third_nonneg (he : ∀ x, J.F (-x) = J.F x)
    (hthird : ∀ x, 0 ≤ x → 0 ≤ deriv (fun y => J.H 0 (fun _ => y)) x)
    {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ realSpatialJet (J.scalarClockPlane m) 3 (t,x) := by
  let u := J.scalarClockPlane m
  let j := realSpatialJet u
  have hr := J.scalarClockPlane_spatialRegular hG hm
  have hd (k : ℕ) (s y : ℝ) := realSpatialJet_hasDerivAt hr k s y
  have hdif := J.scalarClockPlane_contDiffOn hG hH hm
  have hpde (s y : ℝ) (hs : 0 < s) := J.scalarClockPlane_timePDE hG hH hm hs y
  obtain ⟨B,hB,hb⟩ := J.scalarClockPlane_positiveJets_uniformBounded hG hm 0
  obtain ⟨C,hC,hc⟩ := J.scalarClockPlane_positiveJets_uniformBounded hG hm 1
  obtain ⟨L,hL,hl⟩ := J.scalarClockPlane_positiveJets_uniformBounded hG hm 2
  have hvx (s y : ℝ) : deriv (fun z => j 3 (s,z)) y = j 4 (s,y) := (hd 3 s y).deriv
  have hvxx (s y : ℝ) : deriv (deriv (fun z => j 3 (s,z))) y = j 5 (s,y) := by
    rw [show deriv (fun z => j 3 (s,z)) = _ from funext (hvx s)]
    exact (hd 4 s y).deriv
  apply parabolic_nonneg_bounded_halfline
    (v := fun s y => j 3 (s,y)) (b := fun s y => m*j 1 (s,y))
    (c := fun s y => 3*m*j 2 (s,y)) (F := fun _ _ => 0) (R := t)
    (M := 3*m*C) (B := m*B) (L := L)
    (realSpatialJet_continuous hr 3).continuousOn
    (fun s _ y => (hd 3 s y).differentiableAt)
    (fun s _ => by
      rw [show deriv (fun z => j 3 (s,z)) = _ from funext (hvx s)]
      exact fun y => (hd 4 s y).differentiableAt)
    (by
      intro s hs y
      rw [hvxx,hvx]
      have hh := realJet_three_time hdif hpde (x := y) hs.1
      convert hh using 1 ; first | rfl | (dsimp only [j,u]; ring))
    (by
      intro s _ y
      rw [abs_mul,abs_of_pos hm]
      exact mul_le_mul_of_nonneg_left (hb (s,y)) hm.le)
    (fun s _ y => mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hc (s,y))) (by positivity))
    (fun _ _ _ => le_rfl) hL (fun s _ y => hl (s,y))
    (fun y hy => by
      change 0 ≤ realSpatialJet (J.scalarClockPlane m) 3 (0,y)
      rw [TransformedHeatCone_initial_realJet_three J hm]
      exact hthird y hy)
    (fun s _ => by
      change 0 ≤ J.scalarClockJet m 3 s 0
      rw [J.scalarClockJet_odd_zero hG he hm]) t ⟨ht,le_rfl⟩ x hx

end
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

namespace ResidualJet

def Cone (J : ResidualJet) : Prop :=
  (∀ x, J.jet 0 (-x) = J.jet 0 x) ∧
  (∀ x, J.jet 2 x ≤ 0) ∧ (∀ x, 0 ≤ x → 0 ≤ J.jet 3 x)

theorem zero_cone : zero.Cone := ⟨fun _ => rfl,fun _ => le_rfl,fun _ _ => le_rfl⟩

theorem Cone.add {J K : ResidualJet} (hJ : J.Cone) (hK : K.Cone) : (J.add K).Cone := by
  refine ⟨fun x => ?_,fun x => add_nonpos (hJ.2.1 x) (hK.2.1 x),
    fun x hx => add_nonneg (hJ.2.2 x hx) (hK.2.2 x hx)⟩
  change J.jet 0 (-x)+K.jet 0 (-x) = J.jet 0 x+K.jet 0 x
  rw [hJ.1,hK.1]

theorem Cone.scale {J : ResidualJet} (hJ : J.Cone) {c : ℝ} (hc : 0 ≤ c) : (J.scale c).Cone := by
  refine ⟨fun x => ?_,fun x => mul_nonpos_of_nonneg_of_nonpos hc (hJ.2.1 x),
    fun x hx => mul_nonneg hc (hJ.2.2 x hx)⟩
  change c*J.jet 0 (-x) = c*J.jet 0 x
  rw [hJ.1]

theorem Cone.heat {J : ResidualJet} (hJ : J.Cone) {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) :
    (J.heat t a).Cone := by
  have hg (k : ℕ) (i : Fin 1) : BddSmooth k (J.heatJet.G i) := J.bddSmooth k 0
  have hh (k : ℕ) (i : Fin 1) : BddSmooth k (J.heatJet.H i) := J.bddSmooth k 1
  have he (x : Fin 1 → ℝ) : J.heatJet.F (-x) = J.heatJet.F x := hJ.1 (x 0)
  refine ⟨?_,?_,?_⟩
  · intro x
    change a^0*clockContinuation 1 J.heatJet.F t (fun _ => a*(-x)) =
      a^0*clockContinuation 1 J.heatJet.F t (fun _ => a*x)
    have hp := clockContinuation_even he 1 t (fun _ : Fin 1 => a*x)
    change clockContinuation 1 J.heatJet.F t (fun _ => -(a*x)) = _ at hp
    simpa only [mul_neg] using congrArg (fun z => a^0*z) hp
  · intro x
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a)
      (J.heatJet.scalarClockPlane_concave hg hh (by norm_num) hJ.2.1 ht (a*x))
  · intro x hx
    apply mul_nonneg (pow_nonneg ha _)
    apply J.heatJet.scalarClockPlane_third_nonneg hg hh (by norm_num) he _ ht (mul_nonneg ha hx)
    intro y hy
    change 0 ≤ deriv (J.jet 2) y
    rw [(J.derivative 2 y).deriv]
    exact hJ.2.2 y hy

 
noncomputable def scalarPotential (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) : ResidualJet where
  jet := scalarProfileJet α l t
  derivative := scalarProfileJet_hasDerivAt α hα l t
  bounded n := ⟨(ReplicaTree.attachmentCount 1 n:ℝ),by positivity,
    scalarProfileJet_bound α hα l t n⟩

 

theorem scalarPotential_neg_cone (α : NonnegativeMassProfile) (hα : ∀ s, α.mass s ≤ 1)
    (l : ℝ) (t : ℝ≥0) {c : ℝ} (hc : 0 ≤ c) :
    ((scalarPotential α hα l t).scale (-c)).Cone := by
  refine ⟨?_,?_,?_⟩
  · intro x
    change -c*scalarProfileJet α l t 0 (-x) = -c*scalarProfileJet α l t 0 x
    rw [scalarProfileJet_parity α hα l t]
    simp only [pow_zero,one_mul]
  · intro x
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc)
      (scalarProfileJet_curvature_pos α hα l t x).le
  · intro x hx
    apply mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hc)
    exact (scalarProfileJet_third_barrier α hα l t hx).trans
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (third_nonpos hx))

end ResidualJet
end SKFluctuations.Hierarchy

end

end OAI
