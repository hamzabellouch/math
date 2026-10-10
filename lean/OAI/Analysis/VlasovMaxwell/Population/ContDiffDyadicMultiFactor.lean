import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ConeRadius
import OAI.Analysis.VlasovMaxwell.Regularity.PhysicalCutoffCoordinates

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiffAt_dyadicMultiFactor_curve {ι : Type*} [Fintype ι] {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) {g : ι → ℝ → ℝ} {t : ℝ}
    (hg : ∀ i,ContDiffAt ℝ k (g i) t) (n : ι→ℕ) :
    ContDiffAt ℝ k (fun r=>dyadicMultiFactor n (fun i=>g i r)) t := by
  classical
  exact contDiffAt_prod (fun i _ => ((contDiff_dyadicFactor (n i)).of_le hk).contDiffAt.comp t (hg i))

lemma contDiffAt_selectedDyadicCutoff_curve {ι : Type*} [Fintype ι] {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) {g : ι → ℝ → ℝ} {t : ℝ}
    (hg : ∀ i,ContDiffAt ℝ k (g i) t) (hp : ∀ i,0<g i t) (S : Set (ι→ℕ)) :
    ContDiffAt ℝ k (fun r=>selectedDyadicCutoff S (fun i=>g i r)) t := by
  classical
  obtain ⟨N,_hN,he⟩ := selectedDyadicCutoff_curve_eventually (fun i=>(hg i).continuousAt) hp S
  exact (ContDiffAt.sum (s:=selectedDyadicBox N S)
    (fun n _=>contDiffAt_dyadicMultiFactor_curve hk hg n)).congr_of_eventuallyEq he

lemma contDiffOn_selectedDyadicCutoff_curve {ι : Type*} [Fintype ι] {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) {g : ι → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ∀ i,ContDiffOn ℝ k (g i) U) (hp : ∀ t∈U,∀ i,0<g i t) (S : Set (ι→ℕ)) :
    ContDiffOn ℝ k (fun r=>selectedDyadicCutoff S (fun i=>g i r)) U := by
  intro t ht
  exact (contDiffAt_selectedDyadicCutoff_curve hk
    (fun i=>(hg i).contDiffAt (hU.mem_nhds ht)) (hp t ht) S).contDiffWithinAt

lemma inverseCoordinate_log_deriv {d : ℝ→ℝ} {d' t : ℝ}
    (hd : HasDerivAt d d' t) (hp : 0<d t) :
    deriv (fun s=>1/d s) t / (1/d t) = -d'/d t := by
  have hh := ((hasDerivAt_const t (1:ℝ)).div hd hp.ne').deriv
  change deriv ((fun _ : ℝ => (1:ℝ))/d) t / (1/d t) = -d'/d t
  rw [hh]
  field_simp
  ring

lemma source_cutoff_logarithmic_rates {V : ℝ→Vec} {E B n : Vec} {t : ℝ}
    (hV : HasDerivAt V (E+cross (velocity (V t)) B) t) (hn : ‖n‖=1) :
    let θ := Real.sqrt ((1-dot n (velocity (V t)))/2)
    |deriv (fun s=>1/q (V s)) t / (1/q (V t))| +
      |deriv (fun s=>Real.sqrt ((1-dot n (velocity (V s)))/2)) t / θ| ≤
      (3/q (V t))*(goodField E B n/θ+θ*‖B‖) := by
  let d := 1-dot n (velocity (V t))
  let θ := Real.sqrt (d/2)
  let U := fderiv ℝ velocity (V t) (E+cross (velocity (V t)) B)
  have hdpos : 0<d := cone_denom_pos (V t) n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=d/2 := Real.sq_sqrt (by positivity)
  have hθ1 : θ≤1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num,by nlinarith [real_deficit_le_two hn (V t)]⟩
  have htwo : Real.sqrt (2*d)=2*θ := by
    have hs := Real.sq_sqrt (show 0≤2*d by positivity)
    nlinarith [Real.sqrt_nonneg (2*d)]
  have hu : HasDerivAt (fun s=>velocity (V s)) U t :=
    ((contDiff_velocity (k:=1)).differentiable one_ne_zero (V t)).hasFDerivAt.comp_hasDerivAt t hV
  have hd : HasDerivAt (fun s=>1-dot n (velocity (V s))) (-dot n U) t := by
    have hh := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot (hasDerivAt_const t n) hu)
    convert hh using 1
    try rfl
    simp only [dot_zero_left_rvm,add_zero,zero_sub]
  have hq := inverseCoordinate_log_deriv (hasDerivAt_lorentz_energy hV) (q_pos (V t))
  have ha := angularCoordinate_log_deriv hd hdpos
  change |deriv (fun s=>1/q (V s)) t / (1/q (V t))|+
      |deriv (fun s=>Real.sqrt ((1-dot n (velocity (V s)))/2)) t/θ| ≤ _
  rw [hq]
  change |-dot (velocity (V t)) E/q (V t)|+
    |deriv (fun s=>Real.sqrt ((1-dot n (velocity (V s)))/2)) t/Real.sqrt ((1-dot n (velocity (V t)))/2)| ≤ _
  rw [ha,abs_div,abs_neg,abs_of_pos (q_pos (V t)),abs_div,abs_neg]
  change |dot (velocity (V t)) E|/q (V t)+|dot n U|/|2*d| ≤ _
  rw [abs_of_pos (by positivity : 0<2*d)]
  have he : |dot (velocity (V t)) E|≤goodField E B n+2*θ*‖B‖ := by
    simpa only [← htwo] using source_energy_rate_bound (V t) E B n hn
  have hu' : |dot n U|≤(q (V t))⁻¹*(2*θ)*(goodField E B n+d*‖B‖) := by
    simpa only [U,← htwo] using lorentz_source_normal_acceleration_bound (V t) E B n hn
  have hG : 0≤goodField E B n := by unfold goodField; positivity
  calc
    _ ≤ (goodField E B n+2*θ*‖B‖)/q (V t)+
        ((q (V t))⁻¹*(2*θ)*(goodField E B n+d*‖B‖))/(2*d) :=
      add_le_add (div_le_div_of_nonneg_right he (q_pos _).le)
        (div_le_div_of_nonneg_right hu' (by positivity))
    _ = (q (V t))⁻¹*(goodField E B n+goodField E B n/(2*θ)+3*θ*‖B‖) := by
      have hdθ : d=2*θ^2 := by linarith
      rw [hdθ]
      field_simp
      ring
    _ ≤ (q (V t))⁻¹*(3*(goodField E B n/θ+θ*‖B‖)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (q_pos _).le)
      apply (mul_le_mul_iff_right₀ hθ).mp
      field_simp
      nlinarith [mul_le_mul_of_nonneg_left hθ1 hG]
    _ = _ := by ring

lemma coneMotion_tangent {a u n : Vec} (hn : ‖n‖=1) (hD : 1-dot n a≠0) :
    dot n (coneMotion a u n)=0 := by
  simp only [coneMotion,dot_add_right,dot_sub_right,dot_smul_right,dot_self,hn,one_pow]
  field_simp
  ring

lemma geometric_cutoff_logarithmic_rates {v w n : Vec} {r : ℝ}
    (hn : ‖n‖=1) (hr : 0<r)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity w)) :
    let d := 1-dot n (velocity v)
    let D := 1-dot n (velocity w)
    let N := r⁻¹ • coneMotion (velocity w) (velocity v) n
    |(d/D-1)/r| + |dot N (velocity v)/(2*d)| +
      |dot N (velocity w)/(2*D)| ≤ 5/r := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity w)
  let θ := Real.sqrt (d/2)
  let φ := Real.sqrt (D/2)
  let N := r⁻¹ • coneMotion (velocity w) (velocity v) n
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos w n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=d/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=D/2 := Real.sq_sqrt (by positivity)
  have hdθ : d=2*θ^2 := by linarith
  have hDφ : D=2*φ^2 := by linarith
  have hθφ : θ≤φ := Real.sqrt_le_sqrt (by dsimp [d,D]; linarith)
  have hun : ‖velocity v-n‖≤2*θ := by
    apply (velocity_normal_distance_bound v n hn).trans_eq
    change Real.sqrt (2*d)=2*θ
    have hh := Real.sq_sqrt (show 0≤2*d by positivity)
    nlinarith [Real.sqrt_nonneg (2*d)]
  have han : ‖velocity w-n‖≤2*φ := by
    apply (velocity_normal_distance_bound w n hn).trans_eq
    change Real.sqrt (2*D)=2*φ
    have hh := Real.sq_sqrt (show 0≤2*D by positivity)
    nlinarith [Real.sqrt_nonneg (2*D)]
  have hfac : (d/D)*(2*φ)≤2*θ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hD).mpr
    rw [hdθ,hDφ]
    nlinarith [mul_nonneg (show 0≤4*θ*φ by positivity) (sub_nonneg.mpr hθφ)]
  have hmotion : ‖coneMotion (velocity w) (velocity v) n‖≤4*θ := by
    have he : coneMotion (velocity w) (velocity v) n =
        (d/D) • (velocity w-n)-(velocity v-n) := by unfold coneMotion; dsimp [d,D]; module
    rw [he]
    calc
      _ ≤ ‖(d/D) • (velocity w-n)‖+‖velocity v-n‖ := norm_sub_le _ _
      _ ≤ (d/D)*(2*φ)+2*θ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hd hD)]
        exact add_le_add (mul_le_mul_of_nonneg_left han (div_nonneg hd.le hD.le)) hun
      _ ≤ _ := by linarith
  have hnorm : ‖N‖≤4*θ/r := by
    dsimp only [N]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left hmotion (inv_nonneg.mpr hr.le)).trans_eq (by ring)
  have htan : dot N n=0 := by
    dsimp only [N]
    rw [dot_smul_left,dot_comm _ n,coneMotion_tangent hn hD.ne',mul_zero]
  have hsDot : |dot N (velocity v)|≤(4*θ/r)*(2*θ) := by
    have he : dot N (velocity v)=dot N (velocity v-n) := by rw [dot_sub_right,htan,sub_zero]
    rw [he]
    exact (abs_dot_le _ _).trans (mul_le_mul hnorm hun (norm_nonneg _) (by positivity))
  have hrDot : |dot N (velocity w)|≤(4*θ/r)*(2*φ) := by
    have he : dot N (velocity w)=dot N (velocity w-n) := by rw [dot_sub_right,htan,sub_zero]
    rw [he]
    exact (abs_dot_le _ _).trans (mul_le_mul hnorm han (norm_nonneg _) (by positivity))
  have hsRate : |dot N (velocity v)/(2*d)|≤2/r := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*d)]
    apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
    apply hsDot.trans_eq
    rw [hdθ]
    ring
  have hrRate : |dot N (velocity w)/(2*D)|≤2/r := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*D)]
    apply (div_le_iff₀ (by positivity : 0<2*D)).mpr
    apply hrDot.trans
    rw [hDφ]
    have hh := mul_le_mul_of_nonneg_right hθφ (show 0≤8*φ/r by positivity)
    convert hh using 1 <;> ring
  have hrad : |(d/D-1)/r|≤1/r := by
    rw [abs_div,abs_of_pos hr]
    apply div_le_div_of_nonneg_right _ hr.le
    apply abs_le.mpr
    constructor
    · linarith [div_nonneg hd.le hD.le]
    · have hh : d/D≤1 := (div_le_one hD).mpr hsmall
      linarith
  change |(d/D-1)/r|+|dot N (velocity v)/(2*d)|+|dot N (velocity w)/(2*D)|≤5/r
  exact (add_le_add (add_le_add hrad hsRate) hrRate).trans_eq (by ring)

end RVM

end

end OAI
