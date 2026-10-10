import OAI.Geometry.HarmonicGrowth.PulseSystem
import OAI.Geometry.HarmonicGrowth.AngularStream

namespace OAI

noncomputable section


namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open scoped InnerProductSpace

lemma weighted_slope_gap_deriv {A S : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hb : Continuous b) {C t : ℝ} (hS : (S t).IsSymmetric)
    (hD : HasDerivAt S (A t-b t • S t-S t*S t) t) (v : E) :
    HasDerivAt (fun s => integratingWeight (fun s => 2*C+b s) s * ⟪v,C • v-S s v⟫_ℝ)
      (integratingWeight (fun s => 2*C+b s) t *
        (‖C • v-S t v‖^2+(C^2+b t*C)*‖v‖^2-⟪v,A t v⟫_ℝ)) t := by
  have hv : HasDerivAt (fun s => C • v-S s v)
      (-(A t v-b t • S t v-S t (S t v))) t := by
    simpa only [map_zero,add_zero,sub_apply,smul_apply,mul_apply_eq_comp,zero_sub] using
      (hasDerivAt_const t (C • v)).fun_sub (hD.clm_apply (hasDerivAt_const t v))
  have hd := (integratingWeight_deriv (b := fun s => 2*C+b s) (continuous_const.add hb) t).fun_mul
    ((hasDerivAt_const t v).inner ℝ hv)
  have hs : ⟪v,S t (S t v)⟫_ℝ = ‖S t v‖^2 := by
    calc
      ⟪v,S t (S t v)⟫_ℝ = ⟪S t v,S t v⟫_ℝ := (hS v (S t v)).symm
      _ = ‖S t v‖^2 := real_inner_self_eq_norm_sq _
  have hn : ‖C • v-S t v‖^2 = C^2*‖v‖^2-2*C*⟪v,S t v⟫_ℝ+‖S t v‖^2 := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
      real_inner_smul_left]
    ring
  convert hd using 1; first | rfl |
    (simp only [inner_zero_left,inner_neg_right,inner_sub_right,
      inner_smul_right,real_inner_self_eq_norm_sq,hs,hn]; ring)

lemma riccati_quadratic_upper {A S : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hb : Continuous b) {C l MA Mb : ℝ} (hC : 0 ≤ C) (hlC : l ≤ C)
    (hbnd : ∀ t, |b t| ≤ Mb) (hCbound : MA ≤ C^2-Mb*C)
    (hAbnd : ∀ t v, ⟪v,A t v⟫_ℝ ≤ MA*‖v‖^2)
    (hS : ∀ t, 0 ≤ t → (S t).IsSymmetric)
    (hD : ∀ t, 0 ≤ t → HasDerivAt S (A t-b t • S t-S t*S t) t)
    (hi : S 0 = l • (1 : E →L[ℝ] E)) {t : ℝ} (ht : 0 ≤ t) (v : E) :
    ⟪v,S t v⟫_ℝ ≤ C*‖v‖^2 := by
  let F (s : ℝ) := integratingWeight (fun s => 2*C+b s) s * ⟪v,C • v-S s v⟫_ℝ
  have hnonneg (s : ℝ) : 0 ≤ ‖C • v-S s v‖^2+(C^2+b s*C)*‖v‖^2-⟪v,A s v⟫_ℝ := by
    have hb0 : -Mb ≤ b s := (abs_le.1 (hbnd s)).1
    have hcoef : MA ≤ C^2+b s*C := by
      nlinarith [mul_le_mul_of_nonneg_right hb0 hC]
    have := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖v‖)
    have := hAbnd s v
    nlinarith [sq_nonneg ‖C • v-S s v‖]
  have hmono : MonotoneOn F (Set.Ici (0:ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro s hs
      exact (weighted_slope_gap_deriv hb (hS s hs) (hD s hs) v).continuousAt.continuousWithinAt
    · intro s hs
      exact (weighted_slope_gap_deriv hb (hS s (interior_subset hs))
        (hD s (interior_subset hs)) v).hasDerivWithinAt
    · intro s _
      exact mul_nonneg (integratingWeight_pos _ _).le (hnonneg s)
  have hzero : 0 ≤ F 0 := by
    simp only [F,hi,integratingWeight_initial,one_mul,smul_apply,one_apply_eq_self,
      inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖v‖]
  have hpos : 0 ≤ F t := hzero.trans (hmono (by simp : (0:ℝ) ∈ Set.Ici (0:ℝ)) ht ht)
  have hiq : 0 ≤ ⟪v,C • v-S t v⟫_ℝ :=
    (mul_nonneg_iff_of_pos_left (integratingWeight_pos _ _)).1 hpos
  simpa only [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,sub_nonneg] using hiq

lemma symmetric_norm_bound {S : E →L[ℝ] E} {C : ℝ} (hC : 0 ≤ C)
    (hs : S.IsSymmetric) (hpos : ∀ v, 0 ≤ ⟪v,S v⟫_ℝ)
    (hb : ∀ v, ⟪v,S v⟫_ℝ ≤ C*‖v‖^2) : ‖S‖ ≤ C := by
  rw [S.norm_eq_iSup_rayleighQuotient hs]
  apply ciSup_le
  intro v
  by_cases hv : v = 0
  · simp [hv,hC]
  · have hn : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.2 hv)
    have hp := hpos v
    have hupper := hb v
    change |⟪S v,v⟫_ℝ / ‖v‖^2| ≤ C
    rw [real_inner_comm v (S v),abs_of_nonneg (div_nonneg hp hn.le)]
    exact (div_le_iff₀ hn).2 hupper

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The history-independent Riccati bound is proved for the actual center-regular
PB solution. It is not an assumption on an arbitrary incoming solution. -/
theorem actual_slope_norm_bound {A : ℝ → E →L[ℝ] E} {p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p) {MA Mp : ℝ}
    (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,‖A t‖ ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAs : ∀ t x y,inner ℝ (A t x) y=inner ℝ x (A t y))
    (hAp : ∀ t x,0 ≤ inner ℝ x (A t x))
    {l B : ℝ} (hl : 0 < l) (hAc : ∀ t ≤ 0,∀ x,A t x=(l*(l+B)) • x)
    (hpc : ∀ t ≤ 0,p t=B) {t : ℝ} (ht : 0 ≤ t) :
    ‖slope A p l t‖ ≤ l+MA+Mp+1 := by
  let C := l+MA+Mp+1
  have hC : 0 ≤ C := by dsimp [C];linarith
  have hCbound : MA ≤ C^2-Mp*C := by
    have hc1 : 1 ≤ C-Mp := by dsimp [C];linarith
    have hc2 : MA ≤ C := by dsimp [C];linarith
    have hm := mul_le_mul_of_nonneg_left hc1 hC
    nlinarith
  have hu (s : ℝ) := actual_value_unit_all_time hA hp hMA hMp hAn hpn hAp hl hAc hpc s
  have hsym (s : ℝ) : (slope A p l s).IsSymmetric :=
    slope_symmetric hA hp hMA hMp hAn hpn hAs l s (hu s)
  apply symmetric_norm_bound hC (hsym t)
  · exact slope_nonnegative hA hp hMA hMp hAn hpn hAp hl ht (hu t)
  · apply riccati_quadratic_upper hp hC (show l ≤ C by dsimp [C];linarith)
      hpn hCbound
    · intro s x
      calc
        inner ℝ x (A s x) ≤ ‖x‖*‖A s x‖ := real_inner_le_norm _ _
        _ ≤ ‖x‖*(MA*‖x‖) := mul_le_mul_of_nonneg_left
          (((A s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hAn s) (norm_nonneg x)))
          (norm_nonneg x)
        _ = MA*‖x‖^2 := by ring
    · intro s _;exact hsym s
    · intro s _;exact slope_deriv hA hp hMA hMp hAn hpn l s (hu s)
    · exact slope_initial A p l
    · exact ht

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

/-- A single late threshold resets EVERY positive symmetric bounded history.
Only the actual preceding round interval is used. -/
theorem uniform_round_reset (basis : OrthonormalBasis ι ℝ E)
    {α p : ℝ → ℝ} (hp : Continuous p) {β p₀ γ θ B l B₀ MA Mp : ℝ}
    (hαlim : Tendsto α atTop (𝓝 β)) (hplim : Tendsto p atTop (𝓝 p₀))
    (hγ : 0 < γ) (hθ : 0 < θ) (hpl : ∀ᶠ t in atTop,γ ≤ p t)
    (hroot : β*B-p₀*θ-θ^2=0) (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hpn : ∀ t,|p t| ≤ Mp) (hl : 0 < l) (hpc : ∀ t ≤ 0,p t=B₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ,∀ j,J ≤ j → ∀ A : ℝ → E →L[ℝ] E,
      Continuous A → (∀ t,‖A t‖ ≤ MA) →
      (∀ t x y,inner ℝ (A t x) y=inner ℝ x (A t y)) →
      (∀ t x,0 ≤ inner ℝ x (A t x)) →
      (∀ t ≤ 0,∀ x,A t x=(l*(l+B₀)) • x) →
      (∀ t ∈ Icc (time j+3*pulse j+dwell j) (time (j+1)),
        A t=α t • (B • (1:E →L[ℝ] E))) →
      ‖orthogonalMatrix basis (slope A p l (time (j+1)))-θ • (1:Matrix ι ι ℝ)‖ ≤ ε := by
  let lam := γ+θ
  have hlam : 0 < lam := by dsimp [lam];linarith
  let C := ‖orthogonalMatrix basis‖*(l+MA+Mp+1)+|θ| * ‖(1:Matrix ι ι ℝ)‖
  let M := ε/2*lam
  have hM : 0 < M := mul_pos (by linarith) hlam
  have hroot' : β*B-(p₀*θ+θ^2)=0 := by linarith
  have hf : Tendsto (fun t : ℝ => ‖(α t*B-(p t*θ+θ^2)) • (1:Matrix ι ι ℝ)‖)
      atTop (𝓝 0) := by
    have hh := (((hαlim.mul_const B).sub ((hplim.mul_const θ).add_const (θ^2))).smul_const
      (1:Matrix ι ι ℝ)).norm
    simpa only [hroot',zero_smul,norm_zero] using hh
  obtain ⟨a₀,ha₀⟩ := eventually_atTop.1 ((hf.eventually (gt_mem_nhds hM)).and hpl)
  have he : Tendsto (fun j => C*Real.exp (-lam*pulse j)) atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (pulse_atTop_limit.const_mul_atTop hlam)).const_mul C
    simpa only [Function.comp_apply,neg_mul,mul_zero] using hh
  obtain ⟨J,hJ⟩ := eventually_atTop.1
    ((time_atTop.eventually_ge_atTop a₀).and (he.eventually (gt_mem_nhds (show 0<ε/2 by linarith))))
  refine ⟨J,fun j hj A hA hAn hAs hAp hAc hround => ?_⟩
  let a := time j+3*pulse j+dwell j
  have ha : 0 ≤ a := by dsimp [a];linarith [time_pos j,pulse_pos j,dwell_pos j]
  have hab : a ≤ time (j+1) := by dsimp [a];rw [time_succ];linarith [pulse_pos j]
  have hat (t : ℝ) (ht : t ∈ Icc a (time (j+1))) : a₀ ≤ t := by
    have := (hJ j hj).1
    dsimp [a] at ht
    linarith [ht.1,pulse_pos j,dwell_pos j]
  have hinit : ‖orthogonalMatrix basis (slope A p l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ C := by
    calc
      _ ≤ ‖orthogonalMatrix basis (slope A p l a)‖+‖θ • (1:Matrix ι ι ℝ)‖ := norm_sub_le _ _
      _ ≤ ‖orthogonalMatrix basis‖*(l+MA+Mp+1)+|θ| * ‖(1:Matrix ι ι ℝ)‖ := by
        rw [norm_smul,Real.norm_eq_abs]
        exact add_le_add (((orthogonalMatrix basis).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (actual_slope_norm_bound hA hp hMA hMp hAn hpn hAs hAp hl hAc hpc ha)
            (norm_nonneg _))) le_rfl
      _ = C := rfl
  have hforce (t : ℝ) (ht : t ∈ Icc a (time (j+1))) :
      ‖orthogonalMatrix basis (A t)-(p t*θ+θ^2) • (1:Matrix ι ι ℝ)‖ ≤ M := by
    rw [hround t ht,map_smul,map_smul,orthogonalMatrix_one,smul_smul,← sub_smul]
    exact (ha₀ t (hat t ht)).1.le
  have hh := actual_round_reset basis hA hp hMA hMp hAn hpn hAp hl hAc hpc ha
    hlam hM.le (fun t ht => (ha₀ t (hat t ht)).2) hforce hinit
    (time (j+1)) ⟨hab,le_rfl⟩
  have hlen : time (j+1)-a=pulse j := by dsimp [a];rw [time_succ];ring
  rw [hlen] at hh
  have hdiv : M/lam=ε/2 := by dsimp [M];exact mul_div_cancel_right₀ _ (ne_of_gt hlam)
  change _ ≤ C*Real.exp (-lam*pulse j)+M/lam at hh
  rw [hdiv] at hh
  linarith [(hJ j hj).2]

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace

/-- Primitive radial coefficients and fixed angular operators. All fields are
scalar/asymptotic or pointwise geometric facts; no transmission/reset/growth
conclusion is part of this data. -/
structure HistoryGeometry (S : PulseSystem E ι κ) where
  D₀ : ∀ b,E b →L[ℝ] E b
  D₀nonpos : ∀ b v,inner ℝ v (D₀ b v) ≤ 0
  BD₀ : ∀ b v,-(S.B b*‖v‖^2) ≤ inner ℝ v (D₀ b v)
  D₀symm : ∀ b x y,inner ℝ (D₀ b x) y=inner ℝ x (D₀ b y)
  Dsymm : ∀ b j x y,inner ℝ (S.D b j x) y=inner ℝ x (S.D b j y)
  qstar : ℝ
  qstar_ge : 1 ≤ qstar
  l : ξ → ℝ
  lpos : ∀ b,0 < l b
  B₀ : ℝ
  B_eq : ∀ b,S.B b=l b*(l b+B₀)
  α : ℝ → ℝ
  drift : ℝ → ℝ
  Mp : ℝ
  Mpnonneg : 0 ≤ Mp
  αsmooth : ContDiff ℝ ∞ α
  driftContinuous : Continuous drift
  αbound : ∀ t,|α t| ≤ S.M
  αnonneg : ∀ t,0 ≤ α t
  driftBound : ∀ t,|drift t| ≤ Mp
  αcenter : ∀ t ≤ 0,α t=1
  driftCenter : ∀ t ≤ 0,drift t=B₀
  αlimit : ∀ b,Tendsto α atTop (𝓝 (S.β b))
  driftLimit : Tendsto drift atTop (𝓝 S.p₀)
  driftLower : ∀ᶠ t in atTop,S.γ ≤ drift t

variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)

def HistoryGeometry.coefficient (s : ℕ → Fin n → ℝ) (j0 : ℕ) (b : ξ) (t : ℝ) : E b →L[ℝ] E b :=
  G.α t • angular S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b) (fun i => S.D b (slot i)) s G.qstar j0 t

def HistoryGeometry.bound (b : ξ) : ℝ := S.M *
  (angular_uniform_bound S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b)
    (fun i => S.D b (slot i)) G.qstar_ge).choose

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.bound_nonneg (b : ξ) : 0 ≤ G.bound slot b :=
  mul_nonneg S.hM (angular_uniform_bound S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b)
    (fun i => S.D b (slot i)) G.qstar_ge).choose_spec.1

variable (s : ℕ → Fin n → ℝ) (j0 : ℕ)
  (hpos : ∀ j,j0 ≤ j → ∀ t i,packetStretch (s j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2))

include hpos

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_smooth (b : ξ) : ContDiff ℝ ∞ (G.coefficient slot s j0 b) :=
  G.αsmooth.smul (angular_smooth S.r _ _ _ s G.qstar_ge j0
    (fun j hj t i => by linarith [(hpos j hj t i).1]))

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.coefficient_bound (b : ξ) (t : ℝ) :
    ‖G.coefficient slot s j0 b t‖ ≤ G.bound slot b := by
  rw [HistoryGeometry.coefficient,norm_smul,Real.norm_eq_abs]
  apply mul_le_mul (G.αbound t)
    ((angular_uniform_bound S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b)
      (fun i => S.D b (slot i)) G.qstar_ge).choose_spec.2 s j0 hpos t)
    (norm_nonneg _) S.hM

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.coefficient_nonnegative (b : ξ) (t : ℝ) (x : E b) :
    0 ≤ inner ℝ x (G.coefficient slot s j0 b t x) := by
  simp only [HistoryGeometry.coefficient,smul_apply,inner_smul_right]
  apply mul_nonneg (G.αnonneg t)
  apply angular_nonnegative S.r (S.B b) (G.D₀ b) (fun i => S.D b (slot i)) s G.qstar_ge j0 hpos
  · intro d x;cases d with
    | none => exact G.D₀nonpos b x
    | some i => exact S.hD b (slot i) x
  · intro d x;cases d with
    | none => exact G.BD₀ b x
    | some i => exact S.hBD b (slot i) x

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.coefficient_symmetric (b : ξ) (t : ℝ) (x y : E b) :
    inner ℝ (G.coefficient slot s j0 b t x) y=inner ℝ x (G.coefficient slot s j0 b t y) := by
  simp only [HistoryGeometry.coefficient,smul_apply,real_inner_smul_left,inner_smul_right]
  congr 1
  apply angular_symmetric S.r (S.B b) (G.D₀ b) (fun i => S.D b (slot i)) s G.qstar_ge j0 hpos
  intro d x y;cases d with
  | none => exact G.D₀symm b x y
  | some i => exact G.Dsymm b (slot i) x y

omit hpos [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_center (b : ξ) (t : ℝ) (ht : t ≤ 0) (x : E b) :
    G.coefficient slot s j0 b t x=(G.l b*(G.l b+G.B₀)) • x := by
  rw [HistoryGeometry.coefficient,angular_initial S.r _ _ _ s (ht.trans (time_pos j0).le),
    G.αcenter t ht,one_smul,G.B_eq b]
  rfl

omit hpos [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_round (b : ξ) {j : ℕ} (hj : j0 ≤ j) (hz : s j=0)
    (t : ℝ) (ht : t ∈ Icc (time j) (time j+pulse j)) :
    G.coefficient slot s j0 b t=G.α t • (S.B b • (1:E b →L[ℝ] E b)) := by
  rw [HistoryGeometry.coefficient,angular_zero_pulse S.r _ _ _ s hj hz ht.1 ht.2]

omit hpos [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_rest (b : ξ) (j : ℕ)
    (t : ℝ) (ht : t ∈ Icc (time j+3*pulse j+dwell j) (time (j+1))) :
    G.coefficient slot s j0 b t=G.α t • (S.B b • (1:E b →L[ℝ] E b)) := by
  rw [HistoryGeometry.coefficient,angular_rest S.r _ _ _ s ht.1 ht.2]

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)

omit [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
/-- Uniform reset for the explicit smooth angular stream, including the first
active period and arbitrary prior admissible control choices. -/
theorem HistoryGeometry.uniform_incoming {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ,∀ j0 j,J ≤ j → ∀ s : ℕ → Fin n → ℝ,
      (∀ k,j0 ≤ k → ∀ t i,packetStretch (s k) (pulse k) t i ∈ Icc (1/2:ℝ) (3/2)) →
      ∀ b,‖orthogonalMatrix (S.basis b) (slope (G.coefficient slot s j0 b) G.drift (G.l b) (time j))-
        S.θ b • (1:Matrix (ι b) (ι b) ℝ)‖ ≤ ε := by
  classical
  have hex (b : ξ) := uniform_round_reset (S.basis b) G.driftContinuous (G.αlimit b) G.driftLimit
    S.hγ (S.hθ b) G.driftLower (S.hroot b) (G.bound_nonneg slot b) G.Mpnonneg
    G.driftBound (G.lpos b) G.driftCenter hε
  choose J hJ using hex
  refine ⟨Finset.univ.sup J+1,fun j0 j hj s hpos b => ?_⟩
  have hji : J b ≤ j-1 := by
    have hsup := Finset.le_sup (s:=Finset.univ) (f:=J) (Finset.mem_univ b)
    omega
  have he : j-1+1=j := by omega
  have hh := hJ b (j-1) hji (G.coefficient slot s j0 b)
    (G.coefficient_smooth slot s j0 hpos b).continuous
    (G.coefficient_bound slot s j0 hpos b)
    (G.coefficient_symmetric slot s j0 hpos b)
    (G.coefficient_nonnegative slot s j0 hpos b)
    (G.coefficient_center slot s j0 b)
    (G.coefficient_rest slot s j0 b (j-1))
  simpa only [he] using hh

omit [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.uniform_radial_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : ℕ,∀ j,J ≤ j → ∀ t,time j ≤ t →
      (∀ b,|G.α t-S.β b| ≤ δ) ∧ |G.drift t-S.p₀| ≤ δ ∧ S.γ ≤ G.drift t := by
  have hα : ∀ᶠ t in atTop,∀ b,|G.α t-S.β b| ≤ δ := by
    apply Filter.eventually_all.2
    intro b
    have hh : Tendsto (fun t => |G.α t-S.β b|) atTop (𝓝 0) := by
      simpa only [sub_self,abs_zero] using ((G.αlimit b).sub_const (S.β b)).abs
    exact (hh.eventually (gt_mem_nhds hδ)).mono (fun _ h => h.le)
  have hp : Tendsto (fun t => |G.drift t-S.p₀|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (G.driftLimit.sub_const S.p₀).abs
  obtain ⟨a,ha⟩ := eventually_atTop.1 (hα.and ((hp.eventually (gt_mem_nhds hδ)).and G.driftLower))
  obtain ⟨J,hJ⟩ := eventually_atTop.1 (time_atTop.eventually_ge_atTop a)
  exact ⟨J,fun j hj t ht => ⟨(ha t ((hJ j hj).trans ht)).1,
    (ha t ((hJ j hj).trans ht)).2.1.le,(ha t ((hJ j hj).trans ht)).2.2⟩⟩

omit [Nonempty ξ] [Nonempty κ] [∀ b, Nontrivial (ι b)] in
/-- All scalar and incoming thresholds simultaneously, chosen BEFORE the
start index, entire control stream, and current history. -/
theorem HistoryGeometry.eventual_history_conditions (T₀ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ J : ℕ,∀ j0 j,J ≤ j0 → j0 ≤ j →
      T₀ ≤ pulse j ∧ ρ/4+(pulse j)⁻¹+ρ/4 ≤ ρ ∧
      (∀ t,time j ≤ t → (∀ b,|G.α t-S.β b| ≤ ρ/4) ∧
        |G.drift t-S.p₀| ≤ ρ/4 ∧ S.γ ≤ G.drift t) ∧
      ∀ s : ℕ → Fin n → ℝ,
        (∀ k,j0 ≤ k → ∀ t i,packetStretch (s k) (pulse k) t i ∈ Icc (1/2:ℝ) (3/2)) →
        ∀ b,‖orthogonalMatrix (S.basis b) (slope (G.coefficient slot s j0 b) G.drift (G.l b) (time j))-
          S.θ b • (1:Matrix (ι b) (ι b) ℝ)‖ ≤ ρ/4 := by
  have hquarter : 0 < ρ/4 := by linarith
  obtain ⟨J₁,hJ₁⟩ := G.uniform_incoming slot hquarter
  obtain ⟨J₂,hJ₂⟩ := G.uniform_radial_tail hquarter
  have hi : Tendsto (fun j => (pulse j)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp pulse_atTop_limit
  obtain ⟨J₃,hJ₃⟩ := eventually_atTop.1 ((pulse_atTop_limit.eventually_ge_atTop T₀).and
    (hi.eventually (gt_mem_nhds (show 0 < ρ/2 by linarith))))
  refine ⟨max J₁ (max J₂ J₃),fun j0 j hj0 hj => ?_⟩
  have hh := hj0.trans hj
  have h1 : J₁ ≤ j := (le_max_left _ _).trans hh
  have h2 : J₂ ≤ j := (le_max_left _ _).trans ((le_max_right _ _).trans hh)
  have h3 : J₃ ≤ j := (le_max_right _ _).trans ((le_max_right _ _).trans hh)
  exact ⟨(hJ₃ j h3).1,by linarith [(hJ₃ j h3).2],hJ₂ j h2,hJ₁ j0 j h1⟩

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl HarmonicCounterexample.FiniteControl.SmoothWord
open HarmonicCounterexample.FiniteControl.Frobenius HarmonicCounterexample.Transmission
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
local instance (d : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedAddCommGroup
local instance (d : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedSpace

omit [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma PhysicalWord.ideal_factor (S : PulseSystem E ι κ) (w : PhysicalWord κ) :
    (fun x b => orthogonalMatrix (S.basis b) (flow (fun t => ContinuousLinearMap.mul ℝ (E b →L[ℝ] E b)
        (unitPacketCoefficient (fun j => w.amps j x) (fun j => bergerSlowGenerator S.r (S.B b) (S.β b) S.p₀ (S.θ b) 1 (S.D b (w.slot j))) t)) 1 1))=w.ideal S := by
  funext x b
  rw [orthogonalMatrix_packet]
  exact (actual_packet_apply (fun j => w.amps j x) (S.generator ∘ w.slot) b).symm

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma PhysicalWord.value_factor (S : PulseSystem E ι κ) (w : PhysicalWord κ) (H : PulseHistory S) :
    (fun x b => orthogonalMatrix (S.basis b) (Real.exp (-(∫ t in H.a..H.a+H.T,
      scalarBaseline (fun s => H.α (H.a+s)*S.B b) (fun s => H.drift (H.a+s)) (S.θ b) (max 0 (t-H.a)))) •
        (operatorValue (insertWord (H.history b) H.α S.r (S.B b • (1:E b →L[ℝ] E b))
          (fun j => S.D b (w.slot j)) (fun j => w.amps j x) H.a H.T) H.drift (H.l b) (H.a+H.T)*
        Ring.inverse (operatorValue (insertWord (H.history b) H.α S.r (S.B b • (1:E b →L[ℝ] E b))
          (fun j => S.D b (w.slot j)) (fun j => w.amps j x) H.a H.T) H.drift (H.l b) H.a)))) = w.value S H := rfl

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma PhysicalWord.defect_factor (S : PulseSystem E ι κ) (w : PhysicalWord κ) (H : PulseHistory S) :
    (fun x b => orthogonalMatrix (S.basis b) (slope (insertWord (H.history b) H.α S.r
      (S.B b • (1:E b →L[ℝ] E b)) (fun j => S.D b (w.slot j)) (fun j => w.amps j x) H.a H.T)
      H.drift (H.l b) (H.a+H.T))-S.θ b • (1:Matrix (ι b) (ι b) ℝ)) = w.defect S H := rfl

omit [Nonempty κ] [∀ b,Nontrivial (ι b)] in
/-- Packaged uniform estimate with precisely the data that occur in a recursive
center-regular geometric construction. -/
theorem word_physical_C1 (S : PulseSystem E ι κ) (w : PhysicalWord κ) :
    ∃ T₀ ρ C : ℝ,1 ≤ T₀ ∧ 0 < ρ ∧ 1 ≤ C ∧
      ∀ H : PulseHistory S,T₀ ≤ H.T → H.δ+H.T⁻¹+H.ε ≤ ρ →
      ∀ x ∈ w.ball,
        DifferentiableAt ℝ (w.value S H) x ∧ DifferentiableAt ℝ (w.defect S H) x ∧
        max (max ‖w.value S H x-w.ideal S x‖ ‖fderiv ℝ (w.value S H) x-fderiv ℝ (w.ideal S) x‖)
          (max ‖w.defect S H x‖ ‖fderiv ℝ (w.defect S H) x‖) ≤ C*(H.δ+H.T⁻¹+H.ε) := by
  classical
  let : NeZero w.n := ⟨w.n_ne⟩
  obtain ⟨threshold,smallness,constant,hthreshold,hsmallness,hconstant,hestimate⟩ :=
    compact_simultaneous_physical_C1 S.basis
      (EuclideanSpace.basisFun (Fin w.d) ℝ) (isCompact_closedBall _ _) S.r S.p₀ S.γ S.M S.B S.β S.θ
      (fun block index => S.D block (w.slot index))
      (fun block index => S.hD block (w.slot index))
      (fun block index => S.hBD block (w.slot index))
      S.hM S.hB S.hθ S.hγ S.hden S.hroot w.amps
      (fun index => fderiv ℝ (w.amps index))
      (fun point (_ : point ∈ Metric.closedBall (0:w.Parameter) (w.radius+1)) index =>
        ((w.smooth index).differentiable (by simp) point).hasFDerivAt)
      (fun index => (w.smooth index).continuous.continuousOn)
      (fun index => ((w.smooth index).continuous_fderiv (by simp)).continuousOn)
  refine ⟨threshold,smallness,constant,hthreshold,hsmallness,hconstant,?_⟩
  intro H hT hsmall x hx
  have hlocal := hestimate H.T hT H.history H.α H.drift H.MH H.Mb H.l H.B₀ H.a H.δ H.ε
    (Metric.ball (0:w.Parameter) (w.radius+1))
    Metric.isOpen_ball (convex_ball _ _).isPreconnected Metric.ball_subset_closedBall
    H.smooth H.αsmooth H.driftContinuous H.MHnonneg H.Mbnonneg H.αbound H.αnonneg
    H.driftBound H.bound H.nonneg H.round H.lpos H.center H.driftCenter H.apos H.δnonneg H.εnonneg
    H.αclose H.driftClose H.driftLower hsmall H.incoming
  have hball : w.ball ⊆ Metric.ball (0:w.Parameter) (w.radius+1) :=
    Metric.closedBall_subset_ball (by linarith)
  simp only [← w.ideal_factor S,← w.value_factor S H,← w.defect_factor S H]
  exact hlocal x (hball hx)


end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl HarmonicCounterexample.FiniteControl.SmoothWord
open HarmonicCounterexample.FiniteControl.Frobenius HarmonicCounterexample.Transmission
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
local instance (d : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedAddCommGroup
local instance (d : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedSpace

/-- The uniform local producer: the genuine simultaneous Lie packet admits
exact physical whole-period tuning, with all thresholds chosen before histories
and BEFORE the bounded complete diagonal-leg normalizers. -/
theorem local_physical_tuning (S : PulseSystem E ι κ)
    (htrace : ∀ j b,(S.generator j b).trace=0)
    (hfull : ∀ X : MatrixProduct ι,(∀ b,(X b).trace=0) →
      X ∈ LieSubalgebra.lieSpan ℝ _ (Set.range S.generator))
    (target : ∀ b,Matrix.SpecialLinearGroup (ι b) ℝ)
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ (w : PhysicalWord κ) (T₀ ρ : ℝ),1 ≤ T₀ ∧ 0 < ρ ∧
      ∀ H : PulseHistory S,T₀ ≤ H.T → H.δ+H.T⁻¹+H.ε ≤ ρ →
      ∀ K : MatrixProduct ι,‖K‖ ≤ K₀ →
      ∃ x ∈ w.ball,∀ b,∃ c : ℝ,c ∈ Ioo (1/2:ℝ) (3/2) ∧
        wholePeriod K (w.defect S H x) (w.value S H x) b=
          c • ((slProductToUnits target:MatrixProduct ι) b) := by
  classical
  obtain ⟨d,n,hn,slot,amps,A,ha,hΦs,hΦ₀,hΦjet⟩ :=
    smooth_SL_packet_submersion S.generator htrace hfull target
  let Φ := fun x => flow (fun t => ContinuousLinearMap.mul ℝ (MatrixProduct ι)
    (unitPacketCoefficient (fun j => amps j x) (S.generator ∘ slot) t)) 1 1
  have hΦs' : ContDiff ℝ ∞ Φ := hΦs
  obtain ⟨R,σ,hR,hσ,hatt⟩ := Frobenius.whole_period_uniform_attainment (slProductToUnits target) Φ
    (fderiv ℝ Φ) A hΦs'.continuous (hΦs'.continuous_fderiv (by simp)) hΦ₀ (by convert! hΦjet using 1) hK₀
  let w : PhysicalWord κ := ⟨d,n,hn.out,slot,amps,ha,R,hR⟩
  obtain ⟨T₀,ρ,C,hT₀,hρ,hC,hworks⟩ := word_physical_C1 S w
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨w,T₀,min ρ (σ/C),hT₀,lt_min hρ (div_pos hσ hCpos),?_⟩
  intro H hT hsmall K hK
  have heσ : C*(H.δ+H.T⁻¹+H.ε) ≤ σ := by
    have he := (le_div_iff₀ hCpos).1 (hsmall.trans (min_le_right ρ (σ/C)))
    simpa only [mul_comm] using he
  have hlocal := hworks H hT (hsmall.trans (min_le_left ρ (σ/C)))
  apply hatt K (w.defect S H) (w.value S H) (fderiv ℝ (w.defect S H)) (fderiv ℝ (w.value S H)) hK
  · intro x hx;exact (hlocal x hx).2.1.hasFDerivAt
  · intro x hx;exact (hlocal x hx).1.hasFDerivAt
  · intro x hx;exact ((le_max_left _ _).trans ((le_max_right _ _).trans (hlocal x hx).2.2)).trans heσ
  · intro x hx;exact ((le_max_left _ _).trans ((le_max_left _ _).trans (hlocal x hx).2.2)).trans heσ
  · intro x hx;exact ((le_max_right _ _).trans ((le_max_right _ _).trans (hlocal x hx).2.2)).trans heσ
  · intro x hx;exact ((le_max_right _ _).trans ((le_max_left _ _).trans (hlocal x hx).2.2)).trans heσ

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses FiniteControl.SmoothWord
open scoped Topology ContDiff BigOperators
variable {κ : Type*} (w : PhysicalWord κ)

/-- Zero belongs to the admissible control space as a genuinely absent pulse,
not as the generally nonzero word at parameter zero. -/
def PhysicalWord.admissible : Set (Fin w.n → ℝ) :=
  {a | a=0 ∨ ∃ x ∈ w.ball,a=(fun i => w.amps i x)}

lemma PhysicalWord.zero_admissible : (0:Fin w.n → ℝ) ∈ w.admissible := Or.inl rfl

lemma PhysicalWord.amplitudes_admissible {x : w.Parameter} (hx : x ∈ w.ball) :
    (fun i => w.amps i x) ∈ w.admissible := Or.inr ⟨x,hx,rfl⟩

lemma PhysicalWord.admissible_uniform_bound : ∃ U : ℝ,0 ≤ U ∧
    ∀ a ∈ w.admissible,∀ i,|a i| ≤ U := by
  classical
  choose C hC using fun i : Fin w.n => (isCompact_closedBall (0:w.Parameter) w.radius).exists_bound_of_continuousOn
    (f:=w.amps i) ((w.smooth i).continuous.continuousOn : ContinuousOn (w.amps i) w.ball)
  let U := ∑ i : Fin w.n,max (C i) 0
  have hU : 0 ≤ U := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  refine ⟨U,hU,fun a ha i => ?_⟩
  rcases ha with rfl | ⟨x,hx,rfl⟩
  · simpa using hU
  · exact (hC i x hx).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)))

/-- The same compact parameter ball works in every later pulse, with a
threshold independent of histories or later parameter choices. -/
theorem PhysicalWord.admissible_stretch_threshold : ∃ J : ℕ,∀ j,J ≤ j →
    ∀ a ∈ w.admissible,∀ t i,packetStretch a (pulse j) t i ∈ Icc (1/2:ℝ) (3/2) := by
  obtain ⟨U,hU,hbound⟩ := w.admissible_uniform_bound
  obtain ⟨C,hC,hpos⟩ := packetStretch_uniform_positive w.n
  obtain ⟨J,hJ⟩ := eventually_atTop.1 (pulse_atTop_limit.eventually_ge_atTop (2*C*U))
  exact ⟨J,fun j hj a ha => hpos a U (pulse j) hU (hbound a ha) (pulse_pos j) (hJ j hj)⟩

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl HarmonicCounterexample.FiniteControl.Frobenius
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)

def HistoryGeometry.baseline (j : ℕ) (b : ξ) (t : ℝ) : ℝ :=
  scalarBaseline (fun s => G.α (time j+s)*S.B b) (fun s => G.drift (time j+s))
    (S.θ b) (max 0 (t-time j))

def HistoryGeometry.packet (s : ℕ → Fin n → ℝ) (j0 j : ℕ) : MatrixProduct ι := fun b =>
  orthogonalMatrix (S.basis b) (Real.exp (-(∫ t in time j..time j+pulse j,G.baseline j b t)) •
    (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j)*
      Ring.inverse (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j))))

def HistoryGeometry.defect (s : ℕ → Fin n → ℝ) (j0 j : ℕ) : MatrixProduct ι := fun b =>
  orthogonalMatrix (S.basis b) (slope (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j))-
    S.θ b • (1:Matrix (ι b) (ι b) ℝ)

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_causal {s u : ℕ → Fin n → ℝ} {j0 j : ℕ}
    (he : ∀ i < j,s i=u i) {t : ℝ} (ht : t ≤ time j) (b : ξ) :
    G.coefficient slot s j0 b t=G.coefficient slot u j0 b t := by
  dsimp [HistoryGeometry.coefficient]
  rw [angular_causal S.r _ _ _ G.qstar j0 he ht]

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.packet_causal {s u : ℕ → Fin n → ℝ} {j0 j : ℕ}
    (he : ∀ i < j+1,s i=u i) :
    G.packet slot s j0 j=G.packet slot u j0 j ∧ G.defect slot s j0 j=G.defect slot u j0 j := by
  have ht1 : time j ∈ Icc 0 (time (j+1)) :=
    ⟨(time_pos j).le,time_strictMono.monotone (by omega)⟩
  have ht2 : time j+pulse j ∈ Icc 0 (time (j+1)) := by
    constructor
    · linarith [time_pos j,pulse_pos j]
    · rw [time_succ];linarith [dwell_pos j,pulse_pos j]
  have hcoeff (b : ξ) : EqOn (G.coefficient slot s j0 b) (G.coefficient slot u j0 b)
      (Icc 0 (time (j+1))) := fun t ht => G.coefficient_causal slot he ht.2 b
  constructor
  · funext b
    simp only [HistoryGeometry.packet,(operator_history_eq (hcoeff b) G.drift (G.l b) ht1).1,
      (operator_history_eq (hcoeff b) G.drift (G.l b) ht2).1]
  · funext b
    simp only [HistoryGeometry.defect,slope_history_eq (hcoeff b) G.drift (G.l b) ht2]

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)
variable (s : ℕ → Fin n → ℝ) (j0 j : ℕ) (δ ε : ℝ)
  (hpos : ∀ k,j0 ≤ k → ∀ t i,packetStretch (s k) (pulse k) t i ∈ Icc (1/2:ℝ) (3/2))
  (hj : j0 ≤ j) (hz : s j=0) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
  (hr : ∀ t,time j ≤ t → (∀ b,|G.α t-S.β b| ≤ δ) ∧ |G.drift t-S.p₀| ≤ δ ∧ S.γ ≤ G.drift t)
  (hi : ∀ b,‖orthogonalMatrix (S.basis b) (slope (G.coefficient slot s j0 b) G.drift (G.l b) (time j))-
    S.θ b • (1:Matrix (ι b) (ι b) ℝ)‖ ≤ ε)

/-- This is a constructor from the actual stream. All nontrivial input facts
are supplied by the single history-independent threshold theorem. -/
def HistoryGeometry.pulseHistory : PulseHistory S where
  history := G.coefficient slot s j0
  α := G.α
  drift := G.drift
  MH := G.bound slot
  Mb := G.Mp
  l := G.l
  B₀ := G.B₀
  a := time j
  T := pulse j
  δ := δ
  ε := ε
  smooth := G.coefficient_smooth slot s j0 hpos
  αsmooth := G.αsmooth
  driftContinuous := G.driftContinuous
  MHnonneg := G.bound_nonneg slot
  Mbnonneg := G.Mpnonneg
  αbound := G.αbound
  αnonneg := G.αnonneg
  driftBound := G.driftBound
  bound := G.coefficient_bound slot s j0 hpos
  nonneg := G.coefficient_nonnegative slot s j0 hpos
  round := fun b t ht => G.coefficient_round slot s j0 b hj hz t ht
  lpos := G.lpos
  center := G.coefficient_center slot s j0
  driftCenter := G.driftCenter
  apos := (time_pos j).le
  δnonneg := hδ
  εnonneg := hε
  αclose := fun b t ht => (hr t ht.1).1 b
  driftClose := fun t ht => (hr t ht.1).2.1
  driftLower := fun t ht => (hr t ht.1).2.2
  incoming := hi

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace

/-- One smooth infinite stream simultaneously tunes every whole-period packet.
All thresholds precede EVERY history. The bounded normalizers may be any
predetermined actual complete diagonal legs; they do not supply transmissions. -/
theorem global_physical_tuning (S : PulseSystem E ι κ) (G : HistoryGeometry S)
    (htrace : ∀ j b,(S.generator j b).trace=0)
    (hfull : ∀ X : MatrixProduct ι,(∀ b,(X b).trace=0) →
      X ∈ LieSubalgebra.lieSpan ℝ _ (Set.range S.generator))
    (target : ∀ b,Matrix.SpecialLinearGroup (ι b) ℝ)
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ w : PhysicalWord κ,∃ J : ℕ,∀ j0,J ≤ j0 →
      ∀ K : ℕ → MatrixProduct ι,(∀ j,j0 ≤ j → ‖K j‖ ≤ K₀) →
      ∃ s : ℕ → Fin w.n → ℝ,
        (∀ j,s j ∈ w.admissible) ∧ (∀ j,j<j0 → s j=0) ∧
        (∀ j,j0 ≤ j → ∀ t i,packetStretch (s j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2)) ∧
        ∀ j,j0 ≤ j → ∀ b,∃ c : ℝ,c ∈ Ioo (1/2:ℝ) (3/2) ∧
          wholePeriod (K j) (G.defect w.slot s j0 j) (G.packet w.slot s j0 j) b=
            c • ((slProductToUnits target:MatrixProduct ι) b) := by
  classical
  obtain ⟨w,T₀,ρ,hT₀,hρ,htune⟩ := local_physical_tuning S htrace hfull target hK₀
  let : NeZero w.n := ⟨w.n_ne⟩
  obtain ⟨J₁,hJ₁⟩ := G.eventual_history_conditions w.slot T₀ hρ
  obtain ⟨J₂,hJ₂⟩ := w.admissible_stretch_threshold
  refine ⟨w,max J₁ J₂,fun j0 hj0 K hK => ?_⟩
  have hj1 : J₁ ≤ j0 := (le_max_left _ _).trans hj0
  have hj2 : J₂ ≤ j0 := (le_max_right _ _).trans hj0
  let good (j : ℕ) (s : ℕ → Fin w.n → ℝ) (a : Fin w.n → ℝ) : Prop :=
    (j<j0 → a=0) ∧ (j0 ≤ j → ∀ b,∃ c : ℝ,c ∈ Ioo (1/2:ℝ) (3/2) ∧
      wholePeriod (K j) (G.defect w.slot (Function.update s j a) j0 j)
        (G.packet w.slot (Function.update s j a) j0 j) b=
          c • ((slProductToUnits target:MatrixProduct ι) b))
  have produce : ∀ j s,(∀ i < j,s i ∈ w.admissible) → (∀ i,j ≤ i → s i=0) →
      ∃ a ∈ w.admissible,good j s a := by
    intro j s hs hz
    by_cases hj : j0 ≤ j
    · have hsall (i : ℕ) : s i ∈ w.admissible := by
        by_cases hi : i<j
        · exact hs i hi
        · rw [hz i (by omega)];exact w.zero_admissible
      have hpos : ∀ k,j0 ≤ k → ∀ t i,packetStretch (s k) (pulse k) t i ∈ Icc (1/2:ℝ) (3/2) :=
        fun k hk => hJ₂ k (hj2.trans hk) (s k) (hsall k)
      obtain ⟨hT,hsmall,hr,hin⟩ := hJ₁ j0 j hj1 hj
      have hquarter : 0 ≤ ρ/4 := by linarith
      let H := G.pulseHistory w.slot s j0 j (ρ/4) (ρ/4) hpos hj (hz j le_rfl)
        hquarter hquarter hr (hin s hpos)
      obtain ⟨x,hx,hxTune⟩ := htune H hT hsmall (K j) (hK j hj)
      let a : Fin w.n → ℝ := fun i => w.amps i x
      have hc (b : ξ) : w.coefficient S H b x=G.coefficient w.slot (Function.update s j a) j0 b := by
        change insertWord (G.coefficient w.slot s j0 b) G.α S.r (S.B b • (1:E b →L[ℝ] E b))
          (fun i => S.D b (w.slot i)) a (time j) (pulse j)=_
        exact (coefficient_update S.r _ (G.D₀ b) _ s a G.qstar G.α hj (hz j le_rfl)).symm
      have hv : w.value S H x=G.packet w.slot (Function.update s j a) j0 j := by
        funext b
        unfold PhysicalWord.value HistoryGeometry.packet
        rw [hc b]
        rfl
      have hd : w.defect S H x=G.defect w.slot (Function.update s j a) j0 j := by
        funext b
        unfold PhysicalWord.defect HistoryGeometry.defect
        rw [hc b]
        rfl
      refine ⟨a,w.amplitudes_admissible hx,?_,?_⟩
      · intro h;omega
      · intro _
        rw [←hv,←hd]
        exact hxTune
    · refine ⟨0,w.zero_admissible,fun _ => rfl,?_⟩
      intro h;exact (hj h).elim
  obtain ⟨s,hs,hgood⟩ := CausalConstruction.causal_choice 0 w.admissible good produce
  refine ⟨s,hs,fun j hj => (hgood j).1 hj,?_,?_⟩
  · intro j hj
    exact hJ₂ j (hj2.trans hj) (s j) (hs j)
  · intro j hj
    have ht := (hgood j).2 hj
    have he : ∀ i < j+1,s i=Function.update (fun k => if k<j then s k else 0) j (s j) i := by
      intro i hi
      by_cases hij : i=j
      · subst i;simp
      · rw [Function.update_of_ne hij,ite_eq_left (by omega)]
    obtain ⟨hv,hd⟩ := G.packet_causal w.slot (j0:=j0) he
    rw [←hv,←hd] at ht
    exact ht

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.Transmission
open Set
open scoped Matrix.Norms.Frobenius
variable {β : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)]

omit [Fintype β] in
/-- Block-dependent Riccati roots are kept in the complete-leg identity. -/
lemma blockwise_whole_period_exact_leg
    {U V P B : ∀ b,Matrix (ι b) (ι b) ℝ} (θ : β → ℝ)
    (D M : ∀ b,(Matrix (ι b) (ι b) ℝ)ˣ)
    (hD : ∀ b,(D b:Matrix (ι b) (ι b) ℝ)=U b+θ b • V b)
    (hatt : ∀ b,∃ c : ℝ,c ∈ Ioo (1/2:ℝ) (3/2) ∧
      wholePeriod ((↑(D b)⁻¹:Matrix (ι b) (ι b) ℝ)*V b) (P b-θ b • 1) (B b)=
        c • (M b:Matrix (ι b) (ι b) ℝ)) :
    ∀ b,∃ c : ℝ,c ∈ Ioo (1/2:ℝ) (3/2) ∧
      (U b+V b*P b)*B b=c • ((D b:Matrix (ι b) (ι b) ℝ)*(M b:Matrix (ι b) (ι b) ℝ)) := by
  intro b
  obtain ⟨c,hc,he⟩ := hatt b
  refine ⟨c,hc,?_⟩
  have hf := full_leg_factor (U b) (V b) (P b) (B b) (θ b) (D b) (hD b)
  change (↑(D b)⁻¹:Matrix (ι b) (ι b) ℝ)*((U b+V b*P b)*B b)=
    wholePeriod ((↑(D b)⁻¹:Matrix (ι b) (ι b) ℝ)*V b) (P b-θ b • 1) (B b) at hf
  have hh := congrArg (fun X => (D b:Matrix (ι b) (ι b) ℝ)*X) hf
  rw [← mul_assoc,Units.mul_inv,one_mul,he,Matrix.mul_smul] at hh
  exact hh

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Undo ONLY the harmless scalar pulse normalization. The scalar logarithmic
cost is separated from the genuine diagonal factor of the entire leg. -/
lemma unnormalize_whole_leg {Fa Fc Fd U V P D M : R} {I c : ℝ}
    (hvalue : Fd=(U+V*P)*Fc)
    (htune : (U+V*P)*(Real.exp (-I) • (Fc*Fa))=c • (D*M)) :
    Fd*Fa=(Real.exp I*c) • (D*M) := by
  have he := congrArg (fun X : R => Real.exp I • X) htune
  rw [mul_smul_comm,smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul] at he
  rw [hvalue,mul_assoc]
  simpa only [smul_smul] using he

end HarmonicCounterexample.Transmission

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
local instance (b : ξ) : NormedAddCommGroup ((E b →L[ℝ] E b) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ ((E b →L[ℝ] E b) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedSpace

local instance (b : ξ) : NormedAddCommGroup (Matrix (ι b) (ι b) ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (Matrix (ι b) (ι b) ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance (b : ξ) : NormedAddCommGroup ((ι b → ℝ) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ ((ι b → ℝ) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedSpace

variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma zero_stretch (j : ℕ) (t : ℝ) (i : Fin n) :
    packetStretch (0:Fin n → ℝ) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2) := by
  norm_num [packetStretch]

/-- Background diagonal coefficient, independent of all control choices. -/
def HistoryGeometry.baseCoefficient (j0 : ℕ) (b : ξ) (t : ℝ) : E b →L[ℝ] E b :=
  G.α t • PulseTaylor.angular S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b) (base G.qstar j0 t)

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.baseCoefficient_eq (slot : Fin n → κ) (j0 : ℕ) (b : ξ) :
    G.baseCoefficient j0 b=G.coefficient slot 0 j0 b := by
  funext t
  unfold HistoryGeometry.baseCoefficient HistoryGeometry.coefficient angular
  have he : (fun j => activeIncrement S.r (S.B b • (1:E b →L[ℝ] E b))
      (fun i => S.D b (slot i)) 0 j0 j t)=fun _ => (0:E b →L[ℝ] E b) := by
    funext j
    dsimp [activeIncrement]
    split_ifs
    · exact increment_zero S.r _ _ rfl t
    · rfl
  rw [he,tsum_zero,add_zero]

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.baseCoefficient_diagonal (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b))
    (j0 : ℕ) (b : ξ) (t : ℝ) :
    orthogonalMatrix (S.basis b) (G.baseCoefficient j0 b t)=Matrix.diagonal (fun i =>
      G.α t*((base G.qstar j0 t)^S.r*S.B b+
        ((base G.qstar j0 t)^S.r-(base G.qstar j0 t)^(S.r-1))*d₀ b i)) := by
  simp only [HistoryGeometry.baseCoefficient,PulseTaylor.angular,map_smul,map_add,
    orthogonalMatrix_one,hd₀]
  ext i j
  by_cases h : i=j
  · subst j;simp [Matrix.diagonal_apply_eq,smul_eq_mul]
  · simp [h,smul_eq_mul]

/-- The genuine fixed diagonal scalar coefficient. -/
def HistoryGeometry.legLambda (d₀ : ∀ b,ι b → ℝ) (j0 : ℕ) (b : ξ) (i : ι b) (t : ℝ) : ℝ :=
  G.α t*((base G.qstar j0 t)^S.r*S.B b+
    ((base G.qstar j0 t)^S.r-(base G.qstar j0 t)^(S.r-1))*d₀ b i)

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.legLambda_properties (slot : Fin n → κ) (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b)) (j0 : ℕ) (b : ξ) :
    ∃ N : ι b → ℝ,(∀ i,0 ≤ N i) ∧
      (∀ i,Continuous (G.legLambda d₀ j0 b i)) ∧
      (∀ i t,|G.legLambda d₀ j0 b i t| ≤ N i) ∧
      (∀ i t,0 ≤ G.legLambda d₀ j0 b i t) := by
  have hp : ∀ j,j0 ≤ j → ∀ t i,packetStretch ((0:ℕ → Fin n → ℝ) j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2) :=
    fun j _ t i => zero_stretch j t i
  have hbc := G.baseCoefficient_eq slot j0 b
  have hc : Continuous (G.baseCoefficient j0 b) := by
    rw [hbc];exact (G.coefficient_smooth slot 0 j0 hp b).continuous
  have he (i : ι b) (t : ℝ) : G.legLambda d₀ j0 b i t=
      matrixEntry i i (orthogonalMatrix (S.basis b) (G.baseCoefficient j0 b t)) := by
    rw [matrixEntry_apply,G.baseCoefficient_diagonal d₀ hd₀,Matrix.diagonal_apply_eq]
    rfl
  let N : ι b → ℝ := fun i => ‖matrixEntry i i‖*‖orthogonalMatrix (S.basis b)‖*G.bound slot b
  refine ⟨N,fun i => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (G.bound_nonneg slot b),?_,?_,?_⟩
  · intro i
    have hf : G.legLambda d₀ j0 b i=fun t => matrixEntry i i (orthogonalMatrix (S.basis b) (G.baseCoefficient j0 b t)) := funext (he i)
    rw [hf];exact (matrixEntry i i).continuous.comp ((orthogonalMatrix (S.basis b)).continuous.comp hc)
  · intro i t
    rw [he i t,← Real.norm_eq_abs]
    calc
      _ ≤ ‖matrixEntry i i‖*‖orthogonalMatrix (S.basis b) (G.baseCoefficient j0 b t)‖ := (matrixEntry i i).le_opNorm _
      _ ≤ ‖matrixEntry i i‖*(‖orthogonalMatrix (S.basis b)‖*‖G.baseCoefficient j0 b t‖) :=
        mul_le_mul_of_nonneg_left ((orthogonalMatrix (S.basis b)).le_opNorm _) (norm_nonneg _)
      _ ≤ N i := by
        dsimp [N];rw [mul_assoc,hbc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (G.coefficient_bound slot 0 j0 hp b t) (norm_nonneg _)) (norm_nonneg _)
  · intro i t
    rw [he i t,matrixEntry_apply,orthogonalMatrix_apply,OrthonormalBasis.repr_apply_apply,hbc]
    exact G.coefficient_nonnegative slot 0 j0 hp b t (S.basis b i)

/-- ACTUAL complete-leg columns with the physical schedule. -/
def HistoryGeometry.legU (d₀ : ∀ b,ι b → ℝ) (j0 j : ℕ) (b : ξ) : Matrix (ι b) (ι b) ℝ :=
  Matrix.diagonal (fun i => scalarU (fun t => G.legLambda d₀ j0 b i (time j+pulse j+t))
    (fun t => G.drift (time j+pulse j+t)) (time (j+1)-(time j+pulse j)))
def HistoryGeometry.legV (d₀ : ∀ b,ι b → ℝ) (j0 j : ℕ) (b : ξ) : Matrix (ι b) (ι b) ℝ :=
  Matrix.diagonal (fun i => scalarV (fun t => G.legLambda d₀ j0 b i (time j+pulse j+t))
    (fun t => G.drift (time j+pulse j+t)) (time (j+1)-(time j+pulse j)))

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b, Nontrivial (ι b)] in
lemma HistoryGeometry.leg_normalizer (slot : Fin n → κ) (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b)) (j0 j : ℕ) (b : ξ) :
    ∃ D : (Matrix (ι b) (ι b) ℝ)ˣ,
      (D:Matrix (ι b) (ι b) ℝ)=G.legU d₀ j0 j b+S.θ b • G.legV d₀ j0 j b ∧
      (∀ i,0 < (D:Matrix (ι b) (ι b) ℝ) i i) ∧
      ‖(↑D⁻¹:Matrix (ι b) (ι b) ℝ)*G.legV d₀ j0 j b‖ ≤
        ‖diagonalL (ι:=ι b)‖*(S.θ b)⁻¹ := by
  obtain ⟨N,hN,hc,hb,hp⟩ := G.legLambda_properties slot d₀ hd₀ j0 b
  apply actual_diagonal_normalizer (fun i => (hc i).comp (continuous_const.add continuous_id))
    (G.driftContinuous.comp (continuous_const.add continuous_id)) N hN G.Mpnonneg
    (fun i t => hb i _) (fun t => G.driftBound _) (fun i t _ => hp i _) ?_ (S.hθ b)
  rw [time_succ];linarith [pulse_pos j,dwell_pos j]

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)

/-- Actual center-regular value transmission, including the complete diagonal
leg and with no pulse scalar normalization. -/
def HistoryGeometry.transmission (s : ℕ → Fin n → ℝ) (j0 j : ℕ) (b : ξ) : Matrix (ι b) (ι b) ℝ :=
  orthogonalMatrix (S.basis b)
    (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time (j+1))*
      Ring.inverse (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j)))

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b, Nontrivial (ι b)] in
lemma HistoryGeometry.actual_leg_restart (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b))
    (s : ℕ → Fin n → ℝ) (j0 j : ℕ)
    (hpos : ∀ k,j0 ≤ k → ∀ t i,packetStretch (s k) (pulse k) t i ∈ Icc (1/2:ℝ) (3/2))
    (hj : j0 ≤ j) (b : ξ) :
    orthogonalMatrix (S.basis b) (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time (j+1)))=
      (G.legU d₀ j0 j b+G.legV d₀ j0 j b*
        orthogonalMatrix (S.basis b) (slope (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j)))*
      orthogonalMatrix (S.basis b) (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j)) := by
  obtain ⟨N,hN,hc,hb,hp⟩ := G.legLambda_properties slot d₀ hd₀ j0 b
  have hA := (G.coefficient_smooth slot s j0 hpos b).continuous
  have hbound := G.coefficient_bound slot s j0 hpos b
  have hnonneg := G.coefficient_nonnegative slot s j0 hpos b
  have hdiag (t : ℝ) (ht : t ∈ Ico (time j+pulse j) (time (j+1))) :
      orthogonalMatrix (S.basis b) (G.coefficient slot s j0 b t)=
        Matrix.diagonal (fun i => G.legLambda d₀ j0 b i t) := by
    change orthogonalMatrix (S.basis b) (G.α t • angular _ _ _ _ _ _ _ _)=_
    rw [angular_leg _ _ _ _ _ hj ht.1 ht.2.le]
    exact G.baseCoefficient_diagonal d₀ hd₀ j0 b t
  have he := actual_diagonal_restart (S.basis b) N (G.l b) hA G.driftContinuous hc
    (G.bound_nonneg slot b) G.Mpnonneg hN hbound G.driftBound hb hdiag
    (time (j+1)) ⟨by rw [time_succ];linarith [pulse_pos j,dwell_pos j],le_rfl⟩
  change _=G.legU d₀ j0 j b*_
    +G.legV d₀ j0 j b*orthogonalMatrix (S.basis b)
      (operatorVelocity (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j)) at he
  have hu := operatorValue_isUnit hA G.driftContinuous (G.bound_nonneg slot b) G.Mpnonneg
    hbound G.driftBound hnonneg (G.lpos b) (t:=time j+pulse j) (by linarith [time_pos j,pulse_pos j])
  have hs : operatorVelocity (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j)=
      slope (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j)*
        operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j) := by
    ext x;exact (slope_value hu x).symm
  rw [hs,orthogonalMatrix_mul,← mul_assoc,← add_mul] at he
  exact he

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b, Nontrivial (ι b)] in
/-- Attainment in normalized pulse coordinates gives the actual WHOLE period,
with its scalar exactly separated. -/
theorem HistoryGeometry.exact_period (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b))
    (s : ℕ → Fin n → ℝ) (j0 j : ℕ)
    (hpos : ∀ k,j0 ≤ k → ∀ t i,packetStretch (s k) (pulse k) t i ∈ Icc (1/2:ℝ) (3/2))
    (hj : j0 ≤ j) (b : ξ) (D : (Matrix (ι b) (ι b) ℝ)ˣ)
    (hD : (D:Matrix (ι b) (ι b) ℝ)=G.legU d₀ j0 j b+S.θ b • G.legV d₀ j0 j b)
    (M : Matrix (ι b) (ι b) ℝ) {c : ℝ}
    (htune : wholePeriod ((↑D⁻¹:Matrix (ι b) (ι b) ℝ)*G.legV d₀ j0 j b)
      (G.defect slot s j0 j b) (G.packet slot s j0 j b)=c • M) :
    G.transmission slot s j0 j b=
      (Real.exp (∫ t in time j..time j+pulse j,G.baseline j b t)*c) • ((D:Matrix (ι b) (ι b) ℝ)*M) := by
  let P := orthogonalMatrix (S.basis b) (slope (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j))
  have hf := full_leg_factor (G.legU d₀ j0 j b) (G.legV d₀ j0 j b) P
    (G.packet slot s j0 j b) (S.θ b) D hD
  have he := congrArg (fun X => (D:Matrix (ι b) (ι b) ℝ)*X) hf
  rw [←mul_assoc,Units.mul_inv,one_mul] at he
  change (G.legU d₀ j0 j b+G.legV d₀ j0 j b*P)*G.packet slot s j0 j b=
    (D:Matrix (ι b) (ι b) ℝ)*wholePeriod _ (G.defect slot s j0 j b) (G.packet slot s j0 j b) at he
  rw [htune,Matrix.mul_smul] at he
  have hv := G.actual_leg_restart slot d₀ hd₀ s j0 j hpos hj b
  have hp : G.packet slot s j0 j b=
      Real.exp (-(∫ t in time j..time j+pulse j,G.baseline j b t)) •
        (orthogonalMatrix (S.basis b) (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j))*
        orthogonalMatrix (S.basis b) (Ring.inverse (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j)))) := by
    simp only [HistoryGeometry.packet,map_smul,orthogonalMatrix_mul]
  rw [hp] at he
  have hu := unnormalize_whole_leg hv he
  simpa only [HistoryGeometry.transmission,orthogonalMatrix_mul] using hu

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup ((ι b → ℝ) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ ((ι b → ℝ) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedSpace

/-- One actual infinite center-regular equation realizes ALL the requested
complete-period transmissions. Its normalizers are the true second-order
post-pulse columns U,V, not supplied targets or asymptotic substitutes. -/
theorem global_actual_transmission (S : PulseSystem E ι κ) (G : HistoryGeometry S)
    (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b))
    (htrace : ∀ j b,(S.generator j b).trace=0)
    (hfull : ∀ X : MatrixProduct ι,(∀ b,(X b).trace=0) →
      X ∈ LieSubalgebra.lieSpan ℝ _ (Set.range S.generator))
    (target : ∀ b,Matrix.SpecialLinearGroup (ι b) ℝ) :
    ∃ w : PhysicalWord κ,∃ J : ℕ,∀ j0,J ≤ j0 →
      ∃ s : ℕ → Fin w.n → ℝ,
        (∀ j,s j ∈ w.admissible) ∧ (∀ j,j<j0 → s j=0) ∧
        (∀ j,j0 ≤ j → ∀ t i,packetStretch (s j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2)) ∧
        ∀ j,j0 ≤ j → ∀ b,∃ D : (Matrix (ι b) (ι b) ℝ)ˣ,
          (D:Matrix (ι b) (ι b) ℝ)=G.legU d₀ j0 j b+S.θ b • G.legV d₀ j0 j b ∧
          (∀ i,0 < (D:Matrix (ι b) (ι b) ℝ) i i) ∧
          ∃ c : ℝ,c ∈ Ioo (1/2:ℝ) (3/2) ∧
            G.transmission w.slot s j0 j b=
              (Real.exp (∫ t in time j..time j+pulse j,G.baseline j b t)*c) •
                ((D:Matrix (ι b) (ι b) ℝ)*((target b):Matrix (ι b) (ι b) ℝ)) := by
  classical
  let K₀ : ℝ := ∑ b : ξ,‖diagonalL (ι:=ι b)‖*(S.θ b)⁻¹
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg (fun b _ => mul_nonneg (norm_nonneg _) (inv_nonneg.2 (S.hθ b).le))
  obtain ⟨w,J,htune⟩ := global_physical_tuning S G htrace hfull target hK₀
  let : NeZero w.n := ⟨w.n_ne⟩
  refine ⟨w,J,fun j0 hj0 => ?_⟩
  let D (j : ℕ) (b : ξ) := (G.leg_normalizer w.slot d₀ hd₀ j0 j b).choose
  have hD (j : ℕ) (b : ξ) := (G.leg_normalizer w.slot d₀ hd₀ j0 j b).choose_spec
  let K (j : ℕ) : MatrixProduct ι := fun b => (↑(D j b)⁻¹:Matrix (ι b) (ι b) ℝ)*G.legV d₀ j0 j b
  have hK (j : ℕ) (_ : j0 ≤ j) : ‖K j‖ ≤ K₀ := by
    apply (pi_norm_le_iff_of_nonneg hK₀).2
    intro b
    exact (hD j b).2.2.trans (Finset.single_le_sum
      (fun c _ => mul_nonneg (norm_nonneg (diagonalL (ι:=ι c))) (inv_nonneg.2 (S.hθ c).le)) (Finset.mem_univ b))
  obtain ⟨s,hs,hzero,hpos,he⟩ := htune j0 hj0 K hK
  refine ⟨s,hs,hzero,hpos,fun j hj b => ?_⟩
  obtain ⟨c,hc,ht⟩ := he j hj b
  refine ⟨D j b,(hD j b).1,(hD j b).2.1,c,hc,?_⟩
  apply G.exact_period w.slot d₀ hd₀ s j0 j hpos hj b (D j b) (hD j b).1 _ ht

end HarmonicCounterexample.LinearODE

end

end OAI
