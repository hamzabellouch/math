import OAI.Geometry.PolarProducts.SmoothProfiles

namespace OAI

universe u123 u124 u125 u126

section NonsqueezingInline

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE SmoothProfiles EmbeddingInverse
variable {κ : Type u123} [Fintype κ]

 def domain (L : ℝ) : Set (Vector κ) := {z | ‖z‖^2 < L}
 def core (L ε : ℝ) : Set (Vector κ) := Metric.closedBall 0 (Real.sqrt (L-ε))
 def radial (r L ε : ℝ) (z : Vector κ) : ℝ := ballProfile r L ε (‖z‖^2)

 theorem isOpen_domain (L : ℝ) : IsOpen (domain (κ := κ) L) :=
   isOpen_lt (continuous_norm.pow 2) continuous_const

 theorem core_compact (L ε : ℝ) : IsCompact (core (κ := κ) L ε) := isCompact_closedBall _ _

 theorem mem_core_iff {L ε : ℝ} (hL : 0 ≤ L-ε) (z : Vector κ) :
    z ∈ core L ε ↔ ‖z‖^2 ≤ L-ε := by
   simp only [core, Metric.mem_closedBall, dist_zero_right]
   exact (Real.le_sqrt (norm_nonneg z) hL)

 theorem core_subset_domain {L ε : ℝ} (hε : 0 < ε) (hL : ε ≤ L) :
    core (κ := κ) L ε ⊆ domain L := by
   intro z hz
   have hh := (mem_core_iff (sub_nonneg.mpr hL) z).mp hz
   change ‖z‖^2 < L
   linarith

 theorem contDiff_radial (r L ε : ℝ) : ContDiff ℝ ∞ (radial (κ := κ) r L ε) :=
   (contDiff_ballProfile r L ε).comp ((contDiff_id : ContDiff ℝ ∞ (id : Vector κ → Vector κ)).norm_sq ℝ)

 theorem radial_eq_height {r L ε : ℝ} (hε : 0 < ε) (hL : ε ≤ L)
    {z : Vector κ} (hz : z ∉ core L ε) : radial r L ε z = ballHeight r L ε := by
   apply ballProfile_plateau r L hε
   exact le_of_lt (lt_of_not_ge ((mem_core_iff (sub_nonneg.mpr hL) z).not.mp hz))

 def pushed (e : OpenPartialHomeomorph (Vector κ) (Vector κ)) (r L ε : ℝ) (z : Vector κ) : ℝ :=
   extendFunction e (fun w => radial r L ε w-ballHeight r L ε) z+ballHeight r L ε

 theorem contDiff_pushed (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source) {L : ℝ} (hs : e.source = domain L)
    (hD : ∀ x ∈ e.source, (fderiv ℝ e x).IsInvertible)
    {r ε : ℝ} (hε : 0 < ε) (hL : ε ≤ L) : ContDiff ℝ ∞ (pushed e r L ε) := by
   apply (contDiff_extendFunction e he hD ((contDiff_radial r L ε).sub contDiff_const)
     (core_compact L ε) _ _).add contDiff_const
   · rw [hs]; exact core_subset_domain hε hL
   · intro z hz
     rw [radial_eq_height hε hL hz, sub_self]

 theorem pushed_apply (e : OpenPartialHomeomorph (Vector κ) (Vector κ)) (r L ε : ℝ)
    {x : Vector κ} (hx : x ∈ e.source) : pushed e r L ε (e x) = radial r L ε x := by
   simp only [pushed, extendFunction_apply e _ hx, sub_add_cancel]

 theorem pushed_plateau (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    {r L ε : ℝ} (hε : 0 < ε) (hL : ε ≤ L) {x : Vector κ} (hx : x ∉ e '' core L ε) :
    pushed e r L ε x = ballHeight r L ε := by
   rw [pushed, extendFunction_zero e _ (core L ε) (fun z hz => by rw [radial_eq_height hε hL hz,sub_self]) hx,
     zero_add]

 theorem pushed_bounds (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    {r L ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) (x : Vector κ) :
    0 ≤ pushed e r L ε x ∧ pushed e r L ε x ≤ ballHeight r L ε := by
   rcases extendFunction_mem_range e (fun w => radial r L ε w-ballHeight r L ε) x with hz | ⟨w,_,hw⟩
   · simp only [pushed,hz,zero_add,le_refl,and_true]
     exact ballProfile_nonneg hr L hε (L-ε)
   · simp only [pushed,hw,sub_add_cancel]
     exact ⟨ballProfile_nonneg hr L hε _,ballProfile_le_height hr L hε _⟩

 theorem zero_mem_domain {L : ℝ} (hL : 0 < L) : (0 : Vector κ) ∈ domain L := by
   simpa only [domain, mem_ofPred_eq, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hL

 theorem radial_flat {r L ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 (0 : Vector κ), radial r L ε z = 0 := by
   have hsmall : ∀ᶠ z in 𝓝 (0 : Vector κ), ‖z‖^2 < ε :=
     (isOpen_domain ε).mem_nhds (zero_mem_domain hε)
   filter_upwards [hsmall] with z hz
   exact ballProfile_zero r L hε hz.le

 theorem pushed_flat (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    {r L ε : ℝ} (hs : e.source = domain L) (hε : 0 < ε) (hL : ε ≤ L) :
    ∀ᶠ z in 𝓝 (e 0), pushed e r L ε z = 0 := by
   have h0 : (0 : Vector κ) ∈ e.source := by
     rw [hs]; exact zero_mem_domain (hε.trans_le hL)
   apply eventually_of_comp e h0
   filter_upwards [e.open_source.mem_nhds h0,radial_flat (r := r) (L := L) hε] with z hz hflat
   rw [pushed_apply e r L ε hz]
   exact hflat

 theorem radial_slow {r L ε : ℝ} (hr : 0 ≤ r) (hrπ : r < Real.pi)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (radial r L ε) (x t)) t)
    (hp : x 1 = x 0) (t : ℝ) : x t = x 0 :=
   slow_radial_constant (hasDerivAt_ballProfile r L ε) (ballSlope_nonneg hr L ε)
     (fun s => (ballSlope_le hr L ε s).trans_lt hrπ) hx hp t

end
end PushedBall

namespace ExteriorHamiltonian
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth SmoothProfiles
variable {κ : Type u124} [Fintype κ]

 def potential (d : κ → ℝ) (T δ : ℝ) (z : Vector κ) : ℝ := exterior δ (energy d z-T)
 def full (H₀ : Vector κ → ℝ) (d : κ → ℝ) (T δ : ℝ) (z : Vector κ) : ℝ :=
   H₀ z+potential d T δ z

 theorem contDiff_potential (d : κ → ℝ) (T δ : ℝ) : ContDiff ℝ ∞ (potential d T δ) :=
   (contDiff_exterior δ).comp ((contDiff_energy d).sub contDiff_const)

 theorem contDiff_full {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀) (d : κ → ℝ) (T δ : ℝ) :
    ContDiff ℝ ∞ (full H₀ d T δ) := hH₀.add (contDiff_potential d T δ)

 theorem gradient_potential (d : κ → ℝ) (T δ : ℝ) (z : Vector κ) :
    gradient (potential d T δ) z = (2*exteriorSlope δ (energy d z-T)) • diag d z := by
   change gradient (fun w : Vector κ => exterior δ (energy d w-T)) z = _
   convert! gradient_comp_energy d z ((hasDerivAt_exterior δ (energy d z-T)).comp (energy d z)
     ((hasDerivAt_id (energy d z)).sub_const T)) using 1
   simp only [mul_one]

 theorem gradient_sum {H G : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (z : Vector κ) : gradient (fun w => H w+G w) z = gradient H z+gradient G z := by
   apply HasGradientAt.gradient
   rw [hasGradientAt_iff_hasFDerivAt]
   have hh := ((hH.differentiable (by simp) z).hasGradientAt.hasFDerivAt).add
     ((hG.differentiable (by simp) z).hasGradientAt.hasFDerivAt)
   convert! hh using 1
   ext w
   change inner (𝕜 := ℝ) (gradient H z+gradient G z) w =
     inner (𝕜 := ℝ) (gradient H z) w+inner (𝕜 := ℝ) (gradient G z) w
   exact inner_add_left _ _ _

 theorem gradient_full {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    (d : κ → ℝ) (T δ : ℝ) (z : Vector κ) :
    gradient (full H₀ d T δ) z = gradient H₀ z+(2*exteriorSlope δ (energy d z-T)) • diag d z := by
   change gradient (fun w => H₀ w+potential d T δ w) z = _
   rw [gradient_sum hH₀ (contDiff_potential d T δ), gradient_potential]

 theorem gradient_at_max {H : Vector κ → ℝ} {m : ℝ} (hm : ∀ z, H z ≤ m)
    {z : Vector κ} (hz : H z = m) : gradient H z = 0 := by
   have he : IsLocalMax H z := Filter.Eventually.of_forall (fun w => by rw [hz]; exact hm w)
   simp only [gradient,he.fderiv_eq_zero,map_zero]

 theorem gradient_at_min {H : Vector κ → ℝ} {m : ℝ} (hm : ∀ z, m ≤ H z)
    {z : Vector κ} (hz : H z = m) : gradient H z = 0 := by
   have he : IsLocalMin H z := Filter.Eventually.of_forall (fun w => by rw [hz]; exact hm w)
   simp only [gradient,he.fderiv_eq_zero,map_zero]

 theorem potential_zero (d : κ → ℝ) (T : ℝ) {δ : ℝ} (hδ : 0 < δ) {z : Vector κ}
    (hz : energy d z ≤ T) : potential d T δ z = 0 := exterior_zero hδ (sub_nonpos.mpr hz)

 theorem potential_nonneg (d : κ → ℝ) (T : ℝ) {δ : ℝ} (hδ : 0 < δ) (z : Vector κ) :
    0 ≤ potential d T δ z := exterior_nonneg hδ _

 theorem compact_sublevel (d : κ → ℝ) {b C : ℝ} (hb : 0 < b) (hd : ∀ j, b ≤ d j) (hC : 0 ≤ C) :
    IsCompact {z : Vector κ | energy d z ≤ C} := by
   apply (isCompact_closedBall (0 : Vector κ) (Real.sqrt (C/b))).of_isClosed_subset
     (isClosed_le (contDiff_energy d).continuous continuous_const)
   intro z hz
   simp only [Metric.mem_closedBall,dist_zero_right]
   apply (Real.le_sqrt (norm_nonneg z) (div_nonneg hC hb.le)).mpr
   apply (le_div_iff₀ hb).mpr
   have he := energy_lower d b hd z
   change energy d z ≤ C at hz
   nlinarith

 theorem bounded_remainder {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    {m : ℝ} (hm : ∀ z, H₀ z ≤ m) {S : Set (Vector κ)} (hS : IsCompact S)
    (he : ∀ z ∉ S, H₀ z = m) (d : κ → ℝ) {b T δ : ℝ}
    (hb : 0 < b) (hd : ∀ j, b ≤ d j) (hδ : 0 < δ) (hT : 0 ≤ T+δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z,
      ‖gradient (full H₀ d T δ) z-(2 : ℝ) • diag d z‖ ≤ B := by
   apply bound_remainder_of_compact (contDiff_full hH₀ d T δ) d
     (hS.union (compact_sublevel d hb hd hT))
   intro z hz
   have hzS : z ∉ S := fun h => hz (Or.inl h)
   have hzQ : T+δ < energy d z := lt_of_not_ge (fun h => hz (Or.inr h))
   rw [gradient_full hH₀, gradient_at_max hm (he z hzS),
     exteriorSlope_one hδ (by linarith), mul_one, zero_add]

 theorem full_flat {H₀ : Vector κ → ℝ} (d : κ → ℝ) {T δ : ℝ} (hδ : 0 < δ)
    {p : Vector κ} (hf : ∀ᶠ z in 𝓝 p, H₀ z = 0) (hp : energy d p < T) :
    ∀ᶠ z in 𝓝 p, full H₀ d T δ z = 0 := by
   have hq : ∀ᶠ z in 𝓝 p, energy d z < T :=
     (isOpen_lt (contDiff_energy d).continuous continuous_const).mem_nhds hp
   filter_upwards [hf,hq] with z hz hze
   simp only [full,hz,potential_zero d T hδ hze.le,add_zero]

end
end ExteriorHamiltonian

namespace ExteriorHamiltonian
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
variable {κ : Type u125} [Fintype κ]

 theorem action_nonpos {H : Vector κ → ℝ} {x : ℝ → Vector κ}
    (h : ∀ t, inner (𝕜 := ℝ) (gradient H (x t)) (x t)/2-H (x t) ≤ 0) :
    actionIntegral H x ≤ 0 := by
   rw [actionIntegral,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
   exact integral_nonpos h

 theorem gradient_of_constant_curve {H : Vector κ → ℝ} {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t)
    (hc : ∀ t, x t = x 0) (t : ℝ) : gradient H (x t) = 0 := by
   have he : x = fun _ => x 0 := funext hc
   have hd0 : HasDerivAt x 0 t := by
     convert! hasDerivAt_const t (x 0) using 1
   have hd := (hx t).unique hd0
   exact (smul_eq_zero.mp hd).resolve_left Complex.I_ne_zero

 theorem action_nonpos_of_constant {H : Vector κ → ℝ} (hH0 : ∀ z, 0 ≤ H z)
    {x : ℝ → Vector κ} (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t)
    (hc : ∀ t, x t = x 0) : actionIntegral H x ≤ 0 := by
   apply action_nonpos
   intro t
   rw [gradient_of_constant_curve hx hc t,inner_zero_left,zero_div,zero_sub]
   exact neg_nonpos.mpr (hH0 (x t))

 theorem high_orbit_nonpos (j₀ : κ) {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    {m : ℝ} (hm : ∀ z, H₀ z ≤ m) (hH₀0 : ∀ z, 0 ≤ H₀ z)
    (d : κ → ℝ) (hd : ∀ j, 0 ≤ d j) (hda : Real.pi < d j₀)
    (hdb : ∀ j, j ≠ j₀ → d j < Real.pi) (hda2 : d j₀ < 2*Real.pi)
    {T δ : ℝ} (hδ : 0 < δ) (hmag : Real.pi*(T+δ) < m*d j₀)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (full H₀ d T δ) (x t)) t)
    (hp : x 1 = x 0) (hplateau : ∀ t, H₀ (x t) = m) :
    actionIntegral (full H₀ d T δ) x ≤ 0 := by
   have he (t : ℝ) : gradient (full H₀ d T δ) (x t) =
       (2*exteriorSlope δ (energy d (x t)-T)) • diag d (x t) := by
     rw [gradient_full hH₀,gradient_at_max hm (hplateau t),zero_add]
   have hode (t : ℝ) := (hx t).congr_deriv (congrArg (fun z : Vector κ => Complex.I • z) (he t))
   have hQ (t : ℝ) := quadratic_constant d hode t 0
   let v := exteriorSlope δ (energy d (x 0)-T)
   have hv : 0 ≤ v := exteriorSlope_nonneg _ _
   have hv1 : v ≤ 1 := exteriorSlope_le_one _ _
   have hode' (t : ℝ) : HasDerivAt x (Complex.I • ((2*v) • diag d (x t))) t := by
     simpa only [hQ t] using hode t
   rcases diagonal_either j₀ d hv hv1 hd hdb hda2 hode' hp with heq | hc
   · have ha0 : 0 < d j₀ := Real.pi_pos.trans hda
     have hvlt : v < 1 := by nlinarith
     have hQt : energy d (x 0) < T+δ := by
       by_contra hn
       have hz : v = 1 := exteriorSlope_one hδ (by linarith)
       linarith
     have hvT : v*(T+δ) < m := by
       apply (mul_lt_mul_iff_left₀ ha0).mp
       calc
         (v*(T+δ))*d j₀ = Real.pi*(T+δ) := by rw [← heq]; ring
         _ < m*d j₀ := hmag
     apply action_nonpos
     intro t
     rw [he t,hQ t,real_inner_smul_left,← energy_eq_inner, hQ t]
     have hg := potential_nonneg d T hδ (x t)
     change (2*v)*energy d (x 0)/2-(H₀ (x t)+potential d T δ (x t)) ≤ 0
     rw [hplateau t]
     nlinarith [mul_le_mul_of_nonneg_left hQt.le hv]
   · apply action_nonpos_of_constant _ hx hc
     intro z
     exact add_nonneg (hH₀0 z) (potential_nonneg d T hδ z)

 theorem zero_vector_at_plateau {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    {m : ℝ} (hm : ∀ z, H₀ z ≤ m) (d : κ → ℝ) {T δ : ℝ} (hδ : 0 < δ)
    {U : Set (Vector κ)} (hU : ∀ z ∈ U, energy d z ≤ T)
    (he : ∀ z ∉ U, H₀ z = m) {z : Vector κ} (hz : full H₀ d T δ z = m) :
    gradient (full H₀ d T δ) z = 0 := by
   have hp : potential d T δ z = 0 := by
     by_cases hu : z ∈ U
     · exact potential_zero d T hδ (hU z hu)
     · have hh := he z hu
       change H₀ z+potential d T δ z=m at hz
       linarith
   have h0 : H₀ z = m := by simpa only [full,hp,add_zero] using hz
   change gradient (fun w => H₀ w+potential d T δ w) z = 0
   rw [gradient_sum hH₀ (contDiff_potential d T δ),gradient_at_max hm h0,
     gradient_at_min (potential_nonneg d T hδ) hp,add_zero]

 theorem all_orbits_nonpos (j₀ : κ) {H₀ : Vector κ → ℝ} (hH₀ : ContDiff ℝ ∞ H₀)
    {m : ℝ} (hm : ∀ z, H₀ z ≤ m) (hH₀0 : ∀ z, 0 ≤ H₀ z)
    (d : κ → ℝ) (hd : ∀ j, 0 ≤ d j) (hda : Real.pi < d j₀)
    (hdb : ∀ j, j ≠ j₀ → d j < Real.pi) (hda2 : d j₀ < 2*Real.pi)
    {T δ : ℝ} (hδ : 0 < δ) (hmag : Real.pi*(T+δ) < m*d j₀)
    {U : Set (Vector κ)} (hU : ∀ z ∈ U, energy d z ≤ T)
    (he : ∀ z ∉ U, H₀ z = m)
    (hslow : ∀ x : ℝ → Vector κ, (∀ t, x t ∈ U) → x 1 = x 0 →
      (∀ t, HasDerivAt x (Complex.I • gradient (full H₀ d T δ) (x t)) t) → ∀ t, x t = x 0)
    {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (full H₀ d T δ) (x t)) t)
    (hp : x 1 = x 0) : actionIntegral (full H₀ d T δ) x ≤ 0 := by
   have hH0 (z : Vector κ) : 0 ≤ full H₀ d T δ z :=
     add_nonneg (hH₀0 z) (potential_nonneg d T hδ z)
   have hE (t : ℝ) := energy_constant (contDiff_full hH₀ d T δ) hx t 0
   rcases lt_trichotomy (full H₀ d T δ (x 0)) m with hl | heq | hh
   · have hxt (t : ℝ) : x t ∈ U := by
       by_contra hn
       have hz := he (x t) hn
       have hg := potential_nonneg d T hδ (x t)
       have ht : full H₀ d T δ (x t) < m := by rw [hE t]; exact hl
       change H₀ (x t)+potential d T δ (x t) < m at ht
       linarith
     exact action_nonpos_of_constant hH0 hx (hslow x hxt hp hx)
   · apply action_nonpos_of_constant hH0 hx
     intro s
     apply zero_derivative_constant _ s 0
     intro t
     have hz := zero_vector_at_plateau hH₀ hm d hδ hU he ((hE t).trans heq)
     simpa only [hz,smul_zero] using hx t
   · apply high_orbit_nonpos j₀ hH₀ hm hH₀0 d hd hda hdb hda2 hδ hmag hx hp
     intro t
     apply he
     intro hu
     have hpz := potential_zero d T hδ (hU (x t) hu)
     have ht : m < full H₀ d T δ (x t) := by rw [hE t]; exact hh
     simp only [full,hpz,add_zero] at ht
     exact (not_lt_of_ge (hm (x t))) ht

end
end ExteriorHamiltonian

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles ExteriorHamiltonian
variable {κ : Type u126} [Fintype κ]

 theorem pushed_full_comp (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (r L ε : ℝ) (d : κ → ℝ) {T δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ z ∈ e.target, energy d z ≤ T) {z : Vector κ} (hz : z ∈ e.source) :
    full (pushed e r L ε) d T δ (e z) = radial r L ε z := by
   rw [full,pushed_apply e r L ε hz,potential_zero d T hδ (hQ _ (e.map_source hz)),add_zero]

 theorem pushed_full_slow (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source) (hω : ∀ z ∈ e.source, ComplexSymplectic.Preserves (fderiv ℝ e z))
    {r L ε : ℝ} (hs : e.source = domain L) (hr : 0 ≤ r) (hrπ : r < Real.pi)
    (hε : 0 < ε) (hL : ε ≤ L) (d : κ → ℝ) {T δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ z ∈ e.target, energy d z ≤ T)
    {x : ℝ → Vector κ} (hxt : ∀ t, x t ∈ e.target) (hp : x 1 = x 0)
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient (full (pushed e r L ε) d T δ) (x t)) t)
    (t : ℝ) : x t = x 0 := by
   have hD (z) (hz : z ∈ e.source) := ComplexSymplectic.invertible (hω z hz)
   have hH := contDiff_full (contDiff_pushed e he hs hD (r := r) hε hL) d T δ
   have hy (s : ℝ) := ComplexSymplectic.inverse_curve e he hω hH (contDiff_radial r L ε)
     (fun z hz => pushed_full_comp e r L ε d hδ hQ hz) hxt hx s
   have hp' : e.symm (x 1) = e.symm (x 0) := congrArg e.symm hp
   have hc := radial_slow hr hrπ hy hp' t
   have hh := congrArg e hc
   simpa only [e.right_inv (hxt t),e.right_inv (hxt 0)] using hh

 theorem pushed_plateau_outside (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    {r L ε : ℝ} (hs : e.source = domain L) (hε : 0 < ε) (hL : ε ≤ L)
    {z : Vector κ} (hz : z ∉ e.target) : pushed e r L ε z = ballHeight r L ε := by
   apply pushed_plateau e hε hL
   rintro ⟨x,hx,rfl⟩
   apply hz
   apply e.map_source
   rw [hs]
   exact core_subset_domain hε hL hx

end
end PushedBall

end NonsqueezingInline

end OAI
