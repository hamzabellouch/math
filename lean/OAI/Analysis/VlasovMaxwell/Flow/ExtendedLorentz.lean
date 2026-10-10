import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ConeMotion

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma exists_local_retarded_branch {X Y : ℝ → Vec} {s t : ℝ} {a : Vec}
    (hst : s < t) (hcone : t-s = ‖X t-Y s‖)
    (hX : ContDiffAt ℝ 1 X t) (hY : ContDiffAt ℝ 1 Y s)
    (hXd : HasDerivAt X a t) (ha : ‖a‖ < 1) :
    ∃ τ : ℝ → ℝ, τ s = t ∧ ContDiffAt ℝ 1 τ s ∧
      ∀ᶠ z in nhds s, z < τ z ∧ τ z-z = ‖X (τ z)-Y z‖ := by
  have hF := contDiffAt_squaredCone hX hY
  have hbound := dot_le_norm (X t-Y s) a
  rw [← hcone] at hbound
  have hpos : 0 < 2*(t-s)-2*dot (X t-Y s) a := by
    have hgap := mul_pos (sub_pos.mpr hst) (sub_pos.mpr ha)
    nlinarith
  have hinv : (fderiv ℝ (squaredCone X Y) (s,t) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    apply scalar_clm_invertible
    rw [receiver_partial_squaredCone hX hY hXd]
    exact ne_of_gt hpos
  let τ := hF.implicitFunction one_ne_zero hinv
  have hτ : τ s = t := hF.implicitFunction_apply_self one_ne_zero hinv
  have hτc : ContDiffAt ℝ 1 τ s := hF.contDiffAt_implicitFunction one_ne_zero hinv
  refine ⟨τ, hτ, hτc, ?_⟩
  have hsign : 0 < τ s-s := by rw [hτ]; exact sub_pos.mpr hst
  have hevent : ∀ᶠ z in nhds s, 0 < τ z-z :=
    (hτc.continuousAt.sub continuousAt_id) (isOpen_Ioi.mem_nhds hsign)
  filter_upwards [hF.eventually_apply_implicitFunction one_ne_zero hinv, hevent]
    with z hz hzn
  refine ⟨by linarith, ?_⟩
  dsimp [squaredCone] at hz
  rw [hcone, sub_self] at hz
  change (τ z-z)^2 - ‖X (τ z)-Y z‖^2 = 0 at hz
  have hn := norm_nonneg (X (τ z)-Y z)
  nlinarith

lemma derivative_retarded_branch {X Y : ℝ → Vec} {τ : ℝ → ℝ}
    {s t k : ℝ} {a u n : Vec}
    (hτ : τ s = t) (hst : s < t) (hgeom : X t-Y s = (t-s) • n)
    (hD : 1-dot n a ≠ 0)
    (hXd : HasDerivAt X a t) (hYd : HasDerivAt Y u s)
    (hτd : HasDerivAt τ k s)
    (heq : ∀ᶠ z in nhds s, (τ z-z)^2 = ‖X (τ z)-Y z‖^2) :
    k = (1-dot n u)/(1-dot n a) := by
  have hXτ : HasDerivAt (fun z => X (τ z)) (k • a) s := by
    exact (hτ ▸ hXd).scomp s hτd
  have hleft := (hτd.sub (hasDerivAt_id s)).pow 2
  have hright := ((hXτ.sub hYd).norm_sq)
  have hsame := (hleft.congr_of_eventuallyEq (Filter.EventuallyEq.symm heq)).unique hright
  simp only [Pi.sub_apply, id_eq, hτ, Nat.cast_ofNat, Nat.reduceSub, pow_one, ← dot_eq_inner,
    hgeom, dot_smul_left, dot_sub_right, dot_smul_right] at hsame
  apply (eq_div_iff hD).mpr
  have hr : t-s ≠ 0 := ne_of_gt (sub_pos.mpr hst)
  apply (mul_left_cancel₀ hr)
  nlinarith

lemma exists_local_retarded_branch_with_derivative {X Y : ℝ → Vec}
    {s t : ℝ} {a u n : Vec}
    (hst : s < t) (hgeom : X t-Y s = (t-s) • n) (hn : ‖n‖ = 1)
    (hX : ContDiffAt ℝ 1 X t) (hY : ContDiffAt ℝ 1 Y s)
    (hXd : HasDerivAt X a t) (hYd : HasDerivAt Y u s) (ha : ‖a‖ < 1) :
    ∃ τ : ℝ → ℝ, τ s = t ∧ ContDiffAt ℝ 1 τ s ∧
      HasDerivAt τ ((1-dot n u)/(1-dot n a)) s ∧
      ∀ᶠ z in nhds s, z < τ z ∧ τ z-z = ‖X (τ z)-Y z‖ := by
  have hcone : t-s = ‖X t-Y s‖ := by
    rw [hgeom, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hst), hn, mul_one]
  have hD : 1-dot n a ≠ 0 := by
    have hb := dot_le_norm n a
    rw [hn, one_mul] at hb
    linarith
  obtain ⟨τ, hτ, hτc, hevent⟩ := exists_local_retarded_branch hst hcone hX hY hXd ha
  have hτd := (hτc.differentiableAt one_ne_zero).hasDerivAt
  have heq : ∀ᶠ z in nhds s, (τ z-z)^2 = ‖X (τ z)-Y z‖^2 := by
    filter_upwards [hevent] with z hz using congrArg (fun r : ℝ => r^2) hz.2
  have hk := derivative_retarded_branch hτ hst hgeom hD hXd hYd hτd heq
  rw [hk] at hτd
  exact ⟨τ, hτ, hτc, hτd, hevent⟩

lemma hasDerivAt_cone_direction {X Y : ℝ → Vec} {τ : ℝ → ℝ}
    {s t k : ℝ} {a u n : Vec}
    (hτ : τ s = t) (hst : s < t) (hgeom : X t-Y s = (t-s) • n)
    (hXd : HasDerivAt X a t) (hYd : HasDerivAt Y u s)
    (hτd : HasDerivAt τ k s) :
    HasDerivAt (fun z => (τ z-z)⁻¹ • (X (τ z)-Y z))
      ((t-s)⁻¹ • (k • (a-n)+n-u)) s := by
  have hXτ : HasDerivAt (fun z => X (τ z)) (k • a) s :=
    (hτ ▸ hXd).scomp s hτd
  have hrad := hτd.sub (hasDerivAt_id s)
  have hr : τ s-s ≠ 0 := by simpa [hτ] using ne_of_gt (sub_pos.mpr hst)
  have h := (hrad.inv hr).smul (hXτ.sub hYd)
  convert h using 1 <;> try rfl
  simp only [Pi.inv_apply, Pi.sub_apply, id_eq, hτ, hgeom]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have hts : t-s ≠ 0 := ne_of_gt (sub_pos.mpr hst)
  field_simp
  ring

lemma hasDerivAt_particle_energy {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => q (V t)) (dot (velocity (V s)) K) s := by
  have hp : 1+‖V s‖^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hV.norm_sq).const_add 1).sqrt hp
  convert h using 1 <;> try rfl
  rw [velocity, dot_smul_left, dot_eq_inner]
  dsimp [q]
  have hq : Real.sqrt (1+‖V s‖^2) ≠ 0 := ne_of_gt (q_pos (V s))
  field_simp

lemma hasDerivAt_particle_velocity {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => velocity (V t))
      ((q (V s))⁻¹ • (K-dot (velocity (V s)) K • velocity (V s))) s := by
  have hq := hasDerivAt_particle_energy hV
  have h := (hq.inv (ne_of_gt (q_pos (V s)))).smul hV
  convert h using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply, velocity, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma dot_cross_self_left (a b : Vec) : dot a (cross a b) = 0 := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

lemma hasDerivAt_lorentz_energy {V : ℝ → Vec} {E B : Vec} {s : ℝ}
    (hV : HasDerivAt V (E+cross (velocity (V s)) B) s) :
    HasDerivAt (fun t => q (V t)) (dot (velocity (V s)) E) s := by
  simpa only [dot_add_right, dot_cross_self_left, add_zero] using hasDerivAt_particle_energy hV

lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

lemma contDiff_cross {k : ℕ∞ω} : ContDiff ℝ k (fun z : Vec × Vec => cross z.1 z.2) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 1 * z.2 2 - z.1 2 * z.2 1)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 2 * z.2 0 - z.1 0 * z.2 2)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 0 * z.2 1 - z.1 1 * z.2 0)
    fun_prop

def extendedLorentz (E B : Field) (z : ℝ × Phase) : ℝ × Phase :=
  (1, velocity z.2.2, E (z.1,z.2.1)+cross (velocity z.2.2) (B (z.1,z.2.1)))

lemma contDiffAt_extendedLorentz {E B : Field} {t : ℝ} {x v : Vec}
    (hE : ContDiffAt ℝ 1 E (t,x)) (hB : ContDiffAt ℝ 1 B (t,x)) :
    ContDiffAt ℝ 1 (extendedLorentz E B) (t,x,v) := by
  have htx : ContDiffAt ℝ 1 (fun z : ℝ × Phase => (z.1,z.2.1)) (t,x,v) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.fst)
  have hv : ContDiffAt ℝ 1 (fun z : ℝ × Phase => velocity z.2.2) (t,x,v) :=
    contDiff_velocity.contDiffAt.comp _ (contDiffAt_snd.snd)
  have hE' : ContDiffAt ℝ 1 (fun z : ℝ × Phase => E (z.1,z.2.1)) (t,x,v) :=
    hE.comp (t,x,v) htx
  have hB' : ContDiffAt ℝ 1 (fun z : ℝ × Phase => B (z.1,z.2.1)) (t,x,v) :=
    hB.comp (t,x,v) htx
  exact contDiffAt_const.prodMk (hv.prodMk
    (hE'.add (contDiff_cross.contDiffAt.comp (t,x,v) (hv.prodMk hB'))))

lemma exists_local_characteristic {E B : Field} {t₀ : ℝ} {x₀ v₀ : Vec}
    (hE : ContDiffAt ℝ 1 E (t₀,x₀)) (hB : ContDiffAt ℝ 1 B (t₀,x₀)) :
    ∃ X V : ℝ → Vec, X t₀ = x₀ ∧ V t₀ = v₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀-ε) (t₀+ε),
        HasDerivAt X (velocity (V t)) t ∧
        HasDerivAt V (E (t,X t)+cross (velocity (V t)) (B (t,X t))) t := by
  obtain ⟨α, hα₀, ε, hε, hα⟩ :=
    (contDiffAt_extendedLorentz (v := v₀) hE hB).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have ht₀ : t₀ ∈ Ioo (t₀-ε) (t₀+ε) := by constructor <;> linarith
  have hdtime (t) (ht : t ∈ Ioo (t₀-ε) (t₀+ε)) :
      HasDerivAt (fun s => (α s).1-s) 0 t := by
    have h : HasDerivAt (fun s => (α s).1) 1 t := by
      simpa [extendedLorentz] using (hα t ht).hasFDerivAt.fst.hasDerivAt
    convert h.sub (hasDerivAt_id t) using 1 <;> try rfl
    norm_num
  have htime (t) (ht : t ∈ Ioo (t₀-ε) (t₀+ε)) : (α t).1 = t := by
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (t₀-ε) (t₀+ε)).isPreconnected
      (fun s hs => (hdtime s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hdtime s hs).deriv) ht ht₀
    have hz : (α t).1-t = 0 := by simpa [hα₀] using hc
    exact sub_eq_zero.mp hz
  refine ⟨fun t => (α t).2.1, fun t => (α t).2.2, ?_, ?_, ε, hε, ?_⟩
  · simp [hα₀]
  · simp [hα₀]
  · intro t ht
    constructor
    · simpa [extendedLorentz] using (hα t ht).hasFDerivAt.snd.fst.hasDerivAt
    · simpa [extendedLorentz, htime t ht] using (hα t ht).hasFDerivAt.snd.snd.hasDerivAt

lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma full_directional_derivative {f : Particle} {t : ℝ} {x v u K : Vec}
    (hf : DifferentiableAt ℝ f (t,x,v)) :
    fderiv ℝ f (t,x,v) (1,u,K) =
      deriv (fun t' => f (t',x,v)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,v)) x i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,x,v')) v i) := by
  let L := fderiv ℝ f (t,x,v)
  have hT := hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (x,v)))
  have hιX : HasFDerivAt (fun y : Vec => (t,y,v))
      ((0 : Vec →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Vec).prod 0)) x := by
    exact (hasFDerivAt_const t x).prodMk
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const v x))
  have hιV : HasFDerivAt (fun y : Vec => (t,x,y))
      ((0 : Vec →L[ℝ] ℝ).prod ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec))) v := by
    exact (hasFDerivAt_const t v).prodMk
      ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))
  have hX := hf.hasFDerivAt.comp x hιX
  have hV := hf.hasFDerivAt.comp v hιV
  have ht : deriv (fun t' => f (t',x,v)) t = L (1,0,0) := by
    convert hT.deriv using 1
    rfl
  have hx : fderiv ℝ (fun y => f (t,y,v)) x u = L (0,u,0) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F u) hX.fderiv
    convert h using 1 <;> rfl
  have hv : fderiv ℝ (fun v' => f (t,x,v')) v K = L (0,0,K) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F K) hV.fderiv
    convert h using 1 <;> rfl
  change L (1,u,K) = deriv (fun t' => f (t',x,v)) t +
    (∑ i : Fin 3, u i * fderiv ℝ (fun y => f (t,y,v)) x (basis i)) +
    (∑ i : Fin 3, K i * fderiv ℝ (fun v' => f (t,x,v')) v (basis i))
  rw [← clm_sum_basis, ← clm_sum_basis, ht, hx, hv]
  rw [← map_add, ← map_add]
  congr 1
  ext <;> simp

lemma hasDerivAt_particle_along_curve {f : Particle} {X V : ℝ → Vec}
    {t : ℝ} {u K : Vec} (hf : DifferentiableAt ℝ f (t,X t,V t))
    (hX : HasDerivAt X u t) (hV : HasDerivAt V K t) :
    HasDerivAt (fun s => f (s,X s,V s))
      (deriv (fun s => f (s,X t,V t)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,V t)) (X t) i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,X t,v')) (V t) i)) t := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hX.prodMk hV))
  rw [full_directional_derivative hf] at h
  exact h

lemma particle_differentiableAt_positive {s : Solution}
    (hreg : ContDiffOn ℝ 1 s.f particleHalfSpace) {t : ℝ} (ht : 0 < t) (x v : Vec) :
    DifferentiableAt ℝ s.f (t,x,v) := by
  have hnhds : particleHalfSpace ∈ nhds (t,x,v) := by
    have hopen : IsOpen {z : ℝ × Phase | 0 < z.1} :=
      isOpen_lt continuous_const continuous_fst
    apply Filter.mem_of_superset (hopen.mem_nhds ht)
    intro z hz
    change 0 ≤ z.1
    exact le_of_lt hz
  exact ((hreg (t,x,v) ht.le).contDiffAt hnhds).differentiableAt (by norm_num)

lemma hasDerivAt_transport_zero {s : Solution} {X V : ℝ → Vec} {t : ℝ}
    (hreg : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : Equations s) (ht : 0 < t)
    (hX : HasDerivAt X (velocity (V t)) t)
    (hV : HasDerivAt V (s.E (t,X t) + cross (velocity (V t)) (s.B (t,X t))) t) :
    HasDerivAt (fun r => s.f (r,X r,V r)) 0 t := by
  have hf := hasDerivAt_particle_along_curve
    (particle_differentiableAt_positive hreg ht (X t) (V t)) hX hV
  have hpde := (heq t ht.le).1 (X t) (V t)
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at hpde
  exact hpde ▸ hf

lemma transport_on_characteristic {s : Solution} {X V : ℝ → Vec} {a b : ℝ}
    (hreg : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : Equations s)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hXc : ContinuousOn X (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hX : ∀ t ∈ Ioo a b, HasDerivAt X (velocity (V t)) t)
    (hV : ∀ t ∈ Ioo a b,
      HasDerivAt V (s.E (t,X t) + cross (velocity (V t)) (s.B (t,X t))) t) :
    s.f (b,X b,V b) = s.f (a,X a,V a) := by
  rcases hab.eq_or_lt with h | h
  · simp [h]
  have hc : ContinuousOn (fun t => s.f (t,X t,V t)) (Icc a b) :=
    hreg.continuousOn.comp (continuousOn_id.prodMk (hXc.prodMk hVc))
      (fun t ht => ha.trans ht.1)
  have hd : ∀ t ∈ Ioo a b, HasDerivAt (fun r => s.f (r,X r,V r)) (0 : ℝ) t :=
    fun t ht => hasDerivAt_transport_zero hreg heq (ha.trans_lt ht.1) (hX t ht) (hV t ht)
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope (fun r => s.f (r,X r,V r)) (fun _ => 0) h hc hd
  have hnum : s.f (b,X b,V b) - s.f (a,X a,V a) = 0 := by
    exact (div_eq_zero_iff.mp he.symm).resolve_right (sub_ne_zero.mpr (ne_of_gt h))
  exact sub_eq_zero.mp hnum

lemma dot_cross_cycle (a b c : Vec) : dot a (cross b c) = dot b (cross c a) := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

lemma cross_antisymm (a b : Vec) : cross a b = -cross b a := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_dot_square (a b : Vec) :
    dot (cross a b) (cross a b) = dot a a * dot b b - (dot a b)^2 := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

lemma norm_cross_le (a b : Vec) : ‖cross a b‖ ≤ ‖a‖*‖b‖ := by
  have h := cross_dot_square a b
  simp only [dot_self] at h
  nlinarith [norm_nonneg (cross a b), norm_nonneg a, norm_nonneg b,
    mul_nonneg (norm_nonneg a) (norm_nonneg b), sq_nonneg (dot a b)]

lemma poynting_norm_le_energy (E B : Vec) :
    ‖cross E B‖ ≤ (‖E‖^2+‖B‖^2)/2 := by
  have h := norm_cross_le E B
  nlinarith [sq_nonneg (‖E‖-‖B‖)]

lemma field_cone_energy_identity (E B n : Vec) (hn : ‖n‖ = 1) :
    (‖E‖^2+‖B‖^2)/2-dot n (cross E B) =
      (‖E+cross n B‖^2+(dot n B)^2)/2 := by
  have hcross := cross_dot_square n B
  rw [dot_self, dot_self, dot_self, hn] at hcross
  rw [norm_add_sq_real, ← dot_eq_inner]
  have he : dot E (cross n B) = -dot n (cross E B) := by
    rw [dot_cross_cycle, cross_antisymm B E]
    simp [dot, Finset.sum_neg_distrib]
  rw [he]
  nlinarith

lemma good_field_square_le_flux (E B n : Vec) (hn : ‖n‖ = 1) :
    (‖E+cross n B‖+|dot n B|)^2 ≤
      4*((‖E‖^2+‖B‖^2)/2-dot n (cross E B)) := by
  rw [field_cone_energy_identity E B n hn]
  nlinarith [sq_abs (dot n B), sq_nonneg (‖E+cross n B‖-|dot n B|)]

lemma fderiv_velocity_apply (v h : Vec) :
    fderiv ℝ velocity v h = (q v)⁻¹ • (h-dot (velocity v) h • velocity v) := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt velocity (fderiv ℝ velocity v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_velocity hc
  have he := h₁.unique h₂
  simpa using he

lemma spatialPartial_velocity (v : Vec) (i j : Fin 3) :
    spatialPartial (fun w => velocity w j) v i =
      (q v)⁻¹ * ((if i=j then 1 else 0)-velocity v i*velocity v j) := by
  have hv : DifferentiableAt ℝ velocity v := contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v
  have hj := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp v hv.hasFDerivAt
  have hp := congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i)) hj.fderiv
  have h : spatialPartial (fun w => velocity w j) v i =
      (fderiv ℝ velocity v (basis i)) j := by
    convert hp using 1 <;> rfl
  rw [h, fderiv_velocity_apply]
  simp [basis, dot, eq_comm]

lemma spatialPartial_mul {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y*g y) x i =
      f x*spatialPartial g x i+g x*spatialPartial f x i := by
  change fderiv ℝ (f*g) x (basis i) = _
  rw [fderiv_mul hf hg]
  rfl

lemma spatialPartial_sub {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y-g y) x i =
      spatialPartial f x i-spatialPartial g x i := by
  change fderiv ℝ (f-g) x (basis i) = _
  rw [fderiv_sub hf hg]
  rfl

lemma divergence_magnetic_force (v B : Vec) :
    divergence (fun w => cross (velocity w) B) v = 0 := by
  have hd (j : Fin 3) : DifferentiableAt ℝ (fun w : Vec => velocity w j) v :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) j).differentiableAt.comp v
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v)
  simp only [divergence, Fin.sum_univ_succ]
  change spatialPartial (fun w => velocity w 1 * B 2 - velocity w 2 * B 1) v 0 +
    (spatialPartial (fun w => velocity w 2 * B 0 - velocity w 0 * B 2) v 1 +
    (spatialPartial (fun w => velocity w 0 * B 1 - velocity w 1 * B 0) v 2 + 0)) = 0
  simp only [spatialPartial_sub ((hd _).mul_const _) ((hd _).mul_const _),
    spatialPartial_mul (hd _) (differentiableAt_const _), spatialPartial_velocity]
  simp [spatialPartial]
  ring

lemma divergence_cross {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => cross (F y) (G y)) x =
      dot (G x) (curl F x) - dot (F x) (curl G x) := by
  have hf (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF
  have hg (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG
  simp only [divergence, Fin.sum_univ_succ]
  change spatialPartial (fun y => F y 1 * G y 2 - F y 2 * G y 1) x 0 +
    (spatialPartial (fun y => F y 2 * G y 0 - F y 0 * G y 2) x 1 +
    (spatialPartial (fun y => F y 0 * G y 1 - F y 1 * G y 0) x 2+0)) = _
  have hm (i j k : Fin 3) :
      spatialPartial ((fun y => F y i) * (fun y => G y j)) x k =
        F x i * spatialPartial (fun y => G y j) x k +
        G x j * spatialPartial (fun y => F y i) x k :=
    spatialPartial_mul (hf i) (hg j) k
  have hs (i j k l r : Fin 3) := spatialPartial_sub ((hf i).mul (hg j)) ((hf k).mul (hg l)) r
  simp only [Pi.mul_apply] at hs
  simp only [hs, hm]
  simp [dot, curl, Fin.sum_univ_succ]
  ring

lemma hasDerivAt_field_energy {E B : ℝ → Vec} {e b : Vec} {t : ℝ}
    (he : HasDerivAt E e t) (hb : HasDerivAt B b t) :
    HasDerivAt (fun s => (‖E s‖^2+‖B s‖^2)/2)
      (dot (E t) e + dot (B t) b) t := by
  convert (he.norm_sq.add hb.norm_sq).div_const 2 using 1
  rw [← dot_eq_inner, ← dot_eq_inner]
  ring

lemma maxwell_energy_balance {E B : Field} {j : Vec} {t : ℝ} {x : Vec}
    (hE : DifferentiableAt ℝ E (t,x)) (hB : DifferentiableAt ℝ B (t,x))
    (he : deriv (fun s => E (s,x)) t - curl (fun y => B (t,y)) x = -j)
    (hb : deriv (fun s => B (s,x)) t + curl (fun y => E (t,y)) x = 0) :
    deriv (fun s => (‖E (s,x)‖^2+‖B (s,x)‖^2)/2) t +
      divergence (fun y => cross (E (t,y)) (B (t,y))) x = -dot (E (t,x)) j := by
  have heT : DifferentiableAt ℝ (fun s => E (s,x)) t :=
    hE.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hbT : DifferentiableAt ℝ (fun s => B (s,x)) t :=
    hB.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have heX : DifferentiableAt ℝ (fun y => E (t,y)) x :=
    hE.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hbX : DifferentiableAt ℝ (fun y => B (t,y)) x :=
    hB.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  rw [(hasDerivAt_field_energy heT.hasDerivAt hbT.hasDerivAt).deriv,
    divergence_cross heX hbX]
  have he' : deriv (fun s => E (s,x)) t = curl (fun y => B (t,y)) x-j := by
    apply sub_eq_iff_eq_add.mp at he
    simpa only [sub_eq_add_neg, add_comm] using he
  have hb' : deriv (fun s => B (s,x)) t = -curl (fun y => E (t,y)) x :=
    eq_neg_of_add_eq_zero_left hb
  rw [he', hb']
  simp only [dot, PiLp.sub_apply, PiLp.neg_apply, mul_sub, mul_neg,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end RVM
end

end OAI
