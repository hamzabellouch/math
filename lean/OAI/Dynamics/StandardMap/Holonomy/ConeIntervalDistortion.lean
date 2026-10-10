import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Holonomy.FineStableGeometry
import OAI.Dynamics.StandardMap.Holonomy.FiniteOrbitDecay

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma LocalRecurrence.trapped_affine_derivative (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p V : Plane) (hcone : |V.1|≤|V.2|) (hV0 : V.2≠0)
    (x : ℝ) {N : ℕ} (hv : p+x•V∈r.extend.trappedBox N) :
    ∃ J : ℝ, HasDerivAt (fun t : ℝ => (r.trueOrbit (p+t•V) N).2) J x ∧
      J≠0 ∧ |Real.log |J|-Real.log |V.2|-(∑ j ∈ Finset.range N,Real.log |r.b j|)|≤
        4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  classical
  let L (n : ℕ) : Plane →L[ℝ] Plane := if n<N then D n (r.trueOrbit (p+x•V) n) else 0
  have hLs (n : ℕ) (hn : n<N) : ‖L n‖≤(δ : ℝ)*‖r.extend.orbit (p+x•V) n‖ := by
    dsimp only [L]
    rw [ite_eq_left hn,r.trueOrbit_eq_extend hv hn.le]
    exact hsmall n _ (hv n hn.le)
  have hL (n : ℕ) : ‖L n‖≤δ := by
    by_cases hn : n<N
    · exact (hLs n hn).trans ((mul_le_mul_of_nonneg_left (hv n hn.le) δ.coe_nonneg).trans_eq (mul_one _))
    · simp only [L,ite_eq_right hn,norm_zero]; exact δ.coe_nonneg
  let R := r.linearized L hL
  refine ⟨(R.orbit V N).2,?_,R.orbit_snd_ne_zero h hcone hV0 N,
    r.linearized_cone_log_distortion h hδ L hL hv hcone hV0 hLs⟩
  exact (r.trueOrbit_affine_hasDerivAt D hd L hL p V x (fun n hn => ite_eq_left hn) (le_refl N)).snd

theorem LocalRecurrence.affine_interval_distortion (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p V : Plane) (hcone : |V.1|≤|V.2|) (hV0 : V.2≠0)
    {t u : ℝ} (htu : t≤u) {N : ℕ}
    (ht : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t•V) n‖≤1/3)
    (hu : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+u•V) n‖≤1/3) :
    let A := Real.log |V.2|+∑ j ∈ Finset.range N,Real.log |r.b j|
    let C := 4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ))
    Real.exp (A-C)*(u-t)≤|(r.trueOrbit (p+u•V) N).2-(r.trueOrbit (p+t•V) N).2| ∧
      |(r.trueOrbit (p+u•V) N).2-(r.trueOrbit (p+t•V) N).2|≤Real.exp (A+C)*(u-t) := by
  dsimp only
  rcases htu.eq_or_lt with he | htu
  · subst u; simp
  let f : ℝ → ℝ := fun v => (r.trueOrbit (p+v•V) N).2
  have hfc : Continuous f := ((r.trueOrbit_continuous (fun n => continuous_iff_continuousAt.mpr
    fun v => (hd n v).continuousAt) N).comp (continuous_const.add (continuous_id.smul continuous_const))).snd
  have htrap (v : ℝ) (hv : v∈Icc t u) : (p+v•V)∈r.extend.trappedBox N :=
    r.extend.affine_interval_trapped h hcone hV0 p hv.1 hv.2 ht hu
  have hf (v : ℝ) (hv : v∈Icc t u) : ∃ J : ℝ, HasDerivAt f J v ∧ J≠0 ∧
      |Real.log |J|-Real.log |V.2|-(∑ j ∈ Finset.range N,Real.log |r.b j|)|≤
        4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) :=
    r.trapped_affine_derivative h hδ D hd hsmall p V hcone hV0 v (htrap v hv)
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope f htu hfc.continuousOn
    (fun v hv => (hf v ⟨hv.1.le,hv.2.le⟩).choose_spec.1.differentiableAt.differentiableWithinAt)
  obtain ⟨J,hJ,hJn,hJL⟩ := hf c ⟨hc.1.le,hc.2.le⟩
  rw [hJ.deriv] at he
  have hab : f u-f t=J*(u-t) := (eq_div_iff (sub_ne_zero.mpr htu.ne')).mp he |>.symm
  have heq : |f u-f t|=|J| *(u-t) := by rw [hab,abs_mul,abs_of_pos (sub_pos.mpr htu)]
  change _≤|f u-f t| ∧ |f u-f t|≤_
  rw [heq]
  have hJL' : |Real.log |J|-(Real.log |V.2|+∑ j ∈ Finset.range N,Real.log |r.b j|)|≤
      4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
    convert hJL using 1
    congr 1
    ring
  have hb := exp_bounds_of_log_error hJn hJL'
  exact ⟨mul_le_mul_of_nonneg_right hb.1 (sub_nonneg.mpr htu.le),
    mul_le_mul_of_nonneg_right hb.2 (sub_nonneg.mpr htu.le)⟩

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.pair_norm_eq_snd (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v w : Plane}
    (hv : |v.1-w.1|≤|v.2-w.2|) (n : ℕ) :
    ‖r.orbit v n-r.orbit w n‖=|(r.orbit v n).2-(r.orbit w n).2| := by
  change max _ _ = _
  exact max_eq_right (r.orbit_pair_cone h hv n).1

lemma Recurrence.exists_orbit_escape (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v w : Plane}
    (hv : |v.1-w.1|≤|v.2-w.2|) (hne : v.2≠w.2)
    {R : ℝ} (hw : ∀ n, ‖r.orbit w n‖≤R) : ∃ n, R<‖r.orbit v n‖ := by
  by_contra hn
  push Not at hn
  have hbound (n : ℕ) : |v.2-w.2|≤((ℓ+δ : ℝ≥0) : ℝ)^n*(2*R) := by
    have hb : |(r.orbit v n).2-(r.orbit w n).2|≤2*R :=
      (abs_sub _ _).trans (by
        have h₁ := (norm_snd_le (r.orbit v n)).trans (hn n)
        have h₂ := (norm_snd_le (r.orbit w n)).trans (hw n)
        simp only [Real.norm_eq_abs] at h₁ h₂
        linarith)
    exact (r.orbit_pair_cone h hv n).2.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (ℓ+δ).coe_nonneg
    (show ((ℓ+δ : ℝ≥0) : ℝ)<1 from h)).mul_const (2*R)
  have hz : |v.2-w.2|≤0 := by simpa only [zero_mul] using
    (le_of_tendsto_of_tendsto tendsto_const_nhds ht (Filter.Eventually.of_forall hbound))
  exact (abs_pos.mpr (sub_ne_zero.mpr hne)).not_ge hz

lemma last_trapped_time {P : ℕ → Prop} [DecidablePred P] (hbad : ∃ n, ¬P n)
    {N₀ : ℕ} (hprefix : ∀ n, n≤N₀ → P n) :
    ∃ N : ℕ, N₀≤N ∧ (∀ n, n≤N → P n) ∧ ¬P (N+1) := by
  let j := Nat.find hbad
  have hj : ¬P j := Nat.find_spec hbad
  have hmin (n : ℕ) (hn : n<j) : P n := by
    exact not_not.mp (Nat.find_min hbad hn)
  have hNj : N₀<j := by
    by_contra hh
    exact hj (hprefix j (le_of_not_gt hh))
  refine ⟨j-1,by omega,?_,?_⟩
  · intro n hn; exact hmin n (by omega)
  · have he : j-1+1=j := by omega
    rwa [he]

lemma Recurrence.escape_vertical_lower (r : Recurrence ℓ δ) (h : ℓ+δ<1)
    {v w : Plane} (hc : |v.1-w.1|≤|v.2-w.2|)
    {M a : ℝ} (hM : 0<M) (ha : 0<a)
    (hstep : ∀ n u, ‖r.step n u‖≤M*a^n*‖u‖) {N : ℕ}
    (hescape : 1/3<‖r.orbit v (N+1)‖)
    (hw : ‖r.orbit w N‖≤1/(6*M*a^N)) :
    1/(6*M*a^N)< |(r.orbit v N).2-(r.orbit w N).2| := by
  have hp : 0<M*a^N := mul_pos hM (pow_pos ha N)
  have hl : 1/(3*M*a^N)<‖r.orbit v N‖ := by
    have hh := hescape.trans_le (hstep N (r.orbit v N))
    apply (div_lt_iff₀ (by positivity : 0<3*M*a^N)).mpr
    nlinarith
  have hh := norm_add_le (r.orbit v N-r.orbit w N) (r.orbit w N)
  rw [sub_add_cancel,r.pair_norm_eq_snd h hc] at hh
  have he : 1/(3*M*a^N)=1/(6*M*a^N)+1/(6*M*a^N) := by field_simp; ring
  rw [he] at hl
  linarith

lemma terminal_size_comparison {p₀ p₁ q₀ q₁ ρ : ℝ} (hρ : 0<ρ)
    (hl : ρ< |(p₁-p₀)| ∨ ρ< |(q₁-q₀)|)
    (hpair₀ : |p₀-q₀|≤ρ/4) (hpair₁ : |p₁-q₁|≤ρ/4) :
    |q₁-q₀|≤2* |p₁-p₀| ∧ |p₁-p₀|≤2* |q₁-q₀| := by
  have he : (p₁-p₀)-(q₁-q₀)=(p₁-q₁)-(p₀-q₀) := by ring
  have hh : abs (abs (p₁-p₀)-abs (q₁-q₀))≤ρ/2 :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans (by
      rw [he]
      exact (abs_sub _ _).trans (by linarith))
  have hb := abs_le.mp hh
  rcases hl with hl|hl <;> constructor <;> linarith

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma LocalRecurrence.affine_interval_abs_distortion (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p V : Plane) (hc : |V.1|≤|V.2|) (hV : V.2≠0)
    {t u : ℝ} {N : ℕ}
    (ht : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t•V) n‖≤1/3)
    (hu : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+u•V) n‖≤1/3) :
    let A := Real.log |V.2|+∑ j ∈ Finset.range N,Real.log |r.b j|
    let C := 4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ))
    Real.exp (A-C)* |u-t|≤|(r.extend.orbit (p+u•V) N).2-(r.extend.orbit (p+t•V) N).2| ∧
      |(r.extend.orbit (p+u•V) N).2-(r.extend.orbit (p+t•V) N).2|≤Real.exp (A+C)* |u-t| := by
  dsimp only
  have ht' : p+t•V∈r.extend.trappedBox N := fun n hn => (ht n hn).trans (by norm_num)
  have hu' : p+u•V∈r.extend.trappedBox N := fun n hn => (hu n hn).trans (by norm_num)
  rcases le_total t u with htu|hut
  · have hh := r.affine_interval_distortion h hδ D hd hsmall p V hc hV htu ht hu
    rw [r.trueOrbit_eq_extend ht' le_rfl,r.trueOrbit_eq_extend hu' le_rfl] at hh
    simpa only [abs_of_nonneg (sub_nonneg.mpr htu)] using hh
  · have hh := r.affine_interval_distortion h hδ D hd hsmall p V hc hV hut hu ht
    rw [r.trueOrbit_eq_extend ht' le_rfl,r.trueOrbit_eq_extend hu' le_rfl] at hh
    rw [abs_sub_comm u t,abs_sub_comm ((r.extend.orbit (p+u•V) N).2)]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hut)] using hh

lemma relative_interval_ratio {A C p q P Q : ℝ}
    (hp : P≤Real.exp (A+C)*p) (hq : Real.exp (A-C)*q≤Q) (h : Q≤2*P) :
    q≤2*Real.exp (2*C)*p := by
  have he : Real.exp (A+C)=Real.exp (A-C)*Real.exp (2*C) := by
    rw [←Real.exp_add]; congr 1; ring
  rw [he] at hp
  have hh : Real.exp (A-C)*q≤Real.exp (A-C)*(2*Real.exp (2*C)*p) := by nlinarith
  exact (mul_le_mul_iff_right₀ (Real.exp_pos (A-C))).mp hh

theorem LocalRecurrence.finite_holonomy_ratio (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p q V : Plane) (hc : |V.1|≤|V.2|) (hV : V.2≠0)
    {t₀ t₁ u₀ u₁ : ℝ} {N : ℕ}
    (hp₀ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t₀•V) n‖≤1/3)
    (hp₁ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t₁•V) n‖≤1/3)
    (hq₀ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (q+u₀•V) n‖≤1/3)
    (hq₁ : ∀ n : ℕ,n≤N → ‖r.extend.orbit (q+u₁•V) n‖≤1/3)
    (hterminal : |(r.extend.orbit (q+u₁•V) N).2-(r.extend.orbit (q+u₀•V) N).2|≤
      2* |(r.extend.orbit (p+t₁•V) N).2-(r.extend.orbit (p+t₀•V) N).2|) :
    |u₁-u₀|≤(2*Real.exp (8*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ))))* |t₁-t₀| := by
  have hp := r.affine_interval_abs_distortion h hδ D hd hsmall p V hc hV hp₀ hp₁
  have hq := r.affine_interval_abs_distortion h hδ D hd hsmall q V hc hV hq₀ hq₁
  have hh := relative_interval_ratio hp.2 hq.1 hterminal
  convert hh using 1
  congr 2
  ring_nf

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma eventually_scaled_power_small {a b C d : ℝ} (ha : 0<a) (hb : 0≤b)
    (hab : a*b<1) (hd : 0<d) :
    ∀ᶠ n : ℕ in atTop, C*b^n≤d/a^n := by
  have ht : Tendsto (fun n : ℕ => C*(a*b)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg ha.le hb) hab).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds hd)] with n hn
  apply (le_div_iff₀ (pow_pos ha n)).mpr
  rw [mul_pow] at hn
  nlinarith

theorem LocalRecurrence.holonomy_local_bound (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    (p q V : Plane) (hc : |V.1|≤|V.2|) (hV : V.2≠0)
    (S : Set ℝ) (H : ℝ → ℝ) {t₀ : ℝ} (ht₀ : t₀∈S)
    (hH : ContinuousWithinAt H S t₀)
    {M a b B ρ : ℝ} (hM : 0<M) (ha : 0<a) (hb : 0≤b) (hb1 : b≤1)
    (hρ : 0≤ρ) (hab : a*b<1) (haρ : a*ρ<1)
    (hstep : ∀ n u, ‖r.extend.step n u‖≤M*a^n*‖u‖)
    (hp₀ : ∀ n, ‖r.extend.orbit (p+t₀•V) n‖≤b^n/12)
    (hq₀ : ∀ n, ‖r.extend.orbit (q+H t₀•V) n‖≤b^n/12)
    (htrack : ∀ t∈S, ∀ N : ℕ,
      (∀ n : ℕ,n≤N → ‖r.extend.orbit (p+t•V) n‖≤1/3) →
      (∀ n : ℕ,n≤N → ‖r.extend.orbit (q+H t•V) n‖≤1/3) →
      ‖r.extend.orbit (p+t•V) N-r.extend.orbit (q+H t•V) N‖≤B*ρ^N) :
    ∀ᶠ t in 𝓝[S] t₀,
      |H t-H t₀|≤(2*Real.exp (8*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ))))* |t-t₀| := by
  classical
  have hcentralP (n : ℕ) : ‖r.extend.orbit (p+t₀•V) n‖≤1/12 :=
    (hp₀ n).trans (div_le_div_of_nonneg_right (pow_le_one₀ hb hb1) (by norm_num))
  have hcentralQ (n : ℕ) : ‖r.extend.orbit (q+H t₀•V) n‖≤1/12 :=
    (hq₀ n).trans (div_le_div_of_nonneg_right (pow_le_one₀ hb hb1) (by norm_num))
  have hcentralP' (n : ℕ) : ‖r.extend.orbit (p+t₀•V) n‖≤1/3 := (hcentralP n).trans (by norm_num)
  have hcentralQ' (n : ℕ) : ‖r.extend.orbit (q+H t₀•V) n‖≤1/3 := (hcentralQ n).trans (by norm_num)
  have hdecay := eventually_scaled_power_small (C := (1:ℝ)/12) (d := 1/(6*M)) ha hb hab (by positivity)
  have hpair := eventually_scaled_power_small (C := B) (d := 1/(24*M)) ha hρ haρ (by positivity)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hdecay.and hpair)
  have hpre (n : ℕ) : ∀ᶠ t in 𝓝[S] t₀,
      ‖r.extend.orbit (p+t•V) n‖≤1/3 ∧ ‖r.extend.orbit (q+H t•V) n‖≤1/3 := by
    have hp : ContinuousAt (fun t : ℝ => ‖r.extend.orbit (p+t•V) n‖) t₀ :=
      ((r.extend.orbit_continuous n).comp (continuous_const.add (continuous_id.smul continuous_const))).norm.continuousAt
    have hq : ContinuousWithinAt (fun t : ℝ => ‖r.extend.orbit (q+H t•V) n‖) S t₀ :=
      (r.extend.orbit_continuous n).continuousAt.continuousWithinAt.comp
        (continuousWithinAt_const.add (hH.smul continuousWithinAt_const)) (mapsTo_univ _ _) |>.norm
    exact ((hp.eventually (gt_mem_nhds ((hcentralP n).trans_lt (by norm_num)))).filter_mono
      inf_le_left).and (hq.eventually (gt_mem_nhds ((hcentralQ n).trans_lt (by norm_num)))) |>.mono
        (fun t ht => ⟨ht.1.le,ht.2.le⟩)
  have hprefix : ∀ᶠ t in 𝓝[S] t₀, ∀ n∈Finset.range (N₀+1),
      ‖r.extend.orbit (p+t•V) n‖≤1/3 ∧ ‖r.extend.orbit (q+H t•V) n‖≤1/3 := by
    exact (Finset.eventually_all _).mpr (fun n hn => hpre n)
  filter_upwards [hprefix,self_mem_nhdsWithin] with t ht htS
  by_cases he : t=t₀
  · simp [he]
  have hcone (x y : ℝ) : |(p+x•V).1-(p+y•V).1|≤|(p+x•V).2-(p+y•V).2| := by
    change |p.1+x*V.1-(p.1+y*V.1)|≤|p.2+x*V.2-(p.2+y*V.2)|
    have h₁ : p.1+x*V.1-(p.1+y*V.1)=(x-y)*V.1 := by ring
    have h₂ : p.2+x*V.2-(p.2+y*V.2)=(x-y)*V.2 := by ring
    rw [h₁,h₂,abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  have hconeQ (x y : ℝ) : |(q+x•V).1-(q+y•V).1|≤|(q+x•V).2-(q+y•V).2| := by
    change |q.1+x*V.1-(q.1+y*V.1)|≤|q.2+x*V.2-(q.2+y*V.2)|
    have h₁ : q.1+x*V.1-(q.1+y*V.1)=(x-y)*V.1 := by ring
    have h₂ : q.2+x*V.2-(q.2+y*V.2)=(x-y)*V.2 := by ring
    rw [h₁,h₂,abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  have hne : (p+t•V).2≠(p+t₀•V).2 := by
    intro hh
    change p.2+t*V.2=p.2+t₀*V.2 at hh
    exact he (mul_right_cancel₀ hV (add_left_cancel hh))
  obtain ⟨j,hj⟩ := r.extend.exists_orbit_escape h (hcone t t₀) hne hcentralP'
  have hbad : ∃ n : ℕ, ¬(‖r.extend.orbit (p+t•V) n‖≤1/3 ∧
      ‖r.extend.orbit (q+H t•V) n‖≤1/3) := ⟨j,fun hh => hj.not_ge hh.1⟩
  obtain ⟨N,hN,htr,hout⟩ := last_trapped_time hbad (N₀ := N₀)
    (fun n hn => ht n (Finset.mem_range.mpr (by omega)))
  have hcentral (n : ℕ) (hn : N₀≤n) : b^n/12≤1/(6*M*a^n) := by
    have hh := (hN₀ n hn).1
    convert hh using 1 <;> ring
  have hpairbound : B*ρ^N≤(1/(6*M*a^N))/4 := by
    have hh := (hN₀ N hN).2
    convert hh using 1
    ring
  have hesc : 1/(6*M*a^N)< |(r.extend.orbit (p+t•V) N).2-(r.extend.orbit (p+t₀•V) N).2| ∨
      1/(6*M*a^N)< |(r.extend.orbit (q+H t•V) N).2-(r.extend.orbit (q+H t₀•V) N).2| := by
    push Not at hout
    by_cases hp : 1/3<‖r.extend.orbit (p+t•V) (N+1)‖
    · exact Or.inl (r.extend.escape_vertical_lower h (hcone t t₀) hM ha hstep hp
        ((hp₀ N).trans (hcentral N hN)))
    · exact Or.inr (r.extend.escape_vertical_lower h (hconeQ (H t) (H t₀)) hM ha hstep
        (hout (le_of_not_gt hp)) ((hq₀ N).trans (hcentral N hN)))
  have hpairs₀ : |(r.extend.orbit (p+t₀•V) N).2-(r.extend.orbit (q+H t₀•V) N).2|≤(1/(6*M*a^N))/4 := by
    exact (norm_snd_le _).trans ((htrack t₀ ht₀ N (fun n _ => hcentralP' n)
      (fun n _ => hcentralQ' n)).trans hpairbound)
  have hpairs₁ : |(r.extend.orbit (p+t•V) N).2-(r.extend.orbit (q+H t•V) N).2|≤(1/(6*M*a^N))/4 := by
    exact (norm_snd_le _).trans ((htrack t htS N (fun n hn => (htr n hn).1)
      (fun n hn => (htr n hn).2)).trans hpairbound)
  have hterminal := (terminal_size_comparison (by positivity : 0<(1/(6*M*a^N)))
    hesc hpairs₀ hpairs₁).1
  exact r.finite_holonomy_ratio h hδ D hd hsmall p q V hc hV
    (fun n _ => hcentralP' n) (fun n hn => (htr n hn).1)
    (fun n _ => hcentralQ' n) (fun n hn => (htr n hn).2) hterminal

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_trueOrbit (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    (v : RealPlane) (n : ℕ) :
    (fineLocalRecurrence k χ ε δ hδ w hw).trueOrbit v n=
      fineCoordinate k χ ε δ w (w+fineFrame k χ ε δ (complexProjection w) v) n := by
  induction n with
  | zero => exact (fineCoordinate_initial k χ ε hδ w (hw 0) v).symm
  | succ n ih => rw [LocalRecurrence.trueOrbit,ih,fineCoordinate_step]

theorem fineTrapped_hasDerivAt_log_distortion (k χ ε δ : ℝ) (hδ : 0<δ) (hδ' : δ≤1/2)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {v : RealPlane} {N : ℕ} (htrap : v∈fineTrapped k χ ε δ w N) :
    ∃ J : ℝ, HasDerivAt (fun t : ℝ =>
      (fineCoordinate k χ ε δ w (w+fineFrame k χ ε δ (complexProjection w) (v.1,t)) N).2) J v.2 ∧
      J≠0 ∧ abs (Real.log |J|-(∑ j ∈ Finset.range N,Real.log |fineUnstableMultiplier k χ ε δ
        (complexProjection ((standardLift k)^[j] w))|))≤4*δ/(1-(Real.exp (-χ+ε)+δ)) := by
  classical
  let r := fineLocalRecurrence k χ ε δ hδ w hw
  let D (j : ℕ) := fineRemainderDerivative k χ ε δ ((standardLift k)^[j] w)
  let L (j : ℕ) : Plane →L[ℝ] Plane := if j<N then D j (r.trueOrbit v j) else 0
  have hv : v∈r.extend.trappedBox N := fineTrapped_subset k χ ε δ hδ w hw N htrap
  have hLsmall (j : ℕ) (hj : j<N) : ‖L j‖≤δ*‖r.extend.orbit v j‖ := by
    dsimp only [L]
    rw [ite_eq_left hj,r.trueOrbit_eq_extend hv hj.le]
    have hh := fineRemainderDerivative_lipschitz k χ ε hδ ((standardLift k)^[j] w)
      (hw j) (fine_regular_lift_next k χ ε w hw j) (r.extend.orbit v j) 0
    simpa only [fineRemainderDerivative_zero,sub_zero] using hh
  have hL (j : ℕ) : ‖L j‖≤fineErrorRate δ hδ := by
    by_cases hj : j<N
    · exact (hLsmall j hj).trans ((mul_le_mul_of_nonneg_left (hv j hj.le) hδ.le).trans_eq (mul_one _))
    · simp only [L,ite_eq_right hj,norm_zero]; exact hδ.le
  let R := r.linearized L hL
  refine ⟨(R.orbit (0,1) N).2,?_,?_,?_⟩
  · have hd := r.trueOrbit_hasDerivAt D (fun j u => hasFDerivAt_fineRemainder k χ ε δ _ u)
      L hL (v := v) (N := N) (fun j hj => ite_eq_left hj) (le_refl N)
    have hs : HasDerivAt (fun t : ℝ => (r.trueOrbit (v.1,t) N).2) (R.orbit (0,1) N).2 v.2 :=
      by exact hd.snd
    simpa only [r,fine_trueOrbit] using hs
  · exact R.orbit_snd_ne_zero hq (v := (0,1)) (by norm_num) one_ne_zero N
  · exact r.linearized_log_distortion hq hδ' L hL hv hLsmall

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fineInverse_forward_bound (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖≤
      (Real.exp (2*ε))^n/(100*codingRadius k χ ε δ (complexProjection w)) := by
  have hr := codingRadius_pos k χ ε hδ (complexProjection w)
  have hh := fineInverse_forward_radius_bound k χ ε δ hδ w hw n
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

lemma fineCoordinate_tracking_rate (k χ ε δ : ℝ) (hδ : 0<δ) (w p p' : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {D b : ℝ} (hD : 0≤D) (hb : 0≤b)
    (htrack : ∀ n : ℕ, ‖(standardLift k)^[n] p-(standardLift k)^[n] p'‖≤D*b^n) (n : ℕ) :
    ‖fineCoordinate k χ ε δ w p n-fineCoordinate k χ ε δ w p' n‖≤
      (D/(100*codingRadius k χ ε δ (complexProjection w)))*(Real.exp (2*ε)*b)^n := by
  have he : fineCoordinate k χ ε δ w p n-fineCoordinate k χ ε δ w p' n=
      fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))
        ((standardLift k)^[n] p-(standardLift k)^[n] p') := by
    dsimp only [fineCoordinate]
    rw [←map_sub,sub_sub_sub_cancel_right]
  rw [he]
  calc
    _ ≤ ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))‖*
        ‖(standardLift k)^[n] p-(standardLift k)^[n] p'‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((Real.exp (2*ε))^n/(100*codingRadius k χ ε δ (complexProjection w)))*(D*b^n) :=
      (mul_le_mul_of_nonneg_left (htrack n) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (fineInverse_forward_bound k χ ε δ hδ w hw n)
          (mul_nonneg hD (pow_nonneg hb n)))
    _ = _ := by rw [mul_pow]; ring

theorem fine_extended_step_bound (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hε : 0≤ε) (hδ : 0<δ)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    ∃ M : ℝ, 0<M ∧ ∀ n u, ‖(fineLocalRecurrence k χ ε δ hδ w hw).extend.step n u‖≤
      M*(Real.exp (2*ε))^n*‖u‖ := by
  let a := Real.exp (2*ε)
  let R := codingRadius k χ ε δ (complexProjection w)
  let C := (a*(9*growthBase k)*(2*fineScale k ε δ))/(100*R)
  let r := fineLocalRecurrence k χ ε δ hδ w hw
  have ha : 1≤a := Real.one_le_exp_iff.mpr (by positivity)
  have hR : 0<R := codingRadius_pos k χ ε hδ _
  have hG : 0<growthBase k := by unfold growthBase; positivity
  have hC : 0<C := by dsimp [C,a]; positivity [fineScale_pos k ε hδ]
  refine ⟨C+δ,by positivity,fun n u => ?_⟩
  let z := complexProjection ((standardLift k)^[n] w)
  have hI : ‖fineInverse k χ ε δ (standardMap k z)‖≤a^(n+1)/(100*R) := by
    simpa only [z,Function.iterate_succ_apply',complexProjection_standardLift] using
      fineInverse_forward_bound k χ ε δ hδ w hw (n+1)
  have hF : ‖fineFrame k χ ε δ z‖≤2*fineScale k ε δ :=
    (fineFrame_norm_le k χ ε hδ z).trans (mul_le_mul_of_nonneg_left (fineSize_le_scale k χ ε hδ z) (by norm_num))
  have hdiag : ‖((r.a n*u.1,r.b n*u.2) : Plane)‖≤C*a^n*‖u‖ := by
    rw [show ((r.a n*u.1,r.b n*u.2) : Plane)=
      fineInverse k χ ε δ (standardMap k z) (standardDerivative k z (fineFrame k χ ε δ z u)) from
        (fine_derivative_diagonal k χ ε δ z (hw n) u).symm]
    calc
      _ ≤ ‖fineInverse k χ ε δ (standardMap k z)‖*
          (‖standardDerivative k z‖*(‖fineFrame k χ ε δ z‖*‖u‖)) :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ (a^(n+1)/(100*R))*((9*growthBase k)*((2*fineScale k ε δ)*‖u‖)) :=
        mul_le_mul hI (mul_le_mul (standardDerivative_norm_bound k hk z)
          (mul_le_mul_of_nonneg_right hF (norm_nonneg _)) (by positivity) (by positivity))
          (by positivity) (by positivity)
      _ = _ := by dsimp only [C]; rw [pow_succ]; ring
  have hrem : ‖r.extend.remainder n u‖≤δ*‖u‖ := by
    have ht := (r.extend.lipschitz n).dist_le_mul u 0
    change ‖r.extend.remainder n u-r.extend.remainder n 0‖≤δ*‖u-0‖ at ht
    rw [r.extend.zero,sub_zero,sub_zero] at ht
    exact ht
  have he : r.extend.step n u=((r.a n*u.1,r.b n*u.2) : Plane)+r.extend.remainder n u := rfl
  change ‖r.extend.step n u‖≤_
  rw [he]
  have hap : 1≤a^n := one_le_pow₀ ha
  have hh := (norm_add_le _ _).trans (add_le_add hdiag hrem)
  have hrem' : δ*‖u‖≤δ*a^n*‖u‖ := by
    have hh := mul_le_mul_of_nonneg_left hap hδ.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_right hh (norm_nonneg u)
  exact hh.trans (by nlinarith)

end StandardMapEntropy

end
end

end OAI
