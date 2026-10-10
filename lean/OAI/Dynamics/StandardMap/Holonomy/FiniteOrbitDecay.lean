import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Holonomy.DerivativeQuantitative

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.stable_cone_backward (r : Recurrence ℓ δ) (h : ℓ+δ<1) (n : ℕ) (v : Plane)
    (hv : |(r.step n v).2|≤|(r.step n v).1|) :
    |v.2|≤|v.1| ∧ ‖r.step n v‖≤((ℓ+δ : ℝ≥0) : ℝ)*‖v‖ := by
  let q : ℝ := ((ℓ+δ : ℝ≥0) : ℝ)
  have hq0 : 0≤q := (ℓ+δ).coe_nonneg
  have hq1 : q<1 := h
  have hn : ‖r.step n v‖=|(r.step n v).1| := max_eq_left hv
  have hf : ‖r.step n v‖≤q*‖v‖ := by
    rw [hn]
    simpa only [r.step_zero,Prod.fst_zero,sub_zero] using step_fst_sub_bound r n v 0
  refine ⟨?_,hf⟩
  by_contra hc
  have hc' : |v.1| < |v.2| := lt_of_not_ge hc
  have hp : 0<‖v‖ := by
    rw [show ‖v‖=|v.2| from max_eq_right hc'.le]
    exact (abs_nonneg _).trans_lt hc'
  have hb := (r.unstable_cone_step h n v 0 (by simpa only [Prod.fst_zero,Prod.snd_zero,sub_zero] using hc'.le)).2
  simp only [r.step_zero,Prod.snd_zero,sub_zero] at hb
  have hnb : ‖v‖≤q*‖r.step n v‖ := by
    rw [show ‖v‖=|v.2| from max_eq_right hc'.le]
    have hsnd : |(r.step n v).2|≤‖r.step n v‖ := norm_snd_le (r.step n v)
    exact hb.trans (mul_le_mul_of_nonneg_left hsnd hq0)
  have hh := mul_le_mul_of_nonneg_left hf hq0
  have hsqr : q*q<1 := by nlinarith
  nlinarith

lemma Recurrence.stable_orbit_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (v : Plane) (n : ℕ)
    (hv : |(r.orbit v n).2|≤|(r.orbit v n).1|) :
    ‖r.orbit v n‖≤((ℓ+δ : ℝ≥0) : ℝ)^n*‖v‖ := by
  induction n with
  | zero => simp only [Recurrence.orbit,pow_zero,one_mul,le_refl]
  | succ n ih =>
    have hh := r.stable_cone_backward h n (r.orbit v n) hv
    exact hh.2.trans ((mul_le_mul_of_nonneg_left (ih hh.1) (ℓ+δ).coe_nonneg).trans_eq (by rw [pow_succ]; ring))

lemma Recurrence.unstable_orbit_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (v : Plane)
    (hv : |v.1|≤|v.2|) (n : ℕ) :
    ‖v‖≤((ℓ+δ : ℝ≥0) : ℝ)^n*‖r.orbit v n‖ := by
  induction n with
  | zero => simp only [Recurrence.orbit,pow_zero,one_mul,le_refl]
  | succ n ih =>
    have hh := (r.orbit_cone h hv n).2
    rw [←r.orbit_norm_eq_snd h hv n,←r.orbit_norm_eq_snd h hv (n+1)] at hh
    exact ih.trans ((mul_le_mul_of_nonneg_left hh (pow_nonneg (ℓ+δ).coe_nonneg n)).trans_eq (by rw [pow_succ]; ring))

lemma Recurrence.orbit_tail (r : Recurrence ℓ δ) (v : Plane) (j n : ℕ) :
    (r.tail j).orbit (r.orbit v j) n=r.orbit v (j+n) := by
  induction n with
  | zero => simp only [Recurrence.orbit,Nat.add_zero]
  | succ n ih =>
    rw [Recurrence.orbit,Nat.add_succ,Recurrence.orbit,ih]
    rfl

lemma Recurrence.trappedBox_two_ended (r : Recurrence ℓ δ) (h : ℓ+δ<1) {N : ℕ} {v : Plane}
    (hv : v∈r.trappedBox N) {j : ℕ} (hj : j≤N) :
    ‖r.orbit v j‖≤((ℓ+δ : ℝ≥0) : ℝ)^j+((ℓ+δ : ℝ≥0) : ℝ)^(N-j) := by
  rcases le_total |(r.orbit v j).1| |(r.orbit v j).2| with hc|hc
  · have hh := (r.tail j).unstable_orbit_bound h (r.orbit v j) hc (N-j)
    rw [r.orbit_tail,Nat.add_sub_of_le hj] at hh
    have he := hh.trans ((mul_le_mul_of_nonneg_left (hv N le_rfl) (pow_nonneg (ℓ+δ).coe_nonneg _)).trans_eq (mul_one _))
    exact he.trans (le_add_of_nonneg_left (pow_nonneg (ℓ+δ).coe_nonneg j))
  · have hh := r.stable_orbit_bound h v j hc
    have he := hh.trans ((mul_le_mul_of_nonneg_left (hv 0 (Nat.zero_le N)) (pow_nonneg (ℓ+δ).coe_nonneg _)).trans_eq (mul_one _))
    exact he.trans (le_add_of_nonneg_right (pow_nonneg (ℓ+δ).coe_nonneg (N-j)))

lemma geometric_partial_bound {q : ℝ} (hq0 : 0≤q) (hq1 : q<1) (N : ℕ) :
    (∑ j ∈ Finset.range N,q^j)≤1/(1-q) := by
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hq0 N]

lemma Recurrence.trappedBox_sum_norm (r : Recurrence ℓ δ) (h : ℓ+δ<1) {N : ℕ} {v : Plane}
    (hv : v∈r.trappedBox N) :
    (∑ j ∈ Finset.range N,‖r.orbit v j‖)≤2/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  let q : ℝ := ((ℓ+δ : ℝ≥0) : ℝ)
  have hq0 : 0≤q := (ℓ+δ).coe_nonneg
  have hq1 : q<1 := h
  have hb : (∑ j ∈ Finset.range N,q^(N-j))≤1/(1-q) := by
    have hh := StandardMapEntropy.sum_of_backward_contraction (fun j => q^(N-j)) (fun _ => pow_nonneg hq0 _)
      hq0 hq1 N (fun j hj => ?_)
    · simpa only [Nat.sub_self,pow_zero] using hh
    · have he : N-j=N-(j+1)+1 := by omega
      rw [he,pow_succ]
      exact le_of_eq (mul_comm _ _)
  calc
    _ ≤ ∑ j ∈ Finset.range N,(q^j+q^(N-j)) :=
      Finset.sum_le_sum fun j hj => r.trappedBox_two_ended h hv (Finset.mem_range.mp hj).le
    _ = (∑ j ∈ Finset.range N,q^j)+(∑ j ∈ Finset.range N,q^(N-j)) := Finset.sum_add_distrib
    _ ≤ 1/(1-q)+1/(1-q) := add_le_add (geometric_partial_bound hq0 hq1 N) hb
    _ = _ := by ring

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma scalar_log_relative_error {b y e d : ℝ} (hb : 1≤|b|) (hy : y≠0)
    (hd0 : 0≤d) (hd1 : d≤1/2) (he : |e|≤d*|y|) :
    abs (Real.log |b*y+e|-Real.log |b|-Real.log |y|)≤2*d := by
  have hyp : 0 < |y| := abs_pos.mpr hy
  have hbp : 0 < |b| := lt_of_lt_of_le zero_lt_one hb
  have hsmall : |e|≤|y|/2 := he.trans (by
    nlinarith [mul_le_mul hd1 (le_refl |y|) hyp.le (hd0.trans hd1)])
  have hlower : |y|/2≤|b*y+e| := by
    have hh : |b*y|≤|b*y+e|+|e| := by
      simpa only [add_sub_cancel_right] using abs_sub (b*y+e) e
    rw [abs_mul] at hh
    have hb' := mul_le_mul_of_nonneg_right hb (abs_nonneg y)
    nlinarith
  have hD : 0<2/|y| := div_pos (by norm_num) hyp
  have hx : 1≤(2/|y|)*|b*y+e| := by
    have hc := mul_le_mul_of_nonneg_left hlower hD.le
    have heq : (2/|y|)*(|y|/2)=1 := by field_simp
    rwa [heq] at hc
  have hb' : 1≤(2/|y|)*|b*y| := by
    rw [abs_mul]
    have heq : (2/|y|)*(|b| *|y|)=2*|b| := by field_simp
    rw [heq]; linarith
  have hl := StandardMapEntropy.log_difference_of_lower hD hx hb'
  have hnorm : abs (|b*y+e|-|b*y|)≤|e| := by
    simpa only [add_sub_cancel_left] using abs_abs_sub_abs_le_abs_sub (b*y+e) (b*y)
  have hh := hl.trans (mul_le_mul_of_nonneg_left (hnorm.trans he) hD.le)
  rw [abs_mul,Real.log_mul hbp.ne' hyp.ne'] at hh
  have hright : (2/|y|)*(d*|y|)=2*d := by field_simp
  rw [hright] at hh
  convert hh using 1
  congr 1
  ring

theorem LocalRecurrence.linearized_log_distortion (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ)
    {N : ℕ} {v : Plane} (hv : v∈r.extend.trappedBox N)
    (hsmall : ∀ j : ℕ,j<N → ‖D j‖≤(δ : ℝ)*‖r.extend.orbit v j‖) :
    abs (Real.log |((r.linearized D hD).orbit (0,1) N).2|-
      ∑ j ∈ Finset.range N,Real.log |r.b j|)≤4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  let R := r.linearized D hD
  let y := fun j : ℕ => |(R.orbit (0,1) j).2|
  have hcone : |(0 : ℝ)|≤|(1 : ℝ)| := by norm_num
  have hnz : (1 : ℝ)≠0 := one_ne_zero
  have hstep (j : ℕ) (hj : j<N) :
      abs ((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|)≤2*(δ : ℝ)*‖r.extend.orbit v j‖ := by
    have hy := R.orbit_snd_ne_zero h (v := (0,1)) hcone hnz j
    have hδj : (δ : ℝ)*‖r.extend.orbit v j‖≤1/2 :=
      ((mul_le_mul_of_nonneg_left (hv j hj.le) δ.coe_nonneg).trans_eq (mul_one _)).trans hδ
    have he : |(D j (R.orbit (0,1) j)).2|≤
        ((δ : ℝ)*‖r.extend.orbit v j‖)*|(R.orbit (0,1) j).2| := by
      have hh := (norm_snd_le (D j (R.orbit (0,1) j))).trans
        (((D j).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsmall j hj) (norm_nonneg _)))
      simpa only [Real.norm_eq_abs,R.orbit_norm_eq_snd h (v := (0,1)) hcone j] using hh
    have hb : 1≤|r.b j| := R.unstable_size_ge_one h j
    have hh := scalar_log_relative_error hb hy (mul_nonneg δ.coe_nonneg (norm_nonneg _)) hδj he
    change abs (Real.log |r.b j*(R.orbit (0,1) j).2+(D j (R.orbit (0,1) j)).2|-
      Real.log |(R.orbit (0,1) j).2|-Real.log |r.b j|)≤_
    convert hh using 1
    · congr 1; ring
    · ring
  have htel : (∑ j ∈ Finset.range N,((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|))=
      Real.log (y N)-(∑ j ∈ Finset.range N,Real.log |r.b j|) := by
    rw [Finset.sum_sub_distrib,Finset.sum_range_sub (fun j => Real.log (y j))]
    simp only [y,Recurrence.orbit,abs_one,Real.log_one,sub_zero]
  calc
    _ = abs (∑ j ∈ Finset.range N,((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|)) := congrArg abs htel.symm
    _ ≤ ∑ j ∈ Finset.range N,abs ((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N,2*(δ : ℝ)*‖r.extend.orbit v j‖ :=
      Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.mp hj)
    _ = (2*(δ : ℝ))*(∑ j ∈ Finset.range N,‖r.extend.orbit v j‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ (2*(δ : ℝ))*(2/(1-((ℓ+δ : ℝ≥0) : ℝ))) :=
      mul_le_mul_of_nonneg_left (r.extend.trappedBox_sum_norm h hv) (by positivity)
    _ = _ := by ring

noncomputable def LocalRecurrence.trueOrbit (r : LocalRecurrence ℓ δ) (v : Plane) : ℕ → Plane
  | 0 => v
  | n+1 => r.step n (r.trueOrbit v n)

lemma LocalRecurrence.trueOrbit_eq_extend (r : LocalRecurrence ℓ δ) {v : Plane} {N : ℕ}
    (hv : v∈r.extend.trappedBox N) {n : ℕ} (hn : n≤N) : r.trueOrbit v n=r.extend.orbit v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [LocalRecurrence.trueOrbit,ih (by omega),Recurrence.orbit,extend_step_eq _ n (hv n (by omega))]

lemma LocalRecurrence.trueOrbit_hasDerivAt (r : LocalRecurrence ℓ δ)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hDeriv : ∀ j u, HasFDerivAt (r.remainder j) (D j u) u)
    (L : ℕ → Plane →L[ℝ] Plane) (hL : ∀ n, ‖L n‖≤δ)
    {v : Plane} {N : ℕ} (hmatch : ∀ j : ℕ,j<N → L j=D j (r.trueOrbit v j))
    {n : ℕ} (hn : n≤N) :
    HasDerivAt (fun t : ℝ => r.trueOrbit (v.1,t) n) ((r.linearized L hL).orbit (0,1) n) v.2 := by
  induction n with
  | zero => exact hasDerivAt_const _ _ |>.prodMk (hasDerivAt_id _)
  | succ n ih =>
    have hi := ih (by omega)
    have rem := (hDeriv n (r.trueOrbit v n)).comp_hasDerivAt v.2 hi
    have hrem : HasDerivAt (fun t : ℝ => r.remainder n (r.trueOrbit (v.1,t) n))
        (L n ((r.linearized L hL).orbit (0,1) n)) v.2 := by
      rw [hmatch n (by omega)]
      exact rem
    have hifst : HasDerivAt (fun t : ℝ => (r.trueOrbit (v.1,t) n).1)
        ((r.linearized L hL).orbit (0,1) n).1 v.2 := by
      exact hi.fst
    have hisnd : HasDerivAt (fun t : ℝ => (r.trueOrbit (v.1,t) n).2)
        ((r.linearized L hL).orbit (0,1) n).2 v.2 := by
      exact hi.snd
    have hrfst : HasDerivAt (fun t : ℝ => (r.remainder n (r.trueOrbit (v.1,t) n)).1)
        (L n ((r.linearized L hL).orbit (0,1) n)).1 v.2 := by
      exact hrem.fst
    have hrsnd : HasDerivAt (fun t : ℝ => (r.remainder n (r.trueOrbit (v.1,t) n)).2)
        (L n ((r.linearized L hL).orbit (0,1) n)).2 v.2 := by
      exact hrem.snd
    exact ((hifst.const_mul (r.a n)).add hrfst).prodMk
      ((hisnd.const_mul (r.b n)).add hrsnd)

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma continuous_injective_abs_sub_le {f : ℝ → ℝ} (hc : Continuous f)
    (hi : Function.Injective f) {s t u : ℝ} (hst : s≤t) (htu : t≤u) :
    |f t-f s|≤|f u-f s| := by
  rcases hc.strictMono_of_inj hi with hm | hm
  · rw [abs_of_nonneg (sub_nonneg.mpr (hm.monotone hst)),
      abs_of_nonneg (sub_nonneg.mpr (hm.monotone (hst.trans htu)))]
    exact sub_le_sub_right (hm.monotone htu) _
  · rw [abs_of_nonpos (sub_nonpos.mpr (hm.antitone hst)),
      abs_of_nonpos (sub_nonpos.mpr (hm.antitone (hst.trans htu)))]
    linarith [hm.antitone htu]

lemma Recurrence.transverse_injective (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (n : ℕ) :
    Function.Injective (fun t : ℝ => (r.orbit (s,t) n).2) := by
  intro t u he
  change (r.orbit (s,t) n).2=(r.orbit (s,u) n).2 at he
  have hh := (r.orbit_unstable_cone h s t u n).2
  rw [he,sub_self,abs_zero,mul_zero] at hh
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

lemma Recurrence.transverse_between (r : Recurrence ℓ δ) (h : ℓ+δ<1)
    {s t u v : ℝ} (htu : t≤u) (huv : u≤v) (n : ℕ) :
    |(r.orbit (s,u) n).2-(r.orbit (s,t) n).2|≤
      |(r.orbit (s,v) n).2-(r.orbit (s,t) n).2| :=
  continuous_injective_abs_sub_le
    ((r.orbit_continuous n).comp (continuous_const.prodMk continuous_id)).snd
    (r.transverse_injective h s n) htu huv

theorem Recurrence.transverse_interval_trapped (r : Recurrence ℓ δ) (h : ℓ+δ<1)
    {s t u v : ℝ} (htu : t≤u) (huv : u≤v) {N : ℕ}
    (ht : ∀ n : ℕ,n≤N → ‖r.orbit (s,t) n‖≤1/3)
    (hv : ∀ n : ℕ,n≤N → ‖r.orbit (s,v) n‖≤1/3) :
    (s,u)∈r.trappedBox N := by
  intro n hn
  have hc := (r.orbit_unstable_cone h s u t n).1
  have hd := r.transverse_between h (s := s) htu huv n
  have ht' := norm_snd_le (r.orbit (s,t) n) |>.trans (ht n hn)
  have hv' := norm_snd_le (r.orbit (s,v) n) |>.trans (hv n hn)
  have hdiff : ‖r.orbit (s,u) n-r.orbit (s,t) n‖≤2/3 := by
    change max _ _ ≤ _
    simp only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] at ht' hv' ⊢
    rw [max_eq_right hc]
    exact hd.trans ((abs_sub _ _).trans (by linarith))
  have hh := norm_add_le (r.orbit (s,u) n-r.orbit (s,t) n) (r.orbit (s,t) n)
  rw [sub_add_cancel] at hh
  linarith [ht n hn]

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma LocalRecurrence.trueOrbit_continuous (r : LocalRecurrence ℓ δ)
    (hc : ∀ j, Continuous (r.remainder j)) (n : ℕ) : Continuous (fun v => r.trueOrbit v n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    exact ((continuous_const.mul ih.fst).add ((hc n).comp ih).fst).prodMk
      ((continuous_const.mul ih.snd).add ((hc n).comp ih).snd)

lemma LocalRecurrence.trapped_transverse_derivative (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    {v : Plane} {N : ℕ} (hv : v∈r.extend.trappedBox N) :
    ∃ J : ℝ, HasDerivAt (fun t : ℝ => (r.trueOrbit (v.1,t) N).2) J v.2 ∧
      J≠0 ∧ |Real.log |J|-(∑ j ∈ Finset.range N,Real.log |r.b j|)|≤
        4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  classical
  let L (n : ℕ) : Plane →L[ℝ] Plane := if n<N then D n (r.trueOrbit v n) else 0
  have hLs (n : ℕ) (hn : n<N) : ‖L n‖≤(δ : ℝ)*‖r.extend.orbit v n‖ := by
    dsimp only [L]
    rw [ite_eq_left hn,r.trueOrbit_eq_extend hv hn.le]
    exact hsmall n _ (hv n hn.le)
  have hL (n : ℕ) : ‖L n‖≤δ := by
    by_cases hn : n<N
    · exact (hLs n hn).trans ((mul_le_mul_of_nonneg_left (hv n hn.le) δ.coe_nonneg).trans_eq (mul_one _))
    · simp only [L,ite_eq_right hn,norm_zero]; exact δ.coe_nonneg
  let R := r.linearized L hL
  refine ⟨(R.orbit (0,1) N).2,?_,R.orbit_snd_ne_zero h (by norm_num) one_ne_zero N,
    r.linearized_log_distortion h hδ L hL hv hLs⟩
  exact (r.trueOrbit_hasDerivAt D hd L hL (fun n hn => ite_eq_left hn) (le_refl N)).snd

lemma exp_bounds_of_log_error {J A C : ℝ} (hJ : J≠0) (h : |Real.log |J|-A|≤C) :
    Real.exp (A-C)≤|J| ∧ |J|≤Real.exp (A+C) := by
  have hh := abs_le.mp h
  have hpos := abs_pos.mpr hJ
  constructor
  · rw [←Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [←Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)

theorem LocalRecurrence.transverse_interval_distortion (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hd : ∀ n v, HasFDerivAt (r.remainder n) (D n v) v)
    (hsmall : ∀ n v, ‖v‖≤1 → ‖D n v‖≤(δ : ℝ)*‖v‖)
    {s t u : ℝ} (htu : t≤u) {N : ℕ}
    (ht : ∀ n : ℕ,n≤N → ‖r.extend.orbit (s,t) n‖≤1/3)
    (hu : ∀ n : ℕ,n≤N → ‖r.extend.orbit (s,u) n‖≤1/3) :
    let A := ∑ j ∈ Finset.range N,Real.log |r.b j|
    let C := 4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ))
    Real.exp (A-C)*(u-t)≤|(r.trueOrbit (s,u) N).2-(r.trueOrbit (s,t) N).2| ∧
      |(r.trueOrbit (s,u) N).2-(r.trueOrbit (s,t) N).2|≤Real.exp (A+C)*(u-t) := by
  dsimp only
  rcases htu.eq_or_lt with he | htu
  · subst u; simp
  let f : ℝ → ℝ := fun v => (r.trueOrbit (s,v) N).2
  have hfc : Continuous f := ((r.trueOrbit_continuous (fun n => continuous_iff_continuousAt.mpr
    fun v => (hd n v).continuousAt) N).comp (continuous_const.prodMk continuous_id)).snd
  have htrap (v : ℝ) (hv : v∈Icc t u) : (s,v)∈r.extend.trappedBox N :=
    r.extend.transverse_interval_trapped h hv.1 hv.2 ht hu
  have hf (v : ℝ) (hv : v∈Icc t u) : ∃ J : ℝ, HasDerivAt f J v ∧ J≠0 ∧
      |Real.log |J|-(∑ j ∈ Finset.range N,Real.log |r.b j|)|≤
        4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) :=
    r.trapped_transverse_derivative h hδ D hd hsmall (htrap v hv)
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope f htu hfc.continuousOn
    (fun v hv => (hf v ⟨hv.1.le,hv.2.le⟩).choose_spec.1.differentiableAt.differentiableWithinAt)
  obtain ⟨J,hJ,hJn,hJL⟩ := hf c ⟨hc.1.le,hc.2.le⟩
  rw [hJ.deriv] at he
  have hab : f u-f t=J*(u-t) := (eq_div_iff (sub_ne_zero.mpr htu.ne')).mp he |>.symm
  have heq : |f u-f t|=|J| *(u-t) := by rw [hab,abs_mul,abs_of_pos (sub_pos.mpr htu)]
  change _≤|f u-f t| ∧ |f u-f t|≤_
  rw [heq]
  have hb := exp_bounds_of_log_error hJn hJL
  exact ⟨mul_le_mul_of_nonneg_right hb.1 (sub_nonneg.mpr htu.le),
    mul_le_mul_of_nonneg_right hb.2 (sub_nonneg.mpr htu.le)⟩

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

lemma Recurrence.orbit_pair_cone (r : Recurrence ℓ δ) (h : ℓ+δ<1) {v w : Plane}
    (hv : |v.1-w.1|≤|v.2-w.2|) (n : ℕ) :
    |(r.orbit v n).1-(r.orbit w n).1|≤|(r.orbit v n).2-(r.orbit w n).2| ∧
    |v.2-w.2|≤((ℓ+δ : ℝ≥0) : ℝ)^n*|(r.orbit v n).2-(r.orbit w n).2| := by
  induction n with
  | zero => exact ⟨hv,by simp only [Recurrence.orbit,pow_zero,one_mul,le_refl]⟩
  | succ n ih =>
    have hh := r.unstable_cone_step h n (r.orbit v n) (r.orbit w n) ih.1
    refine ⟨hh.1,ih.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left hh.2 (pow_nonneg (ℓ+δ).coe_nonneg n)).trans_eq
      (by simp only [Recurrence.orbit,pow_succ]; ring)
lemma affine_cone {V : Plane} (hV : |V.1|≤|V.2|) (p : Plane) (t u : ℝ) :
    |(p+t•V).1-(p+u•V).1|≤|(p+t•V).2-(p+u•V).2| := by
  have he : p+t•V-(p+u•V)=(t-u)•V := by rw [add_sub_add_left_eq_sub,sub_smul]
  change |(p+t•V-(p+u•V)).1|≤|(p+t•V-(p+u•V)).2|
  rw [he]
  change |(t-u)*V.1|≤|(t-u)*V.2|
  rw [abs_mul,abs_mul]
  exact mul_le_mul_of_nonneg_left hV (abs_nonneg _)

lemma Recurrence.affine_transverse_injective (r : Recurrence ℓ δ) (h : ℓ+δ<1)
    {V : Plane} (hV : |V.1|≤|V.2|) (hV0 : V.2≠0) (p : Plane) (n : ℕ) :
    Function.Injective (fun t : ℝ => (r.orbit (p+t•V) n).2) := by
  intro t u he
  change (r.orbit (p+t•V) n).2=(r.orbit (p+u•V) n).2 at he
  have hh := (r.orbit_pair_cone h (affine_cone hV p t u) n).2
  rw [he,sub_self,abs_zero,mul_zero] at hh
  have hz := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  simp only [Prod.snd_add] at hz
  exact (mul_left_inj' hV0).mp (add_left_cancel hz)

lemma Recurrence.affine_interval_trapped (r : Recurrence ℓ δ) (h : ℓ+δ<1)
    {V : Plane} (hV : |V.1|≤|V.2|) (hV0 : V.2≠0) (p : Plane)
    {t u v : ℝ} (htu : t≤u) (huv : u≤v) {N : ℕ}
    (ht : ∀ n : ℕ,n≤N → ‖r.orbit (p+t•V) n‖≤1/3)
    (hv : ∀ n : ℕ,n≤N → ‖r.orbit (p+v•V) n‖≤1/3) :
    p+u•V∈r.trappedBox N := by
  intro n hn
  have hc := (r.orbit_pair_cone h (affine_cone hV p u t) n).1
  have hd := continuous_injective_abs_sub_le
    ((r.orbit_continuous n).comp (continuous_const.add (continuous_id.smul continuous_const))).snd
    (r.affine_transverse_injective h hV hV0 p n) htu huv
  change |(r.orbit (p+u•V) n).2-(r.orbit (p+t•V) n).2|≤
    |(r.orbit (p+v•V) n).2-(r.orbit (p+t•V) n).2| at hd
  have ht' := norm_snd_le (r.orbit (p+t•V) n) |>.trans (ht n hn)
  have hv' := norm_snd_le (r.orbit (p+v•V) n) |>.trans (hv n hn)
  have hdiff : ‖r.orbit (p+u•V) n-r.orbit (p+t•V) n‖≤2/3 := by
    change max _ _ ≤ _
    simp only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] at ht' hv' ⊢
    rw [max_eq_right hc]
    exact hd.trans ((abs_sub _ _).trans (by linarith))
  have hh := norm_add_le (r.orbit (p+u•V) n-r.orbit (p+t•V) n) (r.orbit (p+t•V) n)
  rw [sub_add_cancel] at hh
  linarith [ht n hn]

theorem LocalRecurrence.linearized_cone_log_distortion (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (hδ : (δ : ℝ)≤1/2) (D : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ)
    {N : ℕ} {v : Plane} (hv : v∈r.extend.trappedBox N)
    {V : Plane} (hcone : |V.1|≤|V.2|) (hnz : V.2≠0)
    (hsmall : ∀ j : ℕ,j<N → ‖D j‖≤(δ : ℝ)*‖r.extend.orbit v j‖) :
    abs (Real.log |((r.linearized D hD).orbit V N).2|-Real.log |V.2|-
      ∑ j ∈ Finset.range N,Real.log |r.b j|)≤4*(δ : ℝ)/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  let R := r.linearized D hD
  let y := fun j : ℕ => |(R.orbit V j).2|
  have hstep (j : ℕ) (hj : j<N) :
      abs ((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|)≤2*(δ : ℝ)*‖r.extend.orbit v j‖ := by
    have hy := R.orbit_snd_ne_zero h (v := V) hcone hnz j
    have hδj : (δ : ℝ)*‖r.extend.orbit v j‖≤1/2 :=
      ((mul_le_mul_of_nonneg_left (hv j hj.le) δ.coe_nonneg).trans_eq (mul_one _)).trans hδ
    have he : |(D j (R.orbit V j)).2|≤
        ((δ : ℝ)*‖r.extend.orbit v j‖)*|(R.orbit V j).2| := by
      have hh := (norm_snd_le (D j (R.orbit V j))).trans
        (((D j).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsmall j hj) (norm_nonneg _)))
      simpa only [Real.norm_eq_abs,R.orbit_norm_eq_snd h (v := V) hcone j] using hh
    have hb : 1≤|r.b j| := R.unstable_size_ge_one h j
    have hh := scalar_log_relative_error hb hy (mul_nonneg δ.coe_nonneg (norm_nonneg _)) hδj he
    change abs (Real.log |r.b j*(R.orbit V j).2+(D j (R.orbit V j)).2|-
      Real.log |(R.orbit V j).2|-Real.log |r.b j|)≤_
    convert hh using 1
    · congr 1; ring
    · ring
  have htel : (∑ j ∈ Finset.range N,((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|))=
      Real.log (y N)-Real.log |V.2|-(∑ j ∈ Finset.range N,Real.log |r.b j|) := by
    rw [Finset.sum_sub_distrib,Finset.sum_range_sub (fun j => Real.log (y j))]
    rfl
  calc
    _ = abs (∑ j ∈ Finset.range N,((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|)) := congrArg abs htel.symm
    _ ≤ ∑ j ∈ Finset.range N,abs ((Real.log (y (j+1))-Real.log (y j))-Real.log |r.b j|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N,2*(δ : ℝ)*‖r.extend.orbit v j‖ :=
      Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.mp hj)
    _ = (2*(δ : ℝ))*(∑ j ∈ Finset.range N,‖r.extend.orbit v j‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ (2*(δ : ℝ))*(2/(1-((ℓ+δ : ℝ≥0) : ℝ))) :=
      mul_le_mul_of_nonneg_left (r.extend.trappedBox_sum_norm h hv) (by positivity)
    _ = _ := by ring

lemma LocalRecurrence.trueOrbit_affine_hasDerivAt (r : LocalRecurrence ℓ δ)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hDeriv : ∀ j u, HasFDerivAt (r.remainder j) (D j u) u)
    (L : ℕ → Plane →L[ℝ] Plane) (hL : ∀ n, ‖L n‖≤δ)
    (p V : Plane) (x : ℝ) {N : ℕ} (hmatch : ∀ j : ℕ,j<N → L j=D j (r.trueOrbit (p+x•V) j))
    {n : ℕ} (hn : n≤N) :
    HasDerivAt (fun t : ℝ => r.trueOrbit (p+t•V) n) ((r.linearized L hL).orbit V n) x := by
  induction n with
  | zero =>
    have h1 : HasDerivAt (fun t : ℝ => p.1+t*V.1) V.1 x := by
      convert ((hasDerivAt_id x).mul_const V.1).const_add p.1 using 1 <;> first | rfl | simp only [one_mul]
    have h2 : HasDerivAt (fun t : ℝ => p.2+t*V.2) V.2 x := by
      convert ((hasDerivAt_id x).mul_const V.2).const_add p.2 using 1 <;> first | rfl | simp only [one_mul]
    exact h1.prodMk h2
  | succ n ih =>
    have hi := ih (by omega)
    have rem := (hDeriv n (r.trueOrbit (p+x•V) n)).comp_hasDerivAt x hi
    have hrem : HasDerivAt (fun t : ℝ => r.remainder n (r.trueOrbit (p+t•V) n))
        (L n ((r.linearized L hL).orbit V n)) x := by
      rw [hmatch n (by omega)]
      exact rem
    have hifst : HasDerivAt (fun t : ℝ => (r.trueOrbit (p+t•V) n).1)
        ((r.linearized L hL).orbit V n).1 x := by
      exact hi.fst
    have hisnd : HasDerivAt (fun t : ℝ => (r.trueOrbit (p+t•V) n).2)
        ((r.linearized L hL).orbit V n).2 x := by
      exact hi.snd
    have hrfst : HasDerivAt (fun t : ℝ => (r.remainder n (r.trueOrbit (p+t•V) n)).1)
        (L n ((r.linearized L hL).orbit V n)).1 x := by
      exact hrem.fst
    have hrsnd : HasDerivAt (fun t : ℝ => (r.remainder n (r.trueOrbit (p+t•V) n)).2)
        (L n ((r.linearized L hL).orbit V n)).2 x := by
      exact hrem.snd
    exact ((hifst.const_mul (r.a n)).add hrfst).prodMk
      ((hisnd.const_mul (r.b n)).add hrsnd)

end StandardMapEntropy.NonlinearStable

end
end

end OAI
