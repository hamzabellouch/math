import OAI.Geometry.HarmonicGrowth.StreamData

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology

namespace HarmonicCounterexample.Cycling

def partialSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, f j

lemma weighted_telescoping (f w : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, w j * f j =
      w n * partialSum f n -
        ∑ j ∈ Finset.range n, (w (j+1) - w j) * partialSum f (j+1) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [partialSum, Finset.sum_range_succ]
    ring

/-- A bounded primitive makes every nonnegative monotone weighted mean
asymptotically cancel at the scale of its largest weight. -/
lemma weighted_sum_abs_le (f w : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hpartial : ∀ n, |partialSum f n| ≤ C)
    (hw0 : 0 ≤ w 0) (hw : Monotone w) (n : ℕ) :
    |∑ j ∈ Finset.range n, w j * f j| ≤ 2 * C * w n := by
  have hwn : 0 ≤ w n := hw0.trans (hw (Nat.zero_le n))
  rw [weighted_telescoping]
  calc
    |w n * partialSum f n -
        ∑ j ∈ Finset.range n, (w (j+1) - w j) * partialSum f (j+1)|
      ≤ |w n * partialSum f n| +
        |∑ j ∈ Finset.range n, (w (j+1) - w j) * partialSum f (j+1)| := abs_sub _ _
    _ ≤ w n * C + ∑ j ∈ Finset.range n, (w (j+1) - w j) * C := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hwn]
        exact mul_le_mul_of_nonneg_left (hpartial n) hwn
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hw (Nat.le_succ j)))]
        exact mul_le_mul_of_nonneg_left (hpartial (j+1)) (sub_nonneg.2 (hw (Nat.le_succ j)))
    _ = w n * C + (w n - w 0) * C := by rw [← Finset.sum_mul, Finset.sum_range_sub]
    _ ≤ 2 * C * w n := by nlinarith [mul_nonneg hw0 hC]

lemma partialSum_periodic (f : ℕ → ℝ) {M : ℕ} (hper : Function.Periodic f M)
    (hzero : partialSum f M = 0) : Function.Periodic (partialSum f) M := by
  intro n
  simp only [partialSum, add_comm n M, Finset.sum_range_add]
  have hz : ∑ j ∈ Finset.range M, f j = 0 := hzero
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simpa [add_comm] using hper j

/-- Full cycles cancel exactly; only a bounded incomplete cycle remains. -/
lemma bounded_primitive_of_periodic (f : ℕ → ℝ) {M : ℕ} (hM : 0 < M)
    (hper : Function.Periodic f M) (hzero : partialSum f M = 0) :
    ∀ n, |partialSum f n| ≤ ∑ j ∈ Finset.range M, |f j| := by
  intro n
  rw [← (partialSum_periodic f hper hzero).map_mod_nat n]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.mod_lt n hM).le
  · intro i _ _
    exact abs_nonneg _

lemma weighted_periodic_abs_le (f w : ℕ → ℝ) {M : ℕ} (hM : 0 < M)
    (hper : Function.Periodic f M) (hzero : partialSum f M = 0)
    (hw0 : 0 ≤ w 0) (hw : Monotone w) (n : ℕ) :
    |∑ j ∈ Finset.range n, w j * f j| ≤
      2 * (∑ j ∈ Finset.range M, |f j|) * w n :=
  weighted_sum_abs_le f w (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (bounded_primitive_of_periodic f hM hper hzero) hw0 hw n

/-- The precise asymptotic cancellation required by the cycling argument.
No assumption of equal durations is made. -/
theorem weighted_periodic_limit (f w D : ℕ → ℝ) {M : ℕ} (hM : 0 < M)
    (hper : Function.Periodic f M) (hzero : partialSum f M = 0)
    (hw0 : 0 ≤ w 0) (hw : Monotone w) (hD : ∀ n, 0 < D n)
    (hsmall : Tendsto (fun n => w n / D n) atTop (𝓝 0)) :
    Tendsto (fun n => (∑ j ∈ Finset.range n, w j * f j) / D n)
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      ‖(∑ j ∈ Finset.range n, w j * f j) / D n‖ ≤
        (2 * (∑ j ∈ Finset.range M, |f j|)) * (w n / D n) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hD n), ← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right (hD n)).2
      (weighted_periodic_abs_le f w hM hper hzero hw0 hw n)
  apply squeeze_zero_norm hbound
  simpa using hsmall.const_mul (2 * (∑ j ∈ Finset.range M, |f j|))

end HarmonicCounterexample.Cycling

end

noncomputable section
open Filter
open scoped BigOperators Topology

namespace HarmonicCounterexample.Cycling
open Schedule
open scoped Asymptotics

lemma pulse_little_dwell : pulse =o[atTop] dwell := by
  have hz : ∀ n, dwell n = 0 → pulse n = 0 := by
    intro n hn
    have hpos : 0 < dwell n := by dsimp [dwell]; positivity
    exact False.elim (hpos.ne' hn)
  apply (Asymptotics.isLittleO_iff_tendsto hz).2
  have h := Schedule.tendsto_inv_nat.comp (Filter.tendsto_add_atTop_nat 1)
  apply h.congr'
  filter_upwards [] with n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  dsimp [pulse, dwell]
  push_cast
  field_simp

lemma dwellSum_big_time : dwellSum =O[atTop] time := by
  apply Asymptotics.isBigO_of_le
  intro n
  rw [Real.norm_of_nonneg (dwellSum_nonneg n), Real.norm_of_nonneg (time_pos n).le]
  change (∑ i ∈ Finset.range n, dwell i) ≤
    10 + ∑ i ∈ Finset.range n, (dwell i + 4 * pulse i)
  rw [Finset.sum_add_distrib]
  have hp : 0 ≤ ∑ i ∈ Finset.range n, 4 * pulse i :=
    Finset.sum_nonneg fun i _ => by dsimp [pulse]; positivity
  linarith

lemma small_weighted_error {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    (fun n => e n * dwell n) =o[atTop] dwell := by
  apply (Asymptotics.isLittleO_iff_tendsto (fun n hn => by simp [hn])).2
  convert he using 1
  ext n
  have hn : dwell n ≠ 0 := by dsimp [dwell]; positivity
  exact mul_div_cancel_right₀ _ hn

lemma small_sum_time {f : ℕ → ℝ} (hf : f =o[atTop] dwell) :
    Tendsto (fun n => (∑ j ∈ Finset.range n, f j) / time n)
      atTop (𝓝 0) := by
  have hd : (0 : ℕ → ℝ) ≤ dwell := fun n => by dsimp [dwell]; positivity
  exact ((hf.sum_range hd dwellSum_atTop).trans_isBigO dwellSum_big_time).tendsto_div_nhds_zero

/-- The full endpoint growth calculation: unequal j^7 dwell lengths, O(j^6)
scalar factors, and uniformly vanishing exponent errors are all retained. -/
theorem endpoint_rate {M : ℕ} (hM : 0 < M) (d scalarError exponentError : ℕ → ℝ)
    (hper : Function.Periodic d M) (average : ℝ)
    (haverage : (∑ j ∈ Finset.range M, d j) = (M : ℝ) * average)
    {C : ℝ} (hscalar : ∀ᶠ j in atTop, |scalarError j| ≤ C * pulse j)
    (hexponent : Tendsto exponentError atTop (𝓝 0)) :
    Tendsto (fun n => (∑ j ∈ Finset.range n,
      (scalarError j + dwell j * (d j + exponentError j))) / time n)
      atTop (𝓝 average) := by
  have hcper : Function.Periodic (fun j => d j - average) M := by
    intro j
    change d (j + M) - average = d j - average
    rw [hper j]
  have hzero : partialSum (fun j => d j - average) M = 0 := by
    simp only [partialSum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, haverage, sub_self]
  have hw : Monotone dwell := by
    intro i j hij
    dsimp [dwell]
    gcongr
  have hcycle := weighted_periodic_limit (fun j => d j - average) dwell time hM
    hcper hzero (by norm_num [dwell]) hw time_pos dwell_time
  have hb : scalarError =O[atTop] pulse := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hscalar] with j hj
    have hp : 0 ≤ pulse j := by dsimp [pulse]; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using hj
  have hscalarSum := small_sum_time (hb.trans_isLittleO pulse_little_dwell)
  have herrorSum := small_sum_time (small_weighted_error hexponent)
  have hmean := dwellSum_time.const_mul average
  have h := ((hscalarSum.add hcycle).add hmean).add herrorSum
  convert h using 1
  · ext n
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      dwellSum, ← Finset.sum_mul]
    have hswap : (∑ j ∈ Finset.range n, exponentError j * dwell j) =
        ∑ j ∈ Finset.range n, dwell j * exponentError j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hswap]
    ring
  · simp

/-- Ignoring a fixed initial history does not change the endpoint exponent. -/
theorem remove_initial_history {f : ℕ → ℝ} {average : ℝ}
    (hf : Tendsto (fun n => (∑ j ∈ Finset.range n, f j) / time n)
      atTop (𝓝 average)) (j₀ : ℕ) :
    Tendsto (fun n => (∑ j ∈ Finset.Ico j₀ n, f j) / time n)
      atTop (𝓝 average) := by
  have hconst : Tendsto (fun n => (∑ j ∈ Finset.range j₀, f j) / time n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp time_atTop).const_mul (∑ j ∈ Finset.range j₀, f j)
  have h := hf.sub hconst
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop j₀] with n hn
  rw [Finset.sum_Ico_eq_sub f hn, sub_div]

end HarmonicCounterexample.Cycling

end

noncomputable section
open Filter
open scoped BigOperators Topology
open scoped BigOperators InnerProductSpace

namespace HarmonicCounterexample.Cycling
open Fin.NatCast Matrix
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

/-- Actual chronological product of endpoint transmission operators. -/
def transferOrbit (T : ℕ → E →L[ℝ] E) (x : E) : ℕ → E
  | 0 => x
  | n+1 => T n (transferOrbit T x n)

/-- The signed amplitudes retain all determinant-correcting signs. -/
def orbitAmplitude (π : Equiv.Perm ι) (σ : ι → ℝ) (s : ℕ → ℝ)
    (d : ℕ → ι → ℝ) (i : ι) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n,s j*σ ((π^[j]) i)*d j ((π^[j]) i)

omit [Fintype ι] [DecidableEq ι] in
lemma transferOrbit_eq_signed_basis (b : ι → E)
    (π : Equiv.Perm ι) (σ : ι → ℝ) (s : ℕ → ℝ) (d : ℕ → ι → ℝ)
    (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n i,T n (b i)=(s n*σ i*d n i) • b (π i)) (i : ι) :
    ∀ n,transferOrbit T (b i) n=orbitAmplitude π σ s d i n • b ((π^[n]) i) := by
  intro n
  induction n with
  | zero => simp [transferOrbit,orbitAmplitude]
  | succ n ih =>
    rw [transferOrbit,ih,map_smul,hT,smul_smul]
    simp only [orbitAmplitude,Finset.prod_range_succ,Function.iterate_succ_apply']

omit [Fintype ι] [DecidableEq ι] in
lemma orbitAmplitude_abs (π : Equiv.Perm ι) (σ : ι → ℝ) (s : ℕ → ℝ)
    (d : ℕ → ι → ℝ) (hσ : ∀ i,|σ i|=1) (hs : ∀ n,0<s n)
    (hd : ∀ n i,0<d n i) (i : ι) (n : ℕ) :
    |orbitAmplitude π σ s d i n|=∏ j ∈ Finset.range n,s j*d j ((π^[j]) i) := by
  simp only [orbitAmplitude,Finset.abs_prod,abs_mul,hσ,abs_of_pos (hs _),
    abs_of_pos (hd _ _),mul_one]

omit [Fintype ι] [DecidableEq ι] in
/-- The exact source cycle-sum formula for true operator products. This also
proves nonvanishing, so taking the real logarithm introduces no zero case. -/
theorem signed_cycle_log_norm (b : ι → E) (hb : ∀ i,‖b i‖=1)
    (π : Equiv.Perm ι) (σ : ι → ℝ) (s : ℕ → ℝ) (d : ℕ → ι → ℝ)
    (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n i,T n (b i)=(s n*σ i*d n i) • b (π i))
    (hσ : ∀ i,|σ i|=1) (hs : ∀ n,0<s n) (hd : ∀ n i,0<d n i)
    (i : ι) (n : ℕ) :
    0<‖transferOrbit T (b i) n‖ ∧
      Real.log ‖transferOrbit T (b i) n‖=
        ∑ j ∈ Finset.range n,(Real.log (s j)+Real.log (d j ((π^[j]) i))) := by
  have he : ‖transferOrbit T (b i) n‖=∏ j ∈ Finset.range n,s j*d j ((π^[j]) i) := by
    rw [transferOrbit_eq_signed_basis b π σ s d T hT i n,norm_smul,hb,mul_one,
      Real.norm_eq_abs,orbitAmplitude_abs π σ s d hσ hs hd]
  rw [he]
  refine ⟨Finset.prod_pos (fun j _ => mul_pos (hs j) (hd j _)),?_⟩
  rw [Real.log_prod (fun j _ => (mul_pos (hs j) (hd j _)).ne')]
  apply Finset.sum_congr rfl
  intro j _
  exact Real.log_mul (hs j).ne' (hd j _).ne'

/-- A determinant-one signed permutation with the requested underlying cycle.
One sign correction at i0 is enough and does not alter any coordinate norm. -/
def signedPermutation (π : Equiv.Perm ι) (i₀ : ι) : Matrix ι ι ℝ :=
  (π⁻¹).permMatrix ℝ * Matrix.diagonal (fun i => if i=i₀ then (π.sign:ℝ) else 1)

lemma signedPermutation_det (π : Equiv.Perm ι) (i₀ : ι) :
    (signedPermutation π i₀).det=1 := by
  rw [signedPermutation,Matrix.det_mul,Matrix.det_permutation,Matrix.det_diagonal]
  simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true,Equiv.Perm.sign_inv]
  have h := Int.units_eq_one_or (π.sign)
  rcases h with h|h <;> simp [h]

lemma finRotate_iterate_add {M : ℕ} [NeZero M] (i : Fin M) (j : ℕ) :
    (finRotate M)^[j] i=i+(↑j:Fin M) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih,finRotate_apply]
    simp only [Nat.cast_add,Nat.cast_one]
    exact add_assoc _ _ _

lemma cycle_exponents_periodic {M : ℕ} [NeZero M] (d : Fin M → ℝ) (i : Fin M) :
    Function.Periodic (fun j : ℕ => d ((finRotate M)^[j] i)) M := by
  intro j
  simp [finRotate_iterate_add,Nat.cast_add]

lemma cycle_exponents_sum {M : ℕ} [NeZero M] (d : Fin M → ℝ) (i : Fin M) :
    (∑ j ∈ Finset.range M,d ((finRotate M)^[j] i))=∑ k,d k := by
  simp_rw [finRotate_iterate_add]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Fin.cast_val_eq_self]
  exact Equiv.sum_comp (Equiv.addLeft i) d

lemma signedPermutation_mulVec_single (π : Equiv.Perm ι) (i₀ i : ι) (x : ℝ) :
    signedPermutation π i₀ *ᵥ Pi.single i x=
      Pi.single (π i) ((if i=i₀ then (π.sign:ℝ) else 1)*x) := by
  rw [signedPermutation,← Matrix.mulVec_mulVec,Matrix.diagonal_mulVec_single,
    Matrix.permMatrix_mulVec]
  ext j
  change (Pi.single i ((if i=i₀ then (π.sign:ℝ) else 1)*x) : ι → ℝ) (π.symm j)=
    (Pi.single (π i) ((if i=i₀ then (π.sign:ℝ) else 1)*x) : ι → ℝ) j
  simp only [Pi.single_apply,Equiv.symm_apply_eq]

lemma signedPermutation_abs_sign (π : Equiv.Perm ι) (i₀ i : ι) :
    |if i=i₀ then (π.sign:ℝ) else 1|=1 := by
  split_ifs
  · rcases Int.units_eq_one_or π.sign with h|h <;> simp [h]
  · norm_num

end HarmonicCounterexample.Cycling

end

noncomputable section
open Filter
open scoped BigOperators Topology
open scoped BigOperators InnerProductSpace

namespace HarmonicCounterexample.Cycling
open Filter HarmonicCounterexample.Schedule
open scoped Topology BigOperators

lemma finite_varying_error {ι : Type*} [Fintype ι] (e : ℕ → ι → ℝ)
    (he : ∀ i,Tendsto (fun n => e n i) atTop (𝓝 0)) (i : ℕ → ι) :
    Tendsto (fun n => e n (i n)) atTop (𝓝 0) := by
  have hp : Tendsto e atTop (𝓝 (0 : ι → ℝ)) := tendsto_pi_nhds.2 he
  apply squeeze_zero_norm (fun n => norm_le_pi_norm (e n) (i n))
  simpa using hp.norm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- True endpoint operators, including the determinant-correcting signs and
all scalar-normalization factors, have the averaged selected exponent. This
is not an endpoint-only definition of polynomial growth. -/
theorem endpoint_operator_rate {M : ℕ} [NeZero M] (b : Fin M → E)
    (hb : ∀ i,‖b i‖=1) (σ : Fin M → ℝ) (s : ℕ → ℝ)
    (d : ℕ → Fin M → ℝ) (T : ℕ → E →L[ℝ] E)
    (hT : ∀ n i,T n (b i)=(s n*σ i*d n i) • b (finRotate M i))
    (hσ : ∀ i,|σ i|=1) (hs : ∀ n,0<s n) (hd : ∀ n i,0<d n i)
    (d₀ : Fin M → ℝ) (e : ℕ → Fin M → ℝ)
    (hlog : ∀ n i,Real.log (d n i)=dwell n*(d₀ i+e n i))
    (he : ∀ i,Tendsto (fun n => e n i) atTop (𝓝 0))
    {C : ℝ} (hscalar : ∀ᶠ n in atTop,|Real.log (s n)| ≤ C*pulse n)
    (i : Fin M) :
    Tendsto (fun n => Real.log ‖transferOrbit T (b i) n‖ / time n)
      atTop (𝓝 ((∑ k,d₀ k)/(M:ℝ))) := by
  have hav : (∑ j ∈ Finset.range M,d₀ ((finRotate M)^[j] i))=
      (M:ℝ)*((∑ k,d₀ k)/(M:ℝ)) := by
    rw [cycle_exponents_sum]
    have hM : (M:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne M)
    field_simp [hM]
  have h := endpoint_rate (Nat.pos_of_ne_zero (NeZero.ne M))
    (fun j => d₀ ((finRotate M)^[j] i)) (fun j => Real.log (s j))
    (fun j => e j ((finRotate M)^[j] i)) (cycle_exponents_periodic d₀ i)
    ((∑ k,d₀ k)/(M:ℝ)) hav hscalar
    (finite_varying_error e he (fun j => (finRotate M)^[j] i))
  convert h using 1
  ext n
  rw [(signed_cycle_log_norm b hb (finRotate M) σ s d T hT hσ hs hd i n).2]
  simp only [hlog]

end HarmonicCounterexample.Cycling

end

noncomputable section


namespace HarmonicCounterexample.Cycling
open Module LinearODE
open scoped BigOperators InnerProductSpace
variable {E ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

def fromMatrix (b:OrthonormalBasis ι ℝ E) (M:Matrix ι ι ℝ) : E→L[ℝ]E :=
  ((LinearMap.toMatrix b.toBasis b.toBasis).symm M).toContinuousLinearMap

lemma fromMatrix_matrix (b:OrthonormalBasis ι ℝ E) (M:Matrix ι ι ℝ) :
    orthogonalMatrix b (fromMatrix b M)=M := by
  change (LinearMap.toMatrix b.toBasis b.toBasis) ((LinearMap.toMatrix b.toBasis b.toBasis).symm M)=M
  exact (LinearMap.toMatrix b.toBasis b.toBasis).apply_symm_apply M

lemma fromMatrix_inverse (b:OrthonormalBasis ι ℝ E) (T:E→L[ℝ]E) :
    fromMatrix b (orthogonalMatrix b T)=T := by
  apply orthogonalMatrix_injective b
  exact fromMatrix_matrix b _

omit [FiniteDimensional ℝ E] in
lemma basis_repr_fun (b:OrthonormalBasis ι ℝ E) (i:ι) :
    (fun j=>b.repr (b i) j)=Pi.single i 1 := by
  ext j
  simp only [b.repr_self,PiLp.single_apply,Pi.single_apply]

def weightedCycle (b:OrthonormalBasis ι ℝ E) (π:Equiv.Perm ι) (i₀:ι)
    (s:ℝ) (d:ι→ℝ) : E→L[ℝ]E :=
  fromMatrix b (s • (Matrix.diagonal d*signedPermutation π i₀))

lemma weightedCycle_action (b:OrthonormalBasis ι ℝ E) (π:Equiv.Perm ι) (i₀ i:ι)
    (s:ℝ) (d:ι→ℝ) : weightedCycle b π i₀ s d (b i)=
      (s*(if i=i₀ then (π.sign:ℝ) else 1)*d (π i)) • b (π i) := by
  apply b.repr.injective
  apply PiLp.ext
  have h := orthogonalMatrix_mulVec b (weightedCycle b π i₀ s d) (b i)
  rw [weightedCycle,fromMatrix_matrix,basis_repr_fun,Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec,signedPermutation_mulVec_single,Matrix.diagonal_mulVec_single] at h
  simp only [mul_one] at h
  intro j
  have hj := congrFun h j
  simp only [Pi.smul_apply,smul_eq_mul,Pi.single_apply] at hj
  simp only [map_smul,PiLp.smul_apply,smul_eq_mul,b.repr_self,PiLp.single_apply]
  simp only [weightedCycle]
  rw [←hj]
  split_ifs <;> ring

lemma weightedCycle_injective (b:OrthonormalBasis ι ℝ E) (π:Equiv.Perm ι) (i₀:ι)
    {s:ℝ} (hs:s≠0) {d:ι→ℝ} (hd:∀i,d i≠0) :
    Function.Injective (weightedCycle b π i₀ s d) := by
  have hm : IsUnit (s • (Matrix.diagonal d*signedPermutation π i₀):Matrix ι ι ℝ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_smul,Matrix.det_mul,Matrix.det_diagonal,signedPermutation_det,mul_one]
    apply isUnit_iff_ne_zero.mpr
    exact mul_ne_zero (pow_ne_zero _ hs) (Finset.prod_ne_zero_iff.mpr (fun i _=>hd i))
  let M := s • (Matrix.diagonal d*signedPermutation π i₀)
  have hi : fromMatrix b (Ring.inverse M)*fromMatrix b M=1 := by
    apply orthogonalMatrix_injective b
    rw [orthogonalMatrix_mul,fromMatrix_matrix,fromMatrix_matrix,orthogonalMatrix_one]
    exact Ring.inverse_mul_cancel M hm
  intro x y h
  have he := congrArg (fromMatrix b (Ring.inverse M)) h
  change (fromMatrix b (Ring.inverse M)*fromMatrix b M) x=
    (fromMatrix b (Ring.inverse M)*fromMatrix b M) y at he
  simpa only [hi,one_apply_eq_self] using he

omit [FiniteDimensional ℝ E] in
lemma transferOrbit_linear (T:ℕ→E→L[ℝ]E) (n:ℕ) : ∃U:E→L[ℝ]E,∀x,transferOrbit T x n=U x := by
  induction n with
  | zero => exact ⟨1,fun _=>rfl⟩
  | succ n ih =>
    obtain ⟨U,hU⟩:=ih
    exact ⟨T n*U,fun x=>by rw [transferOrbit,hU];rfl⟩

omit [FiniteDimensional ℝ E] in
lemma transferOrbit_injective (T:ℕ→E→L[ℝ]E) (hT:∀n,Function.Injective (T n)) (n:ℕ) :
    Function.Injective (fun x=>transferOrbit T x n) := by
  induction n with
  | zero => exact fun _ _ h=>h
  | succ n ih => exact fun _ _ h=>ih (hT n h)

end HarmonicCounterexample.Cycling

end

noncomputable section


namespace HarmonicCounterexample.AngularStream
open Set Filter Schedule Pulses FiniteControl.SmoothWord
open scoped Topology

lemma pulse_unique {i j : ℕ} {t : ℝ}
    (hi : t ∈ Icc (time i) (time i+pulse i))
    (hj : t ∈ Icc (time j) (time j+pulse j)) : i=j := by
  by_contra h
  rcases lt_or_gt_of_ne h with h|h
  · have ht := time_strictMono.monotone (Nat.succ_le_of_lt h)
    rw [Nat.succ_eq_add_one,time_succ] at ht
    linarith [hi.2,hj.1,pulse_pos i,dwell_pos i]
  · have ht := time_strictMono.monotone (Nat.succ_le_of_lt h)
    rw [Nat.succ_eq_add_one,time_succ] at ht
    linarith [hj.2,hi.1,pulse_pos j,dwell_pos j]

def pulseIndex (j0 : ℕ) (t : ℝ) : Option ℕ := by
  classical
  exact if h : ∃ j,j0 ≤ j ∧ t ∈ Icc (time j) (time j+pulse j) then some h.choose else none

lemma pulseIndex_some {j0 j : ℕ} {t : ℝ} (hj : j0 ≤ j)
    (ht : t ∈ Icc (time j) (time j+pulse j)) : pulseIndex j0 t=some j := by
  classical
  unfold pulseIndex
  split_ifs with h
  · rw [pulse_unique h.choose_spec.2 ht]
  · exact (h ⟨j,hj,ht⟩).elim

lemma pulseIndex_spec {j0 j : ℕ} {t : ℝ} (h : pulseIndex j0 t=some j) :
    j0 ≤ j ∧ t ∈ Icc (time j) (time j+pulse j) := by
  classical
  unfold pulseIndex at h
  split_ifs at h with he
  · cases Option.some.inj h;exact he.choose_spec

lemma pulseIndex_none_iff {j0 : ℕ} {t : ℝ} : pulseIndex j0 t=none ↔
    ∀ j,j0 ≤ j → t ∉ Icc (time j) (time j+pulse j) := by
  constructor
  · intro h j hj ht
    rw [pulseIndex_some hj ht] at h;contradiction
  · intro h
    classical
    unfold pulseIndex
    split_ifs with he
    · exact (h he.choose he.choose_spec.1 he.choose_spec.2).elim
    · rfl

/-- The union of the physical closed pulse intervals is locally finite. -/
lemma pulseIndex_local_none {j0 : ℕ} {t : ℝ} (h : pulseIndex j0 t=none) :
    ∀ᶠ u in 𝓝 t,pulseIndex j0 u=none := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 (time_atTop.eventually_gt_atTop (t+1))
  have hf (i : Fin N) : ∀ᶠ u in 𝓝 t,j0 ≤ (i:ℕ) → u ∉ Icc (time i) (time i+pulse i) := by
    by_cases hi : j0 ≤ (i:ℕ)
    · have hh : ∀ᶠ u in 𝓝 t,u ∉ Icc (time i) (time i+pulse i) :=
        isClosed_Icc.isOpen_compl.mem_nhds (pulseIndex_none_iff.1 h i hi)
      exact hh.mono (fun _ hu _ => hu)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  have hf' : ∀ᶠ u in 𝓝 t,∀ i : Fin N,j0 ≤ (i:ℕ) → u ∉ Icc (time i) (time i+pulse i) :=
    Filter.eventually_all.2 hf
  filter_upwards [hf',eventually_lt_nhds (show t<t+1 by linarith)] with u hu hu'
  apply pulseIndex_none_iff.2
  intro j hj hjt
  by_cases hjN : j<N
  · exact hu ⟨j,hjN⟩ hj hjt
  · linarith [(hN j (le_of_not_gt hjN)),hjt.1]

lemma pulseIndex_local_some {j0 j : ℕ} {t : ℝ} (hj : j0 ≤ j)
    (ht : t ∈ Ioo (time j) (time j+pulse j)) :
    ∀ᶠ u in 𝓝 t,pulseIndex j0 u=some j := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
  exact pulseIndex_some hj ⟨hu.1.le,hu.2.le⟩

variable {n : ℕ}
/-- One angular choice for the ENTIRE infinite history. At all diagonal legs
it is the distinguished background choice `none`. -/
def globalSlot (d : ℝ → Fin n) (j0 : ℕ) (t : ℝ) : Option (Fin n) :=
  match pulseIndex j0 t with
  | none => none
  | some j => some (d ((t-time j)/pulse j))

lemma globalSlot_local_or_round (d : ℝ → Fin n)
    (hd : ∀ t,(∀ᶠ u in 𝓝 t,d u=d t) ∨
      (∀ᶠ u in 𝓝 t,∀ a : Fin n → ℝ,unitPacketScalar a u=0))
    (s : ℕ → Fin n → ℝ) (qstar : ℝ) (j0 : ℕ) (t : ℝ) :
    (∀ᶠ u in 𝓝 t,globalSlot d j0 u=globalSlot d j0 t) ∨
      (∀ᶠ u in 𝓝 t,scalar s qstar j0 u=1) := by
  cases h : pulseIndex j0 t with
  | none =>
    left;filter_upwards [pulseIndex_local_none h] with u hu
    simp only [globalSlot,hu,h]
  | some j =>
    obtain ⟨hj,hlo,hhi⟩ := pulseIndex_spec h
    by_cases hlo' : time j=t
    · subst t;exact Or.inr (scalar_start_collar s qstar hj)
    by_cases hhi' : t=time j+pulse j
    · subst t;exact Or.inr (scalar_end_collar s qstar hj)
    have ht : t ∈ Ioo (time j) (time j+pulse j) := ⟨lt_of_le_of_ne hlo hlo',lt_of_le_of_ne hhi hhi'⟩
    have hlocal := pulseIndex_local_some hj ht
    have hc : Tendsto (fun u => (u-time j)/pulse j) (𝓝 t) (𝓝 ((t-time j)/pulse j)) :=
      ((continuous_id.sub continuous_const).div_const _).continuousAt
    rcases hd ((t-time j)/pulse j) with he|he
    · left;filter_upwards [hlocal,hc.eventually he] with u hu he
      simp only [globalSlot,hu,h,he]
    · right;filter_upwards [isOpen_Ioo.mem_nhds ht,hc.eventually he] with u hu he
      rw [scalar_pulse s hj hu.1.le hu.2.le,he (s j),mul_zero,add_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Exact identification of the constructed angular stream with the genuine
Berger scalar/operator model for that SAME single global selector. -/
lemma angular_globalSlot (r : ℝ) (b D₀ : E) (D : Fin n → E)
    (d : ℝ → Fin n) (hd : ∀ t i,i ≠ d t → bump i (duration n*t)=0)
    (s : ℕ → Fin n → ℝ) (qstar : ℝ) (j0 : ℕ) (t : ℝ) :
    angular r b D₀ D s qstar j0 t=
      PulseTaylor.angular r b ((globalSlot d j0 t).elim D₀ D) (scalar s qstar j0 t) := by
  cases h : pulseIndex j0 t with
  | some j =>
    obtain ⟨hj,ht⟩ := pulseIndex_spec h
    rw [angular_pulse r b D₀ D s hj ht.1 ht.2,
      nonlinearBergerWord_selected r b D (s j) (pulse j) ((t-time j)/pulse j)
        (d ((t-time j)/pulse j)) (hd _),
      scalar_pulse s hj ht.1 ht.2]
    simp only [globalSlot,h,Option.elim]
  | none =>
    simp only [globalSlot,h,Option.elim]
    by_cases ht : t ≤ time j0
    · rw [angular_initial r b D₀ D s ht,scalar_initial s ht,PulseTaylor.angular]
      simp
    · obtain ⟨j,hj,hlo,hhi⟩ := GlobalGrowth.grid_bracket time_atTop j0 (le_of_not_ge ht)
      have hn := pulseIndex_none_iff.1 h j hj
      have htt : time j+pulse j ≤ t := le_of_lt (lt_of_not_ge (fun hh => hn ⟨hlo,hh⟩))
      rw [angular_leg r b D₀ D s hj htt hhi,scalar_leg s hj htt hhi]
end HarmonicCounterexample.AngularStream

end

end OAI
