import OAI.Analysis.FourierLLogL.Thermal.Form

/-! # Positive Fourier expansions -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Real Period

variable {M : ℕ}

private def ac (f : Grid M → ℝ) (x : Grid M) := (fc (fun y => (↑(f y):ℂ)) x).re
private lemma ac_mul (f g : Grid M → ℝ) (hf : f.Even) (hg : g.Even) (x : Grid M) :
    ac (fun y => f y*g y) x = ∑ u : Grid M, ac f u * ac g (x-u) := by
  unfold ac
  simp_rw [Complex.ofReal_mul]; rw [fc_prod,Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [← real_fc_even f hf i,← real_fc_even g hg (x-i)]
  simp

private lemma ac_scale (f : Grid M → ℝ) (a : ℝ) (x : Grid M) :
    ac (fun y => a*f y) x = a*ac f x := by
  simp_rw [ac,Complex.ofReal_mul]
  rw [fc_lmul]; simp

private lemma ac_sum {ι : Type*} (s : Finset ι) (f : ι → Grid M → ℝ) (x : Grid M) :
    ac (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, ac (f i) x := by
  simp_rw [ac,Complex.ofReal_sum]; rw [fc_sum,Complex.re_sum]

private lemma ac_const (x : Grid M) : ac (fun _ => 1) x =
    if x=0 then 1 else 0 := by
  unfold ac
  simp_rw [Complex.ofReal_one]
  rw [← funext chi_zero_left,fc_chi]
  split_ifs <;> simp_all

private lemma ac_wave (s x : Grid M) :
    ac (wave s) x = ((if s=x then 1 else 0)+(if -s=x then 1 else 0))/2 := by
  have he (y : Grid M) : (↑(wave s y):ℂ) = 2⁻¹*(chi s y + chi (-s) y) := by
    rw [wave,chi_neg']
    rw [Complex.re_eq_add_conj]
    ring
  unfold ac; simp_rw [he]
  rw [fc_lmul,fc_add,fc_chi,fc_chi]
  split_ifs <;> norm_num

/-- cosine series Taylor argument -/
private def blend (A : Form M) (y : Grid M) := ∑ i, A i * wave i y

private lemma blend_even (A : Form M) : (blend A).Even := by intro i; simp [blend,wave_even _ i]
private lemma blend_boltz (A : Form M) (x : Grid M) :
    boltz A x = exp (-(∑ i, A i)) * exp (blend A x) := by
  simp_rw [boltz,form,blend,cost,mul_sub,Finset.sum_sub_distrib,mul_one,← exp_add]
  congr 1; ring

private lemma blend_spec (A : Form M) (x : Grid M) :
    ac (blend A) x = ∑ i, A i * ac (wave i) x := by
  unfold blend
  simp_rw [ac_sum,ac_scale]

private lemma blend_ac_nonneg {A : Form M} (hA : 0 ≤ A) (x : Grid M) :
    0 ≤ ac (blend A) x := by
  rw [blend_spec]
  apply Finset.sum_nonneg; intro i _
  apply mul_nonneg (hA i)
  rw [ac_wave]; split_ifs <;> norm_num

private lemma blend_ac_pos {A : Form M} (hA : 0 ≤ A) {x : Grid M}
    (hx : 0 < A x) : 0 < ac (blend A) x := by
  rw [blend_spec]
  apply lt_of_lt_of_le (b:=A x * ac (wave x) x)
  · apply mul_pos hx; rw [ac_wave,ite_eq_left rfl]; split_ifs <;> norm_num
  apply Finset.single_le_sum (f:=fun i => A i * ac (wave i) x) _ (Finset.mem_univ x)
  intro i _
  apply mul_nonneg (hA i); rw [ac_wave]; split_ifs <;> norm_num

private lemma blend_pow_even (A : Form M) (n : ℕ) : (fun y => blend A y^n).Even :=
  fun y => by dsimp; rw [blend_even _ y]

private lemma blend_pow_ac_nonneg {A : Form M} (hA : 0 ≤ A) (n : ℕ) (x : Grid M) :
    0 ≤ ac (fun y => blend A y^n) x := by
  induction n generalizing x with
  | zero => simp_rw [pow_zero,ac_const]; split_ifs <;> norm_num
  | succ n ih =>
    simp_rw [pow_succ]; rw [ac_mul _ _ (blend_pow_even _ _) (blend_even _)]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (ih i) (blend_ac_nonneg hA _)

private lemma blend_pow_ac_pos {A : Form M} (hA : 0 ≤ A) (n : ℕ) {x : Grid M}
    (hx : 0 < A x) : 0 < ac (fun y => blend A y^n) (n • x) := by
  induction n with
  | zero => simp [ac_const]
  | succ n ih =>
    simp_rw [pow_succ]; rw [ac_mul _ _ (blend_pow_even _ _) (blend_even _)]
    apply lt_of_lt_of_le (b:=ac (fun y => blend A y ^n) (n • x)*ac (blend A) ((n+1)•x-n•x))
    · rw [add_smul,one_smul,add_sub_cancel_left]
      exact mul_pos ih (blend_ac_pos hA hx)
    apply Finset.single_le_sum (f:=fun u => ac (fun y => blend A y ^n) u * ac (blend A) ((n+1)•x-u)) _ (Finset.mem_univ (n•x))
    intro i _
    exact mul_nonneg (blend_pow_ac_nonneg hA n _) (blend_ac_nonneg hA _)

/-- Exp series truncated. -/
def aprox (n : ℕ) (v : ℝ) := ∑ i ∈ Finset.range n, (i.factorial:ℝ)⁻¹*v^i

lemma aprox_lim (v : ℝ) : Tendsto (fun n : ℕ => aprox n v) atTop (𝓝 (exp v)) := by
  simpa only [aprox, Real.exp_eq_exp_ℝ,div_eq_inv_mul] using
    (NormedSpace.expSeries_div_hasSum_exp v).tendsto_sum_nat

private lemma ac_lim (f : ℕ → Grid M → ℝ) (g : Grid M → ℝ) (x : Grid M)
    (h : ∀ y, Tendsto (fun n => f n y) atTop (𝓝 (g y))) :
    Tendsto (fun n => ac (f n) x) atTop (𝓝 (ac g x)) := by
  unfold ac fc expU
  apply Complex.continuous_re.continuousAt.tendsto.comp
  simp only [Complex.real_smul]
  refine Tendsto.const_mul _ <| tendsto_finsetSum _ ?_
  intro y _
  exact Tendsto.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp (h y)) tendsto_const_nhds

private lemma blend_part_le_exp {A : Form M} (hA : 0 ≤ A) (x : Grid M) (n : ℕ) :
    (n.factorial:ℝ)⁻¹ * ac (fun y => blend A y ^ n) x ≤
      ac (fun y => exp (blend A y)) x := by
  apply ge_of_tendsto (ac_lim (fun n y => aprox n (blend A y)) _ x
    (fun y => aprox_lim _))
  filter_upwards [eventually_ge_atTop (n+1)] with k hk
  simp_rw [aprox,ac_sum,ac_scale]
  apply Finset.single_le_sum _ (Finset.mem_range.mpr hk)
  intro i _
  exact mul_nonneg (by positivity) (blend_pow_ac_nonneg hA _ _)

lemma q_nonneg {A : Form M} (hA : 0 ≤ A) (x : Grid M) : 0 ≤ q A x := by
  change 0 ≤ ac (boltz A) x
  rw [show boltz A = _ from funext (blend_boltz A),ac_scale]
  exact mul_nonneg (exp_nonneg _) (le_trans
    (mul_nonneg (by positivity) (blend_pow_ac_nonneg hA 0 _)) (blend_part_le_exp hA x 0))

lemma q_pos_one {A : Form M} (hA : 0 ≤ A) (h : 0 < A 1) (x : Grid M) : 0 < q A x := by
  change 0 < ac (boltz A) x
  rw [show boltz A = _ from funext (blend_boltz A),ac_scale]
  apply mul_pos (exp_pos _)
  apply lt_of_lt_of_le _ (blend_part_le_exp hA x x.val)
  have hi : 0 < ac (fun y => blend A y ^ x.val) (x.val • 1) := blend_pow_ac_pos hA _ h
  rw [nsmul_one, ZMod.natCast_zmod_val] at hi
  exact mul_pos (by positivity) hi

lemma cred_nonneg {A : Form M} (hA : 0 ≤ A) (x : Grid M) : 0 ≤ cred A x :=
  div_nonneg (q_nonneg hA x) (q_origin_pos A).le

lemma norm_fc_translate_boltz {A : Form M} (hA : 0 ≤ A) (a u : Grid M) :
    ‖fc (fun y => (↑(boltz A (a-y)):ℂ)) u‖ = q A u := by
  have hi (y : Grid M) : boltz A (a-y) = boltz A (y-a) := by
    rw [show a-y = -(y-a) by ring,boltz_even _ _]
  simp_rw [hi]
  rw [fc_right_translate (fun y => (↑(boltz A y):ℂ)) a u,norm_mul,norm_chi,one_mul,← cq, Complex.norm_real,
     Real.norm_eq_abs, abs_of_nonneg (q_nonneg hA _)]

lemma envelope {ι : Type*} (s : Finset ι) (f : ι → Form M) (h : ∀ i ∈ s, 0 ≤ f i)
    (a : ι → Grid M) (u : Grid M) :
    ‖fc (fun y => ∏ i ∈ s, (↑(boltz (f i) (a i-y)):ℂ)) u‖ ≤ q (∑ i ∈ s, f i) u := by
  classical
  induction s using Finset.induction_on generalizing u with
  | empty =>
    apply le_of_eq
    convert norm_fc_translate_boltz (M:=M) (le_refl (0:Form M)) 0 u using 1 <;>
      simp [boltz,form_zero]
  | @insert i s hi ih =>
    have H := h i (Finset.mem_insert_self _ _)
    have HH (j) (hj : j∈s) : 0 ≤ f j := h j (Finset.mem_insert_of_mem hj)
    simp_rw [Finset.sum_insert hi, Finset.prod_insert hi]
    rw [q_add,fc_prod]
    apply (norm_sum_le _ _).trans
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul,norm_fc_translate_boltz H]
    exact mul_le_mul_of_nonneg_left (ih HH _) (q_nonneg H j)

end FourierLLogL.Dyadic.Thermal

end OAI
