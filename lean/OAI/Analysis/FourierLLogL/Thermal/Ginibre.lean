import OAI.Analysis.FourierLLogL.Thermal.Positive

/-! # Cosine covariance. On an even cyclic group the two-copy change of variables
uses two branches (one of them half-translated). -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Period Real

variable {M : ℕ}

private lemma chi_one_ne {s : Grid M} (hs : s ≠ 0) : chi s 1 ≠ 1 := by
  intro H
  have hi (x : Grid M) : chi s x = 1 := by
    rw [chi_comm,← ZMod.natCast_zmod_val x,← nsmul_one,chi_nsmul,chi_comm 1 s,H,one_pow]
  have hh := expU_chi s
  rw [ite_eq_right hs,funext hi,← funext chi_zero_left,expU_chi,ite_eq_left rfl] at hh
  norm_num at hh

private lemma odd_phase {s : Grid M} (hs : s ≠ 0) (h : s+s=0) : chi s 1 = -1 := by
  have H1 : chi s 1 * chi s 1 = 1 := by rw [← chi_add', h,chi_zero_left]
  have H2 : (chi s 1 - 1)*(chi s 1+1)=0 := by rw [show
    (chi s 1 - 1)*(chi s 1+1)= chi s 1 * chi s 1-1 by ring,H1,sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero H2 with h1|h1
  · exact (chi_one_ne hs (sub_eq_zero.mp h1)).elim
  · exact eq_neg_of_add_eq_zero_left h1

private lemma ch_parity (s : Grid M) :
    expU (fun i => chi s (i+i)) + expU (fun i => chi s (1+(i+i))) = 2 * expU (chi s) := by
  have hi (i : Grid M) : chi s (i+i) = chi (s+s) i := by rw [chi_add,chi_add']
  simp_rw [chi_add _ 1,hi]
  rw [expU_lmul,expU_chi,expU_chi]
  by_cases hs : s=0
  · subst s; simp [chi_zero_left]; ring
  rw [ite_eq_right hs]
  split_ifs with H
  · rw [odd_phase hs H]; ring
  ring

private lemma c_parity (f : Grid M → ℂ) :
    expU (fun i => f (i+i)) + expU (fun i => f (1+(i+i))) = 2 * expU f := by
  let g (x : Grid M) := ∑ s, fc f s * chi s x
  suffices HH : expU (fun i => g (i+i)) + expU (fun i => g (1+(i+i))) = 2 * expU g by
    have hi : g=f := funext (invert_fc _)
    rwa [hi] at HH
  unfold g
  simp_rw [expU_sum,expU_lmul]
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add,ch_parity]; ring

private lemma r_parity (f : Grid M → ℝ) :
    expU (fun i => f (i+i)) + expU (fun i => f (1+(i+i))) = 2 * expU f := by
  have hi := c_parity (fun x => (↑(f x):ℂ))
  simp_rw [expU_real] at hi
  exact_mod_cast hi

private def dblmean (f : Grid M → Grid M → ℝ) : ℝ := expU fun x => expU (f x)
private lemma dbl_ex (f : Grid M → Grid M → ℝ) (P : Law (Grid M))
    (hP : P = uniform _) : dblmean f = P.Ex fun x => P.Ex (f x) := by simp_rw [hP,dblmean,expU_ex]

private def branch (f : Grid M → Grid M → ℝ) (c : Grid M) :=
  dblmean (fun i j => f (c+i+j) (i-j))

private lemma branch_eq (f : Grid M → Grid M → ℝ) (c : Grid M) :
    branch f c = expU (fun u => expU fun i => f u (c+(i+i)-u)) := by
  unfold branch dblmean
  rw [expU_prod (fun u i : Grid M => f u (c+(i+i)-u))]
  refine congrArg expU (funext fun i => ?_)
  dsimp
  rw [← expU_translate (fun u => f u (c+(i+i)-u)) (c+i)]
  refine congrArg expU (funext fun j => ?_)
  have H : c+(i+i)-(c+i+j)=i-j := by ring
  simp only [H]

private lemma branch_sum (f : Grid M → Grid M → ℝ) :
    branch f 0 + branch f 1 = 2 * dblmean f := by
  simp_rw [branch_eq,dblmean,zero_add, expU_ex]
  rw [← Ex_add, ← Ex_lmul]
  refine congrArg (uniform (Grid M)).Ex (funext fun u => ?_)
  simp_rw [← expU_ex]
  rw [r_parity (fun a => f u (a-u))]
  rw [show (fun a => f u (a-u)) = (fun a => f u (-u+a)) from funext fun a => by
    have H : a-u=-u+a := by ring
    rw [H]]
  rw [expU_translate]

private def halfWave (s c : Grid M) : ℂ :=
  phase (s.val : ℝ) (pos c/2)

private def unitWave (s c i : Grid M) := halfWave s c * chi s i

private lemma half_mul (s c : Grid M) : halfWave s c * halfWave s c = chi s c := by
  rw [halfWave,← phase_add, show pos c /2+pos c/2=pos c by ring]
  have H := chi_cast (s.val:ℤ) c
  simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using H.symm

private lemma branch_waves (s c i j : Grid M) :
    wave s (c+i+j) + wave s (i-j) =
        2*(unitWave s c i).re*(unitWave s c j).re ∧
    wave s (c+i+j) - wave s (i-j) =
        -(2*(unitWave s c i).im*(unitWave s c j).im) := by
  have Hn : halfWave s c * conj (halfWave s c) = 1 := by
    rw [Complex.mul_conj,←Complex.sq_norm,(show ‖halfWave s c‖=1 from phase_unimod _ _)]
    simp
  have He : chi s (c+i+j) = unitWave s c i * unitWave s c j := by
    unfold unitWave
    rw [chi_add,chi_add,← half_mul]
    ring
  have Hf : chi s (i-j) = unitWave s c i * conj (unitWave s c j) := by
    unfold unitWave
    rw [chi_sub,map_mul]
    rw [show halfWave s c * chi s i * (conj (halfWave s c) * conj (chi s j))
          = (chi s i * conj (chi s j)) * (halfWave s c * conj (halfWave s c)) by ring,Hn,mul_one]
  simp only [wave,He,Hf,Complex.mul_re, Complex.conj_re, Complex.conj_im]
  constructor <;> ring

private def bil (f : Grid M → Grid M → ℝ) (h : Grid M → ℝ) : ℝ :=
  dblmean fun i j => h i*h j * f i j

private def pairPot (A : Form M) (R : Grid M → Grid M → ℝ) (i j : Grid M) :=
  ∑ s, A s * R s i * R s j

private lemma bil_sum {ι : Type*} (s : Finset ι) (f : ι → Grid M → Grid M → ℝ) (h : Grid M → ℝ) :
    bil (fun i j => ∑ k ∈ s, f k i j) h = ∑ k ∈ s, bil (f k) h := by
  simp_rw [bil,dblmean, Finset.mul_sum, expU_sum]

private lemma dblmean_scale (c : ℝ) (f : Grid M → Grid M → ℝ) :
    dblmean (fun i j => c*f i j) = c * dblmean f := by
  simp_rw [dbl_ex _ (uniform _) rfl,Ex_lmul]

private lemma bil_scale (c : ℝ) (f : Grid M → Grid M → ℝ) (h : Grid M → ℝ) :
    bil (fun i j => c*f i j) h = c*bil f h := by
  unfold bil
  rw [← dblmean_scale]
  congr 1; funext i j; ring

private lemma pair_nonneg {A : Form M} (hA : 0 ≤ A) (R : Grid M → Grid M → ℝ) (h : Grid M → ℝ)
    (n : ℕ) :
    0 ≤ bil (fun i j => (pairPot A R i j)^n) h := by
  induction n generalizing h with
  | zero =>
    unfold bil dblmean
    simp_rw [pow_zero, mul_one, expU_ex, Ex_lmul,Ex_mul]
    exact mul_self_nonneg _
  | succ n ih =>
    let f := pairPot A R
    have heq :
        bil (fun i j => (f i j)^(n+1)) h =
          ∑ s : Grid M, A s * bil (fun i j => (f i j)^n) (fun i => h i * R s i) := by
      have He (i j : Grid M) : f i j ^(n+1) =
          ∑ s, A s*(R s i*R s j*(f i j)^n) := by
        rw [pow_succ]
        dsimp only [f,pairPot]; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      simp_rw [He,bil_sum,bil_scale]
      refine Finset.sum_congr rfl fun s _ => congrArg (A s*·) ?_
      unfold bil; refine congrArg dblmean ?_; funext i j; ring
    rw [heq]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hA s) (ih _)

private lemma pair_exp_nonneg {A : Form M} (hA : 0 ≤ A) (R : Grid M → Grid M → ℝ) (h : Grid M → ℝ) :
    0 ≤ bil (fun i j => exp (pairPot A R i j)) h := by
  let f := pairPot A R
  have hi : Tendsto (fun n => bil (fun i j => aprox n (f i j)) h)
      atTop (𝓝 (bil (fun i j => exp (f i j)) h)) := by
    simp only [bil,dblmean,expU,smul_eq_mul]
    refine Tendsto.const_mul _ <| tendsto_finsetSum _ fun i _ => ?_
    refine Tendsto.const_mul _ <| tendsto_finsetSum _ fun j _ => ?_
    exact Tendsto.const_mul _ (aprox_lim _)
  apply ge_of_tendsto hi (Eventually.of_forall fun n => ?_)
  simp_rw [aprox,bil_sum,bil_scale]
  exact Finset.sum_nonneg fun s _ => mul_nonneg (by positivity) (pair_nonneg hA _ _ s)

private lemma branch_pos {A : Form M} (hA : 0 ≤ A) (s t c : Grid M) :
    0 ≤ branch (fun y z => K A y*K A z * ((wave s y-wave s z)*(wave t y-wave t z))) c := by
  let U := fun s i => unitWave s c i
  let R := fun s i => (U s i).re
  let h := fun i => (U s i).im*(U t i).im
  let D := (2:ℝ) • A
  let w := 2*(F A-∑ i, A i)
  have HK (i j : Grid M) :
      K A (c+i+j)* K A (i-j) = exp w * exp (pairPot D R i j) := by
    simp_rw [K_eq,← exp_add]
    have He : form A (c+i+j) + form A (i-j) =
        2*∑ i, A i - pairPot D R i j := by
      dsimp [form,pairPot,D]; rw [← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by
        dsimp only [cost,smul_eq_mul,R,U]
        have H := (branch_waves k c i j).1
        linear_combination -(A k) * H
    unfold w
    congr 1
    linarith
  unfold branch
  have Heq :
      (fun i j => K A (c+i+j) * K A (i-j) *
          ((wave s (c+i+j)-wave s (i-j)) * (wave t (c+i+j)-wave t (i-j)))) =
        (fun i j => 4*exp w * (h i * h j * exp (pairPot D R i j))) := by
    funext i j
    rw [HK,(branch_waves _ _ _ _).2,(branch_waves _ _ _ _).2]
    unfold h U; ring
  rw [Heq,dblmean_scale]
  exact mul_nonneg (by positivity) <| pair_exp_nonneg (by
    intro i
    change 0 ≤ 2*A i
    exact mul_nonneg (by norm_num) (hA i)) R h

theorem ginibre {A : Form M} (hA : 0 ≤ A) (s t : Grid M) :
    cred A s * cred A t ≤ (label A).Ex (fun i => wave s i * wave t i) := by
  let P := label A
  let f : Grid M → Grid M → ℝ :=
    fun i j => (wave s i-wave s j) * (wave t i-wave t j)
  let g : Grid M → Grid M → ℝ :=
    fun i j => K A i*K A j*f i j
  have H := branch_sum g
  have H1 := branch_pos hA s t 0
  have H2 := branch_pos hA s t 1
  change 0 ≤ branch g _ at H1 H2
  have heq :
      dblmean g = P.Ex fun i => P.Ex (f i) := by
    unfold P; simp_rw [label_ex,dblmean,expU_ex,g,mul_assoc,Ex_lmul]
  have He (i j : Grid M) : f i j =
      ((wave s i * wave t i + wave s j * wave t j) - wave s j * wave t i) - wave s i*wave t j := by
    unfold f; ring
  rw [heq] at H
  have Heq (i : Grid M) : P.Ex (f i) =
      ((wave s i*wave t i + P.Ex (fun i => wave s i * wave t i))
        - P.Ex (wave s)*wave t i) - wave s i * P.Ex (wave t) := by
    rw [funext (He i)]; simp_rw [Ex_sub,Ex_add,Ex_lmul,Ex_mul,Ex_const]
  simp_rw [Heq,Ex_sub,Ex_add,Ex_lmul,Ex_mul,Ex_const] at H
  rw [cred_ex,cred_ex]
  change P.Ex _ * P.Ex _ ≤ P.Ex _
  nlinarith

end FourierLLogL.Dyadic.Thermal

end OAI
