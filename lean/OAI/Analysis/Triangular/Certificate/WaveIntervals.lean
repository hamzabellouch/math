import OAI.Analysis.Triangular.Basic

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction

def TailNodes : Set ℤ := {n | 0 < n ∧ n % 36 ∈ residues ∧ n ∉ FiniteNodes}

def rootProduct (s : ℂ) : ℂ := ∏ a : Fin 15, sineFactor a s

theorem P_eq_square (s : ℂ) : P s = rootProduct s ^ 2 := by
  simp only [P, rootProduct, Finset.prod_pow]

theorem differentiable_rootProduct : Differentiable ℂ rootProduct := by
  unfold rootProduct sineFactor
  fun_prop

theorem differentiable_P : Differentiable ℂ P := by
  unfold P sineFactor
  fun_prop

theorem node_residue (n : Node) : ∃ a : Fin 15, n.val % 36 = residue a := by
  have hn := n.property.2
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | exact ⟨0,h⟩ | exact ⟨1,h⟩ | exact ⟨2,h⟩ | exact ⟨3,h⟩
    | exact ⟨4,h⟩ | exact ⟨5,h⟩ | exact ⟨6,h⟩ | exact ⟨7,h⟩
    | exact ⟨8,h⟩ | exact ⟨9,h⟩ | exact ⟨10,h⟩ | exact ⟨11,h⟩
    | exact ⟨12,h⟩ | exact ⟨13,h⟩ | exact ⟨14,h⟩

theorem rootProduct_node (n : Node) : rootProduct n.val = 0 := by
  obtain ⟨a,ha⟩ := node_residue n
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  have hn : (n.val : ℂ) - residue a = 36 * (n.val / 36 : ℤ) := by
    have hh := Int.emod_add_mul_ediv n.val 36
    rw [ha] at hh
    have hc := congrArg (fun x : ℤ => (x : ℂ)) hh
    push_cast at hc
    linear_combination -hc
  unfold sineFactor
  rw [hn]
  have he : (kappa : ℂ) * (36 * (n.val / 36 : ℤ)) =
      (n.val / 36 : ℤ) * (Real.pi : ℂ) := by
    unfold kappa
    push_cast
    ring
  rw [he]
  have hz := congrArg Complex.ofReal (Real.sin_int_mul_pi (n.val / 36))
  have hh : Complex.sin ((n.val / 36 : ℤ) * (Real.pi : ℂ)) = 0 := by
    simpa only [Complex.ofReal_zero, Complex.ofReal_sin, Complex.ofReal_mul,
      Complex.ofReal_intCast] using hz
  rw [hh, mul_zero]

theorem P_node (n : Node) : P n.val = 0 := by
  rw [P_eq_square, rootProduct_node]
  norm_num

theorem hasDerivAt_P_node (n : Node) : HasDerivAt P 0 (n.val : ℂ) := by
  have hh := (differentiable_rootProduct (n.val : ℂ)).hasDerivAt.pow 2
  have he : (rootProduct ^ 2) = P := funext fun s => (P_eq_square s).symm
  simpa [he, rootProduct_node] using hh

theorem deriv_P_node (n : Node) : deriv P n.val = 0 := (hasDerivAt_P_node n).deriv

theorem differentiable_dBasis (n : Node) : Differentiable ℂ (dBasis n) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr
    differentiable_P.differentiableOn

theorem differentiable_cBasis (n : Node) : Differentiable ℂ (cBasis n) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr
    (differentiable_dBasis n).differentiableOn

theorem dBasis_node (n : Node) : dBasis n n.val = 0 := by
  simp [dBasis, dslope_same, deriv_P_node]

theorem dBasis_eq (n : Node) {s : ℂ} (hs : s ≠ (n.val : ℂ)) :
    dBasis n s = P s / (s-n.val) := by
  simp [dBasis, dslope_of_ne _ hs, slope_def_field, P_node]

theorem cBasis_eq (n : Node) {s : ℂ} (hs : s ≠ (n.val : ℂ)) :
    cBasis n s = P s / (s-n.val)^2 := by
  rw [cBasis, dslope_of_ne _ hs, slope_def_field, dBasis_node,
    sub_zero, dBasis_eq n hs, div_div, pow_two]

theorem differentiable_finiteC (a : Fin 15) : Differentiable ℂ (finiteC a) := by
  unfold finiteC sineFactor
  fun_prop

theorem differentiable_finiteD (a : Fin 15) : Differentiable ℂ (finiteD a) := by
  unfold finiteD sineFactor
  fun_prop

theorem P_factor (a : Fin 15) (s : ℂ) :
    P s = (sineFactor a s)^2 * ∏ r ∈ Finset.univ.erase a, (sineFactor r s)^2 := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm

theorem finiteC_eq (a : Fin 15) (s : ℂ)
    (hs : Complex.sin ((kappa : ℂ) * (s - (residue a : ℂ))) ≠ 0) :
    finiteC a s = (kappa : ℂ)^2 * P s /
      (Complex.sin ((kappa : ℂ) * (s - (residue a : ℂ))))^2 := by
  rw [P_factor a s]
  unfold finiteC sineFactor
  field_simp
  ring

theorem finiteD_eq (a : Fin 15) (s : ℂ)
    (hs : Complex.sin ((kappa : ℂ) * (s - (residue a : ℂ))) ≠ 0) :
    finiteD a s = (kappa : ℂ) * P s *
      (Complex.cos ((kappa : ℂ) * (s - (residue a : ℂ)))) /
      Complex.sin ((kappa : ℂ) * (s - (residue a : ℂ))) := by
  rw [P_factor a s]
  unfold finiteD sineFactor
  field_simp

theorem phase_add (s t : ℂ) : phase (s+t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  ring

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_neg_mul (s : ℂ) : phase (-s) * phase s = 1 := by
  rw [← phase_add, neg_add_cancel, phase_zero]

theorem sineFactor_sq (a : Fin 15) (s : ℂ) :
    sineFactor a s ^ 2 = 2 - phase ((residue a : ℂ)-s) -
      phase (s-(residue a : ℂ)) := by
  let z : ℂ := (kappa : ℂ) * (s-(residue a : ℂ))
  have hpos : phase (s-(residue a : ℂ)) = Complex.exp ((2*z)*Complex.I) := by
    unfold phase z kappa
    push_cast
    congr 1
    ring
  have hneg : phase ((residue a : ℂ)-s) = Complex.exp (-(2*z)*Complex.I) := by
    unfold phase z kappa
    push_cast
    congr 1
    ring
  change (2 * Complex.sin z)^2 = _
  rw [hpos,hneg]
  have hc := Complex.two_cos (2*z)
  rw [Complex.cos_two_mul] at hc
  have hs := Complex.sin_sq_add_cos_sq z
  linear_combination 4*hs - hc

open Polynomial

theorem eval_atomFactor (a : Fin 15) (s : ℂ) :
    phase (-s) * (atomFactor a).eval (phase s) = sineFactor a s ^ 2 := by
  simp only [atomFactor,eval_sub,eval_add,eval_neg,eval_C,eval_mul,eval_X,eval_pow]
  rw [sineFactor_sq]
  have h1 : phase (-s) * phase (residue a) = phase ((residue a : ℂ)-s) := by
    rw [← phase_add]
    congr 1
    ring
  have h2 : phase (-residue a) * phase s = phase (s-(residue a : ℂ)) := by
    rw [← phase_add]
    congr 1
    ring
  have h0 := phase_neg_mul s
  linear_combination -h1 - phase (-residue a) * phase s * h0 - h2 + 2*h0

theorem P_spectral (s : ℂ) :
    P s = phase (-s)^15 * atomPolynomial.eval (phase s) := by
  unfold P atomPolynomial
  simp only [Polynomial.eval_prod]
  calc
    (∏ a : Fin 15, sineFactor a s ^ 2) =
        ∏ a : Fin 15, phase (-s) * (atomFactor a).eval (phase s) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact (eval_atomFactor a s).symm
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem finiteC_spectral (a : Fin 15) (s : ℂ) :
    finiteC a s = phase (-s)^14 * (cAtomPolynomial a).eval (phase s) := by
  unfold finiteC cAtomPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  have hp : (∏ r ∈ Finset.univ.erase a, sineFactor r s ^ 2) =
      phase (-s)^14 * ∏ r ∈ Finset.univ.erase a, (atomFactor r).eval (phase s) := by
    calc
      _ = ∏ r ∈ Finset.univ.erase a, phase (-s) * (atomFactor r).eval (phase s) := by
        apply Finset.prod_congr rfl
        intro r hr
        exact (eval_atomFactor r s).symm
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hp]
  ring

theorem finiteD_factor (a : Fin 15) (s : ℂ) :
    2 * (kappa : ℂ) * sineFactor a s *
      Complex.cos ((kappa : ℂ) * (s - (residue a : ℂ))) =
    Complex.I * (kappa : ℂ) *
      (phase ((residue a : ℂ)-s)-phase (s-(residue a : ℂ))) := by
  let z : ℂ := (kappa : ℂ) * (s-(residue a : ℂ))
  have hpos : phase (s-(residue a : ℂ)) = Complex.exp ((2*z)*Complex.I) := by
    unfold phase z kappa
    push_cast
    congr 1
    ring
  have hneg : phase ((residue a : ℂ)-s) = Complex.exp (-(2*z)*Complex.I) := by
    unfold phase z kappa
    push_cast
    congr 1
    ring
  rw [hpos,hneg]
  change 2 * (kappa : ℂ) * (2 * Complex.sin z) * Complex.cos z = _
  have hs := Complex.two_sin (2*z)
  rw [Complex.sin_two_mul] at hs
  linear_combination (kappa : ℂ)*hs

theorem rest_spectral (a : Fin 15) (s : ℂ) :
    (∏ r ∈ Finset.univ.erase a, sineFactor r s ^ 2) =
      phase (-s)^14 * ∏ r ∈ Finset.univ.erase a, (atomFactor r).eval (phase s) := by
  calc
    _ = ∏ r ∈ Finset.univ.erase a, phase (-s) * (atomFactor r).eval (phase s) := by
      apply Finset.prod_congr rfl
      intro r hr
      exact (eval_atomFactor r s).symm
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem finiteD_spectral (a : Fin 15) (s : ℂ) :
    finiteD a s = phase (-s)^15 * (dAtomPolynomial a).eval (phase s) := by
  unfold finiteD dAtomPolynomial
  rw [finiteD_factor a s, rest_spectral a s]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  have hh : phase (-s) *
      (phase (residue a) - phase (-residue a) * phase s^2) =
      phase ((residue a : ℂ)-s) - phase (s-(residue a : ℂ)) := by
    have h1 : phase (-s) * phase (residue a) = phase ((residue a : ℂ)-s) := by
      rw [← phase_add]
      congr 1
      ring
    have h2 : phase (-residue a) * phase s = phase (s-(residue a : ℂ)) := by
      rw [← phase_add]
      congr 1
      ring
    have h0 := phase_neg_mul s
    linear_combination h1 - phase (-residue a) * phase s * h0 - h2
  rw [← hh]
  ring

theorem atomFactor_degree (a : Fin 15) : (atomFactor a).natDegree ≤ 2 := by
  unfold atomFactor
  compute_degree!

theorem atomPolynomial_degree : atomPolynomial.natDegree ≤ 30 := by
  unfold atomPolynomial
  apply le_trans (Polynomial.natDegree_prod_le _ _) 
  calc
    ∑ a : Fin 15, (atomFactor a).natDegree ≤ ∑ a : Fin 15, 2 :=
      Finset.sum_le_sum (fun a _ => atomFactor_degree a)
    _ = 30 := by norm_num

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma phase_nat_mul (n : ℕ) (s : ℂ) : phase s ^ n = phase (n*s) := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma phase_offset (j : Fin 31) (s : ℂ) :
    phase (-s)^15 * phase s^j.val =
      Complex.exp (Complex.I * (Real.pi:ℂ) * (frequency j:ℂ) * s) := by
  rw [phase_nat_mul, phase_nat_mul, ← phase_add]
  unfold phase frequency
  push_cast
  congr 1
  ring

lemma P_fourier (s : ℂ) : P s = ∑ j : Fin 31,
    fourierCoeff j * Complex.exp (Complex.I * (Real.pi:ℂ) * (frequency j:ℂ) * s) := by
  rw [P_spectral, Polynomial.eval_eq_sum_range' (n := 31) (by have := atomPolynomial_degree; omega)]
  rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change phase (-s)^15 * (fourierCoeff j * phase s^j.val) = _
  rw [mul_left_comm, phase_offset]

lemma phase_int_mod (n : ℤ) : phase (n:ℂ) = phase ((n%36:ℤ):ℂ) := by
  have hn : (n:ℂ) = ((n%36:ℤ):ℂ) + 36*((n/36:ℤ):ℂ) := by
    have h := congrArg (fun x : ℤ => (x:ℂ)) (Int.emod_add_mul_ediv n 36)
    push_cast at h
    exact h.symm
  rw [hn, phase_add]
  have hp : phase (36*((n/36:ℤ):ℂ)) = 1 := by
    unfold phase
    convert Complex.exp_int_mul_two_pi_mul_I (n/36) using 1
    congr 1
    ring
  rw [hp, mul_one]

lemma wave_phase_integer (j : Fin 31) (n : ℤ) :
    exp (I*Real.pi*frequency j*(n:ℂ)) = phase ((((j.val:ℤ)-15)*n : ℤ):ℂ) := by
  unfold phase frequency
  push_cast
  congr 1
  ring

lemma waveDerivative_zero : waveDerivative 0 = P := by
  ext s
  simp only [waveDerivative, pow_zero, mul_one, P_fourier]

lemma hasDerivAt_waveDerivative (k : ℕ) (s : ℂ) :
    HasDerivAt (waveDerivative k) (waveDerivative (k+1) s) s := by
  have hh (j : Fin 31) : HasDerivAt
      (fun x : ℂ => fourierCoeff j * (I*Real.pi*frequency j)^k * exp (I*Real.pi*frequency j*x))
      (fourierCoeff j * (I*Real.pi*frequency j)^(k+1) * exp (I*Real.pi*frequency j*s)) s := by
    have hj := ((hasDerivAt_id s).const_mul (I*(Real.pi:ℂ)*(frequency j:ℂ))).cexp.const_mul
      (fourierCoeff j * (I*Real.pi*frequency j)^k)
    simpa only [mul_one, one_mul, pow_succ, mul_assoc, id_eq, mul_comm, mul_left_comm] using hj
  exact HasDerivAt.sum (u := Finset.univ) (fun j _ => hh j)

lemma waveDerivative_eq_iterated (k : ℕ) : waveDerivative k = iteratedDeriv k P := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using waveDerivative_zero
  | succ k hk =>
    rw [iteratedDeriv_succ, ← hk]
    exact funext fun s => (hasDerivAt_waveDerivative k s).deriv.symm

lemma hasDerivAt_P (s : ℂ) : HasDerivAt P (waveDerivative 1 s) s := by
  simpa only [waveDerivative_zero] using hasDerivAt_waveDerivative 0 s

lemma fourier_node_cancel (n : Node) : waveDerivative 0 n.val = 0 := by
  rw [waveDerivative_zero, P_node]

lemma fourier_node_deriv_cancel (n : Node) : waveDerivative 1 n.val = 0 := by
  rw [← (hasDerivAt_P n.val).deriv, deriv_P_node]

end AtomicTriangular.Construction

namespace AtomicTriangular.Interval

def scale : ℤ := 10^60
lemma scale_pos : (0:ℝ) < (scale:ℤ) := by norm_num [scale]
lemma scale_int_pos : 0 < scale := by norm_num [scale]

structure RI where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def RI.Mem (a : RI) (x : ℝ) : Prop := (a.lo:ℝ) ≤ (scale:ℝ)*x ∧ (scale:ℝ)*x ≤ a.hi

def RI.point (n : ℤ) : RI := ⟨scale*n,scale*n⟩
def RI.add (a b : RI) : RI := ⟨a.lo+b.lo,a.hi+b.hi⟩
def RI.neg (a : RI) : RI := ⟨-a.hi,-a.lo⟩
def RI.sub (a b : RI) : RI := a.add b.neg

def imin4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def imax4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)
def RI.mul (a b : RI) : RI :=
  ⟨imin4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi) / scale,
   imax4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi) / scale + 1⟩

def RI.divNat (a : RI) (n : ℕ) : RI := ⟨a.lo/n,a.hi/n+1⟩
def RI.widen (a : RI) (r : ℤ) : RI := ⟨a.lo-r,a.hi+r⟩

def RI.pow (a : RI) : ℕ → RI
  | 0 => .point 1
  | n+1 => (a.pow n).mul a

lemma RI.mem_point (n : ℤ) : (RI.point n).Mem (n:ℝ) := by
  simp [RI.Mem,RI.point]

lemma RI.mem_add {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.add b).Mem (x+y) := by
  rcases hx with ⟨hx₀,hx₁⟩; rcases hy with ⟨hy₀,hy₁⟩
  constructor <;> simp only [RI.add,Int.cast_add] <;> nlinarith

lemma RI.mem_neg {a : RI} {x : ℝ} (hx : a.Mem x) : a.neg.Mem (-x) := by
  rcases hx with ⟨hx₀,hx₁⟩
  constructor <;> simp only [RI.neg,Int.cast_neg] <;> nlinarith

lemma RI.mem_sub {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.sub b).Mem (x-y) := by simpa [RI.sub,sub_eq_add_neg] using RI.mem_add hx (RI.mem_neg hy)

lemma mul_bounds {a b x t : ℝ} (h : a ≤ x ∧ x ≤ b) :
    min (a*t) (b*t) ≤ x*t ∧ x*t ≤ max (a*t) (b*t) := by
  rcases le_total 0 t with ht | ht
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right h.1 ht),
      (mul_le_mul_of_nonneg_right h.2 ht).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right h.2 ht),
      (mul_le_mul_of_nonpos_right h.1 ht).trans (le_max_left _ _)⟩

lemma four_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hxy := mul_bounds (t := y) hx
  have ha := mul_bounds (t := a) hy
  have hb := mul_bounds (t := b) hy
  simp only [mul_comm c,mul_comm d,mul_comm y] at ha hb
  constructor
  · apply le_trans _ hxy.1
    exact le_min ((min_le_left _ _).trans ha.1) ((min_le_right _ _).trans hb.1)
  · apply le_trans hxy.2
    exact max_le (ha.2.trans (le_max_left _ _)) (hb.2.trans (le_max_right _ _))

lemma div_floor_bounds (a n : ℤ) (hn : 0 < n) :
    ((a/n:ℤ):ℝ)*(n:ℝ) ≤ a ∧ (a:ℝ) ≤ ((a/n+1:ℤ):ℝ)*(n:ℝ) := by
  constructor
  · exact_mod_cast Int.ediv_mul_le a (ne_of_gt hn)
  · exact_mod_cast (Int.lt_ediv_add_one_mul_self a hn).le

lemma RI.mem_mul {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.mul b).Mem (x*y) := by
  have hh := four_bounds hx hy
  have hl := (div_floor_bounds (imin4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)) scale scale_int_pos).1
  have hu := (div_floor_bounds (imax4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)) scale scale_int_pos).2
  simp only [imin4,imax4,Int.cast_min,Int.cast_max,Int.cast_mul] at hl hu
  constructor
  · apply (mul_le_mul_iff_right₀ scale_pos).mp
    dsimp only [RI.mul,imin4,imax4]
    nlinarith [hh.1]
  · apply (mul_le_mul_iff_right₀ scale_pos).mp
    dsimp only [RI.mul,imin4,imax4]
    nlinarith [hh.2]

lemma RI.mem_divNat {a : RI} {x : ℝ} (hx : a.Mem x) {n : ℕ} (hn : 0 < n) :
    (a.divNat n).Mem (x/n) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hnl : (0:ℤ) < n := by exact_mod_cast hn
  have hl := (div_floor_bounds a.lo n hnl).1
  have hu := (div_floor_bounds a.hi n hnl).2
  constructor
  · simpa only [RI.divNat,mul_div_assoc,Int.cast_natCast] using
      (le_div_iff₀ hn').mpr (hl.trans hx.1)
  · change (scale:ℝ)*(x/(n:ℝ)) ≤ ((a.hi/(n:ℤ)+1:ℤ):ℝ)
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hn').mpr (hx.2.trans hu)

lemma RI.mem_pow {a : RI} {x : ℝ} (hx : a.Mem x) (n : ℕ) : (a.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa [RI.pow] using RI.mem_point 1
  | succ n ih => simpa [RI.pow,pow_succ] using RI.mem_mul ih hx

lemma RI.mem_widen {a : RI} {x y : ℝ} {r : ℤ} (hx : a.Mem x)
    (hxy : |y-x| ≤ (r:ℝ)/(scale:ℝ)) : (a.widen r).Mem y := by
  have hh := abs_le.mp hxy
  have hl := (div_le_iff₀ scale_pos).mp (show -(r:ℝ)/(scale:ℝ) ≤ y-x by simpa only [neg_div] using hh.1)
  have hu := (le_div_iff₀ scale_pos).mp hh.2
  rcases hx with ⟨hx₀,hx₁⟩
  constructor <;> simp only [RI.widen,Int.cast_sub,Int.cast_add] <;> nlinarith

def RI.invPos (a : RI) : RI := ⟨scale^2/a.hi,scale^2/a.lo+1⟩

lemma RI.mem_invPos {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo) :
    a.invPos.Mem x⁻¹ := by
  have halo : (0:ℝ) < a.lo := by exact_mod_cast ha
  have hsx : 0 < (scale:ℝ)*x := halo.trans_le hx.1
  have hahi : (0:ℝ) < a.hi := hsx.trans_le hx.2
  have hahi' : (0:ℤ) < a.hi := by exact_mod_cast hahi
  have hl := (div_floor_bounds (scale^2) a.hi hahi').1
  have hu := (div_floor_bounds (scale^2) a.lo ha).2
  push_cast at hl hu
  have hlow : (((scale^2/a.hi:ℤ):ℝ)) ≤ (scale:ℝ)^2/((scale:ℝ)*x) := by
    exact ((le_div_iff₀ hahi).mpr hl).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hsx hx.2)
  have hupp : (scale:ℝ)^2/((scale:ℝ)*x) ≤ (((scale^2/a.lo+1:ℤ):ℝ)) := by
    exact (div_le_div_of_nonneg_left (sq_nonneg _) halo hx.1).trans
      ((div_le_iff₀ halo).mpr (by simpa only [Int.cast_add,Int.cast_one] using hu))
  have heq : (scale:ℝ)^2/((scale:ℝ)*x) = (scale:ℝ)*x⁻¹ := by
    field_simp [ne_of_gt scale_pos]
  simpa only [heq,RI.Mem,RI.invPos] using And.intro hlow hupp

structure CI where
  re : RI
  im : RI
  deriving DecidableEq, Repr

def CI.Mem (a : CI) (z : ℂ) : Prop := a.re.Mem z.re ∧ a.im.Mem z.im

def CI.ofReal (a : RI) : CI := ⟨a,RI.point 0⟩
def CI.point (n : ℤ) : CI := .ofReal (.point n)
def CI.imag : CI := ⟨RI.point 0,RI.point 1⟩
def CI.add (a b : CI) : CI := ⟨a.re.add b.re,a.im.add b.im⟩
def CI.neg (a : CI) : CI := ⟨a.re.neg,a.im.neg⟩
def CI.sub (a b : CI) : CI := a.add b.neg

def CI.mul (a b : CI) : CI :=
  ⟨(a.re.mul b.re).sub (a.im.mul b.im), (a.re.mul b.im).add (a.im.mul b.re)⟩
def CI.conj (a : CI) : CI := ⟨a.re,a.im.neg⟩
def CI.divNat (a : CI) (n : ℕ) : CI := ⟨a.re.divNat n,a.im.divNat n⟩
def CI.widen (a : CI) (r : ℤ) : CI := ⟨a.re.widen r,a.im.widen r⟩
def CI.normSq (a : CI) : RI := (a.re.mul a.re).add (a.im.mul a.im)
def CI.inv (a : CI) : CI := a.conj.mul (.ofReal a.normSq.invPos)

def CI.pow (a : CI) : ℕ → CI
  | 0 => .point 1
  | n+1 => (a.pow n).mul a

lemma CI.mem_ofReal {a : RI} {x : ℝ} (h : a.Mem x) : (CI.ofReal a).Mem (x:ℂ) := by
  exact ⟨h,by simpa [CI.ofReal] using RI.mem_point 0⟩
lemma CI.mem_point (n : ℤ) : (CI.point n).Mem (n:ℂ) := by
  exact CI.mem_ofReal (RI.mem_point n)
lemma CI.mem_imag : CI.imag.Mem Complex.I := by
  exact ⟨by simpa [CI.imag] using RI.mem_point 0,by simpa [CI.imag] using RI.mem_point 1⟩
lemma CI.mem_add {a b : CI} {x y : ℂ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.add b).Mem (x+y) := by exact ⟨RI.mem_add hx.1 hy.1,RI.mem_add hx.2 hy.2⟩
lemma CI.mem_neg {a : CI} {x : ℂ} (hx : a.Mem x) : a.neg.Mem (-x) := by
  exact ⟨RI.mem_neg hx.1,RI.mem_neg hx.2⟩
lemma CI.mem_sub {a b : CI} {x y : ℂ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.sub b).Mem (x-y) := by simpa [sub_eq_add_neg,CI.sub] using CI.mem_add hx (CI.mem_neg hy)
lemma CI.mem_mul {a b : CI} {x y : ℂ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.mul b).Mem (x*y) := by
  exact ⟨RI.mem_sub (RI.mem_mul hx.1 hy.1) (RI.mem_mul hx.2 hy.2),
    RI.mem_add (RI.mem_mul hx.1 hy.2) (RI.mem_mul hx.2 hy.1)⟩
lemma CI.mem_divNat {a : CI} {x : ℂ} (hx : a.Mem x) {n : ℕ} (hn : 0 < n) :
    (a.divNat n).Mem (x/n) := by
  simpa only [CI.Mem,CI.divNat,Complex.div_natCast_re,Complex.div_natCast_im] using
    And.intro (RI.mem_divNat hx.1 hn) (RI.mem_divNat hx.2 hn)
lemma CI.mem_conj {a : CI} {x : ℂ} (hx : a.Mem x) : a.conj.Mem (starRingEnd ℂ x) := by
  exact ⟨hx.1,RI.mem_neg hx.2⟩
lemma CI.mem_normSq {a : CI} {x : ℂ} (hx : a.Mem x) : a.normSq.Mem (Complex.normSq x) := by
  exact RI.mem_add (RI.mem_mul hx.1 hx.1) (RI.mem_mul hx.2 hx.2)
lemma CI.mem_inv {a : CI} {x : ℂ} (hx : a.Mem x) (ha : 0 < a.normSq.lo) :
    a.inv.Mem x⁻¹ := by
  have hh := CI.mem_mul (CI.mem_conj hx) (CI.mem_ofReal (RI.mem_invPos (CI.mem_normSq hx) ha))
  simpa only [CI.inv,Complex.inv_def] using hh
lemma CI.mem_pow {a : CI} {x : ℂ} (hx : a.Mem x) (n : ℕ) : (a.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa [CI.pow] using CI.mem_point 1
  | succ n ih => simpa [CI.pow,pow_succ] using CI.mem_mul ih hx

noncomputable section
open scoped BigOperators

lemma CI.mem_widen {a : CI} {x y : ℂ} {r : ℤ} (hx : a.Mem x)
    (hxy : ‖y-x‖ ≤ (r:ℝ)/(scale:ℝ)) : (a.widen r).Mem y := by
  constructor
  · apply RI.mem_widen hx.1
    exact (Complex.abs_re_le_norm (y-x)).trans hxy
  · apply RI.mem_widen hx.2
    exact (Complex.abs_im_le_norm (y-x)).trans hxy

def CI.taylor (a : CI) : ℕ → CI × CI
  | 0 => (CI.point 1, CI.point 1)
  | n+1 =>
    let previous := a.taylor n
    let term := (previous.1.mul a).divNat (n+1)
    (term, previous.2.add term)

lemma CI.mem_taylor {a : CI} {x : ℂ} (hx : a.Mem x) (n : ℕ) :
    (a.taylor n).1.Mem (x^n/(n.factorial : ℂ)) ∧
    (a.taylor n).2.Mem (∑ j ∈ Finset.range (n+1), x^j/(j.factorial : ℂ)) := by
  induction n with
  | zero => simpa [CI.taylor] using And.intro (CI.mem_point 1) (CI.mem_point 1)
  | succ n ih =>
    have hf : x^(n+1)/((n+1).factorial : ℂ) = (x^n/(n.factorial : ℂ))*x/((n+1:ℕ):ℂ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      field_simp
    constructor
    · rw [hf]
      exact CI.mem_divNat (CI.mem_mul ih.1 hx) (Nat.succ_pos n)
    · rw [Finset.sum_range_succ, hf]
      exact CI.mem_add ih.2 (CI.mem_divNat (CI.mem_mul ih.1 hx) (Nat.succ_pos n))

lemma small_taylor_error {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖Complex.exp x - ∑ j ∈ Finset.range 61, x^j/(j.factorial : ℂ)‖ ≤
      (1:ℝ)/(scale:ℝ) := by
  have hh := Complex.exp_bound' (n := 61) (x := x) (by norm_num; linarith : ‖x‖ / 62 ≤ 1/2)
  calc
    _ ≤ ‖x‖^61/(Nat.factorial 61 : ℝ)*2 := hh
    _ ≤ (1:ℝ)^61/(Nat.factorial 61 : ℝ)*2 := by gcongr
    _ ≤ _ := by norm_num [scale]

def CI.square (a : CI) : ℕ → CI
  | 0 => a
  | n+1 => (a.square n).mul (a.square n)

lemma CI.mem_square {a : CI} {x : ℂ} (hx : a.Mem x) (n : ℕ) :
    (a.square n).Mem (x^(2^n)) := by
  induction n with
  | zero => simpa [CI.square] using hx
  | succ n ih =>
    rw [CI.square, show 2^(n+1) = 2^n*2 by rw [pow_succ], pow_mul, pow_two]
    exact CI.mem_mul ih ih

def CI.exp (a : CI) : CI :=
  (((a.divNat 1024).taylor 60).2.widen 1).square 10

lemma CI.mem_exp {a : CI} {x : ℂ} (hx : a.Mem x) (hn : ‖x/1024‖ ≤ 1) :
    a.exp.Mem (Complex.exp x) := by
  have hs := CI.mem_taylor (CI.mem_divNat hx (by norm_num : 0 < (1024:ℕ))) 60
  have he := CI.mem_widen (r := 1) hs.2 (by simpa only [Int.cast_one, Nat.cast_ofNat] using small_taylor_error hn)
  have hh := CI.mem_square he 10
  have hpow : Complex.exp (x/1024) ^ (2^10) = Complex.exp x := by
    rw [← Complex.exp_nat_mul]
    norm_num
    congr 1
    ring
  simpa only [hpow, CI.exp] using hh

lemma RI.mem_of_subset {a b : RI} {x : ℝ} (hx : a.Mem x)
    (hl : b.lo ≤ a.lo) (hu : a.hi ≤ b.hi) : b.Mem x := by
  have hl' : (b.lo:ℝ) ≤ a.lo := by exact_mod_cast hl
  have hu' : (a.hi:ℝ) ≤ b.hi := by exact_mod_cast hu
  exact ⟨hl'.trans hx.1, hx.2.trans hu'⟩

lemma CI.mem_of_subset {a b : CI} {x : ℂ} (hx : a.Mem x)
    (hrl : b.re.lo ≤ a.re.lo) (hru : a.re.hi ≤ b.re.hi)
    (hil : b.im.lo ≤ a.im.lo) (hiu : a.im.hi ≤ b.im.hi) : b.Mem x := by
  exact ⟨RI.mem_of_subset hx.1 hrl hru, RI.mem_of_subset hx.2 hil hiu⟩

lemma CI.norm_le_of_mem {a : CI} {x : ℂ} (hx : a.Mem x)
    (ha : a.normSq.hi ≤ scale * 1024^2) : ‖x / 1024‖ ≤ 1 := by
  have hh := (CI.mem_normSq hx).2
  have hu : (a.normSq.hi : ℝ) ≤ (scale : ℝ) * 1024^2 := by exact_mod_cast ha
  rw [Complex.normSq_eq_norm_sq] at hh
  have hn : ‖x‖ ≤ 1024 := by
    have hns : ‖x‖^2 ≤ 1024^2 := by nlinarith [scale_pos]
    nlinarith [norm_nonneg x]
  simpa using (div_le_one (by norm_num : (0:ℝ) < 1024)).mpr hn

lemma CI.mem_exp_checked {a : CI} {x : ℂ} (hx : a.Mem x)
    (ha : a.normSq.hi ≤ scale * 1024^2) : a.exp.Mem (Complex.exp x) :=
  CI.mem_exp hx (CI.norm_le_of_mem hx ha)

def RI.abs (a : RI) : RI := ⟨max 0 (max a.lo (-a.hi)), max a.hi (-a.lo)⟩
def RI.imax (a b : RI) : RI := ⟨max a.lo b.lo, max a.hi b.hi⟩
def RI.imin (a b : RI) : RI := ⟨min a.lo b.lo, min a.hi b.hi⟩
def RI.inv (a : RI) : RI := if a.hi < 0 then a.neg.invPos.neg else a.invPos

lemma RI.mem_abs {a : RI} {x : ℝ} (hx : a.Mem x) : a.abs.Mem |x| := by
  rcases hx with ⟨hl,hu⟩
  change (↑(max 0 (max a.lo (-a.hi))) : ℝ) ≤ (scale:ℝ)*|x| ∧
    (scale:ℝ)*|x| ≤ ↑(max a.hi (-a.lo))
  push_cast
  rw [← abs_of_pos scale_pos, ← abs_mul]
  constructor
  · exact max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _)) (by simpa using (neg_le_neg hu).trans (neg_le_abs _)))
  · exact (abs_le.mpr ⟨by linarith [le_max_right (a.hi:ℝ) (-(a.lo:ℝ))], hu.trans (le_max_left _ _)⟩)

lemma RI.mem_max {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.imax b).Mem (max x y) := by
  constructor
  · simp only [RI.imax, Int.cast_max, mul_max_of_nonneg _ _ scale_pos.le]
    exact max_le_max hx.1 hy.1
  · simp only [RI.imax, Int.cast_max, mul_max_of_nonneg _ _ scale_pos.le]
    exact max_le_max hx.2 hy.2

lemma RI.mem_min {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.imin b).Mem (min x y) := by
  constructor
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.1 hy.1
  · simp only [RI.imin, Int.cast_min, mul_min_of_nonneg _ _ scale_pos.le]
    exact min_le_min hx.2 hy.2

lemma RI.mem_inv {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo ∨ a.hi < 0) :
    a.inv.Mem x⁻¹ := by
  unfold RI.inv
  split_ifs with hh
  · have hp : 0 < a.neg.lo := by simpa [RI.neg] using neg_pos.mpr hh
    simpa using RI.mem_neg (RI.mem_invPos (RI.mem_neg hx) hp)
  · exact RI.mem_invPos hx (ha.resolve_right hh)

lemma RI.mem_sqrt {a r : RI} {x : ℝ} (hx : a.Mem x) (h₀ : 0 ≤ x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.lo)
    (hr₂ : scale * a.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem (Real.sqrt x) := by
  have hs := Real.sq_sqrt h₀
  have hp := Real.sqrt_nonneg x
  have hrl : (0:ℝ) ≤ r.lo := by exact_mod_cast hr₀
  have hrh : (0:ℝ) ≤ r.hi := by exact_mod_cast hr₃
  have hrls : (r.lo:ℝ) * r.lo ≤ (scale:ℝ) * max (0:ℝ) (a.lo:ℝ) := by exact_mod_cast hr₁
  have hrhs : (scale:ℝ) * a.hi ≤ (r.hi:ℝ) * r.hi := by exact_mod_cast hr₂
  have hsl := mul_le_mul_of_nonneg_left (max_le (mul_nonneg scale_pos.le h₀) hx.1) scale_pos.le
  have hsh := mul_le_mul_of_nonneg_left hx.2 scale_pos.le
  have he : ((scale:ℝ) * Real.sqrt x)^2 = (scale:ℝ) * ((scale:ℝ)*x) := by
    rw [mul_pow, hs]
    ring
  constructor <;> nlinarith [mul_nonneg scale_pos.le hp]

lemma CI.mem_norm {a : CI} {r : RI} {x : ℂ} (hx : a.Mem x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.normSq.lo)
    (hr₂ : scale * a.normSq.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem ‖x‖ := by
  have hh := RI.mem_sqrt (CI.mem_normSq hx) (Complex.normSq_nonneg x) hr₀ hr₁ hr₂ hr₃
  simpa [Complex.normSq_eq_norm_sq] using hh

end
end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval

def RI.sum {ι : Type*} [Fintype ι] (v : ι → RI) : RI :=
  ⟨∑ i, (v i).lo, ∑ i, (v i).hi⟩

lemma RI.mem_sum {ι : Type*} [Fintype ι] {v : ι → RI} {x : ι → ℝ}
    (hv : ∀ i, (v i).Mem (x i)) : (RI.sum v).Mem (∑ i, x i) := by
  constructor
  · simp only [RI.sum, Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).1
  · simp only [RI.sum, Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).2

def CI.sum {ι : Type*} [Fintype ι] (v : ι → CI) : CI :=
  ⟨RI.sum (fun i => (v i).re), RI.sum (fun i => (v i).im)⟩

lemma CI.mem_sum {ι : Type*} [Fintype ι] {v : ι → CI} {x : ι → ℂ}
    (hv : ∀ i, (v i).Mem (x i)) : (CI.sum v).Mem (∑ i, x i) := by
  constructor
  · simp only [Complex.re_sum]
    exact RI.mem_sum fun i => (hv i).1
  · simp only [Complex.im_sum]
    exact RI.mem_sum fun i => (hv i).2

end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators Topology
open Finset Filter
namespace AtomicTriangular.Constants

def eps : ℝ := (10^80)⁻¹
def pStar : ℝ := 3.14159265358979323846264338327950288419716939937510582097494459230781640628620899
def bStar : ℝ := 0.86602540378443864676372317075293618347140262690519031402790348972596650845440001

def arctanPoly (x : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, (-1)^j*x^(2*j+1)/(2*j+1)

lemma arctan_bracket {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x < 1) (n : ℕ) :
    arctanPoly x (2*n) ≤ Real.arctan x ∧
      Real.arctan x ≤ arctanPoly x (2*n) + x^(4*n+1)/(4*n+1) := by
  have ha : Antitone (fun j : ℕ => x^(2*j+1)/(2*j+1)) := by
    intro j k hjk
    apply div_le_div₀ (pow_nonneg h₀ _)
      (pow_le_pow_of_le_one h₀ h₁.le (by omega)) (by positivity)
    exact_mod_cast (by omega : 2*j+1 ≤ 2*k+1)
  have ht : Tendsto (fun n : ℕ => ∑ j ∈ range n,
      (-1:ℝ)^j * (x^(2*j+1)/(2*j+1))) atTop (𝓝 (Real.arctan x)) := by
    simpa only [mul_div_assoc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      (Real.hasSum_arctan (x := x) (by simpa [Real.norm_eq_abs, abs_of_nonneg h₀])).tendsto_sum_nat
  constructor
  · simpa only [arctanPoly, mul_div_assoc] using ha.alternating_series_le_tendsto ht n
  · have hh := ha.tendsto_le_alternating_series ht n
    simpa [arctanPoly, sum_range_succ, mul_div_assoc, ← mul_assoc, show (2:ℝ)*2=4 by norm_num] using hh

lemma bStar_bracket : bStar < Real.sqrt 3 / 2 ∧ Real.sqrt 3 / 2 < bStar + eps := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hp : 0 < bStar := by norm_num [bStar]
  have he : 0 < eps := by norm_num [eps]
  have h₁ : bStar^2 < (3:ℝ)/4 := by norm_num [bStar]
  have h₂ : (3:ℝ)/4 < (bStar+eps)^2 := by norm_num [bStar, eps]
  constructor <;> nlinarith

lemma arctanPoly_inv5 : arctanPoly (1/5) 66 =
    (1127735820047281249826929962540366709009681070146611148630124134909087293535356022585063476519722124011352752446574182801704731339148829291186 : ℝ) / 5713075921793397351900334790776425890382017146109705783051183673650632561398172069707387162692372481291591679308794482494704425334930419921875 := by
  norm_num [arctanPoly, Finset.sum_range_succ]

lemma arctanPoly_inv239 : arctanPoly (1/239) 66 =
    (1118499394876416155561248293203315319858384148339754901282838013788591793901685995599875876925744187341881465177415079642435790204501443414217256735370408712354720598117442228707319810097027336706847276448482833107456896007088774973302196447103862002632135039862371139157305730782208439937297739381319965159523409065323737874075361079721743262198339765260034519498 : ℝ) / 267322915339442907721699424219844204360421434646325545345832816547242287762014829735766747100513282387541656695398803852049344802256469797061373857157082424828915581864219799259751119529925859323776796465869821218865822100577138580956944108601031719877043720686956487215878943801043900609923763261313848030486279699763172497745026116723198663028174351830029321704625 := by
  norm_num [arctanPoly, Finset.sum_range_succ]

theorem pStar_bracket : pStar < Real.pi ∧ Real.pi < pStar + eps := by
  have h₅ := arctan_bracket (x := 1/5) (by norm_num) (by norm_num) 33
  have h₂₃₉ := arctan_bracket (x := 1/239) (by norm_num) (by norm_num) 33
  norm_num only [show 2*33 = (66:ℕ) by rfl, show 4*33+1 = (133:ℕ) by rfl] at h₅ h₂₃₉
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  rw [inv_eq_one_div, inv_eq_one_div] at hm
  have hl : pStar < 16*arctanPoly (1/5) 66 -
      4*(arctanPoly (1/239) 66 + (1/239:ℝ)^133/133) := by
    rw [arctanPoly_inv5, arctanPoly_inv239]
    norm_num [pStar]
  have hu : 16*(arctanPoly (1/5) 66 +(1/5:ℝ)^133/133) -
      4*arctanPoly (1/239) 66 < pStar + eps := by
    rw [arctanPoly_inv5, arctanPoly_inv239]
    norm_num [pStar, eps]
  constructor <;> linarith

end AtomicTriangular.Constants

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial

def piBox : RI :=
  ⟨3141592653589793238462643383279502884197169399375100000000000,
   3141592653589793238462643383279502884197169399375110000000000⟩

lemma piBox_mem : piBox.Mem Real.pi := by
  obtain ⟨hl,hu⟩ := Constants.pStar_bracket
  constructor <;> dsimp [RI.Mem, piBox]
  · have hstar : (piBox.lo:ℝ) / (scale:ℝ) ≤ Constants.pStar := by
      norm_num [piBox,scale,Constants.pStar]
    have hpi := hstar.trans hl.le
    simpa only [mul_comm, piBox] using (div_le_iff₀ scale_pos).mp hpi
  · have hstar : Constants.pStar + Constants.eps ≤ (piBox.hi:ℝ) / (scale:ℝ) := by
      norm_num [piBox,scale,Constants.pStar,Constants.eps]
    have hpi := hu.le.trans hstar
    simpa only [mul_comm, piBox] using (le_div_iff₀ scale_pos).mp hpi

lemma phase_conj (s : ℝ) : starRingEnd ℂ (phase (s:ℂ)) = phase (-(s:ℂ)) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

def partialPolynomial (n : ℕ) : Polynomial ℂ :=
  ∏ a ∈ Finset.univ.filter (fun a : Fin 15 => a.val < n), atomFactor a

lemma partialPolynomial_zero : partialPolynomial 0 = 1 := by simp [partialPolynomial]
lemma partialPolynomial_fifteen : partialPolynomial 15 = atomPolynomial := by simp [partialPolynomial, atomPolynomial]
lemma partialPolynomial_succ {n : ℕ} (hn : n < 15) :
    partialPolynomial (n+1) = atomFactor ⟨n,hn⟩ * partialPolynomial n := by
  have he : Finset.univ.filter (fun a : Fin 15 => a.val < n+1) =
      insert ⟨n,hn⟩ (Finset.univ.filter (fun a : Fin 15 => a.val < n)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    simp only [Fin.ext_iff]
    omega
  rw [partialPolynomial, he, Finset.prod_insert]
  · rfl
  · simp

lemma coeff_X_mul' (p : Polynomial ℂ) (n : ℕ) :
    (X*p).coeff n = if n=0 then 0 else p.coeff (n-1) := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_X_mul]

lemma coeff_X_sq_mul (p : Polynomial ℂ) (n : ℕ) :
    (X^2*p).coeff n = if n<2 then 0 else p.coeff (n-2) := by
  rw [pow_two, mul_assoc, coeff_X_mul']
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n => simp [coeff_X_mul]

lemma coeff_atom_mul (a : Fin 15) (p : Polynomial ℂ) (n : ℕ) :
    (atomFactor a*p).coeff n =
      -(phase (residue a))*p.coeff n +
        (if n=0 then 0 else 2*p.coeff (n-1)) -
        (if n<2 then 0 else phase (-(residue a : ℂ))*p.coeff (n-2)) := by
  unfold atomFactor
  rw [sub_mul, add_mul, neg_mul, mul_assoc, mul_assoc, coeff_sub, coeff_add,
    coeff_neg, coeff_C_mul, coeff_C_mul,
    coeff_C_mul, coeff_X_mul', coeff_X_sq_mul]
  split_ifs <;> ring

def coeffStep (e : CI) (v : Fin 31 → CI) (j : Fin 31) : CI :=
  ((e.neg.mul (v j)).add (if h : j.val=0 then CI.point 0
    else (CI.point 2).mul (v ⟨j.val-1,by omega⟩))).sub
      (if h : j.val<2 then CI.point 0 else e.conj.mul (v ⟨j.val-2,by omega⟩))

lemma coeffStep_mem (a : Fin 15) (p : Polynomial ℂ) (e : CI)
    (v : Fin 31 → CI) (he : e.Mem (phase (residue a)))
    (hv : ∀ j : Fin 31, (v j).Mem (p.coeff j.val)) (j : Fin 31) :
    (coeffStep e v j).Mem ((atomFactor a*p).coeff j.val) := by
  rw [coeff_atom_mul]
  apply CI.mem_sub
  · apply CI.mem_add
    · exact CI.mem_mul (CI.mem_neg he) (hv j)
    · split_ifs with hn
      · simpa using CI.mem_point 0
      · exact CI.mem_mul (CI.mem_point 2) (hv ⟨j.val-1,by omega⟩)
  · split_ifs with hn
    · simpa using CI.mem_point 0
    · have he' : e.conj.Mem (phase (-(residue a : ℂ))) := by
        have hh := CI.mem_conj he
        simpa only [← Complex.ofReal_intCast, phase_conj] using hh
      exact CI.mem_mul he' (hv ⟨j.val-2,by omega⟩)

def phaseInputBox (n : ℤ) : CI :=
  (CI.imag.mul (CI.ofReal (piBox.mul (RI.point n)))).divNat 18

lemma phaseInputBox_mem (n : ℤ) :
    (phaseInputBox n).Mem ((Real.pi : ℂ) * Complex.I * (n:ℂ) / 18) := by
  have hp := CI.mem_mul CI.mem_imag (CI.mem_ofReal (RI.mem_mul piBox_mem (RI.mem_point n)))
  have hh := CI.mem_divNat hp (by norm_num : 0 < (18:ℕ))
  change ((CI.imag.mul (CI.ofReal (piBox.mul (RI.point n)))).divNat 18).Mem _
  convert hh using 1
  push_cast
  ring

end AtomicTriangular.FiniteCertificate

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial
def phaseBox0 : CI := ⟨⟨999999999999999999999999999999999999999999999999999999935489,1000000000000000000000000000000000000000000000000000000066558⟩,⟨-63486,68606⟩⟩
lemma phaseBox0_calc : (phaseInputBox 0).exp = phaseBox0 := by decide +kernel
lemma phaseBox0_mem : phaseBox0.Mem (phase ((0:ℤ):ℂ)) := by
  rw [← phaseBox0_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 0) (by decide +kernel)
def phaseBox1 : CI := ⟨⟨984807753012208059366743024589523013670643251719842378260439,984807753012208059366743024589523013670643251719842475161964⟩,⟨173648177666930348851716626769314796000375677184069063062132,173648177666930348851716626769314796000375677184069621580864⟩⟩
lemma phaseBox1_calc : (phaseInputBox 1).exp = phaseBox1 := by decide +kernel
lemma phaseBox1_mem : phaseBox1.Mem (phase ((1:ℤ):ℂ)) := by
  rw [← phaseBox1_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 1) (by decide +kernel)
def phaseBox2 : CI := ⟨⟨939692620785908384054109277324731469936208134264464471960044,939692620785908384054109277324731469936208134264464856618258⟩,⟨342020143325668733044099614682259580763083367514159975976700,342020143325668733044099614682259580763083367514161109522372⟩⟩
lemma phaseBox2_calc : (phaseInputBox 2).exp = phaseBox2 := by decide +kernel
lemma phaseBox2_mem : phaseBox2.Mem (phase ((2:ℤ):ℂ)) := by
  rw [← phaseBox2_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 2) (by decide +kernel)
def phaseBox3 : CI := ⟨⟨866025403784438646763723170752936183471402626905189954512964,866025403784438646763723170752936183471402626905190810370953⟩,⟨499999999999999999999999999999999999999999999999999011153642,500000000000000000000000000000000000000000000000000751856976⟩⟩
lemma phaseBox3_calc : (phaseInputBox 3).exp = phaseBox3 := by decide +kernel
lemma phaseBox3_mem : phaseBox3.Mem (phase ((3:ℤ):ℂ)) := by
  rw [← phaseBox3_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 3) (by decide +kernel)
def phaseBox4 : CI := ⟨⟨766044443118978035202392650555416673935832457080394614080696,766044443118978035202392650555416673935832457080396112163801⟩,⟨642787609686539326322643409907263432907559884205680453940922,642787609686539326322643409907263432907559884205682847200174⟩⟩
lemma phaseBox4_calc : (phaseInputBox 4).exp = phaseBox4 := by decide +kernel
lemma phaseBox4_mem : phaseBox4.Mem (phase ((4:ℤ):ℂ)) := by
  rw [← phaseBox4_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 4) (by decide +kernel)
def phaseBox5 : CI := ⟨⟨642787609686539326322643409907263432907559884205680817903044,642787609686539326322643409907263432907559884205683112135181⟩,⟨766044443118978035202392650555416673935832457080393548649076,766044443118978035202392650555416673935832457080396649890976⟩⟩
lemma phaseBox5_calc : (phaseInputBox 5).exp = phaseBox5 := by decide +kernel
lemma phaseBox5_mem : phaseBox5.Mem (phase ((5:ℤ):ℂ)) := by
  rw [← phaseBox5_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 5) (by decide +kernel)
def phaseBox6 : CI := ⟨⟨499999999999999999999999999999999999999999999999998625582869,500000000000000000000000000000000000000000000000001848404295⟩,⟨866025403784438646763723170752936183471402626905188241914124,866025403784438646763723170752936183471402626905192112487718⟩⟩
lemma phaseBox6_calc : (phaseInputBox 6).exp = phaseBox6 := by decide +kernel
lemma phaseBox6_mem : phaseBox6.Mem (phase ((6:ℤ):ℂ)) := by
  rw [← phaseBox6_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 6) (by decide +kernel)
def phaseBox7 : CI := ⟨⟨342020143325668733044099614682259580763083367514158799320630,342020143325668733044099614682259580763083367514163057632021⟩,⟨939692620785908384054109277324731469936208134264462172730300,939692620785908384054109277324731469936208134264466875061792⟩⟩
lemma phaseBox7_calc : (phaseInputBox 7).exp = phaseBox7 := by decide +kernel
lemma phaseBox7_mem : phaseBox7.Mem (phase ((7:ℤ):ℂ)) := by
  rw [← phaseBox7_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 7) (by decide +kernel)
def phaseBox8 : CI := ⟨⟨173648177666930348851716626769314796000375677184067060768548,173648177666930348851716626769314796000375677184072432368187⟩,⟨984807753012208059366743024589523013670643251719839559295028,984807753012208059366743024589523013670643251719845151568286⟩⟩
lemma phaseBox8_calc : (phaseInputBox 8).exp = phaseBox8 := by decide +kernel
lemma phaseBox8_mem : phaseBox8.Mem (phase ((8:ℤ):ℂ)) := by
  rw [← phaseBox8_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 8) (by decide +kernel)
def phaseBox9 : CI := ⟨⟨-2854777273,3675745116⟩,⟨999999999999999999999999999999999999999999999999996734740088,1000000000000000000000000000000000000000000000000003265262478⟩⟩
lemma phaseBox9_calc : (phaseInputBox 9).exp = phaseBox9 := by decide +kernel
lemma phaseBox9_mem : phaseBox9.Mem (phase ((9:ℤ):ℂ)) := by
  rw [← phaseBox9_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 9) (by decide +kernel)
def phaseBox10 : CI := ⟨⟨-173648177666930348851716626769314796000375677184072788297342,-173648177666930348851716626769314796000375677184065087845911⟩,⟨984807753012208059366743024589523013670643251719838747234178,984807753012208059366743024589523013670643251719846248746530⟩⟩
lemma phaseBox10_calc : (phaseInputBox 10).exp = phaseBox10 := by decide +kernel
lemma phaseBox10_mem : phaseBox10.Mem (phase ((10:ℤ):ℂ)) := by
  rw [← phaseBox10_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 10) (by decide +kernel)
def phaseBox11 : CI := ⟨⟨-342020143325668733044099614682259580763083367514164579490877,-342020143325668733044099614682259580763083367514155734542861⟩,⟨939692620785908384054109277324731469936208134264460562604050,939692620785908384054109277324731469936208134264469046765440⟩⟩
lemma phaseBox11_calc : (phaseInputBox 11).exp = phaseBox11 := by decide +kernel
lemma phaseBox11_mem : phaseBox11.Mem (phase ((11:ℤ):ℂ)) := by
  rw [← phaseBox11_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 11) (by decide +kernel)
def phaseBox12 : CI := ⟨⟨-500000000000000000000000000000000000000000000000004489253604,-499999999999999999999999999999999999999999999999994562770708⟩,⟨866025403784438646763723170752936183471402626905185861538948,866025403784438646763723170752936183471402626905195313833830⟩⟩
lemma phaseBox12_calc : (phaseInputBox 12).exp = phaseBox12 := by decide +kernel
lemma phaseBox12_mem : phaseBox12.Mem (phase ((12:ℤ):ℂ)) := by
  rw [← phaseBox12_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 12) (by decide +kernel)
def phaseBox13 : CI := ⟨⟨-642787609686539326322643409907263432907559884205686789753345,-642787609686539326322643409907263432907559884205675882485247⟩,⟨766044443118978035202392650555416673935832457080390439298182,766044443118978035202392650555416673935832457080400814661650⟩⟩
lemma phaseBox13_calc : (phaseInputBox 13).exp = phaseBox13 := by decide +kernel
lemma phaseBox13_mem : phaseBox13.Mem (phase ((13:ℤ):ℂ)) := by
  rw [← phaseBox13_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 13) (by decide +kernel)
def phaseBox14 : CI := ⟨⟨-766044443118978035202392650555416673935832457080400710407312,-766044443118978035202392650555416673935832457080388960420236⟩,⟨642787609686539326322643409907263432907559884205676669856626,642787609686539326322643409907263432907559884205687889085620⟩⟩
lemma phaseBox14_calc : (phaseInputBox 14).exp = phaseBox14 := by decide +kernel
lemma phaseBox14_mem : phaseBox14.Mem (phase ((14:ℤ):ℂ)) := by
  rw [← phaseBox14_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 14) (by decide +kernel)
def phaseBox15 : CI := ⟨⟨-866025403784438646763723170752936183471402626905196181323615,-866025403784438646763723170752936183471402626905183762590658⟩,⟨499999999999999999999999999999999999999999999999994618824454,500000000000000000000000000000000000000000000000006566147044⟩⟩
lemma phaseBox15_calc : (phaseInputBox 15).exp = phaseBox15 := by decide +kernel
lemma phaseBox15_mem : phaseBox15.Mem (phase ((15:ℤ):ℂ)) := by
  rw [← phaseBox15_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 15) (by decide +kernel)
def phaseBox16 : CI := ⟨⟨-939692620785908384054109277324731469936208134264470823413628,-939692620785908384054109277324731469936208134264457943587609⟩,⟨342020143325668733044099614682259580763083367514155053298568,342020143325668733044099614682259580763083367514167575120924⟩⟩
lemma phaseBox16_calc : (phaseInputBox 16).exp = phaseBox16 := by decide +kernel
lemma phaseBox16_mem : phaseBox16.Mem (phase ((16:ℤ):ℂ)) := by
  rw [← phaseBox16_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 16) (by decide +kernel)
def phaseBox17 : CI := ⟨⟨-984807753012208059366743024589523013670643251719848835505828,-984807753012208059366743024589523013670643251719835732797643⟩,⟨173648177666930348851716626769314796000375677184063698304240,173648177666930348851716626769314796000375677184076603333880⟩⟩
lemma phaseBox17_calc : (phaseInputBox 17).exp = phaseBox17 := by decide +kernel
lemma phaseBox17_mem : phaseBox17.Mem (phase ((17:ℤ):ℂ)) := by
  rw [← phaseBox17_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 17) (by decide +kernel)
def phaseBox18 : CI := ⟨⟨-1000000000000000000000000000000000000000000000000006530375474,-999999999999999999999999999999999999999999999999993469625023⟩,⟨-5709403374,7351347078⟩⟩
lemma phaseBox18_calc : (phaseInputBox 18).exp = phaseBox18 := by decide +kernel
lemma phaseBox18_mem : phaseBox18.Mem (phase ((18:ℤ):ℂ)) := by
  rw [← phaseBox18_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 18) (by decide +kernel)
def phaseBox19 : CI := ⟨⟨-984807753012208059366743024589523013670643251719850175773758,-984807753012208059366743024589523013670643251719834962769522⟩,⟨-173648177666930348851716626769314796000375677184076234168892,-173648177666930348851716626769314796000375677184060833470644⟩⟩
lemma phaseBox19_calc : (phaseInputBox 19).exp = phaseBox19 := by decide +kernel
lemma phaseBox19_mem : phaseBox19.Mem (phase ((19:ℤ):ℂ)) := by
  rw [← phaseBox19_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 19) (by decide +kernel)
def phaseBox20 : CI := ⟨⟨-939692620785908384054109277324731469936208134264473669623711,-939692620785908384054109277324731469936208134264456220534602⟩,⟨-342020143325668733044099614682259580763083367514168657202328,-342020143325668733044099614682259580763083367514150885369606⟩⟩
lemma phaseBox20_calc : (phaseInputBox 20).exp = phaseBox20 := by decide +kernel
lemma phaseBox20_mem : phaseBox20.Mem (phase ((20:ℤ):ℂ)) := by
  rw [← phaseBox20_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 20) (by decide +kernel)
def phaseBox21 : CI := ⟨⟨-866025403784438646763723170752936183471402626905200655848102,-866025403784438646763723170752936183471402626905180930009073⟩,⟨-500000000000000000000000000000000000000000000000009235181440,-499999999999999999999999999999999999999999999999989105858860⟩⟩
lemma phaseBox21_calc : (phaseInputBox 21).exp = phaseBox21 := by decide +kernel
lemma phaseBox21_mem : phaseBox21.Mem (phase ((21:ℤ):ℂ)) := by
  rw [← phaseBox21_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 21) (by decide +kernel)
def phaseBox22 : CI := ⟨⟨-766044443118978035202392650555416673935832457080406888294869,-766044443118978035202392650555416673935832457080384893374795⟩,⟨-642787609686539326322643409907263432907559884205692234760934,-642787609686539326322643409907263432907559884205669808574574⟩⟩
lemma phaseBox22_calc : (phaseInputBox 22).exp = phaseBox22 := by decide +kernel
lemma phaseBox22_mem : phaseBox22.Mem (phase ((22:ℤ):ℂ)) := by
  rw [← phaseBox22_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 22) (by decide +kernel)
def phaseBox23 : CI := ⟨⟨-642787609686539326322643409907263432907559884205694695891306,-642787609686539326322643409907263432907559884205670491952222⟩,⟨-766044443118978035202392650555416673935832457080406878657306,-766044443118978035202392650555416673935832457080382264458734⟩⟩
lemma phaseBox23_calc : (phaseInputBox 23).exp = phaseBox23 := by decide +kernel
lemma phaseBox23_mem : phaseBox23.Mem (phase ((23:ℤ):ℂ)) := by
  rw [← phaseBox23_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 23) (by decide +kernel)
def phaseBox24 : CI := ⟨⟨-500000000000000000000000000000000000000000000000014096951365,-499999999999999999999999999999999999999999999999987799006330⟩,⟨-866025403784438646763723170752936183471402626905203089251490,-866025403784438646763723170752936183471402626905176444175326⟩⟩
lemma phaseBox24_calc : (phaseInputBox 24).exp = phaseBox24 := by decide +kernel
lemma phaseBox24_mem : phaseBox24.Mem (phase ((24:ℤ):ℂ)) := by
  rw [← phaseBox24_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 24) (by decide +kernel)
def phaseBox25 : CI := ⟨⟨-342020143325668733044099614682259580763083367514175810431770,-342020143325668733044099614682259580763083367514147589449286⟩,⟨-939692620785908384054109277324731469936208134264478478914456,-939692620785908384054109277324731469936208134264450007296924⟩⟩
lemma phaseBox25_calc : (phaseInputBox 25).exp = phaseBox25 := by decide +kernel
lemma phaseBox25_mem : phaseBox25.Mem (phase ((25:ℤ):ℂ)) := by
  rw [← phaseBox25_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 25) (by decide +kernel)
def phaseBox26 : CI := ⟨⟨-173648177666930348851716626769314796000375677184085513919999,-173648177666930348851716626769314796000375677184055596221926⟩,⟨-984807753012208059366743024589523013670643251719857237281372,-984807753012208059366743024589523013670643251719827188460900⟩⟩
lemma phaseBox26_calc : (phaseInputBox 26).exp = phaseBox26 := by decide +kernel
lemma phaseBox26_mem : phaseBox26.Mem (phase ((26:ℤ):ℂ)) := by
  rw [← phaseBox26_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 26) (by decide +kernel)
def phaseBox27 : CI := ⟨⟨-16899068771,14436150239⟩,⟨-1000000000000000000000000000000000000000000000000015667611120,-999999999999999999999999999999999999999999999999984332392110⟩⟩
lemma phaseBox27_calc : (phaseInputBox 27).exp = phaseBox27 := by decide +kernel
lemma phaseBox27_mem : phaseBox27.Mem (phase ((27:ℤ):ℂ)) := by
  rw [← phaseBox27_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 27) (by decide +kernel)
def phaseBox28 : CI := ⟨⟨173648177666930348851716626769314796000375677184051917148030,173648177666930348851716626769314796000375677184084341989196⟩,⟨-984807753012208059366743024589523013670643251719858787552808,-984807753012208059366743024589523013670643251719826493551508⟩⟩
lemma phaseBox28_calc : (phaseInputBox 28).exp = phaseBox28 := by decide +kernel
lemma phaseBox28_mem : phaseBox28.Mem (phase ((28:ℤ):ℂ)) := by
  rw [← phaseBox28_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 28) (by decide +kernel)
def phaseBox29 : CI := ⟨⟨342020143325668733044099614682259580763083367514142813650362,342020143325668733044099614682259580763083367514175957454200⟩,⟨-939692620785908384054109277324731469936208134264481532580062,-939692620785908384054109277324731469936208134264448638369502⟩⟩
lemma phaseBox29_calc : (phaseInputBox 29).exp = phaseBox29 := by decide +kernel
lemma phaseBox29_mem : phaseBox29.Mem (phase ((29:ℤ):ℂ)) := by
  rw [← phaseBox29_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 29) (by decide +kernel)
def phaseBox30 : CI := ⟨⟨499999999999999999999999999999999999999999999999982086571115,500000000000000000000000000000000000000000000000015543483824⟩,⟨-866025403784438646763723170752936183471402626905207554081534,-866025403784438646763723170752936183471402626905174442267480⟩⟩
lemma phaseBox30_calc : (phaseInputBox 30).exp = phaseBox30 := by decide +kernel
lemma phaseBox30_mem : phaseBox30.Mem (phase ((30:ℤ):ℂ)) := by
  rw [← phaseBox30_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 30) (by decide +kernel)
def phaseBox31 : CI := ⟨⟨642787609686539326322643409907263432907559884205664038197821,642787609686539326322643409907263432907559884205697376234924⟩,⟨-766044443118978035202392650555416673935832457080412620035652,-766044443118978035202392650555416673935832457080379689347294⟩⟩
lemma phaseBox31_calc : (phaseInputBox 31).exp = phaseBox31 := by decide +kernel
lemma phaseBox31_mem : phaseBox31.Mem (phase ((31:ℤ):ℂ)) := by
  rw [← phaseBox31_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 31) (by decide +kernel)
def phaseBox32 : CI := ⟨⟨766044443118978035202392650555416673935832457080377922011624,766044443118978035202392650555416673935832457080410693391161⟩,⟨-642787609686539326322643409907263432907559884205699080092946,-642787609686539326322643409907263432907559884205666736654508⟩⟩
lemma phaseBox32_calc : (phaseInputBox 32).exp = phaseBox32 := by decide +kernel
lemma phaseBox32_mem : phaseBox32.Mem (phase ((32:ℤ):ℂ)) := by
  rw [← phaseBox32_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 32) (by decide +kernel)
def phaseBox33 : CI := ⟨⟨866025403784438646763723170752936183471402626905173685228535,866025403784438646763723170752936183471402626905205437711262⟩,⟨-500000000000000000000000000000000000000000000000016979488526,-499999999999999999999999999999999999999999999999985627454324⟩⟩
lemma phaseBox33_calc : (phaseInputBox 33).exp = phaseBox33 := by decide +kernel
lemma phaseBox33_mem : phaseBox33.Mem (phase ((33:ℤ):ℂ)) := by
  rw [← phaseBox33_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 33) (by decide +kernel)
def phaseBox34 : CI := ⟨⟨939692620785908384054109277324731469936208134264448958204507,939692620785908384054109277324731469936208134264479247218206⟩,⟨-342020143325668733044099614682259580763083367514177069829976,-342020143325668733044099614682259580763083367514147101516694⟩⟩
lemma phaseBox34_calc : (phaseInputBox 34).exp = phaseBox34 := by decide +kernel
lemma phaseBox34_mem : phaseBox34.Mem (phase ((34:ℤ):ℂ)) := by
  rw [← phaseBox34_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 34) (by decide +kernel)
def phaseBox35 : CI := ⟨⟨984807753012208059366743024589523013670643251719827941038041,984807753012208059366743024589523013670643251719856342140171⟩,⟨-173648177666930348851716626769314796000375677184085066392648,-173648177666930348851716626769314796000375677184056852251010⟩⟩
lemma phaseBox35_calc : (phaseInputBox 35).exp = phaseBox35 := by decide +kernel
lemma phaseBox35_mem : phaseBox35.Mem (phase ((35:ℤ):ℂ)) := by
  rw [← phaseBox35_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 35) (by decide +kernel)
def coeffBox0 (j : Fin 31) : CI := if j.val=0 then CI.point 1 else CI.point 0
lemma coeffBox0_mem (j : Fin 31) : (coeffBox0 j).Mem ((partialPolynomial 0).coeff j.val) := by
  rw [partialPolynomial_zero]
  simp only [coeffBox0, coeff_one]
  split_ifs
  · simpa using CI.mem_point 1
  · simpa using CI.mem_point 0

def coeffBox1 : Fin 31 → CI :=
  ![⟨⟨-1000000000000000000000000000000000000000000000000000000066559,-999999999999999999999999999999999999999999999999999999935488⟩,⟨-68606,63488⟩⟩,
  ⟨⟨1999999999999999999999999999999999999999999999999999999999998,2000000000000000000000000000000000000000000000000000000000002⟩,⟨0,4⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000000000000000066561,-999999999999999999999999999999999999999999999999999999935486⟩,⟨-63488,68610⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩]
lemma coeffBox1_calc (j : Fin 31) : coeffStep phaseBox0 coeffBox0 j = coeffBox1 j := by
  revert j
  decide +kernel
lemma coeffBox1_mem (j : Fin 31) : (coeffBox1 j).Mem ((partialPolynomial 1).coeff j.val) := by
  rw [← coeffBox1_calc, partialPolynomial_succ (by norm_num : 0 < 15)]
  apply coeffStep_mem ⟨0,by norm_num⟩ (partialPolynomial 0) phaseBox0 coeffBox0
  · have hr : residue ⟨0,by norm_num⟩ = (0:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox0_mem
  · exact coeffBox0_mem
def coeffBox2 : Fin 31 → CI :=
  ![⟨⟨984807753012208059366743024589523013670643251719842378184993,984807753012208059366743024589523013670643251719842475238537⟩,⟨173648177666930348851716626769314796000375677184069062988405,173648177666930348851716626769314796000375677184069621659986⟩⟩,
  ⟨⟨-3969615506024416118733486049179046027341286503439684950457050,-3969615506024416118733486049179046027341286503439684756391850⟩,⟨-347296355333860697703433253538629592000751354368139243298945,-347296355333860697703433253538629592000751354368138125997284⟩⟩,
  ⟨⟨5969615506024416118733486049179046027341286503439684756371757,5969615506024416118733486049179046027341286503439684950478860⟩,⟨-558671585,558671592⟩⟩,
  ⟨⟨-3969615506024416118733486049179046027341286503439684950457058,-3969615506024416118733486049179046027341286503439684756391842⟩,⟨347296355333860697703433253538629592000751354368138125997278,347296355333860697703433253538629592000751354368139243298954⟩⟩,
  ⟨⟨984807753012208059366743024589523013670643251719842378184979,984807753012208059366743024589523013670643251719842475238550⟩,⟨-173648177666930348851716626769314796000375677184069621660000,-173648177666930348851716626769314796000375677184069062988392⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩]
lemma coeffBox2_calc (j : Fin 31) : coeffStep phaseBox1 coeffBox1 j = coeffBox2 j := by
  revert j
  decide +kernel
lemma coeffBox2_mem (j : Fin 31) : (coeffBox2 j).Mem ((partialPolynomial 2).coeff j.val) := by
  rw [← coeffBox2_calc, partialPolynomial_succ (by norm_num : 1 < 15)]
  apply coeffStep_mem ⟨1,by norm_num⟩ (partialPolynomial 1) phaseBox1 coeffBox1
  · have hr : residue ⟨1,by norm_num⟩ = (1:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox1_mem
  · exact coeffBox1_mem
def coeffBox3 : Fin 31 → CI :=
  ![⟨⟨-766044443118978035202392650555416673935832457080396117377661,-766044443118978035202392650555416673935832457080394608865489⟩,⟨-642787609686539326322643409907263432907559884205682848189797,-642787609686539326322643409907263432907559884205680452962922⟩⟩,
  ⟨⟨5233755199831249482665717691795751742155756671410853883156340,5233755199831249482665717691795751742155756671410858805946723⟩,⟨2632871574706939350348720073353156457815871122779497054238603,2632871574706939350348720073353156457815871122779506443385298⟩⟩,
  ⟨⟨-14048762311877381627832475986574716402376432240109459794605323,-14048762311877381627832475986574716402376432240109452062046354⟩,⟨-3337380320354260721729509916984522616909062592941966588825188,-3337380320354260721729509916984522616909062592941950502964245⟩⟩,
  ⟨⟨19162103110330220360738301890668762668313016051557984971001343,19162103110330220360738301890668762668313016051557994816582159⟩,⟨-9389146712,9389146726⟩⟩,
  ⟨⟨-14048762311877381627832475986574716402376432240109459794605361,-14048762311877381627832475986574716402376432240109452062046323⟩,⟨3337380320354260721729509916984522616909062592941950502964210,3337380320354260721729509916984522616909062592941966588825220⟩⟩,
  ⟨⟨5233755199831249482665717691795751742155756671410853883156279,5233755199831249482665717691795751742155756671410858805946781⟩,⟨-2632871574706939350348720073353156457815871122779506443385357,-2632871574706939350348720073353156457815871122779497054238545⟩⟩,
  ⟨⟨-766044443118978035202392650555416673935832457080396117377731,-766044443118978035202392650555416673935832457080394608865417⟩,⟨642787609686539326322643409907263432907559884205680452962854,642787609686539326322643409907263432907559884205682848189871⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩]
lemma coeffBox3_calc (j : Fin 31) : coeffStep phaseBox3 coeffBox2 j = coeffBox3 j := by
  revert j
  decide +kernel
lemma coeffBox3_mem (j : Fin 31) : (coeffBox3 j).Mem ((partialPolynomial 3).coeff j.val) := by
  rw [← coeffBox3_calc, partialPolynomial_succ (by norm_num : 2 < 15)]
  apply coeffStep_mem ⟨2,by norm_num⟩ (partialPolynomial 2) phaseBox3 coeffBox2
  · have hr : residue ⟨2,by norm_num⟩ = (3:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox3_mem
  · exact coeffBox2_mem
def coeffBox4 : Fin 31 → CI :=
  ![⟨⟨173648177666930348851716626769314796000375677184067055979553,173648177666930348851716626769314796000375677184072437144710⟩,⟨984807753012208059366743024589523013670643251719839555037241,984807753012208059366743024589523013670643251719845155832624⟩⟩,
  ⟨⟨-3849000747596232886841704603828508967213702771968629488887413,-3849000747596232886841704603828508967213702771968602523815191⟩,⟨-6666664853207267609891776724753869180900487454540783066994312,-6666664853207267609891776724753869180900487454540751449734765⟩⟩,
  ⟨⟨20084259982640082076513803988265308500673999989471170101688802,20084259982640082076513803988265308500673999989471230625140459⟩,⟨16852695143901897122188587307880678000655273393900321520999821,16852695143901897122188587307880678000655273393900401814969538⟩⟩,
  ⟨⟨-48478213543489407248647662562791111952021410423330865453927342,-48478213543489407248647662562791111952021410423330777721731770⟩,⟨-17644626740230823652168816539857840513291657431057853768631887,-17644626740230823652168816539857840513291657431057728196598947⟩⟩,
  ⟨⟨64138612261557255420247693103169995245121475057288279826121600,64138612261557255420247693103169995245121475057288390110694792⟩,⟨-74693174411,74693174447⟩⟩,
  ⟨⟨-48478213543489407248647662562791111952021410423330865453927510,-48478213543489407248647662562791111952021410423330777721731632⟩,⟨17644626740230823652168816539857840513291657431057728196598787,17644626740230823652168816539857840513291657431057853768632026⟩⟩,
  ⟨⟨20084259982640082076513803988265308500673999989471170101688538,20084259982640082076513803988265308500673999989471230625140728⟩,⟨-16852695143901897122188587307880678000655273393900401814969806,-16852695143901897122188587307880678000655273393900321520999559⟩⟩,
  ⟨⟨-3849000747596232886841704603828508967213702771968629488887740,-3849000747596232886841704603828508967213702771968602523814856⟩,⟨6666664853207267609891776724753869180900487454540751449734441,6666664853207267609891776724753869180900487454540783066994648⟩⟩,
  ⟨⟨173648177666930348851716626769314796000375677184067055979197,173648177666930348851716626769314796000375677184072437145063⟩,⟨-984807753012208059366743024589523013670643251719845155832977,-984807753012208059366743024589523013670643251719839555036885⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩]
lemma coeffBox4_calc (j : Fin 31) : coeffStep phaseBox4 coeffBox3 j = coeffBox4 j := by
  revert j
  decide +kernel
lemma coeffBox4_mem (j : Fin 31) : (coeffBox4 j).Mem ((partialPolynomial 4).coeff j.val) := by
  rw [← coeffBox4_calc, partialPolynomial_succ (by norm_num : 3 < 15)]
  apply coeffStep_mem ⟨3,by norm_num⟩ (partialPolynomial 3) phaseBox4 coeffBox3
  · have hr : residue ⟨3,by norm_num⟩ = (4:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox4_mem
  · exact coeffBox3_mem
def coeffBox5 : Fin 31 → CI :=
  ![⟨⟨866025403784438646763723170752936183471402626905183735048403,866025403784438646763723170752936183471402626905196208881899⟩,⟨-500000000000000000000000000000000000000000000000006583676919,-499999999999999999999999999999999999999999999999994601281521⟩⟩,
  ⟨⟨-4600883625124310132316997618442595284339885548631398205006316,-4600883625124310132316997618442595284339885548631300770460832⟩,⟨7866626774538188833014437765148908199971627794190314318391088,7866626774538188833014437765148908199971627794190408160613198⟩⟩,
  ⟨⟨284322541021897412154482253411142429365827116374327333764321,284322541021897412154482253411142429365827116374654661624875⟩,⟨-38143969992255195427604056742112035636044052309928576801899610,-38143969992255195427604056742112035636044052309928251042517266⟩⟩,
  ⟨⟨47749571520445274333396758921864998335504508004721094284979159,47749571520445274333396758921864998335504508004721739415601413⟩,⟨83958083658808470377564491603083021265181338999591417977106533,83958083658808470377564491603083021265181338999592089692084061⟩⟩,
  ⟨⟨-141598699190317800022480092434120163989670454080447340694763832,-141598699190317800022480092434120163989670454080446453087511678⟩,⟨-82450764439004109804374564040425568422117032246160186905322725,-82450764439004109804374564040425568422117032246159228891032639⟩⟩,
  ⟨⟨194599326700380999524964251413067364651337203762153749421765467,194599326700380999524964251413067364651337203762154844813919778⟩,⟨-577872755749,577872755858⟩⟩,
  ⟨⟨-141598699190317800022480092434120163989670454080447340694764545,-141598699190317800022480092434120163989670454080446453087511097⟩,⟨82450764439004109804374564040425568422117032246159228891031967,82450764439004109804374564040425568422117032246160186905323332⟩⟩,
  ⟨⟨47749571520445274333396758921864998335504508004721094284978035,47749571520445274333396758921864998335504508004721739415602586⟩,⟨-83958083658808470377564491603083021265181338999592089692085231,-83958083658808470377564491603083021265181338999591417977105406⟩⟩,
  ⟨⟨284322541021897412154482253411142429365827116374327333762875,284322541021897412154482253411142429365827116374654661626344⟩,⟨38143969992255195427604056742112035636044052309928251042515828,38143969992255195427604056742112035636044052309928576801901082⟩⟩,
  ⟨⟨-4600883625124310132316997618442595284339885548631398205007919,-4600883625124310132316997618442595284339885548631300770459247⟩,⟨-7866626774538188833014437765148908199971627794190408160614786,-7866626774538188833014437765148908199971627794190314318389487⟩⟩,
  ⟨⟨866025403784438646763723170752936183471402626905183735046769,866025403784438646763723170752936183471402626905196208883536⟩,⟨499999999999999999999999999999999999999999999999994601279887,500000000000000000000000000000000000000000000000006583678559⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩]
lemma coeffBox5_calc (j : Fin 31) : coeffStep phaseBox7 coeffBox4 j = coeffBox5 j := by
  revert j
  decide +kernel
lemma coeffBox5_mem (j : Fin 31) : (coeffBox5 j).Mem ((partialPolynomial 5).coeff j.val) := by
  rw [← coeffBox5_calc, partialPolynomial_succ (by norm_num : 4 < 15)]
  apply coeffStep_mem ⟨4,by norm_num⟩ (partialPolynomial 4) phaseBox7 coeffBox4
  · have hr : residue ⟨4,by norm_num⟩ = (7:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox7_mem
  · exact coeffBox4_mem
def coeffBox6 : Fin 31 → CI :=
  ![⟨⟨-500000000000000000000000000000000000000000000000011399596808,-499999999999999999999999999999999999999999999999990496341924⟩,⟨-866025403784438646763723170752936183471402626905200464070792,-866025403784438646763723170752936183471402626905179069377810⟩⟩,
  ⟨⟨9598677582107066126541884106654780566914433048000642967408834,9598677582107066126541884106654780566914433048000843176653748⟩,⟨3600883625124310132316997618442595284339885548631243664311187,3600883625124310132316997618442595284339885548631446483003275⟩⟩,
  ⟨⟨-46845737242503815692238051978997226204723823407191509021720497,-46845737242503815692238051978997226204723823407190716533167499⟩,⟨16314956411838918900638116447639610154048831098911043634092672,16314956411838918900638116447639610154048831098911830997915191⟩⟩,
  ⟨⟨76660101966314076368859018344756397923941365438149176002703563,76660101966314076368859018344756397923941365438151537754771158⟩,⟨-128638395130079975320921870024531664891932498173210799686614747,-128638395130079975320921870024531664891932498173208464063535513⟩⟩,
  ⟨⟨51192348594141634290023010545416463884936036073209453655943824,51192348594141634290023010545416463884936036073213741807724123⟩,⟨309799189048956638189763557893697348949398959196002808819438913,309799189048956638189763557893697348949398959196007081301370058⟩⟩,
  ⟨⟨-367155482039444070422524676471323349244522247160488513912326776,-367155482039444070422524676471323349244522247160482780282282390⟩,⟨-311751284057943944800316620572053503160066760249755224280743448,-311751284057943944800316620572053503160066760249749436774335611⟩⟩,
  ⟨⟨554100182278770218658677630906985866146908472016624609713747195,554100182278770218658677630906985866146908472016631642846714388⟩,⟨-3506512802851,3506512803203⟩⟩,
  ⟨⟨-367155482039444070422524676471323349244522247160488513912329481,-367155482039444070422524676471323349244522247160482780282280210⟩,⟨311751284057943944800316620572053503160066760249749436774333096,311751284057943944800316620572053503160066760249755224280745788⟩⟩,
  ⟨⟨51192348594141634290023010545416463884936036073209453655939531,51192348594141634290023010545416463884936036073213741807728613⟩,⟨-309799189048956638189763557893697348949398959196007081301374578,-309799189048956638189763557893697348949398959196002808819434630⟩⟩,
  ⟨⟨76660101966314076368859018344756397923941365438149176002697956,76660101966314076368859018344756397923941365438151537754776867⟩,⟨128638395130079975320921870024531664891932498173208464063529930,128638395130079975320921870024531664891932498173210799686620469⟩⟩,
  ⟨⟨-46845737242503815692238051978997226204723823407191509021726809,-46845737242503815692238051978997226204723823407190716533161251⟩,⟨-16314956411838918900638116447639610154048831098911830997921448,-16314956411838918900638116447639610154048831098911043634086365⟩⟩,
  ⟨⟨9598677582107066126541884106654780566914433048000642967402323,9598677582107066126541884106654780566914433048000843176660260⟩,⟨-3600883625124310132316997618442595284339885548631446483009789,-3600883625124310132316997618442595284339885548631243664304675⟩⟩,
  ⟨⟨-500000000000000000000000000000000000000000000000011399603377,-499999999999999999999999999999999999999999999999990496335353⟩,⟨866025403784438646763723170752936183471402626905179069371251,866025403784438646763723170752936183471402626905200464077372⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩]
lemma coeffBox6_calc (j : Fin 31) : coeffStep phaseBox9 coeffBox5 j = coeffBox6 j := by
  revert j
  decide +kernel
lemma coeffBox6_mem (j : Fin 31) : (coeffBox6 j).Mem ((partialPolynomial 6).coeff j.val) := by
  rw [← coeffBox6_calc, partialPolynomial_succ (by norm_num : 5 < 15)]
  apply coeffStep_mem ⟨5,by norm_num⟩ (partialPolynomial 5) phaseBox9 coeffBox5
  · have hr : residue ⟨5,by norm_num⟩ = (9:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox9_mem
  · exact coeffBox5_mem
def coeffBox7 : Fin 31 → CI :=
  ![⟨⟨-1000000000000000000000000000000000000000000000000021064579145,-999999999999999999999999999999999999999999999999978935435132⟩,⟨-19419482911,22703347133⟩⟩,
  ⟨⟨6917795486482586948753916921160270903681923406438942996395084,6917795486482586948753916921160270903681923406439389871389727⟩,⟨-8244307623847633411984384969508491764631092645119045359892662,-8244307623847633411984384969508491764631092645118601301227783⟩⟩,
  ⟨⟨10403653257250540448686234131604908102467273346226538973686726,10403653257250540448686234131604908102467273346228678869857872⟩,⟨55062818563402723511256155041554773494989859649215310169708880,55062818563402723511256155041554773494989859649217442676911621⟩⟩,
  ⟨⟨-165084659490935790669487097141401509335117754010472993686228301,-165084659490935790669487097141401509335117754010465823162448457⟩,⟨-87965740059492470667549121704228599039092155747508840626619456,-87965740059492470667549121704228599039092155747501649940149410⟩⟩,
  ⟨⟨409658310682373061938766591695979016771084187651579803715918016,409658310682373061938766591695979016771084187651595505195632065⟩,⟨-179123190402696503470650774138165392847142764409030348970581920,-179123190402696503470650774138165392847142764409014583986566430⟩⟩,
  ⟨⟨-201443406420170187339928907039772853380241319507540216335880830,-201443406420170187339928907039772853380241319507511989283855915⟩,⟨783759108848314465844577513638772579929776019388219385226335817,783759108848314465844577513638772579929776019388247569157895248⟩⟩,
  ⟨⟨-699958666430646530314576599847496095627217909672167995896284820,-699958666430646530314576599847496095627217909672132157718356598⟩,⟨-904133933324497355691380683436857502048917864934765436894996171,-904133933324497355691380683436857502048917864934729617988374113⟩⟩,
  ⟨⟨1281013945831292637975571722559852525130687197571760813056944388,1281013945831292637975571722559852525130687197571803819863436107⟩,⟨-21437303759894,21437303760967⟩⟩,
  ⟨⟨-699958666430646530314576599847496095627217909672167995896296595,-699958666430646530314576599847496095627217909672132157718346589⟩,⟨904133933324497355691380683436857502048917864934729617988363113,904133933324497355691380683436857502048917864934765436895006887⟩⟩,
  ⟨⟨-201443406420170187339928907039772853380241319507540216335900433,-201443406420170187339928907039772853380241319507511989283835858⟩,⟨-783759108848314465844577513638772579929776019388247569157915623,-783759108848314465844577513638772579929776019388219385226316474⟩⟩,
  ⟨⟨409658310682373061938766591695979016771084187651579803715892372,409658310682373061938766591695979016771084187651595505195658228⟩,⟨179123190402696503470650774138165392847142764409014583986540750,179123190402696503470650774138165392847142764409030348970608014⟩⟩,
  ⟨⟨-165084659490935790669487097141401509335117754010472993686257580,-165084659490935790669487097141401509335117754010465823162419376⟩,⟨87965740059492470667549121704228599039092155747501649940120353,87965740059492470667549121704228599039092155747508840626648772⟩⟩,
  ⟨⟨10403653257250540448686234131604908102467273346226538973656122,10403653257250540448686234131604908102467273346228678869888423⟩,⟨-55062818563402723511256155041554773494989859649217442676942211,-55062818563402723511256155041554773494989859649215310169678311⟩⟩,
  ⟨⟨6917795486482586948753916921160270903681923406438942996364070,6917795486482586948753916921160270903681923406439389871420762⟩,⟨8244307623847633411984384969508491764631092645118601301196787,8244307623847633411984384969508491764631092645119045359923713⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000000000021064610266,-999999999999999999999999999999999999999999999999978935404011⟩,⟨-22703378225,19419514063⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩]
lemma coeffBox7_calc (j : Fin 31) : coeffStep phaseBox12 coeffBox6 j = coeffBox7 j := by
  revert j
  decide +kernel
lemma coeffBox7_mem (j : Fin 31) : (coeffBox7 j).Mem ((partialPolynomial 7).coeff j.val) := by
  rw [← coeffBox7_calc, partialPolynomial_succ (by norm_num : 6 < 15)]
  apply coeffStep_mem ⟨6,by norm_num⟩ (partialPolynomial 6) phaseBox12 coeffBox6
  · have hr : residue ⟨6,by norm_num⟩ = (12:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox12_mem
  · exact coeffBox6_mem
def coeffBox8 : Fin 31 → CI :=
  ![⟨⟨-642787609686539326322643409907263432907559884205715205990796,-642787609686539326322643409907263432907559884205644950671034⟩,⟨766044443118978035202392650555416673935832457080361820302316,766044443118978035202392650555416673935832457080431544495687⟩⟩,
  ⟨⟨-3868832817555432838789551276936722917397080294821431008893657,-3868832817555432838789551276936722917397080294820558344285185⟩,⟨-10598677582107066126541884106654780566914433048001170265550136,-10598677582107066126541884106654780566914433048000296560859766⟩⟩,
  ⟨⟨62060708955477453960923877148516799656043731889319834405748786,62060708955477453960923877148516799656043731889324492277286679⟩,⟨10169377070305564859724257431925253462504015971578085941037352,10169377070305564859724257431925253462504015971582762313946973⟩⟩,
  ⟨⟨-141930554245348113630828032308910091907912775884948329464179964,-141930554245348113630828032308910091907912775884930430457098204⟩,⟨180044535386876843869158452121621522566314576656835597773329493,180044535386876843869158452121621522566314576656853439550084625⟩⟩,
  ⟨⟨-239555584085579127298262843034489804366753137625289066027813840,-239555584085579127298262843034489804366753137625242534997781282⟩,⟨-561522761700274177377124604258583402652768405083680639217263737,-561522761700274177377124604258583402652768405083634173646730087⟩⟩,
  ⟨⟨1251496898429272207070423830816425442487874994080484684714885271,1251496898429272207070423830816425442487874994080578981609054392⟩,⟨116853391598027836019101484059740395430096723577773211491488973,116853391598027836019101484059740395430096723577867906940471597⟩⟩,
  ⟨⟨-1144878735419732574051742458397655413283608858240397601100012363,-1144878735419732574051742458397655413283608858240245160313601803⟩,⟨1721229879768017096080962796089755917357404834773775078467099799,1721229879768017096080962796089755917357404834773927413539632397⟩⟩,
  ⟨⟨-1306377076422343307053265617545683906128011426452724152473114895,-1306377076422343307053265617545683906128011426452527952531204663⟩,⟨-2440105439355440960610695384981918413423708827380975627250822799,-2440105439355440960610695384981918413423708827380779815883036971⟩⟩,
  ⟨⟨3047391926430990866335726876017281919785344224824540086495050736,3047391926430990866335726876017281919785344224824761081240298219⟩,⟨-110476150741195,110476150744512⟩⟩,
  ⟨⟨-1306377076422343307053265617545683906128011426452724152473167476,-1306377076422343307053265617545683906128011426452527952531157758⟩,⟨2440105439355440960610695384981918413423708827380779815882987202,2440105439355440960610695384981918413423708827380975627250872373⟩⟩,
  ⟨⟨-1144878735419732574051742458397655413283608858240397601100103503,-1144878735419732574051742458397655413283608858240245160313510024⟩,⟨-1721229879768017096080962796089755917357404834773927413539725785,-1721229879768017096080962796089755917357404834773775078467010137⟩⟩,
  ⟨⟨1251496898429272207070423830816425442487874994080484684714765487,1251496898429272207070423830816425442487874994080578981609176368⟩,⟨-116853391598027836019101484059740395430096723577867906940592023,-116853391598027836019101484059740395430096723577773211491367713⟩⟩,
  ⟨⟨-239555584085579127298262843034489804366753137625289066027951977,-239555584085579127298262843034489804366753137625242534997643575⟩,⟨561522761700274177377124604258583402652768405083634173646592757,561522761700274177377124604258583402652768405083680639217402280⟩⟩,
  ⟨⟨-141930554245348113630828032308910091907912775884948329464326130,-141930554245348113630828032308910091907912775884930430456952416⟩,⟨-180044535386876843869158452121621522566314576656853439550230607,-180044535386876843869158452121621522566314576656835597773183514⟩⟩,
  ⟨⟨62060708955477453960923877148516799656043731889319834405599846,62060708955477453960923877148516799656043731889324492277435689⟩,⟨-10169377070305564859724257431925253462504015971582762314095896,-10169377070305564859724257431925253462504015971578085940888331⟩⟩,
  ⟨⟨-3868832817555432838789551276936722917397080294821431009043466,-3868832817555432838789551276936722917397080294820558344135361⟩,⟨10598677582107066126541884106654780566914433048000296560710054,10598677582107066126541884106654780566914433048001170265700058⟩⟩,
  ⟨⟨-642787609686539326322643409907263432907559884205715206140780,-642787609686539326322643409907263432907559884205644950521053⟩,⟨-766044443118978035202392650555416673935832457080431544645576,-766044443118978035202392650555416673935832457080361820152239⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩]
lemma coeffBox8_calc (j : Fin 31) : coeffStep phaseBox13 coeffBox7 j = coeffBox8 j := by
  revert j
  decide +kernel
lemma coeffBox8_mem (j : Fin 31) : (coeffBox8 j).Mem ((partialPolynomial 8).coeff j.val) := by
  rw [← coeffBox8_calc, partialPolynomial_succ (by norm_num : 7 < 15)]
  apply coeffStep_mem ⟨7,by norm_num⟩ (partialPolynomial 7) phaseBox13 coeffBox7
  · have hr : residue ⟨7,by norm_num⟩ = (13:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox13_mem
  · exact coeffBox7_mem
def coeffBox9 : Fin 31 → CI :=
  ![⟨⟨-342020143325668733044099614682259580763083367514211711020077,-342020143325668733044099614682259580763083367514103974270900⟩,⟨939692620785908384054109277324731469936208134264411915337969,939692620785908384054109277324731469936208134264519378773918⟩⟩,
  ⟨⟨-8546050094779084377999995279403332120772903723070439782024673,-8546050094779084377999995279403332120772903723068997865637239⟩,⟨-7104191472993727658220477472822081860370109043820363676439438,-7104191472993727658220477472822081860370109043818919791367384⟩⟩,
  ⟨⟨53192431010427477720931580224837648280116394338512048806212770,53192431010427477720931580224837648280116394338520804923691523⟩,⟨-32367279145103585003648839828133711987418689984026164839430940,-32367279145103585003648839828133711987418689984017414434627835⟩⟩,
  ⟨⟨52318628796553873942328933638360685806200044358742822194261277,52318628796553873942328933638360685806200044358780443681535818⟩,⟨226785666093013813713357576348077107247170054189914163336179144,226785666093013813713357576348077107247170054189951804297088302⟩⟩,
  ⟨⟨-646181960118240802195224849480853572707850039843872265453185230,-646181960118240802195224849480853572707850039843759830638340523⟩,⟨-54854788433103423019729288476666748903659658107071858586761288,-54854788433103423019729288476666748903659658106959469610007987⟩⟩,
  ⟨⟨541927493675297551999659729871028089280460199295238151919751795,541927493675297551999659729871028089280460199295496798444641212⟩,⟨-1320632989363895133292426257567093585605520632694305134173278950,-1320632989363895133292426257567093585605520632694046807128722444⟩⟩,
  ⟨⟨1982798468468676290624971051539277517788815640382742221282187773,1982798468468676290624971051539277517788815640383232196738845857⟩,⟨1633113758292559146271181035052996054187082431105413424990840548,1633113758292559146271181035052996054187082431105904416852759211⟩⟩,
  ⟨⟨-3215859394967511030987679175935174189434921531107857777705497725,-3215859394967511030987679175935174189434921531107115596460315526⟩,⟨2134161377520389784686638956331344866464578186393619252205296584,2134161377520389784686638956331344866464578186394361227660281172⟩⟩,
  ⟨⟨-1413671836478236560593936860673999082623840470010028390836039547,-1413671836478236560593936860673999082623840470009081855886079859⟩,⟨-4696624874642840501363796288174842396467577340902915864233076807,-4696624874642840501363796288174842396467577340901971079622760932⟩⟩,
  ⟨⟨5308728479702275905199987371421216990625111499351098268029990317,5308728479702275905199987371421216990625111499352137696612587995⟩,⟨-519845486379990,519845486388385⟩⟩,
  ⟨⟨-1413671836478236560593936860673999082623840470010028390836263428,-1413671836478236560593936860673999082623840470009081855885870274⟩,⟨4696624874642840501363796288174842396467577340901971079622545367,4696624874642840501363796288174842396467577340902915864233294501⟩⟩,
  ⟨⟨-3215859394967511030987679175935174189434921531107857777705900119,-3215859394967511030987679175935174189434921531107115596459914776⟩,⟨-2134161377520389784686638956331344866464578186394361227660687578,-2134161377520389784686638956331344866464578186393619252204899715⟩⟩,
  ⟨⟨1982798468468676290624971051539277517788815640382742221281655119,1982798468468676290624971051539277517788815640383232196739384780⟩,⟨-1633113758292559146271181035052996054187082431105904416853295136,-1633113758292559146271181035052996054187082431105413424990304947⟩⟩,
  ⟨⟨541927493675297551999659729871028089280460199295238151919134207,541927493675297551999659729871028089280460199295496798445259357⟩,⟨1320632989363895133292426257567093585605520632694046807128106615,1320632989363895133292426257567093585605520632694305134173898869⟩⟩,
  ⟨⟨-646181960118240802195224849480853572707850039843872265453845644,-646181960118240802195224849480853572707850039843759830637681582⟩,⟨54854788433103423019729288476666748903659658106959469609348825,54854788433103423019729288476666748903659658107071858587421509⟩⟩,
  ⟨⟨52318628796553873942328933638360685806200044358742822193584141,52318628796553873942328933638360685806200044358780443682212828⟩,⟨-226785666093013813713357576348077107247170054189951804297765240,-226785666093013813713357576348077107247170054189914163335501945⟩⟩,
  ⟨⟨53192431010427477720931580224837648280116394338512048805530022,53192431010427477720931580224837648280116394338520804924374394⟩,⟨32367279145103585003648839828133711987418689984017414433945386,32367279145103585003648839828133711987418689984026164840114109⟩⟩,
  ⟨⟨-8546050094779084377999995279403332120772903723070439782708922,-8546050094779084377999995279403332120772903723068997864952990⟩,⟨7104191472993727658220477472822081860370109043818919790683513,7104191472993727658220477472822081860370109043820363677124067⟩⟩,
  ⟨⟨-342020143325668733044099614682259580763083367514211711704585,-342020143325668733044099614682259580763083367514103973586396⟩,⟨-939692620785908384054109277324731469936208134264519379458060,-939692620785908384054109277324731469936208134264411914653102⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩]
lemma coeffBox9_calc (j : Fin 31) : coeffStep phaseBox16 coeffBox8 j = coeffBox9 j := by
  revert j
  decide +kernel
lemma coeffBox9_mem (j : Fin 31) : (coeffBox9 j).Mem ((partialPolynomial 9).coeff j.val) := by
  rw [← coeffBox9_calc, partialPolynomial_succ (by norm_num : 8 < 15)]
  apply coeffStep_mem ⟨8,by norm_num⟩ (partialPolynomial 8) phaseBox16 coeffBox8
  · have hr : residue ⟨8,by norm_num⟩ = (16:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox16_mem
  · exact coeffBox8_mem
def coeffBox10 : Fin 31 → CI :=
  ![⟨⟨-500000000000000000000000000000000000000000000000068900041209,-499999999999999999999999999999999999999999999999924464149127⟩,⟨866025403784438646763723170752936183471402626905120178627774,866025403784438646763723170752936183471402626905264280639668⟩⟩,
  ⟨⟨-7866626774538188833014437765148908199971627794191447572472821,-7866626774538188833014437765148908199971627794189321939919936⟩,⟨-6600883625124310132316997618442595284339885548632392067331037,-6600883625124310132316997618442595284339885548630265113858998⟩⟩,
  ⟨⟨40739089132994957938266150337677580374796016120999326709445850,40739089132994957938266150337677580374796016121013805257717580⟩,⟨-35862353928348965355102339748684407766208223521464442119466510,-35862353928348965355102339748684407766208223521449960692840977⟩⟩,
  ⟨⟨108877889354584710277382157412267909524345878968498729683739106,108877889354584710277382157412267909524345878968566026875498444⟩,⟨162178501682506075077549880652292596695568517409507797601787543,162178501682506075077549880652292596695568517409575068285548190⟩⟩,
  ⟨⟨-475438513119195896047496353023017527047845748907274948211267956,-475438513119195896047496353023017527047845748907047336967802849⟩,⟨246229275274842394008708420720993397345433834098107007805216966,246229275274842394008708420720993397345433834098334731077378558⟩⟩,
  ⟨⟨-438439302020856399511006174874507873620850883672122444324611414,-438439302020856399511006174874507873620850883671521541758222176⟩,⟨-1101919214279253664965036074552028736211323059678545729369954823,-1101919214279253664965036074552028736211323059677945340737831230⟩⟩,
  ⟨⟨2107052625480202631622812170529616016695483076943670515473892952,2107052625480202631622812170529616016695483076944951833397253151⟩,⟨-630466648402993797186286626795947565118181981844940778313336508,-630466648402993797186286626795947565118181981843659135443493893⟩⟩,
  ⟨⟨732369323494674050945093748080595320877318083173653365613099094,732369323494674050945093748080595320877318083175903013653380885⟩,⟨3414863735263651370248900480843071354523797739444510657740251927,3414863735263651370248900480843071354523797739446761969382716412⟩⟩,
  ⟨⟨-4772090891587912160068984993141075852513232383268143574840789589,-4772090891587912160068984993141075852513232383264846052884953550⟩,⟨661562377266063277832866418891398493301858391615309584455957107,661562377266063277832866418891398493301858391618605548936594535⟩⟩,
  ⟨⟨-395676738216551395942468658603011383907053058832324840458132646,-395676738216551395942468658603011383907053058828205292091748011⟩,⟨-5811231928726367914873172624412156411733338670420282818800812792,-5811231928726367914873172624412156411733338670416165525757318008⟩⟩,
  ⟨⟨6201946288513195379238832782093209435634021294520380696586048632,6201946288513195379238832782093209435634021294524839658914149146⟩,⟨-2227707558823541,2227707558839947⟩⟩,
  ⟨⟨-395676738216551395942468658603011383907053058832324840459044147,-395676738216551395942468658603011383907053058828205292090862151⟩,⟨5811231928726367914873172624412156411733338670416165525756425041,5811231928726367914873172624412156411733338670420282818801716877⟩⟩,
  ⟨⟨-4772090891587912160068984993141075852513232383268143574842469856,-4772090891587912160068984993141075852513232383264846052883284048⟩,⟨-661562377266063277832866418891398493301858391618605548938276306,-661562377266063277832866418891398493301858391615309584454289056⟩⟩,
  ⟨⟨732369323494674050945093748080595320877318083173653365610851080,732369323494674050945093748080595320877318083175903013655638000⟩,⟨-3414863735263651370248900480843071354523797739446761969384971797,-3414863735263651370248900480843071354523797739444510657738002168⟩⟩,
  ⟨⟨2107052625480202631622812170529616016695483076943670515471275124,2107052625480202631622812170529616016695483076944951833399876575⟩,⟨630466648402993797186286626795947565118181981843659135440877045,630466648402993797186286626795947565118181981844940778315960920⟩⟩,
  ⟨⟨-438439302020856399511006174874507873620850883672122444327431830,-438439302020856399511006174874507873620850883671521541755403619⟩,⟨1101919214279253664965036074552028736211323059677945340735014857,1101919214279253664965036074552028736211323059678545729372777483⟩⟩,
  ⟨⟨-475438513119195896047496353023017527047845748907274948214178077,-475438513119195896047496353023017527047845748907047336964894250⟩,⟨-246229275274842394008708420720993397345433834098334731080286641,-246229275274842394008708420720993397345433834098107007802306327⟩⟩,
  ⟨⟨108877889354584710277382157412267909524345878968498729680796473,108877889354584710277382157412267909524345878968566026878441112⟩,⟨-162178501682506075077549880652292596695568517409575068288489601,-162178501682506075077549880652292596695568517409507797598843663⟩⟩,
  ⟨⟨40739089132994957938266150337677580374796016120999326706493436,40739089132994957938266150337677580374796016121013805260670111⟩,⟨35862353928348965355102339748684407766208223521449960689889965,35862353928348965355102339748684407766208223521464442122420444⟩⟩,
  ⟨⟨-7866626774538188833014437765148908199971627794191447575427510,-7866626774538188833014437765148908199971627794189321936965249⟩,⟨6600883625124310132316997618442595284339885548630265110905772,6600883625124310132316997618442595284339885548632392070287178⟩⟩,
  ⟨⟨-500000000000000000000000000000000000000000000000068902996253,-499999999999999999999999999999999999999999999999924461194087⟩,⟨-866025403784438646763723170752936183471402626905264283593264,-866025403784438646763723170752936183471402626905120175671299⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩]
lemma coeffBox10_calc (j : Fin 31) : coeffStep phaseBox19 coeffBox9 j = coeffBox10 j := by
  revert j
  decide +kernel
lemma coeffBox10_mem (j : Fin 31) : (coeffBox10 j).Mem ((partialPolynomial 10).coeff j.val) := by
  rw [← coeffBox10_calc, partialPolynomial_succ (by norm_num : 9 < 15)]
  apply coeffStep_mem ⟨9,by norm_num⟩ (partialPolynomial 9) phaseBox19 coeffBox9
  · have hr : residue ⟨9,by norm_num⟩ = (19:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox19_mem
  · exact coeffBox9_mem
def coeffBox11 : Fin 31 → CI :=
  ![⟨⟨-866025403784438646763723170752936183471402626905300135331630,-866025403784438646763723170752936183471402626905075703749691⟩,⟨499999999999999999999999999999999999999999999999892066551761,500000000000000000000000000000000000000000000000116228239841⟩⟩,
  ⟨⟨-4512256816278756118456938628002619397688287391310210258601118,-4512256816278756118456938628002619397688287391306729011161763⟩,⟨-7917795486482586948753916921160270903681923406440902367120502,-7917795486482586948753916921160270903681923406437420793245015⟩⟩,
  ⟨⟨37479009531310300006850551367648045830356516272975173259066998,37479009531310300006850551367648045830356516273000953957285842⟩,⟨-22889932225210003527102216006623810505049214605872261630584365,-22889932225210003527102216006623810505049214605846475539188021⟩⟩,
  ⟨⟨84566805074835469890392359665795136636243630399272057735912200,84566805074835469890392359665795136636243630399401535878753250⟩,⟨121381719705828735132196132309283011763066550975407946779191505,121381719705828735132196132309283011763066550975537400464415412⟩⟩,
  ⟨⟨-299750780074938820892870618696196975276591632812947607225200506,-299750780074938820892870618696196975276591632812466394232953526⟩,⟨248451300240902940453703357514742017998730609444749611284910637,248451300240902940453703357514742017998730609445230907769899359⟩⟩,
  ⟨⟨-604236723733589874827210830126948470617931639818156534941066558,-604236723733589874827210830126948470617931639816752563109322821⟩,⟨-595039375217310207796535860555470977619951030889314574994364411,-595039375217310207796535860555470977619951030887910866129977077⟩⟩,
  ⟨⟨974488628275034602578873981907047468197760479003212676092985921,974488628275034602578873981907047468197760479006544524387294622⟩,⟨-1245352185471187400689490389926650304580367250250293562839532824,-1245352185471187400689490389926650304580367250246961894209428518⟩⟩,
  ⟨⟨2210264641720184399458528892806094123089498209837111502924387214,2210264641720184399458528892806094123089498209843682653112047789⟩,⟨1327539728668295680366779456141429382576698545712764835792456056,1327539728668295680366779456141429382576698545719335706635143205⟩⟩,
  ⟨⟨-1489266706352089832437996636617520920431595336759118253573183980,-1489266706352089832437996636617520920431595336748203057615419668⟩,⟨3417085403137856514915335216318419154734627839609709884206031347,3417085403137856514915335216318419154734627839620630210540134859⟩⟩,
  ⟨⟨-4639549619064101962223905076772006585891620777935289384345743994,-4639549619064101962223905076772006585891620777919786185490421580⟩,⟨-1316214008683221051638572465024791207886463407483165695530457535,-1316214008683221051638572465024791207886463407467669095640152811⟩⟩,
  ⟨⟨777718809675506040434076078185698975229654914678180647433936594,777718809675506040434076078185698975229654914697242535293211849⟩,⟨-5562515442501746475711344878311556406629592958595178622871523014,-5562515442501746475711344878311556406629592958576118953188695391⟩⟩,
  ⟨⟨5907328434335825745556963920158289517630770654238313011961097868,5907328434335825745556963920158289517630770654258733059173516545⟩,⟨-10203465802847119,10203465802876741⟩⟩,
  ⟨⟨777718809675506040434076078185698975229654914678180647429832615,777718809675506040434076078185698975229654914697242535297278488⟩,⟨5562515442501746475711344878311556406629592958576118953184627078,5562515442501746475711344878311556406629592958595178622875624720⟩⟩,
  ⟨⟨-4639549619064101962223905076772006585891620777935289384353412110,-4639549619064101962223905076772006585891620777919786185482780945⟩,⟨1316214008683221051638572465024791207886463407467669095632495781,1316214008683221051638572465024791207886463407483165695538109256⟩⟩,
  ⟨⟨-1489266706352089832437996636617520920431595336759118253583555359,-1489266706352089832437996636617520920431595336748203057605045205⟩,⟨-3417085403137856514915335216318419154734627839620630210550512005,-3417085403137856514915335216318419154734627839609709884195662599⟩⟩,
  ⟨⟨2210264641720184399458528892806094123089498209837111502912223146,2210264641720184399458528892806094123089498209843682653124223363⟩,⟨-1327539728668295680366779456141429382576698545719335706647307936,-1327539728668295680366779456141429382576698545712764835780281101⟩⟩,
  ⟨⟨974488628275034602578873981907047468197760479003212676079794002,974488628275034602578873981907047468197760479006544524400488857⟩,⟨1245352185471187400689490389926650304580367250246961894196244270,1245352185471187400689490389926650304580367250250293562852734855⟩⟩,
  ⟨⟨-604236723733589874827210830126948470617931639818156534954757873,-604236723733589874827210830126948470617931639816752563095634221⟩,⟨595039375217310207796535860555470977619951030887910866116293932,595039375217310207796535860555470977619951030889314575008061203⟩⟩,
  ⟨⟨-299750780074938820892870618696196975276591632812947607239093884,-299750780074938820892870618696196975276591632812466394219061477⟩,⟨-248451300240902940453703357514742017998730609445230907783786811,-248451300240902940453703357514742017998730609444749611271012680⟩⟩,
  ⟨⟨84566805074835469890392359665795136636243630399272057721951365,84566805074835469890392359665795136636243630399401535892714124⟩,⟨-121381719705828735132196132309283011763066550975537400478371018,-121381719705828735132196132309283011763066550975407946765225406⟩⟩,
  ⟨⟨37479009531310300006850551367648045830356516272975173245087868,37479009531310300006850551367648045830356516273000953971265088⟩,⟨22889932225210003527102216006623810505049214605846475525214243,22889932225210003527102216006623810505049214605872261644568939⟩⟩,
  ⟨⟨-4512256816278756118456938628002619397688287391310210272584080,-4512256816278756118456938628002619397688287391306728997178791⟩,⟨7917795486482586948753916921160270903681923406437420779267455,7917795486482586948753916921160270903681923406440902381108840⟩⟩,
  ⟨⟨-866025403784438646763723170752936183471402626905300149315147,-866025403784438646763723170752936183471402626905075689766175⟩,⟨-500000000000000000000000000000000000000000000000116242217967,-499999999999999999999999999999999999999999999999892052562895⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩]
lemma coeffBox11_calc (j : Fin 31) : coeffStep phaseBox21 coeffBox10 j = coeffBox11 j := by
  revert j
  decide +kernel
lemma coeffBox11_mem (j : Fin 31) : (coeffBox11 j).Mem ((partialPolynomial 11).coeff j.val) := by
  rw [← coeffBox11_calc, partialPolynomial_succ (by norm_num : 10 < 15)]
  apply coeffStep_mem ⟨10,by norm_num⟩ (partialPolynomial 10) phaseBox21 coeffBox10
  · have hr : residue ⟨10,by norm_num⟩ = (21:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox21_mem
  · exact coeffBox10_mem
def coeffBox12 : Fin 31 → CI :=
  ![⟨⟨-766044443118978035202392650555416673935832457080562096652337,-766044443118978035202392650555416673935832457080236017549845⟩,⟨-642787609686539326322643409907263432907559884205840414350480,-642787609686539326322643409907263432907559884205514082201062⟩⟩,
  ⟨⟨4164960460944895420753505374463989805687536036937630069585979,4164960460944895420753505374463989805687536036942893971542901⟩,⟨-5948179980458170830020430871981224876340636903002152336580431,-5948179980458170830020430871981224876340636902996890023060468⟩⟩,
  ⟨⟨25477211159031679358278123031647999502929370960248315501705463,25477211159031679358278123031647999502929370960290362001457720⟩,⟨12539147570602880986363505153869713185588833690183522327102303,12539147570602880986363505153869713185588833690225570165954082⟩⟩,
  ⟨⟨-19163513165526571608310526597599643507403362702645028136533031,-19163513165526571608310526597599643507403362702416878403368227⟩,⟨76734020298984841702151163516356146062697505998502220494739912,76734020298984841702151163516356146062697505998730385356147211⟩⟩,
  ⟨⟨-175545972265297872977636312095087520787949684318523106819706685,-175545972265297872977636312095087520787949684317597004244411097⟩,⟨3017626026941955946172733161320399232757925021759570412525128,3017626026941955946172733161320399232757925022685587461900545⟩⟩,
  ⟨⟨-104023523936948958656788248009339890290094622406474404712293441,-104023523936948958656788248009339890290094622403506970033646322⟩,⟨-312361451936102397590849479031690449706967037533931724840415957,-312361451936102397590849479031690449706967037530963958312219338⟩⟩,
  ⟨⟨426016600509389744267675357995167981740501768593429106316840020,426016600509389744267675357995167981740501768601202700219568473⟩,⟨-333645564941496505330156441043791850901932563697869088192493758,-333645564941496505330156441043791850901932563690096017775894835⟩⟩,
  ⟨⟨691637758446381399752768983892442473125789657431896307916978934,691637758446381399752768983892442473125789657448915477516976156⟩,⟨404591669239809112237179302448884957676218351285791985628551978,404591669239809112237179302448884957676218351302811343572272978⟩⟩,
  ⟨⟨-136793385495221344071117481140581595312270513033450123604522478,-136793385495221344071117481140581595312270513001840275876863081⟩,⟨1082683256337036005873538115278089101822862201784558741076117848,1082683256337036005873538115278089101822862201816164520142611328⟩⟩,
  ⟨⟨-1325081930669853424216987020725719034212270184125814200847167152,-1325081930669853424216987020725719034212270184075428717067404263⟩,⟨401324516035198882288909637595247763921496262372573659196652356,401324516035198882288909637595247763921496262422974568891847956⟩⟩,
  ⟨⟨-1084398299482169539681976256669389237589600402521795869462639473,-1084398299482169539681976256669389237589600402452045083900697697⟩,⟨-1235938746085208377803587501985608315899680631093981910785557973,-1235938746085208377803587501985608315899680631024247746112040974⟩⟩,
  ⟨⟨752206920120831188962900784972055024446461760496889522806109841,752206920120831188962900784972055024446461760581373173903096310⟩,⟨-1664379109791823342528998810652508607724895010423173937634051990,-1664379109791823342528998810652508607724895010338680626505117385⟩⟩,
  ⟨⟨1892538437523115562971282965244989739504309015782542821407619223,1892538437523115562971282965244989739504309015872603120591642892⟩,⟨-45017160490578568,45017160490614147⟩⟩,
  ⟨⟨752206920120831188962900784972055024446461760496889522788116802,752206920120831188962900784972055024446461760581373173921065928⟩,⟨1664379109791823342528998810652508607724895010338680626487166361,1664379109791823342528998810652508607724895010423173937652062427⟩⟩,
  ⟨⟨-1084398299482169539681976256669389237589600402521795869496492968,-1084398299482169539681976256669389237589600402452045083866871608⟩,⟨1235938746085208377803587501985608315899680631024247746078218979,1235938746085208377803587501985608315899680631093981910819415889⟩⟩,
  ⟨⟨-1325081930669853424216987020725719034212270184125814200893328886,-1325081930669853424216987020725719034212270184075428717021256420⟩,⟨-401324516035198882288909637595247763921496262422974568937992022,-401324516035198882288909637595247763921496262372573659150486766⟩⟩,
  ⟨⟨-136793385495221344071117481140581595312270513033450123659066914,-136793385495221344071117481140581595312270513001840275822318386⟩,⟨-1082683256337036005873538115278089101822862201816164520197144414,-1082683256337036005873538115278089101822862201784558741021561822⟩⟩,
  ⟨⟨691637758446381399752768983892442473125789657431896307857450152,691637758446381399752768983892442473125789657448915477576509361⟩,⟨-404591669239809112237179302448884957676218351302811343631788890,-404591669239809112237179302448884957676218351285791985569005694⟩⟩,
  ⟨⟨426016600509389744267675357995167981740501768593429106254744724,426016600509389744267675357995167981740501768601202700281665515⟩,⟨333645564941496505330156441043791850901932563690096017713815451,333645564941496505330156441043791850901932563697869088254606691⟩⟩,
  ⟨⟨-104023523936948958656788248009339890290094622406474404775519580,-104023523936948958656788248009339890290094622403506969970420793⟩,⟨312361451936102397590849479031690449706967037530963958249009458,312361451936102397590849479031690449706967037533931724903657696⟩⟩,
  ⟨⟨-175545972265297872977636312095087520787949684318523106883352453,-175545972265297872977636312095087520787949684317597004180765943⟩,⟨-3017626026941955946172733161320399232757925022685587525531199,-3017626026941955946172733161320399232757925021759570348864841⟩⟩,
  ⟨⟨-19163513165526571608310526597599643507403362702645028200307351,-19163513165526571608310526597599643507403362702416878339593927⟩,⟨-76734020298984841702151163516356146062697505998730385419907086,-76734020298984841702151163516356146062697505998502220430951193⟩⟩,
  ⟨⟨25477211159031679358278123031647999502929370960248315437899460,25477211159031679358278123031647999502929370960290362065263834⟩,⟨-12539147570602880986363505153869713185588833690225570229745717,-12539147570602880986363505153869713185588833690183522263281852⟩⟩,
  ⟨⟨4164960460944895420753505374463989805687536036937630005773943,4164960460944895420753505374463989805687536036942894035354977⟩,⟨5948179980458170830020430871981224876340636902996889959262847,5948179980458170830020430871981224876340636903002152400406886⟩⟩,
  ⟨⟨-766044443118978035202392650555416673935832457080562160465188,-766044443118978035202392650555416673935832457080235953736992⟩,⟨642787609686539326322643409907263432907559884205514018402637,642787609686539326322643409907263432907559884205840478177725⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩]
lemma coeffBox12_calc (j : Fin 31) : coeffStep phaseBox25 coeffBox11 j = coeffBox12 j := by
  revert j
  decide +kernel
lemma coeffBox12_mem (j : Fin 31) : (coeffBox12 j).Mem ((partialPolynomial 12).coeff j.val) := by
  rw [← coeffBox12_calc, partialPolynomial_succ (by norm_num : 11 < 15)]
  apply coeffStep_mem ⟨11,by norm_num⟩ (partialPolynomial 11) phaseBox25 coeffBox11
  · have hr : residue ⟨11,by norm_num⟩ = (25:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox25_mem
  · exact coeffBox11_mem
def coeffBox13 : Fin 31 → CI :=
  ![⟨⟨642787609686539326322643409907263432907559884205491065819110,642787609686539326322643409907263432907559884205861544029453⟩,⟨-766044443118978035202392650555416673935832457080584961250795,-766044443118978035202392650555416673935832457080214736087377⟩⟩,
  ⟨⟨4416091094220214759615645570870391528468971988835612510009246,4416091094220214759615645570870391528468971988841843879204807⟩,⟨2879385241571816768108218554649462939872416268525783467215086,2879385241571816768108218554649462939872416268532016930941459⟩⟩,
  ⟨⟨-4852014258399629471179137814848997007121321500556737708852509,-4852014258399629471179137814848997007121321500502600336949783⟩,⟨14346895641234315733439653938240966424183929611323643797525692,14346895641234315733439653938240966424183929611377776400408053⟩⟩,
  ⟨⟨-31727777961379653815615348325041371933179400981237586093399075,-31727777961379653815615348325041371933179400980916744051283054⟩,⟨1749821514734294943662978335675793058086768640777548782127838,1749821514734294943662978335675793058086768641098379962637368⟩⟩,
  ⟨⟨-28805504787392218176430281202649973061975816737795699501608560,-28805504787392218176430281202649973061975816736364548566665293⟩,⟨-47555142826359868931612108094023228165484043281812401964669468,-47555142826359868931612108094023228165484043280381136586420562⟩⟩,
  ⟨⟨38003527704491493337728018357871554193765174892411787226043433,38003527704491493337728018357871554193765174897475976250863618⟩,⟨-78824758717538475156132255089099448317175409660546701891908565,-78824758717538475156132255089099448317175409655483030896720717⟩⟩,
  ⟨⟨128616143094540543962752678186432469554501243898892387453858944,128616143094540543962752678186432469554501243913555743786915243⟩,⟨-23160331097517177936387287973125396885482622156852446028342108,-23160331097517177936387287973125396885482622142187816984137108⟩⟩,
  ⟨⟨135080079842867978707321934509760556097818148350092168791020538,135080079842867978707321934509760556097818148385673879172008278⟩,⟨128370152500337347749244349814198661612019152439641516092871830,128370152500337347749244349814198661612019152475221659308327233⟩⟩,
  ⟨⟨-33053304385769711698156588536996006473215450650271644710815224,-33053304385769711698156588536996006473215450576792439279750964⟩,⟨246373352475007136135565765762020338299664420936901061467521013,246373352475007136135565765762020338299664421010385235733328276⟩⟩,
  ⟨⟨-270319617785832458193965297427525996869818937204127834489685805,-270319617785832458193965297427525996869818937073399423482140873⟩,⟨148646823557837187777320225938016696307664561994344572281134593,148646823557837187777320225938016696307664562125049231707191204⟩⟩,
  ⟨⟨-331541858917462464756848424187740650701997535442878878768821570,-331541858917462464756848424187740650701997535240657046632136044⟩,⟨-144955881916550431033039500338312114434337364774863924340469611,-144955881916550431033039500338312114434337364572590550823327969⟩⟩,
  ⟨⟨-103092973137316854546044065091022103532809532332403069480718896,-103092973137316854546044065091022103532809532057877455956093534⟩,⟨-394588641379732142427287198273442573140629317615712047882835767,-394588641379732142427287198273442573140629317341244762082440806⟩⟩,
  ⟨⟨268475094156454000122214067958501732993242889854714963837750484,268475094156454000122214067958501732993242890183582763062357644⟩,⟨-351821482578361582404738399390638238355880602611827497651162635,-351821482578361582404738399390638238355880602282897779271403473⟩⟩,
  ⟨⟨456318655462584440884568309184962263558828010718663895895607726,456318655462584440884568309184962263558828011067922565062493381⟩,⟨-174593696348640465,174593696348688204⟩⟩,
  ⟨⟨268475094156454000122214067958501732993242889854714963767942069,268475094156454000122214067958501732993242890183582763132154454⟩,⟨351821482578361582404738399390638238355880602282897779201647932,351821482578361582404738399390638238355880602611827497721009600⟩⟩,
  ⟨⟨-103092973137316854546044065091022103532809532332403069612542500,-103092973137316854546044065091022103532809532057877455824286853⟩,⟨394588641379732142427287198273442573140629317341244761950665466,394588641379732142427287198273442573140629317615712048014692483⟩⟩,
  ⟨⟨-331541858917462464756848424187740650701997535442878878949523059,-331541858917462464756848424187740650701997535240657046451449356⟩,⟨144955881916550431033039500338312114434337364572590550642669314,144955881916550431033039500338312114434337364774863924521198983⟩⟩,
  ⟨⟨-270319617785832458193965297427525996869818937204127834704465027,-270319617785832458193965297427525996869818937073399423267369981⟩,⟨-148646823557837187777320225938016696307664562125049231921933999,-148646823557837187777320225938016696307664561994344572066327600⟩⟩,
  ⟨⟨-33053304385769711698156588536996006473215450650271644946518807,-33053304385769711698156588536996006473215450576792439044049144⟩,⟨-246373352475007136135565765762020338299664421010385235969000089,-246373352475007136135565765762020338299664420936901061231786965⟩⟩,
  ⟨⟨135080079842867978707321934509760556097818148350092168544072295,135080079842867978707321934509760556097818148385673879418958526⟩,⟨-128370152500337347749244349814198661612019152475221659555245343,-128370152500337347749244349814198661612019152439641515845891651⟩⟩,
  ⟨⟨128616143094540543962752678186432469554501243898892387201666995,128616143094540543962752678186432469554501243913555744039109888⟩,⟨23160331097517177936387287973125396885482622142187816731974540,23160331097517177936387287973125396885482622156852446280566038⟩⟩,
  ⟨⟨38003527704491493337728018357871554193765174892411786971753298,38003527704491493337728018357871554193765174897475976505155540⟩,⟨78824758717538475156132255089099448317175409655483030642459562,78824758717538475156132255089099448317175409660546702146229580⟩⟩,
  ⟨⟨-28805504787392218176430281202649973061975816737795699756608305,-28805504787392218176430281202649973061975816736364548311664771⟩,⟨47555142826359868931612108094023228165484043280381136331449657,47555142826359868931612108094023228165484043281812402219698790⟩⟩,
  ⟨⟨-31727777961379653815615348325041371933179400981237586348597411,-31727777961379653815615348325041371933179400980916743796084486⟩,⟨-1749821514734294943662978335675793058086768641098380217806972,-1749821514734294943662978335675793058086768640777548526900538⟩⟩,
  ⟨⟨-4852014258399629471179137814848997007121321500556737964095461,-4852014258399629471179137814848997007121321500502600081706755⟩,⟨-14346895641234315733439653938240966424183929611377776655622258,-14346895641234315733439653938240966424183929611323643542253924⟩⟩,
  ⟨⟨4416091094220214759615645570870391528468971988835612254758617,4416091094220214759615645570870391528468971988841844134455456⟩,⟨-2879385241571816768108218554649462939872416268532017186163297,-2879385241571816768108218554649462939872416268525783211935644⟩⟩,
  ⟨⟨642787609686539326322643409907263432907559884205490810567554,642787609686539326322643409907263432907559884205861799281011⟩,⟨766044443118978035202392650555416673935832457080214480864638,766044443118978035202392650555416673935832457080585216531170⟩⟩,
  ⟨⟨-255251619,255251619⟩,⟨-255222800,255280438⟩⟩,
  ⟨⟨-255251619,255251619⟩,⟨-255222800,255280438⟩⟩,
  ⟨⟨-255251619,255251619⟩,⟨-255222800,255280438⟩⟩,
  ⟨⟨-255251619,255251619⟩,⟨-255222800,255280438⟩⟩]
lemma coeffBox13_calc (j : Fin 31) : coeffStep phaseBox27 coeffBox12 j = coeffBox13 j := by
  revert j
  decide +kernel
lemma coeffBox13_mem (j : Fin 31) : (coeffBox13 j).Mem ((partialPolynomial 13).coeff j.val) := by
  rw [← coeffBox13_calc, partialPolynomial_succ (by norm_num : 12 < 15)]
  apply coeffStep_mem ⟨12,by norm_num⟩ (partialPolynomial 12) phaseBox27 coeffBox12
  · have hr : residue ⟨12,by norm_num⟩ = (27:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox27_mem
  · exact coeffBox12_mem
def coeffBox14 : Fin 31 → CI :=
  ![⟨⟨642787609686539326322643409907263432907559884205450996833679,642787609686539326322643409907263432907559884205925511237456⟩,⟨766044443118978035202392650555416673935832457080152454279948,766044443118978035202392650555416673935832457080627190072069⟩⟩,
  ⟨⟨-2316911861358276816436919302717675619342037857811904592355163,-2316911861358276816436919302717675619342037857803706628700402⟩,⟨2316911861358276816436919302717675619342037857803752185672144,2316911861358276816436919302717675619342037857811947743171944⟩⟩,
  ⟨⟨-5320233840503559348056640499798215665394454341561169511136765,-5320233840503559348056640499798215665394454341484900550899844⟩,⟨-2010843059532065689344682916953785201566447671125286878603763,-2010843059532065689344682916953785201566447671049008397171332⟩⟩,
  ⟨⟨-3849000747596232886841704603828508967213702772212946019771931,-3849000747596232886841704603828508967213702771724458321926955⟩,⟨-7704824504620151700561164434554927892577748850961087228412744,-7704824504620151700561164434554927892577748850472606080485304⟩⟩,
  ⟨⟨3350618334479143229323154450619169638053167836900476341232371,3350618334479143229323154450619169638053167839265999885604826⟩,⟨-14323388547977786674655271161271114832315840465663052602267255,-14323388547977786674655271161271114832315840463297636048945315⟩⟩,
  ⟨⟨20649689227276910505519285647892239573321723705644426012368686,20649689227276910505519285647892239573321723714749391304555665⟩,⟨-13054432816245680790053223023741599995750160087097180291817853,-13054432816245680790053223023741599995750160077991555679094312⟩⟩,
  ⟨⟨34650920231336140889453197522086290546366560007430250801020899,34650920231336140889453197522086290546366560036212160384630619⟩,⟨9660155070742856944098328839855123822586247826602732959292736,9660155070742856944098328839855123822586247855382469935395477⟩⟩,
  ⟨⟨23129478202423733314021160428172685570569378041712087217341210,23129478202423733314021160428172685570569378118135532952750343⟩,⟨40677611644359167120709705604477237119124201289801032600985812,40677611644359167120709705604477237119124201366228719647835037⟩⟩,
  ⟨⟨-11873014388882054365633557151108253877307628421271330143326997,-11873014388882054365633557151108253877307628247978542810385229⟩,⟨58766445303134472372956339264977712973917686115537060117177540,58766445303134472372956339264977712973917686288821664342281817⟩⟩,
  ⟨⟨-62591132321930049398796132326675493332278272129412017369259849,-62591132321930049398796132326675493332278271789793503143591423⟩,⟨45402446581159540598010074247522168936488176517847320698825791,45402446581159540598010074247522168936488176857496293340483687⟩⟩,
  ⟨⟨-91943885868744270868448469111380909817943368805007762289403883,-91943885868744270868448469111380909817943368224083326984445685⟩,⟨-14271154518609465659180464386073774789042228127769770775875415,-14271154518609465659180464386073774789042227546938673938175168⟩⟩,
  ⟨⟨-63258804321523326560999460015259942968689732093376830127474469,-63258804321523326560999460015259942968689731219515418949094375⟩,⟨-82518319196160990928914593099031920866390976299640431529572296,-82518319196160990928914593099031920866390975425609335955906455⟩⟩,
  ⟨⟨8488329860743371322815627353293936177409191429859269337371577,8488329860743371322815627353293936177409192594301664757692089⟩,⟨-112011451382787227670045121456915246974862834403076913965405324,-112011451382787227670045121456915246974862833238843222101281880⟩⟩,
  ⟨⟨87019238990653242817878034046992465001508058966083036625388139,87019238990653242817878034046992465001508060346348483287452360⟩,⟨-84210457682694112133159822455607856199924578538509339816142758,-84210457682694112133159822455607856199924577158014946726396551⟩⟩,
  ⟨⟨126443841787877377679759560303609900616067107737665094907574481,126443841787877377679759560303609900616067109198302229144863183⟩,⟨-730197075238485835,730197075238554012⟩⟩,
  ⟨⟨87019238990653242817878034046992465001508058966083036333076816,87019238990653242817878034046992465001508060346348483579757299⟩,⟨84210457682694112133159822455607856199924577158014946434159596,84210457682694112133159822455607856199924578538509340108515189⟩⟩,
  ⟨⟨8488329860743371322815627353293936177409191429859268783548881,8488329860743371322815627353293936177409192594301665311505917⟩,⟨112011451382787227670045121456915246974862833238843221547526409,112011451382787227670045121456915246974862834403076914519292247⟩⟩,
  ⟨⟨-63258804321523326560999460015259942968689732093376830890376980,-63258804321523326560999460015259942968689731219515418186200163⟩,⟨82518319196160990928914593099031920866390975425609335193071141,82518319196160990928914593099031920866390976299640432292532231⟩⟩,
  ⟨⟨-91943885868744270868448469111380909817943368805007763201334195,-91943885868744270868448469111380909817943368224083326072520803⟩,⟨14271154518609465659180464386073774789042227546938673026307097,14271154518609465659180464386073774789042228127769771687861638⟩⟩,
  ⟨⟨-62591132321930049398796132326675493332278272129412018375552415,-62591132321930049398796132326675493332278271789793502137299189⟩,⟨-45402446581159540598010074247522168936488176857496294346720396,-45402446581159540598010074247522168936488176517847319692476356⟩⟩,
  ⟨⟨-11873014388882054365633557151108253877307628421271331202429326,-11873014388882054365633557151108253877307628247978541751278194⟩,⟨-58766445303134472372956339264977712973917686288821665401332616,-58766445303134472372956339264977712973917686115537059058019670⟩⟩,
  ⟨⟨23129478202423733314021160428172685570569378041712086132293345,23129478202423733314021160428172685570569378118135534037805116⟩,⟨-40677611644359167120709705604477237119124201366228720732835625,-40677611644359167120709705604477237119124201289801031515883883⟩⟩,
  ⟨⟨34650920231336140889453197522086290546366560007430249704880607,34650920231336140889453197522086290546366560036212161480776782⟩,⟨-9660155070742856944098328839855123822586247855382471031490356,-9660155070742856944098328839855123822586247826602731863100822⟩⟩,
  ⟨⟨20649689227276910505519285647892239573321723705644424912148919,20649689227276910505519285647892239573321723714749392404778766⟩,⟨13054432816245680790053223023741599995750160077991554578920411,13054432816245680790053223023741599995750160087097181392086646⟩⟩,
  ⟨⟨3350618334479143229323154450619169638053167836900475239741897,3350618334479143229323154450619169638053167839266000987096459⟩,⟨14323388547977786674655271161271114832315840463297634947501526,14323388547977786674655271161271114832315840465663053703805610⟩⟩,
  ⟨⟨-3849000747596232886841704603828508967213702772212947121590589,-3849000747596232886841704603828508967213702771724457220108098⟩,⟨7704824504620151700561164434554927892577748850472604978714005,7704824504620151700561164434554927892577748850961088330278944⟩⟩,
  ⟨⟨-5320233840503559348056640499798215665394454341561170613023497,-5320233840503559348056640499798215665394454341484899449013156⟩,⟨2010843059532065689344682916953785201566447671049007295332185,2010843059532065689344682916953785201566447671125287980538045⟩⟩,
  ⟨⟨-2316911861358276816436919302717675619342037857811905694252664,-2316911861358276816436919302717675619342037857803705526802935⟩,⟨-2316911861358276816436919302717675619342037857811948845021805,-2316911861358276816436919302717675619342037857803751083727038⟩⟩,
  ⟨⟨642787609686539326322643409907263432907559884205449894935006,642787609686539326322643409907263432907559884205926613136127⟩,⟨-766044443118978035202392650555416673935832457080628291923111,-766044443118978035202392650555416673935832457080151352333646⟩⟩,
  ⟨⟨-1101898745,1101898745⟩,⟨-1101851114,1101946376⟩⟩,
  ⟨⟨-1101898745,1101898745⟩,⟨-1101851114,1101946376⟩⟩]
lemma coeffBox14_calc (j : Fin 31) : coeffStep phaseBox28 coeffBox13 j = coeffBox14 j := by
  revert j
  decide +kernel
lemma coeffBox14_mem (j : Fin 31) : (coeffBox14 j).Mem ((partialPolynomial 14).coeff j.val) := by
  rw [← coeffBox14_calc, partialPolynomial_succ (by norm_num : 13 < 15)]
  apply coeffStep_mem ⟨13,by norm_num⟩ (partialPolynomial 13) phaseBox28 coeffBox13
  · have hr : residue ⟨13,by norm_num⟩ = (28:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox28_mem
  · exact coeffBox13_mem
def coeffBox15 : Fin 31 → CI :=
  ![⟨⟨-1000000000000000000000000000000000000000000000000357668187167,-999999999999999999999999999999999999999999999999642331844290⟩,⟨-347827970497,367531293270⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999993651414841229,1000000000000000000000000000000000000000000000006301693187769⟩,⟨-1732050807568877293527446341505872366942805253816719729498660,-1732050807568877293527446341505872366942805253804068711800391⟩⟩,
  ⟨⟨499999999999999999999999999999999999999999999937613287990976,500000000000000000000000000000000000000000000062425585717517⟩,⟨866025403784438646763723170752936183471402626842770407098962,866025403784438646763723170752936183471402626967575393807880⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999573590116305701,1000000000000000000000000000000000000000000000426403438220127⟩,⟨-1732050807568877293527446341505872366942805254236801333268779,-1732050807568877293527446341505872366942805253383966294401230⟩⟩,
  ⟨⟨2999999999999999999999999999999999999999999997791129033444059,3000000000000000000000000000000000000000000002208932276369331⟩,⟨1732050807568877293527446341505872366942805251601454706010736,1732050807568877293527446341505872366942805256019259984594612⟩⟩,
  ⟨⟨-9124260591446541,9124350972912394⟩,⟨3464101615137754587054892683011744733885610498496628994962483,3464101615137754587054892683011744733885610516744944595527729⟩⟩,
  ⟨⟨-1500000000000000000000000000000000000000000031045869893592982,-1499999999999999999999999999999999999999999968954126738405517⟩,⟨866025403784438646763723170752936183471402595858574772131640,866025403784438646763723170752936183471402657951911834279273⟩⟩,
  ⟨⟨-89032996610118055,89032972484916236⟩,⟨3464101615137754587054892683011744733885610418590275204646281,3464101615137754587054892683011744733885610596651299102579322⟩⟩,
  ⟨⟨-6000000000000000000000000000000000000000000218766062218846020,-5999999999999999999999999999999999999999999781233989257513064⟩,⟨1732050807568877293527446341505872366942805035039511932291892,1732050807568877293527446341505872366942805472581352851209727⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000000000466375630056524966,-1999999999999999999999999999999999999999999533624532919605091⟩,⟨-3464101615137754587054892683011744733885610973985977696155229,-3464101615137754587054892683011744733885610041255523607013701⟩⟩,
  ⟨⟨-2500000000000000000000000000000000000000000870865308128601628,-2499999999999999999999999999999999999999999129134785455383937⟩,⟨866025403784438646763723170752936183471401756003179879816604,866025403784438646763723170752936183471403497807120074975169⟩⟩,
  ⟨⟨-5000000000000000000000000000000000000000001435800045040879251,-4999999999999999999999999999999999999999998564200033688553946⟩,⟨-5196152422706631880582339024517617100828417197125514277083081,-5196152422706631880582339024517617100828414325736847984876077⟩⟩,
  ⟨⟨1999999999999999999999999999999999999999997896786134701370754,2000000000000000000000000000000000000000002103213821259903458⟩,⟨-6928203230275509174109785366023489467771223118643747514259613,-6928203230275509174109785366023489467771218911839452891656829⟩⟩,
  ⟨⟨2999999999999999999999999999999999999999997247556623475161820,3000000000000000000000000000000000000000002752443452126372415⟩,⟨-1732050807568877293527446341505872366942808006020615696087887,-1732050807568877293527446341505872366942802501600321429033324⟩⟩,
  ⟨⟨1499999999999999999999999999999999999999996770755461509639462,1500000000000000000000000000000000000000003229244711808191594⟩,⟨-6062177826491070527346062195270553284299821617837770478031202,-6062177826491070527346062195270553284299815158834963112515012⟩⟩,
  ⟨⟨11999999999999999999999999999999999999999996594619670830608816,12000000000000000000000000000000000000000003405380459998996233⟩,⟨-3405109190468067794,3405109190468112178⟩⟩,
  ⟨⟨1499999999999999999999999999999999999999996770755460144782377,1500000000000000000000000000000000000000003229244713173045367⟩,⟨6062177826491070527346062195270553284299815158834961747712830,6062177826491070527346062195270553284299821617837771842925403⟩⟩,
  ⟨⟨2999999999999999999999999999999999999999997247556620880919775,3000000000000000000000000000000000000000002752443454720614479⟩,⟨1732050807568877293527446341505872366942802501600318834832012,1732050807568877293527446341505872366942808006020618290383453⟩⟩,
  ⟨⟨1999999999999999999999999999999999999999997896786131110583771,2000000000000000000000000000000000000000002103213824850693222⟩,⟨6928203230275509174109785366023489467771218911839449300915955,6928203230275509174109785366023489467771223118643751105091926⟩⟩,
  ⟨⟨-5000000000000000000000000000000000000000001435800049357225148,-4999999999999999999999999999999999999999998564200029372204250⟩,⟨5196152422706631880582339024517617100828414325736843668574096,5196152422706631880582339024517617100828417197125518593474909⟩⟩,
  ⟨⟨-2500000000000000000000000000000000000000000870865312918035125,-2499999999999999999999999999999999999999999129134780665942151⟩,⟨-866025403784438646763723170752936183471403497807124864370027,-866025403784438646763723170752936183471401756003175090333297⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000000000466375635121079910,-1999999999999999999999999999999999999999999533624527855036240⟩,⟨3464101615137754587054892683011744733885610041255518542493621,3464101615137754587054892683011744733885610973985982760757402⟩⟩,
  ⟨⟨-6000000000000000000000000000000000000000000218766067425323507,-5999999999999999999999999999999999999999999781233984051020872⟩,⟨-1732050807568877293527446341505872366942805472581358057658275,-1732050807568877293527446341505872366942805035039506725770962⟩⟩,
  ⟨⟨-89033001881081646,89032977755889927⟩,⟨-3464101615137754587054892683011744733885610596651304373515719,-3464101615137754587054892683011744733885610418590269933644684⟩⟩,
  ⟨⟨-1500000000000000000000000000000000000000000031045875190131590,-1499999999999999999999999999999999999999999968954121441862869⟩,⟨-866025403784438646763723170752936183471402657951917130788193,-866025403784438646763723170752936183471402595858569475559699⟩⟩,
  ⟨⟨-9124265896733358,9124356278199251⟩,⟨-3464101615137754587054892683011744733885610516744949900782247,-3464101615137754587054892683011744733885610498496623689643227⟩⟩,
  ⟨⟨2999999999999999999999999999999999999999999997791123725616932,3000000000000000000000000000000000000000000002208937584195704⟩,⟨-1732050807568877293527446341505872366942805256019265292387869,-1732050807568877293527446341505872366942805251601449398150530⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999573584807865983,1000000000000000000000000000000000000000000000426408746659388⟩,⟨1732050807568877293527446341505872366942805253383960985995665,1732050807568877293527446341505872366942805254236806641742215⟩⟩,
  ⟨⟨499999999999999999999999999999999999999999999937607979432453,500000000000000000000000000000000000000000000062430894275904⟩,⟨-866025403784438646763723170752936183471402626967580702332263,-866025403784438646763723170752936183471402626842765098506436⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999993646106265121,1000000000000000000000000000000000000000000000006307001763882⟩,⟨1732050807568877293527446341505872366942805253804063403258327,1732050807568877293527446341505872366942805253816725038108817⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000000000362976765098,-999999999999999999999999999999999999999999999999637023266358⟩,⟨-372839837171,353136582460⟩⟩]
lemma coeffBox15_calc (j : Fin 31) : coeffStep phaseBox31 coeffBox14 j = coeffBox15 j := by
  revert j
  decide +kernel
lemma coeffBox15_mem (j : Fin 31) : (coeffBox15 j).Mem ((partialPolynomial 15).coeff j.val) := by
  rw [← coeffBox15_calc, partialPolynomial_succ (by norm_num : 14 < 15)]
  apply coeffStep_mem ⟨14,by norm_num⟩ (partialPolynomial 14) phaseBox31 coeffBox14
  · have hr : residue ⟨14,by norm_num⟩ = (31:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox31_mem
  · exact coeffBox14_mem
lemma atomPolynomial_coeff_mem (j : Fin 31) : (coeffBox15 j).Mem (atomPolynomial.coeff j.val) := by
  simpa only [partialPolynomial_fifteen] using coeffBox15_mem j
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def phaseTable : Fin 36 → CI := ![phaseBox0, phaseBox1, phaseBox2, phaseBox3, phaseBox4, phaseBox5, phaseBox6, phaseBox7, phaseBox8, phaseBox9, phaseBox10, phaseBox11, phaseBox12, phaseBox13, phaseBox14, phaseBox15, phaseBox16, phaseBox17, phaseBox18, phaseBox19, phaseBox20, phaseBox21, phaseBox22, phaseBox23, phaseBox24, phaseBox25, phaseBox26, phaseBox27, phaseBox28, phaseBox29, phaseBox30, phaseBox31, phaseBox32, phaseBox33, phaseBox34, phaseBox35]
lemma phaseTable_mem (j : Fin 36) : (phaseTable j).Mem (phase ((j.val:ℤ):ℂ)) := by
  fin_cases j
  · exact phaseBox0_mem
  · exact phaseBox1_mem
  · exact phaseBox2_mem
  · exact phaseBox3_mem
  · exact phaseBox4_mem
  · exact phaseBox5_mem
  · exact phaseBox6_mem
  · exact phaseBox7_mem
  · exact phaseBox8_mem
  · exact phaseBox9_mem
  · exact phaseBox10_mem
  · exact phaseBox11_mem
  · exact phaseBox12_mem
  · exact phaseBox13_mem
  · exact phaseBox14_mem
  · exact phaseBox15_mem
  · exact phaseBox16_mem
  · exact phaseBox17_mem
  · exact phaseBox18_mem
  · exact phaseBox19_mem
  · exact phaseBox20_mem
  · exact phaseBox21_mem
  · exact phaseBox22_mem
  · exact phaseBox23_mem
  · exact phaseBox24_mem
  · exact phaseBox25_mem
  · exact phaseBox26_mem
  · exact phaseBox27_mem
  · exact phaseBox28_mem
  · exact phaseBox29_mem
  · exact phaseBox30_mem
  · exact phaseBox31_mem
  · exact phaseBox32_mem
  · exact phaseBox33_mem
  · exact phaseBox34_mem
  · exact phaseBox35_mem
def phaseModBox (n : ℤ) : CI := phaseTable ⟨(n%36).toNat, by omega⟩
lemma phaseModBox_mem (n : ℤ) : (phaseModBox n).Mem (phase (n:ℂ)) := by
  rw [phase_int_mod]
  have hh := phaseTable_mem ⟨(n%36).toNat, by omega⟩
  simpa only [phaseModBox, Int.toNat_of_nonneg (show 0 ≤ n%36 by omega)] using hh

def frequencyBox (j : Fin 31) : CI :=
  ((CI.imag.mul (CI.ofReal piBox)).mul (CI.point ((j.val:ℤ)-15))).divNat 18
lemma frequencyBox_mem (j : Fin 31) :
    (frequencyBox j).Mem (Complex.I*Real.pi*(frequency j:ℂ)) := by
  have hh := CI.mem_divNat
    (CI.mem_mul (CI.mem_mul CI.mem_imag (CI.mem_ofReal piBox_mem))
      (CI.mem_point ((j.val:ℤ)-15))) (by norm_num : 0 < (18:ℕ))
  change (((CI.imag.mul (CI.ofReal piBox)).mul (CI.point ((j.val:ℤ)-15))).divNat 18).Mem _
  convert hh using 1
  unfold frequency
  push_cast
  ring

def waveDerivativeBox (k : ℕ) (n : ℤ) : CI := CI.sum (fun j : Fin 31 =>
  ((coeffBox15 j).mul ((frequencyBox j).pow k)).mul (phaseModBox (((j.val:ℤ)-15)*n)))
lemma waveDerivativeBox_mem (k : ℕ) (n : ℤ) :
    (waveDerivativeBox k n).Mem (waveDerivative k (n:ℂ)) := by
  apply CI.mem_sum
  intro j
  rw [wave_phase_integer]
  exact CI.mem_mul (CI.mem_mul (atomPolynomial_coeff_mem j)
    (CI.mem_pow (frequencyBox_mem j) k)) (phaseModBox_mem (((j.val:ℤ)-15)*n))

def jetBox2_0 : CI := ⟨⟨2193245422464301915296553555528033585625259535611342042812338,2193245422464301915296553555528033585625273534273468147240545⟩,⟨-6999331474201310627,6999331474198725149⟩⟩
lemma jetBox2_0_calc : waveDerivativeBox 2 0 = jetBox2_0 := by decide +kernel
lemma jetBox2_0_mem : jetBox2_0.Mem (waveDerivative 2 ((0:ℤ):ℂ)) := by
  rw [← jetBox2_0_calc]
  exact waveDerivativeBox_mem 2 0
def jetBox3_0 : CI := ⟨⟨-18564500046751676991604216254291247962706875647535313484106627,-18564500046751676991604216254291247962706864169406508811803393⟩,⟨-5739065054797930332,5739065054797752994⟩⟩
lemma jetBox3_0_calc : waveDerivativeBox 3 0 = jetBox3_0 := by decide +kernel
lemma jetBox3_0_mem : jetBox3_0.Mem (waveDerivative 3 ((0:ℤ):ℂ)) := by
  rw [← jetBox3_0_calc]
  exact waveDerivativeBox_mem 3 0
def QBox0 : RI := ⟨1096622711232150957648276777764016792812629767805671021406169,1096622711232150957648276777764016792812636767136734073620273⟩
lemma QBox0_calc : jetBox2_0.re.divNat 2 = QBox0 := by decide +kernel
lemma QBox0_mem : QBox0.Mem (Q 0) := by
  rw [← QBox0_calc]
  exact RI.mem_divNat jetBox2_0_mem.1 (by norm_num)
def DBox0 : RI := ⟨-2821465677697672212035232845221131139108557373444433241507405,-2821465677697672212035232845221131139108537620621874649857953⟩
lemma DBox0_calc : jetBox3_0.re.mul ((RI.point 6).mul QBox0).inv = DBox0 := by decide +kernel
lemma DBox0_mem : DBox0.Mem (D 0) := by
  rw [← DBox0_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_0_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox0_mem
  · left; decide +kernel
lemma Q_0_bounds : (157/1000:ℝ) < Q 0 ∧ Q 0 < 40 := by
  have hh := QBox0_mem
  norm_num [RI.Mem, QBox0, scale] at hh
  constructor <;> linarith
lemma D_0_bound : |D 0| < (283/100:ℝ) := by
  have hh := DBox0_mem
  norm_num [RI.Mem, DBox0, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_1 : CI := ⟨⟨649358508339545667567100424194258763912824850100094785805590,649358508339545667567100424194258763912843619077633365447908⟩,⟨-9384489787203357955,9384489786138007847⟩⟩
lemma jetBox2_1_calc : waveDerivativeBox 2 1 = jetBox2_1 := by decide +kernel
lemma jetBox2_1_mem : jetBox2_1.Mem (waveDerivative 2 ((1:ℤ):ℂ)) := by
  rw [← jetBox2_1_calc]
  exact waveDerivativeBox_mem 2 1
def jetBox3_1 : CI := ⟨⟨639966476654750180084024766787116611503084547391679860744363,639966476654750180084024766787116611503099798483826564847070⟩,⟨-7625547005894580539,7625547004847671723⟩⟩
lemma jetBox3_1_calc : waveDerivativeBox 3 1 = jetBox3_1 := by decide +kernel
lemma jetBox3_1_mem : jetBox3_1.Mem (waveDerivative 3 ((1:ℤ):ℂ)) := by
  rw [← jetBox3_1_calc]
  exact waveDerivativeBox_mem 3 1
def QBox1 : RI := ⟨324679254169772833783550212097129381956412425050047392902795,324679254169772833783550212097129381956421809538816682723955⟩
lemma QBox1_calc : jetBox2_1.re.divNat 2 = QBox1 := by decide +kernel
lemma QBox1_mem : QBox1.Mem (Q 1) := by
  rw [← QBox1_calc]
  exact RI.mem_divNat jetBox2_1_mem.1 (by norm_num)
def DBox1 : RI := ⟨328512148751844566334421943996284209005041942242243381121812,328512148751844566334421943996284209005059266315738736466798⟩
lemma DBox1_calc : jetBox3_1.re.mul ((RI.point 6).mul QBox1).inv = DBox1 := by decide +kernel
lemma DBox1_mem : DBox1.Mem (D 1) := by
  rw [← DBox1_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_1_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox1_mem
  · left; decide +kernel
lemma Q_1_bounds : (157/1000:ℝ) < Q 1 ∧ Q 1 < 40 := by
  have hh := QBox1_mem
  norm_num [RI.Mem, QBox1, scale] at hh
  constructor <;> linarith
lemma D_1_bound : |D 1| < (283/100:ℝ) := by
  have hh := DBox1_mem
  norm_num [RI.Mem, DBox1, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_3 : CI := ⟨⟨314935873091926165719798041528741690796860352768042068448118,314935873091926165719798041528741690796877767398780082367638⟩,⟨-8707279535569115420,8707279520646445484⟩⟩
lemma jetBox2_3_calc : waveDerivativeBox 2 3 = jetBox2_3 := by decide +kernel
lemma jetBox2_3_mem : jetBox2_3.Mem (waveDerivative 2 ((3:ℤ):ℂ)) := by
  rw [← jetBox2_3_calc]
  exact waveDerivativeBox_mem 2 3
def jetBox3_3 : CI := ⟨⟨-1014910349844130235681633870102975669842297425304771309994680,-1014910349844130235681633870102975669842283153998726586069992⟩,⟨-7135672221752091992,7135672275674907079⟩⟩
lemma jetBox3_3_calc : waveDerivativeBox 3 3 = jetBox3_3 := by decide +kernel
lemma jetBox3_3_mem : jetBox3_3.Mem (waveDerivative 3 ((3:ℤ):ℂ)) := by
  rw [← jetBox3_3_calc]
  exact waveDerivativeBox_mem 3 3
def QBox3 : RI := ⟨157467936545963082859899020764370845398430176384021034224059,157467936545963082859899020764370845398438883699390041183820⟩
lemma QBox3_calc : jetBox2_3.re.divNat 2 = QBox3 := by decide +kernel
lemma QBox3_mem : QBox3.Mem (Q 3) := by
  rw [← QBox3_calc]
  exact RI.mem_divNat jetBox2_3_mem.1 (by norm_num)
def DBox3 : RI := ⟨-1074197888689855660750076301760101438086369445867264880330882,-1074197888689855660750076301760101438086294942250526538305496⟩
lemma DBox3_calc : jetBox3_3.re.mul ((RI.point 6).mul QBox3).inv = DBox3 := by decide +kernel
lemma DBox3_mem : DBox3.Mem (D 3) := by
  rw [← DBox3_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_3_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox3_mem
  · left; decide +kernel
lemma Q_3_bounds : (157/1000:ℝ) < Q 3 ∧ Q 3 < 40 := by
  have hh := QBox3_mem
  norm_num [RI.Mem, QBox3, scale] at hh
  constructor <;> linarith
lemma D_3_bound : |D 3| < (283/100:ℝ) := by
  have hh := DBox3_mem
  norm_num [RI.Mem, DBox3, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_4 : CI := ⟨⟨480190930161026078211119768145913141800720940178075083063726,480190930161026078211119768145913141800738985786865741678330⟩,⟨-9022785599708981683,9022785611075412461⟩⟩
lemma jetBox2_4_calc : waveDerivativeBox 2 4 = jetBox2_4 := by decide +kernel
lemma jetBox2_4_mem : jetBox2_4.Mem (waveDerivative 2 ((4:ℤ):ℂ)) := by
  rw [← jetBox2_4_calc]
  exact waveDerivativeBox_mem 2 4
def jetBox3_4 : CI := ⟨⟨2821037415057641454037448174285971970813200215885054810691223,2821037415057641454037448174285971970813214970229555343141501⟩,⟨-7377190765466621317,7377190749811915498⟩⟩
lemma jetBox3_4_calc : waveDerivativeBox 3 4 = jetBox3_4 := by decide +kernel
lemma jetBox3_4_mem : jetBox3_4.Mem (waveDerivative 3 ((4:ℤ):ℂ)) := by
  rw [← jetBox3_4_calc]
  exact waveDerivativeBox_mem 3 4
def QBox4 : RI := ⟨240095465080513039105559884072956570900360470089037541531863,240095465080513039105559884072956570900369492893432870839166⟩
lemma QBox4_calc : jetBox2_4.re.divNat 2 = QBox4 := by decide +kernel
lemma QBox4_mem : QBox4.Mem (Q 4) := by
  rw [← QBox4_calc]
  exact RI.mem_divNat jetBox2_4_mem.1 (by norm_num)
def DBox4 : RI := ⟨1958274815194615409462416280349205188070741451787576794058652,1958274815194615409462416280349205188070825285890898180544800⟩
lemma DBox4_calc : jetBox3_4.re.mul ((RI.point 6).mul QBox4).inv = DBox4 := by decide +kernel
lemma DBox4_mem : DBox4.Mem (D 4) := by
  rw [← DBox4_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_4_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox4_mem
  · left; decide +kernel
lemma Q_4_bounds : (157/1000:ℝ) < Q 4 ∧ Q 4 < 40 := by
  have hh := QBox4_mem
  norm_num [RI.Mem, QBox4, scale] at hh
  constructor <;> linarith
lemma D_4_bound : |D 4| < (283/100:ℝ) := by
  have hh := DBox4_mem
  norm_num [RI.Mem, DBox4, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_7 : CI := ⟨⟨3189148019972792007764637656494857305488305163218904078244812,3189148019972792007764637656494857305488323055140130853335833⟩,⟨-8946107184572060955,8946107179335551303⟩⟩
lemma jetBox2_7_calc : waveDerivativeBox 2 7 = jetBox2_7 := by decide +kernel
lemma jetBox2_7_mem : jetBox2_7.Mem (waveDerivative 2 ((7:ℤ):ℂ)) := by
  rw [← jetBox2_7_calc]
  exact waveDerivativeBox_mem 2 7
def jetBox3_7 : CI := ⟨⟨-1382299550539964033879229599493438562522051079640409546599351,-1382299550539964033879229599493438562522036475971189370307881⟩,⟨-7301729767200386216,7301729769468893611⟩⟩
lemma jetBox3_7_calc : waveDerivativeBox 3 7 = jetBox3_7 := by decide +kernel
lemma jetBox3_7_mem : jetBox3_7.Mem (waveDerivative 3 ((7:ℤ):ℂ)) := by
  rw [← jetBox3_7_calc]
  exact waveDerivativeBox_mem 3 7
def QBox7 : RI := ⟨1594574009986396003882318828247428652744152581609452039122406,1594574009986396003882318828247428652744161527570065426667917⟩
lemma QBox7_calc : jetBox2_7.re.divNat 2 = QBox7 := by decide +kernel
lemma QBox7_mem : QBox7.Mem (Q 7) := by
  rw [← QBox7_calc]
  exact RI.mem_divNat jetBox2_7_mem.1 (by norm_num)
def DBox7 : RI := ⟨-144479501723029361026896582559914730386716021226816443856874,-144479501723029361026896582559914730386713684268620369124310⟩
lemma DBox7_calc : jetBox3_7.re.mul ((RI.point 6).mul QBox7).inv = DBox7 := by decide +kernel
lemma DBox7_mem : DBox7.Mem (D 7) := by
  rw [← DBox7_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_7_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox7_mem
  · left; decide +kernel
lemma Q_7_bounds : (157/1000:ℝ) < Q 7 ∧ Q 7 < 40 := by
  have hh := QBox7_mem
  norm_num [RI.Mem, QBox7, scale] at hh
  constructor <;> linarith
lemma D_7_bound : |D 7| < (283/100:ℝ) := by
  have hh := DBox7_mem
  norm_num [RI.Mem, DBox7, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_9 : CI := ⟨⟨4386490844928603830593107111056067171250526070359086629539213,4386490844928603830593107111056067171250540069410481046659986⟩,⟨-6999139762929181309,6999139749324919077⟩⟩
lemma jetBox2_9_calc : waveDerivativeBox 2 9 = jetBox2_9 := by decide +kernel
lemma jetBox2_9_mem : jetBox2_9.Mem (waveDerivative 2 ((9:ℤ):ℂ)) := by
  rw [← jetBox2_9_calc]
  exact waveDerivativeBox_mem 2 9
def jetBox3_9 : CI := ⟨⟨6179663307388343146755102523626297746929090687276536865680881,6179663307388343146755102523626297746929102165152230001774040⟩,⟨-5739196860913024693,5739196877860715941⟩⟩
lemma jetBox3_9_calc : waveDerivativeBox 3 9 = jetBox3_9 := by decide +kernel
lemma jetBox3_9_mem : jetBox3_9.Mem (waveDerivative 3 ((9:ℤ):ℂ)) := by
  rw [← jetBox3_9_calc]
  exact waveDerivativeBox_mem 3 9
def QBox9 : RI := ⟨2193245422464301915296553555528033585625263035179543314769606,2193245422464301915296553555528033585625270034705240523329994⟩
lemma QBox9_calc : jetBox2_9.re.divNat 2 = QBox9 := by decide +kernel
lemma QBox9_mem : QBox9.Mem (Q 9) := by
  rw [← QBox9_calc]
  exact RI.mem_divNat jetBox2_9_mem.1 (by norm_num)
def DBox9 : RI := ⟨469598100611783043885383549212716193991642259249781619427619,469598100611783043885383549212716193991644630139606133123372⟩
lemma DBox9_calc : jetBox3_9.re.mul ((RI.point 6).mul QBox9).inv = DBox9 := by decide +kernel
lemma DBox9_mem : DBox9.Mem (D 9) := by
  rw [← DBox9_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_9_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox9_mem
  · left; decide +kernel
lemma Q_9_bounds : (157/1000:ℝ) < Q 9 ∧ Q 9 < 40 := by
  have hh := QBox9_mem
  norm_num [RI.Mem, QBox9, scale] at hh
  constructor <;> linarith
lemma D_9_bound : |D 9| < (283/100:ℝ) := by
  have hh := DBox9_mem
  norm_num [RI.Mem, DBox9, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_12 : CI := ⟨⟨2193245422464301915296553555528033585625257827702944738164265,2193245422464301915296553555528033585625275242181781766130093⟩,⟨-8707354858304197389,8707354880361310085⟩⟩
lemma jetBox2_12_calc : waveDerivativeBox 2 12 = jetBox2_12 := by decide +kernel
lemma jetBox2_12_mem : jetBox2_12.Mem (waveDerivative 2 ((12:ℤ):ℂ)) := by
  rw [← jetBox2_12_calc]
  exact waveDerivativeBox_mem 2 12
def jetBox3_12 : CI := ⟨⟨-9282250023375838495802108127145623981353442089922621766704147,-9282250023375838495802108127145623981353427818548128082380784⟩,⟨-7135636939508369437,7135637012310946188⟩⟩
lemma jetBox3_12_calc : waveDerivativeBox 3 12 = jetBox3_12 := by decide +kernel
lemma jetBox3_12_mem : jetBox3_12.Mem (waveDerivative 3 ((12:ℤ):ℂ)) := by
  rw [← jetBox3_12_calc]
  exact waveDerivativeBox_mem 3 12
def QBox12 : RI := ⟨1096622711232150957648276777764016792812628913851472369082132,1096622711232150957648276777764016792812637621090890883065047⟩
lemma QBox12_calc : jetBox2_12.re.divNat 2 = QBox12 := by decide +kernel
lemma QBox12_mem : QBox12.Mem (Q 12) := by
  rw [← QBox12_calc]
  exact RI.mem_divNat jetBox2_12_mem.1 (by norm_num)
def DBox12 : RI := ⟨-1410732838848836106017616422610565569554280433655814469824868,-1410732838848836106017616422610565569554267063377368789475445⟩
lemma DBox12_calc : jetBox3_12.re.mul ((RI.point 6).mul QBox12).inv = DBox12 := by decide +kernel
lemma DBox12_mem : DBox12.Mem (D 12) := by
  rw [← DBox12_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_12_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox12_mem
  · left; decide +kernel
lemma Q_12_bounds : (157/1000:ℝ) < Q 12 ∧ Q 12 < 40 := by
  have hh := QBox12_mem
  norm_num [RI.Mem, QBox12, scale] at hh
  constructor <;> linarith
lemma D_12_bound : |D 12| < (283/100:ℝ) := by
  have hh := DBox12_mem
  norm_num [RI.Mem, DBox12, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_13 : CI := ⟨⟨2807621397887934342703697530467294183654949971789532816313407,2807621397887934342703697530467294183654968017377691935889251⟩,⟨-9022795908507912539,9022795903898093804⟩⟩
lemma jetBox2_13_calc : waveDerivativeBox 2 13 = jetBox2_13 := by decide +kernel
lemma jetBox2_13_mem : jetBox2_13.Mem (waveDerivative 2 ((13:ℤ):ℂ)) := by
  rw [← jetBox2_13_calc]
  exact waveDerivativeBox_mem 2 13
def jetBox3_13 : CI := ⟨⟨16063736884637908466488652459875696207303396032822641395711849,16063736884637908466488652459875696207303410787163987127954303⟩,⟨-7377192311139094782,7377192284763907304⟩⟩
lemma jetBox3_13_calc : waveDerivativeBox 3 13 = jetBox3_13 := by decide +kernel
lemma jetBox3_13_mem : jetBox3_13.Mem (waveDerivative 3 ((13:ℤ):ℂ)) := by
  rw [← jetBox3_13_calc]
  exact waveDerivativeBox_mem 3 13
def QBox13 : RI := ⟨1403810698943967171351848765233647091827474985894766408156703,1403810698943967171351848765233647091827484008688845967944626⟩
lemma QBox13_calc : jetBox2_13.re.divNat 2 = QBox13 := by decide +kernel
lemma QBox13_mem : QBox13.Mem (Q 13) := by
  rw [← QBox13_calc]
  exact RI.mem_divNat jetBox2_13_mem.1 (by norm_num)
def DBox13 : RI := ⟨1907158481401378911137652754194682428075739824095418915998981,1907158481401378911137652754194682428075753833787153364714690⟩
lemma DBox13_calc : jetBox3_13.re.mul ((RI.point 6).mul QBox13).inv = DBox13 := by decide +kernel
lemma DBox13_mem : DBox13.Mem (D 13) := by
  rw [← DBox13_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_13_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox13_mem
  · left; decide +kernel
lemma Q_13_bounds : (157/1000:ℝ) < Q 13 ∧ Q 13 < 40 := by
  have hh := QBox13_mem
  norm_num [RI.Mem, QBox13, scale] at hh
  constructor <;> linarith
lemma D_13_bound : |D 13| < (283/100:ℝ) := by
  have hh := DBox13_mem
  norm_num [RI.Mem, DBox13, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_16 : CI := ⟨⟨33007531783833052762588798763964826898017254795610847195476874,33007531783833052762588798763964826898017272687668020675686737⟩,⟨-8946039095198659698,8946039053156332177⟩⟩
lemma jetBox2_16_calc : waveDerivativeBox 2 16 = jetBox2_16 := by decide +kernel
lemma jetBox2_16_mem : jetBox2_16.Mem (waveDerivative 2 ((16:ℤ):ℂ)) := by
  rw [← jetBox2_16_calc]
  exact waveDerivativeBox_mem 2 16
def jetBox3_16 : CI := ⟨⟨34108203020399732998460324303738196235955754478236087890457408,34108203020399732998460324303738196235955769081806548159520529⟩,⟨-7301779014900085682,7301778947873190120⟩⟩
lemma jetBox3_16_calc : waveDerivativeBox 3 16 = jetBox3_16 := by decide +kernel
lemma jetBox3_16_mem : jetBox3_16.Mem (waveDerivative 3 ((16:ℤ):ℂ)) := by
  rw [← jetBox3_16_calc]
  exact waveDerivativeBox_mem 3 16
def QBox16 : RI := ⟨16503765891916526381294399381982413449008627397805423597738437,16503765891916526381294399381982413449008636343834010337843369⟩
lemma QBox16_calc : jetBox2_16.re.divNat 2 = QBox16 := by decide +kernel
lemma QBox16_mem : QBox16.Mem (Q 16) := by
  rw [← QBox16_calc]
  exact RI.mem_divNat jetBox2_16_mem.1 (by norm_num)
def DBox16 : RI := ⟨344448687689171438118652015972695976450937488262806548151181,344448687689171438118652015972695976450937822451757900078321⟩
lemma DBox16_calc : jetBox3_16.re.mul ((RI.point 6).mul QBox16).inv = DBox16 := by decide +kernel
lemma DBox16_mem : DBox16.Mem (D 16) := by
  rw [← DBox16_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_16_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox16_mem
  · left; decide +kernel
lemma Q_16_bounds : (157/1000:ℝ) < Q 16 ∧ Q 16 < 40 := by
  have hh := QBox16_mem
  norm_num [RI.Mem, QBox16, scale] at hh
  constructor <;> linarith
lemma D_16_bound : |D 16| < (283/100:ℝ) := by
  have hh := DBox16_mem
  norm_num [RI.Mem, DBox16, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_19 : CI := ⟨⟨41594368450902491745324397900324124587329585672093445575455224,41594368450902491745324397900324124587329604441070992504609025⟩,⟨-9384489826205149675,9384489757909251186⟩⟩
lemma jetBox2_19_calc : waveDerivativeBox 2 19 = jetBox2_19 := by decide +kernel
lemma jetBox2_19_mem : jetBox2_19.Mem (waveDerivative 2 ((19:ℤ):ℂ)) := by
  rw [← jetBox2_19_calc]
  exact waveDerivativeBox_mem 2 19
def jetBox3_19 : CI := ⟨⟨-32819491150273111802401255112050382324380964413390713987725980,-32819491150273111802401255112050382324380949162298530836575429⟩,⟨-7625546992712991152,7625547046600646651⟩⟩
lemma jetBox3_19_calc : waveDerivativeBox 3 19 = jetBox3_19 := by decide +kernel
lemma jetBox3_19_mem : jetBox3_19.Mem (waveDerivative 3 ((19:ℤ):ℂ)) := by
  rw [← jetBox3_19_calc]
  exact waveDerivativeBox_mem 3 19
def QBox19 : RI := ⟨20797184225451245872662198950162062293664792836046722787727612,20797184225451245872662198950162062293664802220535496252304513⟩
lemma QBox19_calc : jetBox2_19.re.divNat 2 = QBox19 := by decide +kernel
lemma QBox19_mem : QBox19.Mem (Q 19) := by
  rw [← QBox19_calc]
  exact RI.mem_divNat jetBox2_19_mem.1 (by norm_num)
def DBox19 : RI := ⟨-263012296877102942861247435249124951652992134611952558172030,-263012296877102942861247435249124951652991893709886672401469⟩
lemma DBox19_calc : jetBox3_19.re.mul ((RI.point 6).mul QBox19).inv = DBox19 := by decide +kernel
lemma DBox19_mem : DBox19.Mem (D 19) := by
  rw [← DBox19_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_19_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox19_mem
  · left; decide +kernel
lemma Q_19_bounds : (157/1000:ℝ) < Q 19 ∧ Q 19 < 40 := by
  have hh := QBox19_mem
  norm_num [RI.Mem, QBox19, scale] at hh
  constructor <;> linarith
lemma D_19_bound : |D 19| < (283/100:ℝ) := by
  have hh := DBox19_mem
  norm_num [RI.Mem, DBox19, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_21 : CI := ⟨⟨61095935955908527462583701513256198706710585210988786004672484,61095935955908527462583701513256198706710602625619514804300734⟩,⟨-8707279582232183985,8707279467511139628⟩⟩
lemma jetBox2_21_calc : waveDerivativeBox 2 21 = jetBox2_21 := by decide +kernel
lemma jetBox2_21_mem : jetBox2_21.Mem (waveDerivative 2 ((21:ℤ):ℂ)) := by
  rw [← jetBox2_21_calc]
  exact waveDerivativeBox_mem 2 21
def jetBox3_21 : CI := ⟨⟨123010196371355150466223626398302605139058856838234045349168451,123010196371355150466223626398302605139058871109540066707038290⟩,⟨-7135672310732575004,7135672161010809294⟩⟩
lemma jetBox3_21_calc : waveDerivativeBox 3 21 = jetBox3_21 := by decide +kernel
lemma jetBox3_21_mem : jetBox3_21.Mem (waveDerivative 3 ((21:ℤ):ℂ)) := by
  rw [← jetBox3_21_calc]
  exact waveDerivativeBox_mem 3 21
def QBox21 : RI := ⟨30547967977954263731291850756628099353355292605494393002336242,30547967977954263731291850756628099353355301312809757402150368⟩
lemma QBox21_calc : jetBox2_21.re.divNat 2 = QBox21 := by decide +kernel
lemma QBox21_mem : QBox21.Mem (Q 21) := by
  rw [← QBox21_calc]
  exact RI.mem_divNat jetBox2_21_mem.1 (by norm_num)
def DBox21 : RI := ⟨671131363304473916173614466728511275356539559902564587441891,671131363304473916173614466728511275356539829062969650231253⟩
lemma DBox21_calc : jetBox3_21.re.mul ((RI.point 6).mul QBox21).inv = DBox21 := by decide +kernel
lemma DBox21_mem : DBox21.Mem (D 21) := by
  rw [← DBox21_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_21_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox21_mem
  · left; decide +kernel
lemma Q_21_bounds : (157/1000:ℝ) < Q 21 ∧ Q 21 < 40 := by
  have hh := QBox21_mem
  norm_num [RI.Mem, QBox21, scale] at hh
  constructor <;> linarith
lemma D_21_bound : |D 21| < (283/100:ℝ) := by
  have hh := DBox21_mem
  norm_num [RI.Mem, DBox21, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_25 : CI := ⟨⟨29914105240374937967757202440552063373006499439127337250121405,29914105240374937967757202440552063373006517331048559738158075⟩,⟨-8946107202121091217,8946107153004074020⟩⟩
lemma jetBox2_25_calc : waveDerivativeBox 2 25 = jetBox2_25 := by decide +kernel
lemma jetBox2_25_mem : jetBox2_25.Mem (waveDerivative 2 ((25:ℤ):ℂ)) := by
  rw [← jetBox2_25_calc]
  exact waveDerivativeBox_mem 2 25
def jetBox3_25 : CI := ⟨⟨-99387107842092179114509517405599866691407272393792300141857654,-99387107842092179114509517405599866691407257790123109234565532⟩,⟨-7301729678326190191,7301729841514152467⟩⟩
lemma jetBox3_25_calc : waveDerivativeBox 3 25 = jetBox3_25 := by decide +kernel
lemma jetBox3_25_mem : jetBox3_25.Mem (waveDerivative 3 ((25:ℤ):ℂ)) := by
  rw [← jetBox3_25_calc]
  exact waveDerivativeBox_mem 3 25
def QBox25 : RI := ⟨14957052620187468983878601220276031686503249719563668625060702,14957052620187468983878601220276031686503258665524279869079038⟩
lemma QBox25_calc : jetBox2_25.re.divNat 2 = QBox25 := by decide +kernel
lemma QBox25_mem : QBox25.Mem (Q 25) := by
  rw [← QBox25_calc]
  exact RI.mem_divNat jetBox2_25_mem.1 (by norm_num)
def DBox25 : RI := ⟨-1107472066476851987530274715096997578953247529853022359790164,-1107472066476851987530274715096997578953246704734152800617070⟩
lemma DBox25_calc : jetBox3_25.re.mul ((RI.point 6).mul QBox25).inv = DBox25 := by decide +kernel
lemma DBox25_mem : DBox25.Mem (D 25) := by
  rw [← DBox25_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_25_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox25_mem
  · left; decide +kernel
lemma Q_25_bounds : (157/1000:ℝ) < Q 25 ∧ Q 25 < 40 := by
  have hh := QBox25_mem
  norm_num [RI.Mem, QBox25, scale] at hh
  constructor <;> linarith
lemma D_25_bound : |D 25| < (283/100:ℝ) := by
  have hh := DBox25_mem
  norm_num [RI.Mem, DBox25, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_27 : CI := ⟨⟨4386490844928603830593107111056067171250526070358973263547709,4386490844928603830593107111056067171250540069410367680668482⟩,⟨-6999139762929185781,6999139749324914605⟩⟩
lemma jetBox2_27_calc : waveDerivativeBox 2 27 = jetBox2_27 := by decide +kernel
lemma jetBox2_27_mem : jetBox2_27.Mem (waveDerivative 2 ((27:ℤ):ℂ)) := by
  rw [← jetBox2_27_calc]
  exact waveDerivativeBox_mem 2 27
def jetBox3_27 : CI := ⟨⟨-16787949048389301427671797526078439439904456398564410022812338,-16787949048389301427671797526078439439904444920688716886719179⟩,⟨-5739196842056526685,5739196896717213949⟩⟩
lemma jetBox3_27_calc : waveDerivativeBox 3 27 = jetBox3_27 := by decide +kernel
lemma jetBox3_27_mem : jetBox3_27.Mem (waveDerivative 3 ((27:ℤ):ℂ)) := by
  rw [← jetBox3_27_calc]
  exact waveDerivativeBox_mem 3 27
def QBox27 : RI := ⟨2193245422464301915296553555528033585625263035179486631773854,2193245422464301915296553555528033585625270034705183840334242⟩
lemma QBox27_calc : jetBox2_27.re.divNat 2 = QBox27 := by decide +kernel
lemma QBox27_mem : QBox27.Mem (Q 27) := by
  rw [← QBox27_calc]
  exact RI.mem_divNat jetBox2_27_mem.1 (by norm_num)
def DBox27 : RI := ⟨-1275731151382546533038307219275896519451230915638914889554237,-1275731151382546533038307219275896519451225972055242963562159⟩
lemma DBox27_calc : jetBox3_27.re.mul ((RI.point 6).mul QBox27).inv = DBox27 := by decide +kernel
lemma DBox27_mem : DBox27.Mem (D 27) := by
  rw [← DBox27_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_27_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox27_mem
  · left; decide +kernel
lemma Q_27_bounds : (157/1000:ℝ) < Q 27 ∧ Q 27 < 40 := by
  have hh := QBox27_mem
  norm_num [RI.Mem, QBox27, scale] at hh
  constructor <;> linarith
lemma D_27_bound : |D 27| < (283/100:ℝ) := by
  have hh := DBox27_mem
  norm_num [RI.Mem, DBox27, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_28 : CI := ⟨⟨5990694890363355634538045467393864501436794539821908259433758,5990694890363355634538045467393864501436813308861036652393856⟩,⟨-9384458612011244997,9384458614328773767⟩⟩
lemma jetBox2_28_calc : waveDerivativeBox 2 28 = jetBox2_28 := by decide +kernel
lemma jetBox2_28_mem : jetBox2_28.Mem (waveDerivative 2 ((28:ℤ):ℂ)) := by
  rw [← jetBox2_28_calc]
  exact waveDerivativeBox_mem 2 28
def jetBox3_28 : CI := ⟨⟨34676688316299093943689918788527788220814664076904630179661918,34676688316299093943689918788527788220814679327997751505498025⟩,⟨-7625545977313401335,7625545909352621894⟩⟩
lemma jetBox3_28_calc : waveDerivativeBox 3 28 = jetBox3_28 := by decide +kernel
lemma jetBox3_28_mem : jetBox3_28.Mem (waveDerivative 3 ((28:ℤ):ℂ)) := by
  rw [← jetBox3_28_calc]
  exact waveDerivativeBox_mem 3 28
def QBox28 : RI := ⟨2995347445181677817269022733696932250718397269910954129716879,2995347445181677817269022733696932250718406654430518326196929⟩
lemma QBox28_calc : jetBox2_28.re.divNat 2 = QBox28 := by decide +kernel
lemma QBox28_mem : QBox28.Mem (Q 28) := by
  rw [← QBox28_calc]
  exact RI.mem_divNat jetBox2_28_mem.1 (by norm_num)
def DBox28 : RI := ⟨1929475013662721470471780971509795544141096774500119863158648,1929475013662721470471780971509795544141103668206190962350573⟩
lemma DBox28_calc : jetBox3_28.re.mul ((RI.point 6).mul QBox28).inv = DBox28 := by decide +kernel
lemma DBox28_mem : DBox28.Mem (D 28) := by
  rw [← DBox28_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_28_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox28_mem
  · left; decide +kernel
lemma Q_28_bounds : (157/1000:ℝ) < Q 28 ∧ Q 28 < 40 := by
  have hh := QBox28_mem
  norm_num [RI.Mem, QBox28, scale] at hh
  constructor <;> linarith
lemma D_28_bound : |D 28| < (283/100:ℝ) := by
  have hh := DBox28_mem
  norm_num [RI.Mem, DBox28, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
def jetBox2_31 : CI := ⟨⟨79759068799952036170234820045985819951626970713036857794209793,79759068799952036170234820045985819951626988758625018626937983⟩,⟨-9022795974534550414,9022795843574071670⟩⟩
lemma jetBox2_31_calc : waveDerivativeBox 2 31 = jetBox2_31 := by decide +kernel
lemma jetBox2_31_mem : jetBox2_31.Mem (waveDerivative 2 ((31:ℤ):ℂ)) := by
  rw [← jetBox2_31_calc]
  exact waveDerivativeBox_mem 2 31
def jetBox3_31 : CI := ⟨⟨116885195181612596304217324890480874759503762697504943840671500,116885195181612596304217324890480874759503777451846306500043617⟩,⟨-7377192398215642046,7377192206297317323⟩⟩
lemma jetBox3_31_calc : waveDerivativeBox 3 31 = jetBox3_31 := by decide +kernel
lemma jetBox3_31_mem : jetBox3_31.Mem (waveDerivative 3 ((31:ℤ):ℂ)) := by
  rw [← jetBox3_31_calc]
  exact waveDerivativeBox_mem 3 31
def QBox31 : RI := ⟨39879534399976018085117410022992909975813485356518428897104896,39879534399976018085117410022992909975813494379312509313468992⟩
lemma QBox31_calc : jetBox2_31.re.divNat 2 = QBox31 := by decide +kernel
lemma QBox31_mem : QBox31.Mem (Q 31) := by
  rw [← QBox31_calc]
  exact RI.mem_divNat jetBox2_31_mem.1 (by norm_num)
def DBox31 : RI := ⟨488492811079906047675729539809841112101533963618228618120530,488492811079906047675729539809841112101534135802458981613029⟩
lemma DBox31_calc : jetBox3_31.re.mul ((RI.point 6).mul QBox31).inv = DBox31 := by decide +kernel
lemma DBox31_mem : DBox31.Mem (D 31) := by
  rw [← DBox31_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_31_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox31_mem
  · left; decide +kernel
lemma Q_31_bounds : (157/1000:ℝ) < Q 31 ∧ Q 31 < 40 := by
  have hh := QBox31_mem
  norm_num [RI.Mem, QBox31, scale] at hh
  constructor <;> linarith
lemma D_31_bound : |D 31| < (283/100:ℝ) := by
  have hh := DBox31_mem
  norm_num [RI.Mem, DBox31, scale] at hh
  rw [abs_lt]
  constructor <;> linarith
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex

def restPolynomial (a : Fin 15) : Polynomial ℂ :=
  ∏ r ∈ Finset.univ.erase a, atomFactor r

lemma atomPolynomial_factor (a : Fin 15) :
    atomPolynomial = atomFactor a * restPolynomial a := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm

lemma restPolynomial_degree (a : Fin 15) : (restPolynomial a).natDegree ≤ 28 := by
  unfold restPolynomial
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  calc
    ∑ r ∈ Finset.univ.erase a, (atomFactor r).natDegree ≤
        ∑ r ∈ Finset.univ.erase a, 2 := Finset.sum_le_sum (fun r _ => atomFactor_degree r)
    _ = 28 := by simp

lemma restPolynomial_coeff (a : Fin 15) (n : ℕ) :
    (restPolynomial a).coeff n = phase (-(residue a:ℂ)) *
      (-(atomPolynomial.coeff n) +
        (if n=0 then 0 else 2*(restPolynomial a).coeff (n-1)) -
        (if n<2 then 0 else phase (-(residue a:ℂ))*(restPolynomial a).coeff (n-2))) := by
  have hh := coeff_atom_mul a (restPolynomial a) n
  rw [← atomPolynomial_factor] at hh
  have he : -(atomPolynomial.coeff n) +
      (if n=0 then 0 else 2*(restPolynomial a).coeff (n-1)) -
      (if n<2 then 0 else phase (-(residue a:ℂ))*(restPolynomial a).coeff (n-2)) =
      phase (residue a)*(restPolynomial a).coeff n := by
    linear_combination -hh
  rw [he, ← mul_assoc, phase_neg_mul, one_mul]

def recoverRest (e : CI) (v : Fin 31 → CI) (j : Fin 31) : CI :=
  e.conj.mul (((coeffBox15 j).neg.add
    (if h : j.val=0 then CI.point 0 else (CI.point 2).mul (v ⟨j.val-1,by omega⟩))).sub
      (if h : j.val<2 then CI.point 0 else e.conj.mul (v ⟨j.val-2,by omega⟩)))

lemma recoverRest_mem (a : Fin 15) (e : CI) (he : e.Mem (phase (residue a)))
    (v : Fin 31 → CI) (hv : ∀ j, recoverRest e v j = v j) :
    ∀ j : Fin 31, (v j).Mem ((restPolynomial a).coeff j.val) := by
  have he' : e.conj.Mem (phase (-(residue a:ℂ))) := by
    simpa only [← Complex.ofReal_intCast, phase_conj] using CI.mem_conj he
  suffices hs : ∀ n (hn : n<31), (v ⟨n,hn⟩).Mem ((restPolynomial a).coeff n) from
    fun j => hs j.val j.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [← hv, restPolynomial_coeff]
    simp only [recoverRest]
    apply CI.mem_mul he'
    apply CI.mem_sub
    · apply CI.mem_add (CI.mem_neg (atomPolynomial_coeff_mem ⟨n,hn⟩))
      split_ifs with hz
      · simpa using CI.mem_point 0
      · exact CI.mem_mul (by simpa using CI.mem_point 2) (ih (n-1) (by omega) (by omega))
    · split_ifs with hz
      · simpa using CI.mem_point 0
      · exact CI.mem_mul he' (ih (n-2) (by omega) (by omega))

lemma cCoefficient_eq (a : Fin 15) (j : Fin 31) :
    cCoefficient a j = if j.val=0 then 0
      else 4*(kappa:ℂ)^2*(restPolynomial a).coeff (j.val-1) := by
  simp only [cCoefficient, cShiftPolynomial, coeff_X_mul', cAtomPolynomial, coeff_C_mul,
    restPolynomial]

lemma dCoefficient_eq (a : Fin 15) (j : Fin 31) :
    dCoefficient a j = I*(kappa:ℂ) *
      (phase (residue a)*(restPolynomial a).coeff j.val -
        (if j.val<2 then 0 else phase (-(residue a:ℂ))*(restPolynomial a).coeff (j.val-2))) := by
  change (C (I*(kappa:ℂ)) *
    (C (phase (residue a)) - C (phase (-(residue a:ℂ))) * X^2) * restPolynomial a).coeff j.val = _
  rw [mul_assoc, coeff_C_mul, sub_mul, coeff_sub, coeff_C_mul]
  rw [show C (phase (-(residue a:ℂ))) * X^2 * restPolynomial a =
    C (phase (-(residue a:ℂ))) * (X^2 * restPolynomial a) from mul_assoc _ _ _,
    coeff_C_mul, coeff_X_sq_mul]
  split_ifs <;> ring

lemma cShift_degree (a : Fin 15) : (cShiftPolynomial a).natDegree ≤ 30 := by
  have hr := restPolynomial_degree a
  change (X * (C (4*(kappa:ℂ)^2) * restPolynomial a)).natDegree ≤ 30
  calc
    _ ≤ X.natDegree + (C (4*(kappa:ℂ)^2) * restPolynomial a).natDegree := natDegree_mul_le
    _ ≤ 1 + 28 := add_le_add (by simp) ((natDegree_C_mul_le _ _).trans hr)
    _ ≤ 30 := by norm_num

lemma dAtom_degree (a : Fin 15) : (dAtomPolynomial a).natDegree ≤ 30 := by
  have hr := restPolynomial_degree a
  have hf : (C (I*(kappa:ℂ)) *
    (C (phase (residue a)) - C (phase (-(residue a:ℂ))) * X^2)).natDegree ≤ 2 := by
    compute_degree!
  exact (natDegree_mul_le).trans (add_le_add hf hr)

lemma polynomial_fourier {p : Polynomial ℂ} (hp : p.natDegree ≤ 30) (s : ℂ) :
    phase (-s)^15 * p.eval (phase s) =
      ∑ j : Fin 31, p.coeff j.val * exp (I*Real.pi*frequency j*s) := by
  rw [Polynomial.eval_eq_sum_range' (n:=31) (by omega)]
  rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_left_comm, phase_offset]

lemma finiteC_fourier (a : Fin 15) (s : ℂ) : finiteC a s =
    ∑ j : Fin 31, cCoefficient a j * exp (I*Real.pi*frequency j*s) := by
  change finiteC a s = ∑ j : Fin 31, (cShiftPolynomial a).coeff j.val * _
  rw [← polynomial_fourier (cShift_degree a) s, finiteC_spectral]
  simp only [cShiftPolynomial, eval_mul, eval_X]
  have hp := phase_neg_mul s
  have he : phase (-s)^15 * phase s = phase (-s)^14 := by
    nth_rw 1 [show 15=14+1 by norm_num]
    rw [pow_succ, mul_assoc, hp, mul_one]
  rw [← mul_assoc, he]

lemma finiteD_fourier (a : Fin 15) (s : ℂ) : finiteD a s =
    ∑ j : Fin 31, dCoefficient a j * exp (I*Real.pi*frequency j*s) := by
  rw [finiteD_spectral, polynomial_fourier (dAtom_degree a)]
  rfl

end AtomicTriangular.FiniteCertificate

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex
def kappaBox : CI := (CI.ofReal piBox).divNat 36
lemma kappaBox_mem : kappaBox.Mem (kappa:ℂ) := by
  have hh := CI.mem_divNat (CI.mem_ofReal piBox_mem) (by norm_num : 0 < (36:ℕ))
  simpa only [kappaBox, kappa, Complex.ofReal_div, Complex.ofReal_ofNat, Nat.cast_ofNat] using hh

def cCoeffBox (r : Fin 31 → CI) (j : Fin 31) : CI := if h : j.val=0 then CI.point 0
    else ((CI.point 4).mul (kappaBox.pow 2)).mul (r ⟨j.val-1,by omega⟩)
def dCoeffBox (e : CI) (r : Fin 31 → CI) (j : Fin 31) : CI :=
  (CI.imag.mul kappaBox).mul ((e.mul (r j)).sub
    (if h : j.val<2 then CI.point 0 else e.conj.mul (r ⟨j.val-2,by omega⟩)))
lemma cCoeffBox_mem (a : Fin 15) (r : Fin 31 → CI)
    (hr : ∀ j, (r j).Mem ((restPolynomial a).coeff j.val)) (j : Fin 31) :
    (cCoeffBox r j).Mem (cCoefficient a j) := by
  rw [cCoefficient_eq]
  unfold cCoeffBox
  split_ifs
  · simpa using CI.mem_point 0
  · exact CI.mem_mul (CI.mem_mul (by simpa using CI.mem_point 4)
      (CI.mem_pow kappaBox_mem 2)) (hr ⟨j.val-1,by omega⟩)
lemma dCoeffBox_mem (a : Fin 15) (e : CI) (r : Fin 31 → CI)
    (he : e.Mem (phase (residue a)))
    (hr : ∀ j, (r j).Mem ((restPolynomial a).coeff j.val)) (j : Fin 31) :
    (dCoeffBox e r j).Mem (dCoefficient a j) := by
  rw [dCoefficient_eq]
  apply CI.mem_mul (CI.mem_mul CI.mem_imag kappaBox_mem)
  apply CI.mem_sub (CI.mem_mul he (hr j))
  split_ifs
  · simpa using CI.mem_point 0
  · have hh : e.conj.Mem (phase (-(residue a:ℂ))) := by
      simpa only [← Complex.ofReal_intCast, phase_conj] using CI.mem_conj he
    exact CI.mem_mul hh (hr ⟨j.val-2,by omega⟩)

def restBox0 : Fin 31 → CI :=
  ![⟨⟨999999999999999999999999999999999999999999999999642331779778,1000000000000000000000000000000000000000000000000357668253727⟩,⟨-367531361878,347828033985⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999992982970197314,1000000000000000000000000000000000000000000000007063921851615⟩,⟨1732050807568877293527446341505872366942805253803333648896291,1732050807568877293527446341505872366942805253817415385745401⟩⟩,
  ⟨⟨499999999999999999999999999999999999999999999923182686159625,500000000000000000000000000000000000000000000076872224208513⟩,⟨2598076211353315940291169512258808550414207880638744075685320,2598076211353315940291169512258808550414207880792427896026995⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000000587101988334324,-999999999999999999999999999999999999999999999412828637490517⟩,⟨5196152422706631880582339024517617100828415760844039059449004,5196152422706631880582339024517617100828415762018323477021277⟩⟩,
  ⟨⟨-5500000000000000000000000000000000000000000003460008478208951,-5499999999999999999999999999999999999999999996539968993616806⟩,⟨6062177826491070527346062195270553284299818384876390237331482,6062177826491070527346062195270553284299818391796448173329230⟩⟩,
  ⟨⟨-10000000000000000000000000000000000000000000016631539293146282,-9999999999999999999999999999999999999999999983368575406173535⟩,⟨3464101615137754587054892683011744733885610490989512400841171,3464101615137754587054892683011744733885610524252228293562296⟩⟩,
  ⟨⟨-13000000000000000000000000000000000000000000067768982855906211,-12999999999999999999999999999999999999999999932231272438955558⟩,⟨-67769335207532302,67769491579293604⟩⟩,
  ⟨⟨-16000000000000000000000000000000000000000000241202362792978139,-15999999999999999999999999999999999999999999758798008972289255⟩,⟨-6928203230275509174109785366023489467771221256442197813599752,-6928203230275509174109785366023489467771220774040804444497265⟩⟩,
  ⟨⟨-13000000000000000000000000000000000000000000768939463892261018,-12999999999999999999999999999999999999999999231060972867132730⟩,⟨-15588457268119895641747017073552851302485248053235240060457571,-15588457268119895641747017073552851302485246515351785611031292⟩⟩,
  ⟨⟨-8000000000000000000000000000000000000000002245456385896058125,-7999999999999999999999999999999999999999997754543952881386488⟩,⟨-20784609690826527522329356098070468403313665291174152072840091,-20784609690826527522329356098070468403313660800275395708941011⟩⟩,
  ⟨⟨-500000000000000000000000000000000000000006130717013473303007,-499999999999999999999999999999999999999993869283133738238960⟩,⟨-26846787517317598049675418293341021687613487564803638613340178,-26846787517317598049675418293341021687613475303318731233611979⟩⟩,
  ⟨⟨11999999999999999999999999999999999999999984057309959618823401,12000000000000000000000000000000000000000015942690163464975944⟩,⟨-27712812921102036696439141464093957871084900003595033537420736,-27712812921102036696439141464093957871084868118337796112859897⟩⟩,
  ⟨⟨22499999999999999999999999999999999999999959880689231711308789,22500000000000000000000000000000000000000040119311205706631342⟩,⟨-21650635094610966169093079268823404586785105792031882954323541,-21650635094610966169093079268823404586785025553228206093476247⟩⟩,
  ⟨⟨29999999999999999999999999999999999999999901066244847825825182,30000000000000000000000000000000000000000098933755828324829291⟩,⟨-13856406460551018348219570732046978935542540964125648372283912,-13856406460551018348219570732046978935542343096840762947977614⟩⟩,
  ⟨⟨35999999999999999999999999999999999999999758783933778131632961,36000000000000000000000000000000000000000241216066963434043284⟩,⟨-241216188127543871524,241216188127541669674⟩⟩,
  ⟨⟨29999999999999999999999999999999999999999415228731267933748950,30000000000000000000000000000000000000000584771269408217485908⟩,⟨13856406460551018348219570732046978935541857259355317386371844,13856406460551018348219570732046978935543026801611093929498328⟩⟩,
  ⟨⟨22499999999999999999999999999999999999998586012150859255187147,22500000000000000000000000000000000000001413987849578163861796⟩,⟨21650635094610966169093079268823404586783651684684735382922772,21650635094610966169093079268823404586786479660575353660494629⟩⟩,
  ⟨⟨11999999999999999999999999999999999999996584500588855566793024,12000000000000000000000000000000000000003415499411267518569849⟩,⟨27712812921102036696439141464093957871081468561737758540525872,27712812921102036696439141464093957871088299560195071105343819⟩⟩,
  ⟨⟨-500000000000000000000000000000000000008247089885691885689567,-499999999999999999999999999999999999991752910114455323931101⟩,⟨26846787517317598049675418293341021687605234344256412310832072,26846787517317598049675418293341021687621728523865957531610427⟩⟩,
  ⟨⟨-8000000000000000000000000000000000000019911114982621922296694,-7999999999999999999999999999999999999980088885017716852954532⟩,⟨20784609690826527522329356098070468403293751931192234918390348,20784609690826527522329356098070468403333574160257312858664175⟩⟩,
  ⟨⟨-13000000000000000000000000000000000000048070190716007858449148,-12999999999999999999999999999999999999951929809284428898538590⟩,⟨15588457268119895641747017073552851302437177094521687391851447,15588457268119895641747017073552851302533317474065338274559381⟩⟩,
  ⟨⟨-16000000000000000000000000000000000000116051962789771012354335,-15999999999999999999999999999999999999883948037210600750341085⟩,⟨6928203230275509174109785366023489467655169054800079160886362,6928203230275509174109785366023489467887272975682923091642345⟩⟩,
  ⟨⟨-13000000000000000000000000000000000000280174335061129077922570,-12999999999999999999999999999999999999719825664939126214215966⟩,⟨-280174329425673229770431,280174329425516851814346⟩⟩,
  ⟨⟨-10000000000000000000000000000000000000676400721944635163804716,-9999999999999999999999999999999999999323599278055479532626145⟩,⟨-3464101615137754587054892683011744734562011215943999619962773,-3464101615137754587054892683011744733209209799297741081369692⟩⟩,
  ⟨⟨-5500000000000000000000000000000000001632975809996022673151214,-5499999999999999999999999999999999998367024190003954795593198⟩,⟨-6062177826491070527346062195270553285932794165454946617824734,-6062177826491070527346062195270553282666842611217891800587026⟩⟩,
  ⟨⟨-1000000000000000000000000000000000003942352351060922093163614,-999999999999999999999999999999999996057647648939008529350687⟩,⟨-5196152422706631880582339024517617104770768033115528465955416,-5196152422706631880582339024517617096886063489746834079159789⟩⟩,
  ⟨⟨499999999999999999999999999999999990482319485673173024120090,500000000000000000000000000000000009517680514326881889813103⟩,⟨-2598076211353315940291169512258808559931888203411715734148915,-2598076211353315940291169512258808540896527558019456247154963⟩⟩,
  ⟨⟨999999999999999999999999999999999977022286619858945830353743,1000000000000000000000000000000000022977713380141101065523405⟩,⟨-1732050807568877293527446341505872389920518171313404031467961,-1732050807568877293527446341505872343965092336307345013765616⟩⟩,
  ⟨⟨999999999999999999999999999999999944526892725328578876355744,1000000000000000000000000000000000055473107274671421127771328⟩,⟨-55473106157764586717542480,55473106157764606409220663⟩⟩,
  ⟨⟨-133923927929490250314752322,133923927929490250319107136⟩,⟨-133923925233038553459603387,133923925233038553446834853⟩⟩,
  ⟨⟨-323320963133652284734076177,323320963133652284738688141⟩,⟨-323320956623842066465073387,323320956623842066451117969⟩⟩]
lemma restBox0_calc (j : Fin 31) : recoverRest phaseBox0 restBox0 j = restBox0 j := by
  revert j
  decide +kernel
lemma restBox0_mem (j : Fin 31) : (restBox0 j).Mem ((restPolynomial ⟨0,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨0,by norm_num⟩ phaseBox0
  · have hr : residue ⟨0,by norm_num⟩ = (0:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox0_mem
  · exact restBox0_calc
def cBox0 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651966740766375,30461741978670859934674354937889355355906479651988725086961⟩,⟨-11195645515,10595447836⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651763885012090,30461741978670859934674354937889355355906479652193009253703⟩,⟨52761284794111633070194360652541195326313997272545860379138,52761284794111633070194360652541195326313997272975150502454⟩⟩,
  ⟨⟨15230870989335429967337177468944677677953239823648828787981,15230870989335429967337177468944677677953239828330576803617⟩,⟨79141927191167449605291540978811792989470995906800505278779,79141927191167449605291540978811792989470995911482485993522⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906479669861979172758,-30461741978670859934674354937889355355906479634091373421386⟩,⟨158283854382334899210583081957623585978941991800397396158541,158283854382334899210583081957623585978941991836169152762599⟩⟩,
  ⟨⟨-167539580882689729640708952158391454457485638191275949896232,-167539580882689729640708952158391454457485637980478426044136⟩,⟨184664496779390715745680262283894183642098990349265973467019,184664496779390715745680262283894183642098990560064168401675⟩⟩,
  ⟨⟨-304617419786708599346743549378893553559064797026403957544993,-304617419786708599346743549378893553559064796013154194919287⟩,⟨105522569588223266140388721305082390652627994038904235867635,105522569588223266140388721305082390652627995052145176679232⟩⟩,
  ⟨⟨-396002645722721179150766614192561619626784237540073058469299,-396002645722721179150766614192561619626784233411355774337017⟩,⟨-2064372003158035,2064376766514151⟩⟩,
  ⟨⟨-487387871658733758954789679006229685694503681779089418267878,-487387871658733758954789679006229685694503667084209359986761⟩,⟨-211045139176446532280777442610164781305255996438436174227140,-211045139176446532280777442610164781305255981743648055710895⟩⟩,
  ⟨⟨-396002645722721179150766614192561619626784258898947334859268,-396002645722721179150766614192561619626784212052487025672644⟩,⟨-474851563147004697631749245872870757936825998878154882865656,-474851563147004697631749245872870757936825952031542877160927⟩⟩,
  ⟨⟨-243693935829366879477394839503114842847251905616335690635717,-243693935829366879477394839503114842847251768815318355933710⟩,⟨-633135417529339596842332327830494343915768035673436184600418,-633135417529339596842332327830494343915767898872832985243856⟩⟩,
  ⟨⟨-15230870989335429967337177468944677677953426578308723615810,-15230870989335429967337177468944677677953053073673493630087⟩,⟨-817799914308730312588012590114388527557867144480896772022716,-817799914308730312588012590114388527557866770974702041778144⟩⟩,
  ⟨⟨365540903744050319216092259254672264270877270181621175543864,365540903744050319216092259254672264270878241465848164031142⟩,⟨-844180556705786129123109770440659125221024442004423090698659,-844180556705786129123109770440659125221023470723938826503224⟩⟩,
  ⟨⟨685389194520094348530172986102510495507894570065403823455342,685389194520094348530172986102510495507897014273607482734414⟩,⟨-659516059926395413377429508156764941578926188016386617556272,-659516059926395413377429508156764941578923743802648137184295⟩⟩,
  ⟨⟨913852259360125798040230648136680660677191375864806652373917,913852259360125798040230648136680660677197403253877919922476⟩,⟨-422090278352893064561554885220329562610514991873180869451196,-422090278352893064561554885220329562610508964490999982384792⟩⟩,
  ⟨⟨1096622711232150957648276777764016792812625919609624534145246,1096622711232150957648276777764016792812640615332794825920420⟩,⟨-7347865283819770646,7347865283819703935⟩⟩,
  ⟨⟨913852259360125798040230648136680660677176576407824422701341,913852259360125798040230648136680660677212202710860149612455⟩,⟨422090278352893064561554885220329562610494165034874773428189,422090278352893064561554885220329562610529791329306078274633⟩⟩,
  ⟨⟨685389194520094348530172986102510495507852719636475308031328,685389194520094348530172986102510495507938864702535998191770⟩,⟨659516059926395413377429508156764941578881893373564320049679,659516059926395413377429508156764941578968038445470434557845⟩⟩,
  ⟨⟨365540903744050319216092259254672264270773713761941047576948,365540903744050319216092259254672264270981797885528292045131⟩,⟨844180556705786129123109770440659125220919914307946594403482,844180556705786129123109770440659125221127998420415322664279⟩⟩,
  ⟨⟨-15230870989335429967337177468944677678204460550161767322786,-15230870989335429967337177468944677677702019101820449865123⟩,⟨817799914308730312588012590114388527557615737006088893400812,817799914308730312588012590114388527558118178449509920262666⟩⟩,
  ⟨⟨-243693935829366879477394839503114842847858364462930915631641,-243693935829366879477394839503114842846645309968723130871386⟩,⟨633135417529339596842332327830494343915161440039734603754723,633135417529339596842332327830494343916374494506534565945411⟩⟩,
  ⟨⟨-396002645722721179150766614192561619628248537222168319379171,-396002645722721179150766614192561619625319933729266041079761⟩,⟨474851563147004697631749245872870757935361673737152278783225,474851563147004697631749245872870757938290277172545481088411⟩⟩,
  ⟨⟨-487387871658733758954789679006229685698038819378265594470704,-487387871658733758954789679006229685690968529485033183705727⟩,⟨211045139176446532280777442610164781301720844215955929603010,211045139176446532280777442610164781308791133966128300165084⟩⟩,
  ⟨⟨-396002645722721179150766614192561619635318833779389579120861,-396002645722721179150766614192561619618249637172039253602500⟩,⟨-8534598132011988586676,8534598132007225041597⟩⟩,
  ⟨⟨-304617419786708599346743549378893553579669140785842467794314,-304617419786708599346743549378893553538460452253715684581895⟩,⟨-105522569588223266140388721305082390673232338396654413253765,-105522569588223266140388721305082390632023650694394999504372⟩⟩,
  ⟨⟨-167539580882689729640708952158391454507228925867387958309946,-167539580882689729640708952158391454407742350304366417536438⟩,⟨-184664496779390715745680262283894183691842277234669775125708,-184664496779390715745680262283894183592355703674660366979207⟩⟩,
  ⟨⟨-30461741978670859934674354937889355475997399759002079490308,-30461741978670859934674354937889355235815559544951273002888⟩,⟨-158283854382334899210583081957623586099032909507359284279546,-158283854382334899210583081957623585858851074129207264904953⟩⟩,
  ⟨⟨15230870989335429967337177468944677388028111763141651750909,15230870989335429967337177468944677967878367888837753949337⟩,⟨-79141927191167449605291540978811793279396118134584059643984,-79141927191167449605291540978811792699545873683698931920482⟩⟩,
  ⟨⟨30461741978670859934674354937889354655965303406267787305561,30461741978670859934674354937889356055847655897689107076882⟩,⟨-52761284794111633070194360652541196026255159425710385465258,-52761284794111633070194360652541194626372835119810625738959⟩⟩,
  ⟨⟨30461741978670859934674354937889353666098999095807345841914,30461741978670859934674354937889357045713960208148120136120⟩,⟨-1689807446533242486228767,1689807446533243086071598⟩⟩,
  ⟨⟨-4079556137358243979696731,4079556137358243979829386⟩,⟨-4079556055219628132145969,4079556055219628131757017⟩⟩]
lemma cBox0_calc (j : Fin 31) : cCoeffBox restBox0 j = cBox0 j := by
  revert j
  decide +kernel
lemma cBox0_mem (j : Fin 31) : (cBox0 j).Mem (cCoefficient ⟨0,by norm_num⟩ j) := by
  rw [← cBox0_calc]
  exact cCoeffBox_mem ⟨0,by norm_num⟩ restBox0 restBox0_mem j
def dBox0 : Fin 31 → CI :=
  ![⟨⟨-30353728110,32073167388⟩,⟨87266462599716478846184538424430635672143594427054898665117,87266462599716478846184538424430635672143594427117601337988⟩⟩,
  ⟨⟨-151149947019518154216173188136846311023672187341675814129132,-151149947019518154216173188136846311023672187340446469610477⟩,⟨87266462599716478846184538424430635672143594426473759726270,87266462599716478846184538424430635672143594427702832376369⟩⟩,
  ⟨⟨-226724920529277231324259782205269466535508281018331981224134,-226724920529277231324259782205269466535508281004857389245287⟩,⟨-43633231299858239423092269212215317836071797220277982157179,-43633231299858239423092269212215317836071797206803476013412⟩⟩,
  ⟨⟨-302299894039036308432346376273692622047344374733980056895279,-302299894039036308432346376273692622047344374630274583972932⟩,⟨-174532925199432957692369076848861271344287188906023535010153,-174532925199432957692369076848861271344287188802319503057679⟩⟩,
  ⟨⟨-302299894039036308432346376273692622047344374990780321669751,-302299894039036308432346376273692622047344374373478938831407⟩,⟨-523598775598298873077107230546583814032861566871169400957225,-523598775598298873077107230546583814032861566253868424927244⟩⟩,
  ⟨⟨151149947019518154216173188136846311023672185838457751561125,151149947019518154216173188136846311023672188843653432536882⟩,⟨-785398163397448309615660845819875721049292351346393469562707,-785398163397448309615660845819875721049292348341175093885552⟩⟩,
  ⟨⟨529024814568313539756606158478962088582852649477774322823855,529024814568313539756606158478962088582852661909658942706383⟩,⟨-654498469497873591346384038183229767541076964419051991037620,-654498469497873591346384038183229767541076951987266003600019⟩⟩,
  ⟨⟨906899682117108925297039128821077866142033101546284908714656,906899682117108925297039128821077866142033146546470500797662⟩,⟨-523598775598298873077107230546583814032861589062760897475544,-523598775598298873077107230546583814032861544062296535759882⟩⟩,
  ⟨⟨1360349523175663387945558693231616799213049613052745882550075,1360349523175663387945558693231616799213049759086393132190771⟩,⟨-73016564096571369,73016548260810557⟩⟩,
  ⟨⟨1209199576156145233729385505094770488189377281727355593179296,1209199576156145233729385505094770488189377715729670956614124⟩,⟨698131700797731830769476307395445085377148538414808640509039,698131700797731830769476307395445085377148972418574238235405⟩⟩,
  ⟨⟨982474655626868002405125722889501021653868615605885079972972,982474655626868002405125722889501021653869819827951255202748⟩,⟨1090830782496455985577306730305382945901794328230000570111444,1090830782496455985577306730305382945901795532447180947726563⟩⟩,
  ⟨⟨604599788078072616864692752547385244094687162155027795458020,604599788078072616864692752547385244094690336573486274137310⟩,⟨1745329251994329576923690768488612713442870301326551918860897,1745329251994329576923690768488612713442873475756938386161364⟩⟩,
  ⟨⟨-453449841058554462648519564410538933071020598109672717748782,-453449841058554462648519564410538933071012525936697073941848⟩,⟨2007128639793479013462244383761904620459298635746673748806726,2007128639793479013462244383761904620459306707899344769765927⟩⟩,
  ⟨⟨-1209199576156145233729385505094770488189387523574321826698668,-1209199576156145233729385505094770488189367473882693623361613⟩,⟨1570796326794896619231321691639751442098574674826531273931836,1570796326794896619231321691639751442098594724548621990278003⟩⟩,
  ⟨⟨-1889374337743976927702164851710578887795926892925038698284974,-1889374337743976927702164851710578887795877790601553213756724⟩,⟨1178097245096172464423491268729813581573913973622470238953377,1178097245096172464423491268729813581573963075908885052955751⟩⟩,
  ⟨⟨-2418399152312290467458771010189540976378814661953788024188019,-2418399152312290467458771010189540976378695332960241652105071⟩,⟨-59664518955038107737,59664518955038158357⟩⟩,
  ⟨⟨-1889374337743976927702164851710578887796046785572904411810588,-1889374337743976927702164851710578887795757897953687500232942⟩,⟨-1178097245096172464423491268729813581574082968556305860041990,-1178097245096172464423491268729813581573794080975049431770421⟩⟩,
  ⟨⟨-1209199576156145233729385505094770488189726588171967799833196,-1209199576156145233729385505094770488189028409285047650225339⟩,⟨-1570796326794896619231321691639751442098933789159288190768408,-1570796326794896619231321691639751442098235610215865073355663⟩⟩,
  ⟨⟨-453449841058554462648519564410538933071859650103336079928956,-453449841058554462648519564410538933070173473943033711750521⟩,⟨-2007128639793479013462244383761904620460145759901844842228617,-2007128639793479013462244383761904620458459583744173676273143⟩⟩,
  ⟨⟨604599788078072616864692752547385244092653118296886694919197,604599788078072616864692752547385244096724380431627374703718⟩,⟨-1745329251994329576923690768488612713444907519664310139155635,-1745329251994329576923690768488612713440836257419180165811646⟩⟩,
  ⟨⟨982474655626868002405125722889501021648954607945027633057576,982474655626868002405125722889501021658783827488808702167770⟩,⟨-1090830782496455985577306730305382945906709540199912984058611,-1090830782496455985577306730305382945896880320477268533737075⟩⟩,
  ⟨⟨1209199576156145233729385505094770488177512482131353740590625,1209199576156145233729385505094770488201242515325672809276267⟩,⟨-698131700797731830769476307395445085389013772258028418632780,-698131700797731830769476307395445085365283738575354460078598⟩⟩,
  ⟨⟨1360349523175663387945558693231616799184404948011463729859736,1360349523175663387945558693231616799241694424127675284978565⟩,⟨-28644738632254078130981,28644738632269913919509⟩⟩,
  ⟨⟨906899682117108925297039128821077866072878582865589039799025,906899682117108925297039128821077866211187665227166369832023⟩,⟨523598775598298873077107230546583813963707023988129138467709,523598775598298873077107230546583814102016109136928294795399⟩⟩,
  ⟨⟨529024814568313539756606158478962088415898813473339532266821,529024814568313539756606158478962088749806497914093733399211⟩,⟨654498469497873591346384038183229767374123112621896022025412,654498469497873591346384038183229767708030803784421972643490⟩⟩,
  ⟨⟨151149947019518154216173188136846310620609953153903873170292,151149947019518154216173188136846311426734421528207311077439⟩,⟨785398163397448309615660845819875720646230107541019991284768,785398163397448309615660845819875721452354592146548572200284⟩⟩,
  ⟨⟨-302299894039036308432346376273692623020422688178906309793345,-302299894039036308432346376273692621074266061185352950547209⟩,⟨523598775598298873077107230546583813059783233473702718086202,523598775598298873077107230546583815005939899651335107840473⟩⟩,
  ⟨⟨-302299894039036308432346376273692624396563236696277526961234,-302299894039036308432346376273692619698125512667977113737076⟩,⟨174532925199432957692369076848861268995068279540319661357124,174532925199432957692369076848861273693506098168023376755879⟩⟩,
  ⟨⟨-226724920529277231324259782205269472207024318734880386270074,-226724920529277231324259782205269460863992243288308984019743⟩,⟨43633231299858239423092269212215312164555645298812217286590,43633231299858239423092269212215323507587949128269240930116⟩⟩,
  ⟨⟨-151149947019518154216173188136846324715923124839546668173443,-151149947019518154216173188136846297331421249842575615376216⟩,⟨-87266462599716478846184538424430649364394807608160799538944,-87266462599716478846184538424430621979892381246015792517745⟩⟩,
  ⟨⟨-33056017912725732836921781,33056017912725734556562273⟩,⟨-87266462599716478846184538424430668728162172709437663280394,-87266462599716478846184538424430602616125016144734836677472⟩⟩]
lemma dBox0_calc (j : Fin 31) : dCoeffBox phaseBox0 restBox0 j = dBox0 j := by
  revert j
  decide +kernel
lemma dBox0_mem (j : Fin 31) : (dBox0 j).Mem (dCoefficient ⟨0,by norm_num⟩ j) := by
  rw [← dBox0_calc]
  apply dCoeffBox_mem ⟨0,by norm_num⟩ phaseBox0 restBox0
  · have hr : residue ⟨0,by norm_num⟩ = (0:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox0_mem
  · exact restBox0_mem
def restBox1 : Fin 31 → CI :=
  ![⟨⟨984807753012208059366743024589523013670643251719426322748378,984807753012208059366743024589523013670643251720255109258911⟩,⟨-173648177666930348851716626769314796000375677184493677676862,-173648177666930348851716626769314796000375677183664410956623⟩⟩,
  ⟨⟨1195344954920479302020019325284943778346249533492338608247804,1195344954920479302020019325284943778346249533508914786050570⟩,⟨1195344954920479302020019325284943778346249533492310266667859,1195344954920479302020019325284943778346249533508887631620981⟩⟩,
  ⟨⟨1260695890999055218561659595274285933505145287681579916751251,1260695890999055218561659595274285933505145287865687984080234⟩,⟨1673186568929854202264579447802675380746740549706926998707437,1673186568929854202264579447802675380746740549891031258577320⟩⟩,
  ⟨⟨848048599586618604316586071746314186345498178414123771722695,848048599586618604316586071746314186345498179850884222238540⟩,⟨4022659583452580810172358095205882342427056962576472052285654,4022659583452580810172358095205882342427056964013242889300646⟩⟩,
  ⟨⟨-1944736177650392684649858824638805095031312027148787396791589,-1944736177650392684649858824638805095031312018455026112470990⟩,⟨5302678289647511163687600994724989038497643171096649544162527,5302678289647511163687600994724989038497643179790425724667813⟩⟩,
  ⟨⟨-4763052238228233069358536264446930351891114282284258425762440,-4763052238228233069358536264446930351891114239073243867824078⟩,⟨4218149218596521816155176253340347579159344840095733687330492,4218149218596521816155176253340347579159344883306538950797868⟩⟩,
  ⟨⟨-6575774351329494088867824310925138753973559383598216316714926,-6575774351329494088867824310925138753973559199884138905984306⟩,⟨3200955386427089527797902528550531989217245763841336778956815,3200955386427089527797902528550531989217245947556378422075712⟩⟩,
  ⟨⟨-9408488879558106265608053330141915187880848776142571838725428,-9408488879558106265608053330141915187880848086222206980060741⟩,⟨-415903802171449818665693088196866634357132904572967116237202,-415903802171449818665693088196866634357132214655183515840017⟩⟩,
  ⟨⟨-7983052994534488614659010571533693637444122720786134118112324,-7983052994534488614659010571533693637444120368890703010561404⟩,⟨-5556224252817590106615339307859771982121934118568383840045422,-5556224252817590106615339307859771982121931766668581257762942⟩⟩,
  ⟨⟨-6098715906229370868735544076173868274732371156550539708277738,-6098715906229370868735544076173868274732363700980993266842479⟩,⟨-7934033442590758774230660593512715466092010894763346608338458,-7934033442590758774230660593512715466092003439205150053507597⟩⟩,
  ⟨⟨-3053994058500630795791247119733610295119461556417234324124356,-3053994058500630795791247119733610295119439108500307803267626⟩,⟨-12305144463075410749779676595309481179566829691481880364760645,-12305144463075410749779676595309481179566807243520941842133041⟩⟩,
  ⟨⟨3982132875870569530526401085239845821366295448966369119199826,3982132875870569530526401085239845821366360790932650923001220⟩,⟨-13557123038515227382545171608645942668048159385092107501328466,-13557123038515227382545171608645942668048094043233330384299749⟩⟩,
  ⟨⟨9446808552295449412636903832767264422570750831644394817245444,9446808552295449412636903832767264422570937221782036910825751⟩,⟨-10396529412979611231410237052261207791904090717636058724408615,-10396529412979611231410237052261207791903904327338377600203026⟩⟩,
  ⟨⟨13237076327392490421449572266123032620913883908027651693501459,13237076327392490421449572266123032620914409824889955918108320⟩,⟨-7429827988160338734983041586749502851392052497035808510027594,-7429827988160338734983041586749502851391526580363038941181523⟩⟩,
  ⟨⟨17745799303907691677584378593137503638707098032293656768015324,17745799303907691677584378593137503638708574156582527174478881⟩,⟨-738062251635092861237,738062251635091840550⟩⟩,
  ⟨⟨13237076327392490421449572266123032620912080001069634253500715,13237076327392490421449572266123032620916213731847973357881976⟩,⟨7429827988160338734983041586749502851389722673418684968871736,7429827988160338734983041586749502851393856403980162480316979⟩⟩,
  ⟨⟨9446808552295449412636903832767264422565061046531169243218308,9446808552295449412636903832767264422576627006895262484346846⟩,⟨10396529412979611231410237052261207791898214542202254853308314,10396529412979611231410237052261207791909780502772181469326800⟩⟩,
  ⟨⟨3982132875870569530526401085239845821350152501043359954514962,3982132875870569530526401085239845821382503738855660086826211⟩,⟨13557123038515227382545171608645942668031951095350169151242578,13557123038515227382545171608645942668064302332975268732461830⟩⟩,
  ⟨⟨-3053994058500630795791247119733610295164691128175953986877415,-3053994058500630795791247119733610295074209536741588141834584⟩,⟨12305144463075410749779676595309481179521577671715617638636988,12305144463075410749779676595309481179612059263287204566394812⟩⟩,
  ⟨⟨-6098715906229370868735544076173868274858896034667515723755317,-6098715906229370868735544076173868274605838822864017253250038⟩,⟨7934033442590758774230660593512715465965478561118496927483580,7934033442590758774230660593512715466218535772849999732559313⟩⟩,
  ⟨⟨-7983052994534488614659010571533693637797992240682225758159486,-7983052994534488614659010571533693637090250848994611373054665⟩,⟨5556224252817590106615339307859771981768062246758154949509073,5556224252817590106615339307859771982475803638478810146573406⟩⟩,
  ⟨⟨-9408488879558106265608053330141915188870540121864238767395041,-9408488879558106265608053330141915186891156740500540054671591⟩,⟨415903802171449818665693088196866633367440868937481310550790,415903802171449818665693088196866635346824250290669319926886⟩⟩,
  ⟨⟨-6575774351329494088867824310925138756741489564360236901829819,-6575774351329494088867824310925138751205629019122118324941461⟩,⟨-3200955386427089527797902528550531991985176128324223642129180,-3200955386427089527797902528550531986449315583073491560296002⟩⟩,
  ⟨⟨-4763052238228233069358536264446930359632351028440338476183952,-4763052238228233069358536264446930344149877492917163822274990⟩,⟨-4218149218596521816155176253340347586900581629467493071841212,-4218149218596521816155176253340347571418108093934779567343377⟩⟩,
  ⟨⟨-1944736177650392684649858824638805116681693528756458954339307,-1944736177650392684649858824638805073380930516847354560567652⟩,⟨-5302678289647511163687600994724989060148024681410623112210727,-5302678289647511163687600994724989016847261669476452157179967⟩⟩,
  ⟨⟨848048599586618604316586071746314125794576777889114745193125,848048599586618604316586071746314246896419580375893242424634⟩,⟨-4022659583452580810172358095205882402977978364561597425017742,-4022659583452580810172358095205882281876135562028117516459588⟩⟩,
  ⟨⟨1260695890999055218561659595274285764158749182812238169301522,1260695890999055218561659595274286102851541392735029724587214⟩,⟨-1673186568929854202264579447802675550093136654806504069743438,-1673186568929854202264579447802675211400344444791454186578045⟩⟩,
  ⟨⟨1195344954920479302020019325284943304725019501722534900703777,1195344954920479302020019325284944251967479565278718486177353⟩,⟨-1195344954920479302020019325284944251967479565368899570334461,-1195344954920479302020019325284943304725019501632298325967892⟩⟩,
  ⟨⟨984807753012208059366743024589521689065722827411097463066609,984807753012208059366743024589524338275563676028583961206545⟩,⟨173648177666930348851716626769313471395455252698639129054574,173648177666930348851716626769316120605296101669518962733457⟩⟩,
  ⟨⟨-3704602082754043222517421888,3704602082754043222509558652⟩,⟨-3704602082754389236791793120,3704602082754389236796230833⟩⟩,
  ⟨⟨-10360882992303317198793262409,10360882992303317198785487232⟩,⟨-10360882992303994807389477089,10360882992303994807395273014⟩⟩]
lemma restBox1_calc (j : Fin 31) : recoverRest phaseBox1 restBox1 j = restBox1 j := by
  revert j
  decide +kernel
lemma restBox1_mem (j : Fin 31) : (restBox1 j).Mem ((restPolynomial ⟨1,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨1,by norm_num⟩ phaseBox1
  · have hr : residue ⟨1,by norm_num⟩ = (1:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox1_mem
  · exact restBox1_calc
def cBox1 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨29998959670852502253334400260293903887583974252636250420687,29998959670852502253334400260293903887583974252661687680853⟩,⟨-5289625983156427915144478140897837194877087266739372873631,-5289625983156427915144478140897837194877087266714078289949⟩⟩,
  ⟨⟨36412289592293591044594635370036879032997090597570579815332,36412289592293591044594635370036879032997090598075750874416⟩,⟨36412289592293591044594635370036879032997090597569716481448,36412289592293591044594635370036879032997090598074923703201⟩⟩,
  ⟨⟨38402992945183783072679524751971870167446745480084862608775,38402992945183783072679524751971870167446745485693359533024⟩,⟨50968177544918804122872932493175650349786646604338390837379,50968177544918804122872932493175650349786646609946851772242⟩⟩,
  ⟨⟨25833037625980735214305679088241204643242916042487596882031,25833037625980735214305679088241204643242916086253987469083⟩,⟨122537218299160116183036736211972226603476706118328900023201,122537218299160116183036736211972226603476706162096222639055⟩⟩,
  ⟨⟨-59240051660172877835280117946062529857582891401905659235794,-59240051660172877835280117946062529857582891137078169034699⟩,⟨161528817855142188049118274010326962840075429476452896709668,161528817855142188049118274010326962840075429741281491865022⟩⟩,
  ⟨⟨-145090868311839164547035042169459007435786558940932784430327,-145090868311839164547035042169459007435786557624649084652554⟩,⟨128492173124419354161201274990896540545587163684794076080978,128492173124419354161201274990896540545587165001071294714001⟩⟩,
  ⟨⟨-200309541600160793748134069426613698940469498888235470632013,-200309541600160793748134069426613698940469493291983371486502⟩,⟨97506677066578677226719567201531313276360803273568181323512,97506677066578677226719567201531313276360808869848998203869⟩⟩,
  ⟨⟨-286598960658293129956382401874164573017518273096364630117975,-286598960658293129956382401874164573017518252080186665417088⟩,⟨-12669154309694873691924785757906602296744271317032127469626,-12669154309694873691924785757906602296744250300934536283404⟩⟩,
  ⟨⟨-243177700521565346812336769081884319932887644337835195409863,-243177700521565346812336769081884319932887572695001864079290⟩,⟨-169252269564962717566763251966816636863469610616029977255517,-169252269564962717566763251966816636863469538973063953813524⟩⟩,
  ⟨⟨-185777510336774922443142335881866333568546523226014003364454,-185777510336774922443142335881866333568546296116376992932794⟩,⟨-241684479578345394784854522305757340442852915620391299861896,-241684479578345394784854522305757340442852688511099670832640⟩⟩,
  ⟨⟨-93029979014440055106215379400418445592445819575023903969084,-93029979014440055106215379400418445592445135772369937405145⟩,⟨-374836135644473539026813299217339788680138391086965768541989,-374836135644473539026813299217339788680137707282969325702396⟩⟩,
  ⟨⟨121302704189551844563774955811481578009262117237016166795833,121302704189551844563774955811481578009264107667134194351766⟩,⟨-412973583972345143427081836236749430808142395989435198796855,-412973583972345143427081836236749430808140405562590094436365⟩⟩,
  ⟨⟨287766244641925184999571079890553431412716506825232030628449,287766244641925184999571079890553431412722184593514085007126⟩,⟨-316696396451847336548801001834400465401944646120432080077270,-316696396451847336548801001834400465401938968347274773866101⟩⟩,
  ⟨⟨403224403637002120913307323409929281316674460903887621134964,403224403637002120913307323409929281316690481247651931602566⟩,⟨-226325503121247451356911273837859885637148418488787751569604,-226325503121247451356911273837859885637132398150798123055203⟩⟩,
  ⟨⟨540567959600913056773917034395921519750579614255447896976580,540567959600913056773917034395921519750624579572667357670754⟩,⟨-22482661873505043743,22482661873505012830⟩⟩,
  ⟨⟨403224403637002120913307323409929281316619510755578964830259,403224403637002120913307323409929281316745431395960587900205⟩,⟨226325503121247451356911273837859885637077448002905679778041,226325503121247451356911273837859885637203368636680194785487⟩⟩,
  ⟨⟨287766244641925184999571079890553431412543186059198870628151,287766244641925184999571079890553431412895505359547244991802⟩,⟨316696396451847336548801001834400465401765647580544126094068,316696396451847336548801001834400465402117966887162727789285⟩⟩,
  ⟨⟨121302704189551844563774955811481578008770374922610340954749,121302704189551844563774955811481578009755849981540020166385⟩,⟨412973583972345143427081836236749430807648663249398106007083,412973583972345143427081836236749430808634138302627187167615⟩⟩,
  ⟨⟨-93029979014440055106215379400418445593823591119743800715182,-93029979014440055106215379400418445591067364227650040699505⟩,⟨374836135644473539026813299217339788678759935736829773461244,374836135644473539026813299217339788681516162633105320726365⟩⟩,
  ⟨⟨-185777510336774922443142335881866333572400691417096105721093,-185777510336774922443142335881866333564692127925294890633737⟩,⟨241684479578345394784854522305757340438998520320941256510601,241684479578345394784854522305757340446707083810549714128887⟩⟩,
  ⟨⟨-243177700521565346812336769081884319943667126347026073202678,-243177700521565346812336769081884319922108090685810986363972⟩,⟨169252269564962717566763251966816636852690056963436417056422,169252269564962717566763251966816636874249092625657513959887⟩⟩,
  ⟨⟨-286598960658293129956382401874164573047665995508261586574708,-286598960658293129956382401874164572987370529668289709060293⟩,⟨12669154309694873691924785757906602266596527889158352207212,12669154309694873691924785757906602326891993728808311496905⟩⟩,
  ⟨⟨-200309541600160793748134069426613699024785473869583934577925,-200309541600160793748134069426613698856153518310634907664567⟩,⟨-97506677066578677226719567201531313360676783851374890676496,-97506677066578677226719567201531313192044828292042288893437⟩⟩,
  ⟨⟨-145090868311839164547035042169459007671598115298144863819963,-145090868311839164547035042169459007199975001267437005411255⟩,⟨-128492173124419354161201274990896540781398721358431846785394,-128492173124419354161201274990896540309775607327433524041853⟩⟩,
  ⟨⟨-59240051660172877835280117946062530517091226443667115926973,-59240051660172877835280117946062529198074556095316712515351⟩,⟨-161528817855142188049118274010326963499583764783424507157654,-161528817855142188049118274010326962180567094434309881434143⟩⟩,
  ⟨⟨25833037625980735214305679088241202798756371768915191004578,25833037625980735214305679088241206487729460359826393153383⟩,⟨-122537218299160116183036736211972228447963250436379773393770,-122537218299160116183036736211972224758990161844045349265148⟩⟩,
  ⟨⟨38402992945183783072679524751971865008860522315763032667024,38402992945183783072679524751971875326032968650015189263320⟩,⟨-50968177544918804122872932493175655508372869775673914274126,-50968177544918804122872932493175645191200423438611328306125⟩⟩,
  ⟨⟨36412289592293591044594635370036864605669385749080569144928,36412289592293591044594635370036893460324795446565761318901⟩,⟨-36412289592293591044594635370036893460324795449312834235839,-36412289592293591044594635370036864605669385746331805888273⟩⟩,
  ⟨⟨29998959670852502253334400260293863537810664609509287195509,29998959670852502253334400260293944237357283895788650670433⟩,⟨5289625983156427915144478140897796845103777618204634242553,5289625983156427915144478140897877544650396915248817017140⟩⟩,
  ⟨⟨-112848632778500337391816203,112848632778500337391576675⟩,⟨-112848632778510877589363037,112848632778510877589498217⟩⟩]
lemma cBox1_calc (j : Fin 31) : cCoeffBox restBox1 j = cBox1 j := by
  revert j
  decide +kernel
lemma cBox1_mem (j : Fin 31) : (cBox1 j).Mem (cCoefficient ⟨1,by norm_num⟩ j) := by
  rw [← cBox1_calc]
  exact cCoeffBox_mem ⟨1,by norm_num⟩ restBox1 restBox1_mem j
def dBox1 : Fin 31 → CI :=
  ![⟨⟨-41078466350,42797905629⟩,⟨87266462599716478846184538424430635672143594427044206261316,87266462599716478846184538424430635672143594427128293741945⟩⟩,
  ⟨⟨-120842622615757954989806784943385483777488657250454979128321,-120842622615757954989806784943385483777488657248778666141097⟩,⟨84614915292584877405267514585930721146779762463498237790715,84614915292584877405267514585930721146779762465174351426722⟩⟩,
  ⟨⟨-192745854186654778030905517416873603034825852314726806916004,-192745854186654778030905517416873603034825852296030283027681⟩,⟨986518410711267646848346420326177536587103883604397555515,986518410711267646848346420326177536587103902300530521149⟩⟩,
  ⟨⟨-273946262714078519363244623147248542328670506579953565591203,-273946262714078519363244623147248542328670506433027431786528⟩,⟨-108918766188261799001159249611462746692647109646154963228352,-108918766188261799001159249611462746692647109499230046101670⟩⟩,
  ⟨⟨-301555303566433744803763851245664044375061566772028019182001,-301555303566433744803763851245664044375061565874523449424623⟩,⟨-381186939982665997204627535420101085550660212905292066306987,-381186939982665997204627535420101085550660212007787876125167⟩⟩,
  ⟨⟨42526128733004569348934294027425715933541879674810855849377,42526128733004569348934294027425715933541884188432084780242⟩,⟨-607100304604663942637492387094525792213327545684508254174286,-607100304604663942637492387094525792213327541170871042109718⟩⟩,
  ⟨⟨309740452620390924462611119479835563004846063978111780002448,309740452620390924462611119479835563004846083429543008790431⟩,⟨-526855803397671773616560872029050303896874041140956332842642,-526855803397671773616560872029050303896874021689593723235379⟩⟩,
  ⟨⟨613004456196778685761592063819536537409760968296400831934949,613004456196778685761592063819536537409761042411604799453125⟩,⟨-456849968060734038620080407949651178552847648407384900168365,-456849968060734038620080407949651178552847574291984278979346⟩⟩,
  ⟨⟨973217603076608428958465219050453071392107198673660857745283,973217603076608428958465219050453071392107455009921322021447⟩,⟨-85251547340354678018038376846560435026242137270708542305871,-85251547340354678018038376846560435026241880934828837067870⟩⟩,
  ⟨⟨881104183903313356849043297310709158045419908512806056780455,881104183903313356849043297310709158045420731974629801378128⟩,⟨410976297997245055461030110569485862966928351105015857957293,410976297997245055461030110569485862966929174567823962094835⟩⟩,
  ⟨⟨747258535260107629183722599194757550390940690958699024136991,747258535260107629183722599194757550390943198083799088383764⟩,⟨694271868802801645833572922671994030574529998126355690101929,694271868802801645833572922671994030574532505248030938150679⟩⟩,
  ⟨⟨515326178143969869791379336022821403248060878803180267901860,515326178143969869791379336022821403248068238212617869365945⟩,⟨1192024815138059185542968415968115033644867714728197058047435,1192024815138059185542968415968115033644875074146050635023917⟩⟩,
  ⟨⟨-260902243696474705934731452710099736859428924177386095909747,-260902243696474705934731452710099736859407811812226546746985⟩,⟨1418341086086638108125565285911980755702865535116597169396061,1418341086086638108125565285911980755702886647467316647842496⟩⟩,
  ⟨⟨-787518037653591518317529097894762201208413534789144057194991,-787518037653591518317529097894762201208353761887031850160319⟩,⟨1113405382887101827566158704131505197060832890956619645866471,1113405382887101827566158704131505197060892663879759573895379⟩⟩,
  ⟨⟨-1305552494241480659616681533352383178504853387043380855649583,-1305552494241480659616681533352383178504685316193973235773930⟩,⟨870766477547492771885223515006479966583789104583413672925025,870766477547492771885223515006479966583957175406313822248496⟩⟩,
  ⟨⟨-1678229438519403166598170136390244418672365853545498562219756,-1678229438519403166598170136390244418671894789525608488010864⟩,⟨-235532024325923238987,235532024325923250068⟩⟩,
  ⟨⟨-1305552494241480659616681533352383178505428592179541918609272,-1305552494241480659616681533352383178504110111057812172812126⟩,⟨-870766477547492771885223515006479966584532380540854062464459,-870766477547492771885223515006479966583213899448873432691696⟩⟩,
  ⟨⟨-787518037653591518317529097894762201210227860433890504189687,-787518037653591518317529097894762201206539436242285403157428⟩,⟨-1113405382887101827566158704131505197062706989528293933847309,-1113405382887101827566158704131505197059018565308085285909172⟩⟩,
  ⟨⟨-260902243696474705934731452710099736864576583527203446692233,-260902243696474705934731452710099736854260152462409195946649⟩,⟨-1418341086086638108125565285911980755708034306812214179050904,-1418341086086638108125565285911980755697717875771699638199446⟩⟩,
  ⟨⟨515326178143969869791379336022821403233637967505998365720918,515326178143969869791379336022821403262491149509799771578144⟩,⟨-1192024815138059185542968415968115033659297985448199721059600,-1192024815138059185542968415968115033630444803426047972043374⟩⟩,
  ⟨⟨747258535260107629183722599194757550350594027238850253126245,747258535260107629183722599194757550431289861803647859441337⟩,⟨-694271868802801645833572922671994030614879168963566003786739,-694271868802801645833572922671994030534183334410820624516366⟩⟩,
  ⟨⟨881104183903313356849043297310709157932576753625880065166559,881104183903313356849043297310709158158263886861555793052812⟩,⟨-410976297997245055461030110569485863079772329457177071877569,-410976297997245055461030110569485862854085196215662748242890⟩⟩,
  ⟨⟨973217603076608428958465219050453071076510883519779787642753,973217603076608428958465219050453071707703770163802392195541⟩,⟨85251547340354678018038376846560434710645565782374784141937,85251547340354678018038376846560435341838452423162595147454⟩⟩,
  ⟨⟨613004456196778685761592063819536536527113457927827404204261,613004456196778685761592063819536538292408552780178227260656⟩,⟨456849968060734038620080407949651177670200063923475221344020,456849968060734038620080407949651179435495158775893957707135⟩⟩,
  ⟨⟨309740452620390924462611119479835560536292688316990889954393,309740452620390924462611119479835565473399459090663898914184⟩,⟨526855803397671773616560872029050301428320646029771808223524,526855803397671773616560872029050306365427416800778247748973⟩⟩,
  ⟨⟨42526128733004569348934294027425709029590463334956857750034,42526128733004569348934294027425722837493300528286082949395⟩,⟨607100304604663942637492387094525785309376124833014624433556,607100304604663942637492387094525799117278962022364671738379⟩⟩,
  ⟨⟨-301555303566433744803763851245664063683756870268597624130420,-301555303566433744803763851245664025066366262377953844416414⟩,⟨381186939982665997204627535420101066241964908515370418651668,381186939982665997204627535420101104859355516397709523662793⟩⟩,
  ⟨⟨-273946262714078519363244623147248596330457556985196009238792,-273946262714078519363244623147248488326883456027784988091771⟩,⟨108918766188261799001159249611462692690860059102025734585244,108918766188261799001159249611462800694434160043359274620738⟩⟩,
  ⟨⟨-192745854186654778030905517416873754064864843597441218223498,-192745854186654778030905517416873452004786861013315871686098⟩,⟨-986518410711267646848346420326328566626095169241646039328,-986518410711267646848346420326026506548112616663282167753⟩⟩,
  ⟨⟨-120842622615757954989806784943385906172263414945360694022736,-120842622615757954989806784943385061382713899553872951225784⟩,⟨-84614915292584877405267514585931143541554520129201171465061,-84614915292584877405267514585930298752005004799471417888058⟩⟩,
  ⟨⟨-1181336818385429267109384281,1181336818385429268828831583⟩,⟨-87266462599716478846184538424431817008961979795880611680030,-87266462599716478846184538424429454335325209058291888462391⟩⟩]
lemma dBox1_calc (j : Fin 31) : dCoeffBox phaseBox1 restBox1 j = dBox1 j := by
  revert j
  decide +kernel
lemma dBox1_mem (j : Fin 31) : (dBox1 j).Mem (dCoefficient ⟨1,by norm_num⟩ j) := by
  rw [← dBox1_calc]
  apply dCoeffBox_mem ⟨1,by norm_num⟩ phaseBox1 restBox1
  · have hr : residue ⟨1,by norm_num⟩ = (1:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox1_mem
  · exact restBox1_mem
def restBox3 : Fin 31 → CI :=
  ![⟨⟨866025403784438646763723170752936183471402626904696439157358,866025403784438646763723170752936183471402626905674474092415⟩,⟨-500000000000000000000000000000000000000000000000497877387218,-499999999999999999999999999999999999999999999999518949217189⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999990032334660266,1000000000000000000000000000000000000000000000009988141106391⟩,⟨267949192431122706472553658494127633057194746179631476965235,267949192431122706472553658494127633057194746199588207926258⟩⟩,
  ⟨⟨1133974596215561353236276829247063816528597372981397206321753,1133974596215561353236276829247063816528597373208241485492006⟩,⟨-35898384862245412945107316988255266114389492492661997556718,-35898384862245412945107316988255266114389492265819068737019⟩⟩,
  ⟨⟨1196152422706631880582339024517617100828415760520179621310291,1196152422706631880582339024517617100828415762342148446289059⟩,⟨1535898384862245412945107316988255266114389491468253488335434,1535898384862245412945107316988255266114389493290228165632572⟩⟩,
  ⟨⟨-392304845413263761164678049035234201656831528580188162952852,-392304845413263761164678049035234201656831517144335800862852⟩,⟨2464101615137754587054892683011744733885610501902858717675095,2464101615137754587054892683011744733885610513338715959914096⟩⟩,
  ⟨⟨-1875644347017858945307875609458893431400363253112890436202470,-1875644347017858945307875609458893431400363193541783305682768⟩,⟨1928203230275509174109785366023489467771220985456061655573675,1928203230275509174109785366023489467771221045027066345002388⟩⟩,
  ⟨⟨-2392304845413263761164678049035234201656831657317550418219571,-2392304845413263761164678049035234201656831388407061557885431⟩,⟨2143593539448981651780429267953021064457557835061488558695953,2143593539448981651780429267953021064457558103972488017567796⟩⟩,
  ⟨⟨-4464101615137754587054892683011744733885611052160262693703487,-4464101615137754587054892683011744733885609963081345194346195⟩,⟨516660498395404815856802439576340770256467754996242299553555,516660498395404815856802439576340770256468844073711844003905⟩⟩,
  ⟨⟨-3545517328095665711489259755694212514043352126249729979388515,-3545517328095665711489259755694212514043348051353169326499372⟩,⟨-2284609690826527522329356098070468403313665083174140388423850,-2284609690826527522329356098070468403313661008274997516838680⟩⟩,
  ⟨⟨-3176914536239791283494034147105702604970501788199945362052149,-3176914536239791283494034147105702604970487348973862413441285⟩,⟨-2535898384862245412945107316988255266114396711989388436125008,-2535898384862245412945107316988255266114382272769165799092074⟩⟩,
  ⟨⟨-2555136271329086010033412194400169761972335401144076186132026,-2555136271329086010033412194400169761972285969303049969420724⟩,⟨-5143593539448981651780429267953021064457582685448988505361385,-5143593539448981651780429267953021064457533253585038050608633⟩⟩,
  ⟨⟨1143593539448981651780429267953021064457475011089632556900541,1143593539448981651780429267953021064457640927944272339310034⟩,⟨-5837168574084177751131265854635064439684603796035472241239438,-5837168574084177751131265854635064439684437879242193846326432⟩⟩,
  ⟨⟨3607695154586736238835321950964765798342892836846901801248656,3607695154586736238835321950964765798343444117428616244260981⟩,⟨-3894882233484699542396180486870807927258560056510560540211167,-3894882233484699542396180486870807927258008775832844105313877⟩⟩,
  ⟨⟨5105117766515300457603819513129192072740803958203947216915473,5105117766515300457603819513129192072742627209452957368956193⟩,⟨-3444863728670913989966587805599830238028600940346665729648940,-3444863728670913989966587805599830238026777689206358010553516⟩⟩,
  ⟨⟨8698729810778067661813841462353190826426859284086074641111060,8698729810778067661813841462353190826432878025395055616403830⟩,⟨-3009370715122378170851,3009370715122378495923⟩⟩,
  ⟨⟨5105117766515300457603819513129192072731788062013407879663170,5105117766515300457603819513129192072751643105643496706222636⟩,⟨3444863728670913989966587805599830238017761793023632097392830,3444863728670913989966587805599830238037616836529391643525586⟩⟩,
  ⟨⟨3607695154586736238835321950964765798310426009706186379014139,3607695154586736238835321950964765798375910944569331666626908⟩,⟨3894882233484699542396180486870807927225541948683527116023814,3894882233484699542396180486870807927291026883659877530364827⟩⟩,
  ⟨⟨1143593539448981651780429267953021064349575117231453697541806,1143593539448981651780429267953021064565540821802451199068785⟩,⟨5837168574084177751131265854635064439576537985405609909566213,5837168574084177751131265854635064439792503689872056178969612⟩⟩,
  ⟨⟨-2555136271329086010033412194400169762328426473158101463041166,-2555136271329086010033412194400169761616194897289024691740326⟩,⟨5143593539448981651780429267953021064101442181544235270038084,5143593539448981651780429267953021064813673757489791286840515⟩⟩,
  ⟨⟨-3176914536239791283494034147105702606144921701418758301426843,-3176914536239791283494034147105702603796067435755049472944327⟩,⟨2535898384862245412945107316988255264939962359565111042708557,2535898384862245412945107316988255267288816625193443193098860⟩⟩,
  ⟨⟨-3545517328095665711489259755694212517916466982117947490387426,-3545517328095665711489259755694212510170233195484951814216117⟩,⟨2284609690826527522329356098070468399440546152402459046733516,2284609690826527522329356098070468407186779939046678858560786⟩⟩,
  ⟨⟨-4464101615137754587054892683011744746658674145638760331068782,-4464101615137754587054892683011744721112546869602847555869603⟩,⟨-516660498395404815856802439576340783029531937550894564913098,-516660498395404815856802439576340757483404661519059579278562⟩⟩,
  ⟨⟨-2392304845413263761164678049035234243780825163838415819255315,-2392304845413263761164678049035234159532837881886196156287694⟩,⟨-2143593539448981651780429267953021106581551610494144376561270,-2143593539448981651780429267953021022333564328539832200895695⟩⟩,
  ⟨⟨-1875644347017858945307875609458893570320115422498534182102234,-1875644347017858945307875609458893292480611024156139560047481⟩,⟨-1928203230275509174109785366023489606690973214412348808491998,-1928203230275509174109785366023489328851468816070779193506015⟩⟩,
  ⟨⟨-392304845413263761164678049035234659797094991202175168000071,-392304845413263761164678049035233743516568054522348796968062⟩,⟨-2464101615137754587054892683011745192025873975960829832497470,-2464101615137754587054892683011744275745347039280744846272739⟩⟩,
  ⟨⟨1196152422706631880582339024517615589938152269378556372125684,1196152422706631880582339024517618611718679253483771693642532⟩,⟨-1535898384862245412945107316988256777004652984431834183258565,-1535898384862245412945107316988253755224126000326647471185175⟩⟩,
  ⟨⟨1133974596215561353236276829247058833798262720243073238834656,1133974596215561353236276829247068799258932025946565450911297⟩,⟨35898384862245412945107316988250283384054839527487376244236,35898384862245412945107316988260248844724145230993690594343⟩⟩,
  ⟨⟨999999999999999999999999999999983567567951306417324286605584,1000000000000000000000000000000016432432048693582696187425078⟩,⟨-267949192431122706472553658494144065489243439772303280707662,-267949192431122706472553658494111200625146052606916402573352⟩⟩,
  ⟨⟨866025403784438646763723170752881991330769003257787799392142,866025403784438646763723170752990375612036250552583112990416⟩,⟨499999999999999999999999999999945807859366376352605653083397,500000000000000000000000000000054192140633623647411175929812⟩⟩,
  ⟨⟨-178719017230801457175936915294,178719017230801457175937260236⟩,⟨-178719017230801457180929741536,178719017230801457180932417157⟩⟩,
  ⟨⟨-589393346461127869114286582548,589393346461127869114288165778⟩,⟨-589393346461127869118689449433,589393346461127869118691726358⟩⟩]
lemma restBox3_calc (j : Fin 31) : recoverRest phaseBox3 restBox3 j = restBox3 j := by
  revert j
  decide +kernel
lemma restBox3_mem (j : Fin 31) : (restBox3 j).Mem ((restPolynomial ⟨2,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨2,by norm_num⟩ phaseBox3
  · have hr : residue ⟨2,by norm_num⟩ = (3:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox3_mem
  · exact restBox3_calc
def cBox3 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨26380642397055816535097180326270597663156998636365217531135,26380642397055816535097180326270597663156998636395178123378⟩,⟨-15230870989335429967337177468944677677953239826004081156957,-15230870989335429967337177468944677677953239825974164336873⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651674003513703,30461741978670859934674354937889355355906479652282086066131⟩,⟨8162199163230086799154349223237515385498962030890499607046,8162199163230086799154349223237515385498962031498468358507⟩⟩,
  ⟨⟨34542841560285903334251529549508113048655960664120268414546,34542841560285903334251529549508113048655960671030560222546⟩,⟨-1093527337124743630971520977530353093044684239855755441141,-1093527337124743630971520977530353093044684232945717712125⟩⟩,
  ⟨⟨36436886467651459471885662206066164555316073182621529662938,36436886467651459471885662206066164555316073238122105867080⟩,⟨46786140305131033532983053384364386126904403686616934735997,46786140305131033532983053384364386126904403742117755097349⟩⟩,
  ⟨⟨-11950288977961199074422614536353618398819187290964186611494,-11950288977961199074422614536353618398819186942608126573401⟩,⟨75060827609552406205714366367193035296721514719366139531590,75060827609552406205714366367193035296721515067722750001698⟩⟩,
  ⟨⟨-57135394142610607594080444562662607698492735125683487744903,-57135394142610607594080444562662607698492733311043429215990⟩,⟨58736429283092232607405667920718004525723589923836891411945,58736429283092232607405667920718004525723591738473839599284⟩⟩,
  ⟨⟨-72873772935302918943771324412132329110632150516484158423908,-72873772935302918943771324412132329110632142325001767473263⟩,⟨65297593305840694393234793785900123083991692153810260682257,65297593305840694393234793785900123083991700345308157122355⟩⟩,
  ⟨⟨-135984311566894126075063076242971746008534490785121338932540,-135984311566894126075063076242971746008534457609879493953867⟩,⟨15738378792692311349690879849469721412139395614781260660934,15738378792692311349690879849469721412139428789978232901438⟩⟩,
  ⟨⟨-108002634029356684526640672558645751518146681012554241328537,-108002634029356684526640672558645751518146556884105933380720⟩,⟨-69593190923928688050856761479541269831498155775803644164493,-69593190923928688050856761479541269831498031647276921859138⟩⟩,
  ⟨⟨-96774350891225317092616553484839565908270740576307491628901,-96774350891225317092616553484839565908270300732327565069270⟩,⟨-77247882283801893467657408322253741482811103288246826794015,-77247882283801893467657408322253741482810663444445539842948⟩⟩,
  ⟨⟨-77833901817569755716275226919259050841670148116350408327648,-77833901817569755716275226919259050841668642336363041531516⟩,⟨-156682819241853274197257858599568189151711888095836259409370,-156682819241853274197257858599568189151710382315150078421154⟩⟩,
  ⟨⟨34835851327169834458560438848010767728082689539372298495118,34835851327169834458560438848010767728087743655788469957974⟩,⟨-177810322989758322835542227120209410404404156163529334656166,-177810322989758322835542227120209410404399102048981427742909⟩⟩,
  ⟨⟨109896678936722240664274805215203803024798335007706046668806,109896678936722240664274805215203803024815127974544783232856⟩,⟨-118644897633720189712046973035446627769172601867213477479660,-118644897633720189712046973035446627769155808897450297316481⟩⟩,
  ⟨⟨155510780174317549700022221405557570433966341780917105481829,155510780174317549700022221405557570434021881190027732119890⟩,⟨-104936550054455403891770902708077081293797252388411475274061,-104936550054455403891770902708077081293741712982612436066387⟩⟩,
  ⟨⟨264978463038093889848207440456716595349195339411431168236273,264978463038093889848207440456716595349378680756223401317563⟩,⟨-91670674242226092776,91670674242226102765⟩⟩,
  ⟨⟨155510780174317549700022221405557570433691701877454414662226,155510780174317549700022221405557570434296521093490422939854⟩,⟨104936550054455403891770902708077081293467073079387755755520,104936550054455403891770902708077081294071892291636155606841⟩⟩,
  ⟨⟨109896678936722240664274805215203803023809338896479465284800,109896678936722240664274805215203803025804124085771364620788⟩,⟨118644897633720189712046973035446627768166812785961697216292,118644897633720189712046973035446627770161597978702077606229⟩⟩,
  ⟨⟨34835851327169834458560438848010767724795870813138481440555,34835851327169834458560438848010767731374562382022287024605⟩,⟨177810322989758322835542227120209410401112283323405429648661,177810322989758322835542227120209410407690974889105332779984⟩⟩,
  ⟨⟨-77833901817569755716275226919259050852517302472949950343385,-77833901817569755716275226919259050830821487979763499492388⟩,⟨156682819241853274197257858599568189140863227957734846998077,156682819241853274197257858599568189162559042453251490860074⟩⟩,
  ⟨⟨-96774350891225317092616553484839565944045616947391994109868,-96774350891225317092616553484839565872495424361243062554168⟩,⟨77247882283801893467657408322253741447035787073810597324326,77247882283801893467657408322253741518585979658881769330557⟩⟩,
  ⟨⟨-108002634029356684526640672558645751636128506405768859898583,-108002634029356684526640672558645751400164731490891314771595⟩,⟨69593190923928688050856761479541269713516206253930679347684,69593190923928688050856761479541269949479981169149886676845⟩⟩,
  ⟨⟨-135984311566894126075063076242971746397624243015946764725521,-135984311566894126075063076242971745619444705379054068127023⟩,⟨-15738378792692311349690879849469721801229181020763604048659,-15738378792692311349690879849469721023049643383995889533120⟩⟩,
  ⟨⟨-72873772935302918943771324412132330393802371823329520275513,-72873772935302918943771324412132327827461921018156405604495⟩,⟨-65297593305840694393234793785900124367161921652177612931228,-65297593305840694393234793785900121800821470846940804909777⟩⟩,
  ⟨⟨-57135394142610607594080444562662611930230381450410414175244,-57135394142610607594080444562662603466755086986316502793667⟩,⟨-58736429283092232607405667920718008757461238063189760738102,-58736429283092232607405667920718000293985943599120970316478⟩⟩,
  ⟨⟨-11950288977961199074422614536353632354569682929643949327113,-11950288977961199074422614536353604443068691303928363892837⟩,⟨-75060827609552406205714366367193049252472010706406377323496,-75060827609552406205714366367193021340971019080682512245773⟩⟩,
  ⟨⟨36436886467651459471885662206066118530966708629436170124419,36436886467651459471885662206066210579665437791307465349850⟩,⟨-46786140305131033532983053384364432151253768295302589732578,-46786140305131033532983053384364340102555039133432100115236⟩⟩,
  ⟨⟨34542841560285903334251529549507961266010157176099065759718,34542841560285903334251529549508264831301764159051762814384⟩,⟨1093527337124743630971520977530201310398880744924279740179,1093527337124743630971520977530504875690487727877193429708⟩⟩,
  ⟨⟨30461741978670859934674354937888854795401330306269893243792,30461741978670859934674354937889855916411628997686196283165⟩,⟨-8162199163230086799154349223238015946004111376902792613822,-8162199163230086799154349223237014824993812685486175302651⟩⟩,
  ⟨⟨26380642397055816535097180326268946876151745348066001833047,26380642397055816535097180326272248450162251924694393795037⟩,⟨15230870989335429967337177468943026890947986537674806797702,15230870989335429967337177468946328464958493114303438769523⟩⟩,
  ⟨⟨-5444092589566305490864327246,5444092589566305490864337753⟩,⟨-5444092589566305491016417430,5444092589566305491016498934⟩⟩]
lemma cBox3_calc (j : Fin 31) : cCoeffBox restBox3 j = cBox3 j := by
  revert j
  decide +kernel
lemma cBox3_mem (j : Fin 31) : (cBox3 j).Mem (cCoefficient ⟨2,by norm_num⟩ j) := by
  rw [← cBox3_calc]
  exact cCoeffBox_mem ⟨2,by norm_num⟩ restBox3 restBox3_mem j
def dBox3 : Fin 31 → CI :=
  ![⟨⟨-57553376622,59272815901⟩,⟨87266462599716478846184538424430635672143594427027726413884,87266462599716478846184538424430635672143594427144773589200⟩⟩,
  ⟨⟨-63883484419801675369988649712415675351528592915164813409672,-63883484419801675369988649712415675351528592912785472412528⟩,⟨63883484419801675369988649712415675351528592912786995933470,63883484419801675369988649712415675351528592915166250872993⟩⟩,
  ⟨⟨-122340929869588684060478371492453076153066096710332673449973,-122340929869588684060478371492453076153066096683173685658060⟩,⟨43633231299858239423092269212215317836071797199965343974023,43633231299858239423092269212215317836071797227123982778611⟩⟩,
  ⟨⟨-191650453259405026109965949137247026054585778851715610668774,-191650453259405026109965949137247026054585778632141491428845⟩,⟨-63883484419801675369988649712415675351528593023760913061179,-63883484419801675369988649712415675351528592804187447272732⟩⟩,
  ⟨⟨-221298881559262564644760854272891191985517192575542895317234,-221298881559262564644760854272891191985517191185252375724027⟩,⟨-221298881559262564644760854272891191985517192575539518297850,-221298881559262564644760854272891191985517191185249036264460⟩⟩,
  ⟨⟨-3659279797584541,3659272000464133⟩,⟨-383300906518810052219931898274494052109171561143134271015312,-383300906518810052219931898274494052109171553824578137375556⟩⟩,
  ⟨⟨145723908049503487536674260204468036473681081500050632623718,145723908049503487536674260204468036473681114919674882969381⟩,⟨-352198575458837282914037661909537145493732600230833697931909,-352198575458837282914037661909537145493732566811225114870516⟩⟩,
  ⟨⟨383300906518810052219931898274494052109171489019659069759819,383300906518810052219931898274494052109171625948051654998898⟩,⟨-302299894039036308432346376273692622047344443146350316862233,-302299894039036308432346376273692622047344306217908767860475⟩⟩,
  ⟨⟨593747710138043283505694896682628694994706312193017759914422,593747710138043283505694896682628694994706830010695034001761⟩,⟨-81001012479773743787585522000801430061827441710522248269854,-81001012479773743787585522000801430061826923892945512845455⟩⟩,
  ⟨⟨564099281838185744970899991546984529063774232412984430263652,564099281838185744970899991546984529063776083513798132104895⟩,⟨185385003139462291051366932713617820444268441566046087580085,185385003139462291051366932713617820444270292667091668392013⟩⟩,
  ⟨⟨482258858208483932804214381054932167941619463445470994226505,482258858208483932804214381054932167941625841889534610612101⟩,⟨398964531818666889866429439333567066134959397325625750910310,398964531818666889866429439333567066134965775768874484005865⟩⟩,
  ⟨⟨338213772458836582025740297832965993588581449486187949731371,338213772458836582025740297832965993588602949405719485037438⟩,⟨691866250677789095710877290971815879766821593830501700478230,691866250677789095710877290971815879766843093752181852605590⟩⟩,
  ⟨⟨-140297869079488820857175332272089761923725814007919819228619,-140297869079488820857175332272089761923654204149408164759152⟩,⟨860133725757279318344647351397047945500767316092802267063981,860133725757279318344647351397047945500838925947517723913392⟩⟩,
  ⟨⟨-453449841058554462648519564410538933071135124596116704132131,-453449841058554462648519564410538933070897999450265527544273⟩,⟨704397150917674565828075323819074290987346604466416153693731,704397150917674565828075323819074290987583729617700498008392⟩⟩,
  ⟨⟨-831324708607349848188952534752654710630588630641637432593240,-831324708607349848188952534752654710629805430110063082418413⟩,⟨554701106658271642383001466911540720647908940263036226791737,554701106658271642383001466911540720648692140787669199609009⟩⟩,
  ⟨⟨-966196538716824002366628939092366198005188065622451152095471,-966196538716824002366628939092366198002603835024186467293264⟩,⟨-1292115302852395923905,1292115302852395893723⟩⟩,
  ⟨⟨-831324708607349848188952534752654710634458942821596342067659,-831324708607349848188952534752654710625935117930104172965848⟩,⟨-554701106658271642383001466911540720652562452967353360051386,-554701106658271642383001466911540720644038628083352066405498⟩⟩,
  ⟨⟨-453449841058554462648519564410538933085072446039499986120912,-453449841058554462648519564410538933056960678006882245592743⟩,⟨-704397150917674565828075323819074291001521051062023133809238,-704397150917674565828075323819074290973409283022093517937295⟩⟩,
  ⟨⟨-140297869079488820857175332272089761970045103633426552130169,-140297869079488820857175332272089761877334914523901431900369⟩,⟨-860133725757279318344647351397047945547158215571894387637691,-860133725757279318344647351397047945454448026468425603368655⟩⟩,
  ⟨⟨338213772458836582025740297832965993435718407295472331422087,338213772458836582025740297832965993741465991596435103309007⟩,⟨-691866250677789095710877290971815879919706135944058652429430,-691866250677789095710877290971815879613958551638624900667879⟩⟩,
  ⟨⟨482258858208483932804214381054932167437463417010086688006308,482258858208483932804214381054932168445781888324918916808880⟩,⟨-398964531818666889866429439333567066639121822203265451152436,-398964531818666889866429439333567065630803350891234783765981⟩⟩,
  ⟨⟨564099281838185744970899991546984527401119821573169024549201,564099281838185744970899991546984530726430494353613537814436⟩,⟨-185385003139462291051366932713617822106924703507420476938893,-185385003139462291051366932713617818781614030725717279032108⟩⟩,
  ⟨⟨593747710138043283505694896682628689511473597878792263225304,593747710138043283505694896682628700477939544324920530702893⟩,⟨81001012479773743787585522000801424578594209578883299637399,81001012479773743787585522000801435545060156024584461474009⟩⟩,
  ⟨⟨383300906518810052219931898274494034026143299016833528034224,383300906518810052219931898274494070192199815950877196747072⟩,⟨302299894039036308432346376273692603964316116215029685358024,302299894039036308432346376273692640130372633149229399350435⟩⟩,
  ⟨⟨145723908049503487536674260204467976838077077791373129513586,145723908049503487536674260204468096109285118628352386104346⟩,⟨352198575458837282914037661909537085858128563102576928651814,352198575458837282914037661909537205129336603939481884124643⟩⟩,
  ⟨⟨-196670890247477338048124737,196670890247477330251024249⟩,⟨383300906518810052219931898274493855438281310006507796415149,383300906518810052219931898274494248780061804961204611940121⟩⟩,
  ⟨⟨-221298881559262564644760854272891840581933795336493790511131,-221298881559262564644760854272890543389100588424301480520059⟩,⟨221298881559262564644760854272890543389100588424302440206359,221298881559262564644760854272891840581933795336486114314525⟩⟩,
  ⟨⟨-191650453259405026109965949137249165045826934743286571274740,-191650453259405026109965949137244887063344622740570530824901⟩,⟨63883484419801675369988649712413536360287436912616160697714,63883484419801675369988649712417814342769748915332199593870⟩⟩,
  ⟨⟨-122340929869588684060478371492460130283204065679432215147624,-122340929869588684060478371492446022022928127714074143973211⟩,⟨-43633231299858239423092269212222371966209766196223128912221,-43633231299858239423092269212208263705933828230866197878557⟩⟩,
  ⟨⟨-63883484419801675369988649712438939005463196604387953178991,-63883484419801675369988649712392411697593989223562332663009⟩,⟨-63883484419801675369988649712438939005463196604389006695040,-63883484419801675369988649712392411697593989223564240141174⟩⟩,
  ⟨⟨-76720670558088461129672871711,76720670558088461131392289717⟩,⟨-87266462599716478846184538424507356342701682888216603652120,-87266462599716478846184538424353915001585505965955896370225⟩⟩]
lemma dBox3_calc (j : Fin 31) : dCoeffBox phaseBox3 restBox3 j = dBox3 j := by
  revert j
  decide +kernel
lemma dBox3_mem (j : Fin 31) : (dBox3 j).Mem (dCoefficient ⟨2,by norm_num⟩ j) := by
  rw [← dBox3_calc]
  apply dCoeffBox_mem ⟨2,by norm_num⟩ phaseBox3 restBox3
  · have hr : residue ⟨2,by norm_num⟩ = (3:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox3_mem
  · exact restBox3_mem
def restBox4 : Fin 31 → CI :=
  ![⟨⟨766044443118978035202392650555416673935832457079884379816046,766044443118978035202392650555416673935832457080893681400799⟩,⟨-642787609686539326322643409907263432907559884206194297184146,-642787609686539326322643409907263432907559884205184097598091⟩⟩,
  ⟨⟨694592710667721395406866507077259184001502708725950459214356,694592710667721395406866507077259184001502708746619945012527⟩,⟨-10342827125332,10327047811568⟩⟩,
  ⟨⟨624485151690003756755461324896935225807121693939080319847734,624485151690003756755461324896935225807121694175164719683479⟩,⟨-368945915932827368044695487312014399547051711525047209775293,-368945915932827368044695487312014399547051711288963053701272⟩⟩,
  ⟨⟨709140630618410393378777589590240772383502547827509094901566,709140630618410393378777589590240772383502549735231099682616⟩,⟨1285575219373078652645286819814526865815119767457502091747698,1285575219373078652645286819814526865815119769365225759571202⟩⟩,
  ⟨⟨-417403914311578336354838435718953550195132375081208194789277,-417403914311578336354838435718953550195132363013351128032336⟩,⟨2338561421957243486778181536491060426888338208812779894957904,2338561421957243486778181536491060426888338220880637915459682⟩⟩,
  ⟨⟨-1248970303380007513510922649793870451614243419863571977533248,-1248970303380007513510922649793870451614243356364890911097954⟩,⟨1940961697309137109203566155524044207672009457830802173403472,1940961697309137109203566155524044207672009521329448318036801⟩⟩,
  ⟨⟨-1056436985952271091082210843128870364384254048323586667971966,-1056436985952271091082210843128870364384253757975424228543402⟩,⟨2134626213883608677795709327008068941815713761556090663535191,2134626213883608677795709327008068941815714051904441853503744⟩⟩,
  ⟨⟨-2795607109568652581887619033417685387867908739819309190388717,-2795607109568652581887619033417685387867907544820949006642448⟩,⟨407870416147269617964944418965982970145248018734017961314442,407870416147269617964944418965982970145249213731815361265101⟩⟩,
  ⟨⟨-2194592710667721395406866507077259184001504988638448352052645,-2194592710667721395406866507077259184001500428834212324064155⟩,⟨-2375757886063565362169106447119781996601228729608479583535292,-2375757886063565362169106447119781996601224169803178327391760⟩⟩,
  ⟨⟨-2573977952239538163515085061726722123873927244223217552562296,-2573977952239538163515085061726722123873910710307276373387108⟩,⟨-2274439185243762976386660753232584038391489903051555695963735,-2274439185243762976386660753232584038391473369137907191098825⟩⟩,
  ⟨⟨-2788333149593308082901663492161194593676937267901275089223036,-2788333149593308082901663492161194593676879176693895990436807⟩,⟨-4194689588586428426605329165297306019302753102392731914665387,-4194689588586428426605329165297306019302695011176856596279324⟩⟩,
  ⟨⟨192533317427736422428711806665000087229889213150035834591007,192533317427736422428711806665000087230089756779445748295499⟩,⟨-4215400882552900085590226908756628246063591397477567469372517,-4215400882552900085590226908756628246063390853872147864415016⟩⟩,
  ⟨⟨2412189347576218810347037594874721852775302527378946895519409,2412189347576218810347037594874721852775988818213713706123130⟩,⟨-2130570001025132413421078418179534782910338436204506692629240,-2130570001025132413421078418179534782909652145329102575027828⟩⟩,
  ⟨⟨3889814375042535820123820236337926334710219894635308575635420,3889814375042535820123820236337926334712559427426676924811659⟩,⟨-2188477759097925947796901072267578579384820360887723356539638,-2188477759097925947796901072267578579382480828144202628053782⟩⟩,
  ⟨⟨7573044299142945062032276626054111049533785330878594295603305,7573044299142945062032276626054111049541748603053716905699829⟩,⟨-3981636113622586730025,3981636113622587461722⟩⟩,
  ⟨⟨3889814375042535820123820236337926334697844189089415525691116,3889814375042535820123820236337926334724935132972569975541008⟩,⟨2188477759097925947796901072267578579370105122601753594319143,2188477759097925947796901072267578579397196066430172391473168⟩⟩,
  ⟨⟨2412189347576218810347037594874721852729571750917835337560955,2412189347576218810347037594874721852821719594674825265328889⟩,⟨2130570001025132413421078418179534782863921368863011367682485,2130570001025132413421078418179534782956069212670597900484624⟩⟩,
  ⟨⟨192533317427736422428711806665000087073279613768973724019540,192533317427736422428711806665000087386699356160507860053516⟩,⟨4215400882552900085590226908756628245906781254502022035716260,4215400882552900085590226908756628246220200996847693297749299⟩⟩,
  ⟨⟨-2788333149593308082901663492161194594209914841908508898468356,-2788333149593308082901663492161194593143901602686662180572387⟩,⟨4194689588586428426605329165297306018769717437155928169524283,4194689588586428426605329165297306019835730676413660340479220⟩⟩,
  ⟨⟨-2573977952239538163515085061726722125686793587452566310470580,-2573977952239538163515085061726722122061044367077927615696409⟩,⟨2274439185243762976386660753232584036578607025916360934107271,2274439185243762976386660753232584040204356246273101951877088⟩⟩,
  ⟨⟨-2194592710667721395406866507077259190167491323778000991604884,-2194592710667721395406866507077259177835514093694659685480787⟩,⟨2375757886063565362169106447119781990435237834661565941888227,2375757886063565362169106447119782002767215064750091968376301⟩⟩,
  ⟨⟨-2795607109568652581887619033417685408839801177100841039759252,-2795607109568652581887619033417685366896015107539417158576253⟩,⟨-407870416147269617964944418965982991117141651012859416267193,-407870416147269617964944418965982949173355581452973906166038⟩⟩,
  ⟨⟨-1056436985952271091082210843128870435714306450294228513519835,-1056436985952271091082210843128870293054201356004782384045783⟩,⟨-2134626213883608677795709327008069013145766453875440281616770,-2134626213883608677795709327008068870485661359585092234410791⟩⟩,
  ⟨⟨-1248970303380007513510922649793870694223548117759128578977025,-1248970303380007513510922649793870209004938658469334309930640⟩,⟨-1940961697309137109203566155524044450281314219224816333748257,-1940961697309137109203566155524043965062704759935434156150143⟩⟩,
  ⟨⟨-417403914311578336354838435718954375363103355097316600888515,-417403914311578336354838435718952725027161382997242721229915⟩,⟨-2338561421957243486778181536491061252056309200896799680560928,-2338561421957243486778181536491059601720367228796618128397439⟩⟩,
  ⟨⟨709140630618410393378777589590237965804500608345493948984223,709140630618410393378777589590243578962504489217246247043874⟩,⟨-1285575219373078652645286819814529672394121708847232313682138,-1285575219373078652645286819814524059236117827975495536896764⟩⟩,
  ⟨⟨624485151690003756755461324896925680010422011271487922117095,624485151690003756755461324896944771603821376842757118978916⟩,⟨368945915932827368044695487312004853750352028621371807078809,368945915932827368044695487312023945343751394192638456062928⟩⟩,
  ⟨⟨694592710667721395406866507077226716633020059030275016887668,694592710667721395406866507077291651369985358442295388285179⟩,⟨-32467368482649706003209638324,32467368482649706018987669518⟩⟩,
  ⟨⟨766044443118978035202392650555306245225757039169817872347193,766044443118978035202392650555527102645907874990960188684716⟩,⟨642787609686539326322643409907153004197484466295118632238011,642787609686539326322643409907373861617635302116259760911137⟩⟩,
  ⟨⟨-375592497292700020722111969989,375592497292700020722110642124⟩,⟨-375592497292700020722063253452,375592497292700020722062091971⟩⟩,
  ⟨⟨-1277473257871277388862129844617,1277473257871277388862127912947⟩,⟨-1277473257871277388862116092042,1277473257871277388862116069556⟩⟩]
lemma restBox4_calc (j : Fin 31) : recoverRest phaseBox4 restBox4 j = restBox4 j := by
  revert j
  decide +kernel
lemma restBox4_mem (j : Fin 31) : (restBox4 j).Mem ((restPolynomial ⟨3,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨3,by norm_num⟩ phaseBox4
  · have hr : residue ⟨3,by norm_num⟩ = (4:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox4_mem
  · exact restBox4_calc
def cBox4 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨23335048170484914988453136141165932166689530925471369991158,23335048170484914988453136141165932166689530925502263631162⟩,⟨-19580430313357954872034103663248574042515901359362555589565,-19580430313357954872034103663248574042515901359331658497519⟩⟩,
  ⟨⟨21158503932625711660577912563591348779508349066591077148821,21158503932625711660577912563591348779508349067220840391269⟩,⟨-315060531222,314579865845⟩⟩,
  ⟨⟨19022905560292027148203397875765926271331786028172343959152,19022905560292027148203397875765926271331786035364007135730⟩,⟨-11238735295230177498455422922862826664475463368651476346283,-11238735295230177498455422922862826664475463361459870150680⟩⟩,
  ⟨⟨21601658916489958016749400216749190355793343262982881056958,21601658916489958016749400216749190355793343321095554054087⟩,⟨39160860626715909744068207326497148085031802689637355611586,39160860626715909744068207326497148085031802747750191053237⟩⟩,
  ⟨⟨-12714850338646540342663470969621096897930737752393996691233,-12714850338646540342663470969621096897930737384785967542922⟩,⟨71236654636935182005124223443450634439643411686550076528697,71236654636935182005124223443450634439643412054158507291123⟩⟩,
  ⟨⟨-38045811120584054296406795751531852542663573030676277380368,-38045811120584054296406795751531852542663571096395596541509⟩,⟨59125074413913984959846074110538630118742239627151362529417,59125074413913984959846074110538630118742241561431113784116⟩⟩,
  ⟨⟨-32180910882802813847038356498544864745547522247747482630740,-32180910882802813847038356498544864745547513403236469549574⟩,⟨65024432948229564068934758643956150365648921792069863860970,65024432948229564068934758643956150365648930636586835700744⟩⟩,
  ⟨⟨-85159062445418130629484555687021558452327646340510013820065,-85159062445418130629484555687021558452327609938777758828528⟩,⟨12424443377411235872378929598988968147988953111195515492406,12424443377411235872378929598988968147988989512910164066197⟩⟩,
  ⟨⟨-66851116900632001562589444970425381813368137994664201440015,-66851116900632001562589444970425381813367999095083664717544⟩,⟨-72369723729060850949380130035345095086138671827902371781602,-72369723729060850949380130035345095086138532928289351221381⟩⟩,
  ⟨⟨-78407852239908397467773141127718887502641837277274721908420,-78407852239908397467773141127718887502641333625392925515468⟩,⟨-69283379607073882943713190525738676973741082716764745100086,-69283379607073882943713190525738676973740579064952845648613⟩⟩,
  ⟨⟨-84937484953486007451398811860442637664186015806762699234014,-84937484953486007451398811860442637664184246247391746937189⟩,⟨-127777551928136805667194335637589149099039311909684515108860,-127777551928136805667194335637589149099037542350054480434448⟩⟩,
  ⟨⟨5864900237781240449368439252986987797112999783897117405259,5864900237781240449368439252986987797119108692191705722769⟩,⟨-128408454020987867903559264636277307092486125938932354241285,-128408454020987867903559264636277307092480017031367772382309⟩⟩,
  ⟨⟨73479489509565178277798732860480570126029801955687251582191,73479489509565178277798732860480570126050707570018712588640⟩,⟨-64900873638724093122624175705008525364534325102598926976923,-64900873638724093122624175705008525364513419487029637423169⟩⟩,
  ⟨⟨118490521837470569544970834409744724402317446785651263385886,118490521837470569544970834409744724402388713029893319977031⟩,⟨-66664844823700824303245011295591144004499340279227755035756,-66664844823700824303245011295591144004428074036443550252889⟩⟩,
  ⟨⟨230688121433536691022465447089643199439542397220200823347795,230688121433536691022465447089643199439784972362506805973619⟩,⟨-121287571946129047987,121287571946129070351⟩⟩,
  ⟨⟨118490521837470569544970834409744724401940461236508263295864,118490521837470569544970834409744724402765698579036320090923⟩,⟨66664844823700824303245011295591144004051088487405460896076,66664844823700824303245011295591144004876325828265844429167⟩⟩,
  ⟨⟨73479489509565178277798732860480570124636762842644596406857,73479489509565178277798732860480570127443746683061367801926⟩,⟨64900873638724093122624175705008525363120380373835293453113,64900873638724093122624175705008525365927364215793270962566⟩⟩,
  ⟨⟨5864900237781240449368439252986987792342398576168191787787,5864900237781240449368439252986987801889709899920631376300⟩,⟨128408454020987867903559264636277307087709415823971984961494,128408454020987867903559264636277307097256727146328141652297⟩⟩,
  ⟨⟨-84937484953486007451398811860442637680421441146589008337286,-84937484953486007451398811860442637647948820907565437815142⟩,⟨127777551928136805667194335637589149082802117009811009426113,127777551928136805667194335637589149115274737249927986088470⟩⟩,
  ⟨⟨-78407852239908397467773141127718887557864904066543710445411,-78407852239908397467773141127718887447418266836123936985150⟩,⟨69283379607073882943713190525738676918517512275921534881333,69283379607073882943713190525738677028964149505796055834472⟩⟩,
  ⟨⟨-66851116900632001562589444970425382001194822779695601758422,-66851116900632001562589444970425381625541314310052264428698⟩,⟨72369723729060850949380130035345094898311848143195207453267,72369723729060850949380130035345095273965356612996515529493⟩⟩,
  ⟨⟨-85159062445418130629484555687021559091168022569418787150648,-85159062445418130629484555687021557813487233709868985537669⟩,⟨-12424443377411235872378929598988968786829365741804078330620,-12424443377411235872378929598988967509148576882301601223579⟩⟩,
  ⟨⟨-32180910882802813847038356498544866918385173841648787555553,-32180910882802813847038356498544862572709861809335164656712⟩,⟨-65024432948229564068934758643956152538486582230499002751681,-65024432948229564068934758643956148192811270198157696779245⟩⟩,
  ⟨⟨-38045811120584054296406795751531859932965614362710824467245,-38045811120584054296406795751531845152361529764361049463015⟩,⟨-59125074413913984959846074110538637509044282893459916221105,-59125074413913984959846074110538622728440198295122560045484⟩⟩,
  ⟨⟨-12714850338646540342663470969621122033984558809008616348506,-12714850338646540342663470969621071761876916328171347864182⟩,⟨-71236654636935182005124223443450659575697233110774752356574,-71236654636935182005124223443450609303589590629933831418804⟩⟩,
  ⟨⟨21601658916489958016749400216749104862507943426898758811011,21601658916489958016749400216749275849078743157179676344043⟩,⟨-39160860626715909744068207326497233578317202583834051577799,-39160860626715909744068207326497062591746402853553495064467⟩⟩,
  ⟨⟨19022905560292027148203397875765635489735739446905115233216,19022905560292027148203397875766217052927832616631235909325⟩,⟨11238735295230177498455422922862535882879416780192676489515,11238735295230177498455422922863117446071509949918669997263⟩⟩,
  ⟨⟨21158503932625711660577912563590359766906904161134952283649,21158503932625711660577912563592337792109793972676965285256⟩,⟨-989012601444905770726648235,989012601444905771207274557⟩⟩,
  ⟨⟨23335048170484914988453136141162568315816176093977176663676,23335048170484914988453136141169296017562885756996456952997⟩,⟨19580430313357954872034103663245210191642546527837496914500,19580430313357954872034103663251937893389256190856717122854⟩⟩,
  ⟨⟨-11441201741654861532390186640,11441201741654861532390146191⟩,⟨-11441201741654861532388702650,11441201741654861532388667269⟩⟩]
lemma cBox4_calc (j : Fin 31) : cCoeffBox restBox4 j = cBox4 j := by
  revert j
  decide +kernel
lemma cBox4_mem (j : Fin 31) : (cBox4 j).Mem (cCoefficient ⟨3,by norm_num⟩ j) := by
  rw [← cBox4_calc]
  exact cCoeffBox_mem ⟨3,by norm_num⟩ restBox4 restBox4_mem j
def dBox4 : Fin 31 → CI :=
  ![⟨⟨-61335988179,63055427458⟩,⟨87266462599716478846184538424430635672143594427023925048585,87266462599716478846184538424430635672143594427148574954246⟩⟩,
  ⟨⟨-38962345218975078297758095199889543471863545038551833303255,-38962345218975078297758095199889543471863545036010353287715⟩,⟨46433514890609389663463594161459210988561205761973717378190,46433514890609389663463594161459210988561205764515162728764⟩⟩,
  ⟨⟨-96306404382542279143365458941938201307087263235465373886153,-96306404382542279143365458941938201307087263206315402763496⟩,⟨47288741911422358256006940368167163902478793046216315502016,47288741911422358256006940368167163902478793075366093968368⟩⟩,
  ⟨⟨-164681427509327871503793225800508945836502570138465118564352,-164681427509327871503793225800508945836502569901380238169132⟩,⟨-71140272112867288409087347456432251929765918873828194412247,-71140272112867288409087347456432251929765918636743643071795⟩⟩,
  ⟨⟨-192612808765084558286730917883876402614174527198130001245637,-192612808765084558286730917883876402614174525685435577640316⟩,⟨-180133492380935258173111726747349057649266006709920564139917,-180133492380935258173111726747349057649266005197226057778012⟩⟩,
  ⟨⟨-13531480489809717287620037663662634812830386699517068165393,-13531480489809717287620037663662634812830378658207357022005⟩,⟨-311888413301322945034931880590702964071398988912407574160020,-311888413301322945034931880590702964071398980871096456491571⟩⟩,
  ⟨⟨96306404382542279143365458941938201307087244630796738802841,96306404382542279143365458941938201307087281810982107267203⟩,⟨-293637450281380315362594123400925662349090694886749434460276,-293637450281380315362594123400925662349090657706565244061075⟩⟩,
  ⟨⟨329362855018655743007586451601017891673005062677664649917670,329362855018655743007586451601017891673005217402022402347355⟩,⟨-235147574006953356145101883235782925836654326399248428436730,-235147574006953356145101883235782925836654171674884679339598⟩⟩,
  ⟨⟨483881738840902475204256891041046937967327014360385252523699,483881738840902475204256891041046937967327610656588115341453⟩,⟨-62559705377458580100560785129457594730939179583140563009939,-62559705377458580100560785129457594730938583286952430952939⟩⟩,
  ⟨⟨480512802038173897223759639737864202696676237551049044637938,480512802038173897223759639737864202696678417210771667622804⟩,⟨119518843573414859720378920360427403156897855940808174710755,119518843573414859720378920360427403156900035600560152533052⟩⟩,
  ⟨⟨401106814948169913348511469762771371473066580689739835917033,401106814948169913348511469762771371473074283243175278833362⟩,⟨328869830808985104064572417765409300727690396584432340267883,328869830808985104064572417765409300727698099137764832534003⟩⟩,
  ⟨⟨263337548820061230134588281073803078575467485477687884484926,263337548820061230134588281073803078575494173812005523839513⟩,⟨548981043878214482827861742569021830146611711013670732982564,548981043878214482827861742569021830146638399348272277133707⟩⟩,
  ⟨⟨-116887035656925234893274285599668630415636393688088877388385,-116887035656925234893274285599668630415544876535596590951387⟩,⟨702462722466953660607521737278861906616068768314366488566048,702462722466953660607521737278861906616160285466332237369951⟩⟩,
  ⟨⟨-364494186657385914538182970894237759433254026641385685056314,-364494186657385914538182970894237759432941740025025708960188⟩,⟨606381090603516228990069350198336579334251105177390491943041,606381090603516228990069350198336579334563391794524121607853⟩⟩,
  ⟨⟨-702538288711068969573160229280421806368935320615150504822212,-702538288711068969573160229280421806367871910553732132283435⟩,⟨464514864869249154222048529093835087626439164273373723793110,464514864869249154222048529093835087627502574333792982484521⟩⟩,
  ⟨⟨-728988373314771829076365941788475518868004913829704509216440,-728988373314771829076365941788475518864386619503120285591789⟩,⟨-1809147163842521171360,1809147163842521156582⟩⟩,
  ⟨⟨-702538288711068969573160229280421806374557635577040680039044,-702538288711068969573160229280421806362249595591841957072827⟩,⟨-464514864869249154222048529093835087633124889295629595671665,-464514864869249154222048529093835087620816849311537110633298⟩⟩,
  ⟨⟨-364494186657385914538182970894237759454029720422533539144787,-364494186657385914538182970894237759412166046243877854880625⟩,⟨-606381090603516228990069350198336579355339085575826652896376,-606381090603516228990069350198336579313475411396087960676875⟩⟩,
  ⟨⟨-116887035656925234893274285599668630486784991395373874717031,-116887035656925234893274285599668630344396278828311593630402⟩,⟨-702462722466953660607521737278861906687308883173416370793424,-702462722466953660607521737278861906544920170607282355160387⟩⟩,
  ⟨⟨263337548820061230134588281073803078333332649478902443346565,263337548820061230134588281073803078817629009810790964974087⟩,⟨-548981043878214482827861742569021830388773235347259276158244,-548981043878214482827861742569021829904476875014683733973347⟩⟩,
  ⟨⟨401106814948169913348511469762771370649470571000186738690862,401106814948169913348511469762771372296670292932728376060531⟩,⟨-328869830808985104064572417765409301551294108827148472882746,-328869830808985104064572417765409299904094386895048699935326⟩⟩,
  ⟨⟨480512802038173897223759639737864199895431646918507475251495,480512802038173897223759639737864205497923007843313237012761⟩,⟨-119518843573414859720378920360427405958144626233190893901638,-119518843573414859720378920360427400355653265308177433362533⟩⟩,
  ⟨⟨483881738840902475204256891041046928439670329510506639545240,483881738840902475204256891041046947494984295506466728321270⟩,⟨62559705377458580100560785129457585203281898437099808457455,62559705377458580100560785129457604258595864432993185480426⟩⟩,
  ⟨⟨329362855018655743007586451601017859267333807598702567288492,329362855018655743007586451601017924078676472480984484971906⟩,⟨235147574006953356145101883235782893430982916595915321445908,235147574006953356145101883235782958242325581478217786304444⟩⟩,
  ⟨⟨96306404382542279143365458941938091088222840407995347926217,96306404382542279143365458941938311525951686033783498133350⟩,⟨293637450281380315362594123400925552130226253483768262602661,293637450281380315362594123400925772567955099109546415897323⟩⟩,
  ⟨⟨-13531480489809717287620037663663009691596147243796956896614,-13531480489809717287620037663662259934064618113927468302674⟩,⟨311888413301322945034931880590702589192633220326814446887146,311888413301322945034931880590703338950164749456689583751452⟩⟩,
  ⟨⟨-192612808765084558286730917883877677659873417383717136350221,-192612808765084558286730917883875127568475635499848442543025⟩,⟨180133492380935258173111726747347782603567115011639484226100,180133492380935258173111726747350332694964896895507137686354⟩⟩,
  ⟨⟨-164681427509327871503793225800513282549282079572755888821349,-164681427509327871503793225800504609123723060467089467910986⟩,⟨71140272112867288409087347456427915216986409202452788121019,71140272112867288409087347456436588642545428308119049360167⟩⟩,
  ⟨⟨-96306404382542279143365458941952951427611035953798227593934,-96306404382542279143365458941923451186563490487982549046326⟩,⟨-47288741911422358256006940368181914023002565793698971292794,-47288741911422358256006940368152413781955020327883438184174⟩⟩,
  ⟨⟨-38962345218975078297758095199939711898164173859584310227619,-38962345218975078297758095199839375045562916214977876350022⟩,⟨-46433514890609389663463594161509379414861834585547632463264,-46433514890609389663463594161409042562260576940941247658600⟩⟩,
  ⟨⟨-170633927595723044306530696515,170633927595723044308250146856⟩,⟨-87266462599716478846184538424601269599739317471393781034627,-87266462599716478846184538424260001744547871382778718992105⟩⟩]
lemma dBox4_calc (j : Fin 31) : dCoeffBox phaseBox4 restBox4 j = dBox4 j := by
  revert j
  decide +kernel
lemma dBox4_mem (j : Fin 31) : (dBox4 j).Mem (dCoefficient ⟨3,by norm_num⟩ j) := by
  rw [← dBox4_calc]
  apply dCoeffBox_mem ⟨3,by norm_num⟩ phaseBox4 restBox4
  · have hr : residue ⟨3,by norm_num⟩ = (4:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox4_mem
  · exact restBox4_mem
def restBox7 : Fin 31 → CI :=
  ![⟨⟨342020143325668733044099614682259580763083367513691103162557,342020143325668733044099614682259580763083367514612238733838⟩,⟨-939692620785908384054109277324731469936208134264928676323564,-939692620785908384054109277324731469936208134264007110431366⟩⟩,
  ⟨⟨-246513666864877417759498481296306482056545145758707866258727,-246513666864877417759498481296306482056545145740129038821682⟩,⟨246513666864877417759498481296306482056545145740135080714678,246513666864877417759498481296306482056545145758713026752619⟩⟩,
  ⟨⟨175886518778109536558524572450594315659981404517893873006913,175886518778109536558524572450594315659981404727007324883701⟩,⟨305567604364255416675318168040276472948042207022865735656495,305567604364255416675318168040276472948042207231984904021702⟩⟩,
  ⟨⟨1632871574706939350348720073353156457815871121949677148292397,1632871574706939350348720073353156457815871123609353032578964⟩,⟨1440935404311204426605243448647971429895524423650007856456401,1440935404311204426605243448647971429895524425309663066211543⟩⟩,
  ⟨⟨1109688700594969116086762247363932550155138358658768046617590,1109688700594969116086762247363932550155138368919082889904536⟩,⟨490680765332304413541039565847551542718045593517326417934072,490680765332304413541039565847551542718045603777666332861224⟩⟩,
  ⟨⟨-1249303987978785148392932270700133014746848192209638186224581,-1249303987978785148392932270700133014746848139792330365879377⟩,⟨-781269510372114663792792468177562062658431769749167708465714,-781269510372114663792792468177562062658431717331720907754349⟩⟩,
  ⟨⟨-2088980765480347785649045523925948407891981456154149400725228,-2088980765480347785649045523925948407891981225345187063447078⟩,⟨1196944014492146480511454820272565722183162482051152304209636,1196944014492146480511454820272565722183162712859004796133128⟩⟩,
  ⟨⟨-2889450827866001743028935483364600953764676299031221894598141,-2889450827866001743028935483364600953764675393036316026203526⟩,⟨2158440725242289687679159534245333208672239896760773002600677,2158440725242289687679159534245333208672240802760011110129898⟩⟩,
  ⟨⟨134933479342122020923095880818356301143238112200712119068805,134933479342122020923095880818356301143241374628356638760641⟩,⟨250441022487950603356984063488132476140545447423325542243169,250441022487950603356984063488132476140548709839556804763191⟩⟩,
  ⟨⟨901339404704036405765308325039959101351425788815958431086048,901339404704036405765308325039959101351436835644432522893597⟩,⟨-980714619102555931115762168789675922467388249604686280160567,-980714619102555931115762168789675922467377202748683973028599⟩⟩,
  ⟨⟨-1242950783778116894475798936050070671044289384323213530605367,-1242950783778116894475798936050070671044253474613720524194192⟩,⟨-4731659446453817158441276292761447091328023342518627366906282,-4731659446453817158441276292761447091327987432889996083940791⟩⟩,
  ⟨⟨-1829095289378406254482923044729394898601357708080230527128535,-1829095289378406254482923044729394898601243828387709840692170⟩,⟨-3993837815412523754966373456987727649181392994089861559804276,-3993837815412523754966373456987727649181279114164534634929931⟩⟩,
  ⟨⟨-841497024979908779662793480564746315319362357985849688565623,-841497024979908779662793480564746315319006051677524654746638⟩,⟨530984242622468915817790625379992691306302415007610956345819,530984242622468915817790625379992691306658720783680148072525⟩⟩,
  ⟨⟨2189862196111392626767932357097715556516959201621989257869140,2189862196111392626767932357097715556518066700851175967831808⟩,⟨1121008776750763536467085681576508492455144293967028948333875,1121008776750763536467085681576508492456251794194440653683579⟩⟩,
  ⟨⟨7802380657526412467914968299650453760035380967298305716689666,7802380657526412467914968299650453760038813574628130310088204⟩,⟨-1716302819765961135167,1716302819765961021998⟩⟩,
  ⟨⟨2189862196111392626767932357097715556512199278404885795032916,2189862196111392626767932357097715556522826624068279430455933⟩,⟨-1121008776750763536467085681576508492461011718263053318165161,-1121008776750763536467085681576508492450384369898416284043897⟩⟩,
  ⟨⟨-841497024979908779662793480564746315335629073012725816273574,-841497024979908779662793480564746315302739336650648527465682⟩,⟨-530984242622468915817790625379992691322925434006857952993064,-530984242622468915817790625379992691290035701784433151349953⟩⟩,
  ⟨⟨-1829095289378406254482923044729394898652188723628191062883116,-1829095289378406254482923044729394898550412812839749305213994⟩,⟨3993837815412523754966373456987727649130448095636943922820052,3993837815412523754966373456987727649232224012617452272468790⟩⟩,
  ⟨⟨-1242950783778116894475798936050070671201737039477009808285491,-1242950783778116894475798936050070670886805819459924246128585⟩,⟨4731659446453817158441276292761447091170539782248507502325994,4731659446453817158441276292761447091485470993160115949187806⟩⟩,
  ⟨⟨901339404704036405765308325039959100864180011495495472791986,901339404704036405765308325039959101838682612964895482039638⟩,⟨980714619102555931115762168789675921980131418830792878115053,980714619102555931115762168789675922954634033522577375035815⟩⟩,
  ⟨⟨134933479342122020923095880818356299635523641645327058784866,134933479342122020923095880818356302650955845183741699322629⟩,⟨-250441022487950603356984063488132477648263170849759277043524,-250441022487950603356984063488132474632830986413123070845122⟩⟩,
  ⟨⟨-2889450827866001743028935483364600958430044774322278000384363,-2889450827866001743028935483364600949099306917745259921299820⟩,⟨-2158440725242289687679159534245333213337609291833276486697713,-2158440725242289687679159534245333204006871407687507626658554⟩⟩,
  ⟨⟨-2088980765480347785649045523925948422328164781181657040907853,-2088980765480347785649045523925948393455797900317679424343372⟩,⟨-1196944014492146480511454820272565736619346017995368371490963,-1196944014492146480511454820272565707746979176914788728133865⟩⟩,
  ⟨⟨-1249303987978785148392932270700133059417139682914314008410441,-1249303987978785148392932270700132970076556649087654543428129⟩,⟨781269510372114663792792468177562017988140197924245102052322,781269510372114663792792468177562107328723289156643515617571⟩⟩,
  ⟨⟨1109688700594969116086762247363932411930589368109148567877701,1109688700594969116086762247363932688379687359468702370203153⟩,⟨-490680765332304413541039565847551680942594552911405273019935,-490680765332304413541039565847551404493496644383587477453345⟩⟩,
  ⟨⟨1632871574706939350348720073353156030103732222742778957314150,1632871574706939350348720073353156885528010022816251224439768⟩,⟨-1440935404311204426605243448647971857607663384275929656845514,-1440935404311204426605243448647971002183385464683741267278267⟩⟩,
  ⟨⟨175886518778109536558524572450592992178189284207505999186556,175886518778109536558524572450595639141773525037395197500813⟩,⟨-305567604364255416675318168040277796429834241315060918697889,-305567604364255416675318168040275149466250172939789722409709⟩⟩,
  ⟨⟨-246513666864877417759498481296310577343759380164147380848626,-246513666864877417759498481296302386769330911334689526186215⟩,⟨-246513666864877417759498481296310577343759504582308355369232,-246513666864877417759498481296302386769330786916539751387109⟩⟩,
  ⟨⟨342020143325668733044099614682246908599803073492178609074678,342020143325668733044099614682272252926363661536124732756409⟩,⟨939692620785908384054109277324718797772928019766570089464509,939692620785908384054109277324744142099488248762365699560901⟩⟩,
  ⟨⟨-39211833943912350493900778248,39211833943912350493902982417⟩,⟨-39211833944171387398005210764,39211833944171387398006150440⟩⟩,
  ⟨⟨-121334288965435312593627614730,121334288965435312593629313862⟩,⟨-121334288965061545913201840468,121334288965061545913200018092⟩⟩]
lemma restBox7_calc (j : Fin 31) : recoverRest phaseBox7 restBox7 j = restBox7 j := by
  revert j
  decide +kernel
lemma restBox7_mem (j : Fin 31) : (restBox7 j).Mem ((restPolynomial ⟨4,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨4,by norm_num⟩ phaseBox7
  · have hr : residue ⟨4,by norm_num⟩ = (7:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox7_mem
  · exact restBox7_calc
def cBox7 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨10418529357494547381300296597045329845068072893287803787370,10418529357494547381300296597045329845068072893315929507905⟩,⟨-28624674153641342903597614282063769361566618192227664229079,-28624674153641342903597614282063769361566618192199409496302⟩⟩,
  ⟨⟨-7509235714253920232838064955834716248347259132562987419194,-7509235714253920232838064955834716248347259131996996166254⟩,⟨7509235714253920232838064955834716248347259131997180212836,7509235714253920232838064955834716248347259132563144616826⟩⟩,
  ⟨⟨5357809752545419755764515889149380569211502603878860165129,5357809752545419755764515889149380569211502610248854289353⟩,⟨9308121521184528291954824159550550848464515168299328735854,9308121521184528291954824159550550848464515174669522142738⟩⟩,
  ⟨⟨49740112593028765574357163608292822474785977226868545977842,49740112593028765574357163608292822474785977277425481188632⟩,⟨43893402494059683888866544216759155523444029429723315439943,43893402494059683888866544216759155523444029480279583647177⟩⟩,
  ⟨⟨33803050874170489988303691437347767515820299955356646671301,33803050874170489988303691437347767515820300267903925244362⟩,⟨14946990867449402539614548792702473980315691853579131451891,14946990867449402539614548792702473980315692166127053709378⟩⟩,
  ⟨⟨-38055975734734274920007803100166521663631428322898542959083,-38055975734734274920007803100166521663631426726175794647268⟩,⟨-23798830240757874067377565132660970840774551580566094937794,-23798830240757874067377565132660970840774549983839203805733⟩⟩,
  ⟨⟨-63633993076468696976011006099943188745384411788441831054304,-63633993076468696976011006099943188745384404757598368864753⟩,⟨36460999732374240580091803746531394625031629001370789669331,36460999732374240580091803746531394625031636032180271047401⟩⟩,
  ⟨⟨-88017705578511054248272639605993386190225719676074503945904,-88017705578511054248272639605993386190225692077890887054495⟩,⟨65749864448585831403947273135173936122999424590181578278377,65749864448585831403947273135173936122999452188497020959013⟩⟩,
  ⟨⟨4110308832004035653488103502900775162587179721767121001310,4110308832004035653488103502900775162587279100996278610145⟩,⟨7628869807902457741455914363961597237620502005939169594733,7628869807902457741455914363961597237620601384820681908320⟩⟩,
  ⟨⟨27456368381303148941700505651964321648584504721212232143052,27456368381303148941700505651964321648584841226851067354720⟩,⟨-29874275681812530839267214391716508155935840223414489547522,-29874275681812530839267214391716508155935503716937081550632⟩⟩,
  ⟨⟨-37862446067635710723853266524430712285886367692057808841194,-37862446067635710723853266524430712285885273819752462812432⟩,⟨-144134589188816766120776605320194517972889934444950792350903,-144134589188816766120776605320194517972888840575107958728205⟩⟩,
  ⟨⟨-55717428759447322075265775556947068802152507916101316961383,-55717428759447322075265775556947068802149038942290786729173⟩,⟨-121659257037754796029528978434130885369024549572342570547865,-121659257037754796029528978434130885369021080591439936950606⟩⟩,
  ⟨⟨-25633465250757128519271554480928865854432441362051549245719,-25633465250757128519271554480928865854421587651221816132814⟩,⟨16174704993505614233285762222089071561655631438729284378839,16174704993505614233285762222089071561666485133345517146951⟩⟩,
  ⟨⟨66707017186790767952685539845954535442870471739582161628465,66707017186790767952685539845954535442904208095343648721099⟩,⟨34147880113207203937091553486344969025766748189463291879653,34147880113207203937091553486344969025800484575632243940518⟩⟩,
  ⟨⟨237674106408941864895840587583179054262162347063678734449317,237674106408941864895840587583179054262266910262475458636615⟩,⟨-52281573652975945245,52281573652975941876⟩⟩,
  ⟨⟨66707017186790767952685539845954535442725476186704471025250,66707017186790767952685539845954535443049203648221339317876⟩,⟨-34147880113207203937091553486344969025945480154448388136706,-34147880113207203937091553486344969025621752610647147689257⟩⟩,
  ⟨⟨-25633465250757128519271554480928865854927953838040817870702,-25633465250757128519271554480928865853926075175232547520827⟩,⟨-16174704993505614233285762222089071562161997554390992855835,-16174704993505614233285762222089071561160119017683808667676⟩⟩,
  ⟨⟨-55717428759447322075265775556947068803700909196237097577474,-55717428759447322075265775556947068800600637662155006121580⟩,⟨121659257037754796029528978434130885367472679220539430710539,121659257037754796029528978434130885370572950943243076804791⟩⟩,
  ⟨⟨-37862446067635710723853266524430712290682497538499498282761,-37862446067635710723853266524430712281089143973310773359217⟩,⟨144134589188816766120776605320194517968092710866119022052586,144134589188816766120776605320194517977686064153939729046808⟩⟩,
  ⟨⟨27456368381303148941700505651964321633742149572279371617639,27456368381303148941700505651964321663427196375783927906067⟩,⟨29874275681812530839267214391716508141093148367035067404713,29874275681812530839267214391716508170778195573316503692296⟩⟩,
  ⟨⟨4110308832004035653488103502900775116659570542200637705282,4110308832004035653488103502900775208514888280562761914647⟩,⟨-7628869807902457741455914363961597283548210273624276069280,-7628869807902457741455914363961597191692893117135575460645⟩⟩,
  ⟨⟨-88017705578511054248272639605993386332340970405815732282030,-88017705578511054248272639605993386048110441348149658745209⟩,⟨-65749864448585831403947273135173936265114703338068351997783,-65749864448585831403947273135173935980884173440610247258723⟩⟩,
  ⟨⟨-63633993076468696976011006099943189185135703392220535544335,-63633993076468696976011006099943188305633113153819664407565⟩,⟨-36460999732374240580091803746531395064782927030040077374200,-36460999732374240580091803746531394185280338003510983320702⟩⟩,
  ⟨⟨-38055975734734274920007803100166523024366321824760872083989,-38055975734734274920007803100166520302896533224313465514293⟩,⟨23798830240757874067377565132660969480039655607639587517554,23798830240757874067377565132660972201509445956765711270113⟩⟩,
  ⟨⟨33803050874170489988303691437347763305259753487084465797656,33803050874170489988303691437347771726380846736176106165498⟩,⟨-14946990867449402539614548792702478190876237372799367797300,-14946990867449402539614548792702469769755146646906817354136⟩⟩,
  ⟨⟨49740112593028765574357163608292809445929160933796126885211,49740112593028765574357163608292835503642793570497900308176⟩,⟨-43893402494059683888866544216759168552300847593726463738455,-43893402494059683888866544216759142494587211316276435392978⟩⟩,
  ⟨⟨5357809752545419755764515889149340253650637566079382875187,5357809752545419755764515889149420884772367648048331542649⟩,⟨-9308121521184528291954824159550591164025377585834874065046,-9308121521184528291954824159550510532903652757133976857084⟩⟩,
  ⟨⟨-7509235714253920232838064955834840997929707690794409166329,-7509235714253920232838064955834591498764810573765574478649⟩,⟨-7509235714253920232838064955834840997929711480788326232914,-7509235714253920232838064955834591498764806783771998575095⟩⟩,
  ⟨⟨10418529357494547381300296597044943828899916989465883810347,10418529357494547381300296597045715861236228797137849482920⟩,⟨28624674153641342903597614282063383345398467756993555540937,28624674153641342903597614282064155377734768627433518253615⟩⟩,
  ⟨⟨-1194460768109945792950781064,1194460768109945792950848207⟩,⟨-1194460768117836508286563994,1194460768117836508286592618⟩⟩]
lemma cBox7_calc (j : Fin 31) : cCoeffBox restBox7 j = cBox7 j := by
  revert j
  decide +kernel
lemma cBox7_mem (j : Fin 31) : (cBox7 j).Mem (cCoefficient ⟨4,by norm_num⟩ j) := by
  rw [← cBox7_calc]
  exact cCoeffBox_mem ⟨4,by norm_num⟩ restBox7 restBox7_mem j
def dBox7 : Fin 31 → CI :=
  ![⟨⟨-50906230822,52625670101⟩,⟨87266462599716478846184538424430635672143594427034322360779,87266462599716478846184538424430635672143594427138177642275⟩⟩,
  ⟨⟨12857354874567913519841347642504362883216142939672660061547,12857354874567913519841347642504362883216142941750919308168⟩,⟨-27572686507958198513147578351026046405028879840484576875770,-27572686507958198513147578351026046405028879838406316759717⟩⟩,
  ⟨⟨-79637379670349583992794578166399770257764864418094730890415,-79637379670349583992794578166399770257764864394601136846005⟩,⟨47041994810902043904089784075808370606840687191941990873560,47041994810902043904089784075808370606840687215435829944856⟩⟩,
  ⟨⟨-149336181839478271622650209607928595407769882778170655945566,-149336181839478271622650209607928595407769882590455731611585⟩,⟨-82283183723363853841780708012936955700962478189876136723454,-82283183723363853841780708012936955700962478002162557550507⟩⟩,
  ⟨⟨-110946913346870379921289029357933553247009749699602350298043,-110946913346870379921289029357933553247009748528589057016026⟩,⟨-37424184198063284701723429399378371912813499259205647570713,-37424184198063284701723429399378371912813498088191001470153⟩⟩,
  ⟨⟨34871958806900217767181397003796513891332384743442562863524,34871958806900217767181397003796513891332390791987987906139⟩,⟨-140118983056299762701352785020324224329480601749917678825444,-140118983056299762701352785020324224329480595701365773894360⟩⟩,
  ⟨⟨59225764535476959834945930558390873542060228968576877061987,59225764535476959834945930558390873542060255932275215471376⟩,⟨-233861722824026611984891540336725309174974970023971013679618,-233861722824026611984891540336725309174974943060328756222192⟩⟩,
  ⟨⟨251651802984221159988421230709758327497339493561837340036218,251651802984221159988421230709758327497339600760897062323279⟩,⟨-161886346707445246676559305981991369784561781298776643180508,-161886346707445246676559305981991369784561674099484048751043⟩⟩,
  ⟨⟨188489180423934660731141422275046334749853636937437277397718,188489180423934660731141422275046334749854027657462858952712⟩,⟨-52313937869636745271689587136145061116754932740448493428106,-52313937869636745271689587136145061116754542021076539910633⟩⟩,
  ⟨⟨256726413310086561297183187145562146834857678546172488283743,256726413310086561297183187145562146834859015476864498744458⟩,⟨16565451157827194514200858984828854779076553066644286286222,16565451157827194514200858984828854779077889998997245210405⟩⟩,
  ⟨⟨239561659206079747230586298432101351708054946035130098045539,239561659206079747230586298432101351708059327457031493346358⟩,⟨326350714114826777905596572153666713233787554907585910877682,326350714114826777905596572153666713233791936324674957807264⟩⟩,
  ⟨⟨166011720439607261140270631775496585393004052961139655851956,166011720439607261140270631775496585393018026067621103166372⟩,⟨326436482826874819126047531568882090998387794563617920545645,326436482826874819126047531568882090998401767683678167843043⟩⟩,
  ⟨⟨13858793513509547446850748240510488772503023037220484427199,13858793513509547446850748240510488772546892591918293575120⟩,⟨356452848551332215120554873932884519926223981295360249679320,356452848551332215120554873932884519926267850818081044990618⟩⟩,
  ⟨⟨-182246457101120321030550091126100444634115876962262167921662,-182246457101120321030550091126100444633979265034808020096722⟩,⟨355535843847510148051367987736493850798072964784689095281271,355535843847510148051367987736493850798209576776350441353578⟩⟩,
  ⟨⟨-554969644442649694436752473313240883218652065214051462336594,-554969644442649694436752473313240883218228273247757438588214⟩,⟨214450202981646454168531579929041947902953902226490751513736,214450202981646454168531579929041947903377694076862441149885⟩⟩,
  ⟨⟨-292236143387831555904771624423127477015099068958375160266568,-292236143387831555904771624423127477013786520121720529123568⟩,⟨-656274514802956987871,656274514802956997250⟩⟩,
  ⟨⟨-554969644442649694436752473313240883220471506003617041790804,-554969644442649694436752473313240883216408832458191859107989⟩,⟨-214450202981646454168531579929041947905197134772352954863538,-214450202981646454168531579929041947901134461531000237800455⟩⟩,
  ⟨⟨-182246457101120321030550091126100444640333753540604695623538,-182246457101120321030550091126100444627761388456465492377052⟩,⟨-355535843847510148051367987736493850804427453554512797282097,-355535843847510148051367987736493850791855088006526739384445⟩⟩,
  ⟨⟨13858793513509547446850748240510488753072977290209393107262,13858793513509547446850748240510488791976938338929384880817⟩,⟨-356452848551332215120554873932884519945697896235669707934543,-356452848551332215120554873932884519906793935877771586771996⟩⟩,
  ⟨⟨166011720439607261140270631775496585332819873373378158536069,166011720439607261140270631775496585453202205655382600452765⟩,⟨-326436482826874819126047531568882091058585947770948024867415,-326436482826874819126047531568882090938203614476348063529932⟩⟩,
  ⟨⟨239561659206079747230586298432101351521805665183530474562151,239561659206079747230586298432101351894308608308631116821575⟩,⟨-326350714114826777905596572153666713420041216443081393524805,-326350714114826777905596572153666713047538274789179475145665⟩⟩,
  ⟨⟨256726413310086561297183187145562146258534996560692474211663,256726413310086561297183187145562147411181697462344512836574⟩,⟨-16565451157827194514200858984828855355400573047413175544149,-16565451157827194514200858984828854202753870018228355949791⟩⟩,
  ⟨⟨188489180423934660731141422275046332966520075732009789612954,188489180423934660731141422275046336533187588862890346755386⟩,⟨52313937869636745271689587136145059333420982350952561999586,52313937869636745271689587136145062900088492410572471312133⟩⟩,
  ⟨⟨251651802984221159988421230709758321979119333525636952490332,251651802984221159988421230709758333015559760797097449857820⟩,⟨161886346707445246676559305981991364266341511847403106626424,161886346707445246676559305981991375302781943550857585271812⟩⟩,
  ⟨⟨59225764535476959834945930558390856466875038246887107545348,59225764535476959834945930558390890617245446653964984960480⟩,⟨233861722824026611984891540336725292099789755536214933117103,233861722824026611984891540336725326250160157548084836778154⟩⟩,
  ⟨⟨34871958806900217767181397003796461055102932204973042521349,34871958806900217767181397003796566727561843330457508240900⟩,⟨140118983056299762701352785020324171493251138548995911511508,140118983056299762701352785020324277165710058902287541227209⟩⟩,
  ⟨⟨-110946913346870379921289029357933716739651848511697757886028,-110946913346870379921289029357933389754367649716493649404917⟩,⟨37424184198063284701723429399378208420171405933551315748748,37424184198063284701723429399378535405455591413845333300490⟩⟩,
  ⟨⟨-149336181839478271622650209607929101307685400908173327637356,-149336181839478271622650209607928089507854364460453059896571⟩,⟨82283183723363853841780708012936449801046950266056423690372,82283183723363853841780708012937461600878005925982270559993⟩⟩,
  ⟨⟨-79637379670349583992794578166401335678209759664557109059879,-79637379670349583992794578166398204837319969148138758682943⟩,⟨-47041994810902043904089784075809936027285568601166108439314,-47041994810902043904089784075806805186395805806211712414112⟩⟩,
  ⟨⟨12857354874567913519841347642499518958372360996106785114326,12857354874567913519841347642509206808059924885316794228084⟩,⟨27572686507958198513147578351021202480185077895065798365325,27572686507958198513147578351030890329872681783825095258925⟩⟩,
  ⟨⟨-14988693912197598164293063394,14988693912197598166012490855⟩,⟨-87266462599716478846184538424445624366055763167396793605629,-87266462599716478846184538424415646978231425686775706381508⟩⟩]
lemma dBox7_calc (j : Fin 31) : dCoeffBox phaseBox7 restBox7 j = dBox7 j := by
  revert j
  decide +kernel
lemma dBox7_mem (j : Fin 31) : (dBox7 j).Mem (dCoefficient ⟨4,by norm_num⟩ j) := by
  rw [← dBox7_calc]
  apply dCoeffBox_mem ⟨4,by norm_num⟩ phaseBox7 restBox7
  · have hr : residue ⟨4,by norm_num⟩ = (7:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox7_mem
  · exact restBox7_mem
def restBox9 : Fin 31 → CI :=
  ![⟨⟨-370386070545,351503715615⟩,⟨-1000000000000000000000000000000000000000000000000360933449647,-999999999999999999999999999999999999999999999999639066584377⟩⟩,
  ⟨⟨-267949192431122706472553658494127633057194746196657705768465,-267949192431122706472553658494127633057194746182554673969061⟩,⟨999999999999999999999999999999999999999999999992944157237150,1000000000000000000000000000000000000000000000007046495526604⟩⟩,
  ⟨⟨1133974596215561353236276829247063816528597373017935845143496,1133974596215561353236276829247063816528597373171681568621576⟩,⟨35898384862245412945107316988255266114389492302355082754507,35898384862245412945107316988255266114389492456109481349218⟩⟩,
  ⟨⟨1535898384862245412945107316988255266114389491792008423429527,1535898384862245412945107316988255266114389492966475351723490⟩,⟨-267949192431122706472553658494127633057194746776838373445398,-267949192431122706472553658494127633057194745602411205847772⟩⟩,
  ⟨⟨-1133974596215561353236276829247063816528597376555008526223611,-1133974596215561353236276829247063816528597369634587909203003⟩,⟨-35898384862245412945107316988255266114389495839474227130112,-35898384862245412945107316988255266114389488918967449258807⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000000000016631904288416306,-1999999999999999999999999999999999999999999983368070301657931⟩,⟨1999999999999999999999999999999999999999999983368057711931761,2000000000000000000000000000000000000000000016631975580086093⟩⟩,
  ⟨⟨1999999999999999999999999999999999999999999932229175670224741,2000000000000000000000000000000000000000000067770805878498896⟩,⟨2464101615137754587054892683011744733885610439850778441686762,2464101615137754587054892683011744733885610575390733141059531⟩⟩,
  ⟨⟨-535898384862245412945107316988255266114389733581667849040730,-535898384862245412945107316988255266114389251176857882773031⟩,⟨-2000000000000000000000000000000000000000000241206573037544972,-1999999999999999999999999999999999999999999758793382974977294⟩⟩,
  ⟨⟨-3732050807568877293527446341505872366942806022765358064590990,-3732050807568877293527446341505872366942804484855437195235965⟩,⟨-2464101615137754587054892683011744733885611276561603531106043,-2464101615137754587054892683011744733885609738679886320837241⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000000002245449378027322102,-1999999999999999999999999999999999999999997754550627307196149⟩,⟨3464101615137754587054892683011744733885608262128644133368794,3464101615137754587054892683011744733885612753112825315745521⟩⟩,
  ⟨⟨2330127018922193233818615853764680917357007003684780545818946,2330127018922193233818615853764680917357019265367065952231973⟩,⟨-964101615137754587054892683011744733885616638325688609359935,-964101615137754587054892683011744733885604376915885308475555⟩⟩,
  ⟨⟨1267949192431122706472553658494127633057178803636051646335768,1267949192431122706472553658494127633057210688743159688358140⟩,⟨-6196152422706631880582339024517617100828431704405575326433325,-6196152422706631880582339024517617100828399818456727550984578⟩⟩,
  ⟨⟨-3133974596215561353236276829247063816528637493286942091572167,-3133974596215561353236276829247063816528557252902614736350150⟩,⟨-1500000000000000000000000000000000000000040119025899502329482,-1499999999999999999999999999999999999999959880974141783558946⟩⟩,
  ⟨⟨-98932815459049250633,98932815527502287673⟩,⟨3071796769724490825890214633976510532228680048956243739437391,3071796769724490825890214633976510532228877920560643681461073⟩⟩,
  ⟨⟨9071796769724490825890214633976510532228537763460464362627737,9071796769724490825890214633976510532229020206056488473260092⟩,⟨-241213901535312810146,241213901535313435906⟩⟩,
  ⟨⟨-584765727740203420685,584765727808657664863⟩,⟨-3071796769724490825890214633976510532229363768537082436911563,-3071796769724490825890214633976510532228194200979804984360582⟩⟩,
  ⟨⟨-3133974596215561353236276829247063816530011391451517722762447,-3133974596215561353236276829247063816527183354738039105968773⟩,⟨1499999999999999999999999999999999999998586025398265201101575,1500000000000000000000000000000000000001413974601776083628485⟩⟩,
  ⟨⟨1267949192431122706472553658494127633053779279048136223442730,1267949192431122706472553658494127633060610213331075110053838⟩,⟨6196152422706631880582339024517617100825000188495582773962370,6196152422706631880582339024517617100831831334366720104715709⟩⟩,
  ⟨⟨2330127018922193233818615853764680917348765866895869820940886,2330127018922193233818615853764680917365260402155976678725921⟩,⟨964101615137754587054892683011744733877363495522219873959972,964101615137754587054892683011744733893857519719354045127257⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000019910927032985957536430,-1999999999999999999999999999999999999980089072967019375769284⟩,⟨-3464101615137754587054892683011744733905522051616462455166531,-3464101615137754587054892683011744733865698963625006995901563⟩⟩,
  ⟨⟨-3732050807568877293527446341505872366990876480333912394855974,-3732050807568877293527446341505872366894734027286882867358290⟩,⟨2464101615137754587054892683011744733837540770590914143427648,2464101615137754587054892683011744733933680244650575707368180⟩⟩,
  ⟨⟨-535898384862245412945107316988255266230440359837165952541178,-535898384862245412945107316988255265998338624921359780450065⟩,⟨1999999999999999999999999999999999999883945536581640995433186,2000000000000000000000000000000000000116054463418315019916316⟩⟩,
  ⟨⟨1999999999999999999999999999999999999719819627868841513265300,2000000000000000000000000000000000000280180372131140038644236⟩,⟨-2464101615137754587054892683011744734165782198332469240488576,-2464101615137754587054892683011744733605438816909042341035504⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000676394337911855841292272,-1999999999999999999999999999999999999323605662088118747593235⟩,⟨-2000000000000000000000000000000000000676415296713663345297818,-1999999999999999999999999999999999999323584703286369950254498⟩⟩,
  ⟨⟨-1133974596215561353236276829247063818161608369699933101429765,-1133974596215561353236276829247063814895586376489663337938445⟩,⟨35898384862245412945107316988255264481429094797875023654069,35898384862245412945107316988255267747349889960566651571185⟩⟩,
  ⟨⟨1535898384862245412945107316988255262172074350180499655559228,1535898384862245412945107316988255270056704634577984118388073⟩,⟨267949192431122706472553658494127629114757447141378292258963,267949192431122706472553658494127636999632045237871291374087⟩⟩,
  ⟨⟨1133974596215561353236276829247063807010711776184265241356992,1133974596215561353236276829247063826046482970005352177079299⟩,⟨-35898384862245412945107316988255275631980176566977127386843,-35898384862245412945107316988255256596798808191487435469869⟩⟩,
  ⟨⟨-267949192431122706472553658494127656034691257190270970678753,-267949192431122706472553658494127610079698235188941407831822⟩,⟨-1000000000000000000000000000000000022978208493295750763780628,-999999999999999999999999999999999977021791506704239893989899⟩⟩,
  ⟨⟨-55474302583564478668646631,55474302583564459780887055⟩,⟨999999999999999999999999999999999944527416293748507047986784,1000000000000000000000000000000000055472583706251492950845163⟩⟩,
  ⟨⟨-133922663923509985642515723,133922663923509985641269055⟩,⟨-133926813660431028469465035,133926813660431028475262425⟩⟩,
  ⟨⟨-323327929904426892419904281,323327929904426892426026355⟩,⟨-323317911553271830476576340,323317911553271830477872734⟩⟩]
lemma restBox9_calc (j : Fin 31) : recoverRest phaseBox9 restBox9 j = restBox9 j := by
  revert j
  decide +kernel
lemma restBox9_mem (j : Fin 31) : (restBox9 j).Mem ((restPolynomial ⟨5,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨5,by norm_num⟩ phaseBox9
  · have hr : residue ⟨5,by norm_num⟩ = (9:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox9_mem
  · exact restBox9_calc
def cBox9 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-11282604915,10707415501⟩,⟨-30461741978670859934674354937889355355906479651988824550517,-30461741978670859934674354937889355355906479651966641302835⟩⟩,
  ⟨⟨-8162199163230086799154349223237515385498962031409200157909,-8162199163230086799154349223237515385498962030979545279929⟩,⟨30461741978670859934674354937889355355906479651762702701727,30461741978670859934674354937889355355906479652192478417488⟩⟩,
  ⟨⟨34542841560285903334251529549508113048655960665233299002586,34542841560285903334251529549508113048655960669916881468076⟩,⟨1093527337124743630971520977530353093044684234058668344067,1093527337124743630971520977530353093044684238742302123769⟩⟩,
  ⟨⟨46786140305131033532983053384364386126904403696479074033154,46786140305131033532983053384364386126904403732255680415173⟩,⟨-8162199163230086799154349223237515385498962049082513957686,-8162199163230086799154349223237515385498962013307364643391⟩⟩,
  ⟨⟨-34542841560285903334251529549508113048655960772978914280032,-34542841560285903334251529549508113048655960562170627153898⟩,⟨-1093527337124743630971520977530353093044684341805486029478,-1093527337124743630971520977530353093044684130994787238694⟩⟩,
  ⟨⟨-60923483957341719869348709875778710711812959810592436825510,-60923483957341719869348709875778710711812958797317720848540⟩,⟨60923483957341719869348709875778710711812958797317337343529,60923483957341719869348709875778710711812959810594608493941⟩⟩,
  ⟨⟨60923483957341719869348709875778710711812957239537907511361,60923483957341719869348709875778710711812961368372462135226⟩,⟨75060827609552406205714366367193035296721512829151680924666,75060827609552406205714366367193035296721516957935286629821⟩⟩,
  ⟨⟨-16324398326460173598308698446475030770997931409835760527768,-16324398326460173598308698446475030770997916714944806141195⟩,⟨-60923483957341719869348709875778710711812966651528051206931,-60923483957341719869348709875778710711812951956381540562509⟩⟩,
  ⟨⟨-113684768751453352939543070528319906038126980000424635193031,-113684768751453352939543070528319906038126933153008715492825⟩,⟨-75060827609552406205714366367193035296721538316821423411503,-75060827609552406205714366367193035296721491470264882184886⟩⟩,
  ⟨⟨-60923483957341719869348709875778710711813027704255239413088,-60923483957341719869348709875778710711812890903655854790298⟩,⟨105522569588223266140388721305082390652627926143919560347670,105522569588223266140388721305082390652628062947121589595266⟩⟩,
  ⟨⟨70979728027937362806137191755574277603971847121844173218071,70979728027937362806137191755574277603972220634046627578478⟩,⟨-29368214641546116303702833960359002262861982167528788736116,-29368214641546116303702833960359002262861608663626878875255⟩⟩,
  ⟨⟨38623941141900946733828704161126870741404956045219123054166,38623941141900946733828704161126870741405927321125056402189⟩,⟨-188745596361005759145257436895512941334848957121033972539901,-188745596361005759145257436895512941334847985819486224914892⟩⟩,
  ⟨⟨-95466325517627623203600239425286823760470142102471761831227,-95466325517627623203600239425286823760467697840587504793743⟩,⟨-45692612968006289902011532406834033033860941573382131086950,-45692612968006289902011532406834033033858497382552325331635⟩⟩,
  ⟨⟨-3013665897737017992,3013665899822216713⟩,⟨93572280610262067065966106768728772253805793671854167824026,93572280610262067065966106768728772253811821185612900191285⟩⟩,
  ⟨⟨276342732482287226674012236396064904389240337319660244966488,276342732482287226674012236396064904389255033361541610817247⟩,⟨-7347795630237217621,7347795630237236774⟩⟩,
  ⟨⟨-17812982716391769518,17812982718477005071⟩,⟨-93572280610262067065966106768728772253826620961312036919079,-93572280610262067065966106768728772253790993896155031107615⟩⟩,
  ⟨⟨-95466325517627623203600239425286823760511993433866034181660,-95466325517627623203600239425286823760425846509193232467982⟩,⟨45692612968006289902011532406834033033816647348484014610954,45692612968006289902011532406834033033902791607450441772284⟩⟩,
  ⟨⟨38623941141900946733828704161126870741301400604371896060208,38623941141900946733828704161126870741509482761972283359551⟩,⟨188745596361005759145257436895512941334744427168786873876219,188745596361005759145257436895512941334952515771733323616987⟩⟩,
  ⟨⟨70979728027937362806137191755574277603720807739369442616662,70979728027937362806137191755574277604223260016521358229091⟩,⟨29368214641546116303702833960359002262610577060936212888255,29368214641546116303702833960359002263113013770219454761294⟩⟩,
  ⟨⟨-60923483957341719869348709875778710712419480825790620554384,-60923483957341719869348709875778710711206437782120473611996⟩,⟨-105522569588223266140388721305082390653234534861115721981561,-105522569588223266140388721305082390652021454229925428020931⟩⟩,
  ⟨⟨-113684768751453352939543070528319906039591289875674582992085,-113684768751453352939543070528319906036662623277758767766540⟩,⟨75060827609552406205714366367193035295257226967157648424585,75060827609552406205714366367193035298185802819928657136776⟩⟩,
  ⟨⟨-16324398326460173598308698446475030774533035643293909776036,-16324398326460173598308698446475030767462812481486656928836⟩,⟨60923483957341719869348709875778710708277738183832123771789,60923483957341719869348709875778710715348180424077468083764⟩⟩,
  ⟨⟨60923483957341719869348709875778710703278177100607938343546,60923483957341719869348709875778710720347741507302431400138⟩,⟨-75060827609552406205714366367193035305256032645731912934640,-75060827609552406205714366367193035288186997141355054582574⟩⟩,
  ⟨⟨-60923483957341719869348709875778710732417109101260521583726,-60923483957341719869348709875778710691208809506649636054072⟩,⟨-60923483957341719869348709875778710732417747542873363871208,-60923483957341719869348709875778710691208171065038582073968⟩⟩,
  ⟨⟨-34542841560285903334251529549508113098400320294492655098416,-34542841560285903334251529549508112998911601040656886455582⟩,⟨1093527337124743630971520977530353043301865943889393979095,1093527337124743630971520977530353142787502528910879253607⟩⟩,
  ⟨⟨46786140305131033532983053384364386006814617054102021552635,46786140305131033532983053384364386246994190374632732858958⟩,⟨8162199163230086799154349223237515265405454260499180313796,8162199163230086799154349223237515505592469801890698419513⟩⟩,
  ⟨⟨34542841560285903334251529549508112758724585431978323177668,34542841560285903334251529549508113338587335903171857435288⟩,⟨-1093527337124743630971520977530353382967075916729026967663,-1093527337124743630971520977530352803122292556071943462162⟩⟩,
  ⟨⟨-8162199163230086799154349223237516085433532065106569647860,-8162199163230086799154349223237514685564391997282175752582⟩,⟨-30461741978670859934674354937889356055862737906856291947733,-30461741978670859934674354937889354655950221397098889324002⟩⟩,
  ⟨⟨-1689843891747255419737726,1689843891747254844383656⟩,⟨30461741978670859934674354937889353666114947901923378200508,30461741978670859934674354937889357045698011402032087616227⟩⟩,
  ⟨⟨-4079517633534213660319942,4079517633534213660281966⟩,⟨-4079644041749581830965399,4079644041749581831141998⟩⟩]
lemma cBox9_calc (j : Fin 31) : cCoeffBox restBox9 j = cBox9 j := by
  revert j
  decide +kernel
lemma cBox9_mem (j : Fin 31) : (cBox9 j).Mem (cCoefficient ⟨5,by norm_num⟩ j) := by
  rw [← cBox9_calc]
  exact cCoeffBox_mem ⟨5,by norm_num⟩ restBox9 restBox9_mem j
def dBox9 : Fin 31 → CI :=
  ![⟨⟨-30923612170,32643051449⟩,⟨87266462599716478846184538424430635672143594427054328781012,87266462599716478846184538424430635672143594427118171222183⟩⟩,
  ⟨⟨23382978179914803476195888712014960320615001512493879330783,23382978179914803476195888712014960320615001513725398056837⟩,⟨-87266462599716478846184538424430635672143594427701682524998,-87266462599716478846184538424430635672143594426470020971659⟩⟩,
  ⟨⟨-98957951689673880584282482780438115832451095190381487096765,-98957951689673880584282482780438115832451095176900093306985⟩,⟨84133737539745111316885030212616032866985388607667278962474,84133737539745111316885030212616032866985388621149380611832⟩⟩,
  ⟨⟨-110649440779631282322380427136445595992758595992060653530901,-110649440779631282322380427136445595992758595888336254749724⟩,⟨-63883484419801675369988649712415675351528592965834839693915,-63883484419801675369988649712415675351528592862114120068880⟩⟩,
  ⟨⟨-308670315674931,308668490113275⟩,⟨-308674620800051,308672460987551⟩⟩,
  ⟨⟨40500506239886871893792761000400715030913589898207068313620,40500506239886871893792761000400715030913592903519203619067⟩,⟨-151149947019518154216173188136846311023672188843720950533018,-151149947019518154216173188136846311023672185838404612762080⟩⟩,
  ⟨⟨-75574973509759077108086594068423155511836099886612463607379,-75574973509759077108086594068423155511836087454449782042997⟩,⟨-211900706379348462056862329637447383570042580658371758301655,-211900706379348462056862329637447383570042568226347339581214⟩⟩,
  ⟨⟨221298881559262564644760854272891191985517169380103859064395,221298881559262564644760854272891191985517214380686719633537⟩,⟨-22500663708280804,22500657069265169⟩⟩,
  ⟨⟨151149947019518154216173188136846311023672114322962264992947,151149947019518154216173188136846311023672260359166015903378⟩,⟨-73016799063760448,73016796756729058⟩⟩,
  ⟨⟨221298881559262564644760854272891191985516974879089072181829,221298881559262564644760854272891191985517408881703511438727⟩,⟨-127766968839603350739977299424831350703057402833350835278034,-127766968839603350739977299424831350703056968822550178143231⟩⟩,
  ⟨⟨122340929869588684060478371492453076153065494575954909619430,122340929869588684060478371492453076153066698817557867872334⟩,⟨299167168979064940903046868061878019242185566761763991564447,299167168979064940903046868061878019242186770977127729640718⟩⟩,
  ⟨⟨63883484419801675369988649712415675351527005711296013986330,63883484419801675369988649712415675351530180116658385794300⟩,⟨238416409619234633062357726561276946695814194525014296016601,238416409619234633062357726561276946695817369011288086584757⟩⟩,
  ⟨⟨70148934539744410428587666136044880961840968375261635995156,70148934539744410428587666136044880961849040703402836579816⟩,⟨215033431439319829586161837849261986375196744204636943283809,215033431439319829586161837849261986375204816305444954638309⟩⟩,
  ⟨⟨-110649440779631282322380427136445595992768620707298970573206,-110649440779631282322380427136445595992748571173099424898048⟩,⟨272651465739178769897551471138048456116402936479192028649604,272651465739178769897551471138048456116422986608126395192408⟩⟩,
  ⟨⟨-518172736628284206397608302614205539482895029107956725634870,-518172736628284206397608302614205539482845925754686927183863⟩,⟨130899693899574718269276807636645953508190840711239242239646,130899693899574718269276807636645953508239942570023985037102⟩⟩,
  ⟨⟨-59663953363056169541,59663953351548900629⟩,⟨-59665789231704591616,59665789231704624226⟩⟩,
  ⟨⟨-518172736628284206397608302614205539483014924340751483999223,-518172736628284206397608302614205539482726030521892168748916⟩,⟨-130899693899574718269276807636645953508359834086253630718743,-130899693899574718269276807636645953508070949195009596566146⟩⟩,
  ⟨⟨-110649440779631282322380427136445595993107682112276403077941,-110649440779631282322380427136445595992409509768121992394162⟩,⟨-272651465739178769897551471138048456116762058523248552125487,-272651465739178769897551471138048456116063864564069871793888⟩⟩,
  ⟨⟨70148934539744410428587666136044880961001898287098252159091,70148934539744410428587666136044880962688110791566220345462⟩,⟨-215033431439319829586161837849261986376043860389603604428436,-215033431439319829586161837849261986374357700120478293501828⟩⟩,
  ⟨⟨63883484419801675369988649712415675349492981009162290475544,63883484419801675369988649712415675353564204818792109303767⟩,⟨-238416409619234633062357726561276946697851456745399444478384,-238416409619234633062357726561276946693780106790902938062444⟩⟩,
  ⟨⟨122340929869588684060478371492453076148151380933028779949511,122340929869588684060478371492453076157980812460483997609579⟩,⟨-299167168979064940903046868061878019247100732350999989126742,-299167168979064940903046868061878019237271605387891732087520⟩⟩,
  ⟨⟨221298881559262564644760854272891191973652287026464386009995,221298881559262564644760854272891191997382096734328197607501⟩,⟨127766968839603350739977299424831350691191913327115769471290,127766968839603350739977299424831350714922458328785243873757⟩⟩,
  ⟨⟨151149947019518154216173188136846310995026831483766479928079,151149947019518154216173188136846311052317543198361800898556⟩,⟨-28644468277686892876731,28644468277689199901601⟩⟩,
  ⟨⟨221298881559262564644760854272891191916363302003667254356918,221298881559262564644760854272891192054671081757123324340032⟩,⟨-69156032683962588382257,69156032683969227459616⟩⟩,
  ⟨⟨-75574973509759077108086594068423155678793536696458167791148,-75574973509759077108086594068423155344878650644604077793285⟩,⟨211900706379348462056862329637447383403090304611013865642909,211900706379348462056862329637447383736994844273705232234849⟩⟩,
  ⟨⟨40500506239886871893792761000400714627855153295832860211370,40500506239886871893792761000400715433972029505893411722796⟩,⟨151149947019518154216173188136846310620601260039402258485372,151149947019518154216173188136846311426743114642723304739439⟩⟩,
  ⟨⟨-973099300531343411659438,973099300531341586034111⟩,⟨-973069148943430061604117,973069148943432221409344⟩⟩,
  ⟨⟨-110649440779631282322380427136445598341955332765537391914596,-110649440779631282322380427136445593643561859114859516367884⟩,⟨63883484419801675369988649712415673002259063716170864344294,63883484419801675369988649712415677700798122111778095476697⟩⟩,
  ⟨⟨-98957951689673880584282482780438121504089454308799651160693,-98957951689673880584282482780438110160812736058481929179051⟩,⟨-84133737539745111316885030212616038538448011406726535581033,-84133737539745111316885030212616027195522765822090123997197⟩⟩,
  ⟨⟨23382978179914803476195888712014946628493019065370330232431,23382978179914803476195888712014974012736983960848947156908⟩,⟨87266462599716478846184538424430621979597346941201405984972,87266462599716478846184538424430649364689841912970297442691⟩⟩,
  ⟨⟨-33056730854102404089591485,33056730854102405808968159⟩,⟨-87266462599716478846184538424430668727850182120360953386403,-87266462599716478846184538424430602616437006733811546625023⟩⟩]
lemma dBox9_calc (j : Fin 31) : dCoeffBox phaseBox9 restBox9 j = dBox9 j := by
  revert j
  decide +kernel
lemma dBox9_mem (j : Fin 31) : (dBox9 j).Mem (dCoefficient ⟨5,by norm_num⟩ j) := by
  rw [← dBox9_calc]
  apply dCoeffBox_mem ⟨5,by norm_num⟩ phaseBox9 restBox9
  · have hr : residue ⟨5,by norm_num⟩ = (9:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox9_mem
  · exact restBox9_mem
def restBox12 : Fin 31 → CI :=
  ![⟨⟨-500000000000000000000000000000000000000000000000501614783846,-499999999999999999999999999999999999999999999999514500834255⟩,⟨-866025403784438646763723170752936183471402626905678977555292,-866025403784438646763723170752936183471402626904692346183342⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999990016663915292,1000000000000000000000000000000000000000000000010013768378936⟩,⟨1732050807568877293527446341505872366942805253800365259264217,1732050807568877293527446341505872366942805253820361498001671⟩⟩,
  ⟨⟨499999999999999999999999999999999999999999999886472156547683,500000000000000000000000000000000000000000000113490099350089⟩,⟨-2598076211353315940291169512258808550414207880829073389760285,-2598076211353315940291169512258808550414207880602052392424732⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000000911269410354242,-999999999999999999999999999999999999999999999088679217578619⟩,⟨1732050807568877293527446341505872366942805252899089569673915,1732050807568877293527446341505872366942805254721669681505651⟩⟩,
  ⟨⟨1999999999999999999999999999999999999999999994281044178437498,2000000000000000000000000000000000000000000005718967031343953⟩,⟨1732050807568877293527446341505872366942805248091408037812722,1732050807568877293527446341505872366942805259529336795645903⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000029788934480247761,-999999999999999999999999999999999999999999970211080269035440⟩,⟨-1732050807568877293527446341505872366942805283599330861160112,-1732050807568877293527446341505872366942805224021375068411787⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000134466852007252806,-999999999999999999999999999999999999999999865533137076550312⟩,⟨1732050807568877293527446341505872366942805119343856381265939,1732050807568877293527446341505872366942805388276914723430734⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000544575871285199866,-999999999999999999999999999999999999999999455424140847550371⟩,⟨1732050807568877293527446341505872366942804709233369833110464,1732050807568877293527446341505872366942805798387404824111692⟩⟩,
  ⟨⟨499999999999999999999999999999999999999997962426522407977378,500000000000000000000000000000000000000002037573412475852019⟩,⟨-2598076211353315940291169512258808550414209918286334725579730,-2598076211353315940291169512258808550414205843144795248767273⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000000007220014883767123633,-1999999999999999999999999999999999999999992779985126700565970⟩,⟨-7220020776185843208,7220020762636797087⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000000024717275076351545385,-1999999999999999999999999999999999999999975282724933923232571⟩,⟨-24717256979890161958,24717256948155683070⟩⟩,
  ⟨⟨2999999999999999999999999999999999999999917037195949211816987,3000000000000000000000000000000000000000082962804017742329453⟩,⟨-1732050807568877293527446341505872366942888216667166039432925,-1732050807568877293527446341505872366942722290953648634242596⟩⟩,
  ⟨⟨-275654941235961514027,275654941258306067781⟩,⟨-3464101615137754587054892683011744733885886162452067952109463,-3464101615137754587054892683011744733885334852789467798497448⟩⟩,
  ⟨⟨-3000000000000000000000000000000000000000911673565585319980372,-2999999999999999999999999999999999999999088326434330734277231⟩,⟨1732050807568877293527446341505872366941893580071795468971720,1732050807568877293527446341505872366943716927548916487839366⟩⟩,
  ⟨⟨8999999999999999999999999999999999999996990470718768182653566,9000000000000000000000000000000000000003009529281210668992365⟩,⟨-3009529045908244164974,3009529045908243371055⟩⟩,
  ⟨⟨-3000000000000000000000000000000000000009928044280043698817476,-2999999999999999999999999999999999999990071955719872356976526⟩,⟨-1732050807568877293527446341505872366952733298385138783640028,-1732050807568877293527446341505872366932877209235573172550023⟩⟩,
  ⟨⟨-32744191244465626490736,32744191244487972223114⟩,⟨3464101615137754587054892683011744733852866316717537302028878,3464101615137754587054892683011744733918354698523998449845194⟩⟩,
  ⟨⟨2999999999999999999999999999999999999892011463660955806560446,3000000000000000000000000000000000000107988536339011148290177⟩,⟨1732050807568877293527446341505872366834816717096706633054521,1732050807568877293527446341505872367050793790524108039018338⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000356134534161877982055633,-1999999999999999999999999999999999999643865465838132294588374⟩,⟨-356134533772934769050120,356134533772966503581836⟩⟩,
  ⟨⟨-2000000000000000000000000000000000001174488954684901549605723,-1999999999999999999999999999999999998825511045315108917232976⟩,⟨-1174488955058476139056612,1174488955058489689910184⟩⟩,
  ⟨⟨499999999999999999999999999999999996126679224995226571887158,500000000000000000000000000000000003873320775004708313259649⟩,⟨2598076211353315940291169512258808546540887106049850735280804,2598076211353315940291169512258808554287528655381279237500946⟩⟩,
  ⟨⟨-1000000000000000000000000000000000012773736014039527439052131,-999999999999999999999999999999999987226263985960484695810228⟩,⟨-1732050807568877293527446341505872379716541268151922164113165,-1732050807568877293527446341505872354169069239468852493605649⟩⟩,
  ⟨⟨-1000000000000000000000000000000000042126211055066924622842600,-999999999999999999999999999999999957873788944933064460453137⟩,⟨-1732050807568877293527446341505872409069016308609017161418289,-1732050807568877293527446341505872324816594199011753941002466⟩⟩,
  ⟨⟨-1000000000000000000000000000000000138927064957662564334793177,-999999999999999999999999999999999861072935042337450412608331⟩,⟨1732050807568877293527446341505872228015740295910020614815939,1732050807568877293527446341505872505869870211710685313232256⟩⟩,
  ⟨⟨1999999999999999999999999999999999541835619952714726614551954,2000000000000000000000000000000000458164380047285284592880811⟩,⟨-1732050807568877293527446341505872825107185300885351290886167,-1732050807568877293527446341505871908778425206735393543583238⟩⟩,
  ⟨⟨-1000000000000000000000000000000001510969797003994550734928491,-999999999999999999999999999999998489030202996005397892841168⟩,⟨-1732050807568877293527446341505873877912602257990815903695818,-1732050807568877293527446341505870855973008249629943344763970⟩⟩,
  ⟨⟨499999999999999999999999999999995017007373602514231086775181,500000000000000000000000000000004982992626397485731171562125⟩,⟨2598076211353315940291169512258803567421581483394047317194802,2598076211353315940291169512258813533406834278037078463549213⟩⟩,
  ⟨⟨999999999999999999999999999999983566702945380058907967887589,1000000000000000000000000000000016433297054619941122461844097⟩,⟨-1732050807568877293527446341505888800239859873896595237244436,-1732050807568877293527446341505855933645750633724131521562613⟩⟩,
  ⟨⟨-500000000000000000000000000000054194993316822105929779799993,-499999999999999999999999999999945805006683177894086336001964⟩,⟨866025403784438646763723170752881988478085804927504534127600,866025403784438646763723170752990378464719448882866792800258⟩⟩,
  ⟨⟨-178728425029270456427932046446,178728425029270456427935074168⟩,⟨-178728425029270569749375908762,178728425029270569749374511823⟩⟩,
  ⟨⟨-589424372223849901636762021447,589424372223849901636759187793⟩,⟨-589424372223849801498691190926,589424372223849801498689135994⟩⟩]
lemma restBox12_calc (j : Fin 31) : recoverRest phaseBox12 restBox12 j = restBox12 j := by
  revert j
  decide +kernel
lemma restBox12_mem (j : Fin 31) : (restBox12 j).Mem ((restPolynomial ⟨6,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨6,by norm_num⟩ phaseBox12
  · have hr : residue ⟨6,by norm_num⟩ = (12:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox12_mem
  · exact restBox12_calc
def cBox12 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-15230870989335429967337177468944677677953239826004195004570,-15230870989335429967337177468944677677953239825974028831380⟩,⟨-26380642397055816535097180326270597663156998636395315306702,-26380642397055816535097180326270597663156998636365092852016⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651673526155498,30461741978670859934674354937889355355906479652282866717495⟩,⟨52761284794111633070194360652541195326313997272455438060074,52761284794111633070194360652541195326313997273064894213844⟩⟩,
  ⟨⟨15230870989335429967337177468944677677953239822530562107067,15230870989335429967337177468944677677953239829446021068013⟩,⟨-79141927191167449605291540978811792989470995912598771568301,-79141927191167449605291540978811792989470995905682812690526⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906479679736683540186,-30461741978670859934674354937889355355906479624217217429494⟩,⟨52761284794111633070194360652541195326313997245001010552114,52761284794111633070194360652541195326313997300520311542997⟩⟩,
  ⟨⟨60923483957341719869348709875778710711812959129745915302957,60923483957341719869348709875778710711812959478165357871127⟩,⟨52761284794111633070194360652541195326313997098550656212948,52761284794111633070194360652541195326313997446970226693299⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906480559400665845742,-30461741978670859934674354937889355355906478744555249295417⟩,⟨-52761284794111633070194360652541195326313998180184175345121,-52761284794111633070194360652541195326313996365335522480955⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906483748072380417974,-30461741978670859934674354937889355355906475555882752907987⟩,⟨52761284794111633070194360652541195326313993176675957265611,52761284794111633070194360652541195326314001368845725908280⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906496240707508788551,-30461741978670859934674354937889355355906463063248326648490⟩,⟨52761284794111633070194360652541195326313980683996133288533,52761284794111633070194360652541195326314013861525658101473⟩⟩,
  ⟨⟨15230870989335429967337177468944677677953177757951280990422,15230870989335429967337177468944677677953301894024468383774⟩,⟨-79141927191167449605291540978811792989471057977096158949397,-79141927191167449605291540978811792989470933841185553009987⟩⟩,
  ⟨⟨-60923483957341719869348709875778710711813179238186131255203,-60923483957341719869348709875778710711812739369725119313489⟩,⟨-219934409964816087,219934409552088520⟩⟩,
  ⟨⟨-60923483957341719869348709875778710711813712235211451430658,-60923483957341719869348709875778710711812206372699793261609⟩,⟨-752930704541915487,752930703575227960⟩⟩,
  ⟨⟨91385225936012579804023064813668066067716911764402085750984,91385225936012579804023064813668066067721966147463305171717⟩,⟨-52761284794111633070194360652541195326316524465898070153161,-52761284794111633070194360652541195326311470079624940207701⟩⟩,
  ⟨⟨-8396929695075537912,8396929695756191977⟩,⟨-105522569588223266140388721305082390652636391471868157673493,-105522569588223266140388721305082390652619597619175011928424⟩⟩,
  ⟨⟨-91385225936012579804023064813668066067747210120857124549777,-91385225936012579804023064813668066067691667791006715873644⟩,⟨52761284794111633070194360652541195326286226102567012295809,52761284794111633070194360652541195326341768442952869130433⟩⟩,
  ⟨⟨274155677808037739412069194441004198203066641363356585280105,274155677808037739412069194441004198203249992372241963175034⟩,⟨-91675497273772422876,91675497273772398783⟩⟩,
  ⟨⟨-91385225936012579804023064813668066068021864479144999921784,-91385225936012579804023064813668066067417013432718840548403⟩,⟨-52761284794111633070194360652541195326616422804949885523343,-52761284794111633070194360652541195326011571740569995884040⟩⟩,
  ⟨⟨-997445104989165400686,997445104989846090585⟩,⟨105522569588223266140388721305082390651630549450926697656660,105522569588223266140388721305082390653625439640116471983856⟩⟩,
  ⟨⟨91385225936012579804023064813668066064429920025318621760098,91385225936012579804023064813668066071008957886546769184018⟩,⟨52761284794111633070194360652541195323024478330734361157201,52761284794111633070194360652541195329603516214788649154903⟩⟩,
  ⟨⟨-60923483957341719869348709875778710722661437593288929741425,-60923483957341719869348709875778710700964481014622315007686⟩,⟨-10848478277485382164713,10848478277486348853810⟩⟩,
  ⟨⟨-60923483957341719869348709875778710747589938798365982657641,-60923483957341719869348709875778710676035979809545267885131⟩,⟨-35776979505790055633500,35776979505790468416085⟩⟩,
  ⟨⟨15230870989335429967337177468944677559965141777167962374065,15230870989335429967337177468944677795941337874807787040211⟩,⟨79141927191167449605291540978811792871482897870648081597001,79141927191167449605291540978811793107459093947633630314715⟩⟩,
  ⟨⟨-30461741978670859934674354937889355745016730215305487938286,-30461741978670859934674354937889354966796229088650347563059⟩,⟨-52761284794111633070194360652541195715424247845288393075109,-52761284794111633070194360652541194937203746700233398330046⟩⟩,
  ⟨⟨-30461741978670859934674354937889356639144251350458424468389,-30461741978670859934674354937889354072668707953496708842081⟩,⟨-52761284794111633070194360652541196609551768963068931550623,-52761284794111633070194360652541194043076225582452751553959⟩⟩,
  ⟨⟨-30461741978670859934674354937889359587866886246340960367212,-30461741978670859934674354937889351123946073057614954716662⟩,⟨52761284794111633070194360652541191094353590671153722561235,52761284794111633070194360652541199558274403874365975218407⟩⟩,
  ⟨⟨60923483957341719869348709875778696755327830485855708631481,60923483957341719869348709875778724668298088122055564471093⟩,⟨-52761284794111633070194360652541209282799126084454235550375,-52761284794111633070194360652541181369828868461066647386620⟩⟩,
  ⟨⟨-30461741978670859934674354937889401382678573552346369007348,-30461741978670859934674354937889309329134385751607531957326⟩,⟨-52761284794111633070194360652541241353086091178791765564254,-52761284794111633070194360652541149299541903366729556448028⟩⟩,
  ⟨⟨15230870989335429967337177468944525887317572886335549592283,15230870989335429967337177468944829468588906765641033657058⟩,⟨79141927191167449605291540978811641198835328974490714665140,79141927191167449605291540978811944780106662843790869549803⟩⟩,
  ⟨⟨30461741978670859934674354937888854769051742967518648375050,30461741978670859934674354937889855942761216336437744419918⟩,⟨-52761284794111633070194360652541695913168733961640533615358,-52761284794111633070194360652540694739459260583879798705484⟩⟩,
  ⟨⟨-15230870989335429967337177468946328551856192652636350680894,-15230870989335429967337177468943026804050286999341873160674⟩,⟨26380642397055816535097180326268946789254045813639361718829,26380642397055816535097180326272248537059951459121046537029⟩⟩,
  ⟨⟨-5444379167495855480825544275,5444379167495855480825636505⟩,⟨-5444379167495858932794127859,5444379167495858932794085306⟩⟩]
lemma cBox12_calc (j : Fin 31) : cCoeffBox restBox12 j = cBox12 j := by
  revert j
  decide +kernel
lemma cBox12_mem (j : Fin 31) : (cBox12 j).Mem (cCoefficient ⟨6,by norm_num⟩ j) := by
  rw [← cBox12_calc]
  exact cCoeffBox_mem ⟨6,by norm_num⟩ restBox12 restBox12_mem j
def dBox12 : Fin 31 → CI :=
  ![⟨⟨-58547107015,60266546294⟩,⟨87266462599716478846184538424430635672143594427026719566435,87266462599716478846184538424430635672143594427145780436758⟩⟩,
  ⟨⟨-1195051335308,1191055070473⟩,⟨-174532925199432957692369076848861271344287188855365162313091,-174532925199432957692369076848861271344287188852978558297341⟩⟩,
  ⟨⟨-75574973509759077108086594068423155511836093684120708362741,-75574973509759077108086594068423155511836093656936456431401⟩,⟨218166156499291197115461346061076589180358986054122917910475,218166156499291197115461346061076589180358986081307603910109⟩⟩,
  ⟨⟨-109830230664856,109825466116866⟩,⟨-174532925199432957692369076848861271344287188963999663950375,-174532925199432957692369076848861271344287188744343821854377⟩⟩,
  ⟨⟨-695281373491471,695281482044894⟩,⟨-695282506156716,695280559828450⟩⟩,
  ⟨⟨-3659722639500399,3659722755389623⟩,⟨-3659724700841848,3659723556150935⟩⟩,
  ⟨⟨-75574973509759077108086594068423155511836110381819596497721,-75574973509759077108086594068423155511836076959242652267563⟩,⟨-130899693899574718269276807636645953508215408351907485574731,-130899693899574718269276807636645953508215374929351168413537⟩⟩,
  ⟨⟨302299894039036308432346376273692622047344306213072256927694,302299894039036308432346376273692622047344443151174454817804⟩,⟨-68469091669726268,68469086361468135⟩⟩,
  ⟨⟨-151149947019518154216173188136846311023672446265956304480929,-151149947019518154216173188136846311023671928416162477585038⟩,⟨-258924799755137831,258924801593737981⟩⟩,
  ⟨⟨151149947019518154216173188136846311023671261737828896753851,151149947019518154216173188136846311023673112944295272188396⟩,⟨-87266462599716478846184538424430635672144520030544446372771,-87266462599716478846184538424430635672142668823628280552394⟩⟩,
  ⟨⟨226724920529277231324259782205269466535505091615037052361394,226724920529277231324259782205269466535511470408151623074597⟩,⟨305432619099007675961645884485507224852499391098907806547697,305432619099007675961645884485507224852505769890694966067366⟩⟩,
  ⟨⟨-151149947019518154216173188136846311023682937875568746956982,-151149947019518154216173188136846311023661436806552958839645⟩,⟨-87266462599716478846184538424430635672154344963463114034712,-87266462599716478846184538424430635672132843890702843447907⟩⟩,
  ⟨⟨-35806827096762438432,35806827097039407626⟩,⟨174532925199432957692369076848861271344251382031166780598908,174532925199432957692369076848861271344322995677180525843980⟩⟩,
  ⟨⟨151149947019518154216173188136846311023553618515143600891341,151149947019518154216173188136846311023790756166975795734394⟩,⟨261799387799149436538553615273291907016312214448135606268560,261799387799149436538553615273291907016549352114384055475480⟩⟩,
  ⟨⟨-529024814568313539756606158478962088583244276592286553643963,-529024814568313539756606158478962088582461034795145401516222⟩,⟨-130899693899574718269276807636645953508607012528169320111891,-130899693899574718269276807636645953507823770753085621609288⟩⟩,
  ⟨⟨302299894039036308432346376273692622046052191356680549619523,302299894039036308432346376273692622048636558007558337978784⟩,⟨-1292183340375393640764,1292183340375393660871⟩⟩,
  ⟨⟨-529024814568313539756606158478962088587114792507698120574329,-529024814568313539756606158478962088578590518879733834550362⟩,⟨130899693899574718269276807636645953503953254845062153060011,130899693899574718269276807636645953512477528436192788633964⟩⟩,
  ⟨⟨151149947019518154216173188136846311009615563418955684308100,151149947019518154216173188136846311037728811263163712283509⟩,⟨-261799387799149436538553615273291907030487407224744922753261,-261799387799149436538553615273291907002374159337774739014353⟩⟩,
  ⟨⟨-46357534712485639920928,46357534712485916889093⟩,⟨-174532925199432957692369076848861271390644723543336827242477,-174532925199432957692369076848861271297929654165010479167320⟩⟩,
  ⟨⟨-151149947019518154216173188136846311176554026787416975659353,-151149947019518154216173188136846310870790347894704730106007⟩,⟨87266462599716478846184538424430635519261754956826173791627,87266462599716478846184538424430635825025433897339783669109⟩⟩,
  ⟨⟨226724920529277231324259782205269466031322506315097564572456,226724920529277231324259782205269467039694055708091110834405⟩,⟨-305432619099007675961645884485507225356688355168046328914929,-305432619099007675961645884485507224348316805821556443724732⟩⟩,
  ⟨⟨151149947019518154216173188136846309360929328509262769580131,151149947019518154216173188136846312686415046172861399356895⟩,⟨87266462599716478846184538424430634009400735573707281013562,87266462599716478846184538424430637334886453280465445941829⟩⟩,
  ⟨⟨-151149947019518154216173188136846316507193798860257176971343,-151149947019518154216173188136846305540150575821861605064930⟩,⟨-5483521611499799384663152,5483521611499797546044634⟩⟩,
  ⟨⟨302299894039036308432346376273692603963364222640912838206726,302299894039036308432346376273692640131324526723333873511374⟩,⟨-18083980152058449148466366,18083980152058454456702930⟩⟩,
  ⟨⟨-75574973509759077108086594068423215150579342103364052325111,-75574973509759077108086594068423095873092845237698196444430⟩,⟨130899693899574718269276807636645893869472143223083593290696,130899693899574718269276807636646013146958640058175060726577⟩⟩,
  ⟨⟨-196681243035488620510877320,196681243035488620626797158⟩,⟨-196681243035502151614042649,196681243035502152758718153⟩⟩,
  ⟨⟨-648630558825536174642862142,648630558825536174751389928⟩,⟨-648630558825524210398953626,648630558825524212345258260⟩⟩,
  ⟨⟨-2139103838006827478422170310,2139103838006827473657617728⟩,⟨174532925199432957692369076848859132240449182016123234944913,174532925199432957692369076848863410448125195692220250889699⟩⟩,
  ⟨⟨-75574973509759077108086594068430210013304633633446857112423,-75574973509759077108086594068416101010367553707610307650154⟩,⟨-218166156499291197115461346061083643681827526021291548581864,-218166156499291197115461346061069534678890446114138973256377⟩⟩,
  ⟨⟨-23264878537174032626175113526,23264878537174032622178819825⟩,⟨174532925199432957692369076848838006465750014813292203511692,174532925199432957692369076848884536222824362895051517076865⟩⟩,
  ⟨⟨-76724709146808372605482454668,76724709146808372607201893177⟩,⟨-87266462599716478846184538424507360381290402792397911096354,-87266462599716478846184538424353910962996786061774588876945⟩⟩]
lemma dBox12_calc (j : Fin 31) : dCoeffBox phaseBox12 restBox12 j = dBox12 j := by
  revert j
  decide +kernel
lemma dBox12_mem (j : Fin 31) : (dBox12 j).Mem (dCoefficient ⟨6,by norm_num⟩ j) := by
  rw [← dBox12_calc]
  apply dCoeffBox_mem ⟨6,by norm_num⟩ phaseBox12 restBox12
  · have hr : residue ⟨6,by norm_num⟩ = (12:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox12_mem
  · exact restBox12_mem
def restBox13 : Fin 31 → CI :=
  ![⟨⟨-642787609686539326322643409907263432907559884206198239737317,-642787609686539326322643409907263432907559884205179526142416⟩,⟨-766044443118978035202392650555416673935832457080898383898648,-766044443118978035202392650555416673935832457079880205033532⟩⟩,
  ⟨⟨1622319150690555421030052795640416435340535149061199048322284,1622319150690555421030052795640416435340535149081918309846068⟩,⟨1622319150690555421030052795640416435340535149061164446332861,1622319150690555421030052795640416435340535149081882639197323⟩⟩,
  ⟨⟨-808121704448264933562500704645117726092205315238339912840664,-808121704448264933562500704645117726092205315002038824764664⟩,⟨-3131457817960248921236464362304322261694031402676392896268604,-3131457817960248921236464362304322261694031402440091470703850⟩⟩,
  ⟨⟨90230264452599350625267494529583087468870233956524634882790,90230264452599350625267494529583087468870235865054979400758⟩,⟨3600582784712126904031969058367812923420748439592616632647309,3600582784712126904031969058367812923420748441501143897298760⟩⟩,
  ⟨⟨2777737210472681052295986753824163753433491812524515746292283,2777737210472681052295986753824163753433491824595164238027771⟩,⟨-1103514084499157157088170676503207557465596762491463644801740,-1103514084499157157088170676503207557465596750420813782893697⟩⟩,
  ⟨⟨-4353777418318757851458945400985351077826047832890109088556545,-4353777418318757851458945400985351077826047769381888341189932⟩,⟨-74033175772932835464251942751710852011338412185500819052971,-74033175772932835464251942751710852011338348677243976864831⟩⟩,
  ⟨⟨3251687369806599027837100309841561387583083877033808586187486,3251687369806599027837100309841561387583084167414787180557867⟩,⟨3245992595986006103297083061499160471362269045782688198208887,3245992595986006103297083061499160471362269336163459346119849⟩⟩,
  ⟨⟨-2689729275466474278886959458636871020868891261429629794082706,-2689729275466474278886959458636871020868890066320875332035867⟩,⟨-2653382097173519678216383079625354895350805326832273935443075,-2653382097173519678216383079625354895350804131722859788736980⟩⟩,
  ⟨⟨-2029593212260685551656740680819598056642017989511685165536511,-2029593212260685551656740680819598056642013429328604772081711⟩,⟨1410474508180377524042737816673675976221704632248600496943752,1410474508180377524042737816673675976221709192430312340409865⟩⟩,
  ⟨⟨3058109782595500226908538589892048910070446767543530998455239,3058109782595500226908538589892048910070463302741340938663456⟩,⟨-274413076174114954951380211890201539924460011376393850373073,-274413076174114954951380211890201539924443476175691716584342⟩⟩,
  ⟨⟨-5585627282889308501828257651556422625976986543646250635168333,-5585627282889308501828257651556422625976928448060916231593257⟩,⟨-3447272609893326880671648238880571139217942509463571824590087,-3447272609893326880671648238880571139217884413888022565356547⟩⟩,
  ⟨⟨2926552672576453703453196886790535020797856832805083073553371,2926552672576453703453196886790535020798057391267579011615846⟩,⟨2759859559463095882700335100210078921515725489901973276741718,2759859559463095882700335100210078921515926048392973354636380⟩⟩,
  ⟨⟨2694098577531239004734848780376805374062097386488865265406300,2694098577531239004734848780376805374062783727910818435912317⟩,⟨-6050863743816623415844361919207507386937591500667905142187912,-6050863743816623415844361919207507386936905159299545045111069⟩⟩,
  ⟨⟨-6252615108643266929774053794178576630876762482732503826391195,-6252615108643266929774053794178576630874422778102616576120348⟩,⟨2433187348258195477901500437954032906179854603202159600389533,2433187348258195477901500437954032906182194307903197112720106⟩⟩,
  ⟨⟨11883033167175339173210218979668173204860889213313902812004022,11883033167175339173210218979668173204868853070219388825402074⟩,⟨-3981928411916720749446,3981928411916722570290⟩⟩,
  ⟨⟨-6252615108643266929774053794178576630889139096608441352315799,-6252615108643266929774053794178576630862046164226679047704950⟩,⟨-2433187348258195477901500437954032906194570921787591392624107,-2433187348258195477901500437954032906167477989317765323081993⟩⟩,
  ⟨⟨2694098577531239004734848780376805374016363253503550620264226,2694098577531239004734848780376805374108517860896133077417927⟩,⟨6050863743816623415844361919207507386891171026330559096150843,6050863743816623415844361919207507386983325633636891091323428⟩⟩,
  ⟨⟨2926552672576453703453196886790535020641235738677179274601744,2926552672576453703453196886790535020954678485395482813310808⟩,⟨-2759859559463095882700335100210078921672547142546677892541032,-2759859559463095882700335100210078921359104395748268736315556⟩⟩,
  ⟨⟨-5585627282889308501828257651556422626510003237002357261861110,-5585627282889308501828257651556422625443911754704809605085871⟩,⟨3447272609893326880671648238880571138684867720560760492637701,3447272609893326880671648238880571139750959202790833893548465⟩⟩,
  ⟨⟨3058109782595500226908538589892048908257447364044792274251690,3058109782595500226908538589892048911883462706240079660242493⟩,⟨274413076174114954951380211890201538111444072656449072323187,274413076174114954951380211890201541737459414895636497530084⟩⟩,
  ⟨⟨-2029593212260685551656740680819598062808456894143167042007142,-2029593212260685551656740680819598050475574524697122891595836⟩,⟨-1410474508180377524042737816673675982388148097052029973831655,-1410474508180377524042737816673675970055265727626882863601572⟩⟩,
  ⟨⟨-2689729275466474278886959458636871041842322988338682914463974,-2689729275466474278886959458636870999895458339411822214608159⟩,⟨2653382097173519678216383079625354874377372404809954127175621,2653382097173519678216383079625354916324237053745179594104035⟩⟩,
  ⟨⟨3251687369806599027837100309841561316247796009984919113577790,3251687369806599027837100309841561458918372034463676653103255⟩,⟨-3245992595986006103297083061499160542697557203210661937039012,-3245992595986006103297083061499160400026981178735485602955584⟩⟩,
  ⟨⟨-4353777418318757851458945400985351320453159506951991651871188,-4353777418318757851458945400985350835198936095320005774578868⟩,⟨74033175772932835464251942751710609384226674614569573650299,74033175772932835464251942751711094638450086248175219268858⟩⟩,
  ⟨⟨2777737210472681052295986753824162928204955363213078863834584,2777737210472681052295986753824164578662028273906601115865849⟩,⟨1103514084499157157088170676503206732237060301109702990636584,1103514084499157157088170676503208382694133211802574436706240⟩⟩,
  ⟨⟨90230264452599350625267494529580280683871721235483465853580,90230264452599350625267494529585894253868748586096151394644⟩,⟨-3600582784712126904031969058367815730205746954222297421931711,-3600582784712126904031969058367810116635749926871463104204388⟩⟩,
  ⟨⟨-808121704448264933562500704645127272589544961226256606922359,-808121704448264933562500704645108179594865669014122129853500⟩,⟨3131457817960248921236464362304312715196691756452207074217255,3131457817960248921236464362304331808191371048664277287849405⟩⟩,
  ⟨⟨1622319150690555421030052795640383965589020828101257778863855,1622319150690555421030052795640448905092049470041859574924666⟩,⟨-1622319150690555421030052795640448905092049470041833145066767,-1622319150690555421030052795640383965589020828101213937656921⟩⟩,
  ⟨⟨-642787609686539326322643409907373869722853736040525112184417,-642787609686539326322643409907152996092266032370852648489965⟩,⟨766044443118978035202392650555306237120538605245555107448638,766044443118978035202392650555527110751126308915223482974047⟩⟩,
  ⟨⟨-375620064935486225040450475719,375620064935486225040448010319⟩,⟨-375620064935486225041042360782,375620064935486225041037302159⟩⟩,
  ⟨⟨-1277567021529219894102778263393,1277567021529219894102776006253⟩,⟨-1277567021529219894102592308686,1277567021529219894102597770254⟩⟩]
lemma restBox13_calc (j : Fin 31) : recoverRest phaseBox13 restBox13 j = restBox13 j := by
  revert j
  decide +kernel
lemma restBox13_mem (j : Fin 31) : (restBox13 j).Mem ((restPolynomial ⟨7,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨7,by norm_num⟩ phaseBox13
  · have hr : residue ⟨7,by norm_num⟩ = (13:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox13_mem
  · exact restBox13_calc
def cBox13 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-19580430313357954872034103663248574042515901359362675686604,-19580430313357954872034103663248574042515901359331519243016⟩,⟨-23335048170484914988453136141165932166689530925502406877438,-23335048170484914988453136141165932166689530925471242820010⟩⟩,
  ⟨⟨49418667375392148676379844238792133385413773971529833621446,49418667375392148676379844238792133385413773972161293029020⟩,⟨49418667375392148676379844238792133385413773971528779584589,49418667375392148676379844238792133385413773972160206438938⟩⟩,
  ⟨⟨-24616794848266757729821300182897265522355200689708846035122,-24616794848266757729821300182897265522355200682510546545444⟩,⟨-95389660067796766486550332777764559842356706726739447912613,-95389660067796766486550332777764559842356706719540687588378⟩⟩,
  ⟨⟨2748571034422318699473571956460269052034712091803621418638,2748571034422318699473571956460269052034712149940797829794⟩,⟨109680023760745019489955393763268478675276265989531292381066,109680023760745019489955393763268478675276266047669055720905⟩⟩,
  ⟨⟨84614714189971762236490100703485073297523149007559936634433,84614714189971762236490100703485073297523149375253455178964⟩,⟨-33614961311842518064331204109038671679705146777507723682087,-33614961311842518064331204109038671679705146409814488074231⟩⟩,
  ⟨⟨-132623644349389747063044049248511665268141227927079522528765,-132623644349389747063044049248511665268141225992507644289607⟩,⟨-2255179498256666641698735281523932059658868196293732895779,-2255179498256666641698735281523932059658866261721585096920⟩⟩,
  ⟨⟨99052061654351514124169269104978288693487545143439659380805,99052061654351514124169269104978288693487553988950735421549⟩,⟨98878588923601722798265571154258660966427594784104373029266,98878588923601722798265571154258660966427603629609128785127⟩⟩,
  ⟨⟨-81933839181737056678859311030386106895880925851922875448197,-81933839181737056678859311030386106895880889446827838967533⟩,⟨-80826640814924327272308978941164710039431112244352602723210,-80826640814924327272308978941164710039431075839237478147313⟩⟩,
  ⟨⟨-61824944753546762117752942748156556037288900635407776845961,-61824944753546762117752942748156556037288761724287012810200⟩,⟨42965510535683341256438101791449475845397669139727944934782,42965510535683341256438101791449475845397808050806900491014⟩⟩,
  ⟨⟨93155351139873366384907378193769418560875209697719936404903,93155351139873366384907378193769418560875713388649782132442⟩,⟨-8359100321989241898595993093700805108257950856059410432234,-8359100321989241898595993093700805108257447165042003279803⟩⟩,
  ⟨⟨-170147937080398503471648542021284028301549223875923609546263,-170147937080398503471648542021284028301547454183191969894190⟩,⟨-105009928772709810620909074317698163797551192201251254984705,-105009928772709810620909074317698163797549422508818102556235⟩⟩,
  ⟨⟨89147892399013556127599509751844042930252370797417099600352,89147892399013556127599509751844042930258480157553857335300⟩,⟨84070129797733054195663568217845295907894905121802695453260,84070129797733054195663568217845295907901014482807706615059⟩⟩,
  ⟨⟨82066935733860793592611363413259760554744295765701398224633,82066935733860793592611363413259760554765202921006732222787⟩,⟨-184319850112236357496544192525942586754381678137409120680980,-184319850112236357496544192525942586754360770983735674095188⟩⟩,
  ⟨⟨-190465548131430263825085779272647499309539206234723277514354,-190465548131430263825085779272647499309467934755980137953826⟩,⟨74119125188407506277224867176381668326210288306369327569065,74119125188407506277224867176381668326281559787279087369825⟩⟩,
  ⟨⟨361977890262483171833229981609085417805657015812970977097240,361977890262483171833229981609085417805899608767183252625568⟩,⟨-121296475861345764128,121296475861345819713⟩⟩,
  ⟨⟨-190465548131430263825085779272647499309916219453181723906269,-190465548131430263825085779272647499309090921537521691485988⟩,⟨-74119125188407506277224867176381668326658573005995141219524,-74119125188407506277224867176381668325833275087653273798583⟩⟩,
  ⟨⟨82066935733860793592611363413259760553351154407084523443643,82066935733860793592611363413259760556158344279623606892882⟩,⟨184319850112236357496544192525942586752967629625616199844226,184319850112236357496544192525942586755774819495528594937337⟩⟩,
  ⟨⟨89147892399013556127599509751844042925481419439675772329734,89147892399013556127599509751844042935029431515295184689540⟩,⟨-84070129797733054195663568217845295912671965841334969338521,-84070129797733054195663568217845295903123953763275432652929⟩⟩,
  ⟨⟨-170147937080398503471648542021284028317785840859261656023354,-170147937080398503471648542021284028285310837199853923422816⟩,⟨105009928772709810620909074317698163781312805526358711439767,105009928772709810620909074317698163813787809183710645986512⟩⟩,
  ⟨⟨93155351139873366384907378193769418505648089660857178278379,93155351139873366384907378193769418616102833425512540179013⟩,⟨8359100321989241898595993093700805053030327127554660030966,8359100321989241898595993093700805163485070893546753769345⟩⟩,
  ⟨⟨-61824944753546762117752942748156556225129371475529743743513,-61824944753546762117752942748156555849448290884165045790307⟩,⟨-42965510535683341256438101791449476033238278890631431536230,-42965510535683341256438101791449475657557198299903413892032⟩⟩,
  ⟨⟨-81933839181737056678859311030386107534768191524295646111784,-81933839181737056678859311030386106256993623774455068393970⟩,⟨80826640814924327272308978941164709400543810166747352368336,80826640814924327272308978941164710678318377916842728413784⟩⟩,
  ⟨⟨99052061654351514124169269104978286520490412163186433396295,99052061654351514124169269104978290866484686969203961404165⟩,⟨-98878588923601722798265571154258663139424736609810969414831,-98878588923601722798265571154258658793430461803902532267471⟩⟩,
  ⟨⟨-132623644349389747063044049248511672658985700772513032665281,-132623644349389747063044049248511657877296753147074134052677⟩,⟨2255179498256666641698735281523924668814393416263954137642,2255179498256666641698735281523939450503341041751363763627⟩⟩,
  ⟨⟨84614714189971762236490100703485048159624398252453908502764,84614714189971762236490100703485098435421900130359483169888⟩,⟨33614961311842518064331204109038646541806395654718393218153,33614961311842518064331204109038696817603897532603818527479⟩⟩,
  ⟨⟨2748571034422318699473571956460183552474297793221913888987,2748571034422318699473571956460354551595126448522505449827⟩,⟨-109680023760745019489955393763268564174836680346254185798002,-109680023760745019489955393763268393175715851690946162187909⟩⟩,
  ⟨⟨-24616794848266757729821300182897556325293961053585208919839,-24616794848266757729821300182896974719416440318634183635523⟩,⟨95389660067796766486550332777764269039417946355665308544692,95389660067796766486550332777764850645295467090614826806844⟩⟩,
  ⟨⟨49418667375392148676379844238791144300221033169020845607289,49418667375392148676379844238793122470606514774670280909792⟩,⟨-49418667375392148676379844238793122470606514774669475810263,-49418667375392148676379844238791144300221033169019510127739⟩⟩,
  ⟨⟨-19580430313357954872034103663251938140288328805824396555650,-19580430313357954872034103663245209944743473912869798215421⟩,⟨23335048170484914988453136141162568068917103479009576016360,23335048170484914988453136141169296264461958371964073726480⟩⟩,
  ⟨⟨-11442041500076375055380442254,11442041500076375055380367154⟩,⟨-11442041500076375055398472105,11442041500076375055398318010⟩⟩]
lemma cBox13_calc (j : Fin 31) : cCoeffBox restBox13 j = cBox13 j := by
  revert j
  decide +kernel
lemma cBox13_mem (j : Fin 31) : (cBox13 j).Mem (cCoefficient ⟨7,by norm_num⟩ j) := by
  rw [← cBox13_calc]
  exact cCoeffBox_mem ⟨7,by norm_num⟩ restBox13 restBox13_mem j
def dBox13 : Fin 31 → CI :=
  ![⟨⟨-62403109972,64122549251⟩,⟨87266462599716478846184538424430635672143594427022854019608,87266462599716478846184538424430635672143594427149645983688⟩⟩,
  ⟨⟨-17449969529192285706525055550956464362967387152009327851502,-17449969529192285706525055550956464362967387149459014652869⟩,⟨-199454064400259554764599631361387403223952236732141357604549,-199454064400259554764599631361387403223952236729590476563590⟩⟩,
  ⟨⟨-35691755575021880690632652555016546814720203052589639133049,-35691755575021880690632652555016546814720203023407517333674⟩,⟨269822200080984273853445433615046568555591386463261753849392,269822200080984273853445433615046568555591386492444505222983⟩⟩,
  ⟨⟨-3515582712801591269172999617852814154799638706789304100634,-3515582712801591269172999617852814154799638469593745939152⟩,⟨-263210246652608341982344575532768607236995722172921234093306,-263210246652608341982344575532768607236995721935725056861922⟩⟩,
  ⟨⟨-17913702388310802049758239027145398638305701765648211350435,-17913702388310802049758239027145398638305700252577760499729⟩,⟨81963367985453275964350490747430806621415929745046274620155,81963367985453275964350490747430806621415931258116917585046⟩⟩,
  ⟨⟨78894903178015150724851413936118612884647943077053228858507,78894903178015150724851413936118612884647951119646138792269⟩,⟨13531480489809717287620037663662634812830378657561649360297,13531480489809717287620037663662634812830386700154742064070⟩⟩,
  ⟨⟨-159086603581942902614981469893983888613689989785873256024490,-159086603581942902614981469893983888613689952601325491646657⟩,⟨-169810330253978055405292504988094187077236638427638688695388,-169810330253978055405292504988094187077236601243093028800645⟩⟩,
  ⟨⟨326172858356647899232637378931667217363271892003456629971013,326172858356647899232637378931667217363272046742646314846469⟩,⟨88984895086233237835393820183014048068347509662350003102838,88984895086233237835393820183014048068347664401546617262248⟩⟩,
  ⟨⟨-184658166843689753963979846368376659038083328726847309286164,-184658166843689753963979846368376659038082732380198581238576⟩,⟨-15037672036791746335724694693473638253093931677123700235227,-15037672036791746335724694693473638253093335330492434818040⟩⟩,
  ⟨⟨108819181856341709266850522493336923706585251380214666540503,108819181856341709266850522493336923706587431211502845214836⟩,⟨-126695065343300956952164063819954919071080892249051018313688,-126695065343300956952164063819954919071078712417724447169896⟩⟩,
  ⟨⟨236587904727616980696697421237547250207621484823505026510259,236587904727616980696697421237547250207629187960503707121559⟩,⟨335631397328104005734830019296362576600023403205450474352280,335631397328104005734830019296362576600031106342329626992271⟩⟩,
  ⟨⟨-229870732671268424244129766028553797505914209590530456147721,-229870732671268424244129766028553797505887519271454274686557⟩,⟨-158772531098149656329482146620440468616322987031944450952765,-158772531098149656329482146620440468616296296712530653994847⟩⟩,
  ⟨⟨47253338717496890611777665403712505595256961135764283732220,47253338717496890611777665403712505595348485039054086625957⟩,⟨170509014422273446120534918987054794222194429249124612969591,170509014422273446120534918987054794222285953151733043627222⟩⟩,
  ⟨⟨204022950441796539435409655519514609635307395843648514769738,204022950441796539435409655519514609635619705420526431912217⟩,⟨167739282615654754559132956965827017335393727990339025561819,167739282615654754559132956965827017335706037568288913701626⟩⟩,
  ⟨⟨-635065146950070759430295951592764626426121801514301266688196,-635065146950070759430295951592764626425058313358306757392904⟩,⟨-110942094184458769587637694457872359816207682868357969176138,-110942094184458769587637694457872359815144194713819459995609⟩⟩,
  ⟨⟨563001045948766460002503846225506152320508691072178650400694,563001045948766460002503846225506152324127251014597988877246⟩,⟨-1809279972065218456323,1809279972065218490184⟩⟩,
  ⟨⟨-635065146950070759430295951592764626431744529138748177731152,-635065146950070759430295951592764626419435585733859846301296⟩,⟨110942094184458769587637694457872359809521467089548183405623,110942094184458769587637694457872359821830410492629245714928⟩⟩,
  ⟨⟨204022950441796539435409655519514609614530177178342056071686,204022950441796539435409655519514609656396924085832890547458⟩,⟨-167739282615654754559132956965827017356483256233963852373372,-167739282615654754559132956965827017314616509324664086899225⟩⟩,
  ⟨⟨47253338717496890611777665403712505524103141287457150330451,47253338717496890611777665403712505666502304887361220062449⟩,⟨-170509014422273446120534918987054794293439772999554285060342,-170509014422273446120534918987054794151040609401303371490384⟩⟩,
  ⟨⟨-229870732671268424244129766028553797748066817734673766113212,-229870732671268424244129766028553797263734911127310964708014⟩,⟨158772531098149656329482146620440468374143688567889282353395,158772531098149656329482146620440468858475595176585822533164⟩⟩,
  ⟨⟨236587904727616980696697421237547249383965025047756247078164,236587904727616980696697421237547251031285647736252486504110⟩,⟨-335631397328104005734830019296362577423687566117663122874560,-335631397328104005734830019296362575776366943430116978448907⟩⟩,
  ⟨⟨108819181856341709266850522493336920905135055711813225470964,108819181856341709266850522493336926508037626879904286332133⟩,⟨126695065343300956952164063819954916269628516749061023383575,126695065343300956952164063819954921872531087917714442118772⟩⟩,
  ⟨⟨-184658166843689753963979846368376668566439322101613837573185,-184658166843689753963979846368376649509726739005432052968090⟩,⟨15037672036791746335724694693473628724737341955849076958595,15037672036791746335724694693473647781449925051767058039090⟩⟩,
  ⟨⟨326172858356647899232637378931667184955222133692005391956693,326172858356647899232637378931667249771321805054097552832360⟩,⟨-88984895086233237835393820183014080476397422713047811042217,-88984895086233237835393820183014015660297751350848809279095⟩⟩,
  ⟨⟨-159086603581942902614981469893983998840644210242632305902346,-159086603581942902614981469893983778386735732144566441718583⟩,⟨169810330253978055405292504988094076850282380786355630749541,169810330253978055405292504988094297304190858884376086735848⟩⟩,
  ⟨⟨78894903178015150724851413936118237978366926032716243210578,78894903178015150724851413936118987790928968163983124403565⟩,⟨-13531480489809717287620037663663009719111403744501453378872,-13531480489809717287620037663662259906549361613214938081121⟩⟩,
  ⟨⟨-17913702388310802049758239027146673777590072535672511878258,-17913702388310802049758239027144123499021329482553459973938⟩,⟨-81963367985453275964350490747432081760700302028137363194572,-81963367985453275964350490747429531482131558975025828964765⟩⟩,
  ⟨⟨-3515582712801591269172999617857151185884092019388622830257,-3515582712801591269172999617848477123715185156994427171220⟩,⟨263210246652608341982344575532764270205911268623124430188234,263210246652608341982344575532772944268080175485521860736665⟩⟩,
  ⟨⟨-35691755575021880690632652555031298017869578209241693375896,-35691755575021880690632652555001795611570827866755463135456⟩,⟨-269822200080984273853445433615061319758740761649096192911515,-269822200080984273853445433615031817352442011306610066178008⟩⟩,
  ⟨⟨-17449969529192285706525055551006636471517436210947157738759,-17449969529192285706525055550906292254417338090521184749197⟩,⟨199454064400259554764599631361337231115402187670652540950009,199454064400259554764599631361437575332502285791079293261297⟩⟩,
  ⟨⟨-170646451741431684825163837459,170646451741431684826883302404⟩,⟨-87266462599716478846184538424601282123885026111912385677699,-87266462599716478846184538424259989220402162742260114371743⟩⟩]
lemma dBox13_calc (j : Fin 31) : dCoeffBox phaseBox13 restBox13 j = dBox13 j := by
  revert j
  decide +kernel
lemma dBox13_mem (j : Fin 31) : (dBox13 j).Mem (dCoefficient ⟨7,by norm_num⟩ j) := by
  rw [← dBox13_calc]
  apply dCoeffBox_mem ⟨7,by norm_num⟩ phaseBox13 restBox13
  · have hr : residue ⟨7,by norm_num⟩ = (13:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox13_mem
  · exact restBox13_mem
def restBox16 : Fin 31 → CI :=
  ![⟨⟨-939692620785908384054109277324731469936208134264932624675400,-939692620785908384054109277324731469936208134264002881288675⟩,⟨-342020143325668733044099614682259580763083367514616756222741,-342020143325668733044099614682259580763083367513687357140495⟩⟩,
  ⟨⟨3064177772475912140809570602221666695743329828312251538515964,3064177772475912140809570602221666695743329828330899116012093⟩,⟨-9356007407618,9290944777211⟩⟩,
  ⟨⟨-5085122305476703187364720482529611083744456859978470030636908,-5085122305476703187364720482529611083744456859769068170473925⟩,⟨-245187885038432948748028028940247213691231159043736269919611,-245187885038432948748028028940247213691231158834340978251123⟩⟩,
  ⟨⟨8573977952239538163515085061726722123873918976434848978267220,8573977952239538163515085061726722123873918978095518979052628⟩,⟨684040286651337466088199229364519161526166734197911443828900,684040286651337466088199229364519161526166735858583545172718⟩⟩,
  ⟨⟨-9681388964190571398579076385862111127359451607487916867995426,-9681388964190571398579076385862111127359451597224319228644048⟩,⟨-1040387334334645703897258790874279652123888614603985955213819,-1040387334334645703897258790874279652123888604340390519163067⟩⟩,
  ⟨⟨10170244610953406374729440965059222167488913693533664305400963,10170244610953406374729440965059222167488913745961462441214482⟩,⟨5797687355428373067139426614967624805117368768600293658541464,5797687355428373067139426614967624805117368821027907907209078⟩⟩,
  ⟨⟨-10106066838477494233919870362837555471745584006846160343003504,-10106066838477494233919870362837555471745583776005870667783734⟩,⟨-10532117816773418059755629475259749298232599367647135073843909,-10532117816773418059755629475259749298232599136806117592528959⟩⟩,
  ⟨⟨6539829672761597120132145060203629679230740386283748692996556,6539829672761597120132145060203629679230741292382109651564087⟩,⟨18983460964877544711716741368770939292217420832460714967280694,18983460964877544711716741368770939292217421738556924735649535⟩⟩,
  ⟨⟨-4564177772475912140809570602221666695743331459687097116766735,-4564177772475912140809570602221666695743328196956287813903158⟩,⟨-26011143958356558786970939037268334324696666122349075092041614,-26011143958356558786970939037268334324696662859614735620335081⟩⟩,
  ⟨⟨-2716881417142051443106137348683037103742583997857550890571102,-2716881417142051443106137348683037103742572950049116343467298⟩,⟨29321914265076491202880227672546663856306310596685603908920215,29321914265076491202880227672546663856306321644485162195431314⟩⟩,
  ⟨⟨9294729762643410131484902289956157393296017457490349177034200,9294729762643410131484902289956157393296053370118733596293173⟩,⟨-30430480048983093681543638155507954055832797881104647012318050,-30430480048983093681543638155507954055832761968441716768977298⟩⟩,
  ⟨⟨-20276311449430900608649311327896777639234554555705541087400728,-20276311449430900608649311327896777639234440666641291396416739⟩,⟨23524226909648118135740801057579039051188890381283203494771248,23524226909648118135740801057579039051189004270259273674768017⟩⟩,
  ⟨⟨31766978096215571136685201086228027748271806300139485826223381,31766978096215571136685201086228027748272162634619165710188555⟩,⟨-18831049125267871282890154016744170286692501886487247974058665,-18831049125267871282890154016744170286692145551875538186577067⟩⟩,
  ⟨⟨-38518474619383860173915682654270462833826370878416902575133014,-38518474619383860173915682654270462833825263290412291416388961⟩,⟨8072126540672136043526087368200208843508296636982807116557881,8072126540672136043526087368200208843509404224834902136428312⟩⟩,
  ⟨⟨44956356240147933006084266752461055234852284040204704563434235,44956356240147933006084266752461055234855716919524458320254339⟩,⟨-1716439745766806092058,1716439745766808388410⟩⟩,
  ⟨⟨-38518474619383860173915682654270462833831131180218848646237355,-38518474619383860173915682654270462833820502988610345345919233⟩,⟨-8072126540672136043526087368200208843514164526626433578904744,-8072126540672136043526087368200208843503536335191275679130522⟩⟩,
  ⟨⟨31766978096215571136685201086228027748255538293680817381320694,31766978096215571136685201086228027748288430641077834155737764⟩,⟨18831049125267871282890154016744170286675877545402348145559380,18831049125267871282890154016744170286708769892960438021529262⟩⟩,
  ⟨⟨-20276311449430900608649311327896777639285389611179783023728051,-20276311449430900608649311327896777639183605611167049459666945⟩,⟨-23524226909648118135740801057579039051239839325703490994979731,-23524226909648118135740801057579039051138055325838986182737372⟩⟩,
  ⟨⟨9294729762643410131484902289956157393138557295645023051461015,9294729762643410131484902289956157393453513531964059719091401⟩,⟨30430480048983093681543638155507954055675301806560943276741988,30430480048983093681543638155507954055990258042985420514345333⟩⟩,
  ⟨⟨-2716881417142051443106137348683037104229868489458696261685679,-2716881417142051443106137348683037103255288458447970966055386⟩,⟨-29321914265076491202880227672546663856793606136064135356800277,-29321914265076491202880227672546663855819026105106630757970764⟩⟩,
  ⟨⟨-4564177772475912140809570602221666697251165711253487890994711,-4564177772475912140809570602221666694235493945389897050210921⟩,⟨26011143958356558786970939037268334323188828608041140240048627,26011143958356558786970939037268334326204500373922670481959096⟩⟩,
  ⟨⟨6539829672761597120132145060203629674565001247113106058086273,6539829672761597120132145060203629683896480431552752301288457⟩,⟨-18983460964877544711716741368770939296883160877723696803584120,-18983460964877544711716741368770939287551681693293942906204353⟩⟩,
  ⟨⟨-10106066838477494233919870362837555486182914256484566494043658,-10106066838477494233919870362837555457308253526367464534988037⟩,⟨10532117816773418059755629475259749283795268887167861000037915,10532117816773418059755629475259749312669929617285391668534255⟩⟩,
  ⟨⟨10170244610953406374729440965059222122815073196331358411648830,10170244610953406374729440965059222212162754243163768354963735⟩,⟨-5797687355428373067139426614967624849791209318227318915310916,-5797687355428373067139426614967624760443528271400882646279993⟩⟩,
  ⟨⟨-9681388964190571398579076385862111265594982324311200505368068,-9681388964190571398579076385862110989123920880401035610618372⟩,⟨1040387334334645703897258790874279513888357887520123948984510,1040387334334645703897258790874279790359419331424252513997156⟩⟩,
  ⟨⟨8573977952239538163515085061726721696127798916457933429911305,8573977952239538163515085061726722551620039038072434543296176⟩,⟨-684040286651337466088199229364519589272286795830733685633017,-684040286651337466088199229364518733780046674225761284708354⟩⟩,
  ⟨⟨-5085122305476703187364720482529612407331397713450222956356258,-5085122305476703187364720482529609760157516006297315254365709⟩,⟨245187885038432948748028028940245890104290305369358739716268,245187885038432948748028028940248537278172012508718483765882⟩⟩,
  ⟨⟨3064177772475912140809570602221662600130750693549596276877756,3064177772475912140809570602221670791355908963093554378610966⟩,⟨-4095612579134762152694523502,4095612579134762217785665778⟩⟩,
  ⟨⟨-939692620785908384054109277324744143106273977447159714751185,-939692620785908384054109277324718796766142291081775782033889⟩,⟨342020143325668733044099614682246907593017524345589531959311,342020143325668733044099614682272253933149210682714552329197⟩⟩,
  ⟨⟨-39214949269374853546020360585,39214949269374853546000780568⟩,⟨-39214949269374833157846006298,39214949269374833157871967897⟩⟩,
  ⟨⟨-121343928804708931904354784186,121343928804708931904383601183⟩,⟨-121343928804708902486230631857,121343928804708902486211671145⟩⟩]
lemma restBox16_calc (j : Fin 31) : recoverRest phaseBox16 restBox16 j = restBox16 j := by
  revert j
  decide +kernel
lemma restBox16_mem (j : Fin 31) : (restBox16 j).Mem ((restPolynomial ⟨8,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨8,by norm_num⟩ phaseBox16
  · have hr : residue ⟨8,by norm_num⟩ = (16:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox16_mem
  · exact restBox16_calc
def cBox16 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-28624674153641342903597614282063769361566618192227784502755,-28624674153641342903597614282063769361566618192199280669248⟩,⟨-10418529357494547381300296597045329845068072893316067118486,-10418529357494547381300296597045329845068072893287689677013⟩⟩,
  ⟨⟨93340192681939659953812544564663728666758123701663536299024,93340192681939659953812544564663728666758123702232168215405⟩,⟨-285000283602,283018362573⟩⟩,
  ⟨⟨-154901683599415233601257511394191273285249104983283173365574,-154901683599415233601257511394191273285249104976903441796616⟩,⟨-7468850090336757826755954330336569721614730086471311426294,-7468850090336757826755954330336569721614730080092718531707⟩⟩,
  ⟨⟨261178304111933557075819270755055019638080463337904020762708,261178304111933557075819270755055019638080463388492584551201⟩,⟨20837058714989094762600593194090659690136145761308483228732,20837058714989094762600593194090659690136145811895580943977⟩⟩,
  ⟨⟨-294911972622324723531976328241186866285386290689339128454102,-294911972622324723531976328241186866285386290376690187923212⟩,⟨-31692010536379151917312252996160578363417072791731181985610,-31692010536379151917312252996160578363417072479083984281450⟩⟩,
  ⟨⟨309803367198830467202515022788382546570498209161665366154789,309803367198830467202515022788382546570498210758709397747470⟩,⟨176607656294061714192050696090030074373837647951850226226723,176607656294061714192050696090030074373837649548887808346365⟩⟩,
  ⟨⟨-307848400452903387052725543037386883971459528730073216028106,-307848400452903387052725543037386883971459521698273913835891⟩,⟨-320826655423514117295944595797029698565975891829001637404294,-320826655423514117295944595797029698565975884797180082348458⟩⟩,
  ⟨⟨199214604076119255887703525162118794322309092882697309509577,199214604076119255887703525162118794322309120484033056565874⟩,⟨578269289774269930757264685601738240405117617554728521658685,578269289774269930757264685601738240405117645156001152851324⟩⟩,
  ⟨⟨-139032805649945949855824076971497761700617892874150491853235,-139032805649945949855824076971497761700617793485685547898792⟩,⟨-792344755829520905029405736282398788388154034135956367763185,-792344755829520905029405736282398788388153934747379729603180⟩⟩,
  ⟨⟨-82760940715626804123523588282868054277004117436237098749000,-82760940715626804123523588282868054277003780900746608918646⟩,⟨893196586663468468944120596865350418724186665780808326445463,893196586663468468944120596865350418724187002316033589309566⟩⟩,
  ⟨⟨283133659791116204448706888257314439807969729533373843914499,283133659791116204448706888257314439807970823494595268470598⟩,⟨-926965431539214390869154465718170579554632088563982254418505,-926965431539214390869154465718170579554630994601704405122353⟩⟩,
  ⟨⟨-617651767651733854255240565825769430541959469804002641907474,-617651767651733854255240565825769430541956000544709343459155⟩,⟨716588930369406754752069900775320344350347450669746696488840,716588930369406754752069900775320344350350919926354523279213⟩⟩,
  ⟨⟨967677490209007579082037607943258413042295271772168364572309,967677490209007579082037607943258413042306126341152637559076⟩,⟨-573626559641585491538742490599162805805836617449089213633386,-573626559641585491538742490599162805805825762876085588398417⟩⟩,
  ⟨⟨-1173339835267653407322365386058602635768160983198890757088215,-1173339835267653407322365386058602635768127244138868151345925⟩,⟨245891035901135597135763886615768751347561610113543097931396,245891035901135597135763886615768751347595349168913892081192⟩⟩,
  ⟨⟨1369448924088595957991831509245547466286884315921547727343606,1369448924088595957991831509245547466286988887405638699606788⟩,⟨-52285744657483855590,52285744657483925991⟩⟩,
  ⟨⟨-1173339835267653407322365386058602635768305990284122240260142,-1173339835267653407322365386058602635767982237053636668193169⟩,⟨-245891035901135597135763886615768751347740356253828127523518,-245891035901135597135763886615768751347416603028628862643644⟩⟩,
  ⟨⟨967677490209007579082037607943258413041799719956917055328295,967677490209007579082037607943258413042801678156403946822408⟩,⟨573626559641585491538742490599162805805330211060391926040935,573626559641585491538742490599162805806332169264782876188070⟩⟩,
  ⟨⟨-617651767651733854255240565825769430543507994147330419398784,-617651767651733854255240565825769430540407476201381565954505⟩,⟨-716588930369406754752069900775320344351899444268767698661838,-716588930369406754752069900775320344348798926327333521355730⟩⟩,
  ⟨⟨283133659791116204448706888257314439803173218711321765417832,283133659791116204448706888257314439812767334316647346882125⟩,⟨926965431539214390869154465718170579549834483778572538088999,926965431539214390869154465718170579559428599387114121750326⟩⟩,
  ⟨⟨-82760940715626804123523588282868054291847651889598996775071,-82760940715626804123523588282868054262160246447384710700159⟩,⟨-893196586663468468944120596865350418739030536768720083203590,-893196586663468468944120596865350418709343131328121832868890⟩⟩,
  ⟨⟨-139032805649945949855824076971497761746549150791968175542253,-139032805649945949855824076971497761654686535567867864531232⟩,⟨792344755829520905029405736282398788342222676829342581063566,792344755829520905029405736282398788434085292053993516596087⟩⟩,
  ⟨⟨199214604076119255887703525162118794180182551085495303198571,199214604076119255887703525162118794464435662281235063328521⟩,⟨-578269289774269930757264685601738240547244186953085254949928,-578269289774269930757264685601738240262991075757644419768863⟩⟩,
  ⟨⟨-307848400452903387052725543037386884411245757655418098428508,-307848400452903387052725543037386883531673292772929031991457⟩,⟨320826655423514117295944595797029698126189655871839755761993,320826655423514117295944595797029699005762120754341964057551⟩⟩,
  ⟨⟨309803367198830467202515022788382545209655206739591603435134,309803367198830467202515022788382547931341213180783161076387⟩,⟨-176607656294061714192050696090030075734680651970873387806238,-176607656294061714192050696090030073012994645529864646639937⟩⟩,
  ⟨⟨-294911972622324723531976328241186870496281359669840057544830,-294911972622324723531976328241186862074491221396189259421848⟩,⟨31692010536379151917312252996160574152522003498674960313035,31692010536379151917312252996160582574312141772140205606715⟩⟩,
  ⟨⟨261178304111933557075819270755055006608188521693319600531754,261178304111933557075819270755055032667972405033077005266132⟩,⟨-20837058714989094762600593194090672720028087456334838549111,-20837058714989094762600593194090646660244204116869225055003⟩⟩,
  ⟨⟨-154901683599415233601257511394191313604012983600028265176995,-154901683599415233601257511394191232966485226360158350277972⟩,⟨7468850090336757826755954330336529402850851463553873646271,7468850090336757826755954330336610040378608703010155559573⟩⟩,
  ⟨⟨93340192681939659953812544564663603907264493499834654159023,93340192681939659953812544564663853426251753904061050384669⟩,⟨-124759493630201813573070226,124759493630201815555859838⟩⟩,
  ⟨⟨-28624674153641342903597614282064155408403215722437839044596,-28624674153641342903597614282063383314730020661989225847806⟩,⟨10418529357494547381300296597044943798231475363508037156734,10418529357494547381300296597045715891904670423095718753081⟩⟩,
  ⟨⟨-1194555666350364144385521532,1194555666350364144384925090⟩,⟨-1194555666350363523326214935,1194555666350363523327005771⟩⟩]
lemma cBox16_calc (j : Fin 31) : cCoeffBox restBox16 j = cBox16 j := by
  revert j
  decide +kernel
lemma cBox16_mem (j : Fin 31) : (cBox16 j).Mem (cCoefficient ⟨8,by norm_num⟩ j) := by
  rw [← cBox16_calc]
  exact cCoeffBox_mem ⟨8,by norm_num⟩ restBox16 restBox16_mem j
def dBox16 : Fin 31 → CI :=
  ![⟨⟨-51827941654,53547380933⟩,⟨87266462599716478846184538424430635672143594427033405136294,87266462599716478846184538424430635672143594427139094866778⟩⟩,
  ⟨⟨-91456170927759873883136228063441721756557472754468701734531,-91456170927759873883136228063441721756557472752379371969706⟩,⟨-251273764493802546582199074203781309579031924709903813854885,-251273764493802546582199074203781309579031924707813847030483⟩⟩,
  ⟨⟨187762575310302153026501687005379923063644735962547860162886,187762575310302153026501687005379923063644735986080837714502⟩,⟨357466701171119366105852128545454222146042603345675412360282,357466701171119366105852128545454222146042603369209460526278⟩⟩,
  ⟨⟨-291268930075817916917525973157170535353152786160628234151195,-291268930075817916917525973157170535353152785972781123499439⟩,⟨-472240204583844893938031745214101791911880319420195626268930,-472240204583844893938031745214101791911880319232347674286498⟩⟩,
  ⟨⟨375525150620604306053003374010759846127289471362910749752655,375525150620604306053003374010759846127289472534339445503007⟩,⟨415281066387888614318213609983131983485920254404913612294509,415281066387888614318213609983131983485920255576343313267848⟩⟩,
  ⟨⟨-140118983056299762701352785020324224329480601750559470784084,-140118983056299762701352785020324224329480595700721849772709⟩,⟨-324359093176608016639114400402749501747369667741221701316476,-324359093176608016639114400402749501747369661691373629349324⟩⟩,
  ⟨⟨-187762575310302153026501687005379923063644749458155446952510,-187762575310302153026501687005379923063644722490460968107522⟩,⟨380228401823439083203647903097891322848675481613506502721070,380228401823439083203647903097891322848675508581164005760027⟩⟩,
  ⟨⟨582537860151635833835051946314341070706305518527635944714130,582537860151635833835051946314341070706305625739159960766820⟩,⟨-441932880180084694711665342020640964665696842840655237799204,-441932880180084694711665342020640964665696735629010131384827⟩⟩,
  ⟨⟨-831475508205750094474322572968439327316945023414347321292541,-831475508205750094474322572968439327316944632656127969866805⟩,⟨636247506477930961674046280993452465818768454229054543571711,636247506477930961674046280993452465818768844987050508027601⟩⟩,
  ⟨⟨733687807171153988051225134451187381729977090949416429886203,733687807171153988051225134451187381729978427999497031783251⟩,⟨-682681021368540351337509875154911676807330523896621262348090,-682681021368540351337509875154911676807329186845966886621520⟩⟩,
  ⟨⟨-503593949839148178746468100942735179923821684229410347089265,-503593949839148178746468100942735179923817302441166731323818⟩,⟨548125816857401514235318396362313877232705276990288960099566,548125816857401514235318396362313877232709658776545466722127⟩⟩,
  ⟨⟨210843723111276434549210148210250900290779914804360714895439,210843723111276434549210148210250900290793889053036803851779⟩,⟨-137355488101889987342562803741841692727118783164445062276136,-137355488101889987342562803741841692727104808910708025030880⟩⟩,
  ⟨⟨-274368512783279621649408684190325165269694354792371435016301,-274368512783279621649408684190325165269650481728155098156608⟩,⟨-372503062108843343487664686977624618563787981602400698185687,-372503062108843343487664686977624618563744108546872355859917⟩⟩,
  ⟨⟨487712752421147381971418466947716613679029802827960042122948,487712752421147381971418466947716613679166425676843013960114⟩,⟨552871157018090846123517700054093710623700386254549234813696,552871157018090846123517700054093710623837009115987169723273⟩⟩,
  ⟨⟨-745737991008909878059113192539536272263140249628853250133353,-745737991008909878059113192539536272262716423998006291597924⟩,⟨-519528946495267252194038685582268955814571025194565349312008,-519528946495267252194038685582268955814147199579563035848909⟩⟩,
  ⟨⟨975425504842294763942836933895433227357539901880496759083580,975425504842294763942836933895433227358852555129109354681592⟩,⟨-656326632803637980808,656326632803638183559⟩⟩,
  ⟨⟨-745737991008909878059113192539536272264959834920786478906111,-745737991008909878059113192539536272260896838706073062691931⟩,⟨519528946495267252194038685582268955812327614288387206415115,519528946495267252194038685582268955816390610485741178363089⟩⟩,
  ⟨⟨487712752421147381971418466947716613672811432154430502020559,487712752421147381971418466947716613685384796350372553812277⟩,⟨-552871157018090846123517700054093710630055379791625889985887,-552871157018090846123517700054093710617482015578910514242972⟩⟩,
  ⟨⟨-274368512783279621649408684190325165289125944059523963683945,-274368512783279621649408684190325165250218892461002569151630⟩,⟨372503062108843343487664686977624618544312519282326046744591,372503062108843343487664686977624618583219570866947007096722⟩⟩,
  ⟨⟨210843723111276434549210148210250900230590953425631818185635,210843723111276434549210148210250900350982850431765700177187⟩,⟨137355488101889987342562803741841692666915847529256710419065,137355488101889987342562803741841692787307744545896376961268⟩⟩,
  ⟨⟨-503593949839148178746468100942735180110085761954910665096901,-503593949839148178746468100942735179737553224715666412932085⟩,⟨-548125816857401514235318396362313877418973736499821195211372,-548125816857401514235318396362313877046441199267013231553637⟩⟩,
  ⟨⟨733687807171153988051225134451187381153608620406462762869432,733687807171153988051225134451187382306346898542450698461933⟩,⟨682681021368540351337509875154911676230960716301654911750575,682681021368540351337509875154911677383698994440933237036334⟩⟩,
  ⟨⟨-831475508205750094474322572968439329100420267205491447023085,-831475508205750094474322572968439325533469388864983843886677⟩,⟨-636247506477930961674046280993452467602244088777826664244165,-636247506477930961674046280993452464035293210438278387076122⟩⟩,
  ⟨⟨582537860151635833835051946314341065187646942515669395978917,582537860151635833835051946314341076224964201751126509366523⟩,⟨441932880180084694711665342020640959147038159616690717458407,441932880180084694711665342020640970184355418852974651381155⟩⟩,
  ⟨⟨-187762575310302153026501687005379940140186538148104757251849,-187762575310302153026501687005379905987102933800511657800988⟩,⟨-380228401823439083203647903097891339925217297271278476088102,-380228401823439083203647903097891305772133692923392032028120⟩⟩,
  ⟨⟨-140118983056299762701352785020324277169907821085461274618368,-140118983056299762701352785020324171489053376365820045820378⟩,⟨324359093176608016639114400402749448906942442356072288829022,324359093176608016639114400402749554587796887076523041492664⟩⟩,
  ⟨⟨375525150620604306053003374010759682621658114260562200732469,375525150620604306053003374010760009632920829636687994297407⟩,⟨-415281066387888614318213609983132146991551612679202359806114,-415281066387888614318213609983131819980288897302054565477619⟩⟩,
  ⟨⟨-291268930075817916917525973157171041293261349414375659019999,-291268930075817916917525973157170029413044222719033698325645⟩,⟨472240204583844893938031745214101285971771755977840903836599,472240204583844893938031745214102297851988882674702396534948⟩⟩,
  ⟨⟨187762575310302153026501687005378357518829383983514747744779,187762575310302153026501687005381488608460087965113949785835⟩,⟨-357466701171119366105852128545455787690857955349332647975118,-357466701171119366105852128545452656601227251365552224847630⟩⟩,
  ⟨⟨-91456170927759873883136228063446566066244314844293260917129,-91456170927759873883136228063436877446870630662554812440516⟩,⟨251273764493802546582199074203776465269345082616415110556504,251273764493802546582199074203786153888718766801302550387410⟩⟩,
  ⟨⟨-14989884742938991971769901044,14989884742938991973489035649⟩,⟨-87266462599716478846184538424445625556886533421330329851216,-87266462599716478846184538424415645787400655432842170328534⟩⟩]
lemma dBox16_calc (j : Fin 31) : dCoeffBox phaseBox16 restBox16 j = dBox16 j := by
  revert j
  decide +kernel
lemma dBox16_mem (j : Fin 31) : (dBox16 j).Mem (dCoefficient ⟨8,by norm_num⟩ j) := by
  rw [← dBox16_calc]
  apply dCoeffBox_mem ⟨8,by norm_num⟩ phaseBox16 restBox16
  · have hr : residue ⟨8,by norm_num⟩ = (16:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox16_mem
  · exact restBox16_mem
def restBox19 : Fin 31 → CI :=
  ![⟨⟨-984807753012208059366743024589523013670643251720262809870705,-984807753012208059366743024589523013670643251719418907257461⟩,⟨173648177666930348851716626769314796000375677183656181365135,173648177666930348851716626769314796000375677184500290264890⟩⟩,
  ⟨⟨2563425528223154234196417784013982101398583003548877429215100,2563425528223154234196417784013982101398583003565564867365967⟩,⟨-2563425528223154234196417784013982101398583003565618772693437,-2563425528223154234196417784013982101398583003548930233049741⟩⟩,
  ⟨⟨-2649881312334498009375392609428804301508150705338367928412568,-2649881312334498009375392609428804301508150705153819740399317⟩,⟨6205275455167810272669364748913508728618405463867500131171246,6205275455167810272669364748913508728618405464052044066412373⟩⟩,
  ⟨⟨2216129172889293536492984530475352509397831648469878501569179,2216129172889293536492984530475352509397831649908131774825052⟩,⟨-11736110899691052726044079014093043537317775574482130042370372,-11736110899691052726044079014093043537317775573043866632749489⟩⟩,
  ⟨⟨3333921598985835475463591838793323463034317435925509576272319,3333921598985835475463591838793323463034317444623761591938188⟩,⟨18332707782645482261114231595423563289597794861483518749723828,18332707782645482261114231595423563289597794870181782042918456⟩⟩,
  ⟨⟨-10400385239298125357126353377192106558574875565808021887346118,-10400385239298125357126353377192106558574875522583926307022033⟩,⟨-19752754941502100187901001581633689244076655479820558844722369,-19752754941502100187901001581633689244076655436596682533892399⟩⟩,
  ⟨⟨16614975070383998179689882148945360466495915795640010697879175,16614975070383998179689882148945360466495915979391345654550316⟩,⟨20319815451004787858884250486978013060201084038262728490219441,20319815451004787858884250486978013060201084222015003882891272⟩⟩,
  ⟨⟨-22651570106437835929245207871255233314319455294608910915727390,-22651570106437835929245207871255233314319454604583551943104085⟩,⟨-15836052369601456808388865138722570327796442022786179133705504,-15836052369601456808388865138722570327796441332763451511154573⟩⟩,
  ⟨⟨21943852275479984523836952733513471924921763772968787922621568,21943852275479984523836952733513471924921766125158649634443812⟩,⟨12660028210617368307180710818639857154912260111679354306844956,12660028210617368307180710818639857154912262463873489313473639⟩⟩,
  ⟨⟨-23487121619013778290463210145470168374043657649411572454463894,-23487121619013778290463210145470168374043650193017748177471589⟩,⟨-13244817425817193383400277931626790409050303121098691911522913,-13244817425817193383400277931626790409050295664716409434062214⟩⟩,
  ⟨⟨23598379384402492121177250973878129186502381434608163930733227,23598379384402492121177250973878129186502403884831104535081216⟩,⟨14825899428823491534127706531729519275399727431338347082917538,14825899428823491534127706531729519275399749881604930055312417⟩⟩,
  ⟨⟨-30854386729697745393252702307774918645135236670995975198724971,-30854386729697745393252702307774918645135171322579415538050201⟩,⟨-20841672060906067883107101738191756694368709894576292176824403,-20841672060906067883107101738191756694368644546267957782255354⟩⟩,
  ⟨⟨41530081700476328740341200274376512742880393557248709088115429,41530081700476328740341200274376512742880579965427034363534576⟩,⟨17303552603924967470733296684429551678585765480307813711061896,17303552603924967470733296684429551678585951888644771997236832⟩⟩,
  ⟨⟨-49032186650524844161151932256984477953055341022523723096004917,-49032186650524844161151932256984477953054815055205147974980501⟩,⟨-12852837434656129612042348593732908804957619600849638178499916,-12852837434656129612042348593732908804957093633723347369297127⟩⟩,
  ⟨⟨56519149358955896777566522617398199531350797981232755549910846,56519149358955896777566522617398199531352274246635911072142642⟩,⟨-738132806087677603555,738132806087674730702⟩⟩,
  ⟨⟨-49032186650524844161151932256984477953057145101584503947843187,-49032186650524844161151932256984477953053010976144367126012083⟩,⟨12852837434656129612042348593732908804955289554680118240787668,12852837434656129612042348593732908804959423679892867313415768⟩⟩,
  ⟨⟨41530081700476328740341200274376512742874703229270263024136061,41530081700476328740341200274376512742886270293405480432861726⟩,⟨-17303552603924967470733296684429551678591642216636515097919742,-17303552603924967470733296684429551678580075152316070618493322⟩⟩,
  ⟨⟨-30854386729697745393252702307774918645151381159181628564140904,-30854386729697745393252702307774918645119026834393762179773308⟩,⟨20841672060906067883107101738191756694352500058141963754572618,20841672060906067883107101738191756694384854382702286215397881⟩⟩,
  ⟨⟨23598379384402492121177250973878129186457147547245496441898426,23598379384402492121177250973878129186547637772193772031916122⟩,⟨-14825899428823491534127706531729519275444983768974887679442536,-14825899428823491534127706531729519275354493543968389473095882⟩⟩,
  ⟨⟨-23487121619013778290463210145470168374170194600033593733692218,-23487121619013778290463210145470168373917113242395726906036202⟩,⟨13244817425817193383400277931626790408923758714201964071660407,13244817425817193383400277931626790409176840071613137292213345⟩⟩,
  ⟨⟨21943852275479984523836952733513471924567860488199888881449575,21943852275479984523836952733513471925275669409927548682037085⟩,⟨-12660028210617368307180710818639857155266165748505300438668130,-12660028210617368307180710818639857154558356827047543204064541⟩⟩,
  ⟨⟨-22651570106437835929245207871255233315309241072873061849793030,-22651570106437835929245207871255233313329668826319401012831186⟩,⟨15836052369601456808388865138722570326806655554799869247737491,15836052369601456808388865138722570328786227800749761423704061⟩⟩,
  ⟨⟨16614975070383998179689882148945360463727721509714436888151052,16614975070383998179689882148945360469264110265316919464177733⟩,⟨-20319815451004787858884250486978013062969278507365522185632844,-20319815451004787858884250486978013057432889752912210217827658⟩⟩,
  ⟨⟨-10400385239298125357126353377192106566316850950528839661444054,-10400385239298125357126353377192106550832900137863108527664260⟩,⟨19752754941502100187901001581633689236334680053008555216383007,19752754941502100187901001581633689251818630863408686195746723⟩⟩,
  ⟨⟨3333921598985835475463591838793323441381870139971829459391429,3333921598985835475463591838793323484686764740577441697282852⟩,⟨-18332707782645482261114231595423563311250242163920272859161982,-18332707782645482261114231595423563267945347567745027969086691⟩⟩,
  ⟨⟨2216129172889293536492984530475352448841132717838118501794637,2216129172889293536492984530475352569954530580539891793319412⟩,⟨11736110899691052726044079014093043476761076646751328095038699,11736110899691052726044079014093043597874474500774668616522814⟩⟩,
  ⟨⟨-2649881312334498009375392609428804470870705173593455028518258,-2649881312334498009375392609428804132145596236898732666788605⟩,⟨-6205275455167810272669364748913508897980959923809992431739958,-6205275455167810272669364748913508559255851004109551801478313⟩⟩,
  ⟨⟨2563425528223154234196417784013981627732161910666087995379969,2563425528223154234196417784013982575065004096448354335700890⟩,⟨2563425528223154234196417784013981627732161927306324677286769,2563425528223154234196417784013982575065004079808224361628501⟩⟩,
  ⟨⟨-984807753012208059366743024589524338401952221963611027628808,-984807753012208059366743024589521688939334281476070731856562⟩,⟨-173648177666930348851716626769316120731684614841209605379448,-173648177666930348851716626769313471269066739526946895090601⟩⟩,
  ⟨⟨-3704955561172471201459926339,3704955561172471201509600522⟩,⟨-3704955561108656368161953370,3704955561108656368184734104⟩⟩,
  ⟨⟨-10361871586584749055940097430,10361871586584749055884030068⟩,⟨-10361871586459779677888990151,10361871586459779677874052430⟩⟩]
lemma restBox19_calc (j : Fin 31) : recoverRest phaseBox19 restBox19 j = restBox19 j := by
  revert j
  decide +kernel
lemma restBox19_mem (j : Fin 31) : (restBox19 j).Mem ((restPolynomial ⟨9,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨9,by norm_num⟩ phaseBox19
  · have hr : residue ⟨9,by norm_num⟩ = (19:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox19_mem
  · exact restBox19_calc
def cBox19 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-29998959670852502253334400260293903887583974252661922254902,-29998959670852502253334400260293903887583974252636024531917⟩,⟨5289625983156427915144478140897837194877087266713827602257,5289625983156427915144478140897837194877087266739574304582⟩⟩,
  ⟨⟨78086407022271780569795821758218198413269382170775846533150,78086407022271780569795821758218198413269382171284672081956⟩,⟨-78086407022271780569795821758218198413269382171286314132106,-78086407022271780569795821758218198413269382170777455029911⟩⟩,
  ⟨⟨-80720000810435206393835349879154567726463443619508748554834,-80720000810435206393835349879154567726463443613886575389358⟩,⟨189023499821901213903802269589175580750885147411238541307570,189023499821901213903802269589175580750885147416861274407702⟩⟩,
  ⟨⟨67507155055958924739506865476422524023515207615668978818468,67507155055958924739506865476422524023515207659481108692414⟩,⟨-357502382059455574647445980170955115113667522474281043405528,-357502382059455574647445980170955115113667522430466758593259⟩⟩,
  ⟨⟨101557059525424301156435943073245227416599589270826380034608,101557059525424301156435943073245227416599589535790935133826⟩,⟨558446214245317866030907332236726730461939952322224489699378,558446214245317866030907332236726730461939952587192296978519⟩⟩,
  ⟨⟨-316813851638276482210105745845552627547356702942999283715638,-316813851638276482210105745845552627547356701626316019986436⟩,⟨-601703324395952791558640268212132304843598359512603356451727,-601703324395952791558640268212132304843598358195924958390532⟩⟩,
  ⟨⟨506121083576086063020068714933506598554881096112685948901954,506121083576086063020068714933506598554881101710074924655714⟩,⟨618976975322717298666015133405325669399951741549123731773832,618976975322717298666015133405325669399951747146542073309327⟩⟩,
  ⟨⟨-690006283994083385615241844205971094361649671524974608116270,-690006283994083385615241844205971094361649650505595771635579⟩,⟨-482393741243518841048223492776900887676042270870130483109826,-482393741243518841048223492776900887676042249850833123838616⟩⟩,
  ⟨⟨668447966033740715972586642084335948860231481516704581744113,668447966033740715972586642084335948860231553168509489527479⟩,⟨385646512794520419157083715915497786976514590509616856569899,385646512794520419157083715915497786976514662161550135987056⟩⟩,
  ⟨⟨-715458638580059901986008458442524668361845996529158190953812,-715458638580059901986008458442524668361845769394408869721595⟩,⟨-403460210979846917994325574928498767314801919771670706277635,-403460210979846917994325574928498767314801692637274954608435⟩⟩,
  ⟨⟨718847743922454399947720228927531466340474793034918292267314,718847743922454399947720228927531466340475476907821448921677⟩,⟨451622723002544877139974661387162452885423166620231768972962,451622723002544877139974661387162452885423850494462646974757⟩⟩,
  ⟨⟨-939878367470178921963504273211870500198541921428454833740560,-939878367470178921963504273211870500198539930801844895202854⟩,⟨-634873636723393983507044971236595974941072115797798745401444,-634873636723393983507044971236595974941070125174487478715883⟩⟩,
  ⟨⟨1265078633113030273681581575773852304879836996777787625007695,1265078633113030273681581575773852304879842675095626537354899⟩,⟨527096354735120649335024318014269194272578787681612380576866,527096354735120649335024318014269194272584466004278832625825⟩⟩,
  ⟨⟨-1493605818398317590648981886871000986505573365232055247199583,-1493605818398317590648981886871000986505557343351298089895170⟩,⟨-391519817628296909079952779285602707159119367006676357123971,-391519817628296909079952779285602707159103345131783531010332⟩⟩,
  ⟨⟨1721671744626475063966632333378512160200365871519935349965516,1721671744626475063966632333378512160200410841135749272501570⟩,⟨-22484811085035126531,22484811085035039585⟩⟩,
  ⟨⟨-1493605818398317590648981886871000986505628320622913876371973,-1493605818398317590648981886871000986505502387960439460810458⟩,⟨391519817628296909079952779285602707159048389741459557904904,391519817628296909079952779285602707159174322397000330423569⟩⟩,
  ⟨⟨1265078633113030273681581575773852304879663659475134189248483,1265078633113030273681581575773852304880016012398279973277361⟩,⟨-527096354735120649335024318014269194272757803307337319285939,-527096354735120649335024318014269194272405450378553894163097⟩⟩,
  ⟨⟨-939878367470178921963504273211870500199033710661943906609705,-939878367470178921963504273211870500198048141568355822551594⟩,⟨634873636723393983507044971236595974940578335942815733199285,634873636723393983507044971236595974941563905029470491249177⟩⟩,
  ⟨⟨718847743922454399947720228927531466339096890029384454710045,718847743922454399947720228927531466341853379913355286722940⟩,⟨-451622723002544877139974661387162452886801753500218554752292,-451622723002544877139974661387162452884045263614475861630815⟩⟩,
  ⟨⟨-715458638580059901986008458442524668365700532469774018337051,-715458638580059901986008458442524668357991233453793042576007⟩,⟨403460210979846917994325574928498767310947156699936077046583,403460210979846917994325574928498767318656455709009584396123⟩⟩,
  ⟨⟨668447966033740715972586642084335948849450970970670302258425,668447966033740715972586642084335948871012063714543769209023⟩,⟨-385646512794520419157083715915497786987295172703408478747750,-385646512794520419157083715915497786965734079967758514491537⟩⟩,
  ⟨⟨-690006283994083385615241844205971094391800270516615102219731,-690006283994083385615241844205971094331499051513955277647968⟩,⟨482393741243518841048223492776900887645891650868348475027256,482393741243518841048223492776900887706192869852615132730453⟩⟩,
  ⟨⟨506121083576086063020068714933506598470557076027990091960802,506121083576086063020068714933506598639205121794770781594205⟩,⟨-618976975322717298666015133405325669484275767213720737773276,-618976975322717298666015133405325669315627721481945068234056⟩⟩,
  ⟨⟨-316813851638276482210105745845552627783190759517585899416406,-316813851638276482210105745845552627311522645051729404125838⟩,⟨601703324395952791558640268212132304607764301655842067120159,601703324395952791558640268212132305079432416052686248742816⟩⟩,
  ⟨⟨101557059525424301156435943073245226757028326534715813496313,101557059525424301156435943073245228076170852271901501321075⟩,⟨-558446214245317866030907332236726731121511215255824338607035,-558446214245317866030907332236726729802368689653592449155427⟩⟩,
  ⟨⟨67507155055958924739506865476422522178852669710710722084500,67507155055958924739506865476422525868177745564439365996386⟩,⟨357502382059455574647445980170955113269004984657688746425127,357502382059455574647445980170955116958330060247059056683781⟩⟩,
  ⟨⟨-80720000810435206393835349879154572885541878680084755910964,-80720000810435206393835349879154562567385008553310568840187⟩,⟨-189023499821901213903802269589175585909963582218599634068138,-189023499821901213903802269589175575591806712609500182732679⟩⟩,
  ⟨⟨78086407022271780569795821758218183984565078878919718290927,78086407022271780569795821758218212841973685463140801375051⟩,⟨78086407022271780569795821758218183984565079385810314559212,78086407022271780569795821758218212841973684956253455613337⟩⟩,
  ⟨⟨-29998959670852502253334400260293944241207299171120834931905,-29998959670852502253334400260293863533960649334177113145186⟩,⟨-5289625983156427915144478140897877548500411192552700777149,-5289625983156427915144478140897796841253763340900702008225⟩⟩,
  ⟨⟨-112859400346877519141247487,112859400346877519142760649⟩,⟨-112859400344933608154912740,112859400344933608155606681⟩⟩]
lemma cBox19_calc (j : Fin 31) : cCoeffBox restBox19 j = cBox19 j := by
  revert j
  decide +kernel
lemma cBox19_mem (j : Fin 31) : (cBox19 j).Mem (cCoefficient ⟨9,by norm_num⟩ j) := by
  rw [← cBox19_calc]
  exact cCoeffBox_mem ⟨9,by norm_num⟩ restBox19 restBox19_mem j
def dBox19 : Fin 31 → CI :=
  ![⟨⟨-42583077798,44302517076⟩,⟨87266462599716478846184538424430635672143594427042682259620,87266462599716478846184538424430635672143594427129817743561⟩⟩,
  ⟨⟨-181457271423278353442539591330307138269855717433356022029335,-181457271423278353442539591330307138269855717431661495719402⟩,⟨-259147840492017835097636591434791992491066951319352075211822,-259147840492017835097636591434791992491066951317657379576528⟩⟩,
  ⟨⟨463283353389689492913152625700529092592727468812342369416043,463283353389689492913152625700529092592727468831098942901547⟩,⟨239761622777744388978996186713944534605045962234127162870132,239761622777744388978996186713944534605045962252883356251452⟩⟩,
  ⟨⟨-715879142894163214074909965167889506994367295814875328814300,-715879142894163214074909965167889506994367295667760389729781⟩,⟨-186843456626211955596675440011241833636374199720804791858584,-186843456626211955596675440011241833636374199573692176309978⟩⟩,
  ⟨⟨1052605604807642356909770599267183736629640509771488434136173,1052605604807642356909770599267183736629640510669533929643382⟩,⟨-142411835615632875872479695126482728482201354555008845572373,-142411835615632875872479695126482728482201353656966440657340⟩⟩,
  ⟨⟨-812977363793342802495857965562931326390239989956313477922380,-812977363793342802495857965562931326390239985441158924785590⟩,⟨607100304604663942637492387094525792213327541170105197216736,607100304604663942637492387094525792213327545685274208056550⟩⟩,
  ⟨⟨473072243456819281193494896531721261739175618631327382456264,473072243456819281193494896531721261739175638087054928004015⟩,⟨-555655604929565712607196180868459947826557188629096385673297,-555655604929565712607196180868459947826557169173435639871565⟩⟩,
  ⟨⟨-164254048994606382087931692071709467202526473202483808889137,-164254048994606382087931692071709467202526399075258764761691⟩,⟨513574503728378073777157256851500952568070991964542419784128,513574503728378073777157256851500952568071066091970404268698⟩⟩,
  ⟨⟨-73979948119989317195749242042714556673615934468193110335190,-73979948119989317195749242042714556673615678098319371228723⟩,⟨41798032003651696182358695113588094931528895375612307123387,41798032003651696182358695113588094931529151745116787909188⟩⟩,
  ⟨⟨-476477632554014619234664538028970434614952517268193604596324,-476477632554014619234664538028970434614951693712348011581435⟩,⟨-368873804775857495635611946291443473217333740325247339358974,-368873804775857495635611946291443473217332916768399093134400⟩⟩,
  ⟨⟨876268059154901152680500126938744620329962096201600764848496,876268059154901152680500126938744620329964603589648311986013⟩,⟨274321263132523281150547859763576604296978576265731550490534,274321263132523281150547859763576604296981083650385078512737⟩⟩,
  ⟨⟨-1476351782220317664238898615498549808641422893342140070345224,-1476351782220317664238898615498549808641415533197243729743287⟩,⟨116612691931377481974974485439858545954561218550214706597736,116612691931377481974974485439858545954568578703584341729182⟩⟩,
  ⟨⟨1199865919846385717352609925952783968864379288314723116838990,1199865919846385717352609925952783968864400402736798595624681⟩,⟨-1054183988184891228483685874932210759927210994084364144085838,-1054183988184891228483685874932210759927189879676608142172871⟩⟩,
  ⟨⟨-524008195812816144593888790208054388364147579789167579969521,-524008195812816144593888790208054388364087801134272743537150⟩,⟨1051617433767373144881355401663515306385969753876802285604678,1051617433767373144881355401663515306386029532552970224401118⟩⟩,
  ⟨⟨-1274305368544844319877162087721548204034037842402078145887,-1274305368544844319877162087721548203865950903760215312707⟩,⟨-1025958610177857886849970202129735948881281829755629925325420,-1025958610177857886849970202129735948881113742843011174864403⟩⟩,
  ⟨⟨723129021051270681269578775215770990398059333624373763243050,723129021051270681269578775215770990398530442642206701094991⟩,⟨-235554523768393966555,235554523768394310280⟩⟩,
  ⟨⟨-1274305368544844319877162087721548204609297858345324896986,-1274305368544844319877162087721548203290690887816968684155⟩,⟨1025958610177857886849970202129735948880538482828009185056048,1025958610177857886849970202129735948881857089770631914464153⟩⟩,
  ⟨⟨-524008195812816144593888790208054388365962078542347073364442,-524008195812816144593888790208054388362273302381093249908488⟩,⟨-1051617433767373144881355401663515306387844031311615258076303,-1051617433767373144881355401663515306384155255118157251300493⟩⟩,
  ⟨⟨1199865919846385717352609925952783968859231137805321372349553,1199865919846385717352609925952783968869548553246200339784035⟩,⟨1054183988184891228483685874932210759922041729168663700993446,1054183988184891228483685874932210759932359144592308584697561⟩⟩,
  ⟨⟨-1476351782220317664238898615498549808655847180804897084663307,-1476351782220317664238898615498549808626991245734486715015697⟩,⟨-116612691931377481974974485439858545968992866178179440878699,-116612691931377481974974485439858545940136931075619606949883⟩⟩,
  ⟨⟨876268059154901152680500126938744620289611582777055085794183,876268059154901152680500126938744620370315117014193990562267⟩,⟨-274321263132523281150547859763576604337331597084118758321068,-274321263132523281150547859763576604256628062831997871102978⟩⟩,
  ⟨⟨-476477632554014619234664538028970434727806439181664033672643,-476477632554014619234664538028970434502097771798877581967996⟩,⟨368873804775857495635611946291443473104478994826037324126640,368873804775857495635611946291443473330187662267609108702891⟩⟩,
  ⟨⟨-73979948119989317195749242042714556989242362537191895726437,-73979948119989317195749242042714556357989250029320586423697⟩,⟨-41798032003651696182358695113588095247155579864526090745176,-41798032003651696182358695113588094615902467256203004526464⟩⟩,
  ⟨⟨-164254048994606382087931692071709468085258202230848564634619,-164254048994606382087931692071709466319794670046894008398097⟩,⟨-513574503728378073777157256851500953450802795221791310352994,-513574503728378073777157256851500951685339262834721513567140⟩⟩,
  ⟨⟨473072243456819281193494896531721259270386703532419843836687,473072243456819281193494896531721264207964553185962465995482⟩,⟨555655604929565712607196180868459945357768253877014965814812,555655604929565712607196180868459950295346103925517059713359⟩⟩,
  ⟨⟨-812977363793342802495857965562931333294850153667297664325809,-812977363793342802495857965562931319485629821730174737767245⟩,⟨-607100304604663942637492387094525799117937709783598768516423,-607100304604663942637492387094525785308717377071780636853541⟩⟩,
  ⟨⟨1052605604807642356909770599267183717319102847799473667510702,1052605604807642356909770599267183755940178172641548695690108⟩,⟨142411835615632875872479695126482709171663690926657822112488,142411835615632875872479695126482747792739017285317464323252⟩⟩,
  ⟨⟨-715879142894163214074909965167889561001306981065662840569987,-715879142894163214074909965167889452987427610416972877448614⟩,⟨186843456626211955596675440011241779629434512837834937830075,186843456626211955596675440011241887643313886456662030037232⟩⟩,
  ⟨⟨463283353389689492913152625700528941548277793773606174441511,463283353389689492913152625700529243637177143869835137416657⟩,⟨-239761622777744388978996186713944685649495640199818017024074,-239761622777744388978996186713944383560596284287192501711318⟩⟩,
  ⟨⟨-181457271423278353442539591330307560704933700533129825904107,-181457271423278353442539591330306715834777734331887691462133⟩,⟨259147840492017835097636591434791570055988962522712121732101,259147840492017835097636591434792414926144940114297332600038⟩⟩,
  ⟨⟨-1181449536837289227599044726,1181449536837289229318187288⟩,⟨-87266462599716478846184538424431817121680442869236817196463,-87266462599716478846184538424429454222606745984935682291851⟩⟩]
lemma dBox19_calc (j : Fin 31) : dCoeffBox phaseBox19 restBox19 j = dBox19 j := by
  revert j
  decide +kernel
lemma dBox19_mem (j : Fin 31) : (dBox19 j).Mem (dCoefficient ⟨9,by norm_num⟩ j) := by
  rw [← dBox19_calc]
  apply dCoeffBox_mem ⟨9,by norm_num⟩ phaseBox19 restBox19
  · have hr : residue ⟨9,by norm_num⟩ = (19:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox19_mem
  · exact restBox19_mem
def restBox21 : Fin 31 → CI :=
  ![⟨⟨-866025403784438646763723170752936183471402626905684319569564,-866025403784438646763723170752936183471402626904687414653467⟩,⟨499999999999999999999999999999999999999999999999509043922407,500000000000000000000000000000000000000000000000506360711682⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999989904136672550,1000000000000000000000000000000000000000000000010018001015467⟩,⟨-3732050807568877293527446341505872366942805253820445830920759,-3732050807568877293527446341505872366942805253800331394444234⟩⟩,
  ⟨⟨2866025403784438646763723170752936183471402626791502487420769,2866025403784438646763723170752936183471402627019016010849316⟩,⟨6964101615137754587054892683011744733885610507506959717117229,6964101615137754587054892683011744733885610507734468484436884⟩⟩,
  ⟨⟨-9196152422706631880582339024517617100828415762343449384998767,-9196152422706631880582339024517617100828415760518923897346850⟩,⟨-8464101615137754587054892683011744733885610508532910868072301,-8464101615137754587054892683011744733885610506708384547022069⟩⟩,
  ⟨⟨20392304845413263761164678049035234201656831517139802285951370,20392304845413263761164678049035234201656831528584729114001330⟩,⟨4464101615137754587054892683011744733885610501898116250187917,4464101615137754587054892683011744733885610513343043742176236⟩⟩,
  ⟨⟨-26124355652982141054692124390541106568599636806473359987518362,-26124355652982141054692124390541106568599636746871607498444412⟩,⟨11928203230275509174109785366023489467771220985440881136748830,11928203230275509174109785366023489467771221045042536433994291⟩⟩,
  ⟨⟨18392304845413263761164678049035234201656831388355613096297502,18392304845413263761164678049035234201656831657368371656722899⟩,⟨-29856406460551018348219570732046978935542442164989702323283288,-29856406460551018348219570732046978935542441895976423332550518⟩⟩,
  ⟨⟨2464101615137754587054892683011744733885609962912148302178454,2464101615137754587054892683011744733885611052329890432278932⟩,⟨44516660498395404815856802439576340770256467754826637266112423,44516660498395404815856802439576340770256468844242931452610859⟩⟩,
  ⟨⟨-36454482671904334288510740244305787485956651949206565562470963,-36454482671904334288510740244305787485956647873190887325725757⟩,⟨-39284609690826527522329356098070468403313665083733353094386435,-39284609690826527522329356098070468403313661007715107742605232⟩⟩,
  ⟨⟨59176914536239791283494034147105702604970487347127286573037142,59176914536239791283494034147105702604970501790046039998112829⟩,⟨9464101615137754587054892683011744733885603286164000743567619,9464101615137754587054892683011744733885617729076880872417741⟩⟩,
  ⟨⟨-61444863728670913989966587805599830238027714036786805148495941,-61444863728670913989966587805599830238027664592765478891842804⟩,⟨32856406460551018348219570732046978935542417308460992418503102,32856406460551018348219570732046978935542466752505262496181209⟩⟩,
  ⟨⟨28856406460551018348219570732046978935542359051969474715816138,28856406460551018348219570732046978935542525008995999925370386⟩,⟨-73837168574084177751131265854635064439684603816121188560209648,-73837168574084177751131265854635064439684437859155999499463918⟩⟩,
  ⟨⟨24392304845413263761164678049035234201656555816329004134222882,24392304845413263761164678049035234201657107229395701179794098⟩,⟨80105117766515300457603819513129192072741439877246652525266771,80105117766515300457603819513129192072741991290409349348919980⟩⟩,
  ⟨⟨-71105117766515300457603819513129192072742627427913933711460772,-71105117766515300457603819513129192072740803739742311788253747⟩,⟨-55444863728670913989966587805599830238028601158807663866792469,-55444863728670913989966587805599830238026777470744772851920634⟩⟩,
  ⟨⟨95301270189221932338186158537646809173567121254144454573423320,95301270189221932338186158537646809173573141436373931189439133⟩,⟨-3010091175361187798582,3010091175361189900351⟩⟩,
  ⟨⟨-71105117766515300457603819513129192072751645481634208895007591,-71105117766515300457603819513129192072731785686022036607751768⟩,⟨55444863728670913989966587805599830238017759417032287713549943,55444863728670913989966587805599830238037619212520149002131946⟩⟩,
  ⟨⟨24392304845413263761164678049035234201624081219702949054289295,24392304845413263761164678049035234201689581826021756264413788⟩,⟨-80105117766515300457603819513129192072774465887044020795220131,-80105117766515300457603819513129192072708965280611981078779403⟩⟩,
  ⟨⟨28856406460551018348219570732046978935434433336928410318384809,28856406460551018348219570732046978935650450724037064318707893⟩,⟨73837168574084177751131265854635064439576512144136542281887771,73837168574084177751131265854635064439792529531140645781093513⟩⟩,
  ⟨⟨-61444863728670913989966587805599830238383890324039624424219378,-61444863728670913989966587805599830237671488305512659614797419⟩,⟨-32856406460551018348219570732046978935898643039784842293115011,-32856406460551018348219570732046978935186241021181412627323364⟩⟩,
  ⟨⟨59176914536239791283494034147105702603795786386287994591639185,59176914536239791283494034147105702606145202750885331982187813⟩,⟨-9464101615137754587054892683011744735060318689901418850492394,-9464101615137754587054892683011744732710902325339462759347951⟩⟩,
  ⟨⟨-36454482671904334288510740244305787489830693671104683825056273,-36454482671904334288510740244305787482082606151292769069527417⟩,⟨39284609690826527522329356098070468399439619285812655723557261,39284609690826527522329356098070468407187706805635805109564611⟩⟩,
  ⟨⟨2464101615137754587054892683011744721109490177542482940239373,2464101615137754587054892683011744746661730837699555802525541⟩,⟨-44516660498395404815856802439576340783032588629611285976009086,-44516660498395404815856802439576340757480347969458282743077786⟩⟩,
  ⟨⟨18392304845413263761164678049035234159522757287270040814171046,18392304845413263761164678049035234243790905758453943931420058⟩,⟨29856406460551018348219570732046978893408367794890067700665553,29856406460551018348219570732046978977676516266076057960544559⟩⟩,
  ⟨⟨-26124355652982141054692124390541106707552633537542289434293789,-26124355652982141054692124390541106429646640015802678047964467⟩,⟨-11928203230275509174109785366023489606724217776111096319646772,-11928203230275509174109785366023489328818224254372321260398317⟩⟩,
  ⟨⟨20392304845413263761164678049035233743406931577247080184942723,20392304845413263761164678049035234659906731468477451216975492⟩,⟨-4464101615137754587054892683011745192135510453235892796652801,-4464101615137754587054892683011744275635710562005267184968140⟩⟩,
  ⟨⟨-9196152422706631880582339024517618612080246876430644812127425,-9196152422706631880582339024517615589576584646431728478116647⟩,⟨8464101615137754587054892683011743222633779392621203584393903,8464101615137754587054892683011746245137441622620091821965779⟩⟩,
  ⟨⟨2866025403784438646763723170752931199548662406013279708276621,2866025403784438646763723170752941167394142847797238802151612⟩,⟨-6964101615137754587054892683011749717808350728512702239807401,-6964101615137754587054892683011739749962870286728725958115248⟩⟩,
  ⟨⟨999999999999999999999999999999983563635544341698266677114464,1000000000000000000000000000000016436364455658301655447429170⟩,⟨3732050807568877293527446341505855930578349595508686342809146,3732050807568877293527446341505888803307260912112090886002304⟩⟩,
  ⟨⟨-866025403784438646763723170752990388580630955779865021834173,-866025403784438646763723170752881978362174298030506702255156⟩,⟨-500000000000000000000000000000054205109228328874692077449878,-499999999999999999999999999999945794890771671125323337520322⟩⟩,
  ⟨⟨-178761786061733091426931244780,178761786061733091426927646844⟩,⟨-178761786061733091431726216416,178761786061733091431741204222⟩⟩,
  ⟨⟨-589534392807384755736683412775,589534392807384755736678576100⟩,⟨-589534392807384755740934991867,589534392807384755740919436862⟩⟩]
lemma restBox21_calc (j : Fin 31) : recoverRest phaseBox21 restBox21 j = restBox21 j := by
  revert j
  decide +kernel
lemma restBox21_mem (j : Fin 31) : (restBox21 j).Mem ((restPolynomial ⟨10,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨10,by norm_num⟩ phaseBox21
  · have hr : residue ⟨10,by norm_num⟩ = (21:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox21_mem
  · exact restBox21_calc
def cBox21 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-26380642397055816535097180326270597663156998636395478033762,-26380642397055816535097180326270597663156998636364942629027⟩,⟨15230870989335429967337177468944677677953239825973862604340,15230870989335429967337177468944677677953239826004339573799⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651670098379681,30461741978670859934674354937889355355906479652282995651015⟩,⟨-113684768751453352939543070528319906038126956577023122919257,-113684768751453352939543070528319906038126956576409678405484⟩⟩,
  ⟨⟨87304126354397536404445890202049308374969957936872404506549,87304126354397536404445890202049308374969957943803418549328⟩,⟨212138666513571275911748963587695134398300673323976180034379,212138666513571275911748963587695134398300673330907843919176⟩⟩,
  ⟨⟨-280130822297018338949280501709181007402567910453984373837594,-280130822297018338949280501709181007402567910398404365830818⟩,⟨-257831279481577565813760495994529167432160392833196534627727,-257831279481577565813760495994529167432160392777616643197488⟩⟩,
  ⟨⟨621185128551378397767909713294140725516948779982022747080166,621185128551378397767909713294140725516948780330659109668665⟩,⟨135984311566894126075063076242971746008534474023176947637487,135984311566894126075063076242971746008534474371810241566312⟩⟩,
  ⟨⟨-795793381260173470576801493698239342266888696944796735028317,-795793381260173470576801493698239342266888695129218463051055⟩,⟨363353849069800831954149217299611558084788386443150825998307,363353849069800831954149217299611558084788388258723384347552⟩⟩,
  ⟨⟨560261644594036677898561003418362014805135816755076733125810,560261644594036677898561003418362014805135824949677540100926⟩,⟨-909478150011626823516344564226559248305015656711039243503645,-909478150011626823516344564226559248305015648516420360133426⟩⟩,
  ⟨⟨75060827609552406205714366367193035296721498300770189953784,75060827609552406205714366367193035296721531486332835559642⟩,⟨1356055025854210148475362497116601357072024500296630778284272,1356055025854210148475362497116601357072024533482157472068222⟩⟩,
  ⟨⟨-1110467045117477712860333524956928462718112629212057074373401,-1110467045117477712860333524956928462718112505049512113454899⟩,⟨-1196677644134750505633807894181447418000037902916017943214385,-1196677644134750505633807894181447418000037778753394234666298⟩⟩,
  ⟨⟨1802631901696793473434380430006643465839033161186825262226003,1802631901696793473434380430006643465839033601143301223879245⟩,⟨288293021460248425748434850932418522788066652479234314199099,288293021460248425748434850932418522788067092435521724437244⟩⟩,
  ⟨⟨-1871717584817365280102883489105659691936346055575725171141848,-1871717584817365280102883489105659691936344549424693227086919⟩,⟨1000863375947639403320367629040227314372734338493802314931264,1000863375947639403320367629040227314372735844645527623712077⟩⟩,
  ⟨⟨879016408032955963581670209288669892949106645291678576191403,879016408032955963581670209288669892949111700631805730554065⟩,⟨-2249208777539376798393398362896685574606044773109867675066683,-2249208777539376798393398362896685574606039717771600203727289⟩⟩,
  ⟨⟨743032096466061837506607133045698146940566300262971447282248,743032096466061837506607133045698146940583097265537570600442⟩,⟨2440141428574632044800598841747259222126971686881038015216650,2440141428574632044800598841747259222126988483886539263138552⟩⟩,
  ⟨⟨-2165985750766594305388529647306255023923849544875266398541216,-2165985750766594305388529647306255023923793992156719108400310⟩,⟨-1688947132945340120494837359478323559800934200945961187154186,-1688947132945340120494837359478323559800878648230729066810312⟩⟩,
  ⟨⟨2903042702743675543357925473083776361664895181102970879358692,2903042702743675543357925473083776361665078566340728256865948⟩,⟨-91692620716126603246,91692620716126668223⟩⟩,
  ⟨⟨-2165985750766594305388529647306255023924124250500843214021059,-2165985750766594305388529647306255023923519286531142293014327⟩,⟨1688947132945340120494837359478323559800603942605389549676469,1688947132945340120494837359478323559801208906571300704194271⟩⟩,
  ⟨⟨743032096466061837506607133045698146939577067479687142180325,743032096466061837506607133045698146941572330048821875846715⟩,⟨-2440141428574632044800598841747259222127977716670086037770084,-2440141428574632044800598841747259222125982454097491240578927⟩⟩,
  ⟨⟨879016408032955963581670209288669892945819040007234115803487,879016408032955963581670209288669892952399305916250190815798⟩,⟨2249208777539376798393398362896685574602752112487813935678036,2249208777539376798393398362896685574609332378393653943217273⟩⟩,
  ⟨⟨-1871717584817365280102883489105659691947195805736941506772471,-1871717584817365280102883489105659691925494799263476891415370⟩,⟨-1000863375947639403320367629040227314383585594807559131435967,-1000863375947639403320367629040227314361884588331770807383881⟩⟩,
  ⟨⟨1802631901696793473434380430006643465803249723615642007754697,1802631901696793473434380430006643465874817038714484478432286⟩,⟨-288293021460248425748434850932418522823850530006255546265665,-288293021460248425748434850932418522752283214908500492182306⟩⟩,
  ⟨⟨-1110467045117477712860333524956928462836122688559123324668875,-1110467045117477712860333524956928462600102445702445863354769⟩,⟨1196677644134750505633807894181447417882027719406195970599688,1196677644134750505633807894181447418118047962263216207162386⟩⟩,
  ⟨⟨75060827609552406205714366367193034907538633910247717466032,75060827609552406205714366367193035685904395876855308301347⟩,⟨-1356055025854210148475362497116601357461207397872640014130987,-1356055025854210148475362497116601356682841635906148236232532⟩⟩,
  ⟨⟨560261644594036677898561003418362013521658522977609678369889,560261644594036677898561003418362016088613118727144594629941⟩,⟨909478150011626823516344564226559247021538354738929443179764,909478150011626823516344564226559249588492950488530160621446⟩⟩,
  ⟨⟨-795793381260173470576801493698239346499639030529713918278368,-795793381260173470576801493698239338034138361544301279687919⟩,⟨-363353849069800831954149217299611562317538721843629310122411,-363353849069800831954149217299611553852038052858244900507325⟩⟩,
  ⟨⟨621185128551378397767909713294140711557858566261271439501020,621185128551378397767909713294140739476038994051410417307773⟩,⟨-135984311566894126075063076242971759967624688092565416369081,-135984311566894126075063076242971732049444260302421772507053⟩⟩,
  ⟨⟨-280130822297018338949280501709181053437931254645179106630229,-280130822297018338949280501709180961367204566207209633278953⟩,⟨257831279481577565813760495994529121396797048586422351018729,257831279481577565813760495994529213467523737024390826540231⟩⟩,
  ⟨⟨87304126354397536404445890202049156556001403701289343920384,87304126354397536404445890202049460193938512179386479505991⟩,⟨-212138666513571275911748963587695286217269227566491238860357,-212138666513571275911748963587694982579332119088392784982519⟩⟩,
  ⟨⟨30461741978670859934674354937888854675613363991869716804655,30461741978670859934674354937889856036199595312083376825565⟩,⟨113684768751453352939543070528319405357833840916609065562616,113684768751453352939543070528320406718420072236823735867133⟩⟩,
  ⟨⟨-26380642397055816535097180326272248845208237661284933745271,-26380642397055816535097180326268946481105759611475486608816⟩,⟨-15230870989335429967337177468946328860004478850893948034922,-15230870989335429967337177468943026495902000801084254458089⟩⟩,
  ⟨⟨-5445395402658874330671108695,5445395402658874330670999096⟩,⟨-5445395402658874330817171884,5445395402658874330817628439⟩⟩]
lemma cBox21_calc (j : Fin 31) : cCoeffBox restBox21 j = cBox21 j := by
  revert j
  decide +kernel
lemma cBox21_mem (j : Fin 31) : (cBox21 j).Mem (cCoefficient ⟨10,by norm_num⟩ j) := by
  rw [← cBox21_calc]
  exact cCoeffBox_mem ⟨10,by norm_num⟩ restBox21 restBox21_mem j
def dBox21 : Fin 31 → CI :=
  ![⟨⟨-59766454282,61485893561⟩,⟨87266462599716478846184538424430635672143594427025497960562,87266462599716478846184538424430635672143594427147002042267⟩⟩,
  ⟨⟨-238416409619234633062357726561276946695815781769353816009653,-238416409619234633062357726561276946695815781766947095224861⟩,⟨-238416409619234633062357726561276946695815781769348502303695,-238416409619234633062357726561276946695815781766941703596748⟩⟩,
  ⟨⟨575790770928143146708997935902992009224082658706306080633642,575790770928143146708997935902992009224082658733567307571768⟩,⟨43633231299858239423092269212215317836071797199905931980442,43633231299858239423092269212215317836071797227165735178653⟩⟩,
  ⟨⟨-715249228857703899187073179683830840087447345414406563501297,-715249228857703899187073179683830840087447345194469129676810⟩,⟨238416409619234633062357726561276946695815781658186309688711,238416409619234633062357726561276946695815781878122251233225⟩⟩,
  ⟨⟨825898669637335181509453606820276436080205940548874392649522,825898669637335181509453606820276436080205941940387900831653⟩,⟨-825898669637335181509453606820276436080205941940402412345543,-825898669637335181509453606820276436080205940548889189998016⟩⟩,
  ⟨⟨-3661288260996330,3661317930385404⟩,⟨1430498457715407798374146359367661680174894686947577405792627,1430498457715407798374146359367661680174894694270190702817772⟩⟩,
  ⟨⟨-901473643147094258617540200888699591592042051631690409369429,-901473643147094258617540200888699591592042018198663748900234⟩,⟨-956798363536909899778730414456922389588421349601761350369224,-956798363536909899778730414456922389588421316168751315637655⟩⟩,
  ⟨⟨1430498457715407798374146359367661680174894622122590108938247,1430498457715407798374146359367661680174894759095176516924212⟩,⟨302299894039036308432346376273692622047344306195796620180014,302299894039036308432346376273692622047344443168429772156317⟩⟩,
  ⟨⟨-1500647392255152208802734025503706561136739954129956463393579,-1500647392255152208802734025503706561136739436166463183885931⟩,⟨1128198563676371489941799983093969058127550056945074769801394,1128198563676371489941799983093969058127550574908468745498298⟩⟩,
  ⟨⟨40500506239886871893792761000400715030912665610050812131877,40500506239886871893792761000400715030914517191648974808234⟩,⟨-1930714255133791867975057701202230533887142181449206798164193,-1930714255133791867975057701202230533887140329867369035317395⟩⟩,
  ⟨⟨1180390559006215763573690688450377253318768218069304311264865,1180390559006215763573690688450377253318774598099064862114710⟩,⟨1608164107974812123595814944428337554324336895261252133143302,1608164107974812123595814944428337554324343275290198274929643⟩⟩,
  ⟨⟨-2454313030732090741052164931748814347920013574795232326020356,-2454313030732090741052164931748814347919992069646381410705601⟩,⟨-517333325478356138018508214122954608422555907512648146207158,-517333325478356138018508214122954608422534402361656776341194⟩⟩,
  ⟨⟨1954097233313706671451253589914245494207720443619317140013093,1954097233313706671451253589914245494207792070723468146801285⟩,⟨-1558265426555011149114123658792493030877987689987018924398753,-1558265426555011149114123658792493030877916062886667488298168⟩⟩,
  ⟨⟨-453449841058554462648519564410538933071135153033089707064645,-453449841058554462648519564410538933070897971013263741473922⟩,⟨1913596727073819799557460828913844779176724074757897824114755,1913596727073819799557460828913844779176961256783161707987198⟩⟩,
  ⟨⟨-831324708607349848188952534752654710630588724423214778697916,-831324708607349848188952534752654710629805336328453470189140⟩,⟨-1863698045654018825075769543278000255730846150975547704346222,-1863698045654018825075769543278000255730062762887723704651118⟩⟩,
  ⟨⟨2175396114872969236096014444187136686191981024472437880972001,2175396114872969236096014444187136686194565873631157920255994⟩,⟨-1292424583077888194849,1292424583077888292726⟩⟩,
  ⟨⟨-831324708607349848188952534752654710634459962789574441976460,-831324708607349848188952534752654710625934097962093807009701⟩,⟨1863698045654018825075769543278000255726191524521639263022248,1863698045654018825075769543278000255734717389341632145812503⟩⟩,
  ⟨⟨-453449841058554462648519564410538933085075809768578308664653,-453449841058554462648519564410538933056957314277775139706288⟩,⟨-1913596727073819799557460828913844779190901913519589308090563,-1913596727073819799557460828913844779162783418021470223920058⟩⟩,
  ⟨⟨1954097233313706671451253589914245494161390069451771881504425,1954097233313706671451253589914245494254122444891013405123054⟩,⟨1558265426555011149114123658792493030831585688720252229126955,1558265426555011149114123658792493030924318064153434183581357⟩⟩,
  ⟨⟨-2454313030732090741052164931748814348072913198265108501052589,-2454313030732090741052164931748814347767092446176505235520772⟩,⟨517333325478356138018508214122954608269634778890619161817070,517333325478356138018508214122954608575455530983685760631972⟩⟩,
  ⟨⟨1180390559006215763573690688450377252814491523242757780719687,1180390559006215763573690688450377253823051292925611392581324⟩,⟨-1608164107974812123595814944428337554828619970115751600025358,-1608164107974812123595814944428337553820060200435698807884878⟩⟩,
  ⟨⟨40500506239886871893792761000400713367860368834929242100754,40500506239886871893792761000400716693966813966770544826717⟩,⟨1930714255133791867975057701202230532224088033091734326085394,1930714255133791867975057701202230535550194478224841507222930⟩⟩,
  ⟨⟨-1500647392255152208802734025503706566621284848061178130654815,-1500647392255152208802734025503706555652194542235241516528743⟩,⟨-1128198563676371489941799983093969063612095468839526963202777,-1128198563676371489941799983093969052643005163014016551952441⟩⟩,
  ⟨⟨1430498457715407798374146359367661662087539024848815588009641,1430498457715407798374146359367661698262250356368951037701431⟩,⟨-302299894039036308432346376273692640134700040442257968285228,-302299894039036308432346376273692603959988708921968424124939⟩⟩,
  ⟨⟨-901473643147094258617540200888699651241917312558934380578712,-901473643147094258617540200888699531942166757271419777523772⟩,⟨956798363536909899778730414456922329938546055241536421357135,956798363536909899778730414456922449238296610528976244643058⟩⟩,
  ⟨⟨-196717955099245915430176123,196717955099245945099425105⟩,⟨-1430498457715407798374146359367661876892849789854830138551116,-1430498457715407798374146359367661483456939591362937969969386⟩⟩,
  ⟨⟨825898669637335181509453606820275787328575242979800167375297,825898669637335181509453606820277084831836639509462126184650⟩,⟨825898669637335181509453606820275787328575242979819370331614,825898669637335181509453606820277084831836639509472231868869⟩⟩,
  ⟨⟨-715249228857703899187073179683832979590565503399579747430081,-715249228857703899187073179683828700584329187209295945745598⟩,⟨-238416409619234633062357726561279086198933939863295654345936,-238416409619234633062357726561274807192697623673012906410297⟩⟩,
  ⟨⟨575790770928143146708997935902984953405837268852526573231673,575790770928143146708997935902999065042328048587346814890806⟩,⟨-43633231299858239423092269212222373654317187080944732301207,-43633231299858239423092269212208262017826407346126934997422⟩⟩,
  ⟨⟨-238416409619234633062357726561300215916921117469708674019543,-238416409619234633062357726561253677474710446066592237073261⟩,⟨238416409619234633062357726561253677474710446066587241783152,238416409619234633062357726561300215916921117469702964200159⟩⟩,
  ⟨⟨-76739030402714413924509991930,76739030402714413926229267919⟩,⟨-87266462599716478846184538424507374702546308841011450021670,-87266462599716478846184538424353896641740880013161049979486⟩⟩]
lemma dBox21_calc (j : Fin 31) : dCoeffBox phaseBox21 restBox21 j = dBox21 j := by
  revert j
  decide +kernel
lemma dBox21_mem (j : Fin 31) : (dBox21 j).Mem (dCoefficient ⟨10,by norm_num⟩ j) := by
  rw [← dBox21_calc]
  apply dCoeffBox_mem ⟨10,by norm_num⟩ phaseBox21 restBox21
  · have hr : residue ⟨10,by norm_num⟩ = (21:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox21_mem
  · exact restBox21_mem
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

def damping (q : Fin 2) : ℝ := if q.val=0 then h else H
lemma b_pos : 0 < b := by unfold b; positivity
lemma b_sq : b^2 = 3/4 := by
  unfold b
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  nlinarith
lemma damping_pos (q : Fin 2) : 0 < damping q := by
  unfold damping h H
  split_ifs <;> norm_num

lemma waveDen_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < waveDen k t := by
  unfold waveDen
  positivity
lemma transformedWave_hasDeriv (k v t : ℝ) (s : ℂ) :
    HasDerivAt (transformedWave k v t) (I*Real.pi*zeta k v t*transformedWave k v t s) s := by
  unfold transformedWave
  have hh := ((hasDerivAt_id s).const_mul (I*(Real.pi:ℂ)*zeta k v t)).cexp.const_mul (lambda k t)
  simpa only [transformedWave,mul_one,one_mul,id_eq,mul_assoc,mul_comm,mul_left_comm] using hh

lemma complex_gaussian_transform (a : ℂ) (ha : 0 < a.re) (w : Plane) :
    𝓕 (fun x : Plane => Complex.exp (-(Real.pi : ℂ) * a * ‖x‖ ^ 2)) w =
      a⁻¹ * Complex.exp (-(Real.pi : ℂ) * ‖w‖ ^ 2 / a) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ha0 : a ≠ 0 := by intro h; subst a; simp at ha
  have hh : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  have hg := fourier_gaussian_innerProductSpace hh w
  have hf : Module.finrank ℝ Plane = 2 := by simp [Plane]
  rw [hf] at hg
  norm_num at hg
  have hfun : (fun x : Plane => Complex.exp (-(Real.pi : ℂ) * a * ‖x‖ ^ 2)) =
      (fun x : Plane => Complex.exp (-((Real.pi : ℂ) * a * ‖x‖ ^ 2))) := by
    funext x
    congr 1
    ring
  rw [hfun, hg]
  have hquot : (Real.pi : ℂ) / ((Real.pi : ℂ) * a) = a⁻¹ := by field_simp
  rw [hquot]
  congr 2
  field_simp

def spectralParameter (k t : ℝ) : ℂ := (b:ℂ)*((k:ℂ)-I*t)
lemma spectralParameter_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < (spectralParameter k t).re := by
  simpa [spectralParameter] using mul_pos b_pos hk
lemma spectralParameter_inv {k : ℝ} (hk : 0 < k) (t : ℝ) :
    (spectralParameter k t)⁻¹ = lambda k t := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  apply inv_eq_of_mul_eq_one_right
  unfold lambda spectralParameter
  push_cast
  field_simp
  simp only [waveDen]
  push_cast
  ring_nf
  simp [I_sq]

lemma spectral_exponent {k : ℝ} (hk : 0 < k) (v t : ℝ) (x : Plane) :
    -(Real.pi:ℂ)*(‖x‖:ℂ)^2/spectralParameter k t =
      -(Real.pi:ℂ)*v*(radial x:ℂ)+I*Real.pi*zeta k v t*(radial x:ℂ) := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  have hbs := congrArg (fun r : ℝ => (r:ℂ)) b_sq
  push_cast at hbs
  rw [div_eq_mul_inv,spectralParameter_inv hk]
  unfold lambda zeta Xwave radial
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  rw [hbs]
  ring

lemma transformed_spectral_wave {k : ℝ} (hk : 0 < k) (v t : ℝ) (w : Plane) :
    𝓕 (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedWave k v t (radial w) := by
  have hfun : (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) =
      (fun x : Plane => exp (-(Real.pi:ℂ)*spectralParameter k t*‖x‖^2)) := by
    funext x
    rw [← exp_add]
    congr 1
    unfold spectralParameter radial
    push_cast
    ring
  rw [hfun,complex_gaussian_transform _ (spectralParameter_pos hk t),
    spectralParameter_inv hk,spectral_exponent hk,exp_add]
  unfold transformedWave
  ring

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

def bBox : RI :=
  ⟨866025403784438646763723170752936183471402626905190314027903,
   866025403784438646763723170752936183471402626905190314027904⟩
lemma bBox_mem : bBox.Mem b := by
  obtain ⟨hl,hu⟩ := Constants.bStar_bracket
  constructor <;> dsimp [RI.Mem, bBox]
  · have hr : (bBox.lo:ℝ)/(scale:ℝ) ≤ Constants.bStar := by norm_num [bBox,scale,Constants.bStar]
    simpa only [b, mul_comm, bBox] using (div_le_iff₀ scale_pos).mp (hr.trans hl.le)
  · have hr : Constants.bStar+Constants.eps ≤ (bBox.hi:ℝ)/(scale:ℝ) := by
      norm_num [bBox,scale,Constants.bStar,Constants.eps]
    simpa only [b,mul_comm,bBox] using (le_div_iff₀ scale_pos).mp (hu.le.trans hr)

def dampingBox (q : Fin 2) : RI := (RI.point (if q.val=0 then 17 else 27)).divNat 50
lemma dampingBox_mem (q : Fin 2) : (dampingBox q).Mem (damping q) := by
  unfold dampingBox damping h H
  split_ifs
  · simpa using RI.mem_divNat (RI.mem_point 17) (by norm_num : 0<(50:ℕ))
  · simpa using RI.mem_divNat (RI.mem_point 27) (by norm_num : 0<(50:ℕ))
def realFrequencyBox (j : Fin 31) : RI := (RI.point ((j.val:ℤ)-15)).divNat 18
lemma realFrequencyBox_mem (j : Fin 31) : (realFrequencyBox j).Mem (frequency j) := by
  have hh := RI.mem_divNat (RI.mem_point ((j.val:ℤ)-15)) (by norm_num : 0<(18:ℕ))
  simpa only [realFrequencyBox, frequency, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_ofNat] using hh

def denBox (q : Fin 2) (j : Fin 31) : RI :=
  ((dampingBox q).pow 2).add ((realFrequencyBox j).pow 2)
lemma denBox_mem (q : Fin 2) (j : Fin 31) :
    (denBox q j).Mem (waveDen (damping q) (frequency j)) := by
  exact RI.mem_add (RI.mem_pow (dampingBox_mem q) 2) (RI.mem_pow (realFrequencyBox_mem j) 2)
lemma denBox_pos (q : Fin 2) (j : Fin 31) : 0 < (denBox q j).lo := by
  revert q j
  decide +kernel
lemma bdenBox_pos (q : Fin 2) (j : Fin 31) : 0 < (bBox.mul (denBox q j)).lo := by
  revert q j
  decide +kernel

def xwaveBox (q : Fin 2) (j : Fin 31) : RI :=
  ((RI.point 4).divNat 3).mul (denBox q j).invPos
lemma xwaveBox_mem (q : Fin 2) (j : Fin 31) :
    (xwaveBox q j).Mem (Xwave (damping q) (frequency j)) := by
  unfold Xwave
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_divNat (RI.mem_point 4) (by norm_num : 0<(3:ℕ)))
    (RI.mem_invPos (denBox_mem q j) (denBox_pos q j))

def lambdaBox (q : Fin 2) (j : Fin 31) : CI :=
  ((CI.ofReal (dampingBox q)).add (CI.imag.mul (CI.ofReal (realFrequencyBox j)))).mul
    (CI.ofReal (bBox.mul (denBox q j)).invPos)
lemma lambdaBox_mem (q : Fin 2) (j : Fin 31) :
    (lambdaBox q j).Mem (lambda (damping q) (frequency j)) := by
  unfold lambda
  rw [div_eq_mul_inv,← Complex.ofReal_inv]
  exact CI.mem_mul (CI.mem_add (CI.mem_ofReal (dampingBox_mem q))
    (CI.mem_mul CI.mem_imag (CI.mem_ofReal (realFrequencyBox_mem j))))
    (CI.mem_ofReal (RI.mem_invPos (RI.mem_mul bBox_mem (denBox_mem q j)) (bdenBox_pos q j)))

def zetaBox (q v : Fin 2) (j : Fin 31) : CI :=
  (CI.ofReal ((realFrequencyBox j).mul (xwaveBox q j)).neg).add
    (CI.imag.mul (CI.ofReal (((dampingBox q).mul (xwaveBox q j)).sub (dampingBox v))))
lemma zetaBox_mem (q v : Fin 2) (j : Fin 31) :
    (zetaBox q v j).Mem (zeta (damping q) (damping v) (frequency j)) := by
  have hh := CI.mem_add (CI.mem_ofReal (RI.mem_neg
    (RI.mem_mul (realFrequencyBox_mem j) (xwaveBox_mem q j))))
    (CI.mem_mul CI.mem_imag (CI.mem_ofReal
      (RI.mem_sub (RI.mem_mul (dampingBox_mem q) (xwaveBox_mem q j)) (dampingBox_mem v))))
  simpa only [zetaBox,zeta,Complex.ofReal_neg,Complex.ofReal_mul,neg_mul] using hh

def wavePhaseBox (q v : Fin 2) (j : Fin 31) : CI :=
  (CI.imag.mul (CI.ofReal piBox)).mul (zetaBox q v j)
lemma wavePhaseBox_mem (q v : Fin 2) (j : Fin 31) :
    (wavePhaseBox q v j).Mem (I*Real.pi*zeta (damping q) (damping v) (frequency j)) :=
  CI.mem_mul (CI.mem_mul CI.mem_imag (CI.mem_ofReal piBox_mem)) (zetaBox_mem q v j)
end AtomicTriangular.FiniteCertificate
end
end
end
end
end
end
end
end
end
end
end

end OAI
