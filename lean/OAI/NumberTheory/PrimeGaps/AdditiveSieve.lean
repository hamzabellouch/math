import OAI.NumberTheory.PrimeGaps.CharacterErrors

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem symmetric_kernel_quadratic_le {ι : Type*} (s : Finset ι) (a : ι→ℝ)
    (w : ι→ι→ℝ) (hw : ∀ i∈s,∀ j∈s,0≤w i j)
    (hs : ∀ i∈s,∀ j∈s,w i j=w j i) :
    (∑ i∈s,∑ j∈s,a i*a j*w i j)≤∑ i∈s,a i^2*(∑ j∈s,w i j) := by
  have hh : (∑ i∈s,∑ j∈s,a i*a j*w i j)≤
      ∑ i∈s,∑ j∈s,(a i^2*w i j+a j^2*w i j)/2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have h := mul_nonneg (sq_nonneg (a i-a j)) (hw i hi j hj)
    nlinarith
  have hswap : (∑ i∈s,∑ j∈s,a j^2*w i j)=(∑ i∈s,∑ j∈s,a i^2*w i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j hj i hi]
  calc
    _ ≤ _ := hh
    _ = _ := by
      simp_rw [←Finset.sum_div,Finset.sum_add_distrib]
      rw [hswap]
      simp only [Finset.mul_sum]
      ring

theorem norm_sum_smul_sq_le_gram {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι→E) (c : ι→ℂ) :
    ‖∑ i∈s,c i • v i‖^2≤∑ i∈s,‖c i‖^2*(∑ j∈s,‖inner ℂ (v i) (v j)‖) := by
  calc
    _ = ∑ i∈s,∑ j∈s,(conj (c i)*(c j*inner ℂ (v i) (v j))).re := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ)]
      simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum,map_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change (c j * (conj (c i) * inner ℂ (v i) (v j))).re = _
      congr 1
      ring
    _ ≤ ∑ i∈s,∑ j∈s,‖c i‖*‖c j‖*‖inner ℂ (v i) (v j)‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_mul,Complex.norm_conj,mul_assoc] using
        Complex.re_le_norm (conj (c i)*(c j*inner ℂ (v i) (v j)))
    _ ≤ _ := symmetric_kernel_quadratic_le s (fun i => ‖c i‖)
      (fun i j => ‖inner ℂ (v i) (v j)‖) (fun _ _ _ _ => norm_nonneg _)
      (fun i _ j _ => by rw [←inner_conj_symm,Complex.norm_conj])

theorem gram_large_sieve {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (v : ι→E) {B : ℝ} (hB : 0≤B)
    (hrows : ∀ i∈s,(∑ j∈s,‖inner ℂ (v i) (v j)‖)≤B) (x : E) :
    (∑ i∈s,‖inner ℂ (v i) x‖^2)≤B*‖x‖^2 := by
  let c : ι→ℂ := fun i => inner ℂ (v i) x
  let y : E := ∑ i∈s,c i • v i
  let A : ℝ := ∑ i∈s,‖c i‖^2
  have hA : 0≤A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy : ‖y‖^2≤B*A := by
    apply (norm_sum_smul_sq_le_gram s v c).trans
    calc
      _ ≤ ∑ i∈s,‖c i‖^2*B := Finset.sum_le_sum
        (fun i hi => mul_le_mul_of_nonneg_left (hrows i hi) (sq_nonneg _))
      _ = B*A := by rw [←Finset.sum_mul,mul_comm]
  have hxy : inner ℂ x y=(A:ℂ) := by
    simp only [y,inner_sum,inner_smul_right,A,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (v i) x * inner ℂ x (v i)=_
    rw [←inner_conj_symm x (v i)]
    simpa only [Complex.normSq_eq_norm_sq,c] using Complex.mul_conj (inner ℂ (v i) x)
  have hn := norm_inner_le_norm (𝕜:=ℂ) x y
  rw [hxy,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA] at hn
  have hn2 : A^2≤‖x‖^2*‖y‖^2 := by
    nlinarith [norm_nonneg x,norm_nonneg y]
  have hprod := mul_le_mul_of_nonneg_left hy (sq_nonneg ‖x‖)
  change A≤B*‖x‖^2
  by_cases hA0 : A=0
  · rw [hA0]
    exact mul_nonneg hB (sq_nonneg _)
  · apply le_of_mul_le_mul_right (a := A) ?_ (lt_of_le_of_ne hA (Ne.symm hA0))
    calc
      A*A = A^2 := by ring
      _ ≤ _ := hn2.trans hprod
      _ = (B*‖x‖^2)*A := by ring

noncomputable def bvExp (x : ℝ) : ℂ := Complex.exp (Complex.I*(2*Real.pi*x:ℝ))

@[simp] theorem bvExp_zero : bvExp 0=1 := by simp [bvExp]

@[simp] theorem norm_bvExp (x : ℝ) : ‖bvExp x‖=1 := by simp [bvExp,Complex.norm_exp]

theorem bvExp_add (x y : ℝ) : bvExp (x+y)=bvExp x*bvExp y := by
  unfold bvExp
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_bvExp (x : ℝ) : conj (bvExp x)=bvExp (-x) := by
  unfold bvExp
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem bvExp_nat_mul (n : ℕ) (x : ℝ) : bvExp ((n:ℝ)*x)=bvExp x^n := by
  unfold bvExp
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem bvExp_sub_one_lower {x : ℝ} (hx : |x|≤1/2) :
    4*|x|≤‖bvExp x-1‖ := by
  rw [bvExp,Complex.norm_exp_I_mul_ofReal_sub_one]
  have hs : |Real.pi*x|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin hs
  rw [abs_mul,abs_of_pos Real.pi_pos] at h
  have hpi : Real.pi≠0 := ne_of_gt Real.pi_pos
  have he : 2/Real.pi*(Real.pi*|x|)=2*|x| := by field_simp
  rw [he] at h
  have hid : 2*Real.pi*x/2=Real.pi*x := by ring
  rw [hid,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

theorem exponential_sum_bound (N : ℕ) {x : ℝ} (hx : |x|≤1/2) (hx0 : x≠0) :
    ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*x)‖≤1/(2*|x|) := by
  have ha : 0 < |x| := abs_pos.mpr hx0
  have hden := bvExp_sub_one_lower hx
  have hn : 0<‖bvExp x-1‖ := lt_of_lt_of_le (by positivity : 0<4*|x|) hden
  have he := geom_sum_mul (bvExp x) N
  have hnorm := congrArg norm he
  rw [norm_mul] at hnorm
  have hu : ‖bvExp x^N-1‖≤2 := by
    calc
      _ ≤ ‖bvExp x^N‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow]; norm_num
  have htimes : ‖∑ n∈Finset.range N,bvExp x^n‖*(4*|x|)≤2 := by
    exact (mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans (hnorm.trans_le hu)
  simp_rw [bvExp_nat_mul]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*|x|)).mpr
  nlinarith

theorem reciprocal_sum_le_harmonic {ι : Type*} (s : Finset ι) (t : ι→ℝ) (D : ℕ)
    (ht : ∀ i∈s,1≤t i ∧ t i≤D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→1≤|t i-t j|) :
    (∑ i∈s,1/t i)≤(harmonic D:ℝ) := by
  classical
  let r : ι→ℕ := fun i => ⌊t i⌋₊
  have hr : ∀ i∈s,r i∈Finset.Icc 1 D := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨Nat.le_floor (by simpa using (ht i hi).1),
      Nat.floor_le_of_le (ht i hi).2⟩
  have hinj : Set.InjOn r s := by
    intro i hi j hj he
    by_contra hij
    have h := hsep i hi j hj hij
    have hil := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht i hi).1)
    have hjl := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht j hj).1)
    have hiu := Nat.lt_floor_add_one (t i)
    have hju := Nat.lt_floor_add_one (t j)
    change ⌊t i⌋₊=⌊t j⌋₊ at he
    rw [he] at hil hiu
    rcases le_abs.mp h with h|h <;> linarith
  calc
    _ ≤ ∑ i∈s,1/(r i:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply one_div_le_one_div_of_le
      · exact_mod_cast (Finset.mem_Icc.mp (hr i hi)).1
      · exact Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤1) (ht i hi).1)
    _ = ∑ k∈s.image r,1/(k:ℝ) := (Finset.sum_image (f := fun k : ℕ => (1:ℝ)/k) hinj).symm
    _ ≤ ∑ k∈Finset.Icc 1 D,1/(k:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hr)
        (fun _ _ _ => by positivity)
    _ = _ := by simp [harmonic_eq_sum_Icc]

theorem reciprocal_sum_le_scaled_harmonic {ι : Type*} (s : Finset ι) (t : ι→ℝ)
    {D : ℕ} (hD : 0<D) (ht : ∀ i∈s,1/(D:ℝ)≤t i ∧ t i≤1)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→1/(D:ℝ)≤|t i-t j|) :
    (∑ i∈s,1/t i)≤(D:ℝ)*(harmonic D:ℝ) := by
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have hh := reciprocal_sum_le_harmonic s (fun i => (D:ℝ)*t i) D
    (fun i hi => ⟨by have h := mul_le_mul_of_nonneg_left (ht i hi).1 hDr.le
                     field_simp at h
                     nlinarith,
      by nlinarith [(ht i hi).2]⟩)
    (fun i hi j hj hij => by
      rw [←mul_sub,abs_mul,abs_of_pos hDr]
      have h := (div_le_iff₀ hDr).mp (hsep i hi j hj hij)
      nlinarith)
  have hm := mul_le_mul_of_nonneg_left hh hDr.le
  rw [Finset.mul_sum] at hm
  calc
    _ = ∑ i∈s,(D:ℝ)*(1/((D:ℝ)*t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ ≤ _ := hm

@[simp] theorem bvExp_int (m : ℤ) : bvExp m=1 := by
  unfold bvExp
  have he : Complex.I * ((2*Real.pi*(m:ℝ):ℝ):ℂ)=(m:ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow]

theorem bvExp_sub_int (x : ℝ) (m : ℤ) : bvExp (x-m)=bvExp x := by
  rw [sub_eq_add_neg,bvExp_add]
  have h : bvExp (-(m:ℝ))=1 := by simpa using bvExp_int (-m)
  rw [h,mul_one]

noncomputable def bvCentered (x : ℝ) : ℝ := x-(⌊x+1/2⌋:ℤ)

theorem abs_bvCentered_le (x : ℝ) : |bvCentered x|≤1/2 := by
  have hl := Int.floor_le (x+1/2)
  have hu := Int.lt_floor_add_one (x+1/2)
  dsimp [bvCentered]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem bvExp_centered (x : ℝ) : bvExp (bvCentered x)=bvExp x := bvExp_sub_int _ _

theorem exponential_sum_centered (N : ℕ) (x : ℝ) :
    (∑ n∈Finset.range N,bvExp ((n:ℝ)*bvCentered x))=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*x) := by
  simp_rw [bvExp_nat_mul,bvExp_centered]

theorem centered_difference_separated {ι : Type*} (s : Finset ι) (θ : ι→ℝ) {D : ℕ}
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (a : ℝ) {i j : ι} (hi : i∈s) (hj : j∈s) (hij : i≠j) :
    1/(D:ℝ)≤|bvCentered (θ i-a)-bvCentered (θ j-a)| := by
  have h := hsep i hi j hj hij (⌊θ i-a+1/2⌋-⌊θ j-a+1/2⌋)
  dsimp [bvCentered]
  convert h using 2
  push_cast
  ring

theorem exponential_kernel_row_bound {ι : Type*} (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) {i : ι} (hi : i∈s) :
    (∑ j∈s,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by
  classical
  let t := s.erase i
  let r := fun j => bvCentered (θ j-θ i)
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have hr : ∀ j∈t,1/(D:ℝ)≤|r j| := by
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hji,hjs⟩
    exact hsep j hjs i hi hji ⌊θ j-θ i+1/2⌋
  have hn : ∀ j∈t,r j≠0 := by
    intro j hj hj0
    have h := hr j hj
    rw [hj0,abs_zero] at h
    exact (not_le_of_gt (one_div_pos.mpr hDr)) h
  have hpair : ∀ j∈t,∀ k∈t,j≠k→1/(D:ℝ)≤|r j-r k| := by
    intro j hj k hk hjk
    exact centered_difference_separated s θ hsep (θ i)
      (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) hjk
  have hhalf : ∀ b:Bool,
      (∑ j∈t.filter (fun j => decide (0≤r j)=b),1/|r j|)≤(D:ℝ)*(harmonic D:ℝ) := by
    intro b
    apply reciprocal_sum_le_scaled_harmonic _ _ hD
    · intro j hj
      exact ⟨hr j ((Finset.mem_filter.mp hj).1),(abs_bvCentered_le _).trans (by norm_num)⟩
    · intro j hj k hk hjk
      have h := hpair j ((Finset.mem_filter.mp hj).1) k ((Finset.mem_filter.mp hk).1) hjk
      have hjb := (Finset.mem_filter.mp hj).2
      have hkb := (Finset.mem_filter.mp hk).2
      cases b <;> simp only [decide_eq_false_iff_not,decide_eq_true_eq,not_le] at hjb hkb
      · simpa only [abs_of_neg hjb,abs_of_neg hkb,neg_sub_neg,abs_sub_comm] using h
      · simpa only [abs_of_nonneg hjb,abs_of_nonneg hkb] using h
  have hrec : (∑ j∈t,1/|r j|)≤2*(D:ℝ)*(harmonic D:ℝ) := by
    have hp := hhalf true
    have hm := hhalf false
    simp only [decide_eq_true_eq,decide_eq_false_iff_not] at hp hm
    have he := Finset.sum_filter_add_sum_filter_not t (fun j => 0≤r j) (fun j => 1/|r j|)
    linarith
  have hoff : (∑ j∈t,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (D:ℝ)*(harmonic D:ℝ) := by
    calc
      _ ≤ ∑ j∈t,1/(2*|r j|) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [←exponential_sum_centered]
        exact exponential_sum_bound N (abs_bvCentered_le _) (hn j hj)
      _ = (∑ j∈t,1/|r j|)/2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := by linarith
  rw [←Finset.sum_erase_add _ _ hi]
  have hd : ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ i-θ i))‖=(N:ℝ) := by simp
  rw [hd]
  linarith

noncomputable def bvExponentialVector (N : ℕ) (θ : ℝ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun n => bvExp (-((n:ℕ):ℝ)*θ))

theorem inner_bvExponentialVector (N : ℕ) (θ η : ℝ) :
    inner ℂ (bvExponentialVector N θ) (bvExponentialVector N η)=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ-η)) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,bvExponentialVector]
  simp_rw [mul_comm (bvExp _)]
  simp_rw [conj_bvExp,←bvExp_add]
  have he : ∀ n:Fin N,-(-((n:ℕ):ℝ)*θ)+(-((n:ℕ):ℝ)*η)=((n:ℕ):ℝ)*(θ-η) := by
    intro n
    ring
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => bvExp ((n:ℝ)*(θ-η))) N

theorem inner_bvExponentialVector_coefficients (N : ℕ) (θ : ℝ) (a : Fin N→ℂ) :
    inner ℂ (bvExponentialVector N θ) (WithLp.toLp 2 a)=
      ∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*θ) := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,bvExponentialVector]
  apply Finset.sum_congr rfl
  intro n _
  rw [conj_bvExp]
  congr 2
  ring

theorem additive_large_sieve {ι : Type*} (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) (a : Fin N→ℂ) :
    (∑ i∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*θ i)‖^2)≤
      ((N:ℝ)+(D:ℝ)*(harmonic D:ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  have hH : 0≤(harmonic D:ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact Finset.sum_nonneg (fun _ _ => by simp only [Rat.cast_inv,Rat.cast_natCast]; positivity)
  have hB : 0≤(N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by positivity
  have hr : ∀ i∈s,(∑ j∈s,‖inner ℂ (bvExponentialVector N (θ i))
      (bvExponentialVector N (θ j))‖)≤(N:ℝ)+(D:ℝ)*(harmonic D:ℝ) := by
    intro i hi
    simp_rw [inner_bvExponentialVector]
    have hh := exponential_kernel_row_bound s (fun i => -θ i) hD
      (fun j hj k hk hjk m => by
        have h := hsep j hj k hk hjk (-m)
        have he : -θ j- -θ k-(m:ℝ)=-(θ j-θ k-(-m:ℤ)) := by
          push_cast
          ring
        rw [he,abs_neg]
        exact h) N hi
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    ring
  have h := gram_large_sieve s (fun i => bvExponentialVector N (θ i)) hB hr (WithLp.toLp 2 a)
  simpa only [inner_bvExponentialVector_coefficients,EuclideanSpace.norm_sq_eq,WithLp.ofLp_toLp] using h

theorem rat_abs_lower (r : ℚ) (hr : r≠0) : 1/(r.den:ℝ)≤|(r:ℝ)| := by
  have hn : r.num≠0 := fun h => hr (Rat.zero_of_num_zero h)
  have ha : (1:ℝ)≤|(r.num:ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  rw [Rat.cast_def,abs_div,abs_of_pos (by exact_mod_cast r.den_pos : (0:ℝ)<r.den)]
  exact div_le_div_of_nonneg_right ha (Nat.cast_nonneg _)

theorem rational_frequency_separation {r t : ℚ} {Q : ℕ}
    (hr : 0≤r ∧ r<1) (ht : 0≤t ∧ t<1) (hrt : r≠t)
    (hrQ : r.den≤Q) (htQ : t.den≤Q) (m : ℤ) :
    1/((Q^2:ℕ):ℝ)≤|(r:ℝ)-(t:ℝ)-m| := by
  have hu0 : r-t-(m:ℚ)≠0 := by
    intro he
    have hm0 : m=0 := by
      have hlo : (-1:ℚ)<(m:ℚ) := by linarith [hr.1,ht.2]
      have hup : (m:ℚ)<1 := by linarith [ht.1,hr.2]
      have h1 : (-1:ℤ) < m := by exact_mod_cast hlo
      have h2 : m<1 := by exact_mod_cast hup
      omega
    simp only [hm0,Int.cast_zero,sub_zero,sub_eq_zero] at he
    exact hrt he
  have hd : (r-t-(m:ℚ)).den≤Q^2 := by
    rw [Rat.sub_intCast_den]
    calc
      _ ≤ r.den*t.den := Nat.le_of_dvd (Nat.mul_pos r.den_pos t.den_pos) (Rat.sub_den_dvd _ _)
      _ ≤ Q*Q := Nat.mul_le_mul hrQ htQ
      _ = _ := by ring
  have hl := rat_abs_lower (r-t-(m:ℚ)) hu0
  push_cast at hl
  exact (one_div_le_one_div_of_le
    (by exact_mod_cast (r-t-(m:ℚ)).den_pos : (0:ℝ)<(r-t-(m:ℚ)).den)
    (by exact_mod_cast hd)).trans hl

theorem rational_additive_large_sieve (s : Finset ℚ) {Q : ℕ} (hQ : 0<Q)
    (hs : ∀ r∈s,0≤r ∧ r<1 ∧ r.den≤Q) (N : ℕ) (a : Fin N→ℂ) :
    (∑ r∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(r:ℝ))‖^2)≤
      ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  have h := additive_large_sieve s (fun r => (r:ℝ)) (pow_pos hQ 2)
    (fun r hr t ht hrt m => rational_frequency_separation
      ⟨(hs r hr).1,(hs r hr).2.1⟩ ⟨(hs t ht).1,(hs t ht).2.1⟩ hrt
      (hs r hr).2.2 (hs t ht).2.2 m) N a
  simpa only [Nat.cast_pow] using h

end LargePrimeGaps

end OAI
