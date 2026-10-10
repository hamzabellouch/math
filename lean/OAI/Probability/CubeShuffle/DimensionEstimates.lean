import Mathlib

namespace OAI

namespace CubeShuffle.DimensionEstimates
open scoped BigOperators

lemma log_factorial_upper_binary (n : ℕ) (hn : 0<n) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n-Real.log 2*((n:ℝ)-1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hb : (2:ℝ) ≤ (1+(n:ℝ)⁻¹)^n := by
      have h := one_add_mul_le_pow (by have := inv_nonneg.mpr hn0.le; linarith : (-2:ℝ)≤(n:ℝ)⁻¹) n
      norm_num [mul_inv_cancel₀ hn0.ne'] at h ⊢
      exact h
    have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) hb
    rw [Real.log_pow] at hl
    have hs : Real.log (1+(n:ℝ)⁻¹)=Real.log ((n:ℝ)+1)-Real.log n := by
      rw [←Real.log_div (by positivity) hn0.ne']
      congr 1
      field_simp
    rw [hs] at hl
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

lemma log_factorial_lower (n : ℕ) (hn : 0<n) :
    (n:ℝ)*Real.log n-n+1 ≤ Real.log (n.factorial:ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hl := Real.log_le_sub_one_of_pos (show 0<((n:ℝ)+1)/n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at hl
    have hh := mul_le_mul_of_nonneg_left hl hn0.le
    have he : (n:ℝ)*(((n:ℝ)+1)/n-1)=1 := by field_simp; ring
    rw [he] at hh
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

lemma log_factorial_upper (n : ℕ) (hn : 0<n) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n-n+Real.log n+1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hl := Real.one_sub_inv_le_log_of_pos (show 0<((n:ℝ)+1)/n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at hl
    have hh := mul_le_mul_of_nonneg_left hl (show 0≤(n:ℝ)+1 by positivity)
    have he : ((n:ℝ)+1)*(1-(((n:ℝ)+1)/n)⁻¹)=1 := by field_simp; ring
    rw [he] at hh
    rw [Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity) (by positivity),Nat.cast_add,Nat.cast_one]
    nlinarith

section Bipartite
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
open scoped Classical

noncomputable def fiberWeight (f : X → I) (i : I) : ℝ := Fintype.card {x // f x=i}

omit [Fintype I] in
lemma fiberWeight_nonneg (f : X → I) (i : I) : 0≤fiberWeight f i := Nat.cast_nonneg _

omit [Fintype I] in
lemma fiberWeight_pos (f : X → I) (x : X) : 0<fiberWeight f (f x) := by
  let : Nonempty {y // f y=f x} := ⟨⟨x,rfl⟩⟩
  exact Nat.cast_pos.mpr Fintype.card_pos

lemma fiber_sum (f : X → I) (u : I → ℝ) :
    ∑ x, u (f x)=∑ i, fiberWeight f i*u i := by
  rw [←Equiv.sum_comp (Equiv.sigmaFiberEquiv f)]
  simp only [Equiv.sigmaFiberEquiv_apply,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ x : {x // f x=i}, u (f x)) = ∑ _x : {x // f x=i}, u i :=
      Finset.sum_congr rfl (fun x _ => congrArg u x.property)
    _ = _ := by simp [fiberWeight]

lemma sum_fiberWeight (f : X → I) : ∑ i, fiberWeight f i=Fintype.card X := by
  have h := fiber_sum f (fun _ => 1)
  simpa using h.symm

/-- Entropy subadditivity for a finite simple bipartite incidence set. -/
theorem incidence_entropy (f : X → I) (g : X → J)
    (hinj : Function.Injective (fun x => (f x,g x))) :
    (∑ i, fiberWeight f i*Real.log (fiberWeight f i))+
      (∑ j, fiberWeight g j*Real.log (fiberWeight g j)) ≤
        (Fintype.card X:ℝ)*Real.log (Fintype.card X) := by
  by_cases hX : Nonempty X
  · let : Nonempty X := hX
    have hN : (0:ℝ)<Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
    have hprod : ∑ x, fiberWeight f (f x)*fiberWeight g (g x) ≤ (Fintype.card X:ℝ)^2 := by
      calc
        _ ≤ ∑ p : I × J, fiberWeight f p.1*fiberWeight g p.2 := by
          calc
            _ = ∑ p ∈ Finset.univ.image (fun x => (f x,g x)), fiberWeight f p.1*fiberWeight g p.2 := by
              rw [Finset.sum_image (fun x _ y _ h => hinj h)]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun p _ _ => mul_nonneg (fiberWeight_nonneg f p.1) (fiberWeight_nonneg g p.2))
        _ = _ := by
          rw [Fintype.sum_prod_type]
          simp_rw [←Finset.mul_sum]
          rw [←Finset.sum_mul,sum_fiberWeight,sum_fiberWeight,pow_two]
    have hdiv : (∑ x, fiberWeight f (f x)*fiberWeight g (g x))/(Fintype.card X:ℝ) ≤ Fintype.card X := by
      apply (div_le_iff₀ hN).mpr
      simpa only [pow_two] using hprod
    have hl (x : X) := Real.log_le_sub_one_of_pos
      (show 0<fiberWeight f (f x)*fiberWeight g (g x)/(Fintype.card X:ℝ) from
        div_pos (mul_pos (fiberWeight_pos f x) (fiberWeight_pos g x)) hN)
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hl x)
    simp_rw [Real.log_div (mul_pos (fiberWeight_pos f _) (fiberWeight_pos g _)).ne' hN.ne',
      Real.log_mul (fiberWeight_pos f _).ne' (fiberWeight_pos g _).ne'] at hs
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,
      fiber_sum f (fun i => Real.log (fiberWeight f i)),
      fiber_sum g (fun j => Real.log (fiberWeight g j)),
      Finset.sum_sub_distrib,←Finset.sum_div] at hs
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hs
    linarith
  · let : IsEmpty X := not_nonempty_iff.mp hX
    have hf (i : I) : fiberWeight f i=0 := by simp [fiberWeight]
    have hg (j : J) : fiberWeight g j=0 := by simp [fiberWeight]
    simp [hf,hg]

end Bipartite
end CubeShuffle.DimensionEstimates

namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical

lemma log_factorial_upper_binary_all (n : ℕ) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n-Real.log 2*((n:ℝ)-1) := by
  by_cases hn : n=0
  · subst n
    simpa using (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  · exact log_factorial_upper_binary n (Nat.pos_of_ne_zero hn)

lemma log_fiber_factorials {X I : Type*} [Fintype X] [Fintype I] (f : X → I) :
    Real.log ((∏ i, (Fintype.card {x // f x=i}).factorial : ℕ):ℝ) ≤
      ∑ i, fiberWeight f i*Real.log (fiberWeight f i) -
        Real.log 2*((Fintype.card X:ℝ)-Fintype.card I) := by
  rw [Nat.cast_prod,Real.log_prod (fun _ _ => by positivity)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    log_factorial_upper_binary_all (Fintype.card {x // f x=i}))
  change ∑ i, Real.log ((Fintype.card {x // f x=i}).factorial:ℝ) ≤
    ∑ i, (fiberWeight f i*Real.log (fiberWeight f i)-Real.log 2*(fiberWeight f i-1)) at h
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_sub_distrib,sum_fiberWeight] at h
  simpa using h

/-- A dimension lower bound using only the actual row and column subgroup
orders, incidence injectivity, and elementary factorial estimates. -/
theorem dimension_log_from_incidence {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    [Nonempty X] (f : X → I) (g : X → J)
    (hinj : Function.Injective (fun x => (f x,g x))) (D : ℕ)
    (hD : (Fintype.card X).factorial ≤ D *
      (∏ i, (Fintype.card {x // f x=i}).factorial) *
      (∏ j, (Fintype.card {x // g x=j}).factorial)) :
    ((2*Real.log 2-1)*(Fintype.card X:ℝ)-
      Real.log 2*((Fintype.card I:ℝ)+Fintype.card J)+1) ≤ Real.log D := by
  have hd : 0<D := by
    by_contra h
    have : D=0 := by omega
    simp [this] at hD
    exact (Nat.factorial_pos _).ne' hD
  have hf := log_fiber_factorials f
  have hg := log_fiber_factorials g
  have hi := incidence_entropy f g hinj
  have hlo := log_factorial_lower (Fintype.card X) Fintype.card_pos
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<(Fintype.card X).factorial)
    (show ((Fintype.card X).factorial:ℝ) ≤ D *
      (∏ i, (Fintype.card {x // f x=i}).factorial) *
      (∏ j, (Fintype.card {x // g x=j}).factorial) by exact_mod_cast hD)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at hlog
  nlinarith

end CubeShuffle.DimensionEstimates

namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical

lemma scaled_binEntropy (N j : ℝ) (hN : 0<N) (hj : 0<j) (hjN : j<N) :
    N*Real.binEntropy (j/N)=N*Real.log N-j*Real.log j-(N-j)*Real.log (N-j) := by
  have hsub : 0<N-j := sub_pos.mpr hjN
  have he : 1-j/N=(N-j)/N := by field_simp
  unfold Real.binEntropy
  rw [he,Real.log_inv,Real.log_inv,Real.log_div hj.ne' hN.ne',
    Real.log_div hsub.ne' hN.ne']
  field_simp
  ring

lemma log_choose_lower_entropy (N j : ℕ) (hj : 0<j) (hjN : j<N) :
    (N:ℝ)*Real.binEntropy ((j:ℝ)/N)-2*Real.log N-1 ≤ Real.log (N.choose j:ℝ) := by
  have hN : 0<N := lt_trans hj hjN
  have ht : 0<N-j := Nat.sub_pos_of_lt hjN
  have hj0 : (0:ℝ)<j := by exact_mod_cast hj
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN
  have hjN0 : (j:ℝ)<N := by exact_mod_cast hjN
  have hchoose : (0:ℝ)<N.choose j := by exact_mod_cast Nat.choose_pos hjN.le
  have hfac := congrArg (fun n : ℕ => Real.log (n:ℝ)) (Nat.choose_mul_factorial_mul_factorial hjN.le)
  simp only [Nat.cast_mul] at hfac
  rw [Real.log_mul (mul_pos hchoose (by positivity)).ne' (by positivity),
    Real.log_mul hchoose.ne' (by positivity)] at hfac
  have hlo := log_factorial_lower N hN
  have hji := log_factorial_upper j hj
  have hti := log_factorial_upper (N-j) ht
  have hjlog := Real.log_le_log hj0 hjN0.le
  have htlog := Real.log_le_log (by exact_mod_cast ht : (0:ℝ)<(N-j:ℕ))
    (by exact_mod_cast Nat.sub_le N j : ((N-j:ℕ):ℝ)≤N)
  rw [Nat.cast_sub hjN.le] at hti htlog
  rw [scaled_binEntropy N j hN0 hj0 hjN0]
  linarith

lemma binEntropy_three_quarters :
    Real.binEntropy (3/4:ℝ)=2*Real.log 2-(3/4:ℝ)*Real.log 3 := by
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  unfold Real.binEntropy
  norm_num only [show (1-(3/4:ℝ))=1/4 by norm_num]
  rw [Real.log_div (by norm_num) (by norm_num),h4]
  ring

noncomputable def entropyGap : ℝ := Real.log (32/27:ℝ)/3

lemma entropyGap_pos : 0<entropyGap := by
  unfold entropyGap
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

lemma entropyGap_eq : entropyGap=(5*Real.log 2-3*Real.log 3)/3 := by
  unfold entropyGap
  rw [Real.log_div (by norm_num) (by norm_num),show (32:ℝ)=2^5 by norm_num,
    show (27:ℝ)=3^3 by norm_num,Real.log_pow,Real.log_pow]
  norm_num

/-- An elementary exponential-dimension constant up to tail fraction 3/4.
It avoids a hook formula or tableau-counting assumption. -/
lemma binEntropy_tail_lower (q : ℝ) (hq : 0≤q) (hq' : q≤3/4) :
    q*Real.log 2+entropyGap*q ≤ Real.binEntropy q := by
  have hc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0:ℝ)∈Set.Icc 0 1 by constructor <;> norm_num)
    (show (3/4:ℝ)∈Set.Icc 0 1 by constructor <;> norm_num)
    (show 0≤1-4*q/3 by linarith) (show 0≤4*q/3 by positivity)
    (show (1-4*q/3)+(4*q/3)=1 by ring)
  simp only [Real.binEntropy_zero,binEntropy_three_quarters,smul_eq_mul,mul_zero,zero_add] at hc
  have he : 4*q/3*(3/4:ℝ)=q := by ring
  rw [he] at hc
  rw [entropyGap_eq]
  linarith

lemma log_dimension_from_binomial (N j D : ℕ) (hj : 0<j) (hjN : j<N)
    (hfrac : (j:ℝ)≤(3/4:ℝ)*N) (hD : N.choose j≤D*2^j) :
    entropyGap*(j:ℝ)-2*Real.log N-1 ≤ Real.log D := by
  have hpos : 0<N.choose j := Nat.choose_pos hjN.le
  have hd : 0<D := by nlinarith [Nat.zero_le (2^j)]
  have hN : (0:ℝ)<N := by exact_mod_cast lt_trans hj hjN
  have hm := Real.log_le_log (by exact_mod_cast hpos : (0:ℝ)<N.choose j)
    (show (N.choose j:ℝ)≤D*2^j by exact_mod_cast hD)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hm
  have he := binEntropy_tail_lower ((j:ℝ)/N) (by positivity)
    ((div_le_iff₀ hN).mpr hfrac)
  have hel := mul_le_mul_of_nonneg_left he hN.le
  have hbin := log_choose_lower_entropy N j hj hjN
  have heq : (N:ℝ)*((j:ℝ)/N*Real.log 2+entropyGap*((j:ℝ)/N))=
      (j:ℝ)*Real.log 2+entropyGap*j := by field_simp
  rw [heq] at hel
  linarith

lemma balanced_dimension_coefficient_pos : 0<(3/2:ℝ)*Real.log 2-1 := by
  linarith [Real.log_two_gt_d9]

end CubeShuffle.DimensionEstimates
namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical

lemma log_choose_upper (N j : ℕ) (hN : 0<N) (hj : j≤N) :
    Real.log (N.choose j:ℝ) ≤ (j:ℝ)*Real.log N-Real.log (j.factorial:ℝ) := by
  have hh := Real.log_le_log (by exact_mod_cast Nat.choose_pos hj : (0:ℝ)<N.choose j)
    (Nat.choose_le_pow_div j N : (N.choose j:ℝ)≤(N:ℝ)^j/(j.factorial:ℝ))
  rw [Real.log_div (by positivity : (N:ℝ)^j≠0) (by positivity : (j.factorial:ℝ)≠0),Real.log_pow] at hh
  exact hh

lemma log_choose_lower (N j : ℕ) (hj : j≤N) :
    (j:ℝ)*Real.log (N+1-j:ℕ)-Real.log (j.factorial:ℝ) ≤ Real.log (N.choose j:ℝ) := by
  have hp : 0<N+1-j := by omega
  have hh := Real.log_le_log (by positivity : (0:ℝ)<((N+1-j:ℕ):ℝ)^j/(j.factorial:ℝ))
    (Nat.pow_le_choose j N : (((N+1-j:ℕ):ℝ)^j)/(j.factorial:ℝ)≤N.choose j)
  rw [Real.log_div (by positivity : (((N+1-j:ℕ):ℝ)^j)≠0) (by positivity : (j.factorial:ℝ)≠0),Real.log_pow] at hh
  exact hh

lemma footprint_log_bound (N k j D m : ℕ) (hN : 0<N) (hk : j≤k) (hj : j≤N)
    (hD : 0<D) (hfoot : D * k.choose j ≤ m * N.choose j) :
    Real.log D-(j:ℝ)*(Real.log N-Real.log (k+1-j:ℕ)) ≤ Real.log m := by
  have hkpos := Nat.choose_pos hk
  have hprod : 0<D*k.choose j := Nat.mul_pos hD hkpos
  have hm : 0 < m := by
    by_contra h
    have he : m=0 := by omega
    simp only [he,zero_mul] at hfoot
    omega
  have hh := Real.log_le_log (by exact_mod_cast hprod : (0:ℝ)<D*k.choose j)
    (show (D:ℝ)*k.choose j≤ m*N.choose j by exact_mod_cast hfoot)
  rw [Real.log_mul (by positivity) (by exact_mod_cast hkpos.ne'),
    Real.log_mul (by positivity) (by exact_mod_cast (Nat.choose_pos hj).ne')] at hh
  have hlo := log_choose_lower k j hk
  have hup := log_choose_upper N j hN hj
  nlinarith

lemma log_factorial_le_mul_log (j : ℕ) (_hj : 0<j) :
    Real.log (j.factorial:ℝ)≤(j:ℝ)*Real.log j := by
  have h := Real.log_le_log (by positivity : (0:ℝ)<j.factorial)
    (show (j.factorial:ℝ)≤(j:ℝ)^j by exact_mod_cast Nat.factorial_le_pow j)
  simpa only [Real.log_pow] using h

lemma near_row_log_dimension (N j D : ℕ) (hj : 0<j) (hsmall : 2*j≤N)
    (hD : N.choose j≤D*2^j) :
    (j:ℝ)*(Real.log ((N:ℝ)/j)-2*Real.log 2) ≤ Real.log D := by
  have hjN : j≤N := by omega
  have hN : 0<N := by omega
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hn : 0<N+1-j := by omega
  have hnreal : (N:ℝ)/2≤(N+1-j:ℕ) := by
    rw [Nat.cast_sub (by omega : j≤N+1),Nat.cast_add,Nat.cast_one]
    have hc : 2*(j:ℝ)≤N := by exact_mod_cast hsmall
    linarith
  have hDpos : 0<D := by
    have hc := Nat.choose_pos hjN
    by_contra h
    have he : D=0 := by omega
    simp only [he,zero_mul] at hD
    omega
  have hm := Real.log_le_log (by exact_mod_cast Nat.choose_pos hjN : (0:ℝ)<N.choose j)
    (show (N.choose j:ℝ)≤D*2^j by exact_mod_cast hD)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hm
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(N:ℝ)/2) hnreal
  rw [Real.log_div hNp.ne' (by norm_num)] at hl
  have hh := log_choose_lower N j hjN
  have hf := log_factorial_le_mul_log j hj
  rw [Real.log_div hNp.ne' hjp.ne']
  nlinarith

end CubeShuffle.DimensionEstimates
namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical
open Filter

noncomputable def nearPower : ℝ := 1/2048
noncomputable def nearFraction : ℝ := 1/4096
noncomputable def tailPower : ℝ := 1535/1048576

noncomputable def chosenTuple (N j : ℕ) : ℕ :=
  ⌈(j:ℝ)*((N:ℝ)/j)^nearPower⌉₊

lemma chosenTuple_bounds (N j : ℕ) (hj : 0<j) (hx : 1≤(N:ℝ)/j)
    (hhalf : ((N:ℝ)/j)^(nearPower-1)≤1/2) :
    j≤chosenTuple N j ∧ chosenTuple N j≤N ∧
      (chosenTuple N j:ℝ)≤2*j*((N:ℝ)/j)^nearPower := by
  let x : ℝ := (N:ℝ)/j
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hj1 : (1:ℝ)≤j := by exact_mod_cast hj
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hpow : 1≤x^nearPower := Real.one_le_rpow hx (by norm_num [nearPower])
  have hceil : (j:ℝ)*x^nearPower≤chosenTuple N j := Nat.le_ceil _
  have hceil' : (chosenTuple N j:ℝ)<(j:ℝ)*x^nearPower+1 := Nat.ceil_lt_add_one (by positivity)
  have he : (j:ℝ)*x=N := by dsimp [x]; field_simp
  have hh : x^nearPower≤x/2 := by
    rw [Real.rpow_sub hxp,Real.rpow_one] at hhalf
    nlinarith [(div_le_iff₀ hxp).mp hhalf]
  constructor
  · exact_mod_cast (le_mul_of_one_le_right hjp.le hpow).trans hceil
  constructor
  · apply Nat.ceil_le.mpr
    change (j:ℝ)*x^nearPower≤N
    nlinarith
  · change (chosenTuple N j:ℝ)≤2*(j:ℝ)*x^nearPower
    nlinarith

lemma chosenTuple_tail_lower (N j : ℕ) (hj : 0<j)
    (hx : 2≤((N:ℝ)/j)^nearPower) :
    (j:ℝ)*((N:ℝ)/j)^nearPower/2 ≤ (chosenTuple N j+1-j:ℕ) := by
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hc : (j:ℝ)*((N:ℝ)/j)^nearPower≤chosenTuple N j := Nat.le_ceil _
  have hjk : j≤chosenTuple N j := by exact_mod_cast (by nlinarith : (j:ℝ)≤chosenTuple N j)
  rw [Nat.cast_sub (by omega : j≤chosenTuple N j+1),Nat.cast_add,Nat.cast_one]
  nlinarith

/-- Quantitative footprint gain at the source's very sparse intermediate tuple size. -/
lemma chosenTuple_log_footprint (N j D m : ℕ) (hj : 0<j)
    (hN : 2*j≤N) (hD : N.choose j≤D*2^j)
    (hx : 2≤((N:ℝ)/j)^nearPower)
    (hlog : 8*Real.log 2/nearPower≤Real.log ((N:ℝ)/j))
    (hfoot : D * (chosenTuple N j).choose j ≤ m * N.choose j) :
    nearFraction*Real.log D≤Real.log m := by
  let x : ℝ := (N:ℝ)/j
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hxp : 0<x := by dsimp [x]; positivity
  have hdpos : 0<D := by
    have hc := Nat.choose_pos (show j≤N by omega)
    by_contra h
    have hz : D=0 := by omega
    simp only [hz,zero_mul] at hD
    omega
  have htail := chosenTuple_tail_lower N j hj hx
  have hjk : j≤chosenTuple N j := by
    have hc : (j:ℝ)*x^nearPower≤chosenTuple N j := Nat.le_ceil _
    exact_mod_cast (by nlinarith : (j:ℝ)≤chosenTuple N j)
  have hh := footprint_log_bound N (chosenTuple N j) j D m (by omega) hjk (by omega) hdpos hfoot
  have htlog := Real.log_le_log (by positivity : (0:ℝ)<(j:ℝ)*x^nearPower/2) htail
  rw [Real.log_div (by positivity) (by norm_num),Real.log_mul hjp.ne' (by positivity),Real.log_rpow hxp] at htlog
  have hxlog : Real.log x=Real.log N-Real.log j := Real.log_div hNp.ne' hjp.ne'
  have hdim := near_row_log_dimension N j D hj hN hD
  change (j:ℝ)*(Real.log x-2*Real.log 2)≤Real.log D at hdim
  have hh' : Real.log D-(j:ℝ)*((1-nearPower)*Real.log x+Real.log 2)≤Real.log m := by
    have hm := mul_le_mul_of_nonneg_left htlog hjp.le
    rw [hxlog] at hm
    nlinarith
  have hlg : (3-nearPower)*Real.log 2≤nearFraction*Real.log x := by
    dsimp [nearPower,nearFraction] at hlog ⊢
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    linarith
  have hlg' := mul_le_mul_of_nonneg_left hlg hjp.le
  dsimp [nearPower,nearFraction] at hh' hlg' ⊢
  nlinarith

lemma near_row_log_uniform (N j D : ℕ) (hj : 0<j) (hN : 2*j≤N)
    (hD : N.choose j≤D*2^j) (hlog : 4*Real.log 2+2≤Real.log ((N:ℝ)/j)) :
    (1/2:ℝ)*Real.log N≤Real.log D ∧ (j:ℝ)≤Real.log D := by
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hj1 : (1:ℝ)≤j := by exact_mod_cast hj
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hd := near_row_log_dimension N j D hj hN hD
  have hjlog := Real.log_le_sub_one_of_pos hjp
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hi : 1≤Real.log ((N:ℝ)/j) := by linarith
  have he : Real.log N=Real.log j+Real.log ((N:ℝ)/j) := by rw [Real.log_div hNp.ne' hjp.ne']; ring
  constructor
  · rw [he]
    nlinarith
  · nlinarith

end CubeShuffle.DimensionEstimates
namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical
open Filter

lemma chosenTuple_density_bound (N j : ℕ) (hj : 0<j) (hx : 1≤(N:ℝ)/j)
    (hhalf : ((N:ℝ)/j)^(nearPower-1)≤1/2) (C : ℝ) (hC : 0≤C) :
    C*(chosenTuple N j:ℝ)*((chosenTuple N j:ℝ)/N)^(1/512:ℝ) ≤
      C*2^(1+(1/512:ℝ))*(j:ℝ)*((N:ℝ)/j)^(-tailPower) := by
  let x : ℝ := (N:ℝ)/j
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hNp : (0:ℝ)<N := by
    have : (0:ℝ)<(N:ℝ)/j := hxp
    exact (div_pos_iff.mp this).resolve_right (by intro h; exact (not_lt_of_ge hjp.le) h.2) |>.1
  have he : (j:ℝ)*x=N := by dsimp [x]; field_simp
  have hk := (chosenTuple_bounds N j hj hx hhalf).2.2
  change (chosenTuple N j:ℝ)≤2*(j:ℝ)*x^nearPower at hk
  have hratio : (chosenTuple N j:ℝ)/N≤2*x^(nearPower-1) := by
    rw [Real.rpow_sub hxp,Real.rpow_one]
    apply (div_le_iff₀ hNp).mpr
    rw [←he]
    have : 2*(x^nearPower/x)*((j:ℝ)*x)=2*(j:ℝ)*x^nearPower := by field_simp
    rw [this]
    exact hk
  have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(chosenTuple N j:ℝ)/N) hratio
    (by norm_num : (0:ℝ)≤1/512)
  have hmain := mul_le_mul hk hpow (by positivity) (by positivity)
  have hrpow : (2*x^(nearPower-1))^(1/512:ℝ)=
      (2:ℝ)^(1/512:ℝ)*x^((nearPower-1)*(1/512)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity),←Real.rpow_mul hxp.le]
  rw [hrpow] at hmain
  have heq : 2*(j:ℝ)*x^nearPower*((2:ℝ)^(1/512:ℝ)*x^((nearPower-1)*(1/512)))=
      (2:ℝ)^(1+(1/512:ℝ))*(j:ℝ)*x^(-tailPower) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
    have hp : nearPower+(nearPower-1)*(1/512) = -tailPower := by norm_num [nearPower,tailPower]
    rw [←hp,Real.rpow_add hxp]
    ring
  rw [heq] at hmain
  have h := mul_le_mul_of_nonneg_left hmain hC
  simpa only [mul_assoc] using h

/-- All cutoffs are absolute. In particular the near-row density cost can be
made smaller than the genuine footprint logarithm, uniformly over that range. -/
lemma near_conditions_eventually (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, 2≤x ∧ 2≤x^nearPower ∧ x^(nearPower-1)≤1/2 ∧
      8*Real.log 2/nearPower≤Real.log x ∧ 4*Real.log 2+2≤Real.log x ∧
      C*2^(1+(1/512:ℝ))*x^(-tailPower) ≤ nearFraction/4000 := by
  have hpow := (tendsto_rpow_atTop (by norm_num [nearPower] : 0<nearPower)).eventually
    (eventually_ge_atTop (2:ℝ))
  have hhalf : ∀ᶠ x : ℝ in atTop, x^(nearPower-1)≤1/2 := by
    have h := (tendsto_rpow_neg_atTop (by norm_num [nearPower] : 0<1-nearPower)).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
    filter_upwards [h] with x hx
    simpa only [neg_sub] using hx.le
  have hdec : Tendsto (fun x : ℝ => C*2^(1+(1/512:ℝ))*x^(-tailPower)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by norm_num [tailPower] : 0<tailPower)))
  have hd := hdec.eventually (gt_mem_nhds (by norm_num [nearFraction] : (0:ℝ)<nearFraction/4000))
  filter_upwards [eventually_ge_atTop (2:ℝ),hpow,hhalf,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (8*Real.log 2/nearPower)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*Real.log 2+2)),hd] with x hx hp hh hl hl' hd
  exact ⟨hx,hp,hh,hl,hl',hd.le⟩

/-- This is the exact simultaneous numerical choice needed by the small-tail
regime of the manuscript: an actual integer k and its density/multiplicity gains. -/
theorem exists_near_cutoff (C : ℝ) (hC : 0≤C) :
    ∃ X : ℝ, 2≤X ∧ ∀ (N j D m : ℕ), 0<j → X≤(N:ℝ)/j →
      N.choose j≤D*2^j →
      D * (chosenTuple N j).choose j ≤ m * N.choose j →
      j≤chosenTuple N j ∧ chosenTuple N j≤N ∧
      nearFraction*Real.log D≤Real.log m ∧
      C*(chosenTuple N j:ℝ)*((chosenTuple N j:ℝ)/N)^(1/512:ℝ)≤Real.log m/4000 ∧
      (1/2:ℝ)*Real.log N≤Real.log D ∧ (j:ℝ)≤Real.log D := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp (near_conditions_eventually C)
  refine ⟨max 2 X,le_max_left _ _,?_⟩
  intro N j D m hj hNx hD hfoot
  have hc := hX ((N:ℝ)/j) ((le_max_right _ _).trans hNx)
  have hjp : (0:ℝ)<j := by exact_mod_cast hj
  have hN : 2*j≤N := by exact_mod_cast (le_div_iff₀ hjp).mp hc.1
  have hk := chosenTuple_bounds N j hj (by linarith [hc.1]) hc.2.2.1
  have hm := chosenTuple_log_footprint N j D m hj hN hD hc.2.1 hc.2.2.2.1 hfoot
  have hd := near_row_log_uniform N j D hj hN hD hc.2.2.2.2.1
  refine ⟨hk.1,hk.2.1,hm,?_,hd⟩
  apply (chosenTuple_density_bound N j hj (by linarith [hc.1]) hc.2.2.1 C hC).trans
  have hh := mul_le_mul_of_nonneg_right hc.2.2.2.2.2 hjp.le
  dsimp [nearFraction] at hm ⊢
  dsimp [nearFraction] at hh
  nlinarith [hd.2]

end CubeShuffle.DimensionEstimates
namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical

lemma amplification_numerical (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ 2*Real.exp (-Real.log m/4000) := by
  have hmp : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hl : 0≤Real.log m := Real.log_nonneg hm
  have he : Real.exp (Real.log m/2)/m=Real.exp (-Real.log m/2) := by
    calc
      _ = Real.exp (Real.log m/2)/Real.exp (Real.log m) := by rw [Real.exp_log hmp]
      _ = _ := by rw [←Real.exp_sub]; congr 1; ring
  have hs : Real.sqrt (Real.exp (-Real.log m/2))=Real.exp (-Real.log m/4) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    ring
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,←Real.exp_add,he,hs]
  have h₁ : u+(Real.log m/2)*(-(1/1000:ℝ))≤ -Real.log m/4000 := by linarith
  have h₂ : -Real.log m/4≤ -Real.log m/4000 := by linarith
  linarith [Real.exp_le_exp.mpr h₁,Real.exp_le_exp.mpr h₂]

lemma amplification_absorb (x : ℝ) (hx : 8000*Real.log 2≤x) :
    2*Real.exp (-x/4000)≤Real.exp (-x/8000) := by
  rw [show (2:ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

lemma amplification_decay (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000)
    (hl : 8000*Real.log 2≤Real.log m) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ Real.exp (-Real.log m/8000) :=
  (amplification_numerical m u hm hu).trans (amplification_absorb _ hl)

end CubeShuffle.DimensionEstimates

namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical
open Filter

lemma finset_power_sum {ι : Type*} [Fintype ι] (x : ℝ) :
    ∑ E : Finset ι, x^E.card=(1+x)^Fintype.card ι := by
  have h := Finset.prod_one_add (f := fun _ : ι => x) Finset.univ
  simpa only [Finset.prod_const,Finset.card_univ,Finset.powerset_univ] using h.symm

lemma small_sets_count {ι : Type*} [Fintype ι] (ε t : ℝ) (ht : 0≤t) :
    (∑ E : Finset ι, if (E.card:ℝ)<ε*Fintype.card ι then (1:ℝ) else 0) ≤
      Real.exp ((t*ε+Real.log (1+Real.exp (-t)))*Fintype.card ι) := by
  have hpow (E : Finset ι) : (Real.exp (-t))^E.card=Real.exp (-t*(E.card:ℝ)) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ ∑ E : Finset ι, Real.exp (t*ε*Fintype.card ι)*(Real.exp (-t))^E.card := by
      apply Finset.sum_le_sum
      intro E _
      split_ifs with hE
      · rw [hpow,←Real.exp_add,←Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hE.le ht]
      · positivity
    _ = Real.exp (t*ε*Fintype.card ι)*(1+Real.exp (-t))^Fintype.card ι := by
      rw [←Finset.mul_sum,finset_power_sum]
    _ = _ := by
      have he : (1+Real.exp (-t))^Fintype.card ι=
          Real.exp (Real.log (1+Real.exp (-t))*(Fintype.card ι:ℝ)) := by
        rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by positivity)]
      rw [he,←Real.exp_add]
      congr 1
      ring

lemma small_sets_ceil_bound {ι : Type*} [Fintype ι] (ε t : ℝ) (ht : 0≤t) :
    (∑ E : Finset ι, if E.card<⌈ε*Fintype.card ι⌉₊ then (1:ℝ) else 0) ≤
      Real.exp ((t*ε+Real.log (1+Real.exp (-t)))*Fintype.card ι) := by
  have he (E : Finset ι) : E.card<⌈ε*Fintype.card ι⌉₊ ↔ (E.card:ℝ)<ε*Fintype.card ι := Nat.lt_ceil
  simp only [he]
  exact small_sets_count ε t ht

/-- The exceptional-subset entropy rate can be made arbitrarily small by
shrinking its positive fraction, after every other absolute parameter is fixed. -/
lemma exists_small_set_rate (κ ε₀ : ℝ) (hκ : 0<κ) (hε₀ : 0<ε₀) :
    ∃ ε : ℝ, 0<ε ∧ ε≤ε₀ ∧ ε<1/2 ∧ ∃ t : ℝ, 0≤t ∧
      t*ε+Real.log (1+Real.exp (-t))≤κ := by
  have ht : Tendsto (fun t : ℝ => Real.log (1+Real.exp (-t))) atTop (nhds 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have hl := (tendsto_const_nhds.add he).log (by norm_num : (1:ℝ)+0≠0)
    simpa only [add_zero,Real.log_one] using hl
  obtain ⟨t,ht,hlog⟩ := ((eventually_ge_atTop (1:ℝ)).and
    (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ)<κ/2)))).exists
  let ε := min ε₀ (min (1/4) (κ/(2*t)))
  have htp : 0<t := by linarith
  have hε : 0<ε := lt_min hε₀ (lt_min (by norm_num) (by positivity))
  refine ⟨ε,hε,min_le_left _ _,(min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by norm_num)),t,htp.le,?_⟩
  have hsmall : ε≤κ/(2*t) := (min_le_right _ _).trans (min_le_right _ _)
  have hm := (le_div_iff₀ (by positivity : (0:ℝ)<2*t)).mp hsmall
  linarith

end CubeShuffle.DimensionEstimates


namespace CubeShuffle.DimensionEstimates
open Filter

lemma log_error_eventually (a : ℝ) (ha : 0<a) :
    ∀ᶠ N : ℕ in atTop, 2*Real.log N+1≤(a/2)*(N:ℝ) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Real.isLittleO_log_id_atTop.bound (by linarith : 0<a/8))
  have hg := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (4/a))
  filter_upwards [h,hg,eventually_ge_atTop 1] with N h hg hN
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hn),id_eq,abs_of_nonneg (by positivity : (0:ℝ)≤N)] at h
  have hh : 4≤(N:ℝ)*a := (div_le_iff₀ ha).mp hg
  linarith

end CubeShuffle.DimensionEstimates

namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical
open Filter

lemma geometric_ceil_bound (θ ε : ℝ) (hθ : 0<θ) (hθ1 : θ<1) (M : ℕ) :
    θ^⌈ε*M⌉₊≤Real.exp (Real.log θ*ε*M) := by
  conv_lhs => rw [←Real.exp_log hθ,←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hg := mul_le_mul_of_nonpos_left (Nat.le_ceil (ε*M)) (Real.log_nonpos hθ.le hθ1.le)
  nlinarith

end CubeShuffle.DimensionEstimates

namespace CubeShuffle.DimensionEstimates
open Filter

lemma twopow_tendsto : Tendsto (fun d : ℕ => (2:ℝ)^d) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

lemma twopow_nat_tendsto : Tendsto (fun d : ℕ => (2:ℕ)^d) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

lemma twopow_mul_eventually (c : ℝ) (hc : 0<c) (B : ℝ) :
    ∀ᶠ d : ℕ in atTop, B≤c*(2:ℝ)^d := by
  filter_upwards [twopow_tendsto.eventually (eventually_ge_atTop (B/c))] with d hd
  exact (div_le_iff₀ hc).mp hd |>.trans_eq (mul_comm _ _)

lemma exp_two_absorb (β n : ℝ) (hx : Real.log 2≤β*n/2) :
    Real.exp (-β*n)+Real.exp (-β*n)≤Real.exp (-β*n/2) := by
  calc
    _ = Real.exp (Real.log 2-β*n) := by rw [Real.exp_sub,Real.exp_log (by norm_num)]; rw [neg_mul,Real.exp_neg]; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end CubeShuffle.DimensionEstimates

end OAI
