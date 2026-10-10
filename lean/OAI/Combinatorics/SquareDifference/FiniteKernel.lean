import OAI.Combinatorics.SquareDifference.RationalApproximation

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

noncomputable def finiteSquareKernel {K : Type*} [Fintype K]
    (ε : K → ℂ) (v : K → ℕ → ℂ) (M N : ℕ) (α : ℝ) : ℂ :=
  ∑k, ε k*∑m∈range M, squareWeight N α m*v k (m+1)

noncomputable def finiteRationalCoefficient {K : Type*} [Fintype K]
    (ε : K → ℂ) (v : K → ℕ → ℂ) (t : K → ℕ) (b : ℚ) : ℂ :=
  ∑k, ε k*periodicMean (fun m => v k (m+1)*expPhase ((b : ℝ)*(m+1)^2)) (b.den*t k)

lemma finite_square_kernel_major {K : Type*} [Fintype K]
    (ε : K → ℂ) (v : K → ℕ → ℂ) (t : K → ℕ)
    (ht : ∀k, 0<t k) (hv : ∀k, Function.Periodic (v k) (t k))
    (B : K → ℝ) (hB : ∀k, 0≤B k) (hb : ∀k m, ‖v k m‖≤B k)
    (b : ℚ) (α : ℝ) (T : ℕ) (R : ℝ) (hq : (b.den : ℝ)≤R)
    (ha : |α-(b : ℝ)|≤1/(((T : ℝ)+1)*b.den))
    (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) :
    ‖finiteSquareKernel ε v M N α-finiteRationalCoefficient ε v t b*normalizedLinearSum N (α-b)‖≤
      (∑k, ‖ε k‖*(2*(t k : ℝ)+1)*B k)*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N := by
  unfold finiteSquareKernel finiteRationalCoefficient
  rw [sum_mul, ←sum_sub_distrib]
  calc
    _ ≤ ∑k, ‖ε k‖*((2*(t k : ℝ)+1)*B k*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro k _
      rw [mul_assoc,←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left
        (rational_kernel_major_uniform (v k) (t k) (ht k) (hv k) (B k) (hB k) (hb k)
          b α T R hq ha M N hM hlo hhi) (norm_nonneg _)
    _ = _ := by simp_rw [mul_div_assoc,←mul_assoc]; rw [←sum_mul,←sum_mul]

lemma finite_kernel_uniform {K I J : Type*} [Fintype K] [Fintype I] [Fintype J]
    (ε : K → ℂ) (v : K → ℕ → ℂ) (t : K → ℕ)
    (ht : ∀k, 0<t k) (hv : ∀k, Function.Periodic (v k) (t k))
    (B : K → ℝ) (hB : ∀k, 0≤B k) (hb : ∀k m, ‖v k m‖≤B k)
    (c : I → ℚ) (z : I → ℂ) (L T : ℕ) (R E : ℝ)
    (hT : 0<T) (hL : 2*L≤T+1) (hc : ∀i, (c i).den≤L)
    (hR : 8≤R) (hRL : (L : ℝ)≤R) (hE : 0≤E)
    (hcoef : ∀b : ℚ, (b.den : ℝ)≤R →
      ‖finiteRationalCoefficient ε v t b-modelCenterCoefficient c z b‖≤E)
    (w : J → ℂ) (θ : J → ℝ)
    (hfourier : ∀m, (∑k, ε k*v k m)=∑j, w j*expPhase (θ j*m))
    (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) (α : ℝ) :
    ‖finiteSquareKernel ε v M N α-∑i, z i*normalizedLinearSum N (α-c i)‖≤
      E+(∑k, ‖ε k‖*(2*(t k : ℝ)+1)*B k)*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N+
      (∑j, ‖w j‖)*(4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T))+
      (∑i, ‖z i‖)*((T : ℝ)*L/N) := by
  obtain ⟨b,hbT,ha,haRat⟩ := dirichlet_fraction α T hT
  have hmodel := rational_model_approximation c z N α b T L hc hL ha
  have hsmall : 0≤(∑k, ‖ε k‖*(2*(t k : ℝ)+1)*B k)*(4*R+8*Real.pi*N/((T : ℝ)+1))*M/N := by
    have : 0≤R := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg (sum_nonneg (fun k _ =>
      mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity)) (hB k))) (by positivity)) (by positivity)) (by positivity)
  have hlarge : 0≤(∑j, ‖w j‖)*(4*(M : ℝ)/N)*Real.sqrt
        (5*M+32*(M : ℝ)^2/R+(64*M+8*T)*(1+Real.log T)) := by positivity
  have hmodel' : ‖(∑i, z i*normalizedLinearSum N (α-c i))-
      modelCenterCoefficient c z b*normalizedLinearSum N (α-b)‖≤
        (∑i, ‖z i‖)*((T : ℝ)*L/N) := by
    apply hmodel.trans
    gcongr
  by_cases hbr : (b.den : ℝ)≤R
  · have hactual := finite_square_kernel_major ε v t ht hv B hB hb b α T R hbr ha M N hM hlo hhi
    have he : ‖finiteRationalCoefficient ε v t b*normalizedLinearSum N (α-b)-
        modelCenterCoefficient c z b*normalizedLinearSum N (α-b)‖≤E := by
      rw [←sub_mul,norm_mul]
      exact (mul_le_mul (hcoef b hbr) (normalizedLinearSum_norm N (α-b))
        (norm_nonneg _) hE).trans_eq (mul_one E)
    have hh := norm_sub_le_norm_sub_add_norm_sub (finiteSquareKernel ε v M N α)
      (finiteRationalCoefficient ε v t b*normalizedLinearSum N (α-b))
      (modelCenterCoefficient c z b*normalizedLinearSum N (α-b))
    have hh' := norm_sub_le_norm_sub_add_norm_sub (finiteSquareKernel ε v M N α)
      (modelCenterCoefficient c z b*normalizedLinearSum N (α-b))
      (∑i, z i*normalizedLinearSum N (α-c i))
    rw [norm_sub_rev (modelCenterCoefficient c z b*normalizedLinearSum N (α-b))] at hh'
    linarith
  · have hbL : L<b.den := by exact_mod_cast (lt_of_le_of_lt hRL (lt_of_not_ge hbr))
    rw [modelCenterCoefficient_zero c z b L hc hbL,zero_mul,sub_zero] at hmodel'
    have hb8 : 8≤b.den := by exact_mod_cast (hR.trans (le_of_not_ge hbr))
    have ha' : |α-(b : ℝ)|≤1/(b.den : ℝ)^2 := by
      simpa only [Rat.cast_def] using haRat
    have hact := quadratic_fourier_weight_uniform w θ α b T R (by linarith) hb8
      (le_of_not_ge hbr) hbT ha' M N
    have heq : finiteSquareKernel ε v M N α=
        ∑m∈range M, squareWeight N α m*∑j, w j*expPhase (θ j*(m+1)) := by
      unfold finiteSquareKernel
      simp_rw [Finset.mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      rw [←mul_sum,show (m : ℝ)+1=((m+1 : ℕ) : ℝ) by simp,←hfourier,mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    rw [←heq] at hact
    have hh := norm_sub_le_norm_sub_add_norm_sub (finiteSquareKernel ε v M N α)
      (0 : ℂ) (∑i, z i*normalizedLinearSum N (α-c i))
    simp only [sub_zero,zero_sub,norm_neg] at hh
    linarith

noncomputable def boundedRationals (L : ℕ) : Finset ℚ :=
  ((univ : Finset (Fin L × Fin L)).image
    (fun v => ((v.1.val : ℚ)/(v.2.val+1)))).filter (fun b => 0≤b ∧ b<1 ∧ b.den≤L)

lemma mem_boundedRationals (L : ℕ) (b : ℚ) :
    b∈boundedRationals L ↔ 0≤b ∧ b<1 ∧ b.den≤L := by
  classical
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · rintro ⟨hb0,hb1,hden⟩
    apply mem_filter.mpr
    refine ⟨?_,hb0,hb1,hden⟩
    have hnum0 : 0≤b.num := Rat.num_nonneg.mpr hb0
    have hnum1 : b.num<(b.den : ℤ) := by
      have hd : (0 : ℚ)<b.den := Nat.cast_pos.mpr b.pos
      have h := (div_lt_one hd).mp ((Rat.num_div_den b).trans_lt hb1)
      exact_mod_cast h
    have hn : b.num.toNat<L := by omega
    have hd : b.den-1<L := by have := b.pos; omega
    apply mem_image.mpr
    refine ⟨(⟨b.num.toNat,hn⟩,⟨b.den-1,hd⟩),mem_univ _,?_⟩
    dsimp only
    rw [show ((b.den-1 : ℕ) : ℚ)+1=(b.den : ℚ) by
      rw [Nat.cast_sub (by have := b.pos; omega : 1≤b.den),Nat.cast_one]; ring]
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hnum0,Rat.num_div_den]

lemma boundedRationals_card (L : ℕ) : (boundedRationals L).card≤L^2 := by
  exact (card_filter_le _ _).trans ((card_image_le).trans_eq (by simp [sq]))

lemma boundedRationals_fract {L : ℕ} (b : ℚ) (hb : b.den≤L) :
    Int.fract b∈boundedRationals L := by
  rw [mem_boundedRationals]
  exact ⟨Int.fract_nonneg b,Int.fract_lt_one b,by simpa only [Rat.den_intFract] using hb⟩

lemma boundedRationals_equiv_int {L : ℕ} (b c : ℚ) (hc : c∈boundedRationals L) :
    (∃k : ℤ, b-c=(k:ℚ)) ↔ Int.fract b=c := by
  rw [← Int.fract_eq_fract]
  rw [(Int.fract_eq_self).mpr ⟨(mem_boundedRationals L c |>.mp hc).1,
    (mem_boundedRationals L c |>.mp hc).2.1⟩]

attribute [local instance] Classical.propDecidable

lemma boundedRationals_sum_mod_int (L : ℕ) (f : ℚ → ℂ) (b : ℚ) :
    (∑c∈boundedRationals L, if ∃k : ℤ, b-c=(k:ℚ) then f c else 0)=
      if b.den≤L then f (Int.fract b) else 0 := by
  classical
  have he : (∑c∈boundedRationals L, if ∃k : ℤ, b-c=(k:ℚ) then f c else 0)=
      ∑c∈boundedRationals L, if Int.fract b=c then f c else 0 := by
    apply sum_congr rfl
    intro c hc
    rw [boundedRationals_equiv_int b c hc]
    split_ifs <;> rfl
  rw [he]
  by_cases hb : b.den≤L
  · rw [ite_eq_left hb,sum_eq_single (Int.fract b)]
    · simp
    · intro c _ hc; rw [ite_eq_right (Ne.symm hc)]
    · exact fun h => False.elim (h (boundedRationals_fract b hb))
  · rw [ite_eq_right hb]
    apply sum_eq_zero
    intro c hc
    rw [ite_eq_right]
    rintro rfl
    exact hb (by simpa only [Rat.den_intFract] using (mem_boundedRationals L (Int.fract b)).mp hc |>.2.2)

section ActualKernelCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))

lemma actualCompleteQuadratic_periodic (b : ℚ) (t : ℕ)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    Function.Periodic (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  apply Function.Periodic.mul
  · intro n
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      actualCompleteWeight_periodic p R c t hpt (n+1)
  · exact expPhase_rat_square_periodic b t hbt

noncomputable def completeRationalCoefficient (b : ℚ) : ℂ :=
  periodicMean (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2))
    (b.den*∏i,p i)

lemma completeRationalCoefficient_eq (b : ℚ) (t : ℕ) (ht : 0<t)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    completeRationalCoefficient p R c b =
      periodicMean (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  apply periodicMean_independent
  · exact (mul_pos b.pos (prod_pos (fun i _ => (Fact.out : (p i).Prime).pos))).ne'
  · exact ht.ne'
  · exact actualCompleteQuadratic_periodic p R c b _
      (fun i => dvd_mul_of_dvd_right (dvd_prod_of_mem p (mem_univ i)) _) (dvd_mul_right _ _)
  · exact actualCompleteQuadratic_periodic p R c b t hpt hbt

noncomputable def kernelModelCoefficient (H : ℝ) (b : ℚ) : ℂ :=
  if ((∏i∈primaryActive p b.den\R,p i : ℕ):ℝ)≤H then completeRationalCoefficient p R c b else 0

lemma primaryModelCoefficient_eq_kernelModel (hinj : Function.Injective p) (b : ℚ)
    (hb : b.den∣∏i,primaryModulus b.den (p i)) (H : ℝ) (htwo : ∀i,p i=2 → i∈R) :
    primaryModelCoefficient p hinj b hb R c H=kernelModelCoefficient p R c H b := by
  rw [primaryModelCoefficient_complete p R c hinj b hb H htwo]
  unfold kernelModelCoefficient
  rw [completeRationalCoefficient_eq p R c b (∏i,primaryModulus b.den (p i))
    (prod_pos (fun i _ => primaryModulus_pos (Fact.out : (p i).Prime)))
    (fun i => (prime_dvd_primaryModulus b.den (p i)).trans
      (dvd_prod_of_mem (fun i => primaryModulus b.den (p i)) (mem_univ i))) hb]

lemma expPhase_rat_add_int_square (b : ℚ) (k : ℤ) (n : ℕ) :
    expPhase (((b+k : ℚ):ℝ)*(n:ℝ)^2)=expPhase ((b:ℝ)*(n:ℝ)^2) := by
  rw [show (((b+k : ℚ):ℝ)*(n:ℝ)^2)=(b:ℝ)*(n:ℝ)^2+((k*(n:ℤ)^2:ℤ):ℝ) by push_cast; ring]
  rw [expPhase_add,expPhase_int,mul_one]

lemma completeRationalCoefficient_add_int (b : ℚ) (k : ℤ) :
    completeRationalCoefficient p R c (b+k)=completeRationalCoefficient p R c b := by
  unfold completeRationalCoefficient
  rw [Rat.add_intCast_den]
  congr 1
  funext n
  have h := expPhase_rat_add_int_square b k (n+1)
  simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun z => actualCompleteWeight p R c (n+1)*z) h

lemma kernelModelCoefficient_add_int (H : ℝ) (b : ℚ) (k : ℤ) :
    kernelModelCoefficient p R c H (b+k)=kernelModelCoefficient p R c H b := by
  simp only [kernelModelCoefficient,Rat.add_intCast_den,completeRationalCoefficient_add_int]

lemma kernelModelCoefficient_fract (H : ℝ) (b : ℚ) :
    kernelModelCoefficient p R c H (Int.fract b)=kernelModelCoefficient p R c H b := by
  have h := kernelModelCoefficient_add_int p R c H (Int.fract b) (Int.floor b)
  rw [Int.fract_add_floor] at h
  exact h.symm

lemma kernelModelCoefficient_norm (hinj : Function.Injective p) (b : ℚ)
    (hb : b.den∣∏i,primaryModulus b.den (p i)) (H : ℝ) (htwo : ∀i,p i=2 → i∈R) :
    ‖kernelModelCoefficient p R c H b‖≤1 := by
  rw [← primaryModelCoefficient_eq_kernelModel p R c hinj b hb H htwo]
  exact primaryModelCoefficient_norm p hinj b hb R c H

lemma kernelModelCoefficient_zero_of_denominator (hinj : Function.Injective p) (b : ℚ)
    (hb : b.den∣∏i,primaryModulus b.den (p i)) (H : ℝ) (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    (hden : rootSquareModulus p R*H<(b.den:ℝ)) :
    kernelModelCoefficient p R c H b=0 := by
  rw [← primaryModelCoefficient_eq_kernelModel p R c hinj b hb H htwo]
  exact primaryModelCoefficient_zero_of_denominator p hinj b hb R c H htwo hc hden

lemma bounded_kernel_model_center (hinj : Function.Injective p) (L : ℕ) (H : ℝ)
    (hL : rootSquareModulus p R*H≤(L:ℝ)) (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    (b : ℚ) (hb : b.den∣∏i,primaryModulus b.den (p i)) :
    modelCenterCoefficient (fun z : boundedRationals L => z.val)
      (fun z => kernelModelCoefficient p R c H z.val) b = kernelModelCoefficient p R c H b := by
  classical
  unfold modelCenterCoefficient
  change (∑ z : boundedRationals L, (fun x : ℚ => if ∃k : ℤ, b-x=(k:ℚ) then kernelModelCoefficient p R c H x else 0) z.val) = _
  rw [Finset.sum_coe_sort (boundedRationals L) (fun x : ℚ => if ∃k : ℤ, b-x=(k:ℚ) then kernelModelCoefficient p R c H x else 0), boundedRationals_sum_mod_int]
  by_cases hden : b.den≤L
  · rw [ite_eq_left hden,kernelModelCoefficient_fract]
  · rw [ite_eq_right hden]
    symm
    apply kernelModelCoefficient_zero_of_denominator p R c hinj b hb H htwo hc
    exact hL.trans_lt (by exact_mod_cast (lt_of_not_ge hden))

end ActualKernelCoefficient

lemma stdAddChar_eq_expPhase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a=expPhase ((a.val : ℝ)/p) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring

section ActualKernelTerms

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))

noncomputable def boundedSieveSets (H : ℝ) : Finset (Finset I) :=
  (univ : Finset I).powerset.filter (fun T => ((∏i∈T,p i : ℕ):ℝ)≤H)

noncomputable def sieveTermSign (T : Finset I) : ℂ := (-1)^T.card

noncomputable def sieveTermWeight (T : Finset I) (n : ℕ) : ℂ :=
  actualRootWeight p R c n*actualSieveWeight p R T n

noncomputable def sieveTermPeriod (T : Finset I) : ℕ := (∏i∈R,p i)*(∏i∈T,p i)

omit [Fintype I] [DecidableEq I] in
lemma sieveTermPeriod_pos (T : Finset I) : 0<sieveTermPeriod p R T :=
  mul_pos (prod_pos (fun i _ => (Fact.out : (p i).Prime).pos))
    (prod_pos (fun i _ => (Fact.out : (p i).Prime).pos))

omit [Fintype I] in
lemma sieveTermWeight_periodic (T : Finset I) :
    Function.Periodic (sieveTermWeight p R c T) (sieveTermPeriod p R T) :=
  actualTermWeight_periodic p R c T

omit [Fintype I] in
lemma sieveTermWeight_norm (T : Finset I) (n : ℕ) :
    ‖sieveTermWeight p R c T n‖≤(∏i∈R,p i : ℕ) := by
  rw [sieveTermWeight,norm_mul]
  exact (mul_le_mul (actualRootWeight_norm p R c n) (actualSieveWeight_norm p R T n)
    (norm_nonneg _) (Nat.cast_nonneg _)).trans_eq (mul_one _)

omit [Fintype I] [DecidableEq I] in
lemma sieveTermSign_norm (T : Finset I) : ‖sieveTermSign T‖=1 := by
  simp only [sieveTermSign,norm_pow,norm_neg,norm_one,one_pow]

lemma actualDivisorWeight_eq_terms (H : ℝ) (n : ℕ) :
    actualDivisorWeight p R c H n=
      ∑T : boundedSieveSets p H, sieveTermSign T.val*sieveTermWeight p R c T.val n := by
  change _ = ∑ T : boundedSieveSets p H, (fun S : Finset I => sieveTermSign S*sieveTermWeight p R c S n) T.val
  rw [Finset.sum_coe_sort (boundedSieveSets p H) (fun S : Finset I => sieveTermSign S*sieveTermWeight p R c S n)]
  unfold boundedSieveSets sieveTermSign sieveTermWeight actualDivisorWeight
  rw [sum_filter,mul_sum]
  apply sum_congr rfl
  intro T _
  split_ifs <;> ring

omit [Fintype I] in
lemma sieveTermQuadratic_periodic (T : Finset I) (b : ℚ) (t : ℕ)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    Function.Periodic (fun n => sieveTermWeight p R c T (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  have hw : Function.Periodic (sieveTermWeight p R c T) t :=
    (actualRootWeight_periodic p R c t (fun i _ => hpt i)).mul
      (actualSieveWeight_periodic p R T t (fun i _ => hpt i))
  apply Function.Periodic.mul
  · intro n
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hw (n+1)
  · exact expPhase_rat_square_periodic b t hbt

omit [Fintype I] in
lemma sieveTermCoefficient_eq (T : Finset I) (b : ℚ) (t : ℕ) (ht : 0<t)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    periodicMean (fun n => sieveTermWeight p R c T (n+1)*expPhase ((b:ℝ)*(n+1)^2))
        (b.den*sieveTermPeriod p R T)=
      periodicMean (fun n => sieveTermWeight p R c T (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  apply periodicMean_independent
  · exact (mul_pos b.pos (sieveTermPeriod_pos p R T)).ne'
  · exact ht.ne'
  · exact periodic_rational_quadratic _ _ (sieveTermWeight_periodic p R c T) b
  · exact sieveTermQuadratic_periodic p R c T b t hpt hbt

lemma finiteRationalCoefficient_actual (H : ℝ) (b : ℚ) (t : ℕ) (ht : 0<t)
    (hpt : ∀i,p i∣t) (hbt : b.den∣t) :
    finiteRationalCoefficient (fun T : boundedSieveSets p H => sieveTermSign T.val)
      (fun T => sieveTermWeight p R c T.val) (fun T => sieveTermPeriod p R T.val) b=
      periodicMean (fun n => actualDivisorWeight p R c H (n+1)*expPhase ((b:ℝ)*(n+1)^2)) t := by
  unfold finiteRationalCoefficient
  simp_rw [sieveTermCoefficient_eq p R c _ b t ht hpt hbt,actualDivisorWeight_eq_terms,sum_mul]
  rw [periodicMean_sum]
  apply sum_congr rfl
  intro T _
  rw [← periodicMean_mul_left]
  congr 1
  funext n
  ring

lemma finiteRationalCoefficient_actual_uniform (hinj : Function.Injective p) (H : ℝ) (hH : 0<H)
    (htwo : ∀i,p i=2 → i∈R) (b : ℚ) (hb : b.den∣∏i,primaryModulus b.den (p i)) :
    ‖finiteRationalCoefficient (fun T : boundedSieveSets p H => sieveTermSign T.val)
      (fun T => sieveTermWeight p R c T.val) (fun T => sieveTermPeriod p R T.val) b-
      kernelModelCoefficient p R c H b‖≤2^64*H^(-(1:ℝ)/3) := by
  rw [finiteRationalCoefficient_actual p R c H b (∏i,primaryModulus b.den (p i))
      (prod_pos (fun i _ => primaryModulus_pos (Fact.out : (p i).Prime)))
      (fun i => (prime_dvd_primaryModulus b.den (p i)).trans
        (dvd_prod_of_mem (fun i => primaryModulus b.den (p i)) (mem_univ i))) hb,
    ← primaryModelCoefficient_eq_kernelModel p R c hinj b hb H htwo]
  exact actualDivisorWeight_coefficient_uniform p hinj b hb R c H hH htwo

lemma actualDivisorWeight_fourier (hinj : Function.Injective p) (H : ℝ) (hH : 0≤H) :
    ∃ (q : ℕ) (_ : NeZero q) (w : ZMod q → ℂ),
      (∀n,actualDivisorWeight p R c H n=
        ∑a : ZMod q,w a*expPhase (((a.val:ℝ)/q)*n)) ∧
      (∑a : ZMod q,‖w a‖)≤(∏i∈R,p i : ℕ)*H := by
  let q : ℕ := ∏i,p i
  have hq : 0<q := prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  let hq' : NeZero q := ⟨hq.ne'⟩
  have hpq (i : I) : p i∣q := dvd_prod_of_mem p (mem_univ i)
  obtain ⟨w,hw,hbound⟩ := ringDivisorWeight_fourier p R c q hpq hinj H hH
  refine ⟨q,hq',w,?_,hbound⟩
  intro n
  rw [← ringDivisorWeight_natCast p R c q hpq H n,hw]
  apply sum_congr rfl
  intro a _
  congr 1
  have he := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=q)) n a
  simp only [nsmul_eq_mul] at he
  rw [mul_comm a _,he,stdAddChar_eq_expPhase,←expPhase_nat_mul,mul_comm]

omit [DecidableEq I] in
lemma boundedSieveSets_card (hinj : Function.Injective p) (H : ℝ) (hH : 0≤H) :
    (Fintype.card (boundedSieveSets p H) : ℝ)≤H := by
  have hc := bounded_prime_subsets_card p (fun i => (Fact.out : (p i).Prime)) hinj
    (boundedSieveSets p H) ⌊H⌋₊ (fun T hT => Nat.le_floor ((mem_filter.mp hT).2))
  rw [Fintype.card_coe]
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hH)

omit [DecidableEq I] in
lemma sieveTermCost (hinj : Function.Injective p) (H : ℝ) (hH : 0≤H) :
    (∑T : boundedSieveSets p H, ‖sieveTermSign T.val‖*
      (2*(sieveTermPeriod p R T.val : ℝ)+1)*(∏i∈R,p i : ℕ))≤
      H*(2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ) := by
  calc
    _ ≤ ∑T : boundedSieveSets p H,
        (2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ) := by
      apply sum_le_sum
      intro T _
      rw [sieveTermSign_norm,one_mul,sieveTermPeriod,Nat.cast_mul]
      have ht := (mem_filter.mp T.property).2
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply add_le_add _ le_rfl
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (Fintype.card (boundedSieveSets p H) : ℝ)*
        ((2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ)) := by simp
    _ ≤ _ := by
      have hc := boundedSieveSets_card p hinj H hH
      nlinarith [show 0≤(2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ) by positivity]

noncomputable def actualSquareTransform (H : ℝ) (M N : ℕ) (α : ℝ) : ℂ :=
  ∑m∈range M,squareWeight N α m*actualDivisorWeight p R c H (m+1)

noncomputable def actualModelTransform (H : ℝ) (L N : ℕ) (α : ℝ) : ℂ :=
  ∑b : boundedRationals L,kernelModelCoefficient p R c H b.val*
    normalizedLinearSum N (α-b.val)

lemma finiteSquareKernel_actual (H : ℝ) (M N : ℕ) (α : ℝ) :
    finiteSquareKernel (fun T : boundedSieveSets p H => sieveTermSign T.val)
      (fun T => sieveTermWeight p R c T.val) M N α=actualSquareTransform p R c H M N α := by
  unfold finiteSquareKernel actualSquareTransform
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [actualDivisorWeight_eq_terms,mul_sum]
  apply sum_congr rfl
  intro T _
  ring

lemma actual_kernel_uniform (hinj : Function.Injective p)
    (H : ℝ) (hH : 0<H) (L T : ℕ) (X : ℝ)
    (hT : 0<T) (hL : 2*L≤T+1) (hX : 8≤X) (hLX : (L:ℝ)≤X)
    (hmodel : (rootSquareModulus p R : ℝ)*H≤L)
    (hcover : ∀b : ℚ, (b.den:ℝ)≤X → b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    (M N : ℕ) (hM : 1≤M) (hlo : M^2≤N) (hhi : N<(M+1)^2) (α : ℝ) :
    ‖actualSquareTransform p R c H M N α-actualModelTransform p R c H L N α‖≤
      2^64*H^(-(1:ℝ)/3)+
      (H*(2*(∏i∈R,p i : ℕ)*H+1)*(∏i∈R,p i : ℕ))*(4*X+8*Real.pi*N/((T:ℝ)+1))*M/N+
      ((∏i∈R,p i : ℕ)*H)*(4*(M:ℝ)/N)*Real.sqrt
        (5*M+32*(M:ℝ)^2/X+(64*M+8*T)*(1+Real.log T))+
      (L:ℝ)^2*((T:ℝ)*L/N) := by
  classical
  obtain ⟨q,hq,w,hw,hwn⟩ := actualDivisorWeight_fourier p R c hinj H hH.le
  let : NeZero q := hq
  have hz : (∑b : boundedRationals L,‖kernelModelCoefficient p R c H b.val‖)≤(L:ℝ)^2 := by
    calc
      _ ≤ ∑b : boundedRationals L,(1:ℝ) := by
        apply sum_le_sum
        intro b _
        exact kernelModelCoefficient_norm p R c hinj b.val
          (hcover b.val ((Nat.cast_le.mpr ((mem_boundedRationals L b.val).mp b.property).2.2).trans hLX)) H htwo
      _ = ((boundedRationals L).card:ℝ) := by simp
      _ ≤ _ := by exact_mod_cast boundedRationals_card L
  have hf := finite_kernel_uniform
    (fun T : boundedSieveSets p H => sieveTermSign T.val)
    (fun T => sieveTermWeight p R c T.val) (fun T => sieveTermPeriod p R T.val)
    (fun T => sieveTermPeriod_pos p R T.val) (fun T => sieveTermWeight_periodic p R c T.val)
    (fun _ => ((∏i∈R,p i : ℕ):ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun T m => sieveTermWeight_norm p R c T.val m)
    (fun b : boundedRationals L => b.val) (fun b => kernelModelCoefficient p R c H b.val)
    L T X (2^64*H^(-(1:ℝ)/3)) hT hL
    (fun b => ((mem_boundedRationals L b.val).mp b.property).2.2) hX hLX (by positivity)
    (fun b hb => by
      rw [bounded_kernel_model_center p R c hinj L H hmodel htwo hc b (hcover b hb)]
      exact finiteRationalCoefficient_actual_uniform p R c hinj H hH htwo b (hcover b hb))
    w (fun a : ZMod q => (a.val:ℝ)/q)
    (fun m => by rw [← actualDivisorWeight_eq_terms,hw]) M N hM hlo hhi α
  rw [finiteSquareKernel_actual] at hf
  apply hf.trans
  have hcost := sieveTermCost p R hinj H hH.le
  have hX0 : 0≤X := by linarith
  gcongr

end ActualKernelTerms

end SquareDifference

namespace SquareDifference

open Finset

noncomputable def rationalGridPoint (q : ℕ) (a : ZMod q) : ℚ := (a.val : ℚ)/q

lemma rationalGridPoint_nonneg (q : ℕ) (a : ZMod q) : 0≤rationalGridPoint q a := by
  unfold rationalGridPoint
  positivity

lemma rationalGridPoint_lt_one (q : ℕ) [NeZero q] (a : ZMod q) : rationalGridPoint q a<1 := by
  unfold rationalGridPoint
  rw [div_lt_one (Nat.cast_pos.mpr (NeZero.pos q))]
  exact_mod_cast ZMod.val_lt a

lemma rationalGridPoint_den_dvd (q : ℕ) (a : ZMod q) : (rationalGridPoint q a).den∣q := by
  have h := Rat.den_dvd (a.val : ℤ) (q : ℤ)
  rw [Rat.divInt_eq_div] at h
  simp only [Int.cast_natCast] at h
  exact Int.natCast_dvd_natCast.mp h

end SquareDifference
end

end OAI
