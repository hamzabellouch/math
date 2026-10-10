import OAI.Combinatorics.SquareDifference.UniformRates

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate

namespace SquareDifference

section CyclicFourier

variable {q : ℕ} [NeZero q]

noncomputable def cyclicChar (a x : ZMod q) : ℂ := ZMod.stdAddChar (a*x)

lemma cyclicChar_sub_right (a x y : ZMod q) :
    cyclicChar a (x-y)=cyclicChar a x*conj (cyclicChar a y) := by
  simp only [cyclicChar, mul_sub]
  simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]

lemma cyclicChar_neg (a x : ZMod q) : cyclicChar (-a) x=conj (cyclicChar a x) := by
  simp only [cyclicChar, neg_mul, AddChar.map_neg_eq_conj]

lemma cyclicChar_symm (a x : ZMod q) : cyclicChar a x=cyclicChar x a := by
  simp only [cyclicChar, mul_comm]

lemma cyclicChar_expect (a : ZMod q) :
    (𝔼 x, cyclicChar a x)=if a=0 then 1 else 0 := by
  classical
  rw [expect_eq_sum_div_card]
  simp only [cyclicChar, mul_comm a]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp only [card_univ,  ZMod.card]
  split_ifs <;> simp_all

lemma cyclicChar_orthogonal (a b : ZMod q) :
    (𝔼 x, cyclicChar a x*conj (cyclicChar b x))=if a=b then 1 else 0 := by
  classical
  have he x : cyclicChar (a-b) x=cyclicChar a x*conj (cyclicChar b x) := by
    simp only [cyclicChar, sub_mul]
    simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  simp_rw [← he]
  rw [cyclicChar_expect]
  simp only [sub_eq_zero]

noncomputable def cyclicPolynomial (c : ZMod q → ℂ) (x : ZMod q) : ℂ :=
  ∑a, c a*cyclicChar a x

noncomputable def cyclicFourier (f : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  𝔼 x, f x*conj (cyclicChar a x)

lemma cyclicPolynomial_parseval (c : ZMod q → ℂ) :
    (𝔼 x, ‖cyclicPolynomial c x‖^2)=∑a, ‖c a‖^2 := by
  classical
  have he : (𝔼 x, cyclicPolynomial c x*conj (cyclicPolynomial c x))=
      ∑a, c a*conj (c a) := by
    simp only [cyclicPolynomial, map_sum, sum_mul, mul_sum, map_mul]
    rw [expect_sum_comm]
    apply sum_congr rfl; intro a _
    rw [expect_sum_comm]
    have he a b x : c a*cyclicChar a x*(conj (c b)*conj (cyclicChar b x))=
        c a*conj (c b)*(cyclicChar a x*conj (cyclicChar b x)) := by ring
    simp only [he, ← mul_expect, cyclicChar_orthogonal]
    simp
  apply Complex.ofReal_injective
  simpa only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_expect] using he

lemma cyclicFourier_reconstruction (f : ZMod q → ℂ) (z : ZMod q) :
    cyclicPolynomial (cyclicFourier f) z=f z := by
  classical
  unfold cyclicPolynomial cyclicFourier
  simp_rw [Finset.expect_mul]
  rw [← expect_sum_comm]
  have he x : (∑a, f x*conj (cyclicChar a x)*cyclicChar a z)=
      f x*q*(if z=x then 1 else 0) := by
    simp_rw [mul_assoc, mul_comm (conj _), ← cyclicChar_sub_right]
    rw [← mul_sum]
    have hs := cyclicChar_expect (z-x)
    simp_rw [cyclicChar_symm _ (z-x)]
    rw [expect_eq_sum_div_card] at hs
    have hc : (Fintype.card (ZMod q) : ℂ)≠0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hs' := (div_eq_iff hc).mp hs
    rw [hs']
    simp only [sub_eq_zero, ZMod.card]
    ring
  simp only [he, expect_eq_sum_div_card, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ite_true, card_univ, ZMod.card]
  exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))

lemma cyclicFourier_parseval (f : ZMod q → ℂ) :
    (∑a, ‖cyclicFourier f a‖^2)=𝔼 x, ‖f x‖^2 := by
  rw [← cyclicPolynomial_parseval]
  simp only [cyclicFourier_reconstruction]

lemma cyclicFourier_neg (f : ZMod q → ℂ) (a : ZMod q) :
    cyclicFourier f (-a)=𝔼 x, f x*cyclicChar a x := by
  simp only [cyclicFourier, cyclicChar_neg, Complex.conj_conj]

lemma cyclic_bilinear_fourier (F G k : ZMod q → ℂ) :
    (𝔼 x, 𝔼 y, F x*G y*k (y-x))=
      ∑a, cyclicFourier k a*cyclicFourier F a*cyclicFourier G (-a) := by
  have hk z : k z=∑a, cyclicFourier k a*cyclicChar a z :=
    (cyclicFourier_reconstruction k z).symm
  simp_rw [hk, mul_sum, cyclicChar_sub_right, expect_sum_comm]
  apply sum_congr rfl
  intro a _
  have he x y : F x*G y*(cyclicFourier k a*(cyclicChar a y*conj (cyclicChar a x)))=
      cyclicFourier k a*(F x*conj (cyclicChar a x))*(G y*cyclicChar a y) := by ring
  simp_rw [he, ← mul_expect, ← expect_mul]
  rw [cyclicFourier_neg, ← mul_expect]
  rfl

lemma cyclic_bilinear_multiplier (F G k : ZMod q → ℂ)
    (δ : ℝ) (hδ : 0≤δ) (hk : ∀a, ‖cyclicFourier k a‖≤δ) :
    ‖𝔼 x, 𝔼 y, F x*G y*k (y-x)‖≤
      δ*Real.sqrt (𝔼 x, ‖F x‖^2)*Real.sqrt (𝔼 x, ‖G x‖^2) := by
  rw [cyclic_bilinear_fourier]
  calc
    _ ≤ ∑a, ‖cyclicFourier k a*cyclicFourier F a*cyclicFourier G (-a)‖ := norm_sum_le _ _
    _ ≤ δ*∑a, ‖cyclicFourier F a‖*‖cyclicFourier G (-a)‖ := by
      rw [mul_sum]
      apply sum_le_sum
      intro a _
      simp only [norm_mul]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hk a) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ δ*(Real.sqrt (∑a, ‖cyclicFourier F a‖^2)*
        Real.sqrt (∑a, ‖cyclicFourier G (-a)‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hδ
    _ = _ := by
      have hs : (∑a, ‖cyclicFourier G (-a)‖^2)=∑a, ‖cyclicFourier G a‖^2 :=
        Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ (fun a => rfl)
      rw [hs, cyclicFourier_parseval, cyclicFourier_parseval]
      ring

lemma cyclic_bilinear_counting (F G k : ZMod q → ℂ)
    (δ : ℝ) (hδ : 0≤δ) (hk : ∀a, ‖∑x, k x*conj (cyclicChar a x)‖≤δ) :
    ‖∑x, ∑y, F x*G y*k (y-x)‖≤
      δ*Real.sqrt (∑x, ‖F x‖^2)*Real.sqrt (∑x, ‖G x‖^2) := by
  have hq : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq' : (q:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hf (a : ZMod q) : ‖cyclicFourier k a‖≤δ/q := by
    simp only [cyclicFourier,expect_eq_sum_div_card,card_univ,ZMod.card,norm_div,
      Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hk a) hq.le
  have h := cyclic_bilinear_multiplier F G k (δ/q) (div_nonneg hδ hq.le) hf
  have he : (𝔼 x, 𝔼 y, F x*G y*k (y-x))=
      (∑x, ∑y, F x*G y*k (y-x))/(q:ℂ)^2 := by
    simp only [expect_eq_sum_div_card,card_univ,ZMod.card,← sum_div]
    field_simp
  rw [he,norm_div,norm_pow,Complex.norm_natCast] at h
  simp only [expect_eq_sum_div_card,card_univ,ZMod.card] at h
  simp only [Real.sqrt_div' _ hq.le] at h
  have hs : Real.sqrt (q:ℝ)*Real.sqrt q=q := Real.mul_self_sqrt hq.le
  have hs0 : 0<Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hq
  have hr : δ/q*(Real.sqrt (∑x, ‖F x‖^2)/Real.sqrt q)*
      (Real.sqrt (∑x, ‖G x‖^2)/Real.sqrt q)=
      (δ*Real.sqrt (∑x, ‖F x‖^2)*Real.sqrt (∑x, ‖G x‖^2))/q^2 := by
    field_simp
    rw [Real.sq_sqrt hq.le]
    ring
  rw [hr] at h
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hq)).mp h

lemma cyclic_bilinear_normalized (F G k : ZMod q → ℂ)
    (N : ℝ) (hN : 0<N) (δ : ℝ) (hδ : 0≤δ)
    (hk : ∀a, ‖∑x, k x*conj (cyclicChar a x)‖≤δ)
    (hF : (∑x, ‖F x‖^2)≤N) (hG : (∑x, ‖G x‖^2)≤N) :
    ‖((∑x, ∑y, F x*G y*k (y-x)) : ℂ)/N‖≤δ := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ δ*Real.sqrt (∑x, ‖F x‖^2)*Real.sqrt (∑x, ‖G x‖^2) :=
      cyclic_bilinear_counting F G k δ hδ hk
    _ ≤ δ*Real.sqrt N*Real.sqrt N := by gcongr
    _ = δ*N := by rw [mul_assoc,Real.mul_self_sqrt hN.le]

end CyclicFourier

end SquareDifference

namespace SquareDifference

open Finset

lemma cyclicChar_nat {q : ℕ} [NeZero q] (a : ZMod q) (n : ℕ) :
    cyclicChar a (n:ZMod q)=expPhase (((a.val:ℝ)/q)*n) := by
  have hs := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=q)) n a
  simp only [nsmul_eq_mul] at hs
  rw [cyclicChar,mul_comm a _,hs,stdAddChar_eq_expPhase,← expPhase_nat_mul,mul_comm]

section SequenceKernel

variable {q : ℕ} [instNeZeroq : NeZero q]

noncomputable def cyclicPush {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (z : ZMod q) : ℂ := ∑t∈s, if shift t=z then w t else 0

lemma cyclicPush_transform {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (a : ZMod q) :
    (∑z, cyclicPush s shift w z*conj (cyclicChar a z))=
      ∑t∈s, w t*conj (cyclicChar a (shift t)) := by
  classical
  simp only [cyclicPush,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl; intro t ht
  simp only [ite_mul,zero_mul]
  simp

lemma cyclicPush_point {q : ℕ}
    [NeZero q] {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (hinj : Set.InjOn shift s) (t : T) (ht : t∈s) :
    cyclicPush s shift w (shift t)=w t := by
  classical
  unfold cyclicPush
  rw [sum_eq_single t]
  · simp
  · intro u hu hut
    exact ite_eq_right (fun h => hut (hinj hu ht h))
  · exact fun hh => (hh ht).elim

lemma cyclicPush_bilinear_zero {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (F G : ZMod q → ℂ)
    (hz : ∀x y t, t∈s → shift t=y-x → F x*G y=0) :
    (∑x, ∑y, F x*G y*cyclicPush s shift w (y-x))=0 := by
  classical
  apply sum_eq_zero; intro x _
  apply sum_eq_zero; intro y _
  rw [cyclicPush,mul_sum]
  apply sum_eq_zero; intro t ht
  split_ifs with h
  · rw [hz x y t ht h,zero_mul]
  · exact mul_zero _

lemma cyclic_interval_injective {q : ℕ}
    [NeZero q] (N : ℕ) (hN : N<q) :
    Set.InjOn (fun n : ℕ => ((n+1:ℕ):ZMod q)) (range N) := by
  intro n hn m hm he
  have hn' : n+1<q := lt_of_le_of_lt (by simpa using Nat.succ_le_of_lt (mem_range.mp hn)) hN
  have hm' : m+1<q := lt_of_le_of_lt (by simpa using Nat.succ_le_of_lt (mem_range.mp hm)) hN
  have h := congrArg ZMod.val he
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hn',Nat.mod_eq_of_lt hm'] at h
  omega

lemma cyclic_interval_point (N : ℕ) (hN : N<q) (w : ℕ → ℂ) (z : ZMod q)
    (hz : 1≤z.val ∧ z.val≤N) :
    cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q)) w z=w (z.val-1) := by
  have hh : ((z.val-1+1:ℕ):ZMod q)=z := by
    rw [Nat.sub_add_cancel hz.1,ZMod.natCast_zmod_val]
  rw [← hh]
  have hn : z.val-1∈range N := mem_range.mpr (by omega)
  convert cyclicPush_point (range N) _ w (cyclic_interval_injective N hN) _ hn using 1
  rw [hh]

end SequenceKernel

end SquareDifference

namespace SquareDifference

open Finset

section OrderedModel

variable {q : ℕ} [NeZero q]

noncomputable def intervalFourier (N : ℕ) (F : ZMod q → ℂ) (α : ℝ) : ℂ :=
  (N:ℂ)⁻¹*∑x, F x*expPhase (-(x.val:ℝ)*α)

noncomputable def intervalModelWeight {B : Type*} [Fintype B]
    (N : ℕ) (β : B → ℝ) (c : B → ℂ) (n : ℕ) : ℂ :=
  (N:ℂ)⁻¹*∑b, c b*expPhase (-β b*((n:ℝ)+1))

lemma intervalModel_bilinear {B : Type*} [Fintype B]
    (N : ℕ) (hN : N<q) (β : B → ℝ) (c : B → ℂ) (F G : ZMod q → ℂ)
    (hord : ∀x y, F x*G y≠0 → x.val<y.val ∧ y.val≤N) :
    ((∑x, ∑y, F x*G y*cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q))
      (intervalModelWeight N β c) (y-x)) : ℂ)/N=
      ∑b, c b*intervalFourier N F (-β b)*intervalFourier N G (β b) := by
  classical
  have he (x y : ZMod q) : F x*G y*cyclicPush (range N)
      (fun n => ((n+1:ℕ):ZMod q)) (intervalModelWeight N β c) (y-x)=
      (N:ℂ)⁻¹*∑b, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
        (G y*expPhase (-(y.val:ℝ)*β b)) := by
    by_cases hz : F x*G y=0
    · rw [hz,zero_mul]
      symm
      rw [mul_eq_zero]
      refine Or.inr (sum_eq_zero (fun b _ => ?_))
      calc
        _ = c b*(F x*G y)*(expPhase (-(x.val:ℝ)*(-β b))*expPhase (-(y.val:ℝ)*β b)) := by ring
        _ = 0 := by rw [hz]; ring
    · obtain ⟨hxy,hy⟩ := hord x y hz
      have hval : (y-x).val=y.val-x.val := ZMod.val_sub (le_of_lt hxy)
      rw [cyclic_interval_point N hN _ _ (by rw [hval]; omega),intervalModelWeight]
      have hv : (((y-x).val-1:ℕ):ℝ)+1=(y.val:ℝ)-(x.val:ℝ) := by
        rw [hval,Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
        norm_num
      rw [hv]
      simp only [mul_sum]
      apply sum_congr rfl
      intro b _
      have hp : expPhase (-β b*((y.val:ℝ)-(x.val:ℝ)))=
          expPhase (-(x.val:ℝ)*(-β b))*expPhase (-(y.val:ℝ)*β b) := by
        rw [← expPhase_add]
        congr 1
        ring
      rw [hp]
      ring
  have hswap : (∑x, ∑y, ∑b, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
      (G y*expPhase (-(y.val:ℝ)*β b)))=
      ∑b, ∑x, ∑y, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
        (G y*expPhase (-(y.val:ℝ)*β b)) := by
    have hh (x : ZMod q) : (∑y, ∑b, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
        (G y*expPhase (-(y.val:ℝ)*β b)))=
        ∑b, ∑y, c b*(F x*expPhase (-(x.val:ℝ)*(-β b)))*
          (G y*expPhase (-(y.val:ℝ)*β b)) := sum_comm
    simp_rw [hh]
    exact sum_comm
  simp_rw [he]
  simp only [← mul_sum]
  rw [hswap]
  simp only [← mul_sum,← sum_mul]
  rw [mul_sum,sum_div]
  apply sum_congr rfl
  intro b _
  unfold intervalFourier
  ring

end OrderedModel

end SquareDifference

namespace SquareDifference

open Finset

section KernelTransforms

variable {q : ℕ} [NeZero q]

lemma cyclic_square_transform (M N : ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑z, cyclicPush (range M) (fun m => (((m+1)^2:ℕ):ZMod q))
      (fun m => (2*((m:ℝ)+1)/(N:ℝ):ℝ) • w (m+1)) z*conj (cyclicChar a z))=
      ∑m∈range M, squareWeight N (-(a.val:ℝ)/q) m*w (m+1) := by
  rw [cyclicPush_transform]
  apply sum_congr rfl
  intro m hm
  rw [cyclicChar_nat,← expPhase_neg]
  have he : -((a.val:ℝ)/q*((((m+1)^2:ℕ):ℝ)))=
      (-(a.val:ℝ)/q)*((m:ℝ)+1)^2 := by push_cast; ring
  rw [he]
  simp only [squareWeight,Complex.real_smul]
  ring

lemma cyclic_model_transform {B : Type*} [Fintype B]
    (N : ℕ) (β : B → ℝ) (c : B → ℂ) (a : ZMod q) :
    (∑z, cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q))
      (intervalModelWeight N β c) z*conj (cyclicChar a z))=
      ∑b, c b*normalizedLinearSum N (-(a.val:ℝ)/q-β b) := by
  rw [cyclicPush_transform]
  simp only [intervalModelWeight,cyclicChar_nat,← expPhase_neg,mul_sum,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  unfold normalizedLinearSum
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,mul_sum]
  apply sum_congr rfl
  intro n hn
  have he : expPhase (-β b*((n:ℝ)+1))*expPhase (-((a.val:ℝ)/q*((n+1:ℕ):ℝ)))=
      expPhase ((-(a.val:ℝ)/q-β b)*((n:ℝ)+1)) := by
    rw [← expPhase_add]
    congr 1
    push_cast
    ring
  calc
    _ = c b*((N:ℂ)⁻¹*(expPhase (-β b*((n:ℝ)+1))*
        expPhase (-((a.val:ℝ)/q*((n+1:ℕ):ℝ))))) := by ring
    _ = _ := by rw [he]

lemma ordered_square_kernel_bilinear {B : Type*} [Fintype B]
    (M N : ℕ) (hN : 0<N) (hq : N<q) (w : ℕ → ℂ)
    (β : B → ℝ) (c : B → ℂ) (δ : ℝ) (hδ : 0≤δ)
    (hkernel : ∀α : ℝ,
      ‖(∑m∈range M, squareWeight N α m*w (m+1))-
        ∑b, c b*normalizedLinearSum N (α-β b)‖≤δ)
    (F G : ZMod q → ℂ)
    (hF : (∑x, ‖F x‖^2)≤N) (hG : (∑x, ‖G x‖^2)≤N)
    (hord : ∀x y, F x*G y≠0 → x.val<y.val ∧ y.val≤N)
    (hsquare : ∀x y m, m∈range M → (((m+1)^2:ℕ):ZMod q)=y-x → F x*G y=0) :
    ‖∑b, c b*intervalFourier N F (-β b)*intervalFourier N G (β b)‖≤δ := by
  let k₁ : ZMod q → ℂ := cyclicPush (range M) (fun m => (((m+1)^2:ℕ):ZMod q))
    (fun m => (2*((m:ℝ)+1)/(N:ℝ):ℝ) • w (m+1))
  let k₂ : ZMod q → ℂ := cyclicPush (range N) (fun n => ((n+1:ℕ):ZMod q))
    (intervalModelWeight N β c)
  have hk : ∀a, ‖∑z, (k₁ z-k₂ z)*conj (cyclicChar a z)‖≤δ := by
    intro a
    simp only [sub_mul,sum_sub_distrib]
    rw [show (∑z, k₁ z*conj (cyclicChar a z))=
      ∑m∈range M, squareWeight N (-(a.val:ℝ)/q) m*w (m+1) from
      cyclic_square_transform M N w a]
    rw [show (∑z, k₂ z*conj (cyclicChar a z))=
      ∑b, c b*normalizedLinearSum N (-(a.val:ℝ)/q-β b) from
      cyclic_model_transform N β c a]
    exact hkernel _
  have hz : (∑x, ∑y, F x*G y*k₁ (y-x))=0 :=
    cyclicPush_bilinear_zero _ _ _ F G hsquare
  have he := intervalModel_bilinear N hq β c F G hord
  have hb := cyclic_bilinear_normalized F G (fun z => k₁ z-k₂ z) N
    (Nat.cast_pos.mpr hN) δ hδ hk hF hG
  simp only [mul_sub,sum_sub_distrib,hz,zero_sub] at hb
  simp only [neg_div,norm_neg,Complex.ofReal_natCast] at hb
  exact he ▸ hb

end KernelTransforms

end SquareDifference

namespace SquareDifference

open Finset

section ActualBilinear

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime]
  (R : Finset I) (c : ∀i,ZMod (p i))

lemma actual_kernel_ordered_bilinear (hinj : Function.Injective p)
    (H : ℝ) (hH : 1≤H) (N : ℕ) (hN : 1≤N)
    (hD : (rootSquareModulus p R:ℝ)≤(N:ℝ)^((1:ℝ)/1000))
    (hHn : H≤(N:ℝ)^((1:ℝ)/1000)) (hlarge : 8≤(N:ℝ)^((1:ℝ)/16))
    (hcover : ∀b : ℚ,(b.den:ℝ)≤(N:ℝ)^((1:ℝ)/8) →
      b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (hq : N<q) (F G : ZMod q → ℂ)
    (hF : (∑x,‖F x‖^2)≤N) (hG : (∑x,‖G x‖^2)≤N)
    (hord : ∀x y,F x*G y≠0 → x.val<y.val ∧ y.val≤N)
    (hsquare : ∀x y m,m∈range N.sqrt → (((m+1)^2:ℕ):ZMod q)=y-x → F x*G y=0) :
    ‖∑b : boundedRationals ⌈(rootSquareModulus p R:ℝ)*H⌉₊,
      kernelModelCoefficient p R c H b.val*
        intervalFourier N F (-(b.val:ℝ))*intervalFourier N G b.val‖≤
      kernelAbsoluteConstant*H^(-(1:ℝ)/3) := by
  apply ordered_square_kernel_bilinear N.sqrt N (by omega) hq
    (actualDivisorWeight p R c H) (fun b : boundedRationals ⌈(rootSquareModulus p R:ℝ)*H⌉₊ => (b.val:ℝ))
    (fun b => kernelModelCoefficient p R c H b.val)
    (kernelAbsoluteConstant*H^(-(1:ℝ)/3))
  · unfold kernelAbsoluteConstant
    positivity
  · exact actual_kernel_power_error p R c hinj H hH N hN hD hHn hlarge hcover htwo hc
  · exact hF
  · exact hG
  · exact hord
  · exact hsquare

end ActualBilinear

end SquareDifference

namespace SquareDifference

open Finset

section DualCoordinates

variable {q : ℕ} [NeZero q]

noncomputable def standardCharEquiv : ZMod q ≃ AddChar (ZMod q) ℂ :=
  Equiv.ofBijective (fun a => (ZMod.stdAddChar (N:=q)).mulShift a) (by
    rw [Fintype.bijective_iff_injective_and_card,AddChar.card_eq]
    refine ⟨?_,rfl⟩
    intro a b h
    have h1 := congrArg (fun ψ : AddChar (ZMod q) ℂ => ψ 1) h
    simp only [AddChar.mulShift_apply,mul_one] at h1
    exact ZMod.injective_stdAddChar h1)

lemma standardCharEquiv_apply (a x : ZMod q) :
    standardCharEquiv a x=ZMod.stdAddChar (a*x) := rfl

lemma standardCharEquiv_symm_apply (ψ : AddChar (ZMod q) ℂ) (x : ZMod q) :
    ZMod.stdAddChar ((standardCharEquiv (q:=q)).symm ψ*x)=ψ x := by
  rw [← standardCharEquiv_apply,(standardCharEquiv (q:=q)).apply_symm_apply]

lemma standardCharEquiv_zero : standardCharEquiv (0:ZMod q)=1 := by
  ext x
  simp [standardCharEquiv_apply,AddChar.map_zero_eq_one]

lemma rationalGrid_char (a : ZMod q) :
    (rationalChar (rationalGridPoint q a)).compAddMonoidHom
      (ZMod.castHom (rationalGridPoint_den_dvd q a) (ZMod (rationalGridPoint q a).den)).toAddMonoidHom=
      standardCharEquiv a := by
  ext x
  have hx : x=(x.val:ZMod q) := (ZMod.natCast_zmod_val x).symm
  rw [hx]
  change rationalChar (rationalGridPoint q a)
    ((ZMod.castHom (rationalGridPoint_den_dvd q a) (ZMod (rationalGridPoint q a).den))
      (x.val:ZMod q))=ZMod.stdAddChar (a*(x.val:ZMod q))
  rw [map_natCast]
  have he := rationalChar_int (rationalGridPoint q a) (x.val:ℤ)
  simp only [Int.cast_natCast] at he
  rw [he]
  have hs := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=q)) x.val a
  simp only [nsmul_eq_mul] at hs
  rw [mul_comm a _,hs,stdAddChar_eq_expPhase,← expPhase_nat_mul]
  congr 1
  simp only [rationalGridPoint,Rat.cast_div,Rat.cast_natCast]
  ring

end DualCoordinates

section ProductDual

variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)] (hcop : Pairwise fun i j => (m i).Coprime (m j))

local instance productModulusNeZero : NeZero (∏i,m i) :=
  ⟨prod_ne_zero_iff.mpr (fun _ _ => NeZero.ne _)⟩

noncomputable def dualCRTCoordinates (a : ZMod (∏i,m i)) (i : I) : ZMod (m i) :=
  standardCharEquiv.symm
    (coordinateChar ((standardCharEquiv a).compAddMonoidHom
      (ZMod.prodEquivPi m hcop).symm.toAddMonoidHom) i)

lemma dualCRTCoordinates_char (a : ZMod (∏i,m i)) (i : I) (x : ZMod (m i)) :
    ZMod.stdAddChar (dualCRTCoordinates m hcop a i*x)=
      coordinateChar ((standardCharEquiv a).compAddMonoidHom
        (ZMod.prodEquivPi m hcop).symm.toAddMonoidHom) i x := by
  exact standardCharEquiv_symm_apply _ x

lemma dualCRTCoordinates_product (a : ZMod (∏i,m i)) (x : ∀i,ZMod (m i)) :
    ZMod.stdAddChar (a*(ZMod.prodEquivPi m hcop).symm x)=
      ∏i,ZMod.stdAddChar (dualCRTCoordinates m hcop a i*x i) := by
  simp_rw [dualCRTCoordinates_char]
  exact additive_character_product
    ((standardCharEquiv a).compAddMonoidHom (ZMod.prodEquivPi m hcop).symm.toAddMonoidHom) x

lemma dualCRTCoordinates_injective : Function.Injective (dualCRTCoordinates m hcop) := by
  intro a b hab
  apply standardCharEquiv.injective
  ext x
  obtain ⟨y,rfl⟩ := (ZMod.prodEquivPi m hcop).symm.surjective x
  change ZMod.stdAddChar (a*(ZMod.prodEquivPi m hcop).symm y)=
    ZMod.stdAddChar (b*(ZMod.prodEquivPi m hcop).symm y)
  rw [dualCRTCoordinates_product,dualCRTCoordinates_product,hab]

noncomputable def dualCRTEquiv : ZMod (∏i,m i) ≃ ∀i,ZMod (m i) :=
  Equiv.ofBijective (dualCRTCoordinates m hcop) (by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨dualCRTCoordinates_injective m hcop,by simp [Fintype.card_pi]⟩)

lemma dualCRT_nat (a : ZMod (∏i,m i)) (n : ℕ) :
    ZMod.stdAddChar (a*(n:ZMod (∏i,m i)))=
      ∏i,ZMod.stdAddChar (dualCRTEquiv m hcop a i*(n:ZMod (m i))) := by
  have h := dualCRTCoordinates_product m hcop a (fun _ => (n:_))
  have hn : (ZMod.prodEquivPi m hcop).symm (fun _ => (n:_))=(n:ZMod (∏i,m i)) := by
    apply (ZMod.prodEquivPi m hcop).injective
    rw [RingEquiv.apply_symm_apply]
    simp only [map_natCast]
    rfl
  rw [hn] at h
  exact h

end ProductDual

end SquareDifference

namespace SquareDifference

open Finset

section SmallDual

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)

local instance smallFactorNeZero (i : I) : NeZero (smallQuadraticModulus (p i)) :=
  ⟨(smallQuadraticModulus_pos (Fact.out : (p i).Prime)).ne'⟩

noncomputable def smallDualEquiv :
    ZMod (∏i,smallQuadraticModulus (p i)) ≃ ∀i,ZMod (smallQuadraticModulus (p i)) :=
  dualCRTEquiv _ (smallQuadraticModuli_pairwise p (fun _ => Fact.out) hinj)

lemma smallCoordinateChar_grid (a : ZMod (∏i,smallQuadraticModulus (p i))) (i : I) :
    smallCoordinateChar p hinj (rationalGridPoint _ a)
      (rationalGridPoint_den_dvd _ a) i=standardCharEquiv (smallDualEquiv p hinj a i) := by
  ext x
  unfold smallCoordinateChar
  rw [rationalGrid_char]
  symm
  exact dualCRTCoordinates_char _ _ a i x

lemma smallDual_active (a : ZMod (∏i,smallQuadraticModulus (p i)))
    (i : I) (h2 : p i≠2) :
    p i∣(rationalGridPoint _ a).den ↔ smallDualEquiv p hinj a i≠0 := by
  have he := smallCoordinateChar_grid p hinj a i
  constructor
  · intro hd hz
    have hp := smallCoordinateChar_primitive p hinj _ (rationalGridPoint_den_dvd _ a) i h2 hd
    rw [he,hz,standardCharEquiv_zero] at hp
    have hne : (1:ZMod (smallQuadraticModulus (p i)))≠0 := by
      rw [ne_eq,ZMod.one_eq_zero_iff]
      simpa only [smallQuadraticModulus,ite_eq_right h2] using (Fact.out : (p i).Prime).ne_one
    have hh := hp hne
    exact hh (by ext x; simp)
  · intro hn
    by_contra hd
    have ht := smallCoordinateChar_trivial p hinj _ (rationalGridPoint_den_dvd _ a) i hd
    rw [he,← standardCharEquiv_zero] at ht
    exact hn (standardCharEquiv.injective ht)

lemma smallDual_support (a : ZMod (∏i,smallQuadraticModulus (p i))) (R : Finset I)
    (htwo : ∀i,p i=2 → i∈R) :
    primaryActive p (rationalGridPoint _ a).den\R=
      Rᶜ.filter (fun i => smallDualEquiv p hinj a i≠0) := by
  classical
  ext i
  by_cases hi : i∈R
  · simp [hi]
  · have h2 : p i≠2 := fun hh => hi (htwo i hh)
    simp only [Finset.mem_sdiff,mem_primaryActive,mem_filter,mem_compl,hi,not_false_eq_true,and_true,true_and]
    exact smallDual_active p hinj a i h2

lemma kernelModelCoefficient_dual (a : ZMod (∏i,smallQuadraticModulus (p i)))
    (R : Finset I) (c : ∀i,ZMod (p i)) (H : ℝ)
    (htwo : ∀i,p i=2 → i∈R) (hc : ∀i∈R,p i=2 → c i=1) :
    kernelModelCoefficient p R c H (rationalGridPoint _ a)=
      if ((∏i∈Rᶜ.filter (fun i => smallDualEquiv p hinj a i≠0),p i : ℕ):ℝ)≤H then
        ∏i, if i∈R then ZMod.stdAddChar
          (smallDualEquiv p hinj a i*smallRootSquare (p i) (c i))
          else unitQuadraticMean (standardCharEquiv (smallDualEquiv p hinj a i))
      else 0 := by
  rw [kernelModelCoefficient_small p hinj R c _ (rationalGridPoint_den_dvd _ a) H htwo hc,
    smallDual_support p hinj a R htwo]
  simp only [smallCoordinateChar_grid,standardCharEquiv_apply]

end SmallDual

end SquareDifference

end

end OAI
