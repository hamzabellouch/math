import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughSampling02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
open Filter FinitePieceAverages
namespace RoughSamplingWeights
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 
def jointAffine (u : ι → ℤ) (K : ℕ) (y : Option ι → ℝ) : Option ι → ℝ
  | none => y none
  | some i => (u i:ℝ)+(K:ℝ)*y (some i)

omit [Fintype ι] [DecidableEq ι] in
theorem jointAffine_degree {f : (Option ι → ℝ) → ℝ} {d : ℕ}
    (hf : RealPolynomialDegree.HasDegree f d) (u : ι → ℤ) (K : ℕ) :
    RealPolynomialDegree.HasDegree (fun y=>f (jointAffine u K y)) d := by
  have h:=RealPolynomialDegree.affine_comp hf
    (fun o=>Option.elim o 0 (fun i=>(u i:ℝ)))
    (fun o=>Option.elim o 1 (fun _=>(K:ℝ))) id
  convert h using 1
  funext y
  congr 1
  funext o
  cases o <;> simp [jointAffine]

 

theorem rescaled_discrepancy (u a : ι → ℤ) (K t : ℕ) (hK : 0<K)
    (h : K.Coprime t) :
    ∃ b : ι → ℤ,∀ (lo hi : ι → ℝ) (f : (ι → ℤ) → ℂ) (η : ℝ),
      η≤‖mean (physicalResidueBox lo hi u K) f-
        mean ((physicalResidueBox lo hi u K).filter (fun x=>∀ i,x i ≡ a i [ZMOD t])) f‖ ↔
      η≤‖mean (boxIndices (rescaledEndpoint lo u K) (rescaledEndpoint hi u K)
          (fun _=>0) 1) (fun y=>f (integerAffine u K y))-
        mean ((boxIndices (rescaledEndpoint lo u K) (rescaledEndpoint hi u K)
          (fun _=>0) 1).filter (fun y=>∀ i,y i ≡ b i [ZMOD t]))
          (fun y=>f (integerAffine u K y))‖ := by
  obtain ⟨b,hb⟩:=residual_mean u a K t hK h
  refine ⟨b,fun lo hi f η=>?_⟩
  rw [residue_mean lo hi u K hK f,hb lo hi f]

 

theorem fixed_period_preserves_scales {α : Type*} {l : Filter α}
    (Z S : α → ℝ) (K : ℕ) (hK : 0<K)
    (h : ∀ a : ℕ,Tendsto (fun N=>Z N/S N^a) l atTop) :
    ∀ a : ℕ,Tendsto (fun N=>(Z N/K)/S N^a) l atTop := by
  intro a
  have hKr : (0:ℝ)<K:=by exact_mod_cast hK
  simpa only [div_right_comm] using (h a).atTop_div_const hKr

end RoughSamplingWeights
end
 
end

section
 

 

open _root_.Polynomial _root_.OAI.Polynomial Filter
open scoped Topology
namespace RoughScales

def Smooth (w : ℕ) (b : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → p ≤ w

def Rough (w : ℕ) (t : ℤ) : Prop := ∀ p : ℕ, p.Prime → p ≤ w → ¬ (p : ℤ) ∣ t

 
lemma rough_iff_coprime (w : ℕ) (t : ℤ) :
    Rough w t ↔ t.natAbs.Coprime (primorial w) := by
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpt hpW
    exact h p hp (hp.dvd_primorial_iff.mp hpW) (Int.natCast_dvd.mpr hpt)
  · intro h p hp hpw hpt
    apply hp.not_dvd_one
    rw [← h]
    exact Nat.dvd_gcd (Int.natCast_dvd.mp hpt) (hp.dvd_primorial_iff.mpr hpw)

lemma smooth_of_abs_le {w : ℕ} {D : ℤ} (hD : D ≠ 0) (hw : D.natAbs ≤ w) :
    Smooth w D := by
  intro p _ hp
  exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hD) (Int.natCast_dvd.mp hp)).trans hw

lemma coprime_smooth_rough {w : ℕ} {b t : ℤ} (hb : Smooth w b) (ht : Rough w t) :
    IsCoprime b t := by
  rw [Int.isCoprime_iff_nat_coprime]
  apply Nat.coprime_of_dvd
  intro p hp hpb hpt
  exact ht p hp (hb p hp (Int.natCast_dvd.mpr hpb)) (Int.natCast_dvd.mpr hpt)

 
lemma denominator_dvd_of_integral_multiple {D : ℤ} (hD : D ≠ 0) {x : ℚ}
    (hx : ∃ n : ℤ, (n : ℚ) = (D : ℚ) * x) : x.den ∣ D.natAbs := by
  obtain ⟨n, hn⟩ := hx
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have heq : x = Rat.divInt n D := by
    rw [Rat.divInt_eq_div, hn, mul_div_cancel_left₀ _ hDq]
  rw [heq]
  exact Int.natCast_dvd.mp (Rat.den_dvd n D)

lemma coefficients_smooth {D : ℤ} {w : ℕ} (hD : D ≠ 0) (hw : Smooth w D)
    {M : ℚ[X]} (hM : C (D : ℚ) * M ∈ lifts (algebraMap ℤ ℚ)) :
    ∀ j p : ℕ, p.Prime → p ∣ (M.coeff j).den → p ≤ w := by
  intro j p hp hpd
  have h := (lifts_iff_coeff_lifts _).mp hM j
  obtain ⟨n, hn⟩ := h
  simp only [coeff_C_mul] at hn
  have hden := denominator_dvd_of_integral_multiple hD ⟨n, hn⟩
  exact hw p hp (Int.natCast_dvd.mpr (hpd.trans hden))

 
lemma derivative_error_bound {A K D S Z a b : ℝ} {e q : ℕ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hD : 0 ≤ D) (hS : 1 ≤ S) (hZ : S ≤ Z)
    (ha : |a| ≤ 2 * S) (hb1 : 1 ≤ |b|) (hbS : |b| ≤ S) (he : 1 ≤ e) :
    A * (S / Z) ^ e * K * (1 + |-a / b|) ^ q * (D * |b| ^ q) ≤
      A * K * D * 3 ^ q * (S ^ (2 * q + 1) / Z) := by
  have hSpos : 0 < S := by linarith
  have hZpos : 0 < Z := hSpos.trans_le hZ
  have hbpos : 0 < |b| := by linarith
  have hratio : 0 ≤ S / Z := by positivity
  have hratio1 : S / Z ≤ 1 := (div_le_one hZpos).mpr hZ
  have hpow : (S / Z) ^ e ≤ S / Z := by
    simpa only [pow_one] using pow_le_pow_of_le_one hratio hratio1 he
  have hab : |-a / b| ≤ 2 * S := by
    rw [abs_div, abs_neg]
    exact (div_le_div_of_nonneg_left (abs_nonneg a) (by norm_num : (0 : ℝ) < 1) hb1).trans
      (by simpa using ha)
  calc
    _ ≤ A * (S / Z) * K * (3 * S) ^ q * (D * S ^ q) := by
      gcongr
      linarith
    _ = _ := by
      rw [mul_pow, pow_add, pow_mul, pow_one]
      ring

 
lemma inverse_ratio_tendsto {S Z : ℕ → ℝ} {k : ℕ}
    (h : Tendsto (fun n => Z n / S n ^ k) atTop atTop) :
    Tendsto (fun n => S n ^ k / Z n) atTop (𝓝 0) := by
  simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp h

end RoughScales
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughSamplingWeights
open FinitePieceAverages
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma period_coprime_of_rough (w K t : ℕ) (hK : 0<K) (hKw : K≤w)
    (ht : t.Coprime (primorial w)) : K.Coprime t := by
  have hs : RoughScales.Smooth w (K:ℤ):=RoughScales.smooth_of_abs_le
    (by exact_mod_cast (Nat.ne_of_gt hK)) (by simpa using hKw)
  have hr : RoughScales.Rough w (t:ℤ):=(RoughScales.rough_iff_coprime w (t:ℤ)).mpr
    (by simpa using ht)
  simpa only [Int.natAbs_natCast] using
    (Int.isCoprime_iff_nat_coprime.mp (RoughScales.coprime_smooth_rough hs hr))

 

theorem source_rescaled_discrepancy (u a : ι → ℤ) (w K t : ℕ) (hK : 0<K)
    (hKw : K≤w) (ht : t.Coprime (primorial w)) :
    ∃ b : ι → ℤ,∀ (lo hi : ι → ℝ) (f : (ι → ℤ) → ℂ) (η : ℝ),
      η≤‖mean (physicalResidueBox lo hi u K) f-
        mean ((physicalResidueBox lo hi u K).filter (fun x=>∀ i,x i ≡ a i [ZMOD t])) f‖ ↔
      η≤‖mean (boxIndices (rescaledEndpoint lo u K) (rescaledEndpoint hi u K)
          (fun _=>0) 1) (fun y=>f (integerAffine u K y))-
        mean ((boxIndices (rescaledEndpoint lo u K) (rescaledEndpoint hi u K)
          (fun _=>0) 1).filter (fun y=>∀ i,y i ≡ b i [ZMOD t]))
          (fun y=>f (integerAffine u K y))‖ :=
  rescaled_discrepancy u a K t hK (period_coprime_of_rough w K t hK hKw ht)

end RoughSamplingWeights
end
 
end

section
 

 

namespace ConstantCoefficientRationalization
open _root_.Polynomial _root_.OAI.Polynomial Finset Function
open scoped BigOperators fwdDiff
noncomputable section

lemma fwdDiff_cast (f : ℕ → ℤ) (k n : ℕ) :
    (Δ_[1] ^[k] (fun j => (f j : ℝ))) n = (Δ_[1] ^[k] f n : ℤ) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    simp only [fwdDiff, ih, Int.cast_sub]

lemma fwdDiff_eval_nat (P : ℝ[X]) (k n : ℕ) :
    (Δ_[1] ^[k] (fun j : ℕ => P.eval (j : ℝ))) n =
      (Δ_[1] ^[k] P.eval) (n : ℝ) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    simp only [fwdDiff, ih, Nat.cast_add, Nat.cast_one]

lemma fwdDiff_sub (f g : ℕ → ℝ) (k n : ℕ) :
    (Δ_[1] ^[k] (fun j => f j - g j)) n =
    (Δ_[1] ^[k] f) n - (Δ_[1] ^[k] g) n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply']
    simp only [fwdDiff, ih]
    ring

lemma fwdDiff_constant (a : ℝ) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (Δ_[1] ^[k] (fun _ : ℕ => a)) n = 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  clear hk
  rw [iterate_succ_apply]
  simp only [fwdDiff_const]
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply']
    simp only [fwdDiff, ih, sub_self]

lemma abs_fwdDiff_le (f : ℕ → ℝ) {ε : ℝ} (_hε : 0 ≤ ε) (k n : ℕ)
    (hf : ∀ j ≤ k, |f (n+j)| ≤ ε) :
    |(Δ_[1] ^[k] f) n| ≤ 2^k * ε := by
  induction k generalizing n with
  | zero => simpa using hf 0 (by omega)
  | succ k ih =>
    rw [iterate_succ_apply']
    change |(Δ_[1] ^[k] f) (n+1) - (Δ_[1] ^[k] f) n| ≤ _
    have hshift : ∀ j ≤ k, |f (n+1+j)| ≤ ε := by
      intro j hj
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hf (j+1) (by omega)
    calc
      _ ≤ |(Δ_[1] ^[k] f) (n+1)| + |(Δ_[1] ^[k] f) n| := abs_sub _ _
      _ ≤ 2^k*ε + 2^k*ε := add_le_add
        (ih (n+1) hshift)
        (ih n (fun j hj => hf j (by omega)))
      _ = _ := by rw [pow_succ]; ring

 
theorem floor_difference_zero (P : ℝ[X]) {q N : ℕ} (hP : P.natDegree ≤ q)
    {a ε : ℝ} (hε : 0 ≤ ε) (hsmall : 2^(q+1)*ε < 1)
    (hfrac : ∀ n ≤ N, |Int.fract (P.eval (n : ℝ)) - a| ≤ ε)
    {n : ℕ} (hn : n+q+1 ≤ N) :
    (Δ_[1] ^[q+1] (fun j : ℕ => ⌊P.eval (j : ℝ)⌋)) n = 0 := by
  let f : ℕ → ℤ := fun j => ⌊P.eval (j : ℝ)⌋
  let r : ℕ → ℝ := fun j => Int.fract (P.eval (j : ℝ)) - a
  have heq : (fun j : ℕ => (f j : ℝ)) = fun j : ℕ => P.eval (j : ℝ) - a - r j := by
    funext j
    dsimp [f,r]
    rw [Int.fract]
    ring
  have hz : (Δ_[1] ^[q+1] (fun j : ℕ => P.eval (j : ℝ))) n = 0 := by
    rw [fwdDiff_eval_nat]
    rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega : P.natDegree < q+1)]
    rfl
  have hb := abs_fwdDiff_le r hε (q+1) n (fun j hj => hfrac (n+j) (by omega))
  have hh : ((Δ_[1] ^[q+1] f n : ℤ) : ℝ) = -(Δ_[1] ^[q+1] r) n := by
    rw [← fwdDiff_cast, heq, fwdDiff_sub, fwdDiff_sub, hz,
      fwdDiff_constant a (by omega)]
    ring
  have hlt : |((Δ_[1] ^[q+1] f n : ℤ) : ℝ)| < 1 := by
    rw [hh, abs_neg]
    exact hb.trans_lt hsmall
  have hle : -1 < (Δ_[1] ^[q+1] f n : ℤ) ∧ (Δ_[1] ^[q+1] f n : ℤ) < 1 := by
    exact_mod_cast abs_lt.mp hlt
  change (Δ_[1] ^[q+1] f) n = 0
  omega

 

lemma higher_difference_zero (f : ℕ → ℤ) {k N : ℕ}
    (hf : ∀ n, n+k ≤ N → (Δ_[1] ^[k] f) n = 0)
    {j : ℕ} (hkj : k ≤ j) (hj : j ≤ N) :
    (Δ_[1] ^[j] f) 0 = 0 := by
  have hh : ∀ l n : ℕ, n+(k+l) ≤ N → (Δ_[1] ^[k+l] f) n = 0 := by
    intro l
    induction l with
    | zero => simpa using hf
    | succ l ih =>
      intro n hn
      rw [show k+(l+1) = (k+l)+1 by omega, iterate_succ_apply']
      change (Δ_[1] ^[k+l] f) (n+1) - (Δ_[1] ^[k+l] f) n = 0
      rw [ih (n+1) (by omega), ih n (by omega), sub_self]
  simpa [Nat.add_sub_of_le hkj] using hh (j-k) 0 (by omega)

 
def newtonPolynomial (q : ℕ) (f : ℕ → ℤ) : ℚ[X] :=
  ∑ k ∈ range (q+1),
    C (((Δ_[1] ^[k] f) 0 : ℤ) / (k.factorial : ℚ)) * descPochhammer ℚ k

lemma newtonPolynomial_eval (q : ℕ) (f : ℕ → ℤ) (n : ℕ) :
    (newtonPolynomial q f).eval (n : ℚ) =
      ∑ k ∈ range (q+1), (n.choose k : ℚ) * ((Δ_[1] ^[k] f) 0 : ℤ) := by
  simp only [newtonPolynomial, eval_finsetSum, eval_mul, eval_C]
  apply sum_congr rfl
  intro k hk
  rw [Nat.cast_choose_eq_descPochhammer_div]
  ring

lemma newtonPolynomial_degree (q : ℕ) (f : ℕ → ℤ) :
    (newtonPolynomial q f).natDegree ≤ q := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_le _ _).trans (by simpa using (show k ≤ q by
    have := mem_range.mp hk; omega))

 
theorem newtonPolynomial_agrees (f : ℕ → ℤ) {q N : ℕ}
    (hf : ∀ n, n+q+1 ≤ N → (Δ_[1] ^[q+1] f) n = 0)
    {n : ℕ} (hn : n ≤ N) :
    (newtonPolynomial q f).eval (n : ℚ) = (f n : ℚ) := by
  have hNewton := shift_eq_sum_fwdDiff_iter (1 : ℕ) f n 0
  simp only [nsmul_eq_mul, Nat.cast_id, mul_one, zero_add] at hNewton
  rw [newtonPolynomial_eval, hNewton]
  push_cast
  by_cases hnq : n ≤ q
  · symm
    apply sum_subset (range_mono (by omega : n+1 ≤ q+1))
    intro k hk hkn
    have hnk : n < k := by simp only [mem_range] at hkn; omega
    simp [Nat.choose_eq_zero_of_lt hnk]
  · apply sum_subset (range_mono (by omega : q+1 ≤ n+1))
    intro k hk hkq
    have hqk : q+1 ≤ k := by simp only [mem_range] at hkq; omega
    have hkN : k ≤ N := (Nat.le_of_lt_succ (mem_range.mp hk)).trans hn
    rw [higher_difference_zero f (fun a ha => hf a (by omega)) hqk hkN]
    simp

 

theorem newtonPolynomial_factorial_denominator (q : ℕ) (f : ℕ → ℤ) :
    C (q.factorial : ℚ) * newtonPolynomial q f ∈ lifts (algebraMap ℤ ℚ) := by
  rw [newtonPolynomial, mul_sum]
  apply (lifts (algebraMap ℤ ℚ)).sum_mem
  intro k hk
  have hkq : k ≤ q := by have := mem_range.mp hk; omega
  obtain ⟨l,hl⟩ := Nat.factorial_dvd_factorial hkq
  have heq : (q.factorial : ℚ) * (((Δ_[1] ^[k] f) 0 : ℤ) / (k.factorial : ℚ)) =
      (((l : ℤ)*((Δ_[1] ^[k] f) 0) : ℤ) : ℚ) := by
    rw [hl, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    have hne : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [← mul_assoc, ← C_mul, heq]
  apply base_mul_mem_lifts
  exact (mem_lifts _).mpr ⟨descPochhammer ℤ k, by simp⟩

 

theorem constant_coefficient_rationalization (P : ℝ[X]) {q N : ℕ}
    (hP : P.natDegree ≤ q) {a ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : 2^(q+1)*ε < 1)
    (hfrac : ∀ n ≤ N, |Int.fract (P.eval (n : ℝ))-a| ≤ ε) :
    ∃ M : ℚ[X], M.natDegree ≤ q ∧
      C (q.factorial : ℚ)*M ∈ lifts (algebraMap ℤ ℚ) ∧
      (∀ n ≤ N, M.eval (n : ℚ) = (⌊P.eval (n : ℝ)⌋ : ℤ)) ∧
      ∀ n ≤ N, 0 ≤ P.eval (n : ℝ)-(M.map (algebraMap ℚ ℝ)).eval (n : ℝ) ∧
        P.eval (n : ℝ)-(M.map (algebraMap ℚ ℝ)).eval (n : ℝ) < 1 := by
  let f : ℕ → ℤ := fun n => ⌊P.eval (n : ℝ)⌋
  let M := newtonPolynomial q f
  have heval (n : ℕ) (hn : n ≤ N) : M.eval (n : ℚ) = (f n : ℚ) :=
    newtonPolynomial_agrees f (fun n hn =>
      floor_difference_zero P hP hε hsmall hfrac hn) hn
  refine ⟨M, newtonPolynomial_degree q f,
    newtonPolynomial_factorial_denominator q f, heval, ?_⟩
  intro n hn
  have hc : (M.map (algebraMap ℚ ℝ)).eval (n : ℝ) = (f n : ℝ) := by
    have h := congrArg (algebraMap ℚ ℝ) (heval n hn)
    rw [eval_map]
    rw [show (n : ℝ) = algebraMap ℚ ℝ (n : ℚ) by simp]
    rw [eval₂_at_apply]
    simpa only [eq_ratCast, Rat.cast_intCast] using h
  rw [hc]
  exact ⟨sub_nonneg.mpr (Int.floor_le _), Int.fract_lt_one _⟩

 

theorem finite_van_der_waerden (r H : ℕ) :
    ∃ N : ℕ, ∀ χ : Fin (N+1) → Fin r,
      ∃ a b : ℕ, 0 < b ∧ ∃ hbound : a+b*H ≤ N,
        ∀ j : Fin (H+1), χ ⟨a+b*j.val, Nat.lt_succ_of_le
          ((Nat.add_le_add_left (Nat.mul_le_mul_left b
            (Nat.le_of_lt_succ j.isLt)) a).trans hbound)⟩ =
          χ ⟨a, Nat.lt_succ_of_le ((Nat.le_add_right _ _).trans hbound)⟩ := by
  classical
  let : TopologicalSpace (Fin r) := ⊥
  let : DiscreteTopology (Fin r) := ⟨rfl⟩
  let O := ℕ × {b : ℕ // 0 < b}
  let U (o : O) : Set (ℕ → Fin r) :=
    {χ | ∀ j : Fin (H+1), χ (o.1+o.2.val*j.val) = χ o.1}
  have hopen (o : O) : IsOpen (U o) := by
    rw [show U o = ⋂ j : Fin (H+1), {χ : ℕ → Fin r |
      χ (o.1+o.2.val*j.val) = χ o.1} by ext χ; simp [U]]
    apply isOpen_iInter_of_finite
    intro j
    change IsOpen ((fun χ : ℕ → Fin r => (χ (o.1+o.2.val*j.val), χ o.1)) ⁻¹'
      {z : Fin r × Fin r | z.1 = z.2})
    exact (isOpen_discrete {z : Fin r × Fin r | z.1 = z.2}).preimage
      ((continuous_apply (o.1+o.2.val*j.val)).prodMk (continuous_apply o.1))
  have hcover : (Set.univ : Set (ℕ → Fin r)) ⊆ ⋃ o, U o := by
    intro χ _
    obtain ⟨b,hb,a,c,hc⟩ := Combinatorics.exists_mono_homothetic_copy
      (range (H+1)) χ
    have ha : χ a = c := by simpa using hc 0 (mem_range.mpr (by omega))
    refine Set.mem_iUnion.mpr ⟨(a,⟨b,hb⟩),?_⟩
    intro j
    have hj := hc j.val (mem_range.mpr j.isLt)
    simpa [nsmul_eq_mul, Nat.add_comm, ha] using hj
  obtain ⟨T,hT⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  let N : ℕ := T.sup (fun o => o.1+o.2.val*H)
  refine ⟨N,?_⟩
  intro χ
  let c : ℕ → Fin r := fun n => if hn : n ≤ N then χ ⟨n,by omega⟩ else χ ⟨0,by omega⟩
  obtain ⟨o,ho,hco⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ c))
  have hbound : o.1+o.2.val*H ≤ N := le_sup (f := fun o : O => o.1+o.2.val*H) ho
  refine ⟨o.1,o.2.val,o.2.property,hbound,?_⟩
  intro j
  have ha : o.1 ≤ N := (Nat.le_add_right _ _).trans hbound
  have hj : o.1+o.2.val*j.val ≤ N :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ j.isLt)) _).trans hbound
  simpa only [c, dite_eq_left ha, dite_eq_left hj] using hco j

lemma fractional_cell_bound {K : ℕ} (hK : 0 < K) (x : ℝ) :
    |Int.fract x - (⌊(K : ℝ)*Int.fract x⌋₊ : ℝ)/(K : ℝ)| ≤ 1/(K : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have h0 : 0 ≤ (K : ℝ)*Int.fract x := mul_nonneg hKr.le (Int.fract_nonneg x)
  have hl := Nat.floor_le h0
  have hu := Nat.lt_floor_add_one ((K : ℝ)*Int.fract x)
  have hl' : (⌊(K : ℝ)*Int.fract x⌋₊ : ℝ)/(K : ℝ) ≤ Int.fract x :=
    (div_le_iff₀ hKr).mpr (by simpa [mul_comm] using hl)
  rw [abs_of_nonneg (sub_nonneg.mpr hl')]
  have hu' : Int.fract x < ((⌊(K : ℝ)*Int.fract x⌋₊ : ℝ)+1)/(K : ℝ) :=
    (lt_div_iff₀ hKr).mpr (by simpa [mul_comm] using hu)
  calc
    _ ≤ ((⌊(K : ℝ)*Int.fract x⌋₊ : ℝ)+1)/(K : ℝ)-
        (⌊(K : ℝ)*Int.fract x⌋₊ : ℝ)/(K : ℝ) := sub_le_sub_right hu'.le _
    _ = 1/(K : ℝ) := by ring

 

theorem constant_coefficient_after_thinning (q H : ℕ) :
    ∃ N : ℕ, ∀ P : ℝ[X], P.natDegree ≤ q →
      ∃ a b : ℕ, 0 < b ∧ b ≤ N ∧ a+b*H ≤ N ∧
        ∃ M : ℚ[X], M.natDegree ≤ q ∧
          C (q.factorial : ℚ)*M ∈ lifts (algebraMap ℤ ℚ) ∧
          ∀ n ≤ H, M.eval (n : ℚ) = (⌊P.eval ((a+b*n : ℕ) : ℝ)⌋ : ℤ) := by
  classical
  let K : ℕ := 2^(q+3)
  have hK : 0 < K := by dsimp [K]; positivity
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨N,hN⟩ := finite_van_der_waerden K (H+1)
  refine ⟨N,?_⟩
  intro P hP
  let χ : Fin (N+1) → Fin K := fun n =>
    ⟨⌊(K : ℝ)*Int.fract (P.eval (n.val : ℝ))⌋₊, (Nat.floor_lt
      (mul_nonneg hKr.le (Int.fract_nonneg _))).mpr (by
        simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one (P.eval (n.val : ℝ))) hKr)⟩
  obtain ⟨a,b,hb,hab,hm⟩ := hN χ
  have haN : a < N+1 := by omega
  let c : ℕ := (χ ⟨a,haN⟩).val
  let T : ℝ[X] := P.comp (C (a : ℝ)+C (b : ℝ)*X)
  have hT : T.natDegree ≤ q := by
    have hlin : (C (a : ℝ)+C (b : ℝ)*X).natDegree ≤ 1 :=
      natDegree_add_le_of_degree_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))
    exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ hlin).trans (by simpa using hP))
  have heval (n : ℕ) : T.eval (n : ℝ) = P.eval ((a+b*n : ℕ) : ℝ) := by
    simp [T, Nat.cast_add, Nat.cast_mul]
  have hfrac : ∀ n ≤ H, |Int.fract (T.eval (n : ℝ))-(c : ℝ)/(K : ℝ)| ≤ 1/(K : ℝ) := by
    intro n hn
    have hn' : n < H+1+1 := by omega
    have hh := congrArg Fin.val (hm ⟨n,hn'⟩)
    change ⌊(K : ℝ)*Int.fract (P.eval ((a+b*n : ℕ) : ℝ))⌋₊ = c at hh
    simpa only [heval, hh] using fractional_cell_bound hK (P.eval ((a+b*n : ℕ) : ℝ))
  have hsmall : (2 : ℝ)^(q+1)*(1/(K : ℝ)) < 1 := by
    rw [mul_one_div, div_lt_one hKr]
    dsimp [K]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  obtain ⟨M,hM,hden,heq,_⟩ := constant_coefficient_rationalization T hT
    (by positivity : (0 : ℝ) ≤ 1/(K : ℝ)) hsmall hfrac
  refine ⟨a,b,hb,?_,?_,M,hM,hden,?_⟩
  · nlinarith
  · nlinarith
  · intro n hn
    simpa only [heval] using heq n hn

end
end ConstantCoefficientRationalization
 

end
end
end

end OAI
