import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.DenseRough01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
open _root_.Polynomial _root_.OAI.Polynomial Finset
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial Filter
open scoped Topology
namespace CoefficientPeeling
open scoped BigOperators
open Finset _root_.Polynomial _root_.OAI.Polynomial
noncomputable section

 
def NearInteger (x ε : ℝ) : Prop := ∃ n : ℤ, |x-(n : ℝ)| ≤ ε

lemma NearInteger.mul_nat {x ε : ℝ} (h : NearInteger x ε) (t : ℕ) :
    NearInteger ((t : ℝ)*x) ((t : ℝ)*ε) := by
  obtain ⟨n,hn⟩ := h
  refine ⟨(t : ℤ)*n, ?_⟩
  simpa only [Int.cast_mul, Int.cast_natCast, ← mul_sub, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) t)] using
      (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg t))

lemma NearInteger.mono {x ε ε' : ℝ} (h : NearInteger x ε) (hh : ε ≤ ε') :
    NearInteger x ε' := by
  obtain ⟨n,hn⟩ := h
  exact ⟨n,hn.trans hh⟩

 

lemma tail_term_bound {e j : ℕ} (hej : e ≤ j) {p Z A C x : ℝ}
    (hp : 0 ≤ p) (hZ : 0 < Z) (hpZ : p ≤ Z) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hx : |x| *Z^j ≤ A) {b : ℝ} (hb : |b| ≤ C*p^(j-e)) :
    |p^e*b*x| ≤ C*A*(p/Z)^e := by
  have hpow : p^(j-e) ≤ Z^(j-e) := pow_le_pow_left₀ hp hpZ _
  calc
    |p^e*b*x| = p^e*|b| *|x| := by rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hp _)]
    _ ≤ p^e*(C*p^(j-e))*(A/Z^j) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hb (pow_nonneg hp _)
      · exact (le_div_iff₀ (pow_pos hZ _)).mpr hx
      · exact abs_nonneg _
      · positivity
    _ ≤ p^e*(C*Z^(j-e))*(A/Z^j) := by gcongr
    _ = C*A*(p/Z)^e := by
      rw [div_pow]
      have hz : Z^j = Z^e*Z^(j-e) := by rw [← pow_add, Nat.add_sub_of_le hej]
      rw [hz]
      field_simp

 

theorem peel {ι : Type*} [DecidableEq ι] (s : Finset ι) (degree : ι → ℕ)
    (e : ℕ) (he : ∀ j ∈ s, e ≤ degree j) (p : ℕ) {Z A A₀ : ℝ}
    (hZ : 0 < Z) (hpZ : (p : ℝ) ≤ Z) (hA : 0 ≤ A)
    (θ : ℝ) (θj : ι → ℝ) (m : ι → ℤ) (c : ι → ℤ) (C : ι → ℝ)
    (hC : ∀ j ∈ s, 0 ≤ C j)
    (hc : ∀ j ∈ s, |(c j : ℝ)| ≤ C j*(p : ℝ)^(degree j-e))
    (hθ : ∀ j ∈ s, |θj j-(m j : ℝ)| *Z^(degree j) ≤ A)
    (ho : NearInteger ((p : ℝ)^e*(θ+∑ j ∈ s, (c j : ℝ)*θj j))
      (A₀*((p : ℝ)/Z)^e)) :
    NearInteger ((p : ℝ)^e*θ) ((A₀+(∑ j ∈ s, C j)*A)*((p : ℝ)/Z)^e) := by
  obtain ⟨n,hn⟩ := ho
  refine ⟨n-(p : ℤ)^e*∑ j ∈ s, c j*m j, ?_⟩
  have htail : |∑ j ∈ s, (p : ℝ)^e*(c j : ℝ)*(θj j-(m j : ℝ))| ≤
      ((∑ j ∈ s, C j)*A)*((p : ℝ)/Z)^e := by
    calc
      _ ≤ ∑ j ∈ s, |(p : ℝ)^e*(c j : ℝ)*(θj j-(m j : ℝ))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, C j*A*((p : ℝ)/Z)^e := sum_le_sum fun j hj =>
        tail_term_bound (he j hj) (Nat.cast_nonneg p) hZ hpZ hA (hC j hj)
          (hθ j hj) (hc j hj)
      _ = _ := by simp only [← sum_mul]
  have hid : (p : ℝ)^e*θ -
      ((n-(p : ℤ)^e*∑ j ∈ s, c j*m j : ℤ) : ℝ) =
      ((p : ℝ)^e*(θ+∑ j ∈ s, (c j : ℝ)*θj j)-(n : ℝ)) -
        ∑ j ∈ s, (p : ℝ)^e*(c j : ℝ)*(θj j-(m j : ℝ)) := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_sum, mul_sub, sum_sub_distrib, mul_assoc, ← mul_sum]
    ring
  rw [hid]
  exact (abs_sub _ _).trans (by nlinarith [hn, htail])

 

theorem unit_or_rough {t p e : ℕ} {θ A Z : ℝ} (_hZ : Z ≠ 0)
    (hp : p = 1 ∨ p = t)
    (ho : NearInteger ((p : ℝ)^e*θ) (A*((p : ℝ)/Z)^e)) :
    NearInteger ((t : ℝ)^e*θ) (A*((t : ℝ)/Z)^e) := by
  rcases hp with rfl | rfl
  · have h := ho.mul_nat (t^e)
    simp only [Nat.cast_one, one_pow, one_mul, Nat.cast_pow] at h
    convert h using 1
    rw [div_pow, one_div_pow]
    ring
  · exact ho

 
lemma affine_coefficient (f : ℝ[X]) (b p : ℤ) (e : ℕ) :
    (f.comp (Polynomial.C (p : ℝ)*Polynomial.X+Polynomial.C (b : ℝ))).coeff e =
      (p : ℝ)^e * ∑ j ∈ f.support, (j.choose e : ℝ)*f.coeff j*(b : ℝ)^(j-e) := by
  have hid : f.comp (Polynomial.C (p : ℝ)*Polynomial.X+Polynomial.C (b : ℝ)) =
      (Polynomial.taylor (b : ℝ) f).comp (Polynomial.C (p : ℝ)*Polynomial.X) := by
    rw [Polynomial.taylor_apply, Polynomial.comp_assoc]
    simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
  rw [hid, Polynomial.comp_C_mul_X_coeff, Polynomial.taylor_coeff,
    Polynomial.hasseDeriv_apply, Polynomial.eval_sum, Polynomial.sum_def]
  simp only [Polynomial.eval_monomial]
  exact mul_comm _ _

end
end CoefficientPeeling

namespace PositiveCoefficientDescent
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial Finset Filter RoughInterpolation RoughScales DenseRoughInterpolation
open DenseRoughScaleCompletion CoefficientPeeling
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 

structure Input (degree : ι → ℕ) (N q w : ℕ) (S Z α A₀ C₀ : ℝ) where
  E : Finset ℤ
  in_interval : ∀ z ∈ E, 0 ≤ z ∧ z ≤ N
  enough_nodes : 2*(q+1) ≤ E.card
  dense : α*N ≤ E.card
  a : ℤ
  b : ℤ
  positive_step : 0 < b
  smooth_step : Smooth w b
  scale : ∀ z : ℤ, 0 ≤ z → z ≤ N → S ≤ (a+b*z : ℤ) ∧
    ((a+b*z : ℤ) : ℝ) < 2*S
  rough : ∀ z ∈ E, Rough w (a+b*z)
  θ : ι → ℝ[X]
  polynomial_degree : ∀ i, ((Polynomial.C (a : ℝ)+Polynomial.C (b : ℝ)*X)^degree i*θ i).natDegree ≤ q
  p : ℤ → ℕ
  steps : ∀ z ∈ E, p z = 1 ∨ p z = (a+b*z).natAbs
  c : ι → ι → ℤ → ℤ
  residue_bound : ∀ i j z, z ∈ E → degree i < degree j →
    |(c i j z : ℝ)| ≤ C₀*(p z : ℝ)^(degree j-degree i)
  obstruction : ∀ i z, z ∈ E → NearInteger
    ((p z : ℝ)^degree i * ((θ i).eval (z : ℝ)+
      ∑ j ∈ univ.filter (fun j => degree i < degree j), (c i j z : ℝ)*(θ j).eval (z : ℝ)))
    (A₀*((p z : ℝ)/Z)^degree i)

 
def Controlled (q w e : ℕ) (N : ℕ) (E : Finset ℤ) (Z B : ℝ) (θ : ℝ[X]) (M : ℚ[X]) : Prop :=
  M.natDegree ≤ q-e ∧
  (∀ j p : ℕ, p.Prime → p ∣ (M.coeff j).den → p ≤ w) ∧
  (∀ z ∈ E, Integral (M.eval (z : ℚ))) ∧
  ∀ z : ℤ, 0 ≤ z → z ≤ N →
    |θ.eval (z : ℝ)-(M.map (algebraMap ℚ ℝ)).eval (z : ℝ)| *Z^e ≤ B

lemma Controlled.mono {q w e N : ℕ} {E : Finset ℤ} {Z B B' : ℝ}
    {θ : ℝ[X]} {M : ℚ[X]} (h : Controlled q w e N E Z B θ M) (hB : B ≤ B') :
    Controlled q w e N E Z B' θ M :=
  ⟨h.1,h.2.1,h.2.2.1,fun z hz hzN => (h.2.2.2 z hz hzN).trans hB⟩

omit [DecidableEq ι] in
lemma step_cast {degree : ι → ℕ} {N q w : ℕ} {S Z α A₀ C₀ : ℝ}
    (d : Input degree N q w S Z α A₀ C₀) (hS : 0 ≤ S)
    {z : ℤ} (hz : z ∈ d.E) :
    ((d.a+d.b*z).natAbs : ℝ) = ((d.a+d.b*z : ℤ) : ℝ) := by
  have h := (d.scale z (d.in_interval z hz).1 (d.in_interval z hz).2).1
  have ht : (0 : ℝ) ≤ ((d.a+d.b*z : ℤ) : ℝ) := hS.trans h
  simp only [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg ht]

omit [DecidableEq ι] in
lemma sample_le {degree : ι → ℕ} {N q w : ℕ} {S Z α A₀ C₀ : ℝ}
    (d : Input degree N q w S Z α A₀ C₀) (hS : 1 ≤ S) (hSZ : 2*S ≤ Z)
    {z : ℤ} (hz : z ∈ d.E) : (d.p z : ℝ) ≤ Z := by
  rcases d.steps z hz with hp | hp
  · rw [hp, Nat.cast_one]; linarith
  · rw [hp, step_cast d (by linarith) hz]
    exact ((d.scale z (d.in_interval z hz).1 (d.in_interval z hz).2).2.le).trans hSZ

 

theorem eventual_rational_coefficients (degree : ι → ℕ) (D q : ℕ)
    (hdeg : ∀ i, 1 ≤ degree i ∧ degree i ≤ D) (hDq : D ≤ q)
    {α A₀ C₀ : ℝ} (hα : 0 < α) (hA₀ : 0 < A₀) (hC₀ : 0 ≤ C₀)
    {w : ℕ → ℕ} {S Z : ℕ → ℝ}
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ, Tendsto (fun n => Z n/S n^k) atTop atTop) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ N : ℕ, 0 < N →
      ∀ᶠ n in atTop, ∀ d : Input degree N q (w n) (S n) (Z n) α A₀ C₀,
        ∃ M : ι → ℚ[X], ∀ i, Controlled q (w n) (degree i) N d.E (Z n) B (d.θ i) (M i) := by
  let K := uniformBound q α
  have hK : 0 ≤ K := by dsimp [K, uniformBound]; positivity
  let J : ℝ := (Fintype.card ι : ℝ)*C₀
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  let β : ℝ := max 1 (K*2^D*(A₀+J))
  have hβ : 1 ≤ β := le_max_left _ _
  have hβ₀ : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hβK : K*2^D*(A₀+J) ≤ β := le_max_right _ _
  have hconst (k : ℕ) : 0 < 2^D*(A₀+J*β^k) := by positivity
  have hbound (k : ℕ) : K*(2^D*(A₀+J*β^k)) ≤ β^(k+1) := by
    have hb1 : 1 ≤ β^k := one_le_pow₀ hβ
    have hAA : A₀+J*β^k ≤ (A₀+J)*β^k := by nlinarith
    calc
      _ ≤ (K*2^D*(A₀+J))*β^k := by nlinarith [mul_le_mul_of_nonneg_left hAA (show 0 ≤ K*2^D by positivity)]
      _ ≤ β*β^k := mul_le_mul_of_nonneg_right hβK (by positivity)
      _ = _ := by rw [pow_succ]; ring
  refine ⟨β^D, one_le_pow₀ hβ, ?_⟩
  intro N hN
  have hscale : ∀ᶠ n in atTop, 1 ≤ S n ∧ 0 < Z n ∧ 2*S n ≤ Z n := by
    filter_upwards [hS.eventually (eventually_ge_atTop (1 : ℝ)),
      (hZ 1).eventually (eventually_ge_atTop (2 : ℝ))] with n hnS hnZ
    have hs : 0 < S n := by linarith
    simp only [pow_one] at hnZ
    have hh : 2*S n ≤ Z n := (le_div_iff₀ hs).mp hnZ
    exact ⟨hnS,by linarith,hh⟩
  have hstage (k : ℕ) (hk : k ≤ D) :
      ∀ᶠ n in atTop, ∀ d : Input degree N q (w n) (S n) (Z n) α A₀ C₀,
        ∃ M : ι → ℚ[X], ∀ i, D-k < degree i →
          Controlled q (w n) (degree i) N d.E (Z n) (β^k) (d.θ i) (M i) := by
    induction k with
    | zero =>
      exact Filter.Eventually.of_forall fun n d => ⟨fun _ => 0, fun i hi => by
        have := (hdeg i).2; omega⟩
    | succ k ih =>
      have hkD : k < D := by omega
      have he : 1 ≤ D-k := by omega
      have heq : D-k ≤ q := by omega
      have hprev := ih (by omega)
      have hex := DenseRoughScaleCompletion.eventually_exact_division he heq hN hα
        (hconst k) hw hS hZ
      filter_upwards [hprev,hex,hscale] with n hnprev hnex hnscale
      intro d
      have hnS : 1 ≤ S n := hnscale.1
      have hnZ : 0 < Z n := hnscale.2.1
      obtain ⟨M, hM⟩ := hnprev d
      have hlocal (i : ι) : ∃ M' : ℚ[X], D-(k+1) < degree i →
          Controlled q (w n) (degree i) N d.E (Z n) (β^(k+1)) (d.θ i) M' := by
        by_cases hhi : D-k < degree i
        · refine ⟨M i, fun _ => (hM i hhi).mono ?_⟩
          exact pow_le_pow_right₀ hβ (by omega)
        by_cases hnew : D-(k+1) < degree i
        · have hei : degree i = D-k := by omega
          let T : Finset ι := univ.filter (fun j => degree i < degree j)
          have hT (j : ι) (hj : j ∈ T) : D-k < degree j := by
            have := (mem_filter.mp hj).2
            omega
          have hnear (z : ℤ) (hz : z ∈ d.E) : ∃ v : ℤ,
              |(((Polynomial.C (d.a : ℝ)+Polynomial.C (d.b : ℝ)*X)^(D-k)*d.θ i).eval (z : ℝ))-(v : ℝ)| ≤
                (2^D*(A₀+J*β^k))*(S n/Z n)^(D-k) := by
            have him (j : ι) : ∃ v : ℤ, j ∈ T →
                (v : ℚ) = (M j).eval (z : ℚ) := by
              by_cases hj : j ∈ T
              · obtain ⟨v,hv⟩ := (hM j (hT j hj)).2.2.1 z hz
                exact ⟨v, fun _ => hv⟩
              · exact ⟨0, fun h => (hj h).elim⟩
            choose m hm using him
            have herr (j : ι) (hj : j ∈ T) :
                |(d.θ j).eval (z : ℝ)-(m j : ℝ)| * Z n^degree j ≤ β^k := by
              have hcast : (m j : ℝ) = ((M j).map (algebraMap ℚ ℝ)).eval (z : ℝ) := by
                have hv := congrArg (algebraMap ℚ ℝ) (hm j hj)
                have heval : ((M j).map (algebraMap ℚ ℝ)).eval (z : ℝ) =
                    (((M j).eval (z : ℚ) : ℚ) : ℝ) := by
                  rw [eval_map]
                  simpa only [eq_ratCast, Rat.cast_intCast] using
                    (eval₂_at_apply (p := M j) (algebraMap ℚ ℝ) (z : ℚ))
                rw [heval]
                simpa only [eq_ratCast, Rat.cast_intCast] using hv
              rw [hcast]
              exact (hM j (hT j hj)).2.2.2 z (d.in_interval z hz).1 (d.in_interval z hz).2
            have hp := peel T degree (degree i) (fun j hj =>
                (mem_filter.mp hj).2.le) (d.p z) hnscale.2.1
              (sample_le d hnscale.1 hnscale.2.2 hz) (by positivity : 0 ≤ β^k)
              ((d.θ i).eval (z : ℝ)) (fun j => (d.θ j).eval (z : ℝ)) m
              (fun j => d.c i j z) (fun _ => C₀) (fun _ _ => hC₀)
              (fun j hj => d.residue_bound i j z hz (mem_filter.mp hj).2) herr (d.obstruction i z hz)
            have hTJ : (∑ j ∈ T, C₀) ≤ J := by
              simp only [sum_const, nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (T.card_le_univ)) hC₀
            have hp' := hp.mono (show
                (A₀+(∑ j ∈ T, C₀)*β^k)*((d.p z : ℝ)/Z n)^degree i ≤
                (A₀+J*β^k)*((d.p z : ℝ)/Z n)^degree i by gcongr)
            have ht := unit_or_rough (ne_of_gt hnscale.2.1) (d.steps z hz) hp'
            have hstep := step_cast d (by linarith [hnscale.1]) hz
            have hscalez := d.scale z (d.in_interval z hz).1 (d.in_interval z hz).2
            have hpowe : (((d.a+d.b*z).natAbs : ℝ)/Z n)^degree i ≤
                2^D*(S n/Z n)^degree i := by
              calc
                _ ≤ (2*S n/Z n)^degree i := by
                  apply pow_le_pow_left₀ (by positivity)
                  exact div_le_div_of_nonneg_right (by rw [hstep]; exact hscalez.2.le) (le_of_lt hnscale.2.1)
                _ = 2^degree i*(S n/Z n)^degree i := by rw [mul_div_assoc, mul_pow]
                _ ≤ _ := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact pow_le_pow_right₀ (by norm_num) (hdeg i).2
            have ht' := ht.mono (show
                (A₀+J*β^k)*(((d.a+d.b*z).natAbs : ℝ)/Z n)^degree i ≤
                (2^D*(A₀+J*β^k))*(S n/Z n)^degree i by
                  nlinarith [mul_le_mul_of_nonneg_left hpowe (show 0 ≤ A₀+J*β^k by positivity)])
            obtain ⟨v,hv⟩ := ht'
            refine ⟨v, ?_⟩
            simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
              Polynomial.eval_C, Polynomial.eval_X, hstep, Int.cast_add, Int.cast_mul, hei] using hv
          obtain ⟨M',hM'deg,hM'sm,hM'int,hM'err⟩ := hnex d.E d.in_interval d.enough_nodes d.dense
            d.a d.b (d.θ i) d.positive_step d.smooth_step d.scale d.rough
            (by simpa only [hei] using d.polynomial_degree i) hnear
          refine ⟨M',fun _ => ?_⟩
          refine ⟨by simpa only [hei] using hM'deg,hM'sm,hM'int,?_⟩
          intro z hz hzN
          have hh := (mul_le_mul_of_nonneg_right (hM'err z hz hzN)
            (show 0 ≤ Z n^(D-k) by positivity)).trans_eq
            (show (uniformBound q α * (2^D*(A₀+J*β^k))/Z n^(D-k))*Z n^(D-k) =
              K*(2^D*(A₀+J*β^k)) by dsimp only [K]; field_simp [ne_of_gt hnZ])
          simpa only [hei] using hh.trans (hbound k)
        · exact ⟨0, fun h => (hnew h).elim⟩
      choose M' hM' using hlocal
      exact ⟨M',hM'⟩
  filter_upwards [hstage D le_rfl] with n hn
  intro d
  obtain ⟨M,hM⟩ := hn d
  exact ⟨M,fun i => hM i (by have := (hdeg i).1; omega)⟩

end
end PositiveCoefficientDescent

end
end
end

end OAI
