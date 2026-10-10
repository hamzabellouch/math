import Mathlib

namespace OAI

/-! Common arithmetic parameter choices and their coprime indices. -/

namespace AmbientMultiplicity.Parameters
noncomputable section

def nextN (r n₀ : ℕ) : ℕ := n₀ + 5*2^r
def exponent (n : ℕ) : ℕ := (n^2-1)/4
def alpha (a b : ℕ) : ℝ := 4*(b:ℝ)/((a:ℝ)+b)
def beta (a b : ℕ) : ℝ := 4*(a:ℝ)/((a:ℝ)+b)
def Choice (r n₀ : ℕ) : Prop :=
  Nat.ModEq (2^r) n₀ 1 ∧ Nat.ModEq 5 n₀ 2 ∧ 5*2^r < n₀
 

def CommonConditions (r n₀ : ℕ) : Prop :=
  let n₁ := nextN r n₀
  let a := exponent n₀
  let b := exponent n₁
  Choice r n₀ ∧ Nat.ModEq 4 n₀ 1 ∧ Nat.ModEq 4 n₁ 1 ∧
  n₀ < n₁ ∧ n₁ < 2*n₀ ∧ Nat.Coprime n₀ n₁ ∧
  4*a+1=n₀^2 ∧ 4*b+1=n₁^2 ∧ 11 ≤ a ∧ a < b ∧ b < 5*a ∧
  alpha a b + beta a b = 4 ∧ (a:ℝ)*alpha a b = (b:ℝ)*beta a b ∧
  4 < ((a:ℝ)-2)*alpha a b/4 ∧ 4 < ((b:ℝ)-2)*beta a b/4

lemma choice_exists (r : ℕ) : ∃ n₀, Choice r n₀ := by
  let k := Nat.chineseRemainder ((by norm_num : Nat.Coprime 2 5).pow_left r) 1 2
  refine ⟨k.val + 5*2^r*(k.val+1), ?_⟩
  have hk : 2 ≤ k.val := by
    have hh := k.property.2
    change k.val % 5 = 2 % 5 at hh
    omega
  refine ⟨?_,?_,?_⟩
  · simpa [Nat.ModEq,Nat.add_mod,Nat.mul_mod, mul_assoc] using k.property.1
  · simpa [Nat.ModEq,Nat.add_mod,Nat.mul_mod, mul_assoc] using k.property.2
  · have hp : 0 < 5*2^r := by positivity
    nlinarith

lemma exact_exponent (n : ℕ) (h4 : Nat.ModEq 4 n 1) :
    4*exponent n + 1 = n^2 := by
  have hn : n % 4 = 1 := h4
  have he : n^2 % 4 = 1 := by simp [Nat.pow_mod,hn]
  unfold exponent
  omega

lemma choice_common (r n₀ : ℕ) (hr : 4 ≤ r) (hc : Choice r n₀) :
    CommonConditions r n₀ := by
  have hp : 16 ≤ 2^r := by simpa using Nat.pow_le_pow_right (n := 2) (by omega) hr
  have hd : 4 ∣ 2^r := by
    simpa using (pow_dvd_pow (2:ℕ) (show 2 ≤ r by omega))
  have h04 : Nat.ModEq 4 n₀ 1 := hc.1.of_dvd hd
  have hn : 80 < n₀ := by have := hc.2.2; nlinarith
  have h14 : Nat.ModEq 4 (nextN r n₀) 1 := by
    dsimp [nextN]
    have hm : 5*2^r % 4 = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hd _)
    simpa [Nat.ModEq,Nat.add_mod,hm] using h04
  have hnp : n₀ < nextN r n₀ := by
    dsimp [nextN]
    have : 0 < 2^r := by positivity
    omega
  have hnlt : nextN r n₀ < 2*n₀ := by dsimp [nextN]; have := hc.2.2; omega
  have hcp : Nat.Coprime n₀ (2^r) :=
    Nat.coprime_of_mul_modEq_one 1 (by simpa using hc.1)
  have hc5 : Nat.Coprime n₀ 5 := by
    apply Nat.coprime_of_mul_modEq_one 3
    have h := hc.2.1.mul_right 3
    simpa [Nat.ModEq] using h
  have hcop : Nat.Coprime n₀ (nextN r n₀) := by
    dsimp [nextN]
    rw [Nat.add_comm, Nat.coprime_add_self_right]
    exact hc5.mul_right hcp
  have ea := exact_exponent n₀ h04
  have eb := exact_exponent (nextN r n₀) h14
  have ha : 11 ≤ exponent n₀ := by nlinarith
  have hab : exponent n₀ < exponent (nextN r n₀) := by nlinarith
  have hb : exponent (nextN r n₀) < 5*exponent n₀ := by nlinarith
  refine ⟨hc,h04,h14,hnp,hnlt,hcop,ea,eb,ha,hab,hb,?_,?_,?_,?_⟩
  all_goals
    let a := exponent n₀
    let b := exponent (nextN r n₀)
    have haR : 11 ≤ (a:ℝ) := by exact_mod_cast ha
    have habR : (a:ℝ) < b := by exact_mod_cast hab
    have hpos : 0 < (a:ℝ)+(b:ℝ) := by positivity
    have hne : (a:ℝ)+(b:ℝ) ≠ 0 := ne_of_gt hpos
  · change alpha a b + beta a b = 4
    unfold alpha beta
    field_simp
    ring
  · change (a:ℝ)*alpha a b = (b:ℝ)*beta a b
    unfold alpha beta
    ring
  · change 4 < ((a:ℝ)-2)*alpha a b/4
    have he : ((a:ℝ)-2)*alpha a b/4 = ((a:ℝ)-2)*(b:ℝ)/((a:ℝ)+b) := by
      unfold alpha
      ring
    rw [he,lt_div_iff₀ hpos]
    have hh := mul_nonneg (sub_nonneg.mpr haR) (show 0 ≤ (b:ℝ) by positivity)
    nlinarith
  · change 4 < ((b:ℝ)-2)*beta a b/4
    have he : ((b:ℝ)-2)*beta a b/4 = ((b:ℝ)-2)*(a:ℝ)/((a:ℝ)+b) := by
      unfold beta
      ring
    rw [he,lt_div_iff₀ hpos]
    have hh := mul_nonneg (sub_nonneg.mpr haR) (show 0 ≤ (b:ℝ) by positivity)
    nlinarith

 
theorem common_parameters_reference (r : ℕ) (hr : 4 ≤ r) :
    ∃ n₀ : ℕ, CommonConditions r n₀ := by
  obtain ⟨n₀,hc⟩ := choice_exists r
  exact ⟨n₀,choice_common r n₀ hr hc⟩


 

def IndexConditions (r n₀ : ℕ) : Prop :=
  let a := exponent n₀
  let b := exponent (nextN r n₀)
  let g := Nat.gcd a b
  let m := 4*a*b+a+b
  Nat.ModEq 5 a 2 ∧ Nat.ModEq 5 b 2 ∧ ¬ 5 ∣ g ∧
  2^(r-1) ≤ g ∧ 5 < 2^(r-1) ∧
  ∀ q : ℕ, q=1 ∨ q=4 → ∃ i j : ℕ,
    0 < i ∧ 0 < j ∧ Nat.ModEq 4 i j ∧ 5*(b*i+a*j)=q*m

lemma exponent_mod_five (n : ℕ) (h4 : Nat.ModEq 4 n 1) (h5 : Nat.ModEq 5 n 2) :
    Nat.ModEq 5 (exponent n) 2 := by
  have he := congrArg (fun x : ℕ => x % 5) (exact_exponent n h4)
  have hn : n % 5 = 2 := h5
  simp [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hn] at he
  change exponent n % 5 = 2
  omega

lemma exponent_two_power (r n : ℕ) (hr : 2 ≤ r) (hn : Nat.ModEq (2^r) n 1) :
    2^(r-1) ∣ exponent n := by
  have hd : 4 ∣ 2^r := by simpa using (pow_dvd_pow (2:ℕ) hr)
  have hh := exact_exponent n (hn.of_dvd hd)
  have hx : 4*(exponent n:ℤ)+1=(n:ℤ)^2 := by exact_mod_cast hh
  have hpow : (2:ℤ)^r = 2*(2:ℤ)^(r-1) := by
    calc
      _ = (2:ℤ)^((r-1)+1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
      _ = _ := by rw [pow_succ]; ring
  have hdiv := hn.dvd
  push_cast at hdiv
  rcases hdiv with ⟨k,hk⟩
  rw [hpow] at hk
  apply Int.natCast_dvd_natCast.mp
  push_cast
  refine ⟨-k*(1-(2:ℤ)^(r-1)*k), ?_⟩
  have he : (n:ℤ)=1-2*(2:ℤ)^(r-1)*k := by linarith
  rw [he] at hx
  nlinarith only [hx]

 

private lemma bounded_bezout (A B D N : ℤ) (hB : 0 < B) (hD : 0 < D)
    (hDA : D ∣ A) (hDB : D ∣ B) (hDN : D ∣ N)
    (hbez : ∃ u v : ℤ, A*u+B*v=D) :
    ∃ j t : ℤ, 0 < j ∧ D*j ≤ B ∧ A*j+B*t=N := by
  obtain ⟨u,v,hbez⟩ := hbez
  let K := B/D
  have hK : 0 < K := Int.ediv_pos_of_pos_of_dvd hB hD.le hDB
  have eB : D*K=B := Int.mul_ediv_cancel' hDB
  have eA : D*(A/D)=A := Int.mul_ediv_cancel' hDA
  have eN : D*(N/D)=N := Int.mul_ediv_cancel' hDN
  let j₀ := u*(N/D)
  let t₀ := v*(N/D)
  have e₀ : A*j₀+B*t₀=N := by
    dsimp [j₀,t₀]
    calc
      _ = (A*u+B*v)*(N/D) := by ring
      _ = N := by rw [hbez,eN]
  let k := (j₀-1)/K
  let j := (j₀-1)%K+1
  have hj : 0 < j := by
    have := Int.emod_nonneg (j₀-1) (ne_of_gt hK)
    dsimp [j]
    omega
  have hjK : j ≤ K := by
    have := Int.emod_lt_of_pos (j₀-1) hK
    dsimp [j]
    omega
  have ej : j+K*k=j₀ := by
    have := Int.emod_add_mul_ediv (j₀-1) K
    dsimp [j,k]
    linarith
  refine ⟨j,t₀+(A/D)*k,hj,?_,?_⟩
  · calc
      D*j ≤ D*K := mul_le_mul_of_nonneg_left hjK hD.le
      _ = B := eB
  · have ek : A*K=B*(A/D) := by
      calc
        A*K = (D*(A/D))*K := by rw [eA]
        _ = (D*K)*(A/D) := by ring
        _ = B*(A/D) := by rw [eB]
    calc
      A*j+B*(t₀+(A/D)*k) = A*(j+K*k)+B*t₀ := by linear_combination -k*ek
      _ = N := by rw [ej,e₀]

lemma positive_indices (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ha5 : Nat.ModEq 5 a 2) (hb5 : Nat.ModEq 5 b 2)
    (hg : 5 < Nat.gcd a b) (q : ℕ) (hq : 0 < q) :
    ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ Nat.ModEq 4 i j ∧
      5*(b*i+a*j)=q*(4*a*b+a+b) := by
  let A := a+b
  let B := 4*b
  let D := Nat.gcd A B
  let m := 4*a*b+a+b
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := Nat.gcd_pos_of_pos_right _ hB
  have hdA : D ∣ A := Nat.gcd_dvd_left _ _
  have hdB : D ∣ B := Nat.gcd_dvd_right _ _
  have hgD : Nat.gcd a b ∣ D := by
    exact Nat.dvd_gcd (dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 4)
  have hD5 : 5 < D := lt_of_lt_of_le hg (Nat.le_of_dvd hD hgD)
  have ha5' : a%5=2 := ha5
  have hb5' : b%5=2 := hb5
  have hA5 : Nat.Coprime A 5 := by
    apply Nat.coprime_of_mul_modEq_one 4
    dsimp [A]
    norm_num [Nat.ModEq,Nat.add_mod,Nat.mul_mod,ha5',hb5']
  have hDc : Nat.Coprime D 5 := hA5.of_dvd_left hdA
  have hm5 : 5 ∣ m := by
    apply Nat.dvd_of_mod_eq_zero
    dsimp [m]
    norm_num [Nat.add_mod,Nat.mul_mod,ha5',hb5']
  have hdm : D ∣ m := by
    have hm : D ∣ a*B := dvd_mul_of_dvd_right hdB a
    have hh := dvd_add hm hdA
    simpa [m,A,B,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc,Nat.add_assoc] using hh
  have e5 : 5*(m/5)=m := Nat.mul_div_cancel' hm5
  have hd5 : D ∣ m/5 := hDc.dvd_of_dvd_mul_left (by simpa [e5] using hdm)
  let N := q*(m/5)
  have hdN : D ∣ N := dvd_mul_of_dvd_right hd5 q
  have eN : 5*N=q*m := by
    dsimp [N]
    calc
      _ = q*(5*(m/5)) := by ring
      _ = q*m := by rw [e5]
  have hbez : ∃ u v : ℤ, (A:ℤ)*u+(B:ℤ)*v=(D:ℤ) := by
    exact ⟨Nat.gcdA A B,Nat.gcdB A B,(Nat.gcd_eq_gcd_ab A B).symm⟩
  obtain ⟨j,t,hj,hDj,he⟩ := bounded_bezout A B D N (by exact_mod_cast hB)
    (by exact_mod_cast hD) (by exact_mod_cast hdA) (by exact_mod_cast hdB)
    (by exact_mod_cast hdN) hbez
  let i : ℤ := j+4*t
  have haI : 0 < (a:ℤ) := by exact_mod_cast ha
  have hbI : 0 < (b:ℤ) := by exact_mod_cast hb
  have hDI : 5 < (D:ℤ) := by exact_mod_cast hD5
  have hqI : 1 ≤ (q:ℤ) := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hmI : 0 < (m:ℤ) := by dsimp [m]; positivity
  have eNI : 5*(N:ℤ)=(q:ℤ)*m := by exact_mod_cast eN
  have hN5 : (m:ℤ) ≤ 5*N := by
    rw [eNI]
    exact le_mul_of_one_le_left hmI.le hqI
  have hNI : 0 < (N:ℤ) := by omega
  have hbig : 4*(a:ℤ)*b < (D:ℤ)*N := by
    have hh := mul_nonneg (sub_nonneg.mpr (show 6 ≤ (D:ℤ) by omega)) hNI.le
    dsimp [m] at hN5
    nlinarith
  have hei : (b:ℤ)*i+(a:ℤ)*j=N := by
    dsimp [A,B] at he
    dsimp [i]
    linear_combination he
  have hi : 0 < i := by
    by_contra hni
    have hi0 : i ≤ 0 := by omega
    have hh : (D:ℤ)*(b:ℤ)*i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by omega) hbI.le) hi0
    have hjb := mul_le_mul_of_nonneg_left hDj haI.le
    have heD : (D:ℤ)*(N:ℤ)=(D:ℤ)*b*i+(a:ℤ)*((D:ℤ)*j) := by rw [← hei]; ring
    dsimp [B] at hjb
    nlinarith only [hh,hjb,heD,hbig]
  have ei : (i.toNat:ℤ)=i := Int.toNat_of_nonneg hi.le
  have ej : (j.toNat:ℤ)=j := Int.toNat_of_nonneg hj.le
  refine ⟨i.toNat,j.toNat,by omega,by omega,?_,?_⟩
  · apply Int.natCast_modEq_iff.mp
    rw [ei,ej]
    change i % 4 = j % 4
    simp [i,Int.add_emod]
  · have hfin : 5*((b:ℤ)*(i.toNat:ℤ)+(a:ℤ)*(j.toNat:ℤ))=(q:ℤ)*m := by
      rw [ei,ej,hei,eNI]
    exact_mod_cast hfin

theorem parameter_indices_reference (r n₀ : ℕ) (hr : 4 ≤ r)
    (hc : Choice r n₀) : IndexConditions r n₀ := by
  have hh := choice_common r n₀ hr hc
  rcases hh with ⟨_,h04,h14,_,_,_,_,_,ha,hab,_⟩
  have h15 : Nat.ModEq 5 (nextN r n₀) 2 := by
    simpa [nextN,Nat.ModEq,Nat.add_mod,Nat.mul_mod] using hc.2.1
  have h12 : Nat.ModEq (2^r) (nextN r n₀) 1 := by
    simpa [nextN,Nat.ModEq,Nat.add_mod,Nat.mul_mod] using hc.1
  have ha5 := exponent_mod_five n₀ h04 hc.2.1
  have hb5 := exponent_mod_five (nextN r n₀) h14 h15
  have ha2 := exponent_two_power r n₀ (by omega) hc.1
  have hb2 := exponent_two_power r (nextN r n₀) (by omega) h12
  have hgp : 0 < Nat.gcd (exponent n₀) (exponent (nextN r n₀)) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  have hg := Nat.le_of_dvd hgp (Nat.dvd_gcd ha2 hb2)
  have hp : 5 < 2^(r-1) := by
    have hh := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2)
      (show 3 ≤ r-1 by omega)
    norm_num at hh ⊢
    omega
  refine ⟨ha5,hb5,?_,hg,hp,?_⟩
  · intro hf
    have hh := Nat.mod_eq_zero_of_dvd (dvd_trans hf (Nat.gcd_dvd_left _ _))
    change exponent n₀ % 5 = 2 at ha5
    omega
  · intro q hq
    exact positive_indices _ _ (by omega) (by omega) ha5 hb5 (lt_of_lt_of_le hp hg)
      q (by rcases hq with rfl | rfl <;> omega)

end
end AmbientMultiplicity.Parameters

end OAI
