import OAI.Combinatorics.Sidorenko.Planted

namespace OAI

namespace SidorenkoCounterexample

private theorem quadratic_ge_right (A B C x b : ℝ)
    (hA : 0 ≤ A) (hxb : x ≤ b) (hderiv : 2 * A * b + B ≤ 0) :
    A * b ^ 2 + B * b + C ≤ A * x ^ 2 + B * x + C := by
  have h : 0 ≤ -A * (x + b) - B := by
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hxb)]
  have := mul_nonneg (sub_nonneg.mpr hxb) h
  nlinarith

private theorem quadratic_ge_endpoints (A B C a b x k : ℝ)
    (hA : A ≤ 0) (hax : a ≤ x) (hxb : x ≤ b)
    (ha : k ≤ A * a ^ 2 + B * a + C)
    (hb : k ≤ A * b ^ 2 + B * b + C) :
    k ≤ A * x ^ 2 + B * x + C := by
  by_cases hab : a = b
  · have : x = a := by linarith
    simpa [this] using ha
  have hab' : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (hax.trans hxb) hab)
  have h₁ := mul_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr ha)
  have h₂ := mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hb)
  have h₃ := mul_nonneg (mul_nonneg (neg_nonneg.mpr hA)
    (mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hxb)))
    (le_of_lt hab')
  have hsum : 0 ≤ (b - a) * (A * x ^ 2 + B * x + C - k) := by
    nlinarith only [h₁, h₂, h₃]
  exact le_of_sub_nonneg ((nonneg_of_mul_nonneg_right hsum hab'))

/-- The scalar minimization for nonnegative δ, without analytic derivatives. -/
theorem coercivity_scalar_pos (P T δ : ℝ) (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    (_hT : 0 ≤ T) (hTP : T ≤ P + 3 * δ) :
    (P ^ 2 + δ ^ 2) / 18 ≤
      3 * δ ^ 2 / 4 + (2 * P - T) ^ 2 / 18 + (5 * P - T) * δ / 6 -
        (min (P / 3 + δ) ((P - T + 3 * δ) / 2)) ^ 2 / 2 := by
  have hPd := mul_nonneg hP hδ
  by_cases ht : T ≤ P / 3 + δ
  · rw [min_eq_left (by linarith)]
    have hmono := quadratic_ge_right (1/18) (-2*P/9-δ/6)
      (3*δ^2/4+2*P^2/9+5*P*δ/6-(P/3+δ)^2/2)
      T (P/3+δ) (by norm_num) ht (by nlinarith)
    nlinarith [sq_nonneg P, sq_nonneg δ]
  · rw [min_eq_right (by linarith)]
    have hl : P / 3 + δ ≤ T := by linarith
    have hem := quadratic_ge_endpoints (-5/72) (P/36+7*δ/12)
      (7*P^2/72+P*δ/12-3*δ^2/8) (P/3+δ) (P+3*δ) T
      ((P^2+δ^2)/18) (by norm_num) hl hTP
      (by nlinarith [sq_nonneg P, sq_nonneg δ])
      (by nlinarith [sq_nonneg P, sq_nonneg δ])
    nlinarith only [hem]

/-- The scalar minimization used after δ = -y and P = x + 3y. -/
theorem coercivity_scalar_neg (x T y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (_hT : 0 ≤ T) (hTx : T ≤ x) :
    (x ^ 2 + y ^ 2) / 18 ≤
      y ^ 2 / 4 + (2*x-T)*y/3 + (2*x-T)^2/18 -
        (min (x/3) ((x-T)/2))^2/2 := by
  have hxy := mul_nonneg hx hy
  by_cases ht : T ≤ x/3
  · rw [min_eq_left (by linarith)]
    have hmono := quadratic_ge_right (1/18) (-2*x/9-y/3)
      (y^2/4+2*x*y/3+x^2/6) T (x/3) (by norm_num) ht (by nlinarith)
    nlinarith [sq_nonneg x, sq_nonneg y]
  · rw [min_eq_right (by linarith)]
    have hem := quadratic_ge_endpoints (-5/72) (x/36-y/3)
      (y^2/4+2*x*y/3+7*x^2/72) (x/3) x T ((x^2+y^2)/18)
      (by norm_num) (by linarith) hTx
      (by nlinarith [sq_nonneg x, sq_nonneg y])
      (by nlinarith [sq_nonneg x, sq_nonneg y])
    nlinarith only [hem]

/-- Scalar lower bound after controlling the v-term and applying Cauchy–Schwarz. -/
noncomputable def scalarForm (c d P T δ : ℝ) : ℝ :=
  (c*(d+δ)-δ*d+2*δ^2)/4 + (2*P-T)^2/18 + δ*P - c*(P+T)/6 -
    (min (P/3+δ) ((P-T+3*δ)/2))^2/2

theorem coercivity_scalar (c d P T δ : ℝ) (hc : |δ| ≤ c)
    (hd : P + T ≤ d) (hP : 0 ≤ P) (hT : 0 ≤ T) (hTP : T ≤ P+3*δ) :
    (P^2+T^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤ scalarForm c d P T δ := by
  have hsplit : scalarForm |δ| d P T δ + (c-|δ|)*(d+3*δ)/12 ≤
      scalarForm c d P T δ := by
    have hm := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hd)
    dsimp [scalarForm]
    nlinarith only [hm]
  suffices h : (P^2+T^2+δ^2)/342 ≤ scalarForm |δ| d P T δ by linarith only [h, hsplit]
  by_cases hδ : 0 ≤ δ
  · rw [abs_of_nonneg hδ]
    have hs := coercivity_scalar_pos P T δ hP hδ hT hTP
    have hsquare := mul_nonneg (sub_nonneg.mpr hTP) (show 0 ≤ P+3*δ+T by linarith)
    have hsize : P^2+T^2+δ^2 ≤ 19*(P^2+δ^2) := by
      nlinarith only [hsquare, sq_nonneg (P-3*δ), sq_nonneg P]
    dsimp [scalarForm]
    nlinarith only [hs, hsize]
  · have hδ' : δ ≤ 0 := le_of_not_ge hδ
    rw [abs_of_nonpos hδ']
    have hx : 0 ≤ P+3*δ := by linarith
    have hs := coercivity_scalar_neg (P+3*δ) T (-δ) hx (neg_nonneg.mpr hδ') hT hTP
    rw [show (P+3*δ)/3 = P/3+δ by ring,
      show (P+3*δ-T)/2 = (P-T+3*δ)/2 by ring] at hs
    have hsquare := mul_nonneg (sub_nonneg.mpr hTP) (show 0 ≤ P+3*δ+T by linarith)
    have hsize : P^2+T^2+δ^2 ≤ 19*((P+3*δ)^2+δ^2) := by
      nlinarith only [hsquare, sq_nonneg (P+6*δ), sq_nonneg (P+3*δ)]
    have hdim := mul_nonneg (neg_nonneg.mpr hδ') (sub_nonneg.mpr hd)
    dsimp [scalarForm]
    nlinarith only [hs, hsize, hdim]

open scoped BigOperators

/-- Exactly the homogeneous quadratic part of equation (tail-linear-loss). -/
noncomputable def quadraticPart (c d δ v : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  (c*(d+δ)-δ*d+2*δ^2)/4 + (∑ i, (2*p i-t i)^2)/6 +
    δ*(∑ i, p i) - c*((∑ i, p i)+(∑ i, t i))/6 +
    ((d-3*δ)/2-(∑ i, p i))*v+v^2/2

private theorem three_sq (z : Fin 3 → ℝ) : (∑ i, z i)^2 ≤ 3*∑ i, (z i)^2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (z 0-z 1), sq_nonneg (z 0-z 2), sq_nonneg (z 1-z 2)]

/-- Manuscript Lemma `lem:coercivity`, with every feasibility condition explicit.
    No dimension-dependent error term or asymptotic assumption occurs here. -/
theorem coercivity (c d δ v : ℝ) (p t : Fin 3 → ℝ)
    (hc : |δ| ≤ c) (hd : (∑ i, p i)+(∑ i, t i) ≤ d)
    (hp : ∀ i, 0 ≤ p i) (ht : ∀ i, 0 ≤ t i) (hv : 0 ≤ v)
    (htp : ∀ i, t i ≤ p i+δ) (hvp : ∀ i, v ≤ p i+δ)
    (hw : 0 ≤ (d-3*δ)/2-(∑ i, p i)+v) :
    ((∑ i, p i)^2+(∑ i, t i)^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤
      quadraticPart c d δ v p t := by
  let P := ∑ i, p i
  let T := ∑ i, t i
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => hp i
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => ht i
  have hTP : T ≤ P+3*δ := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => htp i)
    simpa [Finset.sum_add_distrib, P, T] using hh
  have hvP : v ≤ P/3+δ := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hvp i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hh
    change (3:ℝ)*v ≤ P+3*δ at hh
    linarith only [hh]
  let m := min (P/3+δ) ((P-T+3*δ)/2)
  let k := (d-3*δ)/2-P
  have hm : 0 ≤ m := le_min (by linarith only [hv, hvP]) (by linarith only [hTP])
  have hkm : -k ≤ m := by
    apply le_min
    · dsimp [k]
      change 0 ≤ (d-3*δ)/2-P+v at hw
      linarith only [hw, hvP]
    · dsimp [k]
      change P+T ≤ d at hd
      linarith only [hd]
  have hvquad : -m^2/2 ≤ k*v+v^2/2 := by
    by_cases hk : 0 ≤ k
    · nlinarith only [mul_nonneg hk hv, sq_nonneg v, sq_nonneg m]
    · have hh₁ : 0 ≤ m+k := by linarith only [hkm]
      have hh₂ : 0 ≤ m-k := by linarith only [hm, hk]
      nlinarith only [mul_nonneg hh₁ hh₂, sq_nonneg (v+k)]
  have hsq := three_sq (fun i => 2*p i-t i)
  have hsum : (∑ i, (2*p i-t i)) = 2*P-T := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum, P, T]
  rw [hsum] at hsq
  have hscalar := coercivity_scalar c d P T δ hc hd hP hT hTP
  change (P^2+T^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤ _
  calc
    _ ≤ scalarForm c d P T δ := hscalar
    _ ≤ quadraticPart c d δ v p t := by
      dsimp [scalarForm, quadraticPart]
      change _ ≤ (c*(d+δ)-δ*d+2*δ^2)/4 + (∑ i, (2*p i-t i)^2)/6 +
        δ*P-c*(P+T)/6+k*v+v^2/2
      change - (min (P/3+δ) ((P-T+3*δ)/2))^2/2 ≤ _ at hvquad
      nlinarith only [hsq, hvquad]


noncomputable def triangular (n : ℝ) : ℝ := n*(n+1)/2

/-- The face baseline β=C/2-∑b(h)/6, after D=d+c and s=p+t. -/
noncomputable def baseline (c d : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  ((d+c+1)*c + ∑ i, triangular (p i+t i))/2 -
    (∑ i, triangular (c+p i+t i))/6



noncomputable def plantedGain (c d δ v : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  ((d+c)/2+c+1)*((c+δ)/2)-2*((c+δ)/2)^2 +
    (∑ i, triangular (p i+t i)) - δ*(∑ i, p i) - (∑ i, (p i)^2) -
    v*((d-3*δ)/2-(∑ i, p i)+v) - (∑ i, triangular (t i)) + triangular v

/-- Equation (slack), with the actual baseline and gain, not a new bound. -/
theorem slack_identity (c d δ v : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d δ v p t =
    (c*(d+δ-1)-δ*(d+2)+2*δ^2)/4 +
    (∑ i, ((2*p i-t i)*(2*p i-t i-1)/6 + δ*p i-c*(p i+t i)/6)) +
    v*((d-3*δ)/2-(∑ i, p i)+v) - triangular v := by
  simp only [baseline, plantedGain, triangular, Fin.sum_univ_three]
  ring

/-- Equation (tail-linear-loss). -/
theorem slack_quadratic (c d δ v : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d δ v p t =
    quadraticPart c d δ v p t - c/4 - δ/2 -
      (2*(∑ i, p i)-(∑ i, t i))/6-v/2 := by
  rw [slack_identity]
  simp only [quadraticPart, triangular, Fin.sum_univ_three]
  ring

/-- Uniform linear loss on a face, as used in (tail-budget). -/
theorem slack_uniform_linear (c d δ v M : ℝ) (p t : Fin 3 → ℝ)
    (hc : 0 ≤ c) (hδ : δ ≤ c) (hv : v ≤ M)
    (hP : (∑ i, p i) ≤ 3*(M-c)) (hT : 0 ≤ ∑ i, t i) :
    quadraticPart c d δ v p t - 3*M/2 ≤
      baseline c d p t - plantedGain c d δ v p t := by
  rw [slack_quadratic]
  linarith only [hc, hδ, hv, hP, hT]

/-- The leading coefficient in d is exactly (c-δ+2v)/4. -/
theorem slack_leading_coefficient (c d δ v : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d δ v p t =
    ((c-δ+2*v)/4)*d + baseline c 0 p t - plantedGain c 0 δ v p t := by
  simp only [baseline, plantedGain, triangular, Fin.sum_univ_three]
  ring

/-- Equation (tail-integer-slack), after the bounded-dimension argument forces
u=c, δ=c and v=0. -/
theorem slack_integer_regime (c d : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d c 0 p t =
    (3*c^2-3*c)/4 +
      (∑ i, ((2*p i-t i)^2+(c-1)*(2*p i-t i)+3*c*p i))/6 := by
  simp only [baseline, plantedGain, triangular, Fin.sum_univ_three]
  ring

/-- For common dimension at least two, the eventual integer-regime slack
is strictly positive. This needs no rounding relaxation. -/
theorem slack_pos_of_two_le (c d : ℝ) (p t : Fin 3 → ℝ)
    (hc : 2 ≤ c) (hp : ∀ i, 0 ≤ p i) :
    0 < baseline c d p t - plantedGain c d c 0 p t := by
  rw [slack_integer_regime]
  have hi (i : Fin 3) : -(c-1)^2/4 ≤
      (2*p i-t i)^2+(c-1)*(2*p i-t i)+3*c*p i := by
    have hh := mul_nonneg (show 0 ≤ c by linarith) (hp i)
    nlinarith only [hh, sq_nonneg (2*p i-t i+(c-1)/2)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hpos : 0 < (c-1)*(5*c+1) := mul_pos (by linarith) (by linarith)
  nlinarith only [hh, hpos]

/-- The zero-common-dimension local equality calculation must use integer
parameters; the corresponding assertion is false for general real tuples. -/
theorem integer_pair_slack (p t : ℤ) (hp : 0 ≤ p) (ht : 0 ≤ t) (htp : t ≤ p) :
    0 ≤ (2*p-t)*(2*p-t-1) ∧
      ((2*p-t)*(2*p-t-1) = 0 ↔ (p=0 ∧ t=0) ∨ (p=1 ∧ t=1)) := by
  have hn : 0 ≤ 2*p-t := by omega
  constructor
  · by_cases hz : 2*p-t = 0
    · simp [hz]
    · exact mul_nonneg hn (by omega)
  · rw [mul_eq_zero]
    constructor
    · intro h
      rcases h with h | h
      · left; omega
      · right; omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators
noncomputable def faceBaseline (D c : ℝ) (s : Fin 3 → ℝ) : ℝ :=
  ((D+1)*c + ∑ i, triangular (s i))/2 - (∑ i, triangular (c+s i))/6

 theorem triangular_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ triangular x := by
  unfold triangular; positivity
 theorem triangular_pos {x : ℝ} (hx : 0 < x) : 0 < triangular x := by
  unfold triangular; positivity
 theorem triangular_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    triangular x ≤ triangular y := by
  have h := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ y+x+1 by linarith)
  dsimp [triangular]; nlinarith only [h]
 theorem triangular_nat (n : ℕ) : ((n+1).choose 2 : ℝ) = triangular n := by
  rw [Nat.cast_choose_two]
  simp only [Nat.cast_add,Nat.cast_one]
  unfold triangular
  ring

 theorem faceBaseline_lower (D c : ℝ) (s : Fin 3 → ℝ) (k : Fin 3)
    (hc : 0 ≤ c) (hs : ∀ i, 0 ≤ s i) (hD : (∑ i, s i) ≤ D-c) :
    triangular (c+s k)/3 + triangular c/6 +
      ((∑ i, triangular (s i))-triangular (s k))/3 ≤ faceBaseline D c s := by
  have hm : s k ≤ ∑ i, s i := Finset.single_le_sum (fun i _ => hs i) (Finset.mem_univ k)
  have hn := mul_nonneg hc (show 0 ≤ 3*(D-c)-(∑ i, s i)-2*s k by linarith)
  have he : faceBaseline D c s - (triangular (c+s k)/3 + triangular c/6 +
      ((∑ i, triangular (s i))-triangular (s k))/3) =
      c*(3*(D-c)-(∑ i, s i)-2*s k)/6 := by
    simp only [faceBaseline,triangular,Fin.sum_univ_three]
    ring
  linarith only [hn,he]

 theorem half_triangular_bounds (h : ℕ) :
    0 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
    (h:ℝ)^2/24-(h:ℝ)/12 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
    (triangular (h:ℝ)/3-triangular (h/2:ℕ) = 0 ↔ h=0 ∨ h=2) := by
  have hd := Nat.mod_add_div h 2
  have hr := Nat.mod_lt h (by norm_num : 0<2)
  have hq : 0 ≤ (h/2:ℕ) := Nat.zero_le _
  have hqr : (0:ℝ) ≤ (h/2:ℕ) := Nat.cast_nonneg _
  rcases (show h%2=0 ∨ h%2=1 by omega) with he | he
  · have hh : h=2*(h/2) := by omega
    have hh' : (h:ℝ)=2*(h/2:ℕ) := by exact_mod_cast hh
    have hn : (h/2:ℕ)=0 ∨ (h/2:ℕ)=1 ∨ 2 ≤ h/2 := by omega
    rcases hn with hn | hn | hn
    · have hz : h=0 := by omega
      subst h; norm_num [triangular]
    · have hz : h=2 := by omega
      subst h; norm_num [triangular]
    · have hn' : (2:ℝ) ≤ (h/2:ℕ) := by exact_mod_cast hn
      have hp : 0 < (h/2:ℕ)*( (h/2:ℕ)-1 : ℝ) := mul_pos (by linarith) (by linarith)
      dsimp [triangular]
      constructor
      · nlinarith only [hh',hp]
      constructor
      · nlinarith only [hh',sq_nonneg ((h/2:ℕ):ℝ)]
      constructor
      · intro hz; nlinarith only [hh',hp,hz]
      · intro hz; rcases hz with hz | hz <;> omega
  · have hh : h=2*(h/2)+1 := by omega
    have hh' : (h:ℝ)=2*(h/2:ℕ)+1 := by exact_mod_cast hh
    have hp : 0 < ((h/2:ℕ):ℝ)+1 := by positivity
    have hp' := mul_pos hp (show (0:ℝ) < (h/2:ℕ)+2 by positivity)
    dsimp [triangular]
    constructor
    · nlinarith only [hh',hp',sq_nonneg ((h/2:ℕ):ℝ)]
    constructor
    · nlinarith only [hh',sq_nonneg ((h/2:ℕ):ℝ),hqr]
    constructor
    · intro hz; nlinarith only [hh',hp',hz]
    · intro hz; rcases hz with hz | hz <;> omega

 theorem lower_active_slack (D c : ℕ) (s : Fin 3 → ℕ) (k : Fin 3) (g : ℝ)
    (hD : (∑ i, s i) ≤ D-c) (hcD : c ≤ D)
    (_hk : ∀ i, s i ≤ s k) (hg : g ≤ triangular ((c+s k)/2:ℕ)) :
    0 ≤ faceBaseline D c (fun i => s i)-g ∧
    ((c+s k:ℕ):ℝ)^2/24-((c+s k:ℕ):ℝ)/12 ≤ faceBaseline D c (fun i => s i)-g ∧
    (faceBaseline D c (fun i => s i)-g = 0 →
      c=0 ∧ (∀ i, i≠k → s i=0) ∧ (s k=0 ∨ s k=2)) := by
  have hD' : (∑ i, (s i:ℝ)) ≤ (D:ℝ)-c := by exact_mod_cast hD
  have hb := faceBaseline_lower (D:ℝ) c (fun i => s i) k (by positivity) (fun i => by positivity) hD'
  have hh := half_triangular_bounds (c+s k)
  have he : 0 ≤ (∑ i, triangular (s i))-triangular (s k) := by
    exact sub_nonneg.mpr (Finset.single_le_sum (fun i _ => triangular_nonneg (Nat.cast_nonneg _)) (Finset.mem_univ k))
  have hct : 0 ≤ triangular (c:ℝ) := triangular_nonneg (Nat.cast_nonneg _)
  simp only [Nat.cast_add] at hh
  refine ⟨by linarith [hh.1],by simp only [Nat.cast_add]; linarith [hh.2.1],?_⟩
  intro hz
  have hc : c=0 := by
    by_contra hc
    have hp := triangular_pos (show (0:ℝ)<c by exact_mod_cast Nat.pos_of_ne_zero hc)
    linarith [hh.1]
  subst c
  simp only [Nat.cast_zero,zero_add] at hb hh hg hz
  have hothers : (∑ i, triangular (s i))-triangular (s k) = 0 := by
    have hz0 : triangular (0:ℝ)=0 := by norm_num [triangular]
    rw [hz0] at hb
    linarith [hh.1]
  refine ⟨rfl,?_,?_⟩
  · intro i hik
    have hle : triangular (s i)+triangular (s k) ≤ ∑ j, triangular (s j) := by
      have hsub : ({i,k}:Finset (Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
      have hx := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => triangular_nonneg (Nat.cast_nonneg (s j)))
      simpa only [Finset.sum_pair hik] using hx
    have hi0 : triangular (s i)=0 := by linarith [triangular_nonneg (Nat.cast_nonneg (s i))]
    by_contra hi
    have hp := triangular_pos (show (0:ℝ)<s i by exact_mod_cast Nat.pos_of_ne_zero hi)
    linarith
  · apply (half_triangular_bounds (s k)).2.2.mp
    have hz0 : triangular (0:ℝ)=0 := by norm_num [triangular]
    rw [hz0] at hb
    linarith [(half_triangular_bounds (s k)).1]
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators
structure TailTuple where
  c : ℕ
  u : ℕ
  v : ℕ
  p : Fin 3 → ℕ
  t : Fin 3 → ℕ

def TailTuple.s (a : TailTuple) (i : Fin 3) : ℕ := a.p i+a.t i
def TailTuple.h (a : TailTuple) (i : Fin 3) : ℕ := a.c+a.s i
def TailTuple.maxH (a : TailTuple) : ℕ := Finset.univ.sup a.h
noncomputable def TailTuple.delta (a : TailTuple) : ℝ := 2*a.u-a.c
noncomputable def TailTuple.P (a : TailTuple) : ℝ := ∑ i, (a.p i:ℝ)
noncomputable def TailTuple.T (a : TailTuple) : ℝ := ∑ i, (a.t i:ℝ)
noncomputable def TailTuple.Q (D : ℕ) (a : TailTuple) : ℝ :=
  quadraticPart a.c ((D:ℝ)-a.c) a.delta a.v (fun i => a.p i) (fun i => a.t i)
noncomputable def TailTuple.energy (D : ℕ) (a : TailTuple) : ℝ :=
  (a.P^2+a.T^2+a.delta^2)/342 + ((a.c:ℝ)-|a.delta|)*((D:ℝ)-a.c+3*a.delta)/12
noncomputable def tailGain (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  if full then plantedGain a.c ((D:ℝ)-a.c) a.delta a.v (fun i => a.p i) (fun i => a.t i)
  else triangular (a.maxH/2:ℕ)
noncomputable def tailSlack (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  faceBaseline D a.c (fun i => a.s i)-tailGain D full a
noncomputable def tailEnergy (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  if full then a.energy D else (a.maxH:ℝ)^2/24

def TailFeasible (D : ℕ) (full : Bool) (a : TailTuple) : Prop :=
  a.c ≤ D ∧ (∑ i, a.s i) ≤ D-a.c ∧ (full=true →
    a.u ≤ a.c ∧
    (∀ i, (a.t i:ℝ) ≤ a.p i+a.delta) ∧
    (∀ i, (a.v:ℝ) ≤ a.p i+a.delta) ∧
    0 ≤ (((D:ℝ)-a.c-3*a.delta)/2)-a.P+a.v)

 theorem TailTuple.h_le_max (a : TailTuple) (i : Fin 3) : a.h i ≤ a.maxH :=
  Finset.le_sup (Finset.mem_univ i)
 theorem TailTuple.exists_max (a : TailTuple) : ∃ i, a.maxH=a.h i := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty a.h
  exact ⟨i,hi⟩
 theorem TailTuple.c_le_max (a : TailTuple) : a.c ≤ a.maxH :=
  (Nat.le_add_right a.c (a.s 0)).trans (a.h_le_max 0)
 theorem TailTuple.p_le_h (a : TailTuple) (i : Fin 3) : a.p i ≤ a.h i := by
  unfold TailTuple.h TailTuple.s; omega
 theorem TailTuple.t_le_h (a : TailTuple) (i : Fin 3) : a.t i ≤ a.h i := by
  unfold TailTuple.h TailTuple.s; omega
 theorem TailTuple.s_le_h (a : TailTuple) (i : Fin 3) : a.s i ≤ a.h i := by
  unfold TailTuple.h; omega
 theorem TailTuple.delta_abs_le (a : TailTuple) (hu : a.u ≤ a.c) : |a.delta| ≤ (a.c:ℝ) := by
  have hu' : (a.u:ℝ) ≤ a.c := by exact_mod_cast hu
  rw [abs_le]
  dsimp [TailTuple.delta]
  constructor <;> linarith [(Nat.cast_nonneg a.u : (0:ℝ) ≤ a.u)]
 theorem TailTuple.baseline (D : ℕ) (a : TailTuple) :
    faceBaseline D a.c (fun i => a.s i) =
      baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i) := by
  simp only [faceBaseline,SidorenkoCounterexample.baseline,TailTuple.s,Nat.cast_add,sub_add_cancel,add_assoc]

 theorem TailFeasible.sum_le {D : ℕ} {full : Bool} {a : TailTuple}
    (ha : TailFeasible D full a) : a.P+a.T ≤ (D:ℝ)-a.c := by
  have hh : (∑ i, (a.s i:ℝ)) ≤ (D:ℝ)-a.c := by
    have hc : ((D-a.c:ℕ):ℝ) = (D:ℝ)-a.c := Nat.cast_sub ha.1
    rw [←hc,←Nat.cast_sum]
    exact_mod_cast ha.2.1
  simpa only [TailTuple.s,Nat.cast_add,Finset.sum_add_distrib,TailTuple.P,TailTuple.T] using hh

 theorem TailFeasible.d_delta_nonneg {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) : 0 ≤ (D:ℝ)-a.c+3*a.delta := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (ha.2.2 rfl).2.1 i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at ht
  change a.T ≤ a.P+3*a.delta at ht
  have hT : 0 ≤ a.T := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  linarith [ha.sum_le]

 theorem TailFeasible.energy_nonneg {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) :
    0 ≤ a.energy D ∧ (a.P^2+a.T^2+a.delta^2)/342 ≤ a.energy D := by
  have h := mul_nonneg (sub_nonneg.mpr (a.delta_abs_le (ha.2.2 rfl).1)) ha.d_delta_nonneg
  dsimp [TailTuple.energy]
  constructor
  · positivity
  · linarith only [h]

 theorem TailFeasible.coercivity {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) : a.energy D ≤ a.Q D := by
  apply SidorenkoCounterexample.coercivity
  · exact a.delta_abs_le (ha.2.2 rfl).1
  · exact ha.sum_le
  · intro i; positivity
  · intro i; positivity
  · positivity
  · exact (ha.2.2 rfl).2.1
  · exact (ha.2.2 rfl).2.2.1
  · exact (ha.2.2 rfl).2.2.2

 theorem TailFeasible.v_le_max {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) : a.v ≤ a.maxH := by
  have hv := (ha.2.2 rfl).2.2.1 0
  have hδ := le_abs_self a.delta |>.trans (a.delta_abs_le (ha.2.2 rfl).1)
  have hp : (a.p 0:ℝ) ≤ a.h 0-a.c := by
    dsimp [TailTuple.h,TailTuple.s]; push_cast; linarith [(Nat.cast_nonneg (a.t 0) : (0:ℝ) ≤ a.t 0)]
  have hh : (a.h 0:ℝ) ≤ a.maxH := by exact_mod_cast a.h_le_max 0
  have hv' : (a.v:ℝ) ≤ a.maxH := by linarith
  exact_mod_cast hv'

 theorem tailEnergy_nonneg {D : ℕ} {full : Bool} {a : TailTuple}
    (ha : TailFeasible D full a) : 0 ≤ tailEnergy D full a := by
  cases full
  · simp only [tailEnergy,Bool.false_eq_true,ite_false]; positivity
  · exact ha.energy_nonneg.1

 theorem tailSlack_energy_lower {D : ℕ} {full : Bool} {a : TailTuple} (M : ℝ)
    (ha : TailFeasible D full a) (hM : (a.maxH:ℝ) ≤ M) :
    tailEnergy D full a-3*M/2 ≤ tailSlack D full a := by
  cases full
  · obtain ⟨k,hk⟩ := a.exists_max
    have hsk (i : Fin 3) : a.s i ≤ a.s k := by
      have hh := a.h_le_max i
      rw [hk] at hh
      exact Nat.le_of_add_le_add_left hh
    have hh := lower_active_slack D a.c a.s k (triangular (a.maxH/2:ℕ)) ha.2.1 ha.1 hsk
      (by rw [hk]; rfl)
    simp only [tailSlack,tailGain,tailEnergy,Bool.false_eq_true,ite_false]
    rw [hk] at hh ⊢
    have hhM : (a.c+a.s k:ℕ) ≤ M := by simpa only [hk,TailTuple.h] using hM
    have hMn : 0 ≤ M := (Nat.cast_nonneg a.maxH).trans hM
    change ((a.c+a.s k:ℕ):ℝ)^2/24-3*M/2 ≤ _
    linarith [hh.2.1]
  · have hc : (a.c:ℝ) ≤ M := le_trans (by exact_mod_cast a.c_le_max) hM
    have hv : (a.v:ℝ) ≤ M := le_trans (by exact_mod_cast ha.v_le_max) hM
    have hP : a.P ≤ 3*(M-a.c) := by
      have hi (i : Fin 3) : (a.p i:ℝ) ≤ M-a.c := by
        have hh : (a.h i:ℝ) ≤ M := le_trans (by exact_mod_cast a.h_le_max i) hM
        dsimp [TailTuple.h,TailTuple.s] at hh
        push_cast at hh
        linarith [(Nat.cast_nonneg (a.t i) : (0:ℝ) ≤ a.t i)]
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
      simpa only [TailTuple.P,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hh
    have hδ : a.delta ≤ (a.c:ℝ) := (le_abs_self _).trans (a.delta_abs_le (ha.2.2 rfl).1)
    have hh := slack_uniform_linear (a.c:ℝ) ((D:ℝ)-a.c) a.delta (a.v:ℝ) M
      (fun i => (a.p i:ℝ)) (fun i => (a.t i:ℝ)) (by positivity) hδ hv hP
      (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
    have hh' := sub_le_sub_right ha.coercivity (3*M/2)
    simpa only [tailSlack,tailGain,tailEnergy,ite_true,a.baseline D,TailTuple.Q] using hh'.trans hh
end SidorenkoCounterexample


namespace SidorenkoCounterexample

def pairVertices : Fin 33 → Finset (Fin 13) := ![{0,2}, {0,3}, {2,3}, {0,9}, {2,9}, {0,1}, {1,3}, {2,4}, {3,4}, {1,9}, {4,9}, {1,10}, {3,10}, {3,11}, {4,11}, {1,12}, {9,12}, {4,8}, {8,9}, {1,7}, {7,10}, {10,11}, {8,11}, {7,12}, {8,12}, {5,7}, {5,10}, {5,11}, {6,8}, {6,11}, {6,7}, {6,12}, {5,6}]
def facePair : Fin 22 → Fin 3 → Fin 33 := ![![5, 1, 6], ![5, 3, 9], ![0, 1, 2], ![0, 3, 4], ![6, 11, 12], ![19, 11, 20], ![19, 15, 23], ![9, 15, 16], ![2, 7, 8], ![7, 4, 10], ![8, 13, 14], ![12, 13, 21], ![17, 10, 18], ![17, 14, 22], ![32, 25, 30], ![32, 27, 29], ![25, 26, 20], ![26, 27, 21], ![30, 31, 23], ![28, 29, 22], ![28, 31, 24], ![18, 24, 16]]
def pairFace : Fin 33 → Fin 2 → Fin 22 := ![![2, 3], ![0, 2], ![2, 8], ![1, 3], ![3, 9], ![0, 1], ![0, 4], ![8, 9], ![8, 10], ![1, 7], ![9, 12], ![4, 5], ![4, 11], ![10, 11], ![10, 13], ![6, 7], ![7, 21], ![12, 13], ![12, 21], ![5, 6], ![5, 16], ![11, 17], ![13, 19], ![6, 18], ![20, 21], ![14, 16], ![16, 17], ![15, 17], ![19, 20], ![15, 19], ![14, 18], ![18, 20], ![14, 15]]
def pairParent : Fin 33 → Fin 33 := ![0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 4, 6, 6, 8, 8, 9, 9, 10, 10, 11, 11, 12, 14, 15, 16, 20, 20, 21, 22, 22, 23, 23, 25]
def pairBridge : Fin 33 → Fin 22 := ![2, 2, 2, 3, 3, 0, 0, 8, 8, 1, 9, 4, 4, 10, 10, 7, 7, 12, 12, 5, 5, 11, 13, 6, 21, 16, 16, 17, 19, 19, 18, 18, 14]
def faceBit : Fin 22 → Fin 3 → Bool := ![![false, false, false], ![false, true, false], ![false, false, true], ![true, true, false], ![false, false, true], ![false, false, false], ![true, false, false], ![true, true, false], ![true, false, true], ![true, false, false], ![true, true, true], ![true, false, true], ![true, false, true], ![false, true, true], ![false, false, false], ![true, true, false], ![false, true, false], ![true, true, true], ![false, false, true], ![false, true, false], ![false, true, true], ![true, true, true]]
def separationCount (e : Fin 33) : ℕ := (Finset.univ.filter fun b => faceBit (pairFace e 0) b ≠ faceBit (pairFace e 1) b).card

 theorem faces_card : ∀ j, (faces j).card = 3 := by decide
 theorem pairVertices_card : ∀ e, (pairVertices e).card = 2 := by decide
 theorem pairVertices_injective : Function.Injective pairVertices := by decide
 theorem facePair_injective : ∀ j, Function.Injective (facePair j) := by decide
 theorem facePair_correct : ∀ j e, pairVertices e ⊆ faces j ↔ ∃ k, facePair j k=e := by decide
 theorem pairFace_correct : ∀ e j, pairVertices e ⊆ faces j ↔ ∃ k, pairFace e k=j := by decide
 theorem pairFace_injective : ∀ e, Function.Injective (pairFace e) := by decide
 theorem pairParent_lt : ∀ e, e≠0 → (pairParent e).val < e.val := by decide
 theorem pairBridge_self : ∀ e, pairVertices e ⊆ faces (pairBridge e) := by decide
 theorem pairBridge_parent : ∀ e, pairVertices (pairParent e) ⊆ faces (pairBridge e) := by decide
 theorem separationCount_pos : ∀ e, 1 ≤ separationCount e := by decide
 theorem separationCount_root : separationCount 0=3 := by decide
 theorem separationCount_le : ∀ e, separationCount e ≤ 3 := by decide
 theorem root_pair : pairVertices 0={0,2} := by rfl

end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators
 theorem nonnegative_interval_sq (a b M : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ M) (hbM : b ≤ M) : (a-b)^2 ≤ M^2 := by
  have hM : 0 ≤ M := ha.trans haM
  have hab : |a-b| ≤ M := abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := (sq_le_sq₀ (abs_nonneg _) hM).2 hab
  simpa only [sq_abs] using hh

 theorem tail_pair_energy {D : ℕ} {full : Bool} {a : TailTuple}
    (ha : TailFeasible D full a) (i k : Fin 3) :
    ((a.h i:ℝ)-a.h k)^2 ≤ 684*tailEnergy D full a := by
  cases full
  · have hm (j : Fin 3) : (a.h j:ℝ) ≤ a.maxH := by exact_mod_cast a.h_le_max j
    have hh := nonnegative_interval_sq (a.h i) (a.h k) a.maxH (by positivity) (by positivity) (hm i) (hm k)
    simp only [tailEnergy,Bool.false_eq_true,ite_false]
    nlinarith [sq_nonneg (a.maxH:ℝ)]
  · have hs (j : Fin 3) : (a.s j:ℝ) ≤ a.P+a.T := by
      have hh : (a.s j:ℝ) ≤ ∑ k, (a.s k:ℝ) :=
        Finset.single_le_sum (fun k _ => Nat.cast_nonneg (a.s k)) (Finset.mem_univ j)
      simpa only [TailTuple.s,Nat.cast_add,Finset.sum_add_distrib,TailTuple.P,TailTuple.T] using hh
    have hh := nonnegative_interval_sq (a.s i) (a.s k) (a.P+a.T) (by positivity) (by positivity) (hs i) (hs k)
    have he := ha.energy_nonneg.2
    simp only [tailEnergy,ite_true]
    simp only [TailTuple.h,Nat.cast_add]
    nlinarith only [hh,he,sq_nonneg (a.P-a.T),sq_nonneg a.delta]

 theorem parent_energy_bound {n : ℕ} (p : Fin (n+1) → Fin (n+1))
    (hp : ∀ i, i≠0 → (p i).val < i.val) (f : Fin (n+1) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hstep : ∀ i, (f i-f (p i))^2 ≤ K) (i : Fin (n+1)) :
    (f i-f 0)^2 ≤ (4:ℝ)^i.val*K := by
  have hmain : ∀ m, ∀ i : Fin (n+1), i.val=m → (f i-f 0)^2 ≤ (4:ℝ)^i.val*K := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i him
      by_cases hi : i=0
      · subst i; simpa using hK
      · have hpm : (p i).val < m := by simpa only [him] using hp i hi
        have hind := ih (p i).val hpm (p i) rfl
        have hpow : (4:ℝ)^((p i).val+1) ≤ (4:ℝ)^i.val :=
          pow_le_pow_right₀ (by norm_num) (hp i hi)
        have hone : (1:ℝ) ≤ (4:ℝ)^(p i).val := one_le_pow₀ (by norm_num)
        have hc := mul_le_mul_of_nonneg_right hpow hK
        have hk' := mul_le_mul_of_nonneg_right hone hK
        rw [pow_succ] at hc
        have hh := hstep i
        nlinarith only [hind,hc,hk',hh,sq_nonneg ((f i-f (p i))-(f (p i)-f 0))]
  exact hmain i.val i rfl

noncomputable def separationExcess (h : Fin 33 → ℕ) : ℝ :=
  ∑ e, ((separationCount e:ℝ)-1)/6*triangular (h e)

def GlobalTailFeasible (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
    (h : Fin 33 → ℕ) : Prop :=
  (∀ j, TailFeasible D (full j) (a j)) ∧ ∀ j k, (a j).h k=h (facePair j k)

 theorem separationExcess_nonneg (h : Fin 33 → ℕ) : 0 ≤ separationExcess h := by
  apply Finset.sum_nonneg
  intro e _
  have he : (1:ℝ) ≤ separationCount e := by exact_mod_cast separationCount_pos e
  exact mul_nonneg (by linarith) (triangular_nonneg (Nat.cast_nonneg _))

 theorem separationExcess_root (h : Fin 33 → ℕ) :
    (h 0:ℝ)^2/6 ≤ separationExcess h := by
  have hn (e : Fin 33) : 0 ≤ ((separationCount e:ℝ)-1)/6*triangular (h e) := by
    have hh : (1:ℝ) ≤ separationCount e := by exact_mod_cast separationCount_pos e
    exact mul_nonneg (by linarith) (triangular_nonneg (Nat.cast_nonneg _))
  have he : ((separationCount 0:ℝ)-1)/6*triangular (h 0) ≤ separationExcess h :=
    Finset.single_le_sum (fun e _ => hn e) (Finset.mem_univ (0 : Fin 33))
  rw [separationCount_root] at he
  norm_num only [Nat.cast_ofNat] at he
  dsimp [triangular] at he
  nlinarith [(Nat.cast_nonneg (h 0) : (0:ℝ) ≤ h 0)]

 theorem global_tail_budget (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
    (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
    (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0) :
    (∑ j, tailEnergy D (full j) (a j))+separationExcess h ≤
      33*((Finset.univ.sup h:ℕ):ℝ) := by
  let M : ℝ := (Finset.univ.sup h:ℕ)
  have hM (j : Fin 22) : ((a j).maxH:ℝ) ≤ M := by
    have hh : (a j).maxH ≤ Finset.univ.sup h := by
      apply Finset.sup_le
      intro k _
      rw [ha.2 j k]
      exact Finset.le_sup (Finset.mem_univ _)
    change ((a j).maxH:ℝ) ≤ ((Finset.univ.sup h:ℕ):ℝ)
    exact_mod_cast hh
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun j _ => tailSlack_energy_lower M (ha.1 j) (hM j))
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  change (∑ j, tailEnergy D (full j) (a j))-22*(3*M/2) ≤ _ at hi
  change (∑ j, tailEnergy D (full j) (a j))+separationExcess h ≤ 33*M
  linarith only [hi,htotal]

/-- A deliberately coarse but absolute bound on unseparated pair dimensions.
It replaces the manuscript's unbounded-subsequence argument by a finite
energy propagation along a certified spanning tree of the exact complex. -/
def tailPairBound : ℕ := 2*4^32*22572+396

 theorem global_tail_pair_bound (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
    (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
    (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0) :
    ∀ e, h e ≤ tailPairBound := by
  let M : ℝ := (Finset.univ.sup h:ℕ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hb := global_tail_budget D full a h ha htotal
  change (∑ j, tailEnergy D (full j) (a j))+separationExcess h ≤ 33*M at hb
  have he0 : 0 ≤ separationExcess h := separationExcess_nonneg h
  have hen (j : Fin 22) : 0 ≤ tailEnergy D (full j) (a j) := tailEnergy_nonneg (ha.1 j)
  have hes : 0 ≤ ∑ j, tailEnergy D (full j) (a j) := Finset.sum_nonneg (fun j _ => hen j)
  have he (j : Fin 22) : tailEnergy D (full j) (a j) ≤ 33*M := by
    have hh := Finset.single_le_sum (fun j _ => hen j) (Finset.mem_univ j)
    linarith
  have hroot : (h 0:ℝ)^2 ≤ 198*M := by linarith [separationExcess_root h]
  have hstep (e : Fin 33) : ((h e:ℝ)-h (pairParent e))^2 ≤ 22572*M := by
    obtain ⟨i,hi⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) (pairParent e)).mp (pairBridge_parent e)
    have hh := tail_pair_energy (ha.1 (pairBridge e)) i k
    rw [ha.2,ha.2,hi,hk] at hh
    linarith [he (pairBridge e)]
  obtain ⟨em,_,hem⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty h
  have hem' : (h em:ℝ)=M := by
    dsimp [M]; exact_mod_cast hem.symm
  have hg := parent_energy_bound pairParent pairParent_lt (fun e => (h e:ℝ)) (22572*M) (by positivity) hstep em
  have hp : (4:ℝ)^em.val ≤ (4:ℝ)^32 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hgp := mul_le_mul_of_nonneg_right hp (show 0 ≤ 22572*M by positivity)
  have htotalM : M^2 ≤ (tailPairBound:ℝ)*M := by
    rw [hem'] at hg
    simp only [tailPairBound,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [hg,hgp,hroot,sq_nonneg (M-2*(h 0:ℝ))]
  have hMB : M ≤ (tailPairBound:ℝ) := by
    by_contra hnot
    have hdiff : 0 < M-(tailPairBound:ℝ) := by linarith
    have hMp : 0 < M := lt_of_le_of_lt (Nat.cast_nonneg _) (lt_of_not_ge hnot)
    have hp := mul_pos hMp hdiff
    nlinarith only [hp,htotalM]
  intro e
  have heM : (h e:ℝ) ≤ M := by
    dsimp [M]; exact_mod_cast (Finset.le_sup (f := h) (Finset.mem_univ e))
  exact_mod_cast heM.trans hMB
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators
structure TailBox (B : ℕ) where
  c : Fin (B+1)
  u : Fin (B+1)
  v : Fin (B+1)
  p : Fin 3 → Fin (B+1)
  t : Fin 3 → Fin (B+1)
  deriving Fintype

def TailBox.tuple {B : ℕ} (b : TailBox B) : TailTuple :=
  ⟨b.c,b.u,b.v,fun i => b.p i,fun i => b.t i⟩
noncomputable def tailRemainder (a : TailTuple) : ℝ :=
  baseline a.c 0 (fun i => a.p i) (fun i => a.t i)-
    plantedGain a.c 0 a.delta a.v (fun i => a.p i) (fun i => a.t i)
noncomputable def tailLinear (a : TailTuple) : ℝ := ((a.c:ℝ)-a.u+a.v)/2
noncomputable def tailRemainderBound (B : ℕ) : ℝ :=
  ∑ b : TailBox B, |tailRemainder b.tuple|
 theorem tailRemainderBound_nonneg (B : ℕ) : 0 ≤ tailRemainderBound B :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)
 theorem tailSlack_linear (D : ℕ) (a : TailTuple) :
    tailSlack D true a=tailLinear a*((D:ℝ)-a.c)+tailRemainder a := by
  simp only [tailSlack,tailGain,ite_true,a.baseline D]
  rw [slack_leading_coefficient]
  dsimp [tailLinear,tailRemainder,TailTuple.delta]
  ring
 theorem tailLinear_nonneg {a : TailTuple} (hu : a.u ≤ a.c) : 0 ≤ tailLinear a := by
  have hu' : (a.u:ℝ) ≤ a.c := by exact_mod_cast hu
  dsimp [tailLinear]
  linarith [show (0:ℝ) ≤ a.v by positivity]
 theorem tailLinear_half {a : TailTuple} (hu : a.u ≤ a.c)
    (hbad : ¬(a.u=a.c ∧ a.v=0)) : 1/2 ≤ tailLinear a := by
  have hh : a.u+1 ≤ a.c+a.v := by omega
  have hh' : (a.u:ℝ)+1 ≤ a.c+a.v := by exact_mod_cast hh
  dsimp [tailLinear]; linarith
 theorem tailRemainder_bounded {D B : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) (hB : a.maxH ≤ B) :
    |tailRemainder a| ≤ tailRemainderBound B := by
  have hc : a.c ≤ B := a.c_le_max.trans hB
  have hu : a.u ≤ B := (ha.2.2 rfl).1.trans hc
  have hv : a.v ≤ B := ha.v_le_max.trans hB
  have hp (i : Fin 3) : a.p i ≤ B := (a.p_le_h i).trans ((a.h_le_max i).trans hB)
  have ht (i : Fin 3) : a.t i ≤ B := (a.t_le_h i).trans ((a.h_le_max i).trans hB)
  let b : TailBox B := ⟨⟨a.c,by omega⟩,⟨a.u,by omega⟩,⟨a.v,by omega⟩,
    fun i => ⟨a.p i,by have := hp i; omega⟩,fun i => ⟨a.t i,by have := ht i; omega⟩⟩
  have hb : b.tuple=a := by cases a; rfl
  rw [←hb]
  exact Finset.single_le_sum (f := fun x : TailBox B => |tailRemainder x.tuple|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
 theorem tailSlack_lower_nonneg {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D false a) : 0 ≤ tailSlack D false a := by
  obtain ⟨k,hk⟩ := a.exists_max
  have hsk (i : Fin 3) : a.s i ≤ a.s k := by
    have hh := a.h_le_max i
    rw [hk] at hh
    exact Nat.le_of_add_le_add_left hh
  exact (lower_active_slack D a.c a.s k (triangular (a.maxH/2:ℕ)) ha.2.1 ha.1 hsk
    (by rw [hk]; rfl)).1
 theorem global_maxH_bound {D : ℕ} {full : Fin 22 → Bool} {a : Fin 22 → TailTuple}
    {h : Fin 33 → ℕ} (ha : GlobalTailFeasible D full a h)
    (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0) (j : Fin 22) :
    (a j).maxH ≤ tailPairBound := by
  have hb := global_tail_pair_bound D full a h ha htotal
  apply Finset.sup_le
  intro k _
  rw [ha.2]
  exact hb _




 theorem eventually_integer_regime : ∃ D₀ : ℕ, ∀ D ≥ D₀,
    ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
    GlobalTailFeasible D full a h →
    (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0 →
    ∀ j, full j=true → (a j).u=(a j).c ∧ (a j).v=0 := by
  let B := tailPairBound
  let R := tailRemainderBound B
  have hR : 0 ≤ R := tailRemainderBound_nonneg B
  obtain ⟨D₀,hD₀⟩ := exists_nat_gt ((B:ℝ)+44*R)
  refine ⟨D₀,?_⟩
  intro D hD full a h ha htotal
  have hD' : (B:ℝ)+44*R < D := lt_of_lt_of_le hD₀ (by exact_mod_cast hD)
  have hB (j : Fin 22) : (a j).maxH ≤ B := global_maxH_bound ha htotal j
  have hc (j : Fin 22) : ((a j).c:ℝ) ≤ B := by
    exact_mod_cast (a j).c_le_max.trans (hB j)
  have hrem (j : Fin 22) (hj : full j=true) : -R ≤ tailRemainder (a j) := by
    have hh := tailRemainder_bounded (D := D) (by simpa only [hj] using ha.1 j) (hB j)
    exact (abs_le.mp hh).1
  have hs (j : Fin 22) : -R ≤ tailSlack D (full j) (a j) := by
    cases hj : full j with
    | false =>
      have hh := tailSlack_lower_nonneg (by simpa only [hj] using ha.1 j)
      linarith only [hR,hh]
    | true =>
      have haj : TailFeasible D true (a j) := by simpa only [hj] using ha.1 j
      rw [tailSlack_linear]
      have hdn : 0 ≤ (D:ℝ)-(a j).c := sub_nonneg.mpr (by exact_mod_cast haj.1)
      have hh := mul_nonneg (tailLinear_nonneg (haj.2.2 rfl).1) hdn
      linarith only [hh,hrem j hj]
  intro j hj
  by_contra hbad
  have haj : TailFeasible D true (a j) := by simpa only [hj] using ha.1 j
  have hA := tailLinear_half (haj.2.2 rfl).1 hbad
  have hdn : 0 ≤ (D:ℝ)-(a j).c := by
    have hcD : ((a j).c:ℝ) ≤ D := by exact_mod_cast haj.1
    linarith
  have hmul := mul_le_mul_of_nonneg_right hA hdn
  have hsl : (D:ℝ)/2-(B:ℝ)/2-R ≤ tailSlack D (full j) (a j) := by
    rw [hj,tailSlack_linear]
    linarith only [hmul,hrem j hj,hc j]
  have hsum : tailSlack D (full j) (a j)+R ≤ ∑ k, (tailSlack D (full k) (a k)+R) :=
    Finset.single_le_sum (f := fun k : Fin 22 => tailSlack D (full k) (a k)+R)
      (fun k _ => by linarith only [hs k]) (Finset.mem_univ j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsum
  linarith only [hsum,hsl,htotal,separationExcess_nonneg h,hD']
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators
 theorem delta_integer_regime (a : TailTuple) (hu : a.u=a.c) : a.delta=(a.c:ℝ) := by
  dsimp [TailTuple.delta]; rw [hu]; ring
 theorem tailSlack_integer (D : ℕ) (a : TailTuple) (hu : a.u=a.c) (hv : a.v=0) :
    tailSlack D true a = baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
      plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i) := by
  simp only [tailSlack,tailGain,ite_true,a.baseline D,delta_integer_regime a hu,hv,Nat.cast_zero]

 theorem integer_slack_classification {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D true a) (hu : a.u=a.c) (hv : a.v=0) :
    0 ≤ tailSlack D true a ∧ (tailSlack D true a=0 →
      (a.c=0 ∧ ∀ i, (a.p i=0 ∧ a.t i=0) ∨ (a.p i=1 ∧ a.t i=1)) ∨
      (a.c=1 ∧ ∀ i, a.p i=0 ∧ a.t i=0)) := by
  rw [tailSlack_integer D a hu hv]
  by_cases hc0 : a.c=0
  · have he : baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
        plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i) =
        (∑ i : Fin 3, (2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1))/6 := by
      rw [slack_integer_regime,hc0]
      simp only [Nat.cast_zero,Fin.sum_univ_three]; ring
    rw [he]
    have hi (i : Fin 3) : 0 ≤ (2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1) ∧
        ((2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1)=0 →
          (a.p i=0 ∧ a.t i=0) ∨ (a.p i=1 ∧ a.t i=1)) := by
      have ht := (ha.2.2 rfl).2.1 i
      rw [delta_integer_regime a hu,hc0,Nat.cast_zero,add_zero] at ht
      have ht' : (a.t i:ℤ) ≤ a.p i := by exact_mod_cast ht
      have hh := integer_pair_slack (a.p i) (a.t i) (by positivity) (by positivity) ht'
      refine ⟨by exact_mod_cast hh.1,?_⟩
      intro hz
      have hz' : (2*(a.p i:ℤ)-a.t i)*(2*(a.p i:ℤ)-a.t i-1)=0 := by exact_mod_cast hz
      have hh' := hh.2.mp hz'
      exact_mod_cast hh'
    have hsum : 0 ≤ ∑ i : Fin 3, (2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1) :=
      Finset.sum_nonneg (fun i _ => (hi i).1)
    refine ⟨by positivity,fun hz => Or.inl ⟨hc0,?_⟩⟩
    intro i
    apply (hi i).2
    have hh := Finset.single_le_sum (f := fun k : Fin 3 =>
      (2*(a.p k:ℝ)-a.t k)*(2*(a.p k:ℝ)-a.t k-1))
      (fun k _ => (hi k).1) (Finset.mem_univ i)
    linarith only [hh,hz,(hi i).1]
  · by_cases hc1 : a.c=1
    · have he : baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
          plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i) =
          (∑ i : Fin 3, ((2*(a.p i:ℝ)-a.t i)^2+3*a.p i))/6 := by
        rw [slack_integer_regime,hc1]
        simp only [Nat.cast_one,Fin.sum_univ_three]; ring
      rw [he]
      have hi (i : Fin 3) : 0 ≤ (2*(a.p i:ℝ)-a.t i)^2+3*a.p i := by positivity
      have hsum : 0 ≤ ∑ i : Fin 3, ((2*(a.p i:ℝ)-a.t i)^2+3*a.p i) :=
        Finset.sum_nonneg (fun i _ => hi i)
      refine ⟨by positivity,fun hz => Or.inr ⟨hc1,?_⟩⟩
      intro i
      have hh := Finset.single_le_sum (f := fun k : Fin 3 =>
        (2*(a.p k:ℝ)-a.t k)^2+3*a.p k) (fun k _ => hi k) (Finset.mem_univ i)
      have hp : a.p i=0 := by
        have hn : (0:ℝ) ≤ a.p i := Nat.cast_nonneg _
        have hz' : (a.p i:ℝ)=0 := by nlinarith only [hh,hz,hn,sq_nonneg (2*(a.p i:ℝ)-a.t i)]
        exact_mod_cast hz'
      refine ⟨hp,?_⟩
      simp only [hp,Nat.cast_zero,mul_zero,add_zero,zero_sub,neg_sq] at hh
      have ht' : (a.t i:ℝ)=0 := by nlinarith only [hh,hz,sq_nonneg (a.t i:ℝ)]
      exact_mod_cast ht'
    · have hc : (2:ℝ) ≤ a.c := by
        have hh : 2 ≤ a.c := by omega
        exact_mod_cast hh
      have hh := slack_pos_of_two_le a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)
        hc (fun i => by positivity)
      exact ⟨hh.le,fun hz => (ne_of_gt hh hz).elim⟩

def FaceResidue (a : TailTuple) : Prop :=
  (a.c=0 ∧ ∀ i, a.h i=0 ∨ a.h i=2) ∨ (a.c=1 ∧ ∀ i, a.h i=1)

 theorem full_zero_face_residue {D : ℕ} {a : TailTuple} (ha : TailFeasible D true a)
    (hu : a.u=a.c) (hv : a.v=0) (hz : tailSlack D true a=0) : FaceResidue a := by
  rcases (integer_slack_classification ha hu hv).2 hz with ⟨hc,hh⟩ | ⟨hc,hh⟩
  · left; refine ⟨hc,fun i => ?_⟩
    rcases hh i with ⟨hp,ht⟩ | ⟨hp,ht⟩
    · left; simp only [TailTuple.h,TailTuple.s,hc,hp,ht]
    · right; simp only [TailTuple.h,TailTuple.s,hc,hp,ht]
  · right; refine ⟨hc,fun i => ?_⟩
    simp only [TailTuple.h,TailTuple.s,hc,(hh i).1,(hh i).2]

 theorem lower_zero_face_residue {D : ℕ} {a : TailTuple}
    (ha : TailFeasible D false a) (hz : tailSlack D false a=0) : FaceResidue a := by
  obtain ⟨k,hk⟩ := a.exists_max
  have hsk (i : Fin 3) : a.s i ≤ a.s k := by
    have hh := a.h_le_max i
    rw [hk] at hh
    exact Nat.le_of_add_le_add_left hh
  have hh := (lower_active_slack D a.c a.s k (triangular (a.maxH/2:ℕ)) ha.2.1 ha.1 hsk
    (by rw [hk]; rfl)).2.2 hz
  left; refine ⟨hh.1,fun i => ?_⟩
  by_cases hik : i=k
  · subst i; simpa only [TailTuple.h,hh.1,zero_add] using hh.2.2
  · left; simp only [TailTuple.h,hh.1,hh.2.1 i hik,add_zero]

 theorem FaceResidue.one_iff {a : TailTuple} (ha : FaceResidue a) (i k : Fin 3) :
    a.h i=1 ↔ a.h k=1 := by
  rcases ha with ⟨_,hh⟩ | ⟨_,hh⟩
  · have hi := hh i; have hk := hh k
    constructor <;> intro h <;> omega
  · rw [hh i,hh k]
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators
 theorem pair_incidence_card : ∀ e : Fin 33,
    (Finset.univ.filter fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e).card=2 := by decide
 theorem sum_face_pairs (f : Fin 33 → ℝ) :
    (∑ j : Fin 22, ∑ k : Fin 3, f (facePair j k))=2*∑ e, f e := by
  rw [←Fintype.sum_prod_type (fun p : Fin 22 × Fin 3 => f (facePair p.1 p.2))]
  rw [←Finset.sum_fiberwise Finset.univ (fun p : Fin 22 × Fin 3 => facePair p.1 p.2)]
  have he (e : Fin 33) : (∑ p ∈ Finset.univ.filter (fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e),
      f (facePair p.1 p.2))=2*f e := by
    calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e), f e := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(Finset.mem_filter.mp hp).2]
         _ = _ := by rw [Finset.sum_const,pair_incidence_card]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [he]
  rw [Finset.mul_sum]

 theorem residue_root_zero (h : Fin 33 → ℕ) (he : separationExcess h=0) : h 0=0 := by
  have hh := separationExcess_root h
  rw [he] at hh
  have h0 : (h 0:ℝ)=0 := by nlinarith [sq_nonneg (h 0:ℝ)]
  exact_mod_cast h0

 theorem residue_propagation (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ)
    (hh : ∀ j k, (a j).h k=h (facePair j k)) (ha : ∀ j, FaceResidue (a j))
    (hroot : h 0=0) : ∀ e, h e ≠ 1 := by
  have hstep (e : Fin 33) : h e=1 ↔ h (pairParent e)=1 := by
    obtain ⟨i,hi⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) (pairParent e)).mp (pairBridge_parent e)
    have hs := (ha (pairBridge e)).one_iff i k
    rw [hh,hh,hi,hk] at hs
    exact hs
  have hmain : ∀ m, ∀ e : Fin 33, e.val=m → h e≠1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro e hem he
      by_cases he0 : e=0
      · subst e; omega
      · have hp : (pairParent e).val < m := by simpa only [hem] using pairParent_lt e he0
        exact ih (pairParent e).val hp (pairParent e) rfl ((hstep e).mp he)
  intro e
  exact hmain e.val e rfl

/-- The exact nonsaving residue of the singular-tail exponent calculation,
uniform over all corner activity patterns when D is large enough. -/
 theorem uniform_tail_dichotomy : ∃ D₀ : ℕ, ∀ D ≥ D₀,
    ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
    GlobalTailFeasible D full a h →
    (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0 →
    (∀ j, (a j).c=0) ∧ (∀ e, h e=0 ∨ h e=2) ∧
    (∀ j, tailSlack D (full j) (a j)=0) ∧ separationExcess h=0 ∧
    (∑ j, tailGain D (full j) (a j))=(2/3:ℝ)*∑ e, triangular (h e) := by
  obtain ⟨D₀,hD₀⟩ := eventually_integer_regime
  refine ⟨D₀,?_⟩
  intro D hD full a h ha htotal
  have hreg := hD₀ D hD full a h ha htotal
  have hn (j : Fin 22) : 0 ≤ tailSlack D (full j) (a j) := by
    cases hj : full j with
    | false => exact tailSlack_lower_nonneg (by simpa only [hj] using ha.1 j)
    | true => exact (integer_slack_classification (by simpa only [hj] using ha.1 j)
        (hreg j hj).1 (hreg j hj).2).1
  have hsn : 0 ≤ ∑ j, tailSlack D (full j) (a j) := Finset.sum_nonneg (fun j _ => hn j)
  have he : separationExcess h=0 := by linarith [separationExcess_nonneg h]
  have hsz : (∑ j, tailSlack D (full j) (a j))=0 := by linarith
  have hz (j : Fin 22) : tailSlack D (full j) (a j)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hsz j (Finset.mem_univ j)
  have hr (j : Fin 22) : FaceResidue (a j) := by
    cases hj : full j with
    | false => exact lower_zero_face_residue (by simpa only [hj] using ha.1 j) (by simpa only [hj] using hz j)
    | true =>
        exact full_zero_face_residue (by simpa only [hj] using ha.1 j)
          (hreg j hj).1 (hreg j hj).2 (by simpa only [hj] using hz j)
  have hnone := residue_propagation a h ha.2 hr (residue_root_zero h he)
  have hface (j : Fin 22) : (a j).c=0 ∧ ∀ k, (a j).h k=0 ∨ (a j).h k=2 := by
    rcases hr j with hh | ⟨_hc,hh⟩
    · exact hh
    · exact (hnone (facePair j 0) (by rw [←ha.2]; exact hh 0)).elim
  refine ⟨fun j => (hface j).1,?_,hz,he,?_⟩
  · intro e
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    have hh := (hface (pairBridge e)).2 k
    rwa [ha.2,hk] at hh
  · have hg (j : Fin 22) : tailGain D (full j) (a j)=
        (1/3:ℝ)*∑ k, triangular (h (facePair j k)) := by
      have hh := sub_eq_zero.mp (hz j)
      change faceBaseline D (a j).c (fun k => (a j).s k)=tailGain D (full j) (a j) at hh
      rw [←hh]
      have hk (k : Fin 3) : (a j).s k=h (facePair j k) := by
        have hk := ha.2 j k
        simpa only [TailTuple.h,(hface j).1,zero_add] using hk
      simp only [faceBaseline,(hface j).1,Nat.cast_zero,mul_zero,zero_add,hk]
      ring
    simp_rw [hg]
    rw [←Finset.mul_sum,sum_face_pairs (fun e => triangular (h e))]
    ring
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators

def plantedTailTuple (D r c : ℕ) (s : Fin 3 → ℕ)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) : TailTuple where
  c := c
  u := u.val.val
  v := D-c-θ.val.2.2.2.val
  p := ![θ.val.1.val,θ.val.2.1.val,θ.val.2.2.1.val]
  t := ![s 0-θ.val.1.val,s 1-θ.val.2.1.val,s 2-θ.val.2.2.1.val]

theorem plantedTailTuple_s (D r c : ℕ) (s : Fin 3 → ℕ)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) (i : Fin 3) :
    (plantedTailTuple D r c s u θ).s i = s i := by
  have h := θ.property
  unfold BaseFeasible at h
  fin_cases i <;> simp [plantedTailTuple,TailTuple.s] <;> omega

theorem plantedTailTuple_feasible (D r c : ℕ) (hD : D=2*r) (hc : c ≤ D)
    (s : Fin 3 → ℕ) (hs : (∑ i, s i) ≤ D-c)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) :
    TailFeasible D true (plantedTailTuple D r c s u θ) := by
  have hu := u.property.1
  have huc : u.val.val ≤ c := Nat.le_of_lt_succ u.val.isLt
  have hθ := θ.property
  unfold BaseFeasible at hθ
  have hn : θ.val.2.2.2.val ≤ D-c := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hdc : ((D-c:ℕ):ℝ) = (D:ℝ)-c := Nat.cast_sub hc
  have hru : ((r-u.val.val:ℕ):ℝ) = (r:ℝ)-u.val.val := Nat.cast_sub hu
  have hDs : (D:ℝ)=2*r := by exact_mod_cast hD
  refine ⟨hc,?_,fun _ => ⟨huc,?_,?_,?_⟩⟩
  · change (∑ i, (plantedTailTuple D r c s u θ).s i) ≤ D-c
    simpa only [plantedTailTuple_s] using hs
  · intro i
    fin_cases i
    all_goals dsimp [plantedTailTuple,TailTuple.delta]
    · have hh := hθ.2.2.2.2.2.2.2.2.1
      have hh' : ((s 0-θ.val.1.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.1
      have hh' : ((s 1-θ.val.2.1.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.1
      have hh' : ((s 2-θ.val.2.2.1.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
  · intro i
    fin_cases i
    all_goals dsimp [plantedTailTuple,TailTuple.delta]
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.2.1
      have hh' : ((D-c-θ.val.2.2.2.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hh' : ((D-c-θ.val.2.2.2.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hh' : ((D-c-θ.val.2.2.2.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
  · have hh := hθ.2.2.2.2.1
    have hh' : (θ.val.2.2.2.val:ℝ)+(θ.val.1.val+θ.val.2.1.val+θ.val.2.2.1.val) ≤ 3*(r-u.val.val:ℕ) := by exact_mod_cast hh
    rw [hru] at hh'
    simp only [plantedTailTuple,TailTuple.delta,TailTuple.P,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Nat.cast_sub hn,hdc]
    linarith

noncomputable def fullPlantedExponent (D c r : ℕ) (s : Fin 3 → ℕ)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) : ℝ :=
  ((D:ℝ)+1)*c+(∑ i, triangular (s i))+3*triangular r-4*triangular D+
    isotropicExponent D c+(u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
    3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ)+
    reducedPlantedExponent (D-c) (r-u.val.val) (s 0) (s 1) (s 2) θ.val

theorem fullPlantedExponent_eq (D c r : ℕ) (hD : D=2*r) (hc : c ≤ D)
    (s : Fin 3 → ℕ) (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) :
    fullPlantedExponent D c r s u θ = tailGain D true (plantedTailTuple D r c s u θ) := by
  have hu := u.property.1
  have huc : u.val.val ≤ c := Nat.le_of_lt_succ u.val.isLt
  have huD : u.val.val ≤ D := huc.trans hc
  have hθ := θ.property
  unfold BaseFeasible at hθ
  have hn : θ.val.2.2.2.val ≤ D-c := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hiso : (isotropicExponent D c:ℝ) + triangular (D-c:ℕ) = triangular D+(c:ℝ)*(D-c:ℕ) := by
    have hh := congrArg (Nat.cast : ℕ → ℝ) (isotropicExponent_add D c hc)
    simpa only [Nat.cast_add,Nat.cast_mul,triangular_nat] using hh
  have hDs : (D:ℝ)=2*r := by exact_mod_cast hD
  have h0 : θ.val.1.val ≤ s 0 := hθ.2.2.2.2.2.1
  have h1 : θ.val.2.1.val ≤ s 1 := hθ.2.2.2.2.2.2.1
  have h2 : θ.val.2.2.1.val ≤ s 2 := hθ.2.2.2.2.2.2.2.1
  unfold fullPlantedExponent tailGain plantedGain plantedTailTuple TailTuple.delta reducedPlantedExponent
  simp only [ite_true,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Nat.cast_add,triangular_nat,Nat.cast_sub hn,Nat.cast_sub hc,
    Nat.cast_sub hu,Nat.cast_sub huc,Nat.cast_sub huD,Nat.cast_sub h0,Nat.cast_sub h1,Nat.cast_sub h2]
  rw [Nat.cast_sub hc] at hiso
  dsimp [triangular] at hiso ⊢
  rw [show (isotropicExponent D c:ℝ) = _ from (eq_sub_iff_add_eq.mpr hiso)]
  rw [hDs]
  ring

end SidorenkoCounterexample

end OAI
