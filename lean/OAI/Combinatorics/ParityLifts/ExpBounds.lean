import OAI.Combinatorics.ParityLifts.SparseCertificate

namespace OAI

namespace ParityWL.Complexity
open Filter Topology

def ExpBound (f : ℕ → ℝ) (r : ℝ) : Prop :=
  (∀ n, 0 ≤ f n) ∧ ∃ C : ℝ, 0<C ∧ ∃ d : ℕ, ∀ n,
    f n ≤ C*(n+1 : ℝ)^d*2^(r*n)

lemma ExpBound.const (C : ℝ) (hC : 0 ≤ C) : ExpBound (fun _ => C) 0 := by
  refine ⟨fun _ => hC, C+1,by positivity,0,?_⟩
  intro n
  simp only [pow_zero,zero_mul,Real.rpow_zero,mul_one]
  linarith

lemma ExpBound.poly (d : ℕ) : ExpBound (fun n => (n+1 : ℝ)^d) 0 := by
  refine ⟨by intro n; positivity,1,by norm_num,d,?_⟩
  intro n; simp

lemma ExpBound.exp (r : ℝ) : ExpBound (fun n => (2 : ℝ)^(r*n)) r := by
  exact ⟨fun _ => (Real.rpow_pos_of_pos (by norm_num) _).le,1,by norm_num,0,by intro n; simp⟩

lemma ExpBound.mono {f g : ℕ → ℝ} {r : ℝ} (h : ExpBound f r)
    (hg : ∀ n,0 ≤ g n) (hle : ∀ n,g n ≤ f n) : ExpBound g r := by
  obtain ⟨_,C,hC,d,h⟩ := h
  exact ⟨hg,C,hC,d,fun n => (hle n).trans (h n)⟩

lemma ExpBound.mul {f g : ℕ → ℝ} {r s : ℝ} (hf : ExpBound f r) (hg : ExpBound g s) :
    ExpBound (fun n => f n*g n) (r+s) := by
  obtain ⟨hf0,C,hC,d,hf⟩ := hf
  obtain ⟨hg0,D,hD,e,hg⟩ := hg
  refine ⟨fun n => mul_nonneg (hf0 n) (hg0 n),C*D,mul_pos hC hD,d+e,?_⟩
  intro n
  calc
    _  ≤  (C*(n+1 : ℝ)^d*2^(r*n))*(D*(n+1 : ℝ)^e*2^(s*n)) :=
      mul_le_mul (hf n) (hg n) (hg0 n) (by positivity)
    _ = _ := by rw [add_mul,Real.rpow_add (by norm_num),pow_add]; ring

lemma ExpBound.mono_rate {f : ℕ → ℝ} {r s : ℝ} (h : ExpBound f r) (hrs : r ≤ s) :
    ExpBound f s := by
  obtain ⟨hn,C,hC,d,h⟩ := h
  refine ⟨hn,C,hC,d,?_⟩
  intro n
  apply (h n).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hrs (Nat.cast_nonneg n))

lemma ExpBound.add_same {f g : ℕ → ℝ} {r : ℝ} (hf : ExpBound f r) (hg : ExpBound g r) :
    ExpBound (fun n => f n+g n) r := by
  obtain ⟨hf0,C,hC,d,hf⟩ := hf
  obtain ⟨hg0,D,hD,e,hg⟩ := hg
  refine ⟨fun n => add_nonneg (hf0 n) (hg0 n),C+D,add_pos hC hD,d+e,?_⟩
  intro n
  have hb : (1 : ℝ) ≤ n+1 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
  have hd : (n+1 : ℝ)^d ≤ (n+1 : ℝ)^(d+e) := pow_le_pow_right₀ hb (by omega)
  have he : (n+1 : ℝ)^e ≤ (n+1 : ℝ)^(d+e) := pow_le_pow_right₀ hb (by omega)
  have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hC.le)
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (r*n))
  have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hD.le)
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (r*n))
  nlinarith [hf n,hg n]

lemma ExpBound.add {f g : ℕ → ℝ} {r s : ℝ} (hf : ExpBound f r) (hg : ExpBound g s)
    (hr : 0 ≤ r) (hs : 0 ≤ s) : ExpBound (fun n => f n+g n) (r+s) :=
  (hf.mono_rate (by linarith)).add_same (hg.mono_rate (by linarith))

lemma ExpBound.pow {f : ℕ → ℝ} {r : ℝ} (hf : ExpBound f r) (d : ℕ) :
    ExpBound (fun n => f n^d) (d*r) := by
  induction d with
  | zero => simpa using ExpBound.const 1 (by norm_num)
  | succ d ih =>
    convert ih.mul hf using 1 <;> simp [pow_succ,Nat.cast_add,Nat.cast_one,add_mul]

lemma polynomial_absorb (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, (n+1 : ℝ)^d ≤ C*(2 : ℝ)^(ε*n) := by
  let a := ε*Real.log 2
  have ha : 0<a := mul_pos hε (Real.log_pos (by norm_num))
  have hsmall := (isLittleO_pow_exp_pos_mul_atTop d ha).bound (by norm_num : (0 : ℝ)<1)
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hevent := ht.eventually hsmall
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hevent
  let C := Real.exp a+(N+1 : ℝ)^d
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro n
  have hp : (1 : ℝ) ≤ 2^(ε*n) := Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hn : N ≤ n
  · have h := hN n hn
    simp only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (n+1 : ℝ)^d by positivity),
      abs_of_pos (Real.exp_pos _),one_mul] at h
    have he : Real.exp (a*((n : ℝ)+1))=Real.exp a*2^(ε*n) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      rw [←Real.exp_add]
      congr 1
      dsimp [a]; ring
    rw [he] at h
    apply h.trans
    gcongr
    dsimp [C]; exact le_add_of_nonneg_right (by positivity)
  · have hpow : (n+1 : ℝ)^d ≤ (N+1 : ℝ)^d := by gcongr; exact_mod_cast (show n ≤ N by omega)
    calc
      _  ≤  (N+1 : ℝ)^d := hpow
      _  ≤  C := by dsimp [C]; exact le_add_of_nonneg_left (Real.exp_pos a).le
      _  ≤  C*2^(ε*n) := le_mul_of_one_le_right (by dsimp [C]; positivity) hp

lemma ExpBound.absorb {f : ℕ → ℝ} {r : ℝ} (hf : ExpBound f r) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ n, f n ≤ C*(2 : ℝ)^((r+ε)*n) := by
  obtain ⟨_,A,hA,d,hf⟩ := hf
  obtain ⟨B,hB,hp⟩ := polynomial_absorb d ε hε
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro n
  calc
    _  ≤  A*(n+1 : ℝ)^d*2^(r*n) := hf n
    _  ≤  A*(B*2^(ε*n))*2^(r*n) := by gcongr; exact hp n
    _ = _ := by rw [add_mul,Real.rpow_add (by norm_num)]; ring
end ParityWL.Complexity

end OAI
