import OAI.Combinatorics.PerfectMatching.DyadicEnvelope

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

lemma concave_affine_chord {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {l u t p c : ℝ} (hl : l∈S) (hu : u∈S) (hlu : l<u) (ht : t∈Set.Icc l u)
    (hfl : f l=p*l+c) (hfu : f u=p*u+c) : p*t+c≤f t := by
  let b := (t-l)/(u-l)
  have hd : 0<u-l := sub_pos.mpr hlu
  have hb : 0≤b := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hb1 : b≤1 := (div_le_one hd).2 (by linarith [ht.2])
  have he : (1-b)*l+b*u=t := by dsimp [b]; field_simp; ring
  have hc := hf.2 hl hu (sub_nonneg.mpr hb1) hb (sub_add_cancel 1 b)
  simp only [smul_eq_mul] at hc
  rw [he,hfl,hfu] at hc
  calc
    p*t+c=(1-b)*(p*l+c)+b*(p*u+c) := by rw [←he]; ring
    _ ≤ f t := hc

lemma psiReal_on_first (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 (dyadic k)) :
    psiReal k t=(k:ℝ)*t := by
  apply le_antisymm
  · simpa only [first_eval] using psiReal_le_piece k t _ (first_mem_pieces k)
  · simpa only [add_zero] using concave_affine_chord (psiReal_concave k)
      (Set.mem_univ 0) (Set.mem_univ (dyadic k)) (dyadic_pos k) ht
      (p:=(k:ℝ)) (c:=0) (by simp [psiReal_zero]) (by rw [psiReal_knot k k le_rfl]; ring)

lemma psiReal_on_chord (k j : ℕ) (hj : j<k) {t : ℝ}
    (ht : t∈Set.Icc (dyadic (j+1)) (dyadic j)) :
    psiReal k t=((j:ℝ)-1)*t+dyadic j := by
  apply le_antisymm
  · simpa only [chord_eval] using psiReal_le_piece k t _ (chord_mem_pieces k j hj)
  · apply concave_affine_chord (psiReal_concave k) (Set.mem_univ _) (Set.mem_univ _)
      (show dyadic (j+1)<dyadic j by rw [dyadic_succ]; linarith [dyadic_pos j]) ht
    · rw [psiReal_knot k (j+1) hj,dyadic_succ,Nat.cast_add,Nat.cast_one]; ring
    · rw [psiReal_knot k j hj.le]; ring

lemma dyadic_cover (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    t≤dyadic k ∨ ∃ j<k,t∈Set.Icc (dyadic (j+1)) (dyadic j) := by
  induction k with
  | zero => exact Or.inl (by simpa only [dyadic_zero] using ht.2)
  | succ k ih =>
    by_cases h : t≤dyadic (k+1)
    · exact Or.inl h
    · right
      rcases ih with h'|⟨j,hj,hjt⟩
      · exact ⟨k,Nat.lt_succ_self k,le_of_not_ge h,h'⟩
      · exact ⟨j,Nat.lt_succ_of_lt hj,hjt⟩

def phi (t : ℝ) : ℝ := Real.negMulLog t / Real.log 2

lemma log_two_pos : 0<Real.log 2 := Real.log_pos (by norm_num)
lemma half_le_log_two : (1/2:ℝ)≤Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<2⁻¹ by norm_num)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

lemma log_dyadic (j : ℕ) : Real.log (dyadic j)=-(j:ℝ)*Real.log 2 := by
  simp [dyadic,Real.log_pow,Real.log_inv]

lemma phi_dyadic (j : ℕ) : phi (dyadic j)=(j:ℝ)*dyadic j := by
  simp only [phi,Real.negMulLog_def,log_dyadic]
  field_simp [log_two_pos.ne']

lemma phi_zero : phi 0=0 := by simp [phi]

lemma phi_concave : ConcaveOn ℝ (Set.Ici 0) phi := by
  refine ⟨convex_Ici 0,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := Real.concaveOn_negMulLog.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have hd := div_le_div_of_nonneg_right hh log_two_pos.le
  simpa only [phi,add_div,mul_div_assoc] using hd

lemma phi_le_one {t : ℝ} (ht : t∈Set.Icc 0 1) : phi t≤1 := by
  have hp : (fun b : Bool => if b then t else 1-t) ∈ MatchingEntropy.probabilitySimplex Bool := by
    constructor
    · intro b; cases b <;> simp [ht.1,sub_nonneg.mpr ht.2]
    · simp
  have hh := MatchingEntropy.entropy_le_log_card hp
  simp only [MatchingEntropy.entropy,Fintype.sum_bool,Fintype.card_bool,Bool.false_eq_true,
    ↓reduceIte,Nat.cast_ofNat] at hh
  have hn := Real.negMulLog_nonneg (sub_nonneg.mpr ht.2) (by linarith [ht.1] : 1-t≤1)
  unfold phi
  apply (div_le_one log_two_pos).2
  linarith

lemma phi_mul (u v : ℝ) : phi (u*v)=v*phi u+u*phi v := by
  simp only [phi,Real.negMulLog_mul]; ring

lemma phi_lower_first (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 (dyadic k)) :
    (k:ℝ)*t ≤ phi t := by
  simpa only [add_zero] using concave_affine_chord phi_concave
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (dyadic_nonneg k)) (dyadic_pos k) ht
    (p:=(k:ℝ)) (c:=0) (by simp [phi_zero]) (by rw [phi_dyadic]; ring)

lemma phi_lower_chord (j : ℕ) {t : ℝ} (ht : t∈Set.Icc (dyadic (j+1)) (dyadic j)) :
    ((j:ℝ)-1)*t+dyadic j≤phi t := by
  apply concave_affine_chord phi_concave (Set.mem_Ici.mpr (dyadic_nonneg _))
    (Set.mem_Ici.mpr (dyadic_nonneg _))
    (show dyadic (j+1)<dyadic j by rw [dyadic_succ]; linarith [dyadic_pos j]) ht
  · rw [phi_dyadic,dyadic_succ,Nat.cast_add,Nat.cast_one]; ring
  · rw [phi_dyadic]; ring

lemma phi_upper_chord (j : ℕ) {t : ℝ} (ht : t∈Set.Icc (dyadic (j+1)) (dyadic j)) :
    phi t≤((j:ℝ)+1)*t := by
  have ht0 : 0<t := (dyadic_pos _).trans_le ht.1
  have hh := Real.log_le_log (dyadic_pos (j+1)) ht.1
  rw [log_dyadic,Nat.cast_add,Nat.cast_one] at hh
  unfold phi
  apply (div_le_iff₀ log_two_pos).2
  rw [Real.negMulLog_def]
  nlinarith [mul_le_mul_of_nonneg_left hh ht0.le]

lemma phi_error_first (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 (dyadic k)) :
    phi t-(k:ℝ)*t≤dyadic k := by
  let r := t/dyadic k
  have hr : r∈Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg ht.1 (dyadic_nonneg k),(div_le_one (dyadic_pos k)).2 ht.2⟩
  have he : dyadic k*r=t := by dsimp [r]; field_simp [ne_of_gt (dyadic_pos k)]
  have hh := phi_mul (dyadic k) r
  rw [he,phi_dyadic] at hh
  have hu := mul_le_mul_of_nonneg_left (phi_le_one hr) (dyadic_nonneg k)
  nlinarith [hh,he]

theorem dyadic_entropy_error (k : ℕ) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    0≤phi t-psiReal k t ∧ phi t-psiReal k t≤t+dyadic k := by
  rcases dyadic_cover k ht with h|⟨j,hj,hjt⟩
  · rw [psiReal_on_first k ⟨ht.1,h⟩]
    exact ⟨sub_nonneg.mpr (phi_lower_first k ⟨ht.1,h⟩),
      (phi_error_first k ⟨ht.1,h⟩).trans (by linarith [ht.1])⟩
  · rw [psiReal_on_chord k j hj hjt]
    have hlo := phi_lower_chord j hjt
    have hhi := phi_upper_chord j hjt
    have hd := dyadic_nonneg k
    constructor <;> linarith [hjt.2]

end
end BinaryMatching.Algorithm
end

end OAI
