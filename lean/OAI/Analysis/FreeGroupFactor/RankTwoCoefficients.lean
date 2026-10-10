import OAI.Analysis.FreeGroupFactor.RankTwoCounting

namespace OAI

noncomputable section

universe uG uH uK uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain

namespace RankTwo

def tupleSphere (m l : ℕ) : Finset (Fin l → Fin m) :=
  Finset.univ.filter (fun x => List.ofFn x ∈ Radial.sphere l)

theorem tupleSphere_image (m l : ℕ) :
    (tupleSphere m l).image List.ofFn = Radial.sphere l := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hx).2
  · intro hw
    have hl := Radial.sphere_mem_length l hw
    subst l
    refine Finset.mem_image.mpr ⟨w.get,?_,List.ofFn_get w⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [List.ofFn_get] using hw⟩

theorem shell_eq_tuple (m l : ℕ) (b : Bool) :
    Radial.shell (ι := Fin m) b l =
      ∑ x ∈ tupleSphere m l, Finsupp.single (patternWord (alternating b l) x) (1 : ℝ) := by
  classical
  unfold Radial.shell
  rw [← tupleSphere_image,Finset.sum_image (fun _ _ _ _ he => List.ofFn_injective he)]
  simp only [vertex_ofFn]

theorem pair_push_pattern_le {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset (Fin l → Fin m)) (t : Finset (Fin k → Fin m)) :
    coefficientPair
        (pushCoefficients (prefixHom B m) (∑ x ∈ s, Finsupp.single (patternWord b x) 1))
        (pushCoefficients (prefixHom B m) (∑ y ∈ t, Finsupp.single (patternWord c y) 1)) ≤
      (m : ℝ)^r * r^r := by
  classical
  simp only [map_sum,pushCoefficients_single]
  rw [coefficientPair_shells]
  have hh := card_patternCollisions_le hB hb b c eP eN hc
    ((s ×ˢ t).filter (fun p => prefixHom B m (patternWord b p.1) = prefixHom B m (patternWord c p.2)))
    (fun p hp => (Finset.mem_filter.mp hp).2)
  convert (Nat.cast_le (α := ℝ)).mpr hh using 1
  all_goals push_cast
  all_goals (first | rfl | congr 4)

theorem pair_push_pattern_le_free_add {m l k B r : ℕ} (hB : m*(l+k) < B) (hb : 2 ≤ B)
    (b : Fin l → Bool) (c : Fin k → Bool)
    (eP : Fin r ≃ {i // pairColors b c i = true})
    (eN : Fin r ≃ {i // pairColors b c i = false})
    (hc : ∑ i, boolSign (b i) = ∑ j, boolSign (c j))
    (s : Finset (Fin l → Fin m)) (t : Finset (Fin k → Fin m)) :
    coefficientPair
        (pushCoefficients (prefixHom B m) (∑ x ∈ s, Finsupp.single (patternWord b x) 1))
        (pushCoefficients (prefixHom B m) (∑ y ∈ t, Finsupp.single (patternWord c y) 1)) ≤
      coefficientPair (∑ x ∈ s, Finsupp.single (patternWord b x) 1)
        (∑ y ∈ t, Finsupp.single (patternWord c y) 1) + (r^2*r^r : ℝ)*m^(r-1) := by
  classical
  simp only [map_sum,pushCoefficients_single]
  rw [coefficientPair_shells,coefficientPair_shells]
  convert (Nat.cast_le (α := ℝ)).mpr (card_patternCollisions_le_free_add hB hb b c eP eN hc (s ×ˢ t)) using 1
  all_goals push_cast
  all_goals (first | rfl | congr 4)

theorem right_pairColors_card (k : ℕ) (d : Bool) :
    Fintype.card {i // pairColors (alternating false (2*k+1)) (alternating false (2*k+1)) i = d} =
      2*k+1 := by
  cases d
  · rw [card_pairColors_neg]
    simp only [card_alternating_pos,card_alternating_neg,positiveCount_odd,Bool.false_eq_true,
      ↓reduceIte,zero_add]
    omega
  · rw [card_pairColors_pos]
    simp only [card_alternating_pos,card_alternating_neg,positiveCount_odd,Bool.false_eq_true,
      ↓reduceIte,zero_add]
    omega

theorem positiveCount_even_add_two (b : Bool) (k : ℕ) : positiveCount b (2*k+2) = k+1 := by
  rw [positiveCount_two,positiveCount_even]
  omega

theorem left_pairColors_card (k l : ℕ) (d : Bool) :
    Fintype.card {i // pairColors (alternating true (2*k+2)) (alternating true (2*l+2)) i = d} =
      k+l+2 := by
  cases d
  · rw [card_pairColors_neg]
    simp only [card_alternating_pos,card_alternating_neg,positiveCount_even_add_two]
    omega
  · rw [card_pairColors_pos]
    simp only [card_alternating_pos,card_alternating_neg,positiveCount_even_add_two]
    omega

theorem pair_shell_right_le {m k B : ℕ} (hB : m*((2*k+1)+(2*k+1)) < B) (hb : 2 ≤ B) :
    coefficientPair (pushCoefficients (prefixHom B m) (Radial.shell false (2*k+1)))
      (pushCoefficients (prefixHom B m) (Radial.shell false (2*k+1))) ≤
      (m : ℝ)^(2*k+1) * (2*k+1 : ℝ)^(2*k+1) := by
  let eP : Fin (2*k+1) ≃ {i // pairColors (alternating false (2*k+1)) (alternating false (2*k+1)) i = true} :=
    (Fintype.equivFinOfCardEq (right_pairColors_card k true)).symm
  let eN : Fin (2*k+1) ≃ {i // pairColors (alternating false (2*k+1)) (alternating false (2*k+1)) i = false} :=
    (Fintype.equivFinOfCardEq (right_pairColors_card k false)).symm
  rw [shell_eq_tuple m _ false]
  convert pair_push_pattern_le hB hb _ _ eP eN rfl (tupleSphere m _) (tupleSphere m _) using 1
  all_goals push_cast
  all_goals rfl

theorem pair_shell_left_le_free_add {m k l B : ℕ} (hB : m*((2*k+2)+(2*l+2)) < B) (hb : 2 ≤ B) :
    coefficientPair (pushCoefficients (prefixHom B m) (Radial.shell true (2*k+2)))
      (pushCoefficients (prefixHom B m) (Radial.shell true (2*l+2))) ≤
      coefficientPair (Radial.shell (ι := Fin m) true (2*k+2)) (Radial.shell true (2*l+2)) +
        ((k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2))*(m : ℝ)^(k+l+1) := by
  let eP : Fin (k+l+2) ≃ {i // pairColors (alternating true (2*k+2)) (alternating true (2*l+2)) i = true} :=
    (Fintype.equivFinOfCardEq (left_pairColors_card k l true)).symm
  let eN : Fin (k+l+2) ≃ {i // pairColors (alternating true (2*k+2)) (alternating true (2*l+2)) i = false} :=
    (Fintype.equivFinOfCardEq (left_pairColors_card k l false)).symm
  have hc : ∑ i, boolSign (alternating true (2*k+2) i) = ∑ i, boolSign (alternating true (2*l+2) i) := by
    rw [alternating_charge,alternating_charge,positiveCount_even_add_two,positiveCount_even_add_two]
    push_cast
    ring
  rw [shell_eq_tuple m _ true,shell_eq_tuple m _ true]
  convert pair_push_pattern_le_free_add hB hb _ _ eP eN hc (tupleSphere m _) (tupleSphere m _) using 1
  all_goals push_cast
  all_goals rfl

end RankTwo

theorem coefficientPair_nonneg {G : Type uG} (h k : G →₀ ℝ)
    (hh : ∀ g, 0 ≤ h g) (hk : ∀ g, 0 ≤ k g) : 0 ≤ coefficientPair h k := by
  exact Finset.sum_nonneg (fun g _ => mul_nonneg (hh g) (hk g))

theorem coefficientPair_eq_zero_of_disjoint {G : Type uG} (h k : G →₀ ℝ)
    (hd : Disjoint h.support k.support) : coefficientPair h k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro g hg
  have hk : k g = 0 := by
    by_contra hn
    exact Finset.disjoint_left.mp hd hg (Finsupp.mem_support_iff.mpr hn)
  simp [hk]

theorem pushCoefficients_nonneg {G : Type uG} {H : Type uH} [Group G] [Group H]
    (f : G →* H) (h : G →₀ ℝ) (hh : ∀ g, 0 ≤ h g) (a : H) :
    0 ≤ pushCoefficients f h a := by
  classical
  change 0 ≤ Finsupp.mapDomain f h a
  rw [Finsupp.mapDomain,Finsupp.sum_apply]
  apply Finset.sum_nonneg
  intro g _
  change 0 ≤ Finsupp.single (f g) (h g) a
  rw [Finsupp.single_apply]
  split_ifs
  · exact hh g
  · rfl

namespace RankTwo

def shellWeight (m k : ℕ) : ℝ := 1 / ((m : ℝ)*((m : ℝ)-1)^k)

theorem shellWeight_nonneg {m : ℕ} (hm : 2 ≤ m) (k : ℕ) : 0 ≤ shellWeight m k := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 ≤ (m : ℝ)-1 := by linarith
  unfold shellWeight
  positivity

theorem shellWeight_product_bound {m : ℕ} (hm : 2 ≤ m) (k l : ℕ) :
    shellWeight m k * shellWeight m l * (m : ℝ)^(k+l+1) ≤ 2^(k+l)/(m : ℝ) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < m := by linarith
  have hq : (0 : ℝ) < (m : ℝ)-1 := by linarith
  have he : shellWeight m k * shellWeight m l * (m : ℝ)^(k+l+1) =
      ((m : ℝ)/((m : ℝ)-1))^(k+l)/(m : ℝ) := by
    simp only [shellWeight,pow_succ,pow_add,div_pow]
    field_simp
  rw [he]
  apply div_le_div_of_nonneg_right _ hp.le
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ hq).mpr
  linarith

def rightConstant (k : ℕ) : ℝ := 2^(2*k)*(2*k+1 : ℝ)^(2*k+1)
def leftConstant (k l : ℕ) : ℝ := 2^(k+l)*(k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2)

theorem pair_rightShell_le {m k B : ℕ} (hm : 2 ≤ m)
    (hB : m*((2*k+1)+(2*k+1)) < B) (hb : 2 ≤ B) :
    coefficientSqNorm (pushCoefficients (prefixHom B m) (Radial.rightShell m k)) ≤
      rightConstant k / m := by
  rw [Radial.rightShell,map_smul,coefficientSqNorm_smul,← coefficientPair_self]
  change (shellWeight m k)^2 * _ ≤ _
  calc
    _ ≤ (shellWeight m k)^2 * ((m : ℝ)^(2*k+1)*(2*k+1 : ℝ)^(2*k+1)) :=
      mul_le_mul_of_nonneg_left (pair_shell_right_le hB hb) (sq_nonneg _)
    _ = (2*k+1 : ℝ)^(2*k+1) *
        (shellWeight m k * shellWeight m k * (m : ℝ)^(k+k+1)) := by
      rw [show k+k=2*k by omega]; ring
    _ ≤ (2*k+1 : ℝ)^(2*k+1) * (2^(k+k)/(m : ℝ)) :=
      mul_le_mul_of_nonneg_left (shellWeight_product_bound hm k k) (by positivity)
    _ = _ := by rw [show k+k=2*k by omega]; unfold rightConstant; ring

theorem pair_leftShell_le_free_add {m k l B : ℕ} (hm : 2 ≤ m)
    (hB : m*((2*k+2)+(2*l+2)) < B) (hb : 2 ≤ B) :
    coefficientPair (pushCoefficients (prefixHom B m) (Radial.leftShell m k))
      (pushCoefficients (prefixHom B m) (Radial.leftShell m l)) ≤
      coefficientPair (Radial.leftShell m k) (Radial.leftShell m l) + leftConstant k l / m := by
  simp only [Radial.leftShell,map_smul,coefficientPair_smul_left,coefficientPair_smul_right]
  change shellWeight m l * (shellWeight m k * _) ≤
    shellWeight m l * (shellWeight m k * _) + _
  have hh := mul_le_mul_of_nonneg_left (pair_shell_left_le_free_add hB hb)
    (mul_nonneg (shellWeight_nonneg hm k) (shellWeight_nonneg hm l))
  have he := mul_le_mul_of_nonneg_left (shellWeight_product_bound hm k l)
    (show 0 ≤ (k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2) by positivity)
  calc
    _ = (shellWeight m k * shellWeight m l) * _ := by ring
    _ ≤ (shellWeight m k * shellWeight m l) *
        (coefficientPair (Radial.shell true (2*k+2)) (Radial.shell true (2*l+2)) +
          ((k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2))*(m : ℝ)^(k+l+1)) := hh
    _ = shellWeight m l * (shellWeight m k *
        coefficientPair (Radial.shell true (2*k+2)) (Radial.shell true (2*l+2))) +
        ((k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2)) *
          (shellWeight m k * shellWeight m l * (m : ℝ)^(k+l+1)) := by ring
    _ ≤ shellWeight m l * (shellWeight m k *
        coefficientPair (Radial.shell true (2*k+2)) (Radial.shell true (2*l+2))) +
        ((k+l+2 : ℝ)^2*(k+l+2 : ℝ)^(k+l+2)) * (2^(k+l)/(m : ℝ)) := add_le_add le_rfl he
    _ = _ := by unfold leftConstant; ring

theorem pair_leftShell_free_le {m : ℕ} (hm : 2 ≤ m) (k l : ℕ) :
    coefficientPair (Radial.leftShell m k) (Radial.leftShell m l) ≤ if k=l then 1 else 0 := by
  classical
  by_cases h : k=l
  · subst l
    rw [ite_eq_left rfl,coefficientPair_self,Radial.sqNorm_leftShell m k hm]
    have hp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    apply (div_le_iff₀ hp).mpr
    linarith
  · rw [ite_eq_right h,coefficientPair_eq_zero_of_disjoint _ _ (Radial.leftShell_disjoint m h)]

theorem leftShell_nonneg {m : ℕ} (hm : 2 ≤ m) (k : ℕ) (g : FreeGroup (Fin m)) :
    0 ≤ Radial.leftShell m k g := by
  change 0 ≤ shellWeight m k * Radial.shell true (2*k+2) g
  apply mul_nonneg (shellWeight_nonneg hm k)
  rw [Radial.shell_apply]
  split_ifs <;> norm_num

theorem pair_leftShell_push_nonneg {m B : ℕ} (hm : 2 ≤ m) (k l : ℕ) :
    0 ≤ coefficientPair (pushCoefficients (prefixHom B m) (Radial.leftShell m k))
      (pushCoefficients (prefixHom B m) (Radial.leftShell m l)) := by
  apply coefficientPair_nonneg
  · exact pushCoefficients_nonneg _ _ (leftShell_nonneg hm k)
  · exact pushCoefficients_nonneg _ _ (leftShell_nonneg hm l)

def partialConstant (N : ℕ) : ℝ := (N : ℝ)*∑ k ∈ Finset.range N, rightConstant k
def inverseConstant (N : ℕ) : ℝ :=
  (1/(N+1 : ℝ))^2*(N+1 : ℝ)*∑ k ∈ Finset.range (N+1), partialConstant (k+1)
def residualConstant (N : ℕ) : ℝ :=
  (1/(N+1 : ℝ))^2*∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1), leftConstant k l

theorem rightConstant_nonneg (k : ℕ) : 0 ≤ rightConstant k := by unfold rightConstant; positivity
theorem leftConstant_nonneg (k l : ℕ) : 0 ≤ leftConstant k l := by unfold leftConstant; positivity
theorem partialConstant_nonneg (N : ℕ) : 0 ≤ partialConstant N := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun k _ => rightConstant_nonneg k)
theorem inverseConstant_nonneg (N : ℕ) : 0 ≤ inverseConstant N := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun k _ => partialConstant_nonneg _)
theorem residualConstant_nonneg (N : ℕ) : 0 ≤ residualConstant N := by
  apply mul_nonneg (sq_nonneg _)
  exact Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => leftConstant_nonneg k l))

theorem neg_one_pow_sq (k : ℕ) : ((-1 : ℝ)^k)^2 = 1 := by
  rw [← pow_mul,Nat.mul_comm,pow_mul]
  norm_num

theorem sqNorm_push_partial_le {m N B : ℕ} (hm : 2 ≤ m)
    (hB : m*(4*N+4) < B) (hb : 2 ≤ B) (j : ℕ) (hj : j ≤ N+1) :
    coefficientSqNorm (pushCoefficients (prefixHom B m) (Radial.partialInverse m j)) ≤
      partialConstant j / m := by
  rw [Radial.partialInverse,map_sum]
  calc
    _ ≤ ((Finset.range j).card : ℝ)*∑ k ∈ Finset.range j,
        coefficientSqNorm (pushCoefficients (prefixHom B m) ((-1 : ℝ)^k • Radial.rightShell m k)) :=
      coefficientSqNorm_sum_le _ _
    _ ≤ (j : ℝ)*∑ k ∈ Finset.range j, rightConstant k / m := by
      rw [Finset.card_range]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro k hk
      rw [map_smul,coefficientSqNorm_smul,neg_one_pow_sq,one_mul]
      apply pair_rightShell_le hm _ hb
      have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
      exact lt_of_le_of_lt (Nat.mul_le_mul_left m (by omega)) hB
    _ = _ := by rw [← Finset.sum_div]; unfold partialConstant; ring

theorem sqNorm_push_inverse_le {m N B : ℕ} (hm : 2 ≤ m)
    (hB : m*(4*N+4) < B) (hb : 2 ≤ B) :
    coefficientSqNorm (pushCoefficients (prefixHom B m) (Radial.averagedInverse m N)) ≤
      inverseConstant N / m := by
  rw [Radial.averagedInverse,map_smul,coefficientSqNorm_smul,map_sum]
  calc
    _ ≤ (1/(N+1 : ℝ))^2 * (((Finset.range (N+1)).card : ℝ)*∑ k ∈ Finset.range (N+1),
        coefficientSqNorm (pushCoefficients (prefixHom B m) (Radial.partialInverse m (k+1)))) :=
      mul_le_mul_of_nonneg_left (coefficientSqNorm_sum_le _ _) (sq_nonneg _)
    _ ≤ (1/(N+1 : ℝ))^2 * ((N+1 : ℝ)*∑ k ∈ Finset.range (N+1), partialConstant (k+1)/m) := by
      simp only [Finset.card_range,Nat.cast_add,Nat.cast_one]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun k hk => sqNorm_push_partial_le hm hB hb (k+1)
        (by have := Finset.mem_range.mp hk; omega))
    _ = _ := by rw [← Finset.sum_div]; unfold inverseConstant; ring

theorem signed_left_pair_le {m B k l : ℕ} (hm : 2 ≤ m)
    (hB : m*((2*k+2)+(2*l+2)) < B) (hb : 2 ≤ B) :
    (-1 : ℝ)^k * ((-1 : ℝ)^l *
      coefficientPair (pushCoefficients (prefixHom B m) (Radial.leftShell m k))
        (pushCoefficients (prefixHom B m) (Radial.leftShell m l))) ≤
      (if k=l then (1 : ℝ) else 0) + leftConstant k l/m := by
  have hsign : (-1 : ℝ)^k*(-1 : ℝ)^l ≤ 1 := by
    rw [← pow_add]
    rcases neg_one_pow_eq_or ℝ (k+l) with h | h <;> simp [h]
  have hp := pair_leftShell_push_nonneg (B := B) hm k l
  have hsign' := mul_le_mul_of_nonneg_right hsign hp
  rw [mul_assoc,one_mul] at hsign'
  exact hsign'.trans ((pair_leftShell_le_free_add hm hB hb).trans
    (add_le_add (pair_leftShell_free_le hm k l) le_rfl))

theorem sqNorm_signed_left_sum_le {m N B : ℕ} (hm : 2 ≤ m)
    (hB : m*(4*N+4) < B) (hb : 2 ≤ B) :
    coefficientSqNorm (∑ k ∈ Finset.range (N+1), (-1 : ℝ)^k •
      pushCoefficients (prefixHom B m) (Radial.leftShell m k)) ≤
      (N+1 : ℝ) + (∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1), leftConstant k l)/m := by
  classical
  rw [← coefficientPair_self,coefficientPair_sum_left]
  simp_rw [coefficientPair_sum_right,coefficientPair_smul_left,coefficientPair_smul_right]
  calc
    _ ≤ ∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1),
        ((if k=l then (1 : ℝ) else 0) + leftConstant k l / m) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      apply signed_left_pair_le hm (B := B) (k := k) (l := l) _ hb
      have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
      have hlN : l ≤ N := by have := Finset.mem_range.mp hl; omega
      exact lt_of_le_of_lt (Nat.mul_le_mul_left m (by omega)) hB
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.sum_div]
      have hdiag : (∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1),
          if k=l then (1 : ℝ) else 0) = N+1 := by
        calc
          _ = ∑ _k ∈ Finset.range (N+1), (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [hk]
          _ = _ := by simp
      rw [hdiag]

theorem sqNorm_push_residual_le {m N B : ℕ} (hm : 2 ≤ m)
    (hB : m*(4*N+4) < B) (hb : 2 ≤ B) :
    coefficientSqNorm (pushCoefficients (prefixHom B m)
      (Radial.sumShift (Radial.averagedInverse m N) - Finsupp.single 1 1)) ≤
      1/(N+1 : ℝ)+residualConstant N/m := by
  rw [Radial.sumShift_averagedInverse m N hm,map_smul,coefficientSqNorm_smul,map_sum]
  simp_rw [map_smul]
  calc
    _ ≤ (1/(N+1 : ℝ))^2 * ((N+1 : ℝ) +
        (∑ k ∈ Finset.range (N+1), ∑ l ∈ Finset.range (N+1), leftConstant k l)/m) :=
      mul_le_mul_of_nonneg_left (sqNorm_signed_left_sum_le hm hB hb) (sq_nonneg _)
    _ = _ := by
      unfold residualConstant
      have hN : (N+1 : ℝ) ≠ 0 := by positivity
      field_simp

theorem exists_small_pushed_inverse (ε : ℝ) (hε : 0 < ε) :
    ∃ m B : ℕ, 2 ≤ m ∧ 2 ≤ B ∧ ∃ h : FreeGroup (Fin m) →₀ ℝ,
      coefficientSqNorm (pushCoefficients (prefixHom B m) h) < ε ∧
      coefficientSqNorm (pushCoefficients (prefixHom B m)
        (Radial.sumShift h-Finsupp.single 1 1)) < ε := by
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt (by positivity : 0 < ε/2)
  obtain ⟨m,hm⟩ := exists_nat_gt (max (2 : ℝ) (max (2*inverseConstant N/ε) (2*residualConstant N/ε)))
  have hm2 : 2 ≤ m := by exact_mod_cast ((le_max_left _ _).trans_lt hm).le
  have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmI : inverseConstant N/m < ε/2 := by
    apply (div_lt_iff₀ hmp).mpr
    have hh := (le_max_left (2*inverseConstant N/ε) _).trans_lt ((le_max_right _ _).trans_lt hm)
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  have hmR : residualConstant N/m < ε/2 := by
    apply (div_lt_iff₀ hmp).mpr
    have hh := (le_max_right _ (2*residualConstant N/ε)).trans_lt ((le_max_right _ _).trans_lt hm)
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  let B := m*(4*N+4)+2
  have hB : m*(4*N+4)<B := by dsimp [B]; omega
  have hb : 2 ≤ B := by dsimp [B]; omega
  refine ⟨m,B,hm2,hb,Radial.averagedInverse m N,?_,?_⟩
  · exact (sqNorm_push_inverse_le hm2 hB hb).trans_lt (hmI.trans (by linarith))
  · exact (sqNorm_push_residual_le hm2 hB hb).trans_lt (by linarith)

def twoGenerator (b : Bool) : FreeGroup (Fin 2) := FreeGroup.of (if b then 0 else 1)

def realizeSummand (b : Bool) : Multiplicative ℤ →* FreeGroup (Fin 2) where
  toFun z := twoGenerator b ^ Multiplicative.toAdd z
  map_one' := zpow_zero _
  map_mul' z w := zpow_add _ (Multiplicative.toAdd z) (Multiplicative.toAdd w)

def realize : SyllableGroup →* FreeGroup (Fin 2) := Monoid.CoprodI.lift realizeSummand

@[simp] theorem realize_syllable (b : Bool) (z : ℤ) : realize (syllable b z) = twoGenerator b ^ z := by
  simp [realize,syllable,realizeSummand]

def syllabify : FreeGroup (Fin 2) →* SyllableGroup :=
  FreeGroup.lift (fun i => if i = 0 then syllable true 1 else syllable false 1)

@[simp] theorem syllabify_generator (b : Bool) : syllabify (twoGenerator b) = syllable b 1 := by
  cases b <;> simp [syllabify,twoGenerator]

@[simp] theorem syllable_zpow (b : Bool) (z : ℤ) : (syllable b 1)^z = syllable b z := by
  unfold syllable
  rw [← map_zpow]
  congr 1
  change Multiplicative.ofAdd (z • (1 : ℤ)) = Multiplicative.ofAdd z
  simp

theorem syllabify_realize : syllabify.comp realize = MonoidHom.id _ := by
  apply Monoid.CoprodI.ext_hom
  intro b
  apply DFunLike.ext
  intro z
  change syllabify (realize (syllable b (Multiplicative.toAdd z))) = syllable b (Multiplicative.toAdd z)
  rw [realize_syllable,map_zpow,syllabify_generator,syllable_zpow]

theorem realize_injective : Function.Injective realize := by
  intro x y he
  have hh := congrArg syllabify he
  simpa only [← MonoidHom.comp_apply,syllabify_realize,MonoidHom.id_apply] using hh

end RankTwo

theorem pushCoefficients_comp {G : Type uG} {H : Type uH} {K : Type uK} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (h : G →₀ ℝ) :
    pushCoefficients (g.comp f) h = pushCoefficients g (pushCoefficients f h) := by
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h k ih ik => simp only [map_add,ih,ik]
  | single a c => simp

theorem coefficientSqNorm_shift {G : Type uG} [Group G] (g : G) (h : Coeff G) :
    coefficientSqNorm (coefficientShift g h) = coefficientSqNorm h := by
  rw [coefficientShift,Finsupp.domCongr_apply,Finsupp.equivMapDomain_eq_mapDomain]
  exact Finsupp.sum_mapDomain_index_inj (Equiv.mulLeft g).injective

theorem freeCocycle_zpow_of_zero {ι : Type uι} (h : ι → Coeff (FreeGroup ι))
    (g : FreeGroup ι) (hg : freeCocycle h g = 0) (k : ℤ) : freeCocycle h (g^k) = 0 := by
  cases k with
  | ofNat k => simpa using freeCocycle_pow_of_zero h g hg k
  | negSucc k => simp only [zpow_negSucc,freeCocycle_inv,freeCocycle_pow_of_zero h g hg,map_zero,neg_zero]

namespace RankTwo

def concretePrefix (B j : ℕ) : FreeGroup (Fin 2) := realize (segment (runExponent B) 0 j)
def concreteWord (B m : ℕ) : FreeGroup (Fin 2) := concretePrefix B (m+1) * twoGenerator true

def concretePrefixHom (B m : ℕ) : FreeGroup (Fin m) →* FreeGroup (Fin 2) :=
  realize.comp (prefixHom B m)

@[simp] theorem concretePrefixHom_of (B m : ℕ) (i : Fin m) :
    concretePrefixHom B m (FreeGroup.of i) = concretePrefix B (i.val+2) := by
  simp [concretePrefixHom,prefixHom,concretePrefix]

@[simp] theorem concretePrefix_zero (B : ℕ) : concretePrefix B 0 = 1 := by simp [concretePrefix]
@[simp] theorem concretePrefix_succ (B j : ℕ) :
    concretePrefix B (j+1) = concretePrefix B j *
      (twoGenerator true * (twoGenerator false)^(runExponent B j)) := by
  simp only [concretePrefix,segment_succ,Nat.zero_add,map_mul,piece,realize_syllable,zpow_one]

theorem cocycle_twoGenerator_true (h : Coeff (FreeGroup (Fin 2))) :
    freeCocycle (firstCoefficients h) (twoGenerator true) = h := by
  simp [twoGenerator,firstCoefficients]

theorem cocycle_twoGenerator_false (h : Coeff (FreeGroup (Fin 2))) :
    freeCocycle (firstCoefficients h) (twoGenerator false) = 0 := by
  simp [twoGenerator,firstCoefficients]

theorem cocycle_concretePrefix (B m : ℕ) (h : Coeff (FreeGroup (Fin 2))) :
    freeCocycle (firstCoefficients h) (concretePrefix B m) =
      ∑ j ∈ Finset.range m, coefficientShift (concretePrefix B j) h := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [concretePrefix_succ,freeCocycle_mul,freeCocycle_mul,
      cocycle_twoGenerator_true,freeCocycle_zpow_of_zero _ _ (cocycle_twoGenerator_false h)]
    simp only [map_zero,add_zero,ih,Finset.sum_range_succ]

theorem cocycle_concreteWord (B m : ℕ) (h : Coeff (FreeGroup (Fin 2))) :
    freeCocycle (firstCoefficients h) (concreteWord B m) =
      h + coefficientShift (concretePrefix B 1) h +
        ∑ i : Fin m, coefficientShift (concretePrefix B (i.val+2)) h := by
  rw [concreteWord,freeCocycle_mul,cocycle_concretePrefix,cocycle_twoGenerator_true,
    ← Finset.sum_range_succ]
  rw [Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [concretePrefix_zero,coefficientShift_one,Nat.zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => coefficientShift (concretePrefix B (k+2)) h)]
  simpa only [Nat.add_assoc,Nat.one_add] using (by abel :
    (∑ j ∈ Finset.range m, coefficientShift (concretePrefix B (j+1+1)) h) +
        coefficientShift (concretePrefix B 1) h + h =
      h + coefficientShift (concretePrefix B 1) h +
        (∑ j ∈ Finset.range m, coefficientShift (concretePrefix B (j+2)) h))

theorem push_sumShift (B m : ℕ) (h : FreeGroup (Fin m) →₀ ℝ) :
    pushCoefficients (concretePrefixHom B m) (Radial.sumShift h) =
      ∑ i : Fin m, coefficientShift (concretePrefix B (i.val+2))
        (pushCoefficients (concretePrefixHom B m) h) := by
  rw [Radial.sumShift_apply,map_sum]
  simp only [pushCoefficients_shift,concretePrefixHom_of]

theorem rank_two_cocycle_identity (B m : ℕ) (h : FreeGroup (Fin m) →₀ ℝ) :
    freeCocycle (firstCoefficients (pushCoefficients (concretePrefixHom B m) h)) (concreteWord B m) =
      pushCoefficients (concretePrefixHom B m) h +
        coefficientShift (concretePrefix B 1) (pushCoefficients (concretePrefixHom B m) h) +
        pushCoefficients (concretePrefixHom B m) (Radial.sumShift h) := by
  rw [cocycle_concreteWord,push_sumShift]

theorem sqNorm_concrete_push (B m : ℕ) (h : FreeGroup (Fin m) →₀ ℝ) :
    coefficientSqNorm (pushCoefficients (concretePrefixHom B m) h) =
      coefficientSqNorm (pushCoefficients (prefixHom B m) h) := by
  rw [concretePrefixHom,pushCoefficients_comp,sqNorm_pushCoefficients realize realize_injective]

end RankTwo

theorem smallCocycleTwo (η : ℝ) (hη : 0 < η) :
    ∃ (w : FreeGroup (Fin 2)) (h : Coeff (FreeGroup (Fin 2))),
      coefficientNorm h < η ∧
        coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) < η := by
  obtain ⟨m,B,_hm,_hB,h,hh,hr⟩ := RankTwo.exists_small_pushed_inverse (η^2/16) (by positivity)
  let f := RankTwo.concretePrefixHom B m
  let h₂ := pushCoefficients f h
  have hsmall : coefficientSqNorm h₂ < η^2/16 := by
    simpa only [h₂,f,RankTwo.sqNorm_concrete_push] using hh
  have hrsmall : coefficientSqNorm (pushCoefficients f (Radial.sumShift h-Finsupp.single 1 1)) < η^2/16 := by
    simpa only [f,RankTwo.sqNorm_concrete_push] using hr
  refine ⟨RankTwo.concreteWord B m,h₂,?_,?_⟩
  · apply (Real.sqrt_lt' hη).mpr
    exact hsmall.trans (by nlinarith [sq_pos_of_pos hη])
  · apply (Real.sqrt_lt' hη).mpr
    change coefficientSqNorm (freeCocycle (firstCoefficients h₂) (RankTwo.concreteWord B m)-_) < η^2
    have hid : freeCocycle (firstCoefficients h₂) (RankTwo.concreteWord B m)-Finsupp.single 1 1 =
        (h₂+coefficientShift (RankTwo.concretePrefix B 1) h₂) +
          pushCoefficients f (Radial.sumShift h-Finsupp.single 1 1) := by
      dsimp only [h₂,f]
      rw [RankTwo.rank_two_cocycle_identity,map_sub]
      simp only [pushCoefficients_single,map_one]
      abel
    rw [hid]
    have hshift := coefficientSqNorm_shift (RankTwo.concretePrefix B 1) h₂
    have hsum := coefficientSqNorm_add_le h₂ (coefficientShift (RankTwo.concretePrefix B 1) h₂)
    have htot := coefficientSqNorm_add_le (h₂+coefficientShift (RankTwo.concretePrefix B 1) h₂)
      (pushCoefficients f (Radial.sumShift h-Finsupp.single 1 1))
    nlinarith

end FreeGroupFactorMain

end

end OAI
