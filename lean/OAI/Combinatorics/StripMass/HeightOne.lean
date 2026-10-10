import Mathlib
import OAI.Combinatorics.StripMass.ArchIntegrals

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
theorem integerLinePath_unique {l : List ℤ} {k : ℤ}
    (hh : l.head? = some 0) (ht : l.getLast? = some k)
    (hn : l.Nodup) (hc : l.IsChain unitAdjacent) : l = integerLinePath k := by
  have hlenpos : 0 < l.length := by
    cases l with
    | nil => simp at hh
    | cons => simp
  obtain ⟨s, hs, hsc⟩ := int_chain_direction hc hn
  have he := directed_chain_eq_range hh hsc
  simp only [zero_add] at he
  have ht' : s * ((l.length - 1 : ℕ) : ℤ) = k := by
    rw [he, List.getLast?_map, List.getLast?_range] at ht
    simpa [Nat.ne_of_gt hlenpos] using ht
  have hlen : l.length = k.natAbs + 1 := by
    rw [← ht', Int.natAbs_mul]
    rcases hs with rfl | rfl <;> simp <;> omega
  rw [he]
  unfold integerLinePath
  rw [hlen]
  apply List.map_congr_left
  intro n hn
  rcases hs with rfl | rfl
  · simp only [one_mul] at ht'
    have hk : ¬ k < 0 := by omega
    simp [hk]
  · simp only [neg_one_mul] at ht'
    by_cases hk : k < 0
    · simp [hk]
    · have hk0 : k = 0 := by omega
      simp only [List.mem_range, hk0, Int.natAbs_zero] at hn
      have hn0 : n = 0 := by omega
      simp [hn0]

 
def oneBandPath (finish : Triangle) : List Triangle :=
  (integerLinePath (bandRank finish)).map bandVertex

theorem oneBandPath_spec {finish : Triangle} (hf : finish.2.1 = 0) :
    IsPath 1 finish (oneBandPath finish) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [oneBandPath, List.head?_map, bandVertex, up]
  · simp [oneBandPath, List.getLast?_map, bandVertex_bandRank finish hf]
  · exact (integerLinePath_nodup _).map (Function.LeftInverse.injective bandRank_bandVertex)
  · apply (List.isChain_map _).mpr
    apply (integerLinePath_chain _).imp
    intro a b hab
    apply (band_adjacent_iff (bandVertex_band a) (bandVertex_band b)).mpr
    simpa [unitAdjacent] using hab
  · intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    simp

theorem oneBandPath_unique {finish : Triangle} {p : List Triangle}
    (hp : IsPath 1 finish p) : p = oneBandPath finish := by
  have hz (v) (hv : v ∈ p) : v.2.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (hp.2.2.2.2 v hv))
  have he : p.map bandRank = integerLinePath (bandRank finish) := by
    apply integerLinePath_unique
    · rw [List.head?_map, hp.1]; rfl
    · rw [List.getLast?_map, hp.2.1]; rfl
    · apply hp.2.2.1.map_on
      intro v hv w hw he
      simpa only [bandVertex_bandRank v (hz v hv), bandVertex_bandRank w (hz w hw)] using congrArg bandVertex he
    · rw [List.isChain_iff_getElem]
      intro i hi
      simp only [List.length_map] at hi
      simp only [List.getElem_map]
      exact (band_adjacent_iff (hz _ (List.getElem_mem _)) (hz _ (List.getElem_mem _))).mp
        (hp.2.2.2.1.getElem i hi)
  calc
    p = (p.map bandRank).map bandVertex := by
      rw [List.map_map]
      exact (List.map_id p).symm.trans (List.map_congr_left fun v hv => (bandVertex_bandRank v (hz v hv)).symm)
    _ = oneBandPath finish := by rw [he]; rfl

theorem oneBandPath_length (finish : Triangle) :
    (oneBandPath finish).length = (bandRank finish).natAbs + 1 := by
  simp [oneBandPath]



theorem isPath_one_iff {v : Triangle} (hv : v.2.1 = 0) (p : List Triangle) :
    IsPath 1 v p ↔ p = oneBandPath v := by
  refine ⟨oneBandPath_unique, ?_⟩
  rintro rfl
  exact oneBandPath_spec hv

theorem archWeight_one (k : ℤ) (p : List Triangle) :
    archWeight 1 k p =
      if p = oneBandPath (up k 0) then (if k = 0 then 0 else rho ^ (2 * k.natAbs + 1)) else 0 := by
  classical
  unfold archWeight
  rw [isPath_one_iff rfl]
  by_cases hp : p = oneBandPath (up k 0)
  · subst p
    simp [oneBandPath_length, Int.natAbs_mul]
  · simp [hp]

theorem bridgeWeight_one (k : ℤ) (p : List Triangle) :
    bridgeWeight 1 k p =
      if p = oneBandPath (down k 0) then rho ^ ((2 * k + 1).natAbs + 1) else 0 := by
  classical
  unfold bridgeWeight
  norm_num only [Nat.sub_self, Nat.zero_lt_one, true_and]
  rw [isPath_one_iff rfl]
  by_cases hp : p = oneBandPath (down k 0)
  · subst p
    simp [oneBandPath_length]
  · simp [hp]

theorem hasSum_archWeight_one (k : ℤ) :
    HasSum (archWeight 1 k) (if k = 0 then 0 else rho ^ (2 * k.natAbs + 1)) := by
  classical
  simp_rw [show archWeight 1 k = fun p =>
      if p = oneBandPath (up k 0) then (if k = 0 then 0 else rho ^ (2 * k.natAbs + 1)) else 0
      from funext (archWeight_one k)]
  exact hasSum_ite_eq _ _

theorem hasSum_bridgeWeight_one (k : ℤ) :
    HasSum (bridgeWeight 1 k) (rho ^ ((2 * k + 1).natAbs + 1)) := by
  classical
  simp_rw [show bridgeWeight 1 k = fun p =>
      if p = oneBandPath (down k 0) then rho ^ ((2 * k + 1).natAbs + 1) else 0
      from funext (bridgeWeight_one k)]
  exact hasSum_ite_eq _ _

 
theorem K_one (k : ℤ) : K 1 k = if k = 0 then 0 else rho ^ (2 * k.natAbs + 1) :=
  (hasSum_archWeight_one k).tsum_eq

theorem bridgeKernel_one (k : ℤ) : bridgeKernel 1 k = rho ^ ((2 * k + 1).natAbs + 1) :=
  (hasSum_bridgeWeight_one k).tsum_eq

theorem K_one_right (n : ℕ) : K 1 ((n : ℤ) + 1) = rho ^ 3 * (rho ^ 2) ^ n := by
  have he : (n : ℤ) + 1 = (n + 1 : ℕ) := by omega
  rw [he, K_one]
  simp only [Nat.cast_eq_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, Int.natAbs_natCast]
  rw [show 2 * (n + 1) + 1 = 3 + 2 * n by omega, pow_add, ← pow_mul]

theorem K_one_left (n : ℕ) : K 1 (-((n : ℤ) + 1)) = rho ^ 3 * (rho ^ 2) ^ n := by
  rw [show K 1 (-((n : ℤ) + 1)) = K 1 ((n : ℤ) + 1) by simp only [K_one, neg_eq_zero, Int.natAbs_neg]]
  exact K_one_right n

theorem bridgeKernel_one_right (n : ℕ) :
    bridgeKernel 1 (n : ℤ) = rho ^ 2 * (rho ^ 2) ^ n := by
  rw [bridgeKernel_one, show 2 * (n : ℤ) + 1 = ((2 * n + 1 : ℕ) : ℤ) by omega]
  simp only [Int.natAbs_natCast]
  rw [show 2 * n + 1 + 1 = 2 + 2 * n by omega, pow_add, ← pow_mul]

theorem bridgeKernel_one_left (n : ℕ) :
    bridgeKernel 1 (-((n : ℤ) + 1)) = rho ^ 2 * (rho ^ 2) ^ n := by
  rw [bridgeKernel_one, show 2 * (-((n : ℤ) + 1)) + 1 = -((2 * n + 1 : ℕ) : ℤ) by omega]
  simp only [Int.natAbs_neg, Int.natAbs_natCast]
  rw [show 2 * n + 1 + 1 = 2 + 2 * n by omega, pow_add, ← pow_mul]

 
theorem rho_sq_lt_one : rho ^ 2 < 1 := by
  have hs : (1 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    exact (Real.sqrt_one ▸ Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [Real.sqrt_nonneg 2]))
  have hp : 0 < Real.sqrt (2 + Real.sqrt 2) := lt_trans zero_lt_one hs
  have hr : rho < 1 := (div_lt_one hp).2 hs
  nlinarith [rho_pos]

theorem hasSum_K_one : HasSum (K 1) (2 * rho ^ 3 / (1 - rho ^ 2)) := by
  have hg := hasSum_geometric_of_lt_one (sq_nonneg rho) rho_sq_lt_one
  have hr : HasSum (fun n : ℕ => K 1 ((n : ℤ) + 1)) (rho ^ 3 / (1 - rho ^ 2)) := by
    simp only [K_one_right, div_eq_mul_inv]
    exact hg.mul_left _
  have hl : HasSum (fun n : ℕ => K 1 (-((n : ℤ) + 1))) (rho ^ 3 / (1 - rho ^ 2)) := by
    simp only [K_one_left, div_eq_mul_inv]
    exact hg.mul_left _
  have hn : HasSum (fun n : ℕ => K 1 (n : ℤ)) (rho ^ 3 / (1 - rho ^ 2)) := by
    have h := (hasSum_nat_add_iff (f := fun n : ℕ => K 1 (n : ℤ)) 1).mp (by simpa using hr)
    simpa using h
  convert hn.of_nat_of_neg_add_one hl using 1
  ring

theorem hasSum_bridgeKernel_one : HasSum (bridgeKernel 1) (2 * rho ^ 2 / (1 - rho ^ 2)) := by
  have hg := hasSum_geometric_of_lt_one (sq_nonneg rho) rho_sq_lt_one
  have hr : HasSum (fun n : ℕ => bridgeKernel 1 (n : ℤ)) (rho ^ 2 / (1 - rho ^ 2)) := by
    simp only [bridgeKernel_one_right, div_eq_mul_inv]
    exact hg.mul_left _
  have hl : HasSum (fun n : ℕ => bridgeKernel 1 (-((n : ℤ) + 1))) (rho ^ 2 / (1 - rho ^ 2)) := by
    simp only [bridgeKernel_one_left, div_eq_mul_inv]
    exact hg.mul_left _
  convert hr.of_nat_of_neg_add_one hl using 1
  ring

theorem hasSum_moment_one :
    HasSum (fun n : ℕ => (n + 1 : ℝ) * K 1 (n + 1)) (rho ^ 3 / (1 - rho ^ 2) ^ 2) := by
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one (r := rho ^ 2) 1
    (by simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg rho)] using rho_sq_lt_one)
  have he (n : ℕ) : (n+1 : ℝ) * K 1 (n+1) = rho ^ 3 * ((n+1 : ℝ) * (rho ^ 2) ^ n) := by
    rw [K_one_right]; ring
  simp only [he]
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
    Nat.reduceAdd, one_mul] using hs.mul_left (rho ^ 3)

 

theorem stripSumsFinite_one : StripSumsFinite 1 :=
  ⟨fun k => (hasSum_archWeight_one k).summable,
    fun k => (hasSum_bridgeWeight_one k).summable,
    hasSum_K_one.summable, hasSum_bridgeKernel_one.summable, hasSum_moment_one.summable⟩

theorem archMass_one : archMass 1 = 2 * rho ^ 3 / (1 - rho ^ 2) := hasSum_K_one.tsum_eq

theorem bridgeMass_one : bridgeMass 1 = 2 * rho ^ 2 / (1 - rho ^ 2) := hasSum_bridgeKernel_one.tsum_eq

theorem moment_one : moment 1 = rho ^ 3 / (1 - rho ^ 2) ^ 2 := hasSum_moment_one.tsum_eq

 
theorem two_C_mul_rho : 2 * C * rho = 1 := by
  unfold C lambda rho
  rw [Real.cos_pi_div_eight]
  have hn : Real.sqrt (2 + Real.sqrt 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

theorem c_eq_sqrt_two_mul_rho : c = (Real.sqrt 2 / 2) * rho := by
  have hs : 2 * c * C = Real.sqrt 2 / 2 := by
    unfold c C lambda
    rw [show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring,
      Real.cos_pi_div_two_sub, ← Real.sin_two_mul,
      show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.sin_pi_div_four]
  linear_combination rho * hs - c * two_C_mul_rho

theorem rho_sq : rho ^ 2 = (2 - Real.sqrt 2) / 2 := by
  unfold rho
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 + Real.sqrt 2)]
  apply (div_eq_iff (by positivity : (2 + Real.sqrt 2 : ℝ) ≠ 0)).2
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem critical_one_band_identity : 2 * c * rho ^ 3 + 3 * rho ^ 2 = 1 := by
  rw [c_eq_sqrt_two_mul_rho]
  calc
    2 * (Real.sqrt 2 / 2 * rho) * rho ^ 3 + 3 * rho ^ 2 =
        Real.sqrt 2 * (rho ^ 2) ^ 2 + 3 * rho ^ 2 := by ring
    _ = 1 := by
      rw [rho_sq]
      linear_combination (Real.sqrt 2 / 4 - 1) * Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

 
theorem flux_one : c * archMass 1 + bridgeMass 1 = 1 := by
  rw [archMass_one, bridgeMass_one]
  have hn : 1 - rho ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr rho_sq_lt_one)
  field_simp
  nlinarith [critical_one_band_identity]


 

 

def mirrorTriangle (v : Triangle) : Triangle :=
  (-v.1 - (v.2.1 : ℤ) - (if v.2.2 then 0 else 1), v.2.1, v.2.2)

@[simp] theorem mirrorTriangle_band (v : Triangle) : (mirrorTriangle v).2.1 = v.2.1 := rfl

@[simp] theorem mirrorTriangle_up (i : ℤ) (j : ℕ) :
    mirrorTriangle (up i j) = up (-i - j) j := by
  simp [mirrorTriangle, up]

@[simp] theorem mirrorTriangle_down (i : ℤ) (j : ℕ) :
    mirrorTriangle (down i j) = down (-i - j - 1) j := by
  simp [mirrorTriangle, down]

@[simp] theorem mirrorTriangle_mirrorTriangle (v : Triangle) :
    mirrorTriangle (mirrorTriangle v) = v := by
  rcases v with ⟨i, j, b⟩
  cases b <;> simp [mirrorTriangle]
  ring

theorem mirrorTriangle_involutive : Function.Involutive mirrorTriangle := mirrorTriangle_mirrorTriangle

theorem mirrorTriangles_involutive : Function.Involutive (List.map mirrorTriangle) := by
  intro l
  simp [List.map_map, Function.comp_def]

 
theorem adjacent_mirror_iff (v w : Triangle) :
    adjacent (mirrorTriangle v) (mirrorTriangle w) ↔ adjacent v w := by
  rcases v with ⟨a, j, b⟩
  rcases w with ⟨a', j', b'⟩
  cases b <;> cases b' <;> simp [adjacent, upDownAdjacent, mirrorTriangle]
  all_goals omega

theorem IsPath.mirror {N : ℕ} {finish : Triangle} {p : List Triangle}
    (hp : IsPath N finish p) :
    IsPath N (mirrorTriangle finish) (p.map mirrorTriangle) := by
  refine ⟨?_, ?_, hp.2.2.1.map mirrorTriangle_involutive.injective, ?_, ?_⟩
  · rw [List.head?_map, hp.1]
    simp
  · rw [List.getLast?_map, hp.2.1]
    rfl
  · apply (List.isChain_map _).mpr
    apply hp.2.2.2.1.imp
    intro v w h
    exact (adjacent_mirror_iff v w).mpr h
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact hp.2.2.2.2 w hw

@[simp] theorem isPath_mirror_iff {N : ℕ} {finish : Triangle} {p : List Triangle} :
    IsPath N (mirrorTriangle finish) (p.map mirrorTriangle) ↔ IsPath N finish p := by
  refine ⟨fun h => ?_, IsPath.mirror⟩
  simpa [List.map_map, Function.comp_def] using h.mirror

theorem archWeight_mirror (N : ℕ) (k : ℤ) (p : List Triangle) :
    archWeight N (-k) (p.map mirrorTriangle) = archWeight N k p := by
  classical
  have he : up (-k) 0 = mirrorTriangle (up k 0) := by simp
  simp only [archWeight, neg_ne_zero, he, isPath_mirror_iff, List.length_map]

theorem bridgeWeight_mirror (N : ℕ) (k : ℤ) (p : List Triangle) :
    bridgeWeight N (-k - N) (p.map mirrorTriangle) = bridgeWeight N k p := by
  classical
  rcases N with _ | N
  · simp [bridgeWeight]
  · have he : down (-k - (N + 1 : ℕ)) (N + 1 - 1) =
        mirrorTriangle (down k (N + 1 - 1)) := by
      simp only [mirrorTriangle_down, Nat.add_sub_cancel]
      congr 1
      push_cast
      ring
    simp only [bridgeWeight, he, isPath_mirror_iff, List.length_map]

 

theorem K_reflection (N : ℕ) (k : ℤ) : K N (-k) = K N k := by
  let e := mirrorTriangles_involutive.toPerm _
  calc
    K N (-k) = ∑' p : List Triangle, archWeight N (-k) (p.map mirrorTriangle) :=
      (e.tsum_eq (archWeight N (-k))).symm
    _ = K N k := tsum_congr (archWeight_mirror N k)

theorem bridgeKernel_reflection (N : ℕ) (k : ℤ) :
    bridgeKernel N (-k - N) = bridgeKernel N k := by
  let e := mirrorTriangles_involutive.toPerm _
  calc
    bridgeKernel N (-k - N) = ∑' p : List Triangle, bridgeWeight N (-k - N) (p.map mirrorTriangle) :=
      (e.tsum_eq (bridgeWeight N (-k - N))).symm
    _ = bridgeKernel N k := tsum_congr (bridgeWeight_mirror N k)

 
theorem hasSum_absoluteMoment {N : ℕ}
    (hM : Summable (fun n : ℕ => (n + 1 : ℝ) * K N (n + 1))) :
    HasSum (fun k : ℤ => (k.natAbs : ℝ) * K N k) (2 * moment N) := by
  have hp : HasSum (fun n : ℕ => (((n : ℤ) + 1).natAbs : ℝ) * K N ((n : ℤ) + 1)) (moment N) := by
    have he (n : ℕ) : (((n : ℤ) + 1).natAbs : ℝ) = (n : ℝ) + 1 := by
      rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega, Int.natAbs_natCast,
        Nat.cast_add, Nat.cast_one]
    simp only [he]
    exact hM.hasSum
  have hn : HasSum (fun n : ℕ => ((-((n : ℤ) + 1)).natAbs : ℝ) * K N (-((n : ℤ) + 1))) (moment N) := by
    simpa only [Int.natAbs_neg, K_reflection] using hp
  have hp0 : HasSum (fun n : ℕ => (((n : ℤ)).natAbs : ℝ) * K N (n : ℤ)) (moment N) := by
    have h := (hasSum_nat_add_iff (f := fun n : ℕ => (((n : ℤ)).natAbs : ℝ) * K N (n : ℤ)) 1).mp
      (by simpa using hp)
    simpa using h
  simpa only [two_mul] using hp0.of_nat_of_neg_add_one (f := fun k : ℤ => (k.natAbs : ℝ) * K N k) hn

theorem absoluteMoment_eq {N : ℕ} (hN : StripSumsFinite N) :
    (∑' k : ℤ, (k.natAbs : ℝ) * K N k) = 2 * moment N :=
  (hasSum_absoluteMoment hN.2.2.2.2).tsum_eq

 

theorem summable_K_of_moment {N : ℕ}
    (hM : Summable (fun n : ℕ => (n + 1 : ℝ) * K N (n + 1))) :
    Summable (K N) := by
  have hp : Summable (fun n : ℕ => K N ((n : ℤ) + 1)) := by
    apply Summable.of_nonneg_of_le (fun n => K_nonneg _ _) (fun n => ?_) hM
    have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right hn (K_nonneg _ _))
  have hm : HasSum (fun n : ℕ => K N (-((n : ℤ) + 1))) (∑' n : ℕ, K N ((n : ℤ) + 1)) := by
    simpa only [K_reflection] using hp.hasSum
  have hp0 : HasSum (fun n : ℕ => K N (n : ℤ)) (∑' n : ℕ, K N ((n : ℤ) + 1)) := by
    have h := (hasSum_nat_add_iff (f := fun n : ℕ => K N (n : ℤ)) 1).mp (by simpa using hp.hasSum)
    simpa using h
  exact (hp0.of_nat_of_neg_add_one hm).summable

theorem archMass_eq_twice_right {N : ℕ} (hN : StripSumsFinite N) :
    archMass N = 2 * ∑' n : ℕ, K N ((n : ℤ) + 1) := by
  have hp : Summable (fun n : ℕ => K N ((n : ℤ) + 1)) :=
    hN.2.2.1.comp_injective (fun n m h => by omega)
  have hm : HasSum (fun n : ℕ => K N (-((n : ℤ) + 1))) (∑' n : ℕ, K N ((n : ℤ) + 1)) := by
    simpa only [K_reflection] using hp.hasSum
  have hp0 : HasSum (fun n : ℕ => K N (n : ℤ)) (∑' n : ℕ, K N ((n : ℤ) + 1)) := by
    have h := (hasSum_nat_add_iff (f := fun n : ℕ => K N (n : ℤ)) 1).mp (by simpa using hp.hasSum)
    simpa using h
  unfold archMass
  simpa only [two_mul] using (hp0.of_nat_of_neg_add_one hm).tsum_eq


 

 
def columnVertex (k : ℕ) : Triangle :=
  if k % 2 = 0 then up 0 (k / 2) else down 0 (k / 2)

@[simp] theorem columnVertex_band (k : ℕ) : (columnVertex k).2.1 = k / 2 := by
  simp only [columnVertex]
  split <;> rfl

theorem columnVertex_injective : Function.Injective columnVertex := by
  have hr (k : ℕ) : 2 * (columnVertex k).2.1 + (if (columnVertex k).2.2 then 0 else 1) = k := by
    simp only [columnVertex]
    split <;> simp only [up, down, Bool.false_eq_true, reduceIte, ite_true]
    all_goals omega
  intro a b hab
  have hh := congrArg (fun v : Triangle => 2 * v.2.1 + (if v.2.2 then 0 else 1)) hab
  simpa only [hr] using hh

end
end CriticalStrip

end OAI
