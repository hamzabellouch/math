import Mathlib
import OAI.Combinatorics.MatchingCount.Model

namespace OAI

namespace MatchingFPRAS

@[reducible] noncomputable def completeGraph (n : ℕ) : GraphInput where
  n := n
  edges := by
    classical
    exact Finset.univ.filter (fun e => e.1 < e.2)
  increasing := by
    classical
    intro e he
    exact (Finset.mem_filter.mp he).2

noncomputable def rawWeight (G : GraphInput) (x : ℚ) (M : Finset (Fin G.n × Fin G.n)) : ℚ :=
  ∏ e ∈ M, if e ∈ G.edges then 1 else x

noncomputable def rawPartition (G : GraphInput) (x : ℚ) : ℚ :=
  ∑ M ∈ perfectMatchings (completeGraph G.n), rawWeight G x M



lemma graph_edges_subset_complete (G : GraphInput) : G.edges ⊆ (completeGraph G.n).edges := by
  classical
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.increasing e he⟩

lemma mem_perfectMatchings (G : GraphInput) (M) : M ∈ perfectMatchings G ↔ Perfect G M := by
  classical
  simp only [perfectMatchings, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1,h⟩⟩

lemma pm_subset_complete (G : GraphInput) : perfectMatchings G ⊆ perfectMatchings (completeGraph G.n) := by
  intro M hM
  apply (mem_perfectMatchings _ _).mpr
  have h := (mem_perfectMatchings _ _).mp hM
  exact ⟨h.1.trans (graph_edges_subset_complete G), h.2⟩

lemma rawWeight_nonneg (G : GraphInput) (x : ℚ) (hx : 0 ≤ x) (M) : 0 ≤ rawWeight G x M := by
  classical
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> positivity

lemma rawWeight_one (G : GraphInput) (x : ℚ) (M) (hM : M ⊆ G.edges) : rawWeight G x M = 1 := by
  classical
  apply Finset.prod_eq_one
  intro e he
  simp [hM he]

lemma rawWeight_bad (G : GraphInput) (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (M)
    (hM : ¬ M ⊆ G.edges) : rawWeight G x M ≤ x := by
  classical
  obtain ⟨e, he, hbad⟩ := Finset.not_subset.mp hM
  have hp : (∏ f ∈ M.erase e, if f ∈ G.edges then (1:ℚ) else x) ≤ 1 := by
    apply Finset.prod_le_one₀ (fun f _ => by split_ifs <;> positivity)
    intro f hf
    split_ifs <;> simp_all
  change (∏ f ∈ M, if f ∈ G.edges then (1:ℚ) else x) ≤ x
  rw [← Finset.mul_prod_erase M _ he, ite_eq_right hbad]
  simpa using mul_le_mul_of_nonneg_left hp hx



theorem raw_padding_bound (G : GraphInput) (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (Z G : ℚ) ≤ rawPartition G x ∧
    rawPartition G x ≤ (Z G : ℚ) + (Z (completeGraph G.n) : ℚ)*x := by
  classical
  let full := perfectMatchings (completeGraph G.n)
  let good := perfectMatchings G
  let indicator : Finset (Fin G.n × Fin G.n) → ℚ := fun M => if M ∈ good then 1 else 0
  have hind : (∑ M ∈ full, indicator M) = (Z G : ℚ) := by
    have heq := Finset.sum_subset (f := indicator) (pm_subset_complete G)
      (fun M _ hnot => ite_eq_right hnot)
    change (∑ M ∈ good, indicator M) = ∑ M ∈ full, indicator M at heq
    rw [← heq]
    simp [indicator,good,Z]
  have hlo (M : Finset (Fin G.n × Fin G.n)) (hMF : M ∈ full) : indicator M ≤ rawWeight G x M := by
    by_cases hM : M ∈ good
    · have hsub := ((mem_perfectMatchings G M).mp hM).1
      have hi : indicator M = 1 := ite_eq_left hM
      rw [hi, rawWeight_one G x M hsub]
    · have hi : indicator M = 0 := ite_eq_right hM
      rw [hi]
      exact rawWeight_nonneg G x hx M
  have hup (M : Finset (Fin G.n × Fin G.n)) (hMF : M ∈ full) : rawWeight G x M ≤ indicator M+x := by
    by_cases hM : M ∈ good
    · have hsub := ((mem_perfectMatchings G M).mp hM).1
      have hi : indicator M = 1 := ite_eq_left hM
      rw [hi, rawWeight_one G x M hsub]
      linarith
    · have hsub : ¬ M ⊆ G.edges := by
        intro hh
        apply hM
        apply (mem_perfectMatchings G M).mpr
        exact ⟨hh, ((mem_perfectMatchings (completeGraph G.n) M).mp hMF).2⟩
      have hi : indicator M = 0 := ite_eq_right hM
      rw [hi, zero_add]
      exact rawWeight_bad G x hx hx1 M hsub
  constructor
  · rw [← hind]
    exact Finset.sum_le_sum hlo
  · calc
      rawPartition G x ≤ ∑ M ∈ full, (indicator M+x) := Finset.sum_le_sum hup
      _ = (Z G : ℚ) + (Z (completeGraph G.n) : ℚ)*x := by
        rw [Finset.sum_add_distrib, hind]
        simp [Z,full]



theorem perfect_vertex_factor (G : GraphInput) (M : Finset (Fin G.n × Fin G.n))
    (hM : Perfect G M) (s : Fin G.n → ℚ) :
    (∏ e ∈ M, s e.1*s e.2) = ∏ v, s v := by
  classical
  let ends : Fin G.n × Fin G.n → Finset (Fin G.n) := fun e => {e.1,e.2}
  have hends (e : Fin G.n × Fin G.n) (v) : v ∈ ends e ↔ e.1=v ∨ e.2=v := by
    simp [ends, eq_comm]
  have hpair : (M : Set (Fin G.n × Fin G.n)).PairwiseDisjoint ends := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hve : e ∈ M ∧ (e.1=v ∨ e.2=v) := ⟨he,(hends e v).mp hv⟩
    have hvf : f ∈ M ∧ (f.1=v ∨ f.2=v) := ⟨hf,(hends f v).mp hw⟩
    exact hne ((hM.2 v).unique hve hvf)
  have hall : M.biUnion ends = Finset.univ := by
    ext v
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨e,he,_⟩ := hM.2 v
    exact Finset.mem_biUnion.mpr ⟨e,he.1,(hends e v).mpr he.2⟩
  calc
    (∏ e ∈ M, s e.1*s e.2) = ∏ e ∈ M, ∏ v ∈ ends e, s v := by
      apply Finset.prod_congr rfl
      intro e he
      have hne : e.1 ≠ e.2 := (G.increasing e (hM.1 he)).ne
      simp [ends,hne]
    _ = ∏ v ∈ M.biUnion ends, s v := (Finset.prod_biUnion hpair).symm
    _ = ∏ v, s v := by rw [hall]



noncomputable def weightedPartition (G : GraphInput) (w : Fin G.n × Fin G.n → ℚ) : ℚ :=
  ∑ M ∈ perfectMatchings G, ∏ e ∈ M, w e

theorem vertex_scaled_partition (G : GraphInput) (w : Fin G.n × Fin G.n → ℚ)
    (s : Fin G.n → ℚ) :
    weightedPartition G (fun e => w e*s e.1*s e.2) =
      weightedPartition G w * ∏ v, s v := by
  classical
  unfold weightedPartition
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro M hM
  have hp : Perfect G M := (Finset.mem_filter.mp hM).2
  calc
    (∏ e ∈ M, w e*s e.1*s e.2) = ∏ e ∈ M, w e*(s e.1*s e.2) := by
      apply Finset.prod_congr rfl
      intro e he
      ring
    _ = (∏ e ∈ M, w e)*(∏ e ∈ M, s e.1*s e.2) := Finset.prod_mul_distrib
    _ = (∏ e ∈ M, w e)*(∏ v, s v) := by rw [perfect_vertex_factor G M hp s]



def NearPerfect (G : GraphInput) (i j : Fin G.n)
    (M : Finset (Fin G.n × Fin G.n)) : Prop :=
  M ⊆ G.edges ∧ (∀ e ∈ M, e.1 ≠ i ∧ e.2 ≠ i ∧ e.1 ≠ j ∧ e.2 ≠ j) ∧
  ∀ v, v ≠ i → v ≠ j → ∃! e, e ∈ M ∧ (e.1=v ∨ e.2=v)

noncomputable def holePartition (G : GraphInput) (i j : Fin G.n)
    (w : Fin G.n × Fin G.n → ℚ) : ℚ := by
  classical
  exact ∑ M ∈ G.edges.powerset.filter (NearPerfect G i j), ∏ e ∈ M, w e

noncomputable def holeRatio (G : GraphInput) (i j : Fin G.n)
    (w : Fin G.n × Fin G.n → ℚ) : ℚ :=
  holePartition G i j w / weightedPartition G w



theorem near_vertex_factor (G : GraphInput) (i j : Fin G.n) (hij : i ≠ j)
    (M : Finset (Fin G.n × Fin G.n)) (hM : NearPerfect G i j M) (s : Fin G.n → ℚ) :
    (∏ e ∈ M, s e.1*s e.2) * (s i*s j) = ∏ v, s v := by
  classical
  let ends : Fin G.n × Fin G.n → Finset (Fin G.n) := fun e => {e.1,e.2}
  have hends (e : Fin G.n × Fin G.n) (v) : v ∈ ends e ↔ e.1=v ∨ e.2=v := by
    simp [ends, eq_comm]
  have hpair : (M : Set (Fin G.n × Fin G.n)).PairwiseDisjoint ends := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hve : e ∈ M ∧ (e.1=v ∨ e.2=v) := ⟨he,(hends e v).mp hv⟩
    have hvf : f ∈ M ∧ (f.1=v ∨ f.2=v) := ⟨hf,(hends f v).mp hw⟩
    have hvi : v ≠ i := by
      rcases hve.2 with h | h <;> subst v
      · exact (hM.2.1 e he).1
      · exact (hM.2.1 e he).2.1
    have hvj : v ≠ j := by
      rcases hve.2 with h | h <;> subst v
      · exact (hM.2.1 e he).2.2.1
      · exact (hM.2.1 e he).2.2.2
    exact hne ((hM.2.2 v hvi hvj).unique hve hvf)
  have hall : M.biUnion ends = (Finset.univ.erase i).erase j := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨e,he,hv⟩
      rcases (hends e v).mp hv with h | h <;> subst v
      · exact ⟨(hM.2.1 e he).2.2.1,(hM.2.1 e he).1⟩
      · exact ⟨(hM.2.1 e he).2.2.2,(hM.2.1 e he).2.1⟩
    · rintro ⟨hvj,hvi⟩
      obtain ⟨e,he,_⟩ := hM.2.2 v hvi hvj
      exact ⟨e,he.1,(hends e v).mpr he.2⟩
  have hfactor : (∏ e ∈ M, s e.1*s e.2) = ∏ v ∈ (Finset.univ.erase i).erase j, s v := by
    calc
      (∏ e ∈ M, s e.1*s e.2) = ∏ e ∈ M, ∏ v ∈ ends e, s v := by
        apply Finset.prod_congr rfl
        intro e he
        have hne : e.1 ≠ e.2 := (G.increasing e (hM.1 he)).ne
        simp [ends,hne]
      _ = ∏ v ∈ M.biUnion ends, s v := (Finset.prod_biUnion hpair).symm
      _ = _ := by rw [hall]
  rw [hfactor]
  calc
    (∏ v ∈ (Finset.univ.erase i).erase j, s v)*(s i*s j) =
      ((∏ v ∈ (Finset.univ.erase i).erase j, s v)*s j)*s i := by ring
    _ = (∏ v ∈ Finset.univ.erase i, s v)*s i := by
      rw [Finset.prod_erase_mul _ _ (by simp [hij.symm])]
    _ = ∏ v, s v := Finset.prod_erase_mul _ _ (Finset.mem_univ _)

theorem hole_partition_vertex_scaling (G : GraphInput) (i j : Fin G.n) (hij : i ≠ j)
    (w : Fin G.n × Fin G.n → ℚ) (s : Fin G.n → ℚ) :
    holePartition G i j (fun e => w e*s e.1*s e.2)*(s i*s j) =
      holePartition G i j w * ∏ v, s v := by
  classical
  unfold holePartition
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro M hM
  have hp : NearPerfect G i j M := (Finset.mem_filter.mp hM).2
  calc
    (∏ e ∈ M, w e*s e.1*s e.2)*(s i*s j) =
      ((∏ e ∈ M, w e)*(∏ e ∈ M, s e.1*s e.2))*(s i*s j) := by
      congr 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro e he
      ring
    _ = (∏ e ∈ M, w e)*((∏ e ∈ M, s e.1*s e.2)*(s i*s j)) := by ring
    _ = (∏ e ∈ M, w e)*(∏ v, s v) := by rw [near_vertex_factor G i j hij M hp s]



theorem hole_ratio_vertex_scaling (G : GraphInput) (i j : Fin G.n) (hij : i ≠ j)
    (w : Fin G.n × Fin G.n → ℚ) (s : Fin G.n → ℚ) (hs : ∀ v, 0 < s v) :
    holeRatio G i j (fun e => w e*s e.1*s e.2) =
      holeRatio G i j w / (s i*s j) := by
  classical
  have hsij : s i*s j ≠ 0 := mul_ne_zero (hs i).ne' (hs j).ne'
  have hsall : (∏ v, s v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => (hs v).ne')
  have hp := hole_partition_vertex_scaling G i j hij w s
  have hscaled : holePartition G i j (fun e => w e*s e.1*s e.2) =
      (holePartition G i j w * ∏ v, s v)/(s i*s j) := (eq_div_iff hsij).mpr hp
  unfold holeRatio
  rw [hscaled, vertex_scaled_partition]
  by_cases hw : weightedPartition G w = 0
  · simp [hw]
  · field_simp

end MatchingFPRAS

namespace MatchingFPRAS.Counting

def scheduleAdmissible (n : ℕ) (epsilon : ℚ) (k : ℕ) : Prop :=
  1 ≤ k ∧ (n:ℚ)^(n/2)/(1+1/(n:ℚ))^k ≤ epsilon/32



theorem counting_schedule_exists (n : ℕ) (hn : 2 ≤ n) (epsilon : ℚ)
    (he : 0 < epsilon) (he1 : epsilon < 1) :
    ∃ K : ℕ, scheduleAdmissible n epsilon K ∧
      (∀ k, scheduleAdmissible n epsilon k → K ≤ k) ∧
      (K:ℝ) ≤ 1+2*n*((n/2:ℕ)*Real.log n+Real.log (32/(epsilon:ℝ))) := by
  classical
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have her : (0:ℝ) < epsilon := by exact_mod_cast he
  have he1r : (epsilon:ℝ) < 1 := by exact_mod_cast he1
  let b : ℝ := 1+1/(n:ℝ)
  have hb : 1 < b := by
    dsimp [b]
    have ht : 0 < 1/(n:ℝ) := by positivity
    linarith
  have hb0 : 0 < b := by linarith
  have hlog : 1/(2*(n:ℝ)) ≤ Real.log b := by
    have h := Real.one_sub_inv_le_log_of_pos hb0
    have hcalc : 1/(2*(n:ℝ)) ≤ 1-b⁻¹ := by
      dsimp [b]
      field_simp
      nlinarith
    exact hcalc.trans h
  let L : ℝ := (n/2:ℕ)*Real.log n+Real.log (32/(epsilon:ℝ))
  have hratio : 1 < 32/(epsilon:ℝ) := (lt_div_iff₀ her).mpr (by linarith)
  have hL : 0 < L := by
    have ha : 0 ≤ (n/2:ℕ)*Real.log (n:ℝ) := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    have hb := Real.log_pos hratio
    dsimp [L]
    linarith
  let C : ℝ := 2*n*L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let k : ℕ := ⌊C⌋₊+1
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hkt : C < (k:ℝ) := by
    dsimp [k]
    exact_mod_cast Nat.lt_floor_add_one C
  have hku : (k:ℝ) ≤ C+1 := by
    dsimp [k]
    push_cast
    linarith [Nat.floor_le hC]
  have hkl : L ≤ (k:ℝ)*Real.log b := by
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hlog hk0
    have hsmall : L ≤ (k:ℝ)*(1/(2*(n:ℝ))) := by
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity : 0 < 2*(n:ℝ))).mpr
      dsimp [C] at hkt
      nlinarith
    exact hsmall.trans hm
  have ha0 : (0:ℝ) < (n:ℝ)^(n/2)/b^k := by positivity
  have ht0 : (0:ℝ) < (epsilon:ℝ)/32 := by positivity
  have hlogratio : Real.log ((n:ℝ)^(n/2)/b^k) ≤ Real.log ((epsilon:ℝ)/32) := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_pow]
    have hcancel : Real.log ((epsilon:ℝ)/32) = -Real.log (32/(epsilon:ℝ)) := by
      rw [Real.log_div (by positivity) (by norm_num),Real.log_div (by norm_num) (by positivity)]
      ring
    rw [hcancel]
    dsimp [L] at hkl
    linarith
  have hreal : (n:ℝ)^(n/2)/(1+1/(n:ℝ))^k ≤ (epsilon:ℝ)/32 :=
    (Real.log_le_log_iff ha0 ht0).mp hlogratio
  have hrat : (n:ℚ)^(n/2)/(1+1/(n:ℚ))^k ≤ epsilon/32 := by
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hreal
  have hex : ∃ k, scheduleAdmissible n epsilon k := ⟨k,hk1,hrat⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
  · intro j hj
    exact Nat.find_min' hex hj
  · have hleast : Nat.find hex ≤ k := Nat.find_min' hex ⟨hk1,hrat⟩
    have hlr : (Nat.find hex:ℝ) ≤ k := by exact_mod_cast hleast
    change (Nat.find hex:ℝ) ≤ 1+C
    linarith

end MatchingFPRAS.Counting

end OAI
