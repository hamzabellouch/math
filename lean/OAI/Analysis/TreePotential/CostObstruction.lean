import OAI.Analysis.TreePotential.QuadraticCost

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section BoundaryTrees
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma subspace_radial_adjustment (F : Submodule ℝ E) {d w : E} (hw : w ∈ F)
    {r : ℝ} (hr : 0 < r) (hrd : r ≤ ‖d‖) (he : ‖d-w‖ < r) :
    ∃ u : E, u ∈ F ∧ r ≤ ‖u‖ ∧ ‖d-u‖ ≤ 2*‖d-w‖ := by
  by_cases hrw : r ≤ ‖w‖
  · exact ⟨w, hw, hrw, by nlinarith [norm_nonneg (d-w)]⟩
  have hwr : ‖w‖ < r := lt_of_not_ge hrw
  have hwn : 0 < ‖w‖ := by nlinarith [norm_sub_norm_le d w]
  let a := r / ‖w‖
  have ha : 0 < a := div_pos hr hwn
  have ham : 0 ≤ a-1 := by
    dsimp [a]
    exact sub_nonneg.mpr ((le_div_iff₀ hwn).mpr (by linarith))
  have haw : a * ‖w‖ = r := div_mul_cancel₀ _ (ne_of_gt hwn)
  have hn : ‖a • w‖ = r := by rw [norm_smul, Real.norm_of_nonneg ha.le, haw]
  have hd : ‖w-a • w‖ = r-‖w‖ := by
    rw [norm_sub_rev]
    have heq : a • w-w = (a-1) • w := by module
    rw [heq, norm_smul, Real.norm_of_nonneg ham]
    nlinarith
  refine ⟨a • w, F.smul_mem a hw, hn.ge, ?_⟩
  have hp := norm_add_le (d-w) (w-a • w)
  rw [sub_add_sub_cancel, hd] at hp
  nlinarith [norm_sub_norm_le d w]

/-- Boundary radius is allowed: correcting a quotient approximant radially
costs at most twice its approximation error. -/
lemma oneSided_growth_boundary {t γ c : ℝ} (ht : 0 < t) (hγ : 0 < γ)
    (hδ : (γ : EReal) < oneSidedModulus E t) (p : E) (hp : 0 < ‖p‖)
    (htp : t * ‖p‖ ≤ c) (d : ℕ → E) (hd : WeaklyNull d)
    (hdn : ∀ n, c ≤ ‖d n‖) :
    ∃ n, ‖p‖ + γ * ‖p‖ / 2 ≤ ‖p + d n‖ := by
  obtain ⟨F, hF⟩ := oneSided_wide_tail ht hγ.le hδ p hp
  have hε : 0 < min (t*‖p‖) (γ*‖p‖/4) := lt_min (by positivity) (by positivity)
  obtain ⟨n, w, hw, he⟩ := (hd.approximable F hε).exists
  obtain ⟨u, hu, hun, hed⟩ := subspace_radial_adjustment F.space hw (mul_pos ht hp)
    (htp.trans (hdn n)) (he.trans_le (min_le_left _ _))
  have huf := hF u hu hun
  have hpert := norm_sub_norm_le (p+u) (p+d n)
  have heq : (p+u)-(p+d n) = u-d n := by abel
  rw [heq, norm_sub_rev] at hpert
  have heγ := he.trans_le (min_le_right (t*‖p‖) (γ*‖p‖/4))
  exact ⟨n, by linarith⟩

theorem bounded_tree_modulus_eq_zero_le
    (p : (h : ℕ) → Tree h → E) {m M c t : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hc : 0 < c)
    (hbound : ∀ h, 1 ≤ h → ∀ s : Tree h, m ≤ ‖p h s‖ ∧ ‖p h s‖ ≤ M)
    (hweak : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun n => p h (child s hs n) - p h s))
    (hinc : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (n : ℕ),
      c ≤ ‖p h (child s hs n) - p h s‖)
    (ht : 0 < t) (htM : t*M ≤ c) :
    oneSidedModulus E t = 0 := by
  apply le_antisymm ?_ (oneSidedModulus_nonneg _)
  by_contra hnot
  obtain ⟨γ, hγ, hγδ⟩ := exists_pos_real_lt_ereal (lt_of_not_ge hnot)
  have hM : 0 < M := hm.trans_le hmM
  let a := min (γ * m / 2) c
  have ha : 0 < a := lt_min (by positivity) hc
  obtain ⟨n, hn⟩ := exists_nat_gt (M / a)
  let H := n + 1
  have hH : 1 ≤ H := Nat.le_add_left 1 n
  have hlarge : M < m + (H : ℝ) * a := by
    have hn' : M < (n : ℝ) * a := (div_lt_iff₀ ha).mp hn
    simp only [H, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hpath : ∀ j : ℕ, j ≤ H → ∃ s : Tree H,
      s.val.length = j ∧ m + (j : ℝ) * a ≤ ‖p H s‖ := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨root H, rfl, by simpa using (hbound H hH (root H)).1⟩
    | succ j ih =>
      intro hj
      obtain ⟨s, hsl, hsn⟩ := ih (Nat.le_of_succ_le hj)
      have hs : s.val.length < H := by omega
      have hpb := hbound H hH s
      have hp : 0 < ‖p H s‖ := hm.trans_le hpb.1
      have htp : t * ‖p H s‖ ≤ c :=
        (mul_le_mul_of_nonneg_left hpb.2 ht.le).trans htM
      obtain ⟨i, hi⟩ := oneSided_growth_boundary ht hγ hγδ (p H s) hp htp
        (fun n => p H (child s hs n) - p H s) (hweak H hH s hs) (hinc H hH s hs)
      rw [add_sub_cancel] at hi
      refine ⟨child s hs i, by simp [hsl], ?_⟩
      have hgrowth : a ≤ γ * ‖p H s‖ / 2 := by
        exact (min_le_left _ _).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpb.1 hγ.le) (by norm_num))
      rw [Nat.cast_succ]
      nlinarith
  obtain ⟨s, hs, hsn⟩ := hpath H le_rfl
  have hb := (hbound H hH s).2
  linarith


end BoundaryTrees

section CostBranching
open scoped Classical

lemma prefix_child_iff (r s : List ℕ) (j : ℕ) :
    r <+: s ++ [j] ↔ r <+: s ∨ r = s ++ [j] := by
  simp only [← List.mem_inits]
  simp [List.inits_append]

lemma rootPath_child {n : ℕ} (s : Tree n) (hs : s.val.length < n) (j : ℕ) :
    rootPath (child s hs j) = rootPath s + lp.single 2 (child s hs j) 1 := by
  ext r
  simp only [rootPath_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_single, Pi.single_apply,
    mem_pathNodes_iff, child, prefix_child_iff]
  by_cases he : r.val = s.val ++ [j]
  · have hp : ¬ r.val <+: s.val := by
      intro hh
      have hlen := hh.length_le
      simp only [he, List.length_append, List.length_singleton] at hlen
      omega
    have hr : (⟨s.val ++ [j], by simp only [List.length_append, List.length_singleton]; omega⟩ : Tree n) = r :=
      Subtype.ext he.symm
    have hp' : ¬ s.val ++ [j] <+: s.val := by simpa only [he] using hp
    simp [he, hp', hr]
  · have hr : (⟨s.val ++ [j], by simp only [List.length_append, List.length_singleton]; omega⟩ : Tree n) ≠ r :=
      fun h => he (congrArg Subtype.val h).symm
    simp [he, Ne.symm hr]

lemma single_sequence_weaklyNull {I : Type*} [DecidableEq I] (v : ℕ → I) (hv : Function.Injective v) :
    WeaklyNull (fun j => (lp.single 2 (v j) (1 : ℝ) : lp (fun _ : I => ℝ) 2)) := by
  intro φ
  have hs : Summable (fun i : I => φ (lp.single 2 i (1 : ℝ))^2) :=
    summable_of_sum_le (fun _ => sq_nonneg _)
      (hilbert_upper_eval_sq_sum (fun i : I => lp.single 2 i (1 : ℝ))
        (single_hilbert_upper (fun _ : I => ℝ) (fun _ => (1 : ℝ)) (fun _ => by norm_num)) φ)
  have ht := (hs.comp_injective hv).tendsto_atTop_zero.sqrt
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht

def raiseTree {h : ℕ} (s : Tree h) : Tree (h+1) := ⟨s.val, s.property.trans (Nat.le_succ h)⟩
lemma raiseTree_child {h : ℕ} (s : Tree h) (hs : s.val.length < h) (j : ℕ) :
    raiseTree (child s hs j) = child (raiseTree s) (by simp only [raiseTree]; omega) j := rfl

def linearOuterInsert (n : ℕ) : LinearBlock (n+1) →L[ℝ] LinearOuter :=
  lp.singleContinuousLinearMap ℝ (fun k : ℕ => LinearBlock (k+1)) 2 n

def linearOuterTree (h : ℕ) (s : Tree h) : LinearOuter :=
  linearOuterInsert h ((linearBlockHilbertEquiv (h+1)).symm (rootPath (raiseTree s)))

lemma linearOuterTree_difference (h : ℕ) (s : Tree h) (hs : s.val.length < h) (j : ℕ) :
    linearOuterTree h (child s hs j) - linearOuterTree h s =
      linearOuterInsert h ((linearBlockHilbertEquiv (h+1)).symm
        (lp.single 2 (raiseTree (child s hs j)) 1)) := by
  simp only [linearOuterTree, raiseTree_child, rootPath_child, map_add, add_sub_cancel_left]

lemma linearOuterTree_weak (h : ℕ) (s : Tree h) (hs : s.val.length < h) :
    WeaklyNull (fun j => linearOuterTree h (child s hs j) - linearOuterTree h s) := by
  simp only [linearOuterTree_difference]
  have hw := single_sequence_weaklyNull (fun j => raiseTree (child s hs j)) (by
    intro i j hij
    have he := congrArg Subtype.val hij
    exact TreeCalculus.childNode_injective s.val he)
  simpa only [ContinuousLinearEquiv.coe_coe] using
    (hw.map (linearBlockHilbertEquiv (h+1)).symm.toContinuousLinearMap).map (linearOuterInsert h)

lemma linearOuterTree_norm (h : ℕ) (s : Tree h) :
    ‖linearOuterTree h s‖ = 1 := by
  simp only [linearOuterTree, linearOuterInsert, lp.singleContinuousLinearMap_apply,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact linearBlockCost_rootPath _

lemma linearOuterTree_increment (h : ℕ) (s : Tree h) (hs : s.val.length < h) (j : ℕ) :
    ‖linearOuterTree h (child s hs j) - linearOuterTree h s‖ = 1 := by
  rw [linearOuterTree_difference]
  simp only [linearOuterInsert, lp.singleContinuousLinearMap_apply,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact linearBlockCost_singleton _

def quadraticOuterInsert (n : ℕ) : QuadraticBlock (n+1) →L[ℝ] QuadraticOuter :=
  lp.singleContinuousLinearMap ℝ (fun k : ℕ => QuadraticBlock (k+1)) 2 n

def quadraticOuterTree (h : ℕ) (s : Tree h) : QuadraticOuter :=
  quadraticOuterInsert h ((quadraticBlockHilbertEquiv (h+1)).symm (rootPath (raiseTree s)))

lemma quadraticOuterTree_difference (h : ℕ) (s : Tree h) (hs : s.val.length < h) (j : ℕ) :
    quadraticOuterTree h (child s hs j) - quadraticOuterTree h s =
      quadraticOuterInsert h ((quadraticBlockHilbertEquiv (h+1)).symm
        (lp.single 2 (raiseTree (child s hs j)) 1)) := by
  simp only [quadraticOuterTree, raiseTree_child, rootPath_child, map_add, add_sub_cancel_left]

lemma quadraticOuterTree_weak (h : ℕ) (s : Tree h) (hs : s.val.length < h) :
    WeaklyNull (fun j => quadraticOuterTree h (child s hs j) - quadraticOuterTree h s) := by
  simp only [quadraticOuterTree_difference]
  have hw := single_sequence_weaklyNull (fun j => raiseTree (child s hs j)) (by
    intro i j hij
    have he := congrArg Subtype.val hij
    exact TreeCalculus.childNode_injective s.val he)
  simpa only [ContinuousLinearEquiv.coe_coe] using
    (hw.map (quadraticBlockHilbertEquiv (h+1)).symm.toContinuousLinearMap).map (quadraticOuterInsert h)

lemma quadraticOuterTree_norm (h : ℕ) (s : Tree h) :
    1 / Real.sqrt 2 ≤ ‖quadraticOuterTree h s‖ ∧ ‖quadraticOuterTree h s‖ ≤ 1 := by
  simp only [quadraticOuterTree, quadraticOuterInsert, lp.singleContinuousLinearMap_apply,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact quadraticBlockCost_path_bounds _

lemma quadraticOuterTree_increment (h : ℕ) (s : Tree h) (hs : s.val.length < h) (j : ℕ) :
    1 / Real.sqrt 2 ≤ ‖quadraticOuterTree h (child s hs j) - quadraticOuterTree h s‖ := by
  rw [quadraticOuterTree_difference]
  simp only [quadraticOuterInsert, lp.singleContinuousLinearMap_apply,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact (quadraticBlockCost_single_bounds _).1

end CostBranching

section CostObstructions
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The boundary radius alpha/beta is included. -/
theorem linearOuter_renorming_obstruction (e : LinearOuter ≃L[ℝ] Y) {α β t : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖)
    (ht : 0 < t) (htb : t ≤ α/β) : oneSidedModulus Y t = 0 := by
  have hβ : 0 < β := hα.trans_le hαβ
  apply bounded_tree_modulus_eq_zero_le (fun h s => e (linearOuterTree h s)) hα hαβ hα
  · intro h hh s
    simpa only [linearOuterTree_norm, mul_one] using he (linearOuterTree h s)
  · intro h hh s hs
    simpa only [map_sub, ContinuousLinearEquiv.coe_coe] using (linearOuterTree_weak h s hs).map e.toContinuousLinearMap
  · intro h hh s hs j
    rw [← map_sub]
    simpa only [linearOuterTree_increment, mul_one] using (he (linearOuterTree h (child s hs j)-linearOuterTree h s)).1
  · exact ht
  · exact (le_div_iff₀ hβ).mp htb

theorem quadraticOuter_renorming_obstruction (e : QuadraticOuter ≃L[ℝ] Y) {α β t : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x, α * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β * ‖x‖)
    (ht : 0 < t) (htb : t ≤ α/(Real.sqrt 2*β)) : oneSidedModulus Y t = 0 := by
  have hβ : 0 < β := hα.trans_le hαβ
  have htwo : 0 < Real.sqrt (2 : ℝ) := by positivity
  have htwo1 : 1 ≤ Real.sqrt (2 : ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hab : α/Real.sqrt 2 ≤ β := (div_le_self hα.le htwo1).trans hαβ
  apply bounded_tree_modulus_eq_zero_le (fun h s => e (quadraticOuterTree h s))
    (div_pos hα htwo) hab (div_pos hα htwo)
  · intro h hh s
    have hb := quadraticOuterTree_norm h s
    have he' := he (quadraticOuterTree h s)
    constructor
    · have hi := mul_le_mul_of_nonneg_left hb.1 hα.le
      rw [mul_one_div] at hi
      exact hi.trans he'.1
    · nlinarith
  · intro h hh s hs
    simpa only [map_sub, ContinuousLinearEquiv.coe_coe] using (quadraticOuterTree_weak h s hs).map e.toContinuousLinearMap
  · intro h hh s hs j
    rw [← map_sub]
    have hi := mul_le_mul_of_nonneg_left (quadraticOuterTree_increment h s hs j) hα.le
    rw [mul_one_div] at hi
    exact hi.trans (he _).1
  · exact ht
  · have hh := (le_div_iff₀ (mul_pos htwo hβ)).mp htb
    apply (le_div_iff₀ htwo).mpr
    nlinarith [hh]

theorem linearOuter_no_equivalent_AUC (e : LinearOuter ≃L[ℝ] Y) : ¬ IsAUC Y := by
  obtain ⟨α, β, hα, hαβ, he⟩ := continuousEquiv_bounds e
  have hβ : 0 < β := hα.trans_le hαβ
  intro hauc
  have h := hauc (α/β) (by positivity)
  rw [linearOuter_renorming_obstruction e hα hαβ he (by positivity) le_rfl] at h
  exact lt_irrefl _ h

theorem quadraticOuter_no_equivalent_AUC (e : QuadraticOuter ≃L[ℝ] Y) : ¬ IsAUC Y := by
  obtain ⟨α, β, hα, hαβ, he⟩ := continuousEquiv_bounds e
  have hβ : 0 < β := hα.trans_le hαβ
  intro hauc
  have h := hauc (α/(Real.sqrt 2*β)) (by positivity)
  rw [quadraticOuter_renorming_obstruction e hα hαβ he (by positivity) le_rfl] at h
  exact lt_irrefl _ h

end CostObstructions


end BoundedTreePotentials

end

end OAI
