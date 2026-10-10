import OAI.Geometry.DoublingHilbert.Model

namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

abbrev Base := ℝ × ℝ
abbrev Tuple := ℕ →₀ ℕ

/-- The scale at index `j` has exponent `j + 1`. -/
def scale (j : ℕ) : ℝ := (1000 : ℝ)⁻¹ ^ (j + 1)

def colors (j : ℕ) : ℕ := (Nat.unpair (Nat.unpair j).1).1 + 1

def widthFactor (j : ℕ) : ℕ := (Nat.unpair (Nat.unpair j).1).2 + 1

theorem colors_pos (j : ℕ) : 0 < colors j := Nat.succ_pos _

theorem widthFactor_pos (j : ℕ) : 0 < widthFactor j := Nat.succ_pos _

theorem recurrent_parameters (N W J : ℕ) (hN : 0 < N) (hW : 0 < W) :
    ∃ j ≥ J, colors j = N ∧ widthFactor j = W := by
  refine ⟨Nat.pair (Nat.pair (N - 1) (W - 1)) J, Nat.right_le_pair _ _, ?_⟩
  simp only [colors, widthFactor, Nat.unpair_pair]
  omega

theorem scale_pos (j : ℕ) : 0 < scale j := by unfold scale; positivity

theorem scale_succ (j : ℕ) : scale (j + 1) = scale j / 1000 := by
  simp [scale, pow_succ, div_eq_mul_inv]

def inColoredStrip (width : ℝ) (N i : ℕ) (t : ℝ) : Prop :=
  ∃ q : ℤ, q % (N : ℤ) = (i : ℤ) ∧ (q : ℝ) * width < t ∧
    t < ((q : ℝ) + 1) * width

def allowed (j i : ℕ) (p : Base) : Prop :=
  inColoredStrip (scale j) (colors j) i p.2 ∨
    inColoredStrip ((widthFactor j : ℝ) * scale j) (colors j) i p.1

/-- Value zero means no displacement; a nonzero tuple entry `i+1` means color `i`. -/
def admissible (p : Base) (w : Tuple) : Prop :=
  ∀ j ∈ w.support, w j ≤ colors j ∧ allowed j (w j - 1) p

def sheetDomain (w : Tuple) : Set Base := {p | admissible p w}

def coordinate (j i : ℕ) : ℕ := 2 + Nat.pair j i

noncomputable def levelVector (j i : ℕ) : RealL2 :=
  lp.single 2 (coordinate j i) (scale j)

noncomputable def tupleVector (w : Tuple) : RealL2 :=
  ∑ j ∈ w.support, levelVector j (w j - 1)

noncomputable def baseVector (p : Base) : RealL2 :=
  lp.single 2 0 p.1 + lp.single 2 1 p.2

noncomputable def point (p : Base) (w : Tuple) : RealL2 :=
  baseVector p + tupleVector w

/-- The fixed subset defined by finite-support displacements and open-strip conditions. -/
def constructedSet : Set RealL2 := {z | ∃ p w, admissible p w ∧ z = point p w}

theorem isOpen_inColoredStrip (width : ℝ) (N i : ℕ) :
    IsOpen {t : ℝ | inColoredStrip width N i t} := by
  have h : {t : ℝ | inColoredStrip width N i t} =
      ⋃ (q : ℤ) (_ : q % (N : ℤ) = (i : ℤ)),
        Ioo ((q : ℝ) * width) (((q : ℝ) + 1) * width) := by
    ext t
    simp [inColoredStrip, and_left_comm]
  rw [h]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo

theorem isOpen_allowed (j i : ℕ) : IsOpen {p : Base | allowed j i p} :=
  ((isOpen_inColoredStrip _ _ _).preimage continuous_snd).union
    ((isOpen_inColoredStrip _ _ _).preimage continuous_fst)

theorem isOpen_sheetDomain (w : Tuple) : IsOpen (sheetDomain w) := by
  classical
  by_cases hw : ∀ j ∈ w.support, w j ≤ colors j
  · have h : sheetDomain w = ⋂ j ∈ w.support, {p : Base | allowed j (w j - 1) p} := by
      ext p
      simp only [sheetDomain, mem_ofPred_eq, admissible, mem_iInter]
      exact ⟨fun h j hj => (h j hj).2, fun h j hj => ⟨hw j hj, h j hj⟩⟩
    rw [h]
    exact isOpen_biInter_finset fun j _ => isOpen_allowed j _
  · have h : sheetDomain w = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hw (fun j hj => (hp j hj).1)
    rw [h]
    exact isOpen_empty

@[simp] theorem admissible_zero (p : Base) : admissible p 0 := by simp [admissible]

@[simp] theorem tupleVector_zero : tupleVector 0 = 0 := by simp [tupleVector]

@[simp] theorem point_zero (p : Base) : point p 0 = baseVector p := by simp [point]

theorem point_mem (p : Base) (w : Tuple) (h : admissible p w) :
    point p w ∈ constructedSet := ⟨p, w, h, rfl⟩

theorem coordinate_injective : Function.Injective (fun ji : ℕ × ℕ => coordinate ji.1 ji.2) := by
  intro a b h
  apply Nat.pairEquiv.injective
  exact Nat.add_left_cancel h

@[simp] theorem coordinate_ne_zero (j i : ℕ) : coordinate j i ≠ 0 := by
  unfold coordinate; omega

@[simp] theorem coordinate_ne_one (j i : ℕ) : coordinate j i ≠ 1 := by
  unfold coordinate; omega

@[simp] theorem norm_levelVector (j i : ℕ) : ‖levelVector j i‖ = scale j := by
  rw [levelVector, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  exact Real.norm_of_nonneg (scale_pos j).le

@[simp] theorem inner_levelVector (j i m h : ℕ) :
    inner ℝ (levelVector j i) (levelVector m h) =
      if j = m ∧ i = h then scale j * scale m else 0 := by
  classical
  rw [levelVector, lp.inner_single_left]
  simp only [levelVector, lp.single_apply, RCLike.inner_apply, conj_trivial]
  by_cases heq : coordinate j i = coordinate m h
  · have heq' : (j, i) = (m, h) := coordinate_injective heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq'
    simp
  · have hneq : ¬ (j = m ∧ i = h) := by
      rintro ⟨rfl, rfl⟩
      exact heq rfl
    simp [heq, hneq]

theorem norm_levelVector_sub_sq (j i h : ℕ) (hih : i ≠ h) :
    ‖levelVector j i - levelVector j h‖ ^ 2 = 2 * (scale j) ^ 2 := by
  rw [norm_sub_sq_real]
  simp [hih]
  ring

theorem baseVector_sub (p q : Base) :
    baseVector p - baseVector q = baseVector (p - q) := by
  simp only [baseVector, Prod.fst_sub, Prod.snd_sub, lp.single_sub]
  abel

theorem baseVector_norm_sq (p : Base) : ‖baseVector p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [baseVector, norm_add_sq_real]
  simp [lp.inner_single_left, lp.single_apply, lp.norm_single, Real.norm_eq_abs, sq_abs]

theorem point_dist_sameTuple_sq (p q : Base) (w : Tuple) :
    dist (point p w) (point q w) ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  rw [dist_eq_norm]
  simp only [point, add_sub_add_right_eq_sub, baseVector_sub, baseVector_norm_sq,
    Prod.fst_sub, Prod.snd_sub]

theorem tupleVector_update (w : Tuple) (j i : ℕ) (hj : w j = 0) :
    tupleVector (w.update j (i + 1)) = tupleVector w + levelVector j i := by
  classical
  have hjs : j ∉ w.support := by simpa using hj
  rw [tupleVector, Finsupp.support_update_ne_zero w (a := j) (by omega : i + 1 ≠ 0), Finset.sum_insert hjs]
  simp only [Finsupp.update_apply, ite_true, Nat.add_sub_cancel]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hmj : m ≠ j := by intro h; subst m; exact hjs hm
  simp [hmj]

theorem point_update (p : Base) (w : Tuple) (j i : ℕ) (hj : w j = 0) :
    point p (w.update j (i + 1)) = point p w + levelVector j i := by
  rw [point, tupleVector_update w j i hj, point, add_assoc]

theorem admissible_update_iff (p : Base) (w : Tuple) (j i : ℕ) (hj : w j = 0) :
    admissible p (w.update j (i + 1)) ↔
      admissible p w ∧ i < colors j ∧ allowed j i p := by
  classical
  have hjs : j ∉ w.support := by simpa using hj
  have hs := Finsupp.support_update_ne_zero w (a := j) (by omega : i + 1 ≠ 0)
  constructor
  · intro h
    have hjh := h j (by rw [hs]; exact Finset.mem_insert_self _ _)
    simp only [Finsupp.update_apply, ite_true, Nat.add_sub_cancel] at hjh
    refine ⟨?_, by omega, hjh.2⟩
    intro m hm
    have hmj : m ≠ j := by intro heq; subst m; exact hjs hm
    have hmh := h m (by rw [hs]; exact Finset.mem_insert_of_mem hm)
    simpa [Finsupp.update_apply, hmj] using hmh
  · rintro ⟨hw, hic, hip⟩ m hm
    rw [hs] at hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · simpa only [Finsupp.update_apply, ite_true, Nat.add_sub_cancel] using
        (show i + 1 ≤ colors m ∧ allowed m i p from ⟨by omega, hip⟩)
    · have hmj : m ≠ j := by intro heq; subst m; exact hjs hm
      simpa [Finsupp.update_apply, hmj] using hw m hm


/-- The complete level coordinate, including zero. -/
def entryVector (w : Tuple) (j : ℕ) : RealL2 :=
  if w j = 0 then 0 else levelVector j (w j - 1)

@[simp] theorem entryVector_eq_zero {w : Tuple} {j : ℕ} (hj : w j = 0) :
    entryVector w j = 0 := by simp [entryVector, hj]

@[simp] theorem entryVector_of_ne_zero {w : Tuple} {j : ℕ} (hj : w j ≠ 0) :
    entryVector w j = levelVector j (w j - 1) := by simp [entryVector, hj]

theorem tupleVector_sum_on (w : Tuple) (s : Finset ℕ) (hs : w.support ⊆ s) :
    tupleVector w = ∑ j ∈ s, entryVector w j := by
  classical
  unfold tupleVector
  symm
  calc
    _ = ∑ j ∈ w.support, entryVector w j := by
      symm
      apply Finset.sum_subset hs
      intro j _ hj
      exact entryVector_eq_zero (by simpa using hj)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact entryVector_of_ne_zero (Finsupp.mem_support_iff.mp hj)

theorem inner_entryVector_entryVector {j m : ℕ} (hjm : j ≠ m) (w w' : Tuple) :
    inner ℝ (entryVector w j) (entryVector w' m) = 0 := by
  classical
  unfold entryVector
  split_ifs <;> simp [hjm]

theorem inner_baseVector_levelVector (p : Base) (j i : ℕ) :
    inner ℝ (baseVector p) (levelVector j i) = 0 := by
  simp [baseVector, inner_add_left, lp.inner_single_left, levelVector, lp.single_apply,
    Ne.symm (coordinate_ne_zero j i), Ne.symm (coordinate_ne_one j i)]

theorem inner_baseVector_entryVector (p : Base) (w : Tuple) (j : ℕ) :
    inner ℝ (baseVector p) (entryVector w j) = 0 := by
  classical
  unfold entryVector
  split_ifs <;> simp [inner_baseVector_levelVector]

/-- Finite Pythagoras for pairwise orthogonal vectors. -/
theorem norm_sum_sq_of_inner_eq_zero {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (v : ι → E)
    (hv : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  rw [Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j hj hji
    exact hv i hi j hj hji.symm
  · exact fun h => (h hi).elim

/-- Exact orthogonal decomposition of source distances. -/
theorem point_dist_sq (p q : Base) (w w' : Tuple) (s : Finset ℕ)
    (hw : w.support ⊆ s) (hw' : w'.support ⊆ s) :
    dist (point p w) (point q w') ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 +
      ∑ j ∈ s, ‖entryVector w j - entryVector w' j‖ ^ 2 := by
  rw [dist_eq_norm]
  have heq : point p w - point q w' = baseVector (p - q) +
      ∑ j ∈ s, (entryVector w j - entryVector w' j) := by
    rw [Finset.sum_sub_distrib, ← tupleVector_sum_on w s hw, ← tupleVector_sum_on w' s hw',
      ← baseVector_sub]
    simp only [point]
    abel
  rw [heq, norm_add_sq_real]
  have hinner : inner ℝ (baseVector (p - q))
      (∑ j ∈ s, (entryVector w j - entryVector w' j)) = 0 := by
    simp [inner_sum, inner_sub_right, inner_baseVector_entryVector]
  rw [hinner, mul_zero, add_zero, baseVector_norm_sq]
  congr 1
  apply norm_sum_sq_of_inner_eq_zero
  intro i _ j _ hij
  simp [inner_sub_left, inner_sub_right, inner_entryVector_entryVector hij]

/-- Distinct choices at one level are at least one scale apart. -/
theorem scale_le_norm_entryVector_sub {w w' : Tuple} {j : ℕ} (hne : w j ≠ w' j) :
    scale j ≤ ‖entryVector w j - entryVector w' j‖ := by
  by_cases hw : w j = 0
  · have hw' : w' j ≠ 0 := by intro h; exact hne (hw.trans h.symm)
    simp [hw, hw']
  · by_cases hw' : w' j = 0
    · simp [hw, hw']
    · rw [entryVector_of_ne_zero hw, entryVector_of_ne_zero hw']
      have hpred : w j - 1 ≠ w' j - 1 := by omega
      have hs := norm_levelVector_sub_sq j (w j - 1) (w' j - 1) hpred
      nlinarith [scale_pos j, norm_nonneg (levelVector j (w j - 1) - levelVector j (w' j - 1))]

theorem norm_entryVector_sub_sq_le (w w' : Tuple) (j : ℕ) :
    ‖entryVector w j - entryVector w' j‖ ^ 2 ≤ 2 * (scale j) ^ 2 := by
  by_cases hw : w j = 0
  · by_cases hw' : w' j = 0
    · simp [hw, hw', sq_nonneg]
    · simp only [entryVector_eq_zero hw, entryVector_of_ne_zero hw', zero_sub,
        norm_neg, norm_levelVector]
      nlinarith [sq_nonneg (scale j)]
  · by_cases hw' : w' j = 0
    · simp only [entryVector_eq_zero hw', entryVector_of_ne_zero hw, sub_zero, norm_levelVector]
      nlinarith [sq_nonneg (scale j)]
    · rw [entryVector_of_ne_zero hw, entryVector_of_ne_zero hw']
      by_cases heq : w j - 1 = w' j - 1
      · simp [heq, sq_nonneg]
      · exact (norm_levelVector_sub_sq _ _ _ heq).le

/-- Every individual level distance is no larger than the whole source distance. -/
theorem norm_entryVector_sub_le_dist (p q : Base) (w w' : Tuple) (j : ℕ) :
    ‖entryVector w j - entryVector w' j‖ ≤ dist (point p w) (point q w') := by
  classical
  let s := insert j (w.support ∪ w'.support)
  have hw : w.support ⊆ s := fun m hm => Finset.mem_insert_of_mem (Finset.mem_union_left _ hm)
  have hw' : w'.support ⊆ s := fun m hm => Finset.mem_insert_of_mem (Finset.mem_union_right _ hm)
  have hdist := point_dist_sq p q w w' s hw hw'
  have hj := Finset.single_le_sum (f := fun m => ‖entryVector w m - entryVector w' m‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_insert_self j (w.support ∪ w'.support))
  nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2), dist_nonneg (x := point p w) (y := point q w')]

theorem abs_fst_sub_le_dist (p q : Base) (w w' : Tuple) :
    |p.1 - q.1| ≤ dist (point p w) (point q w') := by
  classical
  have hd := point_dist_sq p q w w' (w.support ∪ w'.support)
    Finset.subset_union_left Finset.subset_union_right
  have hsum := Finset.sum_nonneg (s := w.support ∪ w'.support)
    (f := fun j => ‖entryVector w j - entryVector w' j‖ ^ 2) (fun _ _ => sq_nonneg _)
  nlinarith [sq_abs (p.1 - q.1), sq_nonneg (p.2 - q.2),
    dist_nonneg (x := point p w) (y := point q w')]

theorem abs_snd_sub_le_dist (p q : Base) (w w' : Tuple) :
    |p.2 - q.2| ≤ dist (point p w) (point q w') := by
  classical
  have hd := point_dist_sq p q w w' (w.support ∪ w'.support)
    Finset.subset_union_left Finset.subset_union_right
  have hsum := Finset.sum_nonneg (s := w.support ∪ w'.support)
    (f := fun j => ‖entryVector w j - entryVector w' j‖ ^ 2) (fun _ _ => sq_nonneg _)
  nlinarith [sq_abs (p.2 - q.2), sq_nonneg (p.1 - q.1),
    dist_nonneg (x := point p w) (y := point q w')]

theorem coarse_coordinate_eq {p q : Base} {w w' : Tuple} {t : ℝ}
    (hd : dist (point p w) (point q w') < t) {j : ℕ} (hj : t ≤ scale j) : w j = w' j := by
  by_contra hne
  exact (not_le_of_gt hd) (hj.trans ((scale_le_norm_entryVector_sub hne).trans
    (norm_entryVector_sub_le_dist p q w w' j)))

theorem point_dist_sameTuple_le (p q : Base) (w : Tuple) :
    dist (point p w) (point q w) ≤ 2 * dist p q := by
  have hd := point_dist_sameTuple_sq p q w
  have hx : |p.1 - q.1| ≤ dist p q := by simp [Real.dist_eq, Prod.dist_eq]
  have hy : |p.2 - q.2| ≤ dist p q := by simp [Real.dist_eq, Prod.dist_eq]
  have hxs : (p.1 - q.1)^2 ≤ (dist p q)^2 := by nlinarith [sq_abs (p.1 - q.1), abs_nonneg (p.1 - q.1)]
  have hys : (p.2 - q.2)^2 ≤ (dist p q)^2 := by nlinarith [sq_abs (p.2 - q.2), abs_nonneg (p.2 - q.2)]
  nlinarith [dist_nonneg (x := p) (y := q), dist_nonneg (x := point p w) (y := point q w)]

theorem scale_antitone : Antitone scale := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hij 1)

theorem scale_le_div_of_lt {i j : ℕ} (hij : i < j) : scale j ≤ scale i / 1000 := by
  rw [← scale_succ]
  exact scale_antitone hij

theorem intermediate_unique {t : ℝ} {i j : ℕ}
    (hi : t / 64 < scale i ∧ scale i ≤ t) (hj : t / 64 < scale j ∧ scale j ≤ t) : i = j := by
  rcases lt_trichotomy i j with hij | heq | hji
  · have h := scale_le_div_of_lt hij
    have hp := scale_pos i
    linarith
  · exact heq
  · have h := scale_le_div_of_lt hji
    have hp := scale_pos j
    linarith

theorem scale_add (i j : ℕ) : scale (i + j) = scale i * (1000 : ℝ)⁻¹ ^ j := by
  simp only [scale]
  rw [show i + j + 1 = (i + 1) + j by omega, pow_add]

/-- A deliberately coarse geometric-tail bound, adequate for the covering constant. -/
theorem sum_scale_sq_le {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j ∈ s, scale j ≤ R) : ∑ j ∈ s, (scale j) ^ 2 ≤ 2 * R ^ 2 := by
  classical
  by_cases hse : s.Nonempty
  · let m := s.min' hse
    have hm : m ∈ s := s.min'_mem hse
    have hmj (j : ℕ) (hj : j ∈ s) : m ≤ j := s.min'_le j hj
    have hgeom := (summable_geometric_of_abs_lt_one (r := (1000000 : ℝ)⁻¹) (by norm_num)).sum_le_tsum
      (s.image (fun j => j - m)) (fun _ _ => by positivity)
    rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1000000 : ℝ)⁻¹| < 1)] at hgeom
    have himage : (∑ j ∈ s.image (fun j => j - m), (1000000 : ℝ)⁻¹ ^ j) =
        ∑ j ∈ s, (1000000 : ℝ)⁻¹ ^ (j - m) := by
      apply Finset.sum_image
      intro i hi j hj he
      dsimp at he
      have := hmj i hi
      have := hmj j hj
      omega
    rw [himage] at hgeom
    have heq : (∑ j ∈ s, scale j ^ 2) = scale m ^ 2 *
        ∑ j ∈ s, (1000000 : ℝ)⁻¹ ^ (j - m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : m + (j - m) = j := Nat.add_sub_of_le (hmj j hj)
      conv_lhs => rw [← hj', scale_add]
      rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [heq]
    calc
      _ ≤ scale m ^ 2 * (1 - (1000000 : ℝ)⁻¹)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom (sq_nonneg _)
      _ ≤ 2 * scale m ^ 2 := by nlinarith [sq_nonneg (scale m)]
      _ ≤ 2 * R ^ 2 := by nlinarith [hs m hm, scale_pos m]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hse, Finset.sum_empty]
    positivity

/-- A uniform squared-distance bound for the finite-coordinate fine tail. -/
theorem fine_tail_le (w w' : Tuple) (s : Finset ℕ) {t : ℝ} (ht : 0 < t)
    (hs : ∀ j ∈ s, scale j ≤ t / 64) :
    ∑ j ∈ s, ‖entryVector w j - entryVector w' j‖ ^ 2 ≤ t ^ 2 / 1024 := by
  calc
    _ ≤ ∑ j ∈ s, 2 * scale j ^ 2 := Finset.sum_le_sum fun j _ => norm_entryVector_sub_sq_le w w' j
    _ = 2 * ∑ j ∈ s, scale j ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (2 * (t / 64) ^ 2) := by
      gcongr
      exact sum_scale_sq_le (by positivity) hs
    _ = t ^ 2 / 1024 := by ring

end DoublingHilbert

end

end OAI
