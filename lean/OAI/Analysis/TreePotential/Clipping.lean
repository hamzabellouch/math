import OAI.Analysis.TreePotential.CostObstruction

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace BlockCalculus
open TreeCalculus
open scoped Classical

/-- Zero extension, including the root; longer path sums freeze at height n. -/
def extendCoeff {n : ℕ} (f : TreeHilbert n) (s : Node) : ℝ :=
  if hs : s.length ≤ n then f ⟨s,hs⟩ else 0

@[simp] lemma extendCoeff_apply {n : ℕ} (f : TreeHilbert n) (s : Tree n) :
    extendCoeff f s.val = f s := by simp [extendCoeff, s.property]

lemma pathPotential_root {n : ℕ} (f : TreeHilbert n) : pathPotential f (root n) = f (root n) := by
  have he : pathNodes (root n) = {root n} := by
    ext r
    rw [mem_pathNodes_iff, Finset.mem_singleton]
    change r.val <+: [] ↔ r = root n
    simp [Subtype.ext_iff, root]
  simp only [pathPotential, he, Finset.sum_singleton]

lemma pathPotential_child {n : ℕ} (f : TreeHilbert n) (s : Tree n)
    (hs : s.val.length < n) (j : ℕ) :
    pathPotential f (child s hs j) = pathPotential f s + f (child s hs j) := by
  rw [← inner_rootPath, rootPath_child, inner_add_right, inner_rootPath]
  simp [lp.inner_single_right, RCLike.inner_apply]

lemma potential_extendCoeff {n : ℕ} (f : TreeHilbert n) (s : Tree n) :
    potential (extendCoeff f) s.val = pathPotential f s := by
  rcases s with ⟨s,hs⟩
  induction s using List.reverseRecOn with
  | nil => simpa only [potential_root, extendCoeff, List.length_nil, Nat.zero_le, dite_eq_left, root] using (pathPotential_root f).symm
  | append_singleton s j ih =>
    have hsl : s.length ≤ n := by simp only [List.length_append, List.length_singleton] at hs; omega
    have hst : s.length < n := by simp only [List.length_append, List.length_singleton] at hs; omega
    rw [potential_child, ih hsl]
    have he := pathPotential_child f (⟨s,hsl⟩ : Tree n) hst j
    simpa only [child, extendCoeff, dite_eq_left hs] using he.symm

lemma extendCoeff_potential_bound {n : ℕ} (f : TreeHilbert n) (s : Node) :
    |potential (extendCoeff f) s| ≤ pathBound f := by
  induction s using List.reverseRecOn with
  | nil =>
    have he := path_le_pathBound f (root n)
    rw [pathPotential_root] at he
    simpa [potential, extendCoeff, root] using he
  | append_singleton s j ih =>
    by_cases hs : (s++[j]).length ≤ n
    · rw [potential_extendCoeff f (⟨s++[j],hs⟩ : Tree n)]
      exact path_le_pathBound f ⟨s++[j],hs⟩
    · simpa only [potential_child, extendCoeff, dite_eq_right hs, add_zero] using ih

def dominatedHilbert {n : ℕ} (f : TreeHilbert n) (g : Tree n → ℝ)
    (hg : ∀ s, |g s| ≤ |f s|) : TreeHilbert n :=
  ⟨g, (lp.memℓp f).norm.mono (by intro s; simpa only [Real.norm_eq_abs] using hg s)⟩

lemma dominatedHilbert_norm_le {n : ℕ} (f : TreeHilbert n) (g : Tree n → ℝ)
    (hg : ∀ s, |g s| ≤ |f s|) : ‖dominatedHilbert f g hg‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro s
  change |g s| ≤ |f s|
  exact hg s

def head {n : ℕ} (D : Set Node) (f : TreeHilbert n) : TreeHilbert n :=
  dominatedHilbert f (fun s => if s.val ∈ D then f s else 0)
    (by intro s; split_ifs <;> simp)

@[simp] lemma head_apply {n : ℕ} (D : Set Node) (f : TreeHilbert n) (s : Tree n) :
    head D f s = if s.val ∈ D then f s else 0 := rfl

lemma head_norm_le {n : ℕ} (D : Set Node) (f : TreeHilbert n) : ‖head D f‖ ≤ ‖f‖ :=
  dominatedHilbert_norm_le ..

lemma head_extendCoeff {n : ℕ} (D : Set Node) (f : TreeHilbert n) :
    extendCoeff (head D f) = headPart D (extendCoeff f) := by
  funext s
  by_cases hs : s.length ≤ n <;> by_cases hd : s ∈ D <;> simp [extendCoeff, headPart, hs, hd]

lemma head_pathBound_le {n : ℕ} {D : Set Node} (hD : Initial D) (f : TreeHilbert n) :
    pathBound (head D f) ≤ pathBound f := by
  apply ciSup_le
  intro s
  rw [← potential_extendCoeff, head_extendCoeff]
  exact head_potential_bound hD (pathBound_nonneg f) (extendCoeff_potential_bound f) s.val

lemma head_linearPolar_le {n : ℕ} {D : Set Node} (hD : Initial D) (f : TreeHilbert n) :
    linearPolar n (head D f) ≤ linearPolar n f :=
  max_le_max (head_norm_le D f) (head_pathBound_le hD f)

lemma head_quadraticPolar_le {n : ℕ} {D : Set Node} (hD : Initial D) (f : TreeHilbert n) :
    quadraticPolar n (head D f) ≤ quadraticPolar n f := by
  apply Real.sqrt_le_sqrt
  have h1 := head_norm_le D f
  have h2 := head_pathBound_le hD f
  nlinarith [norm_nonneg f, norm_nonneg (head D f), pathBound_nonneg f, pathBound_nonneg (head D f)]

def headLM {n : ℕ} (D : Set Node) : TreeHilbert n →ₗ[ℝ] TreeHilbert n where
  toFun := head D
  map_add' f g := by ext s; simp only [head_apply, lp.coeFn_add, Pi.add_apply]; split_ifs <;> simp
  map_smul' a f := by ext s; simp only [head_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

def headCLM {n : ℕ} (D : Set Node) : TreeHilbert n →L[ℝ] TreeHilbert n :=
  (headLM D).mkContinuous 1 (by intro f; change ‖head D f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using head_norm_le D f)

lemma head_inner {n : ℕ} (D : Set Node) (f x : TreeHilbert n) :
    inner ℝ (head D f) x = inner ℝ f (head D x) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro s
  simp only [head_apply]
  split_ifs <;> simp

lemma head_idem {n : ℕ} (D : Set Node) (f : TreeHilbert n) : head D (head D f) = head D f := by
  ext s
  simp only [head_apply]
  split_ifs <;> simp

lemma head_eq_iff {n : ℕ} (D : Set Node) (f : TreeHilbert n) :
    head D f = f ↔ ∀ s, s.val ∉ D → f s = 0 := by
  constructor
  · intro h s hs
    simpa only [head_apply, ite_eq_right hs] using (congrArg (fun v : TreeHilbert n => v s) h).symm
  · intro h
    ext s
    by_cases hs : s.val ∈ D <;> simp [hs, h]

lemma extendCoeff_head_support {n : ℕ} {D : Set Node} {h : TreeHilbert n}
    (hh : head D h = h) : ∀ s, s ∉ D → extendCoeff h s = 0 := by
  intro s hs
  by_cases hn : s.length ≤ n
  · simpa only [extendCoeff, dite_eq_left hn] using (head_eq_iff D h).mp hh ⟨s,hn⟩ hs
  · simp [extendCoeff, hn]

lemma linearBlockCost_norming (n : ℕ) (x : TreeHilbert n) :
    ∃ f : TreeHilbert n, linearPolar n f ≤ 1 ∧ inner ℝ f x = linearBlockCost n x := by
  obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' ℝ ((linearBlockHilbertEquiv n).symm x)
  obtain ⟨f, rfl⟩ := blockFunctional_surjective n φ
  refine ⟨f, ?_, hφx⟩
  rwa [blockFunctional_norm] at hφ

lemma head_linearCost_le {n : ℕ} {D : Set Node} (hD : Initial D) (x : TreeHilbert n) :
    linearBlockCost n (head D x) ≤ linearBlockCost n x := by
  obtain ⟨f, hf, he⟩ := linearBlockCost_norming n (head D x)
  rw [← he, ← head_inner]
  exact linearBlockCost_eval_le ((head_linearPolar_le hD f).trans hf) x

lemma head_quadraticCost_le {n : ℕ} {D : Set Node} (hD : Initial D) (x : TreeHilbert n) :
    quadraticBlockCost n (head D x) ≤ quadraticBlockCost n x := by
  obtain ⟨f, hf, he⟩ := quadraticBlockCost_norming n (head D x)
  rw [← he, ← head_inner]
  exact (le_abs_self _).trans ((quadraticBlockCost_abs_eval_scaled (head D f) x).trans
    (by
      have hb := (head_quadraticPolar_le hD f).trans hf
      have hx : 0 ≤ quadraticBlockCost n x := quadraticCost_nonneg (pathSynthesis n) x
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb hx))

/-- Coefficientwise clipping is done with the actual inward potentials, not an
abstract substitute for a test or a changed cost. -/
def inwardOne {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) : TreeHilbert n :=
  dominatedHilbert g (fun s => inwardCoeffsOne D (extendCoeff h) (extendCoeff g) s.val)
    (fun s => by simpa only [extendCoeff_apply] using
      inwardCoeffsOne_abs_le hD (extendCoeff_head_support hh) (extendCoeff g) s.val)

def inwardTwo {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) : TreeHilbert n :=
  dominatedHilbert g (fun s => inwardCoeffsTwo D (extendCoeff h) (extendCoeff g) s.val)
    (fun s => by simpa only [extendCoeff_apply] using
      inwardCoeffsTwo_abs_le hD (extendCoeff_head_support hh) (extendCoeff g) s.val)

lemma inward_difference {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) : inwardOne hD h g hh - inwardTwo hD h g hh = g-head D g := by
  ext s
  change inwardCoeffsOne D (extendCoeff h) (extendCoeff g) s.val -
    inwardCoeffsTwo D (extendCoeff h) (extendCoeff g) s.val = _
  rw [inwardCoeffs_difference, tail_eq_sub_head]
  by_cases hs : s.val ∈ D <;> simp [headPart, hs]

lemma inwardOne_head {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) : head D (inwardOne hD h g hh) = 0 := by
  ext s
  simp only [head_apply, lp.coeFn_zero, Pi.zero_apply]
  split_ifs with hs
  · exact inwardCoeffsOne_on_head hD _ _ hs
  · rfl

lemma inwardTwo_head {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) : head D (inwardTwo hD h g hh) = 0 := by
  ext s
  simp only [head_apply, lp.coeFn_zero, Pi.zero_apply]
  split_ifs with hs
  · exact inwardCoeffsTwo_on_head hD _ _ hs
  · rfl

lemma inwardOne_norm {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) : ‖inwardOne hD h g hh‖ ≤ ‖g‖ := dominatedHilbert_norm_le ..
lemma inwardTwo_norm {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) : ‖inwardTwo hD h g hh‖ ≤ ‖g‖ := dominatedHilbert_norm_le ..

lemma potential_congr_on_prefix (f g : Node → ℝ) (s : Node)
    (h : ∀ r, r <+: s → f r = g r) : potential f s = potential g s := by
  unfold potential
  congr 1
  apply List.map_congr_left
  intro r hr
  exact h r ((List.mem_inits r s).mp hr)

lemma inwardOne_potential {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) (s : Tree n) :
    pathPotential (inwardOne hD h g hh) s =
      TreeCalculus.inwardPotentialOne D (extendCoeff h) (extendCoeff g) s.val := by
  rw [← potential_extendCoeff]
  calc
    _ = potential (inwardCoeffsOne D (extendCoeff h) (extendCoeff g)) s.val := by
      apply potential_congr_on_prefix
      intro r hr
      simp only [extendCoeff, dite_eq_left (hr.length_le.trans s.property)]
      rfl
    _ = _ := potential_increments _ _

lemma inwardTwo_potential {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) (s : Tree n) :
    pathPotential (inwardTwo hD h g hh) s =
      TreeCalculus.inwardPotentialTwo D (extendCoeff h) (extendCoeff g) s.val := by
  rw [← potential_extendCoeff]
  calc
    _ = potential (inwardCoeffsTwo D (extendCoeff h) (extendCoeff g)) s.val := by
      apply potential_congr_on_prefix
      intro r hr
      simp only [extendCoeff, dite_eq_left (hr.length_le.trans s.property)]
      rfl
    _ = _ := potential_increments _ _


lemma head_orthogonal {n : ℕ} {D : Set Node} {h r : TreeHilbert n}
    (hh : head D h = h) (hr : head D r = 0) : inner ℝ h r = 0 := by
  calc
    inner ℝ h r = inner ℝ (head D h) r := by rw [hh]
    _ = inner ℝ h (head D r) := head_inner D h r
    _ = 0 := by rw [hr, inner_zero_right]

lemma disjoint_combination_norm_sq {n : ℕ} {D : Set Node} {h r : TreeHilbert n}
    (hh : head D h = h) (hr : head D r = 0) (a b : ℝ) :
    ‖a • h + b • r‖^2 = a^2*‖h‖^2 + b^2*‖r‖^2 := by
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, head_orthogonal hh hr]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The information delivered by inward clipping, with unnormalized block budgets. -/
structure InwardPiece {n : ℕ} (D : Set Node) (h g r : TreeHilbert n) : Prop where
  head_zero : head D r = 0
  hilbert_le : ‖r‖ ≤ ‖g‖
  prefix_le : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ∀ s : Tree n,
    |pathPotential (a • h+b • r) s| ≤ max (a*pathBound h) (2*b*pathBound g)

lemma inwardOne_piece {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) : InwardPiece D h g (inwardOne hD h g hh) := by
  refine ⟨inwardOne_head hD h g hh, inwardOne_norm hD h g hh, ?_⟩
  intro a b ha hb s
  rw [← inner_rootPath, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_rootPath, inner_rootPath, inwardOne_potential]
  unfold inwardPotentialOne
  have he := inwardOne_combination_bound (extendCoeff_potential_bound h s.val)
    (tail_potential_bound hD (pathBound_nonneg g) (extendCoeff_potential_bound g) s.val) ha hb
  simpa only [potential_extendCoeff, mul_assoc, mul_left_comm b 2] using he

lemma inwardTwo_piece {n : ℕ} {D : Set Node} (hD : Initial D) (h g : TreeHilbert n)
    (hh : head D h = h) : InwardPiece D h g (inwardTwo hD h g hh) := by
  refine ⟨inwardTwo_head hD h g hh, inwardTwo_norm hD h g hh, ?_⟩
  intro a b ha hb s
  rw [← inner_rootPath, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_rootPath, inner_rootPath, inwardTwo_potential]
  unfold inwardPotentialTwo
  have he := inwardTwo_combination_bound (extendCoeff_potential_bound h s.val)
    (tail_potential_bound hD (pathBound_nonneg g) (extendCoeff_potential_bound g) s.val) ha hb
  simpa only [potential_extendCoeff, mul_assoc, mul_left_comm b 2] using he

lemma InwardPiece.hilbert_sq {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) (hh : head D h = h) (a b : ℝ) :
    ‖a • h+b • r‖^2 ≤ a^2*‖h‖^2+b^2*‖g‖^2 := by
  rw [disjoint_combination_norm_sq hh hr.head_zero]
  gcongr
  exact hr.hilbert_le

lemma InwardPiece.pathBound_le {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pathBound (a • h+b • r) ≤ max (a*pathBound h) (2*b*pathBound g) :=
  ciSup_le (hr.prefix_le a b ha hb)

lemma InwardPiece.pathBound_sq {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (pathBound (a • h+b • r))^2 ≤ a^2*(pathBound h)^2+4*b^2*(pathBound g)^2 := by
  have hp := hr.pathBound_le ha hb
  have hpn := pathBound_nonneg (a • h+b • r)
  have hh := pathBound_nonneg h
  have hg := pathBound_nonneg g
  have hA : 0 ≤ a*pathBound h := mul_nonneg ha hh
  have hB : 0 ≤ 2*b*pathBound g := by positivity
  rcases le_total (a*pathBound h) (2*b*pathBound g) with hab | hab
  · rw [max_eq_right hab] at hp
    nlinarith [sq_nonneg (a*pathBound h)]
  · rw [max_eq_left hab] at hp
    nlinarith [sq_nonneg (2*b*pathBound g)]

lemma InwardPiece.linear_sq {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) (hh : head D h = h) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (linearPolar n (a • h+b • r))^2 ≤ a^2*(linearPolar n h)^2+4*b^2*(linearPolar n g)^2 := by
  have hhn := norm_le_linearPolar h
  have hgn := norm_le_linearPolar g
  have hhp : pathBound h ≤ linearPolar n h := le_max_right _ _
  have hgp : pathBound g ≤ linearPolar n g := le_max_right _ _
  have hhp0 := pathBound_nonneg h
  have hgp0 := pathBound_nonneg g
  have h1 := hr.hilbert_sq hh a b
  have h2 := hr.pathBound_sq ha hb
  have hs1 : a^2*‖h‖^2+b^2*‖g‖^2 ≤ a^2*(linearPolar n h)^2+4*b^2*(linearPolar n g)^2 := by
    have hA : a^2*‖h‖^2 ≤ a^2*(linearPolar n h)^2 := by gcongr
    have hB : b^2*‖g‖^2 ≤ b^2*(linearPolar n g)^2 := by gcongr
    nlinarith [sq_nonneg (b*linearPolar n g)]
  have hs2 : a^2*(pathBound h)^2+4*b^2*(pathBound g)^2 ≤
      a^2*(linearPolar n h)^2+4*b^2*(linearPolar n g)^2 := by
    gcongr
  change (max ‖a • h+b • r‖ (pathBound (a • h+b • r)))^2 ≤ _
  rcases le_total ‖a • h+b • r‖ (pathBound (a • h+b • r)) with he | he
  · rw [max_eq_right he]; exact h2.trans hs2
  · rw [max_eq_left he]; exact h1.trans hs1

lemma InwardPiece.quadratic_sq {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) (hh : head D h = h) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (quadraticPolar n (a • h+b • r))^2 ≤
      a^2*(quadraticPolar n h)^2+4*b^2*(quadraticPolar n g)^2 := by
  rw [quadraticPolar_sq, quadraticPolar_sq, quadraticPolar_sq]
  have h1 := hr.hilbert_sq hh a b
  have h2 := hr.pathBound_sq ha hb
  nlinarith [sq_nonneg (b*‖g‖)]

lemma InwardPiece.linear_unit {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) (hh : head D h = h)
    (hh1 : linearPolar n h ≤ 1) (hg1 : linearPolar n g ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1/2)
    (hab : a^2+b^2 ≤ 1) : linearPolar n (a • h+b • r) ≤ 1 := by
  apply max_le
  · have hh2 := (norm_le_linearPolar h).trans hh1
    have hg2 := (norm_le_linearPolar g).trans hg1
    have hh2sq : ‖h‖^2 ≤ 1 := by nlinarith [norm_nonneg h]
    have hg2sq : ‖g‖^2 ≤ 1 := by nlinarith [norm_nonneg g]
    have hA : a^2*‖h‖^2 ≤ a^2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh2sq (sq_nonneg a)
    have hB : b^2*‖g‖^2 ≤ b^2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hg2sq (sq_nonneg b)
    have hn := hr.hilbert_sq hh a b
    nlinarith [norm_nonneg (a • h+b • r)]
  · apply (hr.pathBound_le ha hb).trans
    apply max_le
    · exact (mul_le_mul_of_nonneg_left ((le_max_right ‖h‖ (pathBound h)).trans hh1) ha).trans (by simpa using ha1)
    · have hg2 : pathBound g ≤ 1 := (le_max_right _ _).trans hg1
      nlinarith [mul_le_mul_of_nonneg_left hg2 (show 0 ≤ 2*b by positivity)]


lemma InwardPiece.linear_budget {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) (hh : head D h = h)
    (hh1 : linearPolar n h ≤ 1) (hg1 : linearPolar n g ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2+4*b^2 ≤ 1) :
    linearPolar n (a • h+b • r) ≤ 1 := by
  have h1 : (linearPolar n h)^2 ≤ 1 := by nlinarith [linearPolar_nonneg h]
  have h2 : (linearPolar n g)^2 ≤ 1 := by nlinarith [linearPolar_nonneg g]
  have h3 := hr.linear_sq hh ha hb
  have h4 : a^2*(linearPolar n h)^2 ≤ a^2 := by nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg a)]
  have h5 : 4*b^2*(linearPolar n g)^2 ≤ 4*b^2 := by nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4*b^2 by positivity)]
  nlinarith [linearPolar_nonneg (a • h+b • r)]

lemma InwardPiece.quadratic_budget {n : ℕ} {D : Set Node} {h g r : TreeHilbert n}
    (hr : InwardPiece D h g r) (hh : head D h = h)
    (hh1 : quadraticPolar n h ≤ 1) (hg1 : quadraticPolar n g ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2+4*b^2 ≤ 1) :
    quadraticPolar n (a • h+b • r) ≤ 1 := by
  have h1 : (quadraticPolar n h)^2 ≤ 1 := by nlinarith [quadraticPolar_nonneg h]
  have h2 : (quadraticPolar n g)^2 ≤ 1 := by nlinarith [quadraticPolar_nonneg g]
  have h3 := hr.quadratic_sq hh ha hb
  have h4 : a^2*(quadraticPolar n h)^2 ≤ a^2 := by nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg a)]
  have h5 : 4*b^2*(quadraticPolar n g)^2 ≤ 4*b^2 := by nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4*b^2 by positivity)]
  nlinarith [quadraticPolar_nonneg (a • h+b • r)]

lemma quadratic_eval_le {n : ℕ} {f : TreeHilbert n} (hf : quadraticPolar n f ≤ 1)
    (x : TreeHilbert n) : inner ℝ f x ≤ quadraticBlockCost n x := by
  apply (le_abs_self _).trans ((quadraticBlockCost_abs_eval_scaled f x).trans _)
  have hn : 0 ≤ quadraticBlockCost n x := quadraticCost_nonneg _ _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hf hn

lemma inward_pair_identity {n : ℕ} {D : Set Node} (hD : Initial D) (h g x y : TreeHilbert n)
    (hh : head D h = h) (hx : head D x = x) (a b : ℝ) :
    inner ℝ (a • h+b • inwardOne hD h g hh) (x+y) +
      inner ℝ (a • h+b • inwardTwo hD h g hh) (x-y) =
        2*a*inner ℝ h x + b*inner ℝ g (y-head D y) := by
  have hr1x : inner ℝ (inwardOne hD h g hh) x = 0 := by
    calc
      _ = inner ℝ (inwardOne hD h g hh) (head D x) := by rw [hx]
      _ = inner ℝ (head D (inwardOne hD h g hh)) x := (head_inner D _ _).symm
      _ = 0 := by rw [inwardOne_head, inner_zero_left]
  have hr2x : inner ℝ (inwardTwo hD h g hh) x = 0 := by
    calc
      _ = inner ℝ (inwardTwo hD h g hh) (head D x) := by rw [hx]
      _ = inner ℝ (head D (inwardTwo hD h g hh)) x := (head_inner D _ _).symm
      _ = 0 := by rw [inwardTwo_head, inner_zero_left]
  have hd : inner ℝ (inwardOne hD h g hh) y-inner ℝ (inwardTwo hD h g hh) y =
      inner ℝ g (y-head D y) := by
    rw [← inner_sub_left, inward_difference, inner_sub_left, head_inner, inner_sub_right]
  simp only [inner_add_left, inner_add_right, inner_sub_right, real_inner_smul_left, hr1x, hr2x]
  rw [inner_sub_right] at hd
  rw [← hd]
  ring

theorem linear_paired {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2+4*b^2 ≤ 1) :
    a*linearBlockCost n x+(b/2)*linearBlockCost n (y-head D y) ≤
      (linearBlockCost n (x+y)+linearBlockCost n (x-y))/2 := by
  obtain ⟨f, hf, hfx⟩ := linearBlockCost_norming n x
  obtain ⟨g, hg, hgy⟩ := linearBlockCost_norming n (y-head D y)
  let h := head D f
  have hh : head D h = h := head_idem D f
  have hh1 : linearPolar n h ≤ 1 := (head_linearPolar_le hD f).trans hf
  have hhx : inner ℝ h x = linearBlockCost n x := by
    dsimp [h]
    rw [head_inner, hx, hfx]
  have hp := linearBlockCost_eval_le ((inwardOne_piece hD h g hh).linear_budget hh hh1 hg ha hb hab) (x+y)
  have hm := linearBlockCost_eval_le ((inwardTwo_piece hD h g hh).linear_budget hh hh1 hg ha hb hab) (x-y)
  have he := inward_pair_identity hD h g x y hh hx a b
  rw [hhx, hgy] at he
  linarith

theorem quadratic_paired {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2+4*b^2 ≤ 1) :
    a*quadraticBlockCost n x+(b/2)*quadraticBlockCost n (y-head D y) ≤
      (quadraticBlockCost n (x+y)+quadraticBlockCost n (x-y))/2 := by
  obtain ⟨f, hf, hfx⟩ := quadraticBlockCost_norming n x
  obtain ⟨g, hg, hgy⟩ := quadraticBlockCost_norming n (y-head D y)
  let h := head D f
  have hh : head D h = h := head_idem D f
  have hh1 : quadraticPolar n h ≤ 1 := (head_quadraticPolar_le hD f).trans hf
  have hhx : inner ℝ h x = quadraticBlockCost n x := by
    dsimp [h]
    rw [head_inner, hx, hfx]
  have hp := quadratic_eval_le ((inwardOne_piece hD h g hh).quadratic_budget hh hh1 hg ha hb hab) (x+y)
  have hm := quadratic_eval_le ((inwardTwo_piece hD h g hh).quadratic_budget hh hh1 hg ha hb hab) (x-y)
  have he := inward_pair_identity hD h g x y hh hx a b
  rw [hhx, hgy] at he
  linarith

/-- The stronger unit-budget version used for the bottom-up linear estimate. -/
theorem linear_paired_unit {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (hb1 : b ≤ 1/2) (hab : a^2+b^2 ≤ 1) :
    a*linearBlockCost n x+(b/2)*linearBlockCost n (y-head D y) ≤
      (linearBlockCost n (x+y)+linearBlockCost n (x-y))/2 := by
  obtain ⟨f, hf, hfx⟩ := linearBlockCost_norming n x
  obtain ⟨g, hg, hgy⟩ := linearBlockCost_norming n (y-head D y)
  let h := head D f
  have hh : head D h = h := head_idem D f
  have hh1 : linearPolar n h ≤ 1 := (head_linearPolar_le hD f).trans hf
  have hhx : inner ℝ h x = linearBlockCost n x := by
    dsimp [h]
    rw [head_inner, hx, hfx]
  have hp := linearBlockCost_eval_le ((inwardOne_piece hD h g hh).linear_unit hh hh1 hg ha ha1 hb hb1 hab) (x+y)
  have hm := linearBlockCost_eval_le ((inwardTwo_piece hD h g hh).linear_unit hh hh1 hg ha ha1 hb hb1 hab) (x-y)
  have he := inward_pair_identity hD h g x y hh hx a b
  rw [hhx, hgy] at he
  linarith

lemma disk_sup_bound {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a^2+b^2 ≤ 1 → a*A+b*B ≤ C) :
    Real.sqrt (A^2+B^2) ≤ C := by
  let S := Real.sqrt (A^2+B^2)
  have hS : S^2 = A^2+B^2 := Real.sq_sqrt (by positivity)
  change S ≤ C
  by_cases hz : S = 0
  · rw [hz]; exact hC
  have hSp : 0 < S := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
  have hbudget : (A/S)^2+(B/S)^2 ≤ 1 := by
    rw [div_pow, div_pow, ← add_div, ← hS, div_self (pow_ne_zero 2 hz)]
  have he := h (A/S) (B/S) (div_nonneg hA hSp.le) (div_nonneg hB hSp.le) hbudget
  have hid : A/S*A+B/S*B = S := by
    field_simp
    nlinarith [hS]
  rwa [hid] at he

lemma ellipse_sup_bound {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a^2+4*b^2 ≤ 1 → a*A+(b/2)*B ≤ C) :
    Real.sqrt (A^2+B^2/16) ≤ C := by
  have he := disk_sup_bound hA (show 0 ≤ B/4 by positivity) hC (by
    intro a b ha hb hab
    have hh := h a (b/2) ha (by positivity) (by nlinarith)
    nlinarith)
  convert he using 1 ; congr 1 ; ring

theorem linear_midpoint_tail {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) :
    Real.sqrt ((linearBlockCost n x)^2+(linearBlockCost n (y-head D y))^2/16) ≤
      (linearBlockCost n (x+y)+linearBlockCost n (x-y))/2 := by
  apply ellipse_sup_bound (linearCost_nonneg _ _) (linearCost_nonneg _ _) (by
    have h1 := linearCost_nonneg (pathSynthesis n) (x+y)
    have h2 := linearCost_nonneg (pathSynthesis n) (x-y)
    change 0 ≤ (linearCost (pathSynthesis n) (x+y)+linearCost (pathSynthesis n) (x-y))/2
    positivity)
  intro a b ha hb hab
  exact linear_paired hD x y hx ha hb hab

theorem quadratic_midpoint_tail {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) :
    Real.sqrt ((quadraticBlockCost n x)^2+(quadraticBlockCost n (y-head D y))^2/16) ≤
      (quadraticBlockCost n (x+y)+quadraticBlockCost n (x-y))/2 := by
  apply ellipse_sup_bound (quadraticCost_nonneg _ _) (quadraticCost_nonneg _ _) (by
    have h1 := quadraticCost_nonneg (pathSynthesis n) (x+y)
    have h2 := quadraticCost_nonneg (pathSynthesis n) (x-y)
    change 0 ≤ (quadraticCost (pathSynthesis n) (x+y)+quadraticCost (pathSynthesis n) (x-y))/2
    positivity)
  intro a b ha hb hab
  exact quadratic_paired hD x y hx ha hb hab

end BlockCalculus


end BoundedTreePotentials

end

end OAI
