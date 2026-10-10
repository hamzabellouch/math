import OAI.Analysis.FreeGroupFactor.Cocycles

namespace OAI

noncomputable section

universe uE uG uI uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

def coefficientSqNorm {G : Type uG} (h : G →₀ ℝ) : ℝ := h.sum (fun _ r => r ^ 2)

theorem coefficientSqNorm_nonneg {G : Type uG} (h : G →₀ ℝ) : 0 ≤ coefficientSqNorm h := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

@[simp] theorem coefficientSqNorm_zero {G : Type uG} : coefficientSqNorm (0 : G →₀ ℝ) = 0 := by
  simp [coefficientSqNorm]

@[simp] theorem coefficientSqNorm_single {G : Type uG} (g : G) (c : ℝ) :
    coefficientSqNorm (Finsupp.single g c) = c ^ 2 := by
  simp [coefficientSqNorm]

@[simp] theorem coefficientSqNorm_smul {G : Type uG} (c : ℝ) (h : G →₀ ℝ) :
    coefficientSqNorm (c • h) = c ^ 2 * coefficientSqNorm h := by
  classical
  rw [coefficientSqNorm, Finsupp.sum_of_support_subset _ Finsupp.support_smul
    (fun (_ : G) (r : ℝ) => r ^ 2) (by simp)]
  simp [Finsupp.smul_apply, mul_pow, coefficientSqNorm, Finsupp.sum, Finset.mul_sum]

theorem coefficientSqNorm_add_of_disjoint {G : Type uG} (f g : G →₀ ℝ)
    (hfg : Disjoint f.support g.support) :
    coefficientSqNorm (f + g) = coefficientSqNorm f + coefficientSqNorm g := by
  classical
  rw [coefficientSqNorm, Finsupp.sum_of_support_subset _ Finsupp.support_add
      (fun (_ : G) (r : ℝ) => r ^ 2) (by simp),
    coefficientSqNorm, Finsupp.sum_of_support_subset f Finset.subset_union_left
      (fun (_ : G) (r : ℝ) => r ^ 2) (by simp),
    coefficientSqNorm, Finsupp.sum_of_support_subset g Finset.subset_union_right
      (fun (_ : G) (r : ℝ) => r ^ 2) (by simp), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hf : f a = 0
  · simp [hf]
  · have hg : g a = 0 := by
      by_contra hg
      exact Finset.disjoint_left.mp hfg (Finsupp.mem_support_iff.mpr hf)
        (Finsupp.mem_support_iff.mpr hg)
    simp [hg]

theorem coefficientSqNorm_sum_of_disjoint {I : Type uI} {G : Type uG} (s : Finset I) (f : I → G →₀ ℝ)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i).support (f j).support) :
    coefficientSqNorm (∑ i ∈ s, f i) = ∑ i ∈ s, coefficientSqNorm (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hf
    rw [Finset.sum_insert ha, Finset.sum_insert ha, coefficientSqNorm_add_of_disjoint]
    · exact congrArg (coefficientSqNorm (f a) + ·) (ih (fun i hi j hj hij =>
        hf i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij))
    · apply Finset.disjoint_left.mpr
      intro g hg hs
      obtain ⟨i, hi, hgi⟩ := Finsupp.mem_support_finsetSum g hs
      have hai : a ≠ i := by intro h; exact ha (h.symm ▸ hi)
      exact Finset.disjoint_left.mp (hf a (Finset.mem_insert_self ..) i
        (Finset.mem_insert_of_mem hi) hai) hg hgi

theorem coefficientSqNorm_sum_le {I : Type uI} {G : Type uG} (s : Finset I) (f : I → G →₀ ℝ) :
    coefficientSqNorm (∑ i ∈ s, f i) ≤ (s.card : ℝ) * ∑ i ∈ s, coefficientSqNorm (f i) := by
  classical
  let t := s.biUnion (fun i => (f i).support)
  have hsupp (i : I) (hi : i ∈ s) : (f i).support ⊆ t :=
    Finset.subset_biUnion_of_mem (fun i => (f i).support) hi
  have hsum : (∑ i ∈ s, f i).support ⊆ t := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := Finsupp.mem_support_finsetSum g hg
    exact hsupp i hi hgi
  rw [coefficientSqNorm, Finsupp.sum_of_support_subset _ hsum _ (by simp)]
  have hq (g : G) : ((∑ i ∈ s, f i) g) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, (f i g) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => f i g)
  calc
    _ ≤ ∑ g ∈ t, (s.card : ℝ) * ∑ i ∈ s, (f i g) ^ 2 := Finset.sum_le_sum (fun g _ => hq g)
    _ = (s.card : ℝ) * ∑ i ∈ s, ∑ g ∈ t, (f i g) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finsupp.sum_of_support_subset (f i) (hsupp i hi)
        (fun (_ : G) (r : ℝ) => r ^ 2) (by simp)).symm

theorem coefficientSqNorm_add_le {G : Type uG} (f g : G →₀ ℝ) :
    coefficientSqNorm (f + g) ≤ 2 * (coefficientSqNorm f + coefficientSqNorm g) := by
  simpa using coefficientSqNorm_sum_le (Finset.univ : Finset Bool) (fun b => if b then f else g)

namespace Radial

section
variable {ι : Type uι} [DecidableEq ι] [Fintype ι]

def paths (i : ι) : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => (Finset.univ.erase i).biUnion (fun j => (paths j k).image (List.cons j))

def sphere : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => Finset.univ.biUnion (fun j : ι => (paths j k).image (List.cons j))

theorem paths_mem_length (i : ι) (k : ℕ) {w : List ι} (hw : w ∈ paths i k) :
    w.length = k := by
  induction k generalizing i w with
  | zero => simpa [paths] using hw
  | succ k ih =>
    simp only [paths, Finset.mem_biUnion, Finset.mem_image] at hw
    obtain ⟨j, _, v, hv, rfl⟩ := hw
    simp [ih j hv]

theorem sphere_mem_length (k : ℕ) {w : List ι} (hw : w ∈ sphere (ι := ι) k) :
    w.length = k := by
  cases k with
  | zero => simpa [sphere] using hw
  | succ k =>
    simp only [sphere, Finset.mem_biUnion, Finset.mem_image] at hw
    obtain ⟨j, _, v, hv, rfl⟩ := hw
    simp [paths_mem_length j k hv]

omit [Fintype ι] in
theorem cons_images_disjoint {i j : ι} (hij : i ≠ j) (s t : Finset (List ι)) :
    Disjoint (s.image (List.cons i)) (t.image (List.cons j)) := by
  apply Finset.disjoint_left.mpr
  intro w hw ht
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp ht
  exact hij (List.cons.inj hu).1.symm

theorem card_paths (i : ι) (k : ℕ) :
    (paths i k).card = (Fintype.card ι - 1) ^ k := by
  induction k generalizing i with
  | zero => simp [paths]
  | succ k ih =>
    rw [paths, Finset.card_biUnion]
    · simp only [Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2), ih]
      simp [pow_succ, Nat.mul_comm]
    · intro a _ b _ hab
      exact cons_images_disjoint hab _ _

theorem card_sphere_succ (k : ℕ) :
    (sphere (ι := ι) (k + 1)).card = Fintype.card ι * (Fintype.card ι - 1) ^ k := by
  rw [sphere, Finset.card_biUnion]
  · simp only [Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2), card_paths]
    simp
  · intro a _ b _ hab
    exact cons_images_disjoint hab _ _

def signed (b : Bool) : List ι → List (ι × Bool)
  | [] => []
  | i :: w => (i, b) :: signed (!b) w

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem signed_length (b : Bool) (w : List ι) : (signed b w).length = w.length := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih => simp [signed, ih]

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem signed_map_fst (b : Bool) (w : List ι) :
    (signed b w).map Prod.fst = w := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih => simp [signed, ih]

omit [DecidableEq ι] [Fintype ι] in
theorem signed_injective (b : Bool) : Function.Injective (signed (ι := ι) b) := by
  intro u v huv
  simpa using congrArg (List.map Prod.fst) huv

theorem signed_reduced_paths (b : Bool) (i : ι) (k : ℕ) {w : List ι}
    (hw : w ∈ paths i k) : FreeGroup.IsReduced ((i, b) :: signed (!b) w) := by
  induction k generalizing b i w with
  | zero =>
    have : w = [] := by simpa [paths] using hw
    subst w
    exact FreeGroup.IsReduced.singleton
  | succ k ih =>
    simp only [paths, Finset.mem_biUnion, Finset.mem_image, Finset.mem_erase,
      Finset.mem_univ, and_true] at hw
    obtain ⟨j, hji, v, hv, rfl⟩ := hw
    rw [signed, FreeGroup.isReduced_cons_cons]
    exact ⟨fun hij => False.elim (hji hij.symm), ih (!b) j hv⟩

theorem signed_reduced_sphere (b : Bool) (k : ℕ) {w : List ι}
    (hw : w ∈ sphere (ι := ι) k) : FreeGroup.IsReduced (signed b w) := by
  cases k with
  | zero =>
    have : w = [] := by simpa [sphere] using hw
    subst w
    exact FreeGroup.IsReduced.nil
  | succ k =>
    simp only [sphere, Finset.mem_biUnion, Finset.mem_image] at hw
    obtain ⟨j, _, v, hv, rfl⟩ := hw
    exact signed_reduced_paths b j k hv

def vertex (b : Bool) (w : List ι) : FreeGroup ι := FreeGroup.mk (signed b w)

theorem toWord_vertex (b : Bool) (k : ℕ) {w : List ι}
    (hw : w ∈ sphere (ι := ι) k) : (vertex b w).toWord = signed b w := by
  rw [vertex, FreeGroup.toWord_mk, (signed_reduced_sphere b k hw).reduce_eq]

theorem vertex_injOn (b : Bool) (k : ℕ) :
    Set.InjOn (vertex (ι := ι) b) (↑(sphere (ι := ι) k) : Set (List ι)) := by
  intro u hu v hv huv
  have hh := congrArg FreeGroup.toWord huv
  rw [toWord_vertex b k hu, toWord_vertex b k hv] at hh
  exact signed_injective b hh

theorem sum_sphere_succ {E : Type uE} [AddCommMonoid E] (f : List ι → E) (k : ℕ) :
    ∑ w ∈ sphere (ι := ι) (k + 1), f w =
      ∑ j : ι, ∑ w ∈ paths j k, f (j :: w) := by
  rw [sphere, Finset.sum_biUnion (fun i _ j _ hij => cons_images_disjoint hij _ _)]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)

theorem sum_paths_succ {E : Type uE} [AddCommMonoid E] (f : List ι → E) (i : ι) (k : ℕ) :
    ∑ w ∈ paths i (k + 1), f w =
      ∑ j ∈ Finset.univ.erase i, ∑ w ∈ paths j k, f (j :: w) := by
  rw [paths, Finset.sum_biUnion (fun a _ b _ hab => cons_images_disjoint hab _ _)]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem vertex_nil (b : Bool) : vertex (ι := ι) b [] = 1 := rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem vertex_cons_true (i : ι) (w : List ι) :
    vertex true (i :: w) = FreeGroup.of i * vertex false w := by
  rfl

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem vertex_cons_false (i : ι) (w : List ι) :
    vertex false (i :: w) = (FreeGroup.of i)⁻¹ * vertex true w := by
  rfl

def shell (b : Bool) (k : ℕ) : FreeGroup ι →₀ ℝ :=
  ∑ w ∈ sphere k, Finsupp.single (vertex b w) 1

def shift (g : FreeGroup ι) : (FreeGroup ι →₀ ℝ) →ₗ[ℝ] (FreeGroup ι →₀ ℝ) :=
  (Finsupp.domLCongr (Equiv.mulLeft g)).toLinearMap

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem shift_single (g a : FreeGroup ι) (r : ℝ) :
    shift g (Finsupp.single a r) = Finsupp.single (g * a) r := by
  exact Finsupp.equivMapDomain_single (Equiv.mulLeft g) a r

def sumShift : (FreeGroup ι →₀ ℝ) →ₗ[ℝ] (FreeGroup ι →₀ ℝ) :=
  ∑ i : ι, shift (FreeGroup.of i)

omit [DecidableEq ι] in
@[simp] theorem sumShift_apply (h : FreeGroup ι →₀ ℝ) :
    sumShift h = ∑ i : ι, shift (FreeGroup.of i) h := by
  simp [sumShift]

@[simp] theorem shell_zero (b : Bool) : shell (ι := ι) b 0 = Finsupp.single 1 1 := by
  simp [shell, sphere]

theorem shell_succ (b : Bool) (k : ℕ) :
    shell (ι := ι) b (k + 1) =
      ∑ j : ι, ∑ w ∈ paths j k, Finsupp.single (vertex b (j :: w)) 1 := by
  exact sum_sphere_succ _ _

theorem outward_shell (k : ℕ) :
    (∑ j : ι, ∑ w ∈ paths j k, ∑ i ∈ Finset.univ.erase j,
      Finsupp.single (FreeGroup.of i * vertex false (j :: w)) (1 : ℝ)) =
        shell (ι := ι) true (k + 2) := by
  rw [shell_succ]
  simp only [sum_paths_succ]
  simp_rw [vertex_cons_true]
  simp_rw [Finset.sum_comm (s := paths _ _) (t := Finset.univ.erase _)]
  apply Finset.sum_comm'
  intro x y
  simp [ne_comm, and_comm]

theorem sumShift_shell (k : ℕ) :
    sumShift (shell (ι := ι) false (k + 1)) =
      (∑ j : ι, ∑ w ∈ paths j k, Finsupp.single (vertex true w) (1 : ℝ)) +
        shell (ι := ι) true (k + 2) := by
  rw [shell_succ, map_sum]
  simp only [map_sum, sumShift_apply, shift_single]
  have hs (j : ι) (w : List ι) :
      (∑ i : ι, Finsupp.single (FreeGroup.of i * vertex false (j :: w)) (1 : ℝ)) =
        Finsupp.single (vertex true w) 1 +
          ∑ i ∈ Finset.univ.erase j,
            Finsupp.single (FreeGroup.of i * vertex false (j :: w)) 1 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp [add_comm, vertex_cons_false]
  simp_rw [hs, Finset.sum_add_distrib]
  rw [outward_shell]

theorem sumShift_shell_one :
    sumShift (shell (ι := ι) false 1) =
      (Fintype.card ι : ℝ) • Finsupp.single 1 1 + shell (ι := ι) true 2 := by
  rw [show 1 = 0 + 1 from rfl, sumShift_shell]
  simp [paths, Nat.cast_smul_eq_nsmul]

theorem inward_shell [Nonempty ι] (k : ℕ) :
    (∑ j : ι, ∑ w ∈ paths j (k + 1), Finsupp.single (vertex true w) (1 : ℝ)) =
      ((Fintype.card ι - 1 : ℕ) : ℝ) • shell (ι := ι) true (k + 1) := by
  simp_rw [sum_paths_succ, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← shell_succ, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_sub Fintype.card_pos,
      Nat.cast_one, sub_smul, one_smul]

theorem sumShift_shell_succ [Nonempty ι] (k : ℕ) :
    sumShift (shell (ι := ι) false (k + 2)) =
      ((Fintype.card ι - 1 : ℕ) : ℝ) • shell (ι := ι) true (k + 1) +
        shell (ι := ι) true (k + 3) := by
  rw [show k + 2 = (k + 1) + 1 from rfl, sumShift_shell, inward_shell]

def vertices (b : Bool) (k : ℕ) : Finset (FreeGroup ι) :=
  (sphere k).image (vertex b)

theorem shell_eq_sum_vertices (b : Bool) (k : ℕ) :
    shell (ι := ι) b k = ∑ g ∈ vertices b k, Finsupp.single g 1 := by
  rw [vertices, Finset.sum_image (vertex_injOn b k)]
  rfl

@[simp] theorem shell_apply (b : Bool) (k : ℕ) (g : FreeGroup ι) :
    shell (ι := ι) b k g = if g ∈ vertices b k then 1 else 0 := by
  rw [shell_eq_sum_vertices]
  simp [Finsupp.single_apply]

@[simp] theorem shell_support (b : Bool) (k : ℕ) :
    (shell (ι := ι) b k).support = vertices b k := by
  ext g
  simp only [Finsupp.mem_support_iff, shell_apply]
  split_ifs <;> simp_all

theorem card_vertices (b : Bool) (k : ℕ) :
    (vertices (ι := ι) b k).card = (sphere (ι := ι) k).card :=
  Finset.card_image_iff.mpr (vertex_injOn b k)

theorem vertices_disjoint (b c : Bool) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (vertices (ι := ι) b k) (vertices (ι := ι) c l) := by
  apply Finset.disjoint_left.mpr
  intro g hg hk
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hk
  have heq := congrArg (fun x : FreeGroup ι => x.toWord.length) hveq
  rw [toWord_vertex c l hv, toWord_vertex b k hu, signed_length,
    signed_length, sphere_mem_length l hv, sphere_mem_length k hu] at heq
  exact hkl heq.symm

end

def rightShell (m k : ℕ) : FreeGroup (Fin m) →₀ ℝ :=
  (1 / ((m : ℝ) * ((m : ℝ) - 1) ^ k)) • shell false (2 * k + 1)

def leftShell (m k : ℕ) : FreeGroup (Fin m) →₀ ℝ :=
  (1 / ((m : ℝ) * ((m : ℝ) - 1) ^ k)) • shell true (2 * k + 2)

theorem sqNorm_shell_succ (m k : ℕ) (hm : 1 ≤ m) (b : Bool) :
    coefficientSqNorm (shell (ι := Fin m) b (k + 1)) =
      (m : ℝ) * ((m : ℝ) - 1) ^ k := by
  classical
  rw [coefficientSqNorm, Finsupp.sum, shell_support]
  have hs : (∑ g ∈ vertices (ι := Fin m) b (k + 1), (shell b (k + 1) g) ^ 2) =
      ((vertices (ι := Fin m) b (k + 1)).card : ℝ) := by
    simp only [shell_apply]
    simp
  rw [hs, card_vertices, card_sphere_succ]
  simp [Nat.cast_sub hm]

theorem sumShift_rightShell_zero (m : ℕ) (hm : 2 ≤ m) :
    sumShift (rightShell m 0) = Finsupp.single 1 1 + leftShell m 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [rightShell, map_smul]
  simp only [mul_zero, zero_add]
  rw [sumShift_shell_one, smul_add, smul_smul]
  simp [leftShell, hm0]

theorem sumShift_rightShell_succ (m k : ℕ) (hm : 2 ≤ m) :
    sumShift (rightShell m (k + 1)) = leftShell m k + leftShell m (k + 1) := by
  let : NeZero m := ⟨by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hq0 : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [rightShell, map_smul, show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
    sumShift_shell_succ, smul_add, smul_smul]
  simp only [Fintype.card_fin, Nat.cast_sub hm1, Nat.cast_one, leftShell]
  have heq : 1 / ((m : ℝ) * ((m : ℝ) - 1) ^ (k + 1)) * ((m : ℝ) - 1) =
      1 / ((m : ℝ) * ((m : ℝ) - 1) ^ k) := by
    rw [pow_succ]
    field_simp
  rw [heq]
  congr 2

theorem sqNorm_rightShell (m k : ℕ) (hm : 2 ≤ m) :
    coefficientSqNorm (rightShell m k) = 1 / (m : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hq0 : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [rightShell, coefficientSqNorm_smul, sqNorm_shell_succ m (2 * k) hm1]
  rw [show 2 * k = k * 2 by omega, pow_mul]
  field_simp

theorem sqNorm_leftShell (m k : ℕ) (hm : 2 ≤ m) :
    coefficientSqNorm (leftShell m k) = ((m : ℝ) - 1) / (m : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hq0 : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [leftShell, coefficientSqNorm_smul,
    show 2 * k + 2 = (2 * k + 1) + 1 by omega, sqNorm_shell_succ m (2 * k + 1) hm1,
    pow_succ ((m : ℝ) - 1) (2 * k), show 2 * k = k * 2 by omega, pow_mul]
  field_simp

def partialInverse (m N : ℕ) : FreeGroup (Fin m) →₀ ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k • rightShell m k

@[simp] theorem partialInverse_zero (m : ℕ) : partialInverse m 0 = 0 := by
  simp [partialInverse]

theorem partialInverse_succ (m N : ℕ) :
    partialInverse m (N + 1) = partialInverse m N + (-1 : ℝ) ^ N • rightShell m N := by
  exact Finset.sum_range_succ _ _

theorem sumShift_partialInverse (m N : ℕ) (hm : 2 ≤ m) :
    sumShift (partialInverse m (N + 1)) =
      Finsupp.single 1 1 + (-1 : ℝ) ^ N • leftShell m N := by
  induction N with
  | zero => simp only [partialInverse_succ, partialInverse_zero, pow_zero, one_smul,
      zero_add, sumShift_rightShell_zero m hm]
  | succ N ih =>
    rw [partialInverse_succ, map_add, ih, map_smul, sumShift_rightShell_succ m N hm]
    simp only [pow_succ, mul_neg_one, neg_smul, smul_add]
    abel

theorem rightShell_disjoint (m : ℕ) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (rightShell m j).support (rightShell m k).support := by
  exact Finset.disjoint_of_subset_left Finsupp.support_smul
    (Finset.disjoint_of_subset_right Finsupp.support_smul
      (by rw [shell_support, shell_support]; exact vertices_disjoint _ _ (by omega)))

theorem leftShell_disjoint (m : ℕ) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (leftShell m j).support (leftShell m k).support := by
  exact Finset.disjoint_of_subset_left Finsupp.support_smul
    (Finset.disjoint_of_subset_right Finsupp.support_smul
      (by rw [shell_support, shell_support]; exact vertices_disjoint _ _ (by omega)))

theorem sqNorm_partialInverse (m N : ℕ) (hm : 2 ≤ m) :
    coefficientSqNorm (partialInverse m N) = (N : ℝ) / m := by
  rw [partialInverse, coefficientSqNorm_sum_of_disjoint]
  · have hsign (k : ℕ) : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    simp [coefficientSqNorm_smul, sqNorm_rightShell m _ hm, hsign, div_eq_mul_inv]
  · intro i _ j _ hij
    exact Finset.disjoint_of_subset_left Finsupp.support_smul
      (Finset.disjoint_of_subset_right Finsupp.support_smul (rightShell_disjoint m hij))

def averagedInverse (m N : ℕ) : FreeGroup (Fin m) →₀ ℝ :=
  (1 / (N + 1 : ℝ)) • ∑ k ∈ Finset.range (N + 1), partialInverse m (k + 1)

theorem sumShift_averagedInverse (m N : ℕ) (hm : 2 ≤ m) :
    sumShift (averagedInverse m N) - Finsupp.single 1 1 =
      (1 / (N + 1 : ℝ)) •
        ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k • leftShell m k := by
  rw [averagedInverse, map_smul, map_sum]
  simp_rw [sumShift_partialInverse m _ hm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hN : (N + 1 : ℝ) ≠ 0 := by positivity
  simp [hN]

theorem sqNorm_averagedInverse_le (m N : ℕ) (hm : 2 ≤ m) :
    coefficientSqNorm (averagedInverse m N) ≤ (N + 1 : ℝ) / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  have hb : coefficientSqNorm (∑ k ∈ Finset.range (N + 1), partialInverse m (k + 1)) ≤
      (N + 1 : ℝ) ^ 2 * ((N + 1 : ℝ) / m) := by
    calc
      _ ≤ ((Finset.range (N + 1)).card : ℝ) *
          ∑ k ∈ Finset.range (N + 1), coefficientSqNorm (partialInverse m (k + 1)) :=
        coefficientSqNorm_sum_le _ _
      _ ≤ ((Finset.range (N + 1)).card : ℝ) *
          ∑ _k ∈ Finset.range (N + 1), (N + 1 : ℝ) / m := by
        gcongr with k hk
        rw [sqNorm_partialInverse m (k + 1) hm]
        apply div_le_div_of_nonneg_right _ hmpos.le
        exact_mod_cast (by have := Finset.mem_range.mp hk; omega : k + 1 ≤ N + 1)
      _ = _ := by simp [pow_two, mul_assoc]
  rw [averagedInverse, coefficientSqNorm_smul]
  calc
    _ ≤ (1 / (N + 1 : ℝ)) ^ 2 * ((N + 1 : ℝ) ^ 2 * ((N + 1 : ℝ) / m)) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by field_simp

theorem sqNorm_averagedInverse_residual (m N : ℕ) (hm : 2 ≤ m) :
    coefficientSqNorm (sumShift (averagedInverse m N) - Finsupp.single 1 1) =
      ((m : ℝ) - 1) / ((m : ℝ) * (N + 1 : ℝ)) := by
  rw [sumShift_averagedInverse m N hm, coefficientSqNorm_smul,
    coefficientSqNorm_sum_of_disjoint]
  · have hsign (k : ℕ) : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    simp only [coefficientSqNorm_smul, hsign, sqNorm_leftShell m _ hm, one_mul,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  · intro i _ j _ hij
    exact Finset.disjoint_of_subset_left Finsupp.support_smul
      (Finset.disjoint_of_subset_right Finsupp.support_smul (leftShell_disjoint m hij))

theorem sqNorm_averagedInverse_residual_le (m N : ℕ) (hm : 2 ≤ m) :
    coefficientSqNorm (sumShift (averagedInverse m N) - Finsupp.single 1 1) ≤
      1 / (N + 1 : ℝ) := by
  rw [sqNorm_averagedInverse_residual m N hm]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  apply (div_le_iff₀ (mul_pos hmpos hNpos)).mpr
  field_simp
  linarith

def prefixSumOperator (m : ℕ) (h : FreeGroup (Fin m) →₀ ℝ) : FreeGroup (Fin m) →₀ ℝ :=
  h + sumShift h

theorem sqNorm_prefixSum_residual_le (m N : ℕ) (hm : 2 ≤ m) :
    coefficientSqNorm (prefixSumOperator m (averagedInverse m N) - Finsupp.single 1 1) ≤
      2 * ((N + 1 : ℝ) / m + 1 / (N + 1 : ℝ)) := by
  rw [prefixSumOperator, add_sub_assoc]
  exact (coefficientSqNorm_add_le _ _).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (sqNorm_averagedInverse_le m N hm)
        (sqNorm_averagedInverse_residual_le m N hm)) (by norm_num))

theorem exists_small_prefix_inverse (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ h : FreeGroup (Fin m) →₀ ℝ,
      coefficientSqNorm h < ε ∧
        coefficientSqNorm (prefixSumOperator m h - Finsupp.single 1 1) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (by positivity : 0 < ε / 4)
  obtain ⟨m, hm⟩ := exists_nat_gt (max (2 : ℝ) (4 * (N + 1 : ℝ) / ε))
  have hm2 : 2 ≤ m := by
    have := (le_max_left (2 : ℝ) _).trans_lt hm
    exact_mod_cast this.le
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsmall : (N + 1 : ℝ) / m < ε / 4 := by
    apply (div_lt_iff₀ hmpos).mpr
    have h := (le_max_right (2 : ℝ) _).trans_lt hm
    have h' := (div_lt_iff₀ hε).mp h
    nlinarith
  refine ⟨m, hm2, averagedInverse m N, ?_, ?_⟩
  · exact (sqNorm_averagedInverse_le m N hm2).trans_lt (hsmall.trans (by linarith))
  · exact (sqNorm_prefixSum_residual_le m N hm2).trans_lt (by linarith)

end Radial
end FreeGroupFactorMain

end

end OAI
