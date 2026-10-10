import Mathlib
import OAI.GroupTheory.FiniteType.PresentationGeometryCellCoverExtensionAnyAttachingLiftNullhomotopic

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
namespace DiskHEP
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Boundary (n : ℕ) := sphere (0 : Fin n → ℝ) 1
abbrev Corner (n : ℕ) := {z : I × Disk n // z.1 = 0 ∨ ‖z.2.1‖ = 1}

def den {n : ℕ} (z : I × Disk n) : ℝ := max (2-(z.1:ℝ)) (2*‖z.2.1‖)
def ratio {n : ℕ} (z : I × Disk n) : ℝ := 2 / den z

lemma norm_le {n : ℕ} (x : Disk n) : ‖x.1‖ ≤ 1 := by
  simpa only [mem_closedBall,dist_zero_right] using x.2

lemma den_pos {n : ℕ} (z : I × Disk n) : 0 < den z :=
  lt_of_lt_of_le (by linarith [z.1.2.2] : 0 < 2-(z.1:ℝ)) (le_max_left _ _)

lemma den_le {n : ℕ} (z : I × Disk n) : den z ≤ 2 := by
  apply max_le <;> linarith [z.1.2.1,norm_le z.2]

lemma ratio_pos {n : ℕ} (z : I × Disk n) : 0 < ratio z := div_pos (by norm_num) (den_pos z)
lemma ratio_ge {n : ℕ} (z : I × Disk n) : 1 ≤ ratio z :=
  (le_div_iff₀ (den_pos z)).mpr (by simpa using den_le z)

lemma ratio_mul_den {n : ℕ} (z : I × Disk n) : ratio z * den z = 2 :=
  div_mul_cancel₀ _ (ne_of_gt (den_pos z))

lemma time_bounds {n : ℕ} (z : I × Disk n) :
    2 - ratio z * (2-(z.1:ℝ)) ∈ Icc (0:ℝ) 1 := by
  have hden : 2-(z.1:ℝ) ≤ den z := le_max_left _ _
  have hmul := mul_le_mul_of_nonneg_left hden (ratio_pos z).le
  rw [ratio_mul_den] at hmul
  have ht : 1 ≤ 2-(z.1:ℝ) := by linarith [z.1.2.2]
  constructor
  · linarith
  · nlinarith [ratio_ge z]

lemma point_bound {n : ℕ} (z : I × Disk n) : ‖ratio z • z.2.1‖ ≤ 1 := by
  rw [norm_smul,Real.norm_of_nonneg (ratio_pos z).le]
  have hden : 2*‖z.2.1‖ ≤ den z := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hden (ratio_pos z).le
  rw [ratio_mul_den] at hmul
  nlinarith

lemma hits_corner {n : ℕ} (z : I × Disk n) :
    2 - ratio z * (2-(z.1:ℝ)) = 0 ∨ ‖ratio z • z.2.1‖ = 1 := by
  rcases le_total (2*‖z.2.1‖) (2-(z.1:ℝ)) with h | h
  · left
    have he : den z = 2-(z.1:ℝ) := max_eq_left h
    have hm := ratio_mul_den z
    rw [he] at hm
    linarith
  · right
    have he : den z = 2*‖z.2.1‖ := max_eq_right h
    have hm := ratio_mul_den z
    rw [he] at hm
    rw [norm_smul,Real.norm_of_nonneg (ratio_pos z).le]
    nlinarith

lemma continuous_ratio (n : ℕ) : Continuous (ratio (n := n)) := by
  apply Continuous.div continuous_const
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).max
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd).norm)
  · intro z
    exact ne_of_gt (den_pos z)

def retract (n : ℕ) : C(I × Disk n, Corner n) :=
  ⟨fun z => ⟨(⟨2-ratio z*(2-(z.1:ℝ)),time_bounds z⟩,
    ⟨ratio z • z.2.1,by simpa only [mem_closedBall,dist_zero_right] using point_bound z⟩),
    (hits_corner z).imp (fun h => Subtype.ext h) id⟩,
    (((continuous_const.sub ((continuous_ratio n).mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))).subtype_mk _).prodMk
    (((continuous_ratio n).smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _)).subtype_mk _⟩

lemma ratio_eq_one {n : ℕ} (z : Corner n) : ratio z.1 = 1 := by
  have hd : den z.1 = 2 := by
    rcases z.2 with h | h
    · change max (2 - (z.1.1:ℝ)) (2 * ‖z.1.2.1‖) = 2
      rw [h]
      change max (2 - (0:ℝ)) (2 * ‖z.1.2.1‖) = 2
      rw [sub_zero]
      exact max_eq_left (by linarith [norm_le z.1.2])
    · simp only [den,h,mul_one]
      exact max_eq_right (by linarith [z.1.1.2.1])
  simp [ratio,hd]

@[simp] lemma retract_corner {n : ℕ} (z : Corner n) : retract n z.1 = z := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change 2-ratio z.1*(2-(z.1.1:ℝ)) = _
    rw [ratio_eq_one]
    ring
  · apply Subtype.ext
    change ratio z.1 • z.1.2.1 = _
    rw [ratio_eq_one,one_smul]

def boundaryInclusion (n : ℕ) : C(Boundary n,Disk n) :=
  ⟨fun x => ⟨x.1, sphere_subset_closedBall x.2⟩,continuous_subtype_val.subtype_mk _⟩

def bottom (n : ℕ) : C(Disk n,Corner n) :=
  ⟨fun x => ⟨(0,x),Or.inl rfl⟩,(continuous_const.prodMk continuous_id).subtype_mk _⟩

def side (n : ℕ) : C(I × Boundary n,Corner n) :=
  ⟨fun z => ⟨(z.1,boundaryInclusion n z.2),Or.inr (by
      simpa only [mem_sphere,dist_zero_right,boundaryInclusion,ContinuousMap.coe_mk] using z.2.2)⟩,
    (continuous_fst.prodMk ((boundaryInclusion n).continuous.comp continuous_snd)).subtype_mk _⟩

def cornerQuot (n : ℕ) : C(Disk n ⊕ (I × Boundary n),Corner n) :=
  ⟨Sum.elim (bottom n) (side n),continuous_sum_dom.mpr ⟨(bottom n).continuous,(side n).continuous⟩⟩

theorem cornerQuot_surjective (n : ℕ) : Function.Surjective (cornerQuot n) := by
  intro z
  rcases z.2 with h | h
  · refine ⟨Sum.inl z.1.2,Subtype.ext ?_⟩
    exact Prod.ext h.symm rfl
  · let b : Boundary n := ⟨z.1.2.1,by simpa only [mem_sphere,dist_zero_right] using h⟩
    exact ⟨Sum.inr (z.1.1,b),Subtype.ext (Prod.ext rfl (Subtype.ext rfl))⟩

theorem cornerQuot_isQuotientMap (n : ℕ) : IsQuotientMap (cornerQuot n) :=
  IsQuotientMap.of_surjective_continuous (cornerQuot_surjective n) (cornerQuot n).continuous

universe u
variable {Y : Type u} [TopologicalSpace Y]

def cornerData {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y)) :
    C(Disk n ⊕ (I × Boundary n),Y) :=
  ⟨Sum.elim f h,continuous_sum_dom.mpr ⟨f.continuous,h.continuous⟩⟩

theorem cornerData_factors {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b)) :
    Function.FactorsThrough (cornerData f h) (cornerQuot n) := by
  intro a b hab
  have he := congrArg Subtype.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg f (congrArg Prod.snd he)
    | inr b =>
      have ht : b.1 = 0 := (congrArg Prod.fst he).symm
      have hx : a = boundaryInclusion n b.2 := congrArg Prod.snd he
      change f a = h b
      rw [hx,← h0]
      exact congrArg h (Prod.ext ht.symm rfl)
  | inr a =>
    cases b with
    | inl b =>
      have ht : a.1 = 0 := congrArg Prod.fst he
      have hx : boundaryInclusion n a.2 = b := congrArg Prod.snd he
      change h a = f b
      rw [← hx,← h0]
      exact congrArg h (Prod.ext ht rfl)
    | inr b =>
      apply congrArg h
      refine Prod.ext (show a.1 = b.1 from congrArg (fun z : I × Disk n => z.1) he) ?_
      apply Subtype.ext
      exact congrArg (fun z : I × Disk n => z.2.1) he

def extend {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b)) : C(I × Disk n,Y) :=
  ((cornerQuot_isQuotientMap n).lift (cornerData f h) (cornerData_factors f h h0)).comp (retract n)

lemma extend_corner {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b))
    (z : Disk n ⊕ (I × Boundary n)) :
    extend f h h0 (cornerQuot n z).1 = cornerData f h z := by
  change (cornerQuot_isQuotientMap n).lift (cornerData f h) (cornerData_factors f h h0) (retract n (cornerQuot n z).1) = _
  rw [retract_corner]
  exact DFunLike.congr_fun ((cornerQuot_isQuotientMap n).lift_comp (cornerData f h) (cornerData_factors f h h0)) z

@[simp] theorem extend_zero {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b)) (x : Disk n) :
    extend f h h0 (0,x) = f x :=
  extend_corner f h h0 (Sum.inl x)

@[simp] theorem extend_side {n : ℕ} (f : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f (boundaryInclusion n b)) (t : I) (b : Boundary n) :
    extend f h h0 (t,boundaryInclusion n b) = h (t,b) :=
  extend_corner f h h0 (Sum.inr (t,b))

end DiskHEP

namespace SimplexBoundary
open Set Topology Metric
open scoped unitInterval
abbrev Simplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))
abbrev Boundary (n : ℕ) := {s : Simplex n // ∃ i, s.weights i = 0}

def face {n : ℕ} (i : Fin (n+2)) : C(Simplex n, Simplex (n+1)) :=
  ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ _⟩

lemma face_zero {n : ℕ} (i : Fin (n+2)) (s : Simplex n) : (face i s).weights i = 0 := by
  exact Finsupp.mapDomain_of_notMem_range s.weights i (by simp)

lemma face_succAbove {n : ℕ} (i : Fin (n+2)) (s : Simplex n) (j : Fin (n+1)) :
    (face i s).weights (i.succAbove j) = s.weights j := by
  exact Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective s.weights j

def drop {n : ℕ} (i : Fin (n+2)) (s : Simplex (n+1)) (hi : s.weights i = 0) : Simplex n where
  weights := Finsupp.equivFunOnFinite.symm (fun j => s.weights (i.succAbove j))
  nonneg := by
    intro j
    exact s.weights_nonneg _
  total := by
    have hs := s.total_of_fintype
    rw [Fin.sum_univ_succAbove _ i, hi,zero_add] at hs
    simpa [Finsupp.sum_fintype] using hs

lemma face_drop {n : ℕ} (i : Fin (n+2)) (s : Simplex (n+1)) (hi : s.weights i = 0) :
    face i (drop i s hi) = s := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k,h⟩
  · subst j
    exact (face_zero _ _).trans hi.symm
  · subst j
    exact face_succAbove i _ k

def faceQuot (n : ℕ) : C(Fin (n+2) × Simplex n, Boundary (n+1)) :=
  ⟨fun z => ⟨face z.1 z.2,⟨z.1,face_zero _ _⟩⟩,
    (continuous_prod_of_discrete_left.mpr (fun i => (face i).continuous)).subtype_mk _⟩

theorem faceQuot_surjective (n : ℕ) : Function.Surjective (faceQuot n) := by
  intro s
  obtain ⟨i,hi⟩ := s.2
  exact ⟨(i,drop i s.1 hi),Subtype.ext (face_drop i s.1 hi)⟩

theorem faceQuot_isQuotientMap (n : ℕ) : IsQuotientMap (faceQuot n) :=
  IsQuotientMap.of_surjective_continuous (faceQuot_surjective n) (faceQuot n).continuous

def boundaryEquiv (n : ℕ) : Boundary n ≃ₜ DiskHEP.Boundary n where
  toFun s := ⟨(SimplexDisk.diskEquiv n s.1).1,by
    rw [mem_sphere,dist_zero_right]
    exact (SimplexDisk.diskEquiv_boundary_iff s.1).mpr s.2⟩
  invFun v := ⟨(SimplexDisk.diskEquiv n).symm ⟨v.1,sphere_subset_closedBall v.2⟩,by
    apply (SimplexDisk.diskEquiv_boundary_iff _).mp
    rw [Homeomorph.apply_symm_apply]
    simpa only [mem_sphere,dist_zero_right] using v.2⟩
  left_inv s := by
    apply Subtype.ext
    exact (SimplexDisk.diskEquiv n).symm_apply_apply s.1
  right_inv v := by
    apply Subtype.ext
    exact congrArg (fun z : DiskHEP.Disk n => z.1)
      ((SimplexDisk.diskEquiv n).apply_symm_apply ⟨v.1,sphere_subset_closedBall v.2⟩)
  continuous_toFun :=
    (continuous_subtype_val.comp ((SimplexDisk.diskEquiv n).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((SimplexDisk.diskEquiv n).symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

universe u
variable {Y : Type u} [TopologicalSpace Y]

def glueFaces {n : ℕ} (h : Fin (n+2) → C(Simplex n,Y))
    (hh : ∀ i j a b, face i a = face j b → h i a = h j b) : C(Boundary (n+1),Y) :=
  (faceQuot_isQuotientMap n).lift
    ⟨fun z => h z.1 z.2,continuous_prod_of_discrete_left.mpr (fun i => (h i).continuous)⟩
    (fun a b hab => hh a.1 b.1 a.2 b.2 (congrArg Subtype.val hab))

@[simp] theorem glueFaces_face {n : ℕ} (h : Fin (n+2) → C(Simplex n,Y))
    (hh : ∀ i j a b, face i a = face j b → h i a = h j b)
    (i : Fin (n+2)) (a : Simplex n) : glueFaces h hh (faceQuot n (i,a)) = h i a := by
  exact DFunLike.congr_fun ((faceQuot_isQuotientMap n).lift_comp
    (⟨fun z => h z.1 z.2,continuous_prod_of_discrete_left.mpr (fun i => (h i).continuous)⟩ :
      C(Fin (n+2) × Simplex n,Y))
    (fun a b hab => hh a.1 b.1 a.2 b.2 (congrArg Subtype.val hab))) (i,a)

end SimplexBoundary

end

end OAI
