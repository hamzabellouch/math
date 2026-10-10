import Mathlib

namespace OAI

section
section
section
section
noncomputable section
open scoped InnerProductSpace
open Set

namespace CannonDuality

variable {ι : Type*} [Fintype ι]
abbrev Weights (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

def Nonnegative (w : Weights ι) : Prop := ∀ i, 0 ≤ w i

def Admissible (V : Set (Weights ι)) (w : Weights ι) : Prop :=
  Nonnegative w ∧ ∀ v ∈ V, 1 ≤ ⟪w, v⟫_ℝ

def Modulus (V : Set (Weights ι)) : ℝ :=
  sInf {e : ℝ | ∃ w : Weights ι, Admissible V w ∧ e = ‖w‖ ^ 2}

lemma inner_bound_convexHull {V : Set (Weights ι)} {w : Weights ι} {c : ℝ}
    (h : ∀ v ∈ V, c ≤ ⟪w, v⟫_ℝ) :
    ∀ v ∈ convexHull ℝ V, c ≤ ⟪w, v⟫_ℝ := by
  apply convexHull_min h
  intro x hx y hy a b ha hb hab
  change c ≤ ⟪w, a • x + b • y⟫_ℝ
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  change c ≤ ⟪w, x⟫_ℝ at hx
  change c ≤ ⟪w, y⟫_ℝ at hy
  calc
    c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    _ ≤ a * ⟪w, x⟫_ℝ + b * ⟪w, y⟫_ℝ :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma nonnegative_convexHull {V : Set (Weights ι)}
    (h : ∀ v ∈ V, Nonnegative v) :
    ∀ v ∈ convexHull ℝ V, Nonnegative v := by
  apply convexHull_min h
  intro x hx y hy a b ha hb hab i
  change 0 ≤ a * x i + b * y i
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem exists_dual_minimizer (V : Finset (Weights ι)) (hne : V.Nonempty)
    (hnonneg : ∀ v ∈ V, Nonnegative v)
    (hpositive : ∀ v ∈ V, 1 ≤ ∑ i, v i) :
    ∃ P ∈ convexHull ℝ (V : Set (Weights ι)),
      Nonnegative P ∧ P ≠ 0 ∧ ∀ v ∈ V, ‖P‖ ^ 2 ≤ ⟪P, v⟫_ℝ := by
  have hK : (convexHull ℝ (V : Set (Weights ι))).Nonempty :=
    hne.to_set.mono (subset_convexHull ℝ _)
  obtain ⟨P, hP, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hK
    ((V.finite_toSet.isCompact_convexHull ℝ).isComplete)
    (convex_convexHull ℝ _) (0 : Weights ι)
  refine ⟨P, hP, nonnegative_convexHull hnonneg P hP, ?_, ?_⟩
  · let one : Weights ι := (WithLp.toLp 2 fun _ => (1 : ℝ))
    have hsum : ∀ v ∈ (V : Set (Weights ι)), 1 ≤ ⟪one, v⟫_ℝ := by
      intro v hv
      simpa [one, EuclideanSpace.inner_eq_star_dotProduct, dotProduct] using hpositive v hv
    have hb := inner_bound_convexHull hsum P hP
    intro hz
    norm_num [hz] at hb
  · have hproj := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ _)
      hP).mp hmin
    intro v hv
    have hi := hproj v (subset_convexHull ℝ _ hv)
    simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hi
    linarith

lemma normalized_admissible {V : Set (Weights ι)} {P : Weights ι}
    (hP : Nonnegative P) (hPne : P ≠ 0)
    (hdual : ∀ v ∈ V, ‖P‖ ^ 2 ≤ ⟪P, v⟫_ℝ) :
    Admissible V ((‖P‖ ^ 2)⁻¹ • P) := by
  have hp : 0 < ‖P‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hPne)
  constructor
  · intro i
    change 0 ≤ (‖P‖ ^ 2)⁻¹ * P i
    exact mul_nonneg (inv_nonneg.mpr hp.le) (hP i)
  · intro v hv
    rw [real_inner_smul_left]
    calc
      1 = (‖P‖ ^ 2)⁻¹ * ‖P‖ ^ 2 := (inv_mul_cancel₀ hp.ne').symm
      _ ≤ (‖P‖ ^ 2)⁻¹ * ⟪P, v⟫_ℝ :=
        mul_le_mul_of_nonneg_left (hdual v hv) (inv_nonneg.mpr hp.le)

lemma normalized_energy {P : Weights ι} (hPne : P ≠ 0) :
    ‖(‖P‖ ^ 2)⁻¹ • P‖ ^ 2 = (‖P‖ ^ 2)⁻¹ := by
  have hp : ‖P‖ ≠ 0 := norm_ne_zero_iff.mpr hPne
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

lemma admissible_energy_lower {V : Set (Weights ι)} {P : Weights ι}
    (hP : P ∈ convexHull ℝ V) (hPne : P ≠ 0)
    {w : Weights ι} (hw : Admissible V w) :
    (‖P‖ ^ 2)⁻¹ ≤ ‖w‖ ^ 2 := by
  have hpair : 1 ≤ ⟪w, P⟫_ℝ := inner_bound_convexHull hw.2 P hP
  have hcs := real_inner_mul_inner_self_le w P
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hprod : 1 ≤ ‖w‖ ^ 2 * ‖P‖ ^ 2 := by nlinarith
  have hp : 0 < ‖P‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hPne)
  simpa only [one_div] using (div_le_iff₀ hp).mpr hprod

theorem modulus_eq_inverse_dual_energy (V : Finset (Weights ι)) (hne : V.Nonempty)
    (hnonneg : ∀ v ∈ V, Nonnegative v)
    (hpositive : ∀ v ∈ V, 1 ≤ ∑ i, v i) :
    ∃ P ∈ convexHull ℝ (V : Set (Weights ι)),
      Nonnegative P ∧ P ≠ 0 ∧
      Modulus (V : Set (Weights ι)) = (‖P‖ ^ 2)⁻¹ ∧
      Admissible (V : Set (Weights ι)) ((‖P‖ ^ 2)⁻¹ • P) := by
  obtain ⟨P, hP, hnon, hneP, hdual⟩ := exists_dual_minimizer V hne hnonneg hpositive
  have hadm := normalized_admissible hnon hneP hdual
  have henergy := normalized_energy hneP
  refine ⟨P, hP, hnon, hneP, ?_, hadm⟩
  apply le_antisymm
  · apply csInf_le
    · use 0
      rintro _ ⟨w, _, rfl⟩
      exact sq_nonneg ‖w‖
    · exact ⟨_, hadm, henergy.symm⟩
  · apply le_csInf
    · exact ⟨_, _, hadm, rfl⟩
    · rintro e ⟨w, hw, rfl⟩
      exact admissible_energy_lower hP hneP hw

theorem crossing_dual_weights (V : Finset (Weights ι)) (W : Set (Weights ι))
    (hne : V.Nonempty) (hnonneg : ∀ v ∈ V, Nonnegative v)
    (hpositive : ∀ v ∈ V, 1 ≤ ∑ i, v i)
    (hcross : ∀ w ∈ W, ∀ v ∈ V, 1 ≤ ⟪w, v⟫_ℝ) :
    ∃ P : Weights ι, Admissible W P ∧
      ‖P‖ ^ 2 = (Modulus (V : Set (Weights ι)))⁻¹ := by
  obtain ⟨P, hP, hnon, hneP, hmod, _⟩ :=
    modulus_eq_inverse_dual_energy V hne hnonneg hpositive
  refine ⟨P, ⟨hnon, ?_⟩, ?_⟩
  · intro w hw
    rw [real_inner_comm]
    exact inner_bound_convexHull (hcross w hw) P hP
  · rw [hmod, inv_inv]

end CannonDuality

namespace CannonCells
open Set CannonDuality
open scoped InnerProductSpace

variable {X ι : Type*} [Fintype ι]

noncomputable def indices (C : ι → Set X) (A : Set X) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (A ∩ C i).Nonempty)

noncomputable def weight (s : Finset ι) : Weights ι := by
  classical
  exact WithLp.toLp 2 (fun i => if i ∈ s then (1:ℝ) else 0)

noncomputable def incidence (C : ι → Set X) (A : Set X) : Weights ι :=
  weight (indices C A)

noncomputable def familyVectors (C : ι → Set X) (F : Set (Set X)) : Finset (Weights ι) :=
  ((Set.toFinite (indices C '' F)).toFinset).image weight

lemma mem_indices (C : ι → Set X) (A : Set X) (i : ι) :
    i ∈ indices C A ↔ (A ∩ C i).Nonempty := by
  classical
  simp [indices]

lemma mem_familyVectors (C : ι → Set X) (F : Set (Set X)) (v : Weights ι) :
    v ∈ familyVectors C F ↔ ∃ A ∈ F, incidence C A = v := by
  classical
  simp only [familyVectors,Finset.mem_image,Set.Finite.mem_toFinset,Set.mem_image,incidence]
  constructor
  · rintro ⟨s,⟨A,hA,rfl⟩,hv⟩
    exact ⟨A,hA,hv⟩
  · rintro ⟨A,hA,hv⟩
    exact ⟨indices C A,⟨A,hA,rfl⟩,hv⟩

lemma incidence_nonnegative (C : ι → Set X) (A : Set X) : Nonnegative (incidence C A) := by
  classical
  intro i
  change 0 ≤ if i ∈ indices C A then (1:ℝ) else 0
  split <;> norm_num

lemma incidence_at (C : ι → Set X) (A : Set X) {i : ι} (hi : (A ∩ C i).Nonempty) :
    incidence C A i = 1 := by
  classical
  change (if i ∈ indices C A then (1:ℝ) else 0) = 1
  rw [ite_eq_left ((mem_indices C A i).mpr hi)]

lemma incidence_positive (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {A : Set X} (hA : A.Nonempty) : 1 ≤ ∑ i, incidence C A i := by
  classical
  obtain ⟨x,hx⟩ := hA
  obtain ⟨i,hi⟩ := hC x
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => incidence_nonnegative C A j)
    (Finset.mem_univ i)
  rwa [incidence_at C A ⟨x,hx,hi⟩] at h

lemma incidence_cross (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {A B : Set X} (hAB : (A ∩ B).Nonempty) :
    1 ≤ ⟪incidence C A,incidence C B⟫_ℝ := by
  classical
  obtain ⟨x,hxA,hxB⟩ := hAB
  obtain ⟨i,hi⟩ := hC x
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct]
  have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    mul_nonneg (incidence_nonnegative C B j) (incidence_nonnegative C A j)) (Finset.mem_univ i)
  rw [incidence_at C A ⟨x,hxA,hi⟩,incidence_at C B ⟨x,hxB,hi⟩,one_mul] at hh
  exact hh

noncomputable def modulus (C : ι → Set X) (F : Set (Set X)) : ℝ :=
  Modulus (familyVectors C F : Set (Weights ι))

lemma admissible_iff (C : ι → Set X) (F : Set (Set X)) (w : Weights ι) :
    Admissible (familyVectors C F : Set (Weights ι)) w ↔
      Nonnegative w ∧ ∀ A ∈ F, 1 ≤ ∑ i ∈ indices C A, w i := by
  classical
  have hinner (A : Set X) : ⟪w,incidence C A⟫_ℝ = ∑ i ∈ indices C A, w i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [incidence,weight,dotProduct]
  constructor
  · rintro ⟨hn,hw⟩
    refine ⟨hn,fun A hA => ?_⟩
    rw [← hinner]
    exact hw _ ((mem_familyVectors C F _).mpr ⟨A,hA,rfl⟩)
  · rintro ⟨hn,hw⟩
    refine ⟨hn,?_⟩
    intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    rw [hinner]
    exact hw A hA

lemma familyVectors_nonempty (C : ι → Set X) {F : Set (Set X)} (hF : F.Nonempty) :
    (familyVectors C F).Nonempty := by
  obtain ⟨A,hA⟩ := hF
  exact ⟨incidence C A,(mem_familyVectors C F _).mpr ⟨A,hA,rfl⟩⟩

theorem modulus_minimum (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {F : Set (Set X)} (hF : F.Nonempty) (hFn : ∀ A ∈ F, A.Nonempty) :
    0 < modulus C F ∧ ∃ w : Weights ι,
      Admissible (familyVectors C F : Set (Weights ι)) w ∧ ‖w‖^2 = modulus C F := by
  have hn : ∀ v ∈ familyVectors C F, Nonnegative v := by
    intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    exact incidence_nonnegative C A
  have hp : ∀ v ∈ familyVectors C F, 1 ≤ ∑ i, v i := by
    intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    exact incidence_positive C hC (hFn A hA)
  obtain ⟨P,_,_,hP,hmod,hadm⟩ := modulus_eq_inverse_dual_energy
    (familyVectors C F) (familyVectors_nonempty C hF) hn hp
  have hpositive : 0 < ‖P‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hP)
  refine ⟨?_,(‖P‖^2)⁻¹ • P,hadm,?_⟩
  · change 0 < Modulus _
    rw [hmod]
    exact inv_pos.mpr hpositive
  · exact (normalized_energy hP).trans hmod.symm

theorem transverse_weights (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {F H : Set (Set X)} (hF : F.Nonempty) (hFn : ∀ A ∈ F, A.Nonempty)
    (hcross : ∀ A ∈ F, ∀ B ∈ H, (A ∩ B).Nonempty) :
    ∃ ρ : Weights ι, Admissible (familyVectors C H : Set (Weights ι)) ρ ∧
      ‖ρ‖^2 = (modulus C F)⁻¹ := by
  apply crossing_dual_weights (familyVectors C F) (familyVectors C H : Set (Weights ι))
    (familyVectors_nonempty C hF)
  · intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    exact incidence_nonnegative C A
  · intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    exact incidence_positive C hC (hFn A hA)
  · intro w hw v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    obtain ⟨B,hB,rfl⟩ := (mem_familyVectors C H w).mp hw
    exact incidence_cross C hC (by simpa only [Set.inter_comm] using hcross A hA B hB)

end CannonCells
end

end
end
end
end

end OAI
