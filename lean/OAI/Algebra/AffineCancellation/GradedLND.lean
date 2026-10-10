import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.GradedLND
open DirectSum
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (G : ℤ → Submodule k R) [GradedAlgebra G]

abbrev proj (i : ℤ) : R →ₗ[k] R := GradedAlgebra.proj G i

lemma proj_mem (i : ℤ) (r : R) : proj G i r ∈ G i :=
  (decompose G r i).property

lemma proj_of_mem {r : R} {i : ℤ} (hr : r ∈ G i) : proj G i r = r :=
  decompose_of_mem_same G hr

lemma proj_of_mem_ne {r : R} {i j : ℤ} (hr : r ∈ G i) (hne : i ≠ j) :
    proj G j r = 0 := decompose_of_mem_ne G hr hne

lemma proj_mul_left {r : R} {i : ℤ} (hr : r ∈ G i) (s : R) (j : ℤ) :
    proj G (i+j) (r*s) = r * proj G j s :=
  coe_decompose_mul_add_of_left_mem G hr

lemma proj_mul_right (r : R) {s : R} {j : ℤ} (hs : s ∈ G j) (i : ℤ) :
    proj G (i+j) (r*s) = proj G i r * s :=
  coe_decompose_mul_add_of_right_mem G hs

/-- The shift-j component of a linear map, on an arbitrary ℤ-graded algebra. -/
def componentLinear (D : R →ₗ[k] R) (j : ℤ) : R →ₗ[k] R :=
  (DirectSum.toModule k ℤ R (fun i =>
    ((proj G (i+j)).comp D).comp (G i).subtype)).comp
    (DirectSum.decomposeAlgEquiv G).toLinearMap

lemma componentLinear_of_mem (D : R →ₗ[k] R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : componentLinear G D j r = proj G (i+j) (D r) := by
  change DirectSum.toModule k ℤ R _ (decompose G r) = _
  rw [decompose_of_mem G hr]
  change DirectSum.toModule k ℤ R (fun t =>
    ((proj G (t+j)).comp D).comp (G t).subtype)
      (DirectSum.lof k ℤ (fun t => G t) i ⟨r, hr⟩) = _
  rw [DirectSum.toModule_lof]
  rfl

lemma componentLinear_leibniz (D : Derivation k R R) (j : ℤ) (r s : R) :
    componentLinear G D.toLinearMap j (r*s) =
      r * componentLinear G D.toLinearMap j s + s * componentLinear G D.toLinearMap j r := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp
  | @homogeneous i r =>
    induction s using DirectSum.Decomposition.inductionOn G with
    | zero => simp
    | @homogeneous h s =>
      rw [componentLinear_of_mem G D.toLinearMap j (SetLike.GradedMul.mul_mem r.2 s.2),
        componentLinear_of_mem G D.toLinearMap j s.2,
        componentLinear_of_mem G D.toLinearMap j r.2]
      simp only [Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, map_add]
      rw [show i+h+j = i+(h+j) by omega, proj_mul_left G r.2]
      rw [show i+(h+j) = h+(i+j) by omega, proj_mul_left G s.2]
    | add s t hs ht => simp only [mul_add, map_add, hs, ht, add_mul]; abel
  | add r t hr ht => simp only [add_mul, map_add, hr, ht, mul_add]; abel

def component (D : Derivation k R R) (j : ℤ) : Derivation k R R :=
  Derivation.mk' (componentLinear G D.toLinearMap j) (by
    intro r s
    simpa only [smul_eq_mul] using componentLinear_leibniz G D j r s)

lemma component_of_mem (D : Derivation k R R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : component G D j r = proj G (i+j) (D r) :=
  componentLinear_of_mem G D.toLinearMap j hr

lemma component_homogeneous (D : Derivation k R R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : component G D j r ∈ G (i+j) := by
  rw [component_of_mem G D j hr]
  exact proj_mem G _ _

/-- The increasing filtration associated to an integer grading. -/
def filtration (d : ℤ) : Submodule k R := ⨆ i : {i : ℤ // i ≤ d}, G i

omit [GradedAlgebra G] in
lemma mem_filtration {r : R} {i d : ℤ} (hr : r ∈ G i) (hid : i ≤ d) :
    r ∈ filtration G d := Submodule.mem_iSup_of_mem ⟨i, hid⟩ hr

omit [GradedAlgebra G] in
lemma filtration_mono {d e : ℤ} (h : d ≤ e) : filtration G d ≤ filtration G e := by
  apply iSup_le
  intro i
  exact fun r hr => mem_filtration G hr (i.2.trans h)

lemma proj_filtration {r : R} {d i : ℤ} (hr : r ∈ filtration G d) (hdi : d < i) :
    proj G i r = 0 := by
  refine Submodule.iSup_induction (fun t : {i : ℤ // i ≤ d} => G t)
    (motive := fun r => proj G i r = 0) hr ?_ ?_ ?_
  · intro t r hr
    exact proj_of_mem_ne G hr (by have ht := t.2; omega)
  · exact map_zero _
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

lemma exists_filtration (r : R) : ∃ d, r ∈ filtration G d := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | @homogeneous i r => exact ⟨i, mem_filtration G r.2 le_rfl⟩
  | add r s hr hs =>
    obtain ⟨d, hd⟩ := hr
    obtain ⟨e, he⟩ := hs
    exact ⟨max d e, Submodule.add_mem _
      (filtration_mono G (le_max_left d e) hd) (filtration_mono G (le_max_right d e) he)⟩

def ShiftBound (D : Derivation k R R) (j : ℤ) : Prop :=
  ∀ i r, r ∈ G i → D r ∈ filtration G (i+j)

omit [GradedAlgebra G] in
lemma map_filtration {D : Derivation k R R} {j : ℤ} (hD : ShiftBound G D j)
    {r : R} {d : ℤ} (hr : r ∈ filtration G d) : D r ∈ filtration G (d+j) := by
  refine Submodule.iSup_induction (fun t : {i : ℤ // i ≤ d} => G t)
    (motive := fun r => D r ∈ filtration G (d+j)) hr ?_ ?_ ?_
  · intro i r hr
    exact filtration_mono G (by have ht := i.2; omega) (hD i r hr)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb

lemma top_map {D : Derivation k R R} {j : ℤ} (hD : ShiftBound G D j)
    {r : R} {d : ℤ} (hr : r ∈ filtration G d) :
    proj G (d+j) (D r) = component G D j (proj G d r) := by
  refine Submodule.iSup_induction (fun t : {i : ℤ // i ≤ d} => G t)
    (motive := fun r => proj G (d+j) (D r) = component G D j (proj G d r))
    hr ?_ ?_ ?_
  · intro i r hr
    by_cases hi : (i : ℤ) = d
    · have hr' : r ∈ G d := hi ▸ hr
      rw [proj_of_mem G hr', component_of_mem G D j hr']
    · have hid : (i : ℤ) < d := lt_of_le_of_ne i.2 hi
      rw [proj_of_mem_ne G hr hi, map_zero]
      exact proj_filtration G (hD i r hr) (by omega)
  · simp
  · intro a b ha hb
    simp only [map_add, ha, hb]

lemma iterate_top {D : Derivation k R R} {j : ℤ} (hD : ShiftBound G D j)
    {r : R} {i : ℤ} (hr : r ∈ G i) (n : ℕ) :
    (D : R → R)^[n] r ∈ filtration G (i+n*j) ∧
    proj G (i+n*j) ((D : R → R)^[n] r) = ((component G D j : R → R)^[n] r) := by
  induction n with
  | zero => simpa using And.intro (mem_filtration G hr le_rfl) (proj_of_mem G hr)
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hn : i+(↑(n+1) : ℤ)*j = (i+n*j)+j := by push_cast; ring
    rw [hn]
    exact ⟨map_filtration G hD ih.1, (top_map G hD ih.1).trans (congrArg _ ih.2)⟩

/-- Local nilpotence survives passage to the highest homogeneous component,
including for gradings with negative degrees. -/
lemma component_locallyNilpotent {D : Derivation k R R} {j : ℤ}
    (hD : ShiftBound G D j) (hln : ∀ r : R, ∃ n : ℕ, (D : R → R)^[n] r = 0) :
    ∀ r : R, ∃ n : ℕ, (component G D j : R → R)^[n] r = 0 := by
  intro r
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => exact ⟨0, rfl⟩
  | @homogeneous i r =>
    obtain ⟨n, hn⟩ := hln r
    refine ⟨n, ?_⟩
    have h := (iterate_top G hD r.2 n).2
    rw [hn, map_zero] at h
    exact h.symm
  | add r s hr hs =>
    obtain ⟨n, hn⟩ := hr
    obtain ⟨m, hm⟩ := hs
    let E := (component G D j).toLinearMap
    change (E : R → R)^[n] r = 0 at hn
    change (E : R → R)^[m] s = 0 at hm
    refine ⟨n+m, ?_⟩
    change (E : R → R)^[n+m] (r+s) = 0
    rw [← Module.End.pow_apply, map_add]
    have hnr : (E ^ (n+m)) r = 0 := by
      rw [Module.End.pow_apply, Nat.add_comm, Function.iterate_add_apply, hn]
      simpa only [Module.End.pow_apply] using (E ^ m).map_zero
    have hms : (E ^ (n+m)) s = 0 := by
      rw [Module.End.pow_apply, Function.iterate_add_apply, hm]
      simpa only [Module.End.pow_apply] using (E ^ n).map_zero
    rw [hnr, hms, add_zero]

lemma eq_zero_of_projections {r : R} (h : ∀ i, proj G i r = 0) : r = 0 := by
  apply (DirectSum.decompose G).injective
  ext i
  simpa [proj] using h i

lemma mem_filtration_iff {r : R} {d : ℤ} :
    r ∈ filtration G d ↔ ∀ i, d < i → proj G i r = 0 := by
  constructor
  · exact fun hr i hi => proj_filtration G hr hi
  · intro h
    classical
    rw [← DirectSum.sum_support_decompose G r]
    apply Submodule.sum_mem
    intro i hi
    by_cases hid : i ≤ d
    · exact mem_filtration G (proj_mem G i r) hid
    · have hz := h i (lt_of_not_ge hid)
      change proj G i r ∈ filtration G d
      rw [hz]
      exact Submodule.zero_mem _

lemma shiftBound_of_components {D : Derivation k R R} {j : ℤ}
    (hD : ∀ e, j < e → component G D e = 0) : ShiftBound G D j := by
  intro i r hr
  apply (mem_filtration_iff G).mpr
  intro b hb
  have h := DFunLike.congr_fun (hD (b-i) (by omega)) r
  rw [component_of_mem G D (b-i) hr] at h
  simpa only [add_sub_cancel, Derivation.zero_apply] using h

lemma component_exists {D : Derivation k R R} (hD : D ≠ 0) :
    ∃ j, component G D j ≠ 0 := by
  by_contra h
  push Not at h
  apply hD
  apply Derivation.ext
  intro r
  change D r = 0
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => exact map_zero D
  | @homogeneous i r =>
    apply eq_zero_of_projections G
    intro j
    have he := DFunLike.congr_fun (h (j-i)) (r : R)
    rw [component_of_mem G D (j-i) r.2] at he
    simpa only [add_sub_cancel, Derivation.zero_apply] using he
  | add r s hr hs => rw [map_add, hr, hs, add_zero]

lemma homogeneous_generators [Algebra.FiniteType k R] :
    ∃ s : Finset R, Algebra.adjoin k (s : Set R) = ⊤ ∧
      ∀ r ∈ s, ∃ i, r ∈ G i := by
  classical
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := k) (A := R)
  let ι₀ := Σ (r : F), (DirectSum.decompose G r.1).support
  let v (i : ι₀) : R := (DirectSum.decompose G i.1 i.2).1
  refine ⟨Finset.univ.image v, ?_, ?_⟩
  · rw [← top_le_iff, ← hF, Algebra.adjoin_le_iff]
    intro r hr
    rw [← DirectSum.sum_support_decompose G r]
    apply sum_mem
    intro i hi
    exact Algebra.subset_adjoin (by
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨⟨⟨r, hr⟩, i, hi⟩, rfl⟩)
  · intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨i.2, (DirectSum.decompose G i.1 i.2).property⟩

lemma component_bounded [Algebra.FiniteType k R] (D : Derivation k R R) :
    ∃ J : ℤ, ∀ j, component G D j ≠ 0 → j ≤ J := by
  classical
  obtain ⟨s, hs, hg⟩ := homogeneous_generators G
  choose deg hdeg using fun r : s => hg r r.2
  choose bound hbound using fun r : s => exists_filtration G (D r)
  have hfinite : (Set.range (fun r : s => bound r - deg r)).Finite := Set.finite_range _
  obtain ⟨J, hJ⟩ := hfinite.bddAbove
  refine ⟨J, ?_⟩
  intro j hj
  by_contra h
  apply hj
  apply Derivation.ext_of_adjoin_eq_top (s : Set R) hs
  intro r hr
  have hbound' := hJ (Set.mem_range_self (⟨r, hr⟩ : s))
  rw [component_of_mem G D j (hdeg ⟨r, hr⟩)]
  exact proj_filtration G (hbound ⟨r, hr⟩) (by omega)

/-- Every nonzero locally nilpotent derivation of a finite type graded algebra
has a nonzero highest component, itself locally nilpotent. -/
theorem highest [Algebra.FiniteType k R] (D : Derivation k R R) (hD : D ≠ 0)
    (hln : ∀ r : R, ∃ n : ℕ, (D : R → R)^[n] r = 0) :
    ∃ j, component G D j ≠ 0 ∧ ShiftBound G D j ∧
      ∀ r : R, ∃ n : ℕ, (component G D j : R → R)^[n] r = 0 := by
  obtain ⟨j, hj, hmax⟩ := Int.exists_greatest_of_bdd
    (component_bounded G D) (component_exists G hD)
  have hb : ShiftBound G D j := shiftBound_of_components G (by
    intro e he
    by_contra h
    exact (not_le_of_gt he) (hmax e h))
  exact ⟨j, hj, hb, component_locallyNilpotent G hb hln⟩

end ComplexCancellation.GradedLND

end

end OAI
