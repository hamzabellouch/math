import OAI.Analysis.ForestSpace.Norm

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Finite coordinate vectors with the segment norm (a type synonym prevents
clashes with any other norm on finitely supported functions). -/
def TestVector (V : Type) := V →₀ ℝ

def segmentSeminorm (V : Type) [PartialOrder V] : Seminorm ℝ (V →₀ ℝ) := by
  have segSum_zero [PartialOrder V] (S : Finset V) : segSum (0 : V → ℝ) S = 0 := by
    simp [segSum]
  have segSum_add [PartialOrder V] (u v : V → ℝ) (S : Finset V) :
      segSum (u + v) S = segSum u S + segSum v S := by
    simp [segSum, Finset.sum_add_distrib]
  have segSum_smul [PartialOrder V] (a : ℝ) (u : V → ℝ) (S : Finset V) :
      segSum (a • u) S = a * segSum u S := by
    simp [segSum, Finset.mul_sum]
  have TestBound.nonneg {u : V → ℝ} {C : ℝ} (h : TestBound u C) : 0 ≤ C := by
    simpa using h PEmpty inferInstance PEmpty.elim (by simp) (by simp [Pairwise])
  have TestBound.zero : TestBound (0 : V → ℝ) 0 := by
    intro ι inst S hS hd
    simp [segSum]
  have TestBound.smul {u : V → ℝ} {C : ℝ} (h : TestBound u C) (a : ℝ) :
      TestBound (a • u) (a ^ 2 * C) := by
    intro ι inst S hS hd
    have hh := mul_le_mul_of_nonneg_left (h ι inst S hS hd) (sq_nonneg a)
    simpa only [segSum_smul, mul_pow, Finset.mul_sum] using hh
  have TestBound.add {u v : V → ℝ} {A B : ℝ}
      (hu : TestBound u (A ^ 2)) (hv : TestBound v (B ^ 2))
      (hA : 0 ≤ A) (hB : 0 ≤ B) : TestBound (u + v) ((A + B) ^ 2) := by
    intro ι inst S hS hd
    have h₁ := hu ι inst S hS hd
    have h₂ := hv ι inst S hS hd
    have hc := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset ι)
      (fun i => segSum u (S i)) (fun i => segSum v (S i))
    have hs₁ : Real.sqrt (∑ i, segSum u (S i) ^ 2) ≤ A :=
      (Real.sqrt_le_iff).2 ⟨hA, h₁⟩
    have hs₂ : Real.sqrt (∑ i, segSum v (S i) ^ 2) ≤ B :=
      (Real.sqrt_le_iff).2 ⟨hB, h₂⟩
    have hc' : ∑ i, segSum u (S i) * segSum v (S i) ≤ A * B :=
      hc.trans (mul_le_mul hs₁ hs₂ (Real.sqrt_nonneg _) hA)
    have he : (∑ i, segSum (u + v) (S i) ^ 2) =
        (∑ i, segSum u (S i) ^ 2) + 2 * (∑ i, segSum u (S i) * segSum v (S i)) +
        (∑ i, segSum v (S i) ^ 2) := by
      simp only [segSum_add, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he]
    nlinarith
  have zero_mem_testValues (u : V → ℝ) : 0 ∈ testValues u := by
    refine ⟨PEmpty, inferInstance, PEmpty.elim, by simp, by simp [Pairwise], ?_⟩
    simp [segSum]
  have TestBound.bddAbove {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
      BddAbove (testValues u) := by
    refine ⟨C, ?_⟩
    rintro r ⟨ι, inst, S, hs, hd, rfl⟩
    exact h ι inst S hs hd
  have TestBound.squareSup_le {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
      squareSup u ≤ C := by
    apply csSup_le ⟨0, zero_mem_testValues u⟩
    rintro r ⟨ι, inst, S, hs, hd, rfl⟩
    exact h ι inst S hs hd
  have testBound_squareSup {u : V → ℝ} (hu : ∃ C, TestBound u C) :
      TestBound u (squareSup u) := by
    intro ι inst S hs hd
    exact le_csSup (TestBound.bddAbove hu.choose_spec) ⟨ι, inst, S, hs, hd, rfl⟩
  have squareSup_nonneg {u : V → ℝ} (hu : ∃ C, TestBound u C) : 0 ≤ squareSup u :=
    TestBound.nonneg (testBound_squareSup hu)
  have rho_nonneg (u : V → ℝ) : 0 ≤ rho u := Real.sqrt_nonneg _
  have rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : rho u ^ 2 = squareSup u :=
    Real.sq_sqrt (squareSup_nonneg hu)
  have testBound_rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : TestBound u (rho u ^ 2) := by
    rw [rho_sq hu]
    exact testBound_squareSup hu
  have rho_le_of_testBound {u : V → ℝ} {C : ℝ} (hC : 0 ≤ C)
      (hu : TestBound u (C ^ 2)) : rho u ≤ C :=
    Real.sqrt_le_iff.mpr ⟨hC, TestBound.squareSup_le hu⟩
  have rho_add_le {u v : V → ℝ} (hu : ∃ C, TestBound u C) (hv : ∃ C, TestBound v C) :
      rho (u + v) ≤ rho u + rho v :=
    rho_le_of_testBound (add_nonneg (rho_nonneg u) (rho_nonneg v))
      (TestBound.add (testBound_rho_sq hu) (testBound_rho_sq hv) (rho_nonneg u) (rho_nonneg v))
  have rho_smul_le {u : V → ℝ} (hu : ∃ C, TestBound u C) (a : ℝ) :
      rho (a • u) ≤ |a| * rho u := by
    apply rho_le_of_testBound (mul_nonneg (abs_nonneg a) (rho_nonneg u))
    have hh := TestBound.smul (testBound_rho_sq hu) a
    simpa only [mul_pow, sq_abs] using hh
  have rho_zero : rho (0 : V → ℝ) = 0 := by
    apply le_antisymm _ (rho_nonneg _)
    apply rho_le_of_testBound (C := 0) (by norm_num)
    simpa using (TestBound.zero : TestBound (0 : V → ℝ) 0)
  have l1size_nonneg [PartialOrder V] (u : V →₀ ℝ) : 0 ≤ l1size u :=
    sum_nonneg (fun vertex _ => abs_nonneg (u vertex))
  have finset_abs_sum_le_l1size [PartialOrder V] (u : V →₀ ℝ) (S : Finset V) :
      ∑ v ∈ S, |u v| ≤ l1size u := by
    have he : (∑ v ∈ S ∪ u.support, |u v|) = l1size u := by
      symm
      apply sum_subset subset_union_right
      intro v hv hn
      rw [Finsupp.notMem_support_iff.mp hn, abs_zero]
    rw [← he]
    exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun v hv hn => abs_nonneg _)
  have testBound_l1size (u : V →₀ ℝ) : TestBound u (l1size u ^ 2) := by
    intro ι inst S hS hd
    have habs : (∑ i, |segSum u (S i)|) ≤ l1size u := by
      calc
        (∑ i, |segSum u (S i)|) ≤ ∑ i, ∑ v ∈ S i, |u v| :=
          sum_le_sum fun i hi => abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ univ.biUnion S, |u v| :=
          (sum_biUnion (by intro i hi j hj hij; exact hd hij)).symm
        _ ≤ l1size u := finset_abs_sum_le_l1size u _
    have hsq := sum_sq_le_sq_sum_of_nonneg
      (s := (univ : Finset ι)) (f := fun i => |segSum u (S i)|) (fun i hi => abs_nonneg _)
    simp only [sq_abs] at hsq
    have hnonneg : 0 ≤ ∑ i, |segSum u (S i)| := sum_nonneg (fun i hi => abs_nonneg _)
    nlinarith [l1size_nonneg u]
  have finsupp_has_testBound (u : V →₀ ℝ) : ∃ C, TestBound u C := ⟨_, testBound_l1size u⟩
  exact Seminorm.ofSMulLE (fun u : V →₀ ℝ => rho u) rho_zero
    (fun u v => rho_add_le (finsupp_has_testBound u) (finsupp_has_testBound v))
    (fun a u => by simpa only [Real.norm_eq_abs, Finsupp.coe_smul] using rho_smul_le (finsupp_has_testBound u) a)

namespace TestVector
variable {V : Type}
instance : AddCommGroup (TestVector V) := inferInstanceAs (AddCommGroup (V →₀ ℝ))
instance : Module ℝ (TestVector V) := inferInstanceAs (Module ℝ (V →₀ ℝ))
def toFinsupp (u : TestVector V) : V →₀ ℝ := u
instance : CoeFun (TestVector V) (fun _ => V → ℝ) := ⟨fun u => u.toFinsupp⟩

@[ext] theorem ext {u v : TestVector V} (h : ∀ a, u a = v a) : u = v := Finsupp.ext h
@[simp] theorem zero_apply (v : V) : (0 : TestVector V) v = 0 := rfl
@[simp] theorem add_apply (u v : TestVector V) (a : V) : (u + v) a = u a + v a := rfl
@[simp] theorem smul_apply (r : ℝ) (u : TestVector V) (a : V) : (r • u) a = r * u a := rfl
@[simp] theorem coe_add (u v : TestVector V) : ⇑(u + v) = u + v := rfl
@[simp] theorem coe_smul (r : ℝ) (u : TestVector V) : ⇑(r • u) = r • ⇑u := rfl

variable [PartialOrder V]
instance : Norm (TestVector V) := ⟨fun u => rho u⟩

 theorem normCore : NormedSpace.Core ℝ (TestVector V) where
  norm_nonneg u := rho_nonneg u
  norm_triangle u v := rho_add_le (finsupp_has_testBound u.toFinsupp) (finsupp_has_testBound v.toFinsupp)
  norm_smul r u := by
    change rho (r • ⇑u) = ‖r‖ * rho u
    simpa only [Real.norm_eq_abs] using rho_smul (finsupp_has_testBound u.toFinsupp) r
  norm_eq_zero_iff u := finsupp_rho_eq_zero u.toFinsupp

instance : NormedAddCommGroup (TestVector V) := by
  have isSegment_singleton (v : V) : IsSegment ({v} : Finset V) := by
    constructor
    · intro a ha b hb
      simp only [mem_singleton] at ha hb
      subst a
      subst b
      exact Or.inl le_rfl
    · intro a ha b hb c hac hcb
      simp only [mem_singleton] at ha hb ⊢
      subst a
      subst b
      exact le_antisymm hcb hac
  have TestBound.nonneg {u : V → ℝ} {C : ℝ} (h : TestBound u C) : 0 ≤ C := by
    simpa using h PEmpty inferInstance PEmpty.elim (by simp) (by simp [Pairwise])
  have TestBound.single {u : V → ℝ} {C : ℝ} (h : TestBound u C)
      {S : Finset V} (hS : IsSegment S) : segSum u S ^ 2 ≤ C := by
    simpa using h Unit inferInstance (fun _ => S) (fun _ => hS)
      (by simp [Pairwise])
  have TestBound.bddAbove {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
      BddAbove (testValues u) := by
    refine ⟨C, ?_⟩
    rintro r ⟨ι, inst, S, hs, hd, rfl⟩
    exact h ι inst S hs hd
  have testBound_squareSup {u : V → ℝ} (hu : ∃ C, TestBound u C) :
      TestBound u (squareSup u) := by
    intro ι inst S hs hd
    exact le_csSup (TestBound.bddAbove hu.choose_spec) ⟨ι, inst, S, hs, hd, rfl⟩
  have squareSup_nonneg {u : V → ℝ} (hu : ∃ C, TestBound u C) : 0 ≤ squareSup u :=
    TestBound.nonneg (testBound_squareSup hu)
  have rho_nonneg (u : V → ℝ) : 0 ≤ rho u := Real.sqrt_nonneg _
  have rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : rho u ^ 2 = squareSup u :=
    Real.sq_sqrt (squareSup_nonneg hu)
  have testBound_rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : TestBound u (rho u ^ 2) := by
    rw [rho_sq hu]
    exact testBound_squareSup hu
  have coordinate_le_rho {u : V → ℝ} (hu : ∃ C, TestBound u C) (v : V) :
      |u v| ≤ rho u := by
    have hh := TestBound.single (testBound_rho_sq hu) (isSegment_singleton v)
    simp only [segSum, sum_singleton] at hh
    exact (sq_le_sq₀ (abs_nonneg _) (rho_nonneg _)).mp (by simpa only [sq_abs] using hh)
  have l1size_nonneg [PartialOrder V] (u : V →₀ ℝ) : 0 ≤ l1size u :=
    sum_nonneg (fun vertex _ => abs_nonneg (u vertex))
  have finset_abs_sum_le_l1size [PartialOrder V] (u : V →₀ ℝ) (S : Finset V) :
      ∑ v ∈ S, |u v| ≤ l1size u := by
    have he : (∑ v ∈ S ∪ u.support, |u v|) = l1size u := by
      symm
      apply sum_subset subset_union_right
      intro v hv hn
      rw [Finsupp.notMem_support_iff.mp hn, abs_zero]
    rw [← he]
    exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun v hv hn => abs_nonneg _)
  have testBound_l1size (u : V →₀ ℝ) : TestBound u (l1size u ^ 2) := by
    intro ι inst S hS hd
    have habs : (∑ i, |segSum u (S i)|) ≤ l1size u := by
      calc
        (∑ i, |segSum u (S i)|) ≤ ∑ i, ∑ v ∈ S i, |u v| :=
          sum_le_sum fun i hi => abs_sum_le_sum_abs _ _
        _ = ∑ v ∈ univ.biUnion S, |u v| :=
          (sum_biUnion (by intro i hi j hj hij; exact hd hij)).symm
        _ ≤ l1size u := finset_abs_sum_le_l1size u _
    have hsq := sum_sq_le_sq_sum_of_nonneg
      (s := (univ : Finset ι)) (f := fun i => |segSum u (S i)|) (fun i hi => abs_nonneg _)
    simp only [sq_abs] at hsq
    have hnonneg : 0 ≤ ∑ i, |segSum u (S i)| := sum_nonneg (fun i hi => abs_nonneg _)
    nlinarith [l1size_nonneg u]
  have finsupp_has_testBound (u : V →₀ ℝ) : ∃ C, TestBound u C := ⟨_, testBound_l1size u⟩
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ) {
    norm_nonneg u := apply_nonneg (segmentSeminorm V) u.toFinsupp
    norm_triangle u v := map_add_le_add (segmentSeminorm V) u.toFinsupp v.toFinsupp
    norm_smul a u := map_smul_eq_mul (segmentSeminorm V) a u.toFinsupp
    norm_eq_zero_iff u := ⟨by
      intro h
      apply Finsupp.ext
      intro v
      have hh := coordinate_le_rho (finsupp_has_testBound u.toFinsupp) v
      change rho u.toFinsupp = 0 at h
      rw [h] at hh
      exact abs_nonpos_iff.mp hh, by
      rintro rfl
      exact map_zero (segmentSeminorm V)⟩ }
instance : NormedSpace ℝ (TestVector V) where
  norm_smul_le a u := le_of_eq (map_smul_eq_mul (segmentSeminorm V) a u.toFinsupp)

theorem norm_eq_rho (u : TestVector V) : ‖u‖ = rho u := rfl

/-- The norm on the finite-support space is the nonempty-segment supremum. -/
theorem norm_eq_source_sup [Nonempty V] (u : TestVector V) :
    ‖u‖ = sSup (sourceNormValues u) :=
  rho_eq_source_sup u.toFinsupp

 theorem norm_le_iff_testBound (u : TestVector V) {C : ℝ} (hC : 0 ≤ C) :
    ‖u‖ ≤ C ↔ TestBound u (C ^ 2) :=
  ⟨testBound_of_rho_le (finsupp_has_testBound u.toFinsupp), rho_le_of_testBound hC⟩

noncomputable def single (v : V) (a : ℝ) : TestVector V := Finsupp.single v a

omit [PartialOrder V] in
@[simp] theorem single_apply [PartialOrder V] (v : V) (a : ℝ) (w : V) :
    single v a w = if v = w then a else 0 := Finsupp.single_apply

 theorem norm_single (v : V) (a : ℝ) : ‖single v a‖ = |a| := by
  change rho (Finsupp.single v a) = |a|
  have hl : l1size (Finsupp.single v a) = |a| := by
    change (Finsupp.single v a).sum (fun _ x => |x|) = |a|
    simp
  apply le_antisymm
  · simpa only [hl] using rho_le_l1size (Finsupp.single v a)
  · simpa using coordinate_le_rho (finsupp_has_testBound (Finsupp.single v a)) v

/-- Coordinate evaluation is bounded by singleton segment tests. -/
noncomputable def eval (v : V) : TestVector V →L[ℝ] ℝ :=
  (show TestVector V →ₗ[ℝ] ℝ from
    { toFun := fun u => u v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).mkContinuous 1 (by
        intro u
        change |u v| ≤ 1 * rho u
        simpa only [one_mul]
          using coordinate_le_rho (finsupp_has_testBound u.toFinsupp) v)

@[simp] theorem eval_apply (v : V) (u : TestVector V) : eval v u = u v := rfl

 theorem eval_norm_le (v : V) : ‖eval v‖ ≤ 1 :=
  (eval v).opNorm_le_bound zero_le_one (fun u => by
    simpa only [eval_apply, Real.norm_eq_abs, one_mul, norm_eq_rho]
      using coordinate_le_rho (finsupp_has_testBound u.toFinsupp) v)

/-- Coordinate restriction, before the boundedness hypothesis is imposed. -/
noncomputable def cut (H : Set V) : TestVector V →ₗ[ℝ] TestVector V where
  toFun u := Finsupp.filter (· ∈ H) u.toFinsupp
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

omit [PartialOrder V] in
@[simp] theorem cut_apply [PartialOrder V] (H : Set V) (u : TestVector V) (v : V) :
    cut H u v = if v ∈ H then u v else 0 := Finsupp.filter_apply _ _ _

 theorem cut_supported (H : Set V) (u : TestVector V) : SupportedOn (cut H u) H := by
  intro v hv
  simp [hv]

 theorem cut_add_compl (H : Set V) (u : TestVector V) : cut H u + cut Hᶜ u = u := by
  ext v
  by_cases hv : v ∈ H <;> simp [hv]

 theorem cut_eq_self {H : Set V} {u : TestVector V} (hu : SupportedOn u H) : cut H u = u := by
  ext v
  by_cases hv : v ∈ H
  · simp [hv]
  · simp [hv, hu v hv]

 theorem norm_cut_le (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    ‖cut H u‖ ≤ ‖u‖ := by
  apply (norm_le_iff_testBound _ (norm_nonneg u)).mpr
  have hh := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp)).restrict H hH
  have he : H.indicator ⇑u = ⇑(cut H u) := by
    funext v
    by_cases hv : v ∈ H <;> simp [cut_apply, hv]
  rw [he] at hh
  exact hh

 theorem norm_cut_compl_le (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    ‖cut Hᶜ u‖ ≤ ‖u‖ := by
  apply (norm_le_iff_testBound _ (norm_nonneg u)).mpr
  have hh := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp)).restrict_compl H hH
  have he : Hᶜ.indicator ⇑u = ⇑(cut Hᶜ u) := by
    funext v
    by_cases hv : v ∈ H <;> simp [cut_apply, hv]
  rw [he] at hh
  exact hh

omit [PartialOrder V] in
@[simp] theorem sum_apply [PartialOrder V] {ι : Type} (S : Finset ι) (u : ι → TestVector V) (v : V) :
    (∑ i ∈ S, u i) v = ∑ i ∈ S, u i v := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [ha, ih]

 theorem cut_finite_eq_sum (H : Finset V) (u : TestVector V) :
    cut (H : Set V) u = ∑ v ∈ H, u v • single v 1 := by
  ext w
  simp only [cut_apply, Finset.mem_coe, sum_apply, smul_apply, single_apply,
    mul_ite, mul_one, mul_zero]
  simp

 theorem cut_eq_zero_of_compl {H : Set V} {u : TestVector V}
    (hu : SupportedOn u Hᶜ) : cut H u = 0 := by
  ext v
  by_cases hv : v ∈ H
  · simp [hv, hu v (by simpa using hv)]
  · simp [hv]

noncomputable def head (H : Set V) (hH : IsLowerSet H) : TestVector V →L[ℝ] TestVector V :=
  (cut H).mkContinuous 1 (by intro u; simpa only [one_mul] using norm_cut_le H hH u)

noncomputable def tail (H : Set V) (hH : IsLowerSet H) : TestVector V →L[ℝ] TestVector V :=
  (cut Hᶜ).mkContinuous 1 (by intro u; simpa only [one_mul] using norm_cut_compl_le H hH u)

@[simp] theorem head_apply (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    head H hH u = cut H u := rfl
@[simp] theorem tail_apply (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    tail H hH u = cut Hᶜ u := rfl

 theorem paired_correction (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (f k : TestVector V)
    (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hf₁ : ‖f‖ ≤ 1) (hk₁ : ‖k‖ ≤ 1) (s : ℝ) (hs : 0 < s) :
    ∃ c : TestVector V, SupportedOn c Hᶜ ∧ ‖c‖ ≤ 1 ∧
      ‖f + s • (c + k)‖ ≤ Real.sqrt (1 + 12 * s ^ 2) ∧
      ‖f + s • (c - k)‖ ≤ Real.sqrt (1 + 12 * s ^ 2) := by
  have hf' : TestBound f 1 := by simpa using (norm_le_iff_testBound f zero_le_one).mp hf₁
  have hk' : TestBound k 1 := by simpa using (norm_le_iff_testBound k zero_le_one).mp hk₁
  obtain ⟨c,hcH,hc,hcp,hcm⟩ := finsupp_paired_correction hF hAnc H hH
    f.toFinsupp k.toFinsupp hf hk hf' hk' s hs
  refine ⟨c,hcH, ?_, ?_, ?_⟩
  · exact (norm_le_iff_testBound _ zero_le_one).mpr (by
      change TestBound c (1 ^ 2); simpa only [one_pow] using hc)
  · apply (norm_le_iff_testBound _ (Real.sqrt_nonneg _)).mpr
    rw [Real.sq_sqrt (by positivity)]
    exact hcp
  · apply (norm_le_iff_testBound _ (Real.sqrt_nonneg _)).mpr
    rw [Real.sq_sqrt (by positivity)]
    exact hcm

end TestVector

/-- J(T), completion of the finite-support disjoint-segment norm. -/
abbrev J (V : Type) [PartialOrder V] := UniformSpace.Completion (TestVector V)

/-- The full continuous dual, used for the finite-height forest example. -/
abbrev FullDual (V : Type) [PartialOrder V] := StrongDual ℝ (J V)

end

end ForestSpace

end OAI
