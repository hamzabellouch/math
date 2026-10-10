import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.ComplexMollify

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

abbrev SpinMode := Fin 2 × (Fin 3 → ℕ)

theorem spin_lattice_count (s : Finset SpinMode) {r : ℝ}
    (hr : 0 ≤ r) (hs : ∀ a ∈ s, latticeRadius a.2 ≤ r) :
    (s.card : ℝ) ≤ (Real.pi / 3) * (r + Real.sqrt 3)^3 := by
  classical
  let t := s.image Prod.snd
  have H := spin_two_lattice_count t hr (by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact hs a ha)
  have ht : s ⊆ (Finset.univ : Finset (Fin 2)) ×ˢ t := by
    intro a ha
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  have hc : s.card ≤ 2 * t.card := by simpa using Finset.card_le_card ht
  have hcR : (s.card : ℝ) ≤ 2 * (t.card : ℝ) := by exact_mod_cast hc
  exact hcR.trans H

lemma latticeRadius_nonneg (q : Fin 3 → ℕ) : 0 ≤ latticeRadius q := norm_nonneg _

theorem ordered_lattice_radius_lower {n : ℕ} (a : Fin n → SpinMode)
    (ha : Function.Injective a) (hm : Monotone (fun i => latticeRadius (a i).2))
    (i : Fin n) :
    (3 * ((i.val + 1 : ℕ) : ℝ) / Real.pi) ^ (1/3 : ℝ) ≤
      latticeRadius (a i).2 + Real.sqrt 3 := by
  classical
  let s := (Finset.Iic i).image a
  have hc : s.card = i.val + 1 := by
    rw [Finset.card_image_of_injective _ ha]
    exact Fin.card_Iic i
  have h := spin_lattice_count s (latticeRadius_nonneg _) (by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    exact hm (Finset.mem_Iic.mp hj))
  rw [hc] at h
  have hx : 0 ≤ 3 * ((i.val + 1 : ℕ) : ℝ) / Real.pi := by positivity
  have hy : 0 ≤ latticeRadius (a i).2 + Real.sqrt 3 :=
    add_nonneg (latticeRadius_nonneg _) (Real.sqrt_nonneg _)
  rw [show (1/3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
    Real.rpow_inv_le_iff_of_pos hx hy (by norm_num)]
  norm_num only [Real.rpow_ofNat]
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith

lemma sum_two_thirds_lower (n : ℕ) :
    (3/5 : ℝ) * (n : ℝ) ^ (5/3 : ℝ) ≤
      ∑ i ∈ Finset.range n, ((i+1 : ℕ) : ℝ) ^ (2/3 : ℝ) := by
  have hm : MonotoneOn (fun x : ℝ => x ^ (2/3 : ℝ)) (Set.Icc 0 (0+n)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow hx.1 hxy (by norm_num)
  have h := hm.integral_le_sum
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 2/3))] at h
  norm_num at h ⊢
  convert h using 1
  ring

lemma sum_one_third_upper (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i+1 : ℕ) : ℝ) ^ (1/3 : ℝ)) ≤
      (n : ℝ) ^ (4/3 : ℝ) := by
  have H : (∑ i ∈ Finset.range n, ((i+1 : ℕ) : ℝ) ^ (1/3 : ℝ)) ≤
      ∑ _ ∈ Finset.range n, (n : ℝ) ^ (1/3 : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    exact_mod_cast (show i+1 ≤ n from Nat.succ_le_of_lt (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at H
  convert H using 1
  rw [show (4/3 : ℝ) = 1 + 1/3 by norm_num,
    Real.rpow_add' (Nat.cast_nonneg n) (by norm_num : (1 : ℝ)+1/3 ≠ 0), Real.rpow_one]

lemma square_lower_of_shift {r t c : ℝ} (_hr : 0 ≤ r) (ht : 0 ≤ t) (_hc : 0 ≤ c)
    (h : t ≤ r+c) : t^2 - 2*c*t ≤ r^2 := by
  by_cases htc : t ≤ c
  · nlinarith [mul_nonneg (sub_nonneg.mpr htc) ht, sq_nonneg r]
  · have h2 := pow_le_pow_left₀ (sub_nonneg.mpr (le_of_not_ge htc))
      (show t-c ≤ r by linarith) 2
    nlinarith [sq_nonneg c]

lemma finite_sort_values {n : ℕ} (v : Fin n → ℝ) :
    ∃ e : Equiv.Perm (Fin n), Monotone (fun i => v (e i)) := by
  classical
  let key : Fin n → ℝ ×ₗ Fin n := fun i => toLex (v i, i)
  have hk : Function.Injective key := by
    intro i j h
    exact congrArg (fun z => (ofLex z).2) h
  let s := Finset.univ.image key
  have hs : s.card = n := by
    simp only [s, Finset.card_image_of_injective _ hk, Finset.card_univ, Fintype.card_fin]
  let b := s.orderEmbOfFin hs
  have hb (i : Fin n) : key (ofLex (b i)).2 = b i := by
    have hi := s.orderEmbOfFin_mem hs i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    rw [← hj]
    rfl
  let e : Fin n → Fin n := fun i => (ofLex (b i)).2
  have he : Function.Injective e := by
    intro i j hij
    apply b.injective
    rw [← hb i, ← hb j]
    exact congrArg key hij
  let E : Equiv.Perm (Fin n) := Equiv.ofBijective e
    ⟨he, (Finite.injective_iff_surjective).mp he⟩
  refine ⟨E, ?_⟩
  intro i j hij
  have H := b.monotone hij
  have hi : v (E i) = (ofLex (b i)).1 := by
    exact congrArg (fun z => (ofLex z).1) (hb i)
  have hj : v (E j) = (ofLex (b j)).1 := by
    exact congrArg (fun z => (ofLex z).1) (hb j)
  change v (E i) ≤ v (E j)
  rw [hi, hj]
  rcases Prod.Lex.le_iff.mp H with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

noncomputable def neumannLeading : ℝ := (3/5 : ℝ) * (3/Real.pi) ^ (2/3 : ℝ)
noncomputable def neumannBoundary : ℝ := 2 * Real.sqrt 3 * (3/Real.pi) ^ (1/3 : ℝ)

theorem neumann_radii_sum_lower {n : ℕ} (a : Fin n → SpinMode)
    (ha : Function.Injective a) :
    neumannLeading * (n : ℝ) ^ (5/3 : ℝ) -
      neumannBoundary * (n : ℝ) ^ (4/3 : ℝ) ≤
      ∑ i, (latticeRadius (a i).2)^2 := by
  classical
  obtain ⟨e, he⟩ := finite_sort_values (fun i => latticeRadius (a i).2)
  let A : ℝ := (3/Real.pi) ^ (1/3 : ℝ)
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hAi : A^2 = (3/Real.pi) ^ (2/3 : ℝ) := by
    dsimp only [A]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hl (i : Fin n) :
      A^2 * (((i.val+1 : ℕ) : ℝ) ^ (2/3 : ℝ)) -
       (2 * Real.sqrt 3 * A) * (((i.val+1 : ℕ) : ℝ) ^ (1/3 : ℝ)) ≤
        (latticeRadius (a (e i)).2)^2 := by
    have h := ordered_lattice_radius_lower (fun i => a (e i)) (ha.comp e.injective) he i
    have hx : (3 * ((i.val+1 : ℕ) : ℝ) / Real.pi) ^ (1/3 : ℝ) =
        A * (((i.val+1 : ℕ) : ℝ) ^ (1/3 : ℝ)) := by
      rw [show 3 * ((i.val+1 : ℕ) : ℝ) / Real.pi =
        (3/Real.pi) * ((i.val+1 : ℕ) : ℝ) by ring,
        Real.mul_rpow (by positivity) (by positivity)]
    rw [hx] at h
    have H := square_lower_of_shift (latticeRadius_nonneg _) (mul_nonneg hA (Real.rpow_nonneg (by positivity) _))
      (Real.sqrt_nonneg 3) h
    rw [mul_pow] at H
    have hp : ((((i.val+1 : ℕ) : ℝ) ^ (1/3 : ℝ)))^2 =
        (((i.val+1 : ℕ) : ℝ) ^ (2/3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hp] at H
    nlinarith
  have H := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at H
  have h2 : (3/5 : ℝ) * (n : ℝ) ^ (5/3 : ℝ) ≤
      ∑ i : Fin n, (((i.val+1 : ℕ) : ℝ) ^ (2/3 : ℝ)) := by
    simpa only [Finset.sum_range] using sum_two_thirds_lower n
  have h1 : (∑ i : Fin n, (((i.val+1 : ℕ) : ℝ) ^ (1/3 : ℝ))) ≤
      (n : ℝ) ^ (4/3 : ℝ) := by
    simpa only [Finset.sum_range] using sum_one_third_upper n
  have H2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg A)
  have H1 := mul_le_mul_of_nonneg_left h1
    (show 0 ≤ 2 * Real.sqrt 3 * A by positivity)
  have hs : (∑ i, (latticeRadius (a (e i)).2)^2) =
      ∑ i, (latticeRadius (a i).2)^2 := Equiv.sum_comp e (fun i => (latticeRadius (a i).2)^2)
  rw [hs] at H
  unfold neumannLeading neumannBoundary
  rw [← hAi]
  change (3/5 : ℝ) * A^2 * (n : ℝ) ^ (5/3 : ℝ) -
    (2 * Real.sqrt 3 * A) * (n : ℝ) ^ (4/3 : ℝ) ≤ _
  nlinarith

noncomputable def thomasFermiCoefficient : ℝ :=
  (3/10 : ℝ) * (3*Real.pi^2) ^ (2/3 : ℝ)

lemma neumann_coefficient_exact :
    (Real.pi^2/2) * neumannLeading = thomasFermiCoefficient := by
  unfold neumannLeading thomasFermiCoefficient
  rw [Real.div_rpow (by norm_num) Real.pi_pos.le,
    Real.mul_rpow (by norm_num) (sq_nonneg _)]
  have hp : (Real.pi^2) ^ (2/3 : ℝ) = Real.pi^2 / Real.pi ^ (2/3 : ℝ) := by
    rw [← Real.rpow_natCast_mul Real.pi_pos.le 2 (2/3 : ℝ)]
    rw [← Real.rpow_two, ← Real.rpow_sub Real.pi_pos]
    norm_num
  rw [hp]
  ring

theorem neumann_kinetic_sum_lower {n : ℕ} (a : Fin n → SpinMode)
    (ha : Function.Injective a) {b : ℝ} (_hb : 0 < b) :
    (b⁻¹)^2 * (thomasFermiCoefficient * (n : ℝ) ^ (5/3 : ℝ) -
      ((Real.pi^2/2)*neumannBoundary) * (n : ℝ) ^ (4/3 : ℝ)) ≤
      ∑ i, (Real.pi^2/(2*b^2)) * (latticeRadius (a i).2)^2 := by
  have H := mul_le_mul_of_nonneg_left (neumann_radii_sum_lower a ha)
    (show 0 ≤ Real.pi^2/(2*b^2) by positivity)
  rw [← Finset.mul_sum]
  have he : (b⁻¹)^2 * (thomasFermiCoefficient * (n : ℝ) ^ (5/3 : ℝ) -
      ((Real.pi^2/2)*neumannBoundary) * (n : ℝ) ^ (4/3 : ℝ)) =
      (Real.pi^2/(2*b^2)) * (neumannLeading * (n : ℝ) ^ (5/3 : ℝ) -
        neumannBoundary * (n : ℝ) ^ (4/3 : ℝ)) := by
    rw [← neumann_coefficient_exact]
    field_simp
  rw [he]
  exact H

section IndexBridge
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def finiteCubeMeasure (b : ℝ) (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Ioc 0 b))

noncomputable def finiteCubeMode (b : ℝ) (q : I → ℕ) (x : I → ℝ) : ℂ :=
  ∏ i, neumannMode b (q i) (x i)

noncomputable def reindexCube (e : I ≃ J) : (I → ℝ) ≃ᵐ (J → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma reindexCube_apply (e : I ≃ J) (x : I → ℝ) (j : J) :
    reindexCube e x j = x (e.symm j) := by
  simpa only [reindexCube, e.apply_symm_apply] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : J => ℝ) e x (e.symm j)

omit [DecidableEq I] [DecidableEq J] in
lemma reindexCube_measurePreserving (b : ℝ) (e : I ≃ J) :
    MeasurePreserving (reindexCube e) (finiteCubeMeasure b I) (finiteCubeMeasure b J) := by
  exact measurePreserving_piCongrLeft (fun _ : J => volume.restrict (Ioc 0 b)) e

omit [DecidableEq I] [DecidableEq J] in
lemma finiteCubeMode_reindex (b : ℝ) (e : I ≃ J) (q : I → ℕ) (x : I → ℝ) :
    finiteCubeMode b (q ∘ e.symm) (reindexCube e x) = finiteCubeMode b q x := by
  simpa only [finiteCubeMode, Function.comp_apply, reindexCube_apply] using
    Equiv.prod_comp e.symm (fun i => neumannMode b (q i) (x i))

omit [DecidableEq I] [DecidableEq J] in
lemma euclidean_reindex_toLp (e : I ≃ J) (x : J → ℝ) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 x) =
      WithLp.toLp 2 (reindexCube e.symm x) := by
  ext i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', reindexCube_apply]

omit [DecidableEq I] [DecidableEq J] in
lemma euclidean_reindex_toLp_cancel (e : I ≃ J) (x : I → ℝ) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 (reindexCube e x)) =
      WithLp.toLp 2 x := by
  ext i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', reindexCube_apply]

omit [DecidableEq I] [DecidableEq J] in
lemma finiteCube_integral_reindex (b : ℝ) (e : I ≃ J)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ I → E) :
    (∫ y, f (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 y))
      ∂(finiteCubeMeasure b J)) =
      ∫ x, f (WithLp.toLp 2 x) ∂(finiteCubeMeasure b I) := by
  rw [← (reindexCube_measurePreserving b e).integral_comp'
    (fun y => f (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 y)))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by dsimp only; rw [euclidean_reindex_toLp_cancel])

omit [DecidableEq I] [DecidableEq J] in
lemma finiteCube_coefficient_reindex (b : ℝ) (e : I ≃ J)
    (u : EuclideanSpace ℝ I → ℂ) (q : I → ℕ) :
    (∫ y, star (finiteCubeMode b (q ∘ e.symm) y) *
      u (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 y))
      ∂(finiteCubeMeasure b J)) =
      ∫ x, star (finiteCubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(finiteCubeMeasure b I) := by
  rw [← (reindexCube_measurePreserving b e).integral_comp'
    (fun y => star (finiteCubeMode b (q ∘ e.symm) y) *
      u (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 y)))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by dsimp only; rw [finiteCubeMode_reindex, euclidean_reindex_toLp_cancel])

lemma euclidean_weak_reindex (e : I ≃ J) {u : EuclideanSpace ℝ I → ℂ}
    {g : I → EuclideanSpace ℝ I → ℂ}
    (hw : ∀ i (φ : EuclideanSpace ℝ I → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g i x * (φ x : ℂ))) (j : J)
    (φ : EuclideanSpace ℝ J → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, u (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm x) *
      (fderiv ℝ φ x (EuclideanSpace.single j 1) : ℂ)) =
      -(∫ x, g (e.symm j) (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm x) * (φ x : ℂ)) := by
  classical
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ L) :=
    hφ.comp L.contDiff
  have hc : HasCompactSupport (φ ∘ L) := hφc.comp_homeomorph L.toHomeomorph
  have H := hw (e.symm j) (φ ∘ L) hcomp hc
  have hd (x : EuclideanSpace ℝ I) :
      fderiv ℝ (φ ∘ L) x (EuclideanSpace.single (e.symm j) 1) =
      fderiv ℝ φ (L x) (EuclideanSpace.single j 1) := by
    rw [fderiv_comp x (hφ.differentiable (by simp) _) L.differentiableAt]
    rw [L.fderiv]
    change fderiv ℝ φ (L x) (L (EuclideanSpace.single (e.symm j) 1)) = _
    have hs : L (EuclideanSpace.single (e.symm j) 1) = EuclideanSpace.single j 1 := by
      simp [L, EuclideanSpace.single, LinearIsometryEquiv.piLpCongrLeft_single]
    rw [hs]
  simp_rw [hd] at H
  have hp : MeasurePreserving L.symm.toHomeomorph.toMeasurableEquiv volume volume :=
    L.symm.measurePreserving
  rw [← hp.integral_comp' (fun x => u x * (fderiv ℝ φ (L x) (EuclideanSpace.single j 1) : ℂ)),
      ← hp.integral_comp' (fun x => g (e.symm j) x * ((φ ∘ L) x : ℂ))] at H
  change (∫ x, u (L.symm x) *
    (fderiv ℝ φ (L (L.symm x)) (EuclideanSpace.single j 1) : ℂ)) =
    -(∫ x, g (e.symm j) (L.symm x) * (φ (L (L.symm x)) : ℂ)) at H
  simp_rw [L.apply_symm_apply] at H
  simpa only [L, LinearIsometryEquiv.piLpCongrLeft_symm] using H

theorem finiteCube_weak_spectral_lower {d : ℕ} (e : I ≃ Fin (d+1))
    {b : ℝ} (hb : 0 < b)
    {u : EuclideanSpace ℝ I → ℂ} {g : I → EuclideanSpace ℝ I → ℂ}
    (hu : MemLp u 2) (hg : ∀ i, MemLp (g i) 2)
    (hw : ∀ i (φ : EuclideanSpace ℝ I → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g i x * (φ x : ℂ))) (s : Finset (I → ℕ)) :
    ∑ q ∈ s, ((∑ i, ((q i : ℝ) * Real.pi / b)^2) *
      ‖∫ x, star (finiteCubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(finiteCubeMeasure b I)‖^2) ≤
      ∑ i, ∫ x, ‖g i (WithLp.toLp 2 x)‖^2 ∂(finiteCubeMeasure b I) := by
  classical
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm
  let p : (I → ℕ) → (Fin (d+1) → ℕ) := fun q => q ∘ e.symm
  have hp : Function.Injective p := by
    intro q r h
    funext i
    simpa only [p, Function.comp_apply, e.symm_apply_apply] using congrFun h (e i)
  have H := cube_weak_spectral_lower hb
    (hu.comp_measurePreserving L.measurePreserving)
    (fun j => (hg (e.symm j)).comp_measurePreserving L.measurePreserving)
    (euclidean_weak_reindex e hw) (s.image p)
  rw [Finset.sum_image hp.injOn] at H
  have HC (q : I → ℕ) :
      (∫ x, star (cubeMode b (p q) x) * (u ∘ L) (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))) =
      ∫ x, star (finiteCubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(finiteCubeMeasure b I) := finiteCube_coefficient_reindex b e u q
  simp_rw [HC] at H
  have HS (q : I → ℕ) :
      (∑ j : Fin (d+1), (((p q) j : ℝ) * Real.pi / b)^2) =
      ∑ i, ((q i : ℝ) * Real.pi / b)^2 :=
    Equiv.sum_comp e.symm (fun i => ((q i : ℝ) * Real.pi / b)^2)
  simp_rw [HS] at H
  have HG (j : Fin (d+1)) :
      (∫ x, ‖((g (e.symm j)) ∘ L) (WithLp.toLp 2 x)‖^2 ∂(cubeMeasure b (d+1))) =
      ∫ x, ‖g (e.symm j) (WithLp.toLp 2 x)‖^2 ∂(finiteCubeMeasure b I) :=
    finiteCube_integral_reindex b e (fun x => ‖g (e.symm j) x‖^2)
  simp_rw [HG] at H
  rw [Equiv.sum_comp e.symm (fun i => ∫ x, ‖g i (WithLp.toLp 2 x)‖^2 ∂(finiteCubeMeasure b I))] at H
  exact H

end IndexBridge

noncomputable def spinDelta (s t : Fin 2) : ℂ := if t = s then 1 else 0

lemma spinDelta_memLp (s : Fin 2) : MemLp (spinDelta s) 2 Measure.count := by
  apply MemLp.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun t => by simp [spinDelta]; split_ifs <;> norm_num)

lemma spinDelta_inner (s t : Fin 2) :
    (∫ q, star (spinDelta s q) * spinDelta t q ∂Measure.count) =
      if s = t then (1 : ℂ) else 0 := by
  classical
  simp [integral_count, spinDelta, eq_comm]

lemma spinDelta_complete : CompleteOrbitals Measure.count spinDelta := by
  intro f _ hz
  apply ae_of_all
  intro s
  have H := hz s
  simpa [integral_count, spinDelta] using H

lemma cubeMode_complete {b : ℝ} (hb : 0 < b) (d : ℕ) :
    CompleteOrbitals (cubeMeasure b d) (cubeMode b) :=
  completeOrbitals_finPi (neumannMode b) (neumannMode_memLp b) (neumannModes_complete hb) d

noncomputable def spinCubeMeasure (b : ℝ) : Measure (Fin 2 × (Fin 3 → ℝ)) :=
  Measure.count.prod (cubeMeasure b 3)

noncomputable def spinCubeMode (b : ℝ) (a : SpinMode) (x : Fin 2 × (Fin 3 → ℝ)) : ℂ :=
  spinDelta a.1 x.1 * cubeMode b a.2 x.2

lemma cubeMode_memLp (b : ℝ) {d : ℕ} (q : Fin d → ℕ) :
    MemLp (cubeMode b q) 2 (cubeMeasure b d) :=
  scalarTensor_memLp (neumannMode b) (neumannMode_memLp b) q

lemma spinCubeMode_memLp (b : ℝ) (a : SpinMode) :
    MemLp (spinCubeMode b a) 2 (spinCubeMeasure b) :=
  tensorPair_memLp (spinDelta_memLp a.1) (cubeMode_memLp b a.2)

lemma spinCubeMode_complete {b : ℝ} (hb : 0 < b) :
    CompleteOrbitals (spinCubeMeasure b) (spinCubeMode b) :=
  completeOrbitals_tensorPair (fun q => cubeMode_memLp b q) spinDelta_memLp
    (cubeMode_complete hb 3) spinDelta_complete

end Coulomb
end
end

end OAI
