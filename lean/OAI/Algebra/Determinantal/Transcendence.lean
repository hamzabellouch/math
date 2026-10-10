import OAI.Algebra.Determinantal.HomogeneousPadding

namespace OAI

namespace PermanentBorder.SliceParameters

universe u
open MvPolynomial
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

lemma aeval_mem_field {v : ℕ} (F : IntermediateField K L)
    (x : Fin v → L) (hx : ∀ i, x i ∈ F) (p : MvPolynomial (Fin v) K) :
    aeval x p ∈ F := by
  have h : (aeval (R := K) x).range ≤ F.toSubalgebra := by
    rw [aeval_range, Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact hx i
  exact h ⟨p, rfl⟩

lemma pivot_mem {ι : Type*} [Fintype ι] (F : IntermediateField K L)
    (a b : ι → L) (j : ι) (ha : ∀ i, a i ∈ F) (hj : a j ≠ 0)
    (hb : ∀ i, i ≠ j → b i ∈ F) (hs : (∑ i, a i * b i) ∈ F) :
    b j ∈ F := by
  classical
  have he : (∑ i ∈ Finset.univ.erase j, a i * b i) ∈ F := by
    apply F.sum_mem
    intro i hi
    exact F.mul_mem (ha i) (hb i (Finset.mem_erase.mp hi).1)
  have hp : a j * b j ∈ F := by
    have hh := F.sub_mem hs he
    convert hh using 1
    symm
    exact sub_eq_of_eq_add (by
      simpa only [add_comm] using (Finset.sum_erase_add Finset.univ
        (fun i => a i * b i) (Finset.mem_univ j)).symm)
  simpa [mul_div_cancel_left₀, hj] using F.div_mem hp (ha j)

theorem normalized_avoidance {v d n : ℕ}
    (I : Ideal (MvPolynomial (Fin v) K))
    (hdim : ringKrullDim (MvPolynomial (Fin v) K ⧸ I) ≤ n)
    (hn : n + d < v)
    (H : Fin v × Fin (d+1) → L) (hH : AlgebraicIndependent K H)
    (x : Fin v → L) (y : Fin (d+1) → L) (j : Fin (d+1)) (hyj : y j = 1)
    (hxy : ∀ i, ∑ c, y c * H (i,c) = x i)
    (hx : ∀ p ∈ I, aeval x p = 0) : False := by
  classical
  let C := {c : Fin (d+1) // c ≠ j}
  let κ := C ⊕ (Fin v × C)
  let z : κ → L := Sum.elim (fun c => y c.val) (fun ic => H (ic.1,ic.2.val))
  let F := IntermediateField.adjoin K (Set.range x)
  have hF : Algebra.trdeg K F ≤ (n : Cardinal) :=
    AlgebraicDimension.point_field_trdeg_le I n hdim x hx
  obtain ⟨E, hFE, hz, ht⟩ := add_parameters F n hF z
  have hxE (i : Fin v) : x i ∈ E :=
    hFE (IntermediateField.subset_adjoin K _ (Set.mem_range_self i))
  have hyE (c : Fin (d+1)) : y c ∈ E := by
    by_cases hc : c = j
    · rw [hc, hyj]
      exact E.one_mem
    · exact hz (Sum.inl ⟨c,hc⟩)
  have hHE (ic : Fin v × Fin (d+1)) : H ic ∈ E := by
    obtain ⟨i,c⟩ := ic
    by_cases hc : c = j
    · subst c
      apply pivot_mem E y (fun c => H (i,c)) j hyE
      · simp [hyj]
      · intro a ha
        exact hz (Sum.inr (i,⟨a,ha⟩))
      · rw [hxy]
        exact hxE i
    · exact hz (Sum.inr (i,⟨c,hc⟩))
  have hC : Fintype.card C = d := by
    simp [C, Fintype.card_subtype_compl]
  have hκ : Fintype.card κ = d + v*d := by
    simp [κ, hC]
  have hc := independent_card_le H hH E hHE _ ht
  simp only [Fintype.card_prod, Fintype.card_fin, hκ] at hc
  nlinarith

end PermanentBorder.SliceParameters

namespace PermanentBorder.ParameterBounds
open Algebra MvPolynomial
universe u
variable {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]

theorem trdeg_lt_of_relation {n : ℕ} (x : Fin n → A)
    [Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A]
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (hx : aeval x p = 0) :
    Algebra.trdeg K A < (n : Cardinal) := by
  by_contra! ht
  have ht' : Cardinal.lift.{u} (Cardinal.mk (Fin n)) ≤
      Cardinal.lift.{0} (Algebra.trdeg K A) := by simpa using ht
  have hi := (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K x ht').1
  apply hp
  exact hi (by simpa using hx)

theorem trdeg_le_of_generators {n : ℕ} (x : Fin n → A)
    [Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A] :
    Algebra.trdeg K A ≤ (n : Cardinal) := by
  calc
    Algebra.trdeg K A ≤ Cardinal.mk (Set.range x) :=
      Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range x)
    _ ≤ Cardinal.lift.{u} (Cardinal.mk (Fin n)) := by
      simpa using (Cardinal.mk_range_le_lift (f := x))
    _ = n := by simp

theorem adjoin_trdeg_lt_of_relation {n : ℕ} (x : Fin n → A)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (hx : aeval x p = 0) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range x)) < (n : Cardinal) := by
  let B := Algebra.adjoin K (Set.range x)
  let y : Fin n → B := fun i => ⟨x i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have htop : Algebra.adjoin K (Set.range y) = ⊤ := by
    apply Subalgebra.map_injective (show Function.Injective B.val from Subtype.val_injective)
    rw [AlgHom.map_adjoin, Algebra.map_top, B.range_val, ← Set.range_comp]
    rfl
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range y)) B := by
    constructor
    intro b
    have hb : b ∈ Algebra.adjoin K (Set.range y) := by rw [htop]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin K (Set.range y)) ⟨b, hb⟩
  apply trdeg_lt_of_relation y p hp
  apply (show Function.Injective B.val from Subtype.val_injective)
  rw [map_zero, MvPolynomial.comp_aeval_apply]
  exact hx

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_lt_of_relation {L : Type u} [Field L] [Algebra K L]
    {n : ℕ} (x : Fin n → L) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) < (n : Cardinal) := by
  rw [← trdeg_add_eq K (Algebra.adjoin K (Set.range x)),
    trdeg_eq_zero (R := Algebra.adjoin K (Set.range x)), add_zero]
  exact adjoin_trdeg_lt_of_relation x p hp hx

end PermanentBorder.ParameterBounds

namespace PermanentBorder.SliceParameters

universe u
open MvPolynomial
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem normalized_tangency_impossible {v d : ℕ}
    (f : MvPolynomial (Fin (v+1)) K) (hf : f ≠ 0)
    (H : Fin (v+1) × Fin (d+1) → L) (hH : AlgebraicIndependent K H)
    (x : Fin (v+1) → L) (y : Fin (d+1) → L) (j : Fin (d+1)) (hyj : y j = 1)
    (hxy : ∀ i, ∑ c, y c * H (i,c) = x i)
    (hfx : aeval x f = 0)
    (i₀ : Fin (v+1)) (hp : aeval x (pderiv i₀ f) ≠ 0)
    (horth : ∀ c, ∑ i, aeval x (pderiv i f) * H (i,c) = 0) : False := by
  classical
  let C := {c : Fin (d+1) // c ≠ j}
  let R := {i : Fin (v+1) // i ≠ i₀}
  let κ := C ⊕ (R × C)
  let z : κ → L := Sum.elim (fun c => y c.val) (fun ic => H (ic.1.val,ic.2.val))
  let F := IntermediateField.adjoin K (Set.range x)
  have hF : Algebra.trdeg K F ≤ (v : Cardinal) := by
    apply Cardinal.lt_natCast_add_one_iff.mp
    simpa only [Nat.cast_add, Nat.cast_one] using
      ParameterBounds.field_adjoin_trdeg_lt_of_relation x f hf hfx
  obtain ⟨E, hFE, hz, ht⟩ := add_parameters F v hF z
  have hxE (i : Fin (v+1)) : x i ∈ E :=
    hFE (IntermediateField.subset_adjoin K _ (Set.mem_range_self i))
  have hyE (c : Fin (d+1)) : y c ∈ E := by
    by_cases hc : c = j
    · rw [hc, hyj]
      exact E.one_mem
    · exact hz (Sum.inl ⟨c,hc⟩)
  have hpE (i : Fin (v+1)) : aeval x (pderiv i f) ∈ E :=
    aeval_mem_field E x hxE _
  have hHother (i : Fin (v+1)) (c : Fin (d+1)) (hc : c ≠ j) : H (i,c) ∈ E := by
    by_cases hi : i = i₀
    · subst i
      apply pivot_mem E (fun i => aeval x (pderiv i f)) (fun i => H (i,c)) i₀ hpE hp
      · intro a ha
        exact hz (Sum.inr (⟨a,ha⟩,⟨c,hc⟩))
      · rw [horth]
        exact E.zero_mem
    · exact hz (Sum.inr (⟨i,hi⟩,⟨c,hc⟩))
  have hHE (ic : Fin (v+1) × Fin (d+1)) : H ic ∈ E := by
    obtain ⟨i,c⟩ := ic
    by_cases hc : c = j
    · subst c
      apply pivot_mem E y (fun c => H (i,c)) j hyE
      · simp [hyj]
      · exact hHother i
      · rw [hxy]
        exact hxE i
    · exact hHother i c hc
  have hC : Fintype.card C = d := by
    simp [C, Fintype.card_subtype_compl]
  have hR : Fintype.card R = v := by
    simp [R, Fintype.card_subtype_compl]
  have hκ : Fintype.card κ = d + v*d := by
    simp [κ, hC, hR]
  have hc := independent_card_le H hH E hHE _ ht
  simp only [Fintype.card_prod, Fintype.card_fin, hκ] at hc
  nlinarith

theorem generic_normalized_slice {v d n : ℕ}
    (f : MvPolynomial (Fin (v+1)) K) (hf : f ≠ 0)
    (hdim : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i f))) ≤ n)
    (hn : n + d < v+1)
    (H : Fin (v+1) × Fin (d+1) → L) (hH : AlgebraicIndependent K H)
    (y : Fin (d+1) → L) (j : Fin (d+1)) (hyj : y j = 1) :
    let x := fun i => ∑ c, y c * H (i,c)
    aeval x f = 0 → ¬ ∀ c, ∑ i, aeval x (pderiv i f) * H (i,c) = 0 := by
  intro x hf0 ho
  by_cases hp : ∀ i, aeval x (pderiv i f) = 0
  · apply normalized_avoidance (Ideal.span (Set.range (fun i => pderiv i f)))
      hdim hn H hH x y j hyj (fun _ => rfl)
    have hker : Ideal.span (Set.range (fun i => pderiv i f)) ≤
        RingHom.ker (aeval x) := by
      rw [Ideal.span_le, Set.range_subset_iff]
      exact hp
    exact fun p h => hker h
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hp
    exact normalized_tangency_impossible f hf H hH x y j hyj (fun _ => rfl) hf0 i₀ hi₀ ho

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters

universe u
open MvPolynomial
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem generic_homogeneous_slice {v d n r : ℕ}
    (f : MvPolynomial (Fin (v+1)) K) (hf : f ≠ 0) (hhom : f.IsHomogeneous r)
    (hdim : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i f))) ≤ n)
    (hn : n + d < v+1)
    (H : Fin (v+1) × Fin (d+1) → L) (hH : AlgebraicIndependent K H)
    (y : Fin (d+1) → L)
    (hzero : aeval (fun i => ∑ c, y c * H (i,c)) f = 0)
    (htangent : ∀ c, ∑ i,
      aeval (fun i => ∑ c, y c * H (i,c)) (pderiv i f) * H (i,c) = 0) : y = 0 := by
  classical
  by_contra hy
  obtain ⟨j,hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    apply hy
    ext j
    exact not_not.mp (not_exists.mp h j)
  let a := (y j)⁻¹
  let y' := fun c => a * y c
  have hj' : y' j = 1 := inv_mul_cancel₀ hj
  have hscale : (fun i => ∑ c, y' c * H (i,c)) =
      (fun i => a * (∑ c, y c * H (i,c))) := by
    ext i
    simp [y', Finset.mul_sum, mul_assoc]
  apply generic_normalized_slice f hf hdim hn H hH y' j hj'
  · rw [hscale, homogeneous_aeval_scale hhom, hzero, mul_zero]
  · intro c
    rw [hscale]
    simp_rw [homogeneous_aeval_scale hhom.pderiv, mul_assoc, ← Finset.mul_sum]
    rw [htangent c, mul_zero]

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
variable {K α β : Type*} [CommRing K] [Fintype β]

noncomputable def sectionForm (H : α × β → K) (i : α) : MvPolynomial β K :=
  ∑ c, C (H (i,c)) * X c

noncomputable def linearSection (H : α × β → K) :
    MvPolynomial α K →ₐ[K] MvPolynomial β K := aeval (sectionForm H)

lemma sectionForm_homogeneous (H : α × β → K) (i : α) :
    (sectionForm H i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro c _
  exact isHomogeneous_C_mul_X _ _

lemma linearSection_homogeneous (H : α × β → K) {f : MvPolynomial α K} {r : ℕ}
    (hf : f.IsHomogeneous r) : (linearSection H f).IsHomogeneous r := by
  simpa only [one_mul, linearSection] using hf.aeval (sectionForm H) (sectionForm_homogeneous H)

@[simp] lemma eval_sectionForm (H : α × β → K) (y : β → K) (i : α) :
    eval y (sectionForm H i) = ∑ c, y c * H (i,c) := by
  simp [sectionForm, mul_comm]

@[simp] lemma eval_linearSection (H : α × β → K) (y : β → K) (f : MvPolynomial α K) :
    eval y (linearSection H f) = eval (fun i => ∑ c, y c * H (i,c)) f := by
  have h : (eval y).comp (linearSection H).toRingHom =
      eval (fun i => ∑ c, y c * H (i,c)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [linearSection]
    · intro i
      simp [linearSection]
  exact DFunLike.congr_fun h f

@[simp] lemma pderiv_sectionForm (H : α × β → K) (i : α) (c : β) :
    pderiv c (sectionForm H i) = C (H (i,c)) := by
  classical
  simp [sectionForm, pderiv_X, Pi.single_apply]

@[simp] lemma linearSection_X (H : α × β → K) (i : α) :
    linearSection H (X i) = sectionForm H i := aeval_X _ _

@[simp] lemma linearSection_C (H : α × β → K) (a : K) :
    linearSection H (C a) = C a := aeval_C _ _

variable [Fintype α]

lemma pderiv_linearSection (H : α × β → K) (f : MvPolynomial α K) (c : β) :
    pderiv c (linearSection H f) =
      ∑ i, C (H (i,c)) * linearSection H (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [linearSection]
  | add p q hp hq => simp [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp [map_mul, hp, pderiv_X, Pi.single_apply, apply_ite, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, mul_comm, add_comm]
    apply Finset.sum_congr rfl
    intro i _
    ring

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

noncomputable def singularSystem {R β : Type*} [CommRing R] (f : MvPolynomial β R) :
    Option β → MvPolynomial β R := fun j => match j with
    | none => f
    | some i => pderiv i f

def singularDegrees {β : Type*} (r : ℕ) : Option β → ℤ :=
  fun j => match j with
    | none => r
    | some _ => (r-1 : ℕ)

lemma singularSystem_homogeneous {R β : Type*} [CommRing R] {f : MvPolynomial β R} {r : ℕ}
    (hf : f.IsHomogeneous r) (j : Option β) :
    (singularSystem f j).IsWeightedHomogeneous (fun _ : β => (1 : ℤ))
      (singularDegrees r j) := by
  cases j with
  | none => exact homogeneous_intWeight hf
  | some i => exact homogeneous_intWeight hf.pderiv

theorem generic_slice_certificate {v d n r : ℕ}
    (f : MvPolynomial (Fin (v+1)) K) (hf : f ≠ 0) (hhom : f.IsHomogeneous r)
    (hdim : ringKrullDim (MvPolynomial (Fin (v+1)) K ⧸
      Ideal.span (Set.range (fun i => pderiv i f))) ≤ n)
    (hn : n+d < v+1) [IsAlgClosed L]
    (H : Fin (v+1) × Fin (d+1) → L) (hH : AlgebraicIndependent K H) :
    ∃ D : ℕ, Function.Surjective
      (macaulayMatrix (singularDegrees r)
        (singularSystem (linearSection H (map (algebraMap K L) f))) D).mulVec := by
  classical
  let g := linearSection H (map (algebraMap K L) f)
  have hg : g.IsHomogeneous r := linearSection_homogeneous H (hhom.map _)
  have hz : ∀ y ∈ zeroLocus L (Ideal.span (Set.range (singularSystem g))), y = 0 := by
    intro y hy
    have hh (j : Option (Fin (d+1))) : eval y (singularSystem g j) = 0 := by
      exact hy _ Ideal.mem_span_range_self
    apply generic_homogeneous_slice f hf hhom hdim hn H hH y
    · have h := hh none
      simpa only [singularSystem, g, eval_linearSection, eval_map, aeval_def] using h
    · intro c
      have h := hh (some c)
      simp only [singularSystem, g, pderiv_linearSection, map_sum, map_mul, eval_C,
        eval_linearSection, pderiv_map, eval_map] at h
      simpa only [mul_comm, aeval_def] using h
  obtain ⟨D,hD⟩ := homogeneous_piece_certificate
    (Ideal.span (Set.range (singularSystem g))) hz
  refine ⟨D, (macaulay_surjective_iff _ _ (singularSystem_homogeneous hg) D).mpr ?_⟩
  intro p hp
  exact hD p (intWeight_homogeneous hp)

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma linearSection_map {K L α β : Type*} [CommRing K] [CommRing L] [Fintype β]
    (φ : K →+* L) (H : α × β → K) (f : MvPolynomial α K) :
    map φ (linearSection H f) = linearSection (fun i => φ (H i)) (map φ f) := by
  apply MvPolynomial.induction_on f
  · intro a
    simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro p i hp
    simp only [map_mul, linearSection_X, hp, map_X,
      sectionForm, map_sum, map_C]

end PermanentBorder.SliceParameters

end OAI
