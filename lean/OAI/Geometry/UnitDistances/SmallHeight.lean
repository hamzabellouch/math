import OAI.Geometry.UnitDistances.Loci

namespace OAI

namespace UnitDistances.ExactHeightObstruction
open PlanarUnitDistances.WeightedAbsoluteValues
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
noncomputable abbrev height (x : K) : ℝ := exactHeight K x
omit [IsGalois ℚ K] in
lemma height_nonneg (x : K) : 0 ≤ height x := exactHeight_nonneg K x
omit [IsGalois ℚ K] in
@[simp] lemma height_zero : height (0 : K) = 0 := exactHeight_zero K
omit [IsGalois ℚ K] in
@[simp] lemma height_one : height (1 : K) = 0 := exactHeight_one K
omit [IsGalois ℚ K] in
@[simp] lemma height_neg (x : K) : height (-x) = height x := exactHeight_neg K x
@[simp] lemma height_inv (x : K) : height x⁻¹ = height x := exactHeight_inv K x
omit [IsGalois ℚ K] in
lemma height_mul_le (x y : K) : height (x*y) ≤ height x + height y := exactHeight_mul_le K x y
lemma height_add_le (x y : K) : height (x+y) ≤ Real.log 2 + height x + height y := exactHeight_add_le K x y
omit [IsGalois ℚ K] in
lemma height_root_le {m : ℕ} (hm : 0 < m) (a : Fin m → K) (x : K)
    (hx : x^m = ∑ i, a i*x^(i:ℕ)) :
    height x ≤ Real.log m + ∑ i, height (a i) := exactHeight_root_le K hm a x hx
end UnitDistances.ExactHeightObstruction

namespace UnitDistances.ExactSmallHeightField
open Filter Asymptotics
open scoped BigOperators
open ExactHeightObstruction UltraField

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*)
  [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsGalois ℚ (K i)] (J : ι → ℝ)

def Negligible (f : ∀ i, K i) : Prop :=
  (fun i => height (f i)) =o[(U : Filter ι)] J

variable {U K J}

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.congr {f g : ∀ i, K i} (hf : Negligible U K J f)
    (he : ∀ᶠ i in U, f i = g i) : Negligible U K J g := by
  apply hf.congr' _ (EventuallyEq.refl _ _)
  filter_upwards [he] with i hi
  rw [hi]

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.zero : Negligible U K J 0 := by
  simp [Negligible]

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.one : Negligible U K J 1 := by
  simp [Negligible]

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.neg {f : ∀ i, K i} (hf : Negligible U K J f) :
    Negligible U K J (-f) := by simpa [Negligible] using hf

theorem Negligible.inv {f : ∀ i, K i} (hf : Negligible U K J f) :
    Negligible U K J (fun i => (f i)⁻¹) := by simpa [Negligible] using hf

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.mul {f g : ∀ i, K i} (hf : Negligible U K J f)
    (hg : Negligible U K J g) : Negligible U K J (f * g) := by
  have hb : (fun i => height ((f * g) i)) =O[(U : Filter ι)]
      (fun i => height (f i) + height (g i)) := by
    apply IsBigO.of_bound'
    apply Eventually.of_forall
    intro i
    simp only [Real.norm_eq_abs, abs_of_nonneg (height_nonneg _),
      abs_of_nonneg (add_nonneg (height_nonneg _) (height_nonneg _))]
    exact height_mul_le _ _
  exact hb.trans_isLittleO (hf.add hg)

theorem Negligible.add (hJ : Tendsto J U atTop) {f g : ∀ i, K i}
    (hf : Negligible U K J f) (hg : Negligible U K J g) :
    Negligible U K J (f + g) := by
  have hb : (fun i => height ((f + g) i)) =O[(U : Filter ι)]
      (fun i => Real.log 2 + height (f i) + height (g i)) := by
    apply IsBigO.of_bound'
    apply Eventually.of_forall
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (height_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (add_nonneg (Real.log_nonneg (by norm_num))
        (height_nonneg _)) (height_nonneg _))]
    exact height_add_le _ _
  exact hb.trans_isLittleO (((isLittleO_const_id_atTop (Real.log 2)).comp_tendsto hJ).add hf |>.add hg)

noncomputable def constants (hJ : Tendsto J U atTop) : Subfield (FieldProduct U K) where
  carrier := {x | ∃ f, mk U K f = x ∧ Negligible U K J f}
  zero_mem' := ⟨0, map_zero _, Negligible.zero⟩
  one_mem' := ⟨1, map_one _, Negligible.one⟩
  add_mem' := by
    rintro x y ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f + g, map_add _ _ _, hf.add hJ hg⟩
  neg_mem' := by
    rintro x ⟨f, rfl, hf⟩
    exact ⟨-f, map_neg _ _, hf.neg⟩
  mul_mem' := by
    rintro x y ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f * g, map_mul _ _ _, hf.mul hg⟩
  inv_mem' := by
    rintro x ⟨f, rfl, hf⟩
    exact ⟨fun i => (f i)⁻¹, mk_inv U K f, hf.inv⟩

theorem mk_mem_constants_iff (hJ : Tendsto J U atTop) (f : ∀ i, K i) :
    mk U K f ∈ constants (K := K) hJ ↔ Negligible U K J f := by
  constructor
  · rintro ⟨g, he, hg⟩
    exact hg.congr ((mk_eq_mk U K _ _).mp he)
  · exact fun hf => ⟨f, rfl, hf⟩

omit [∀ i, IsGalois ℚ (K i)] in

theorem Negligible.root (hJ : Tendsto J U atTop) {m : ℕ} (hm : 0 < m)
    (a : Fin m → ∀ i, K i) (u : ∀ i, K i) (ha : ∀ j, Negligible U K J (a j))
    (hu : ∀ᶠ i in U, u i ^ m = ∑ j, a j i * u i ^ (j : ℕ)) :
    Negligible U K J u := by
  have hb : (fun i => height (u i)) =O[(U : Filter ι)]
      (fun i => Real.log m + ∑ j, height (a j i)) := by
    apply IsBigO.of_bound'
    filter_upwards [hu] with i hi
    rw [Real.norm_eq_abs, abs_of_nonneg (height_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (Real.log_nonneg (by exact_mod_cast hm))
        (Finset.sum_nonneg fun j _ => height_nonneg _))]
    exact height_root_le hm (fun j => a j i) (u i) hi
  apply hb.trans_isLittleO
  have hs := IsLittleO.sum (s := Finset.univ) (fun j _ => ha j)
  simpa only [Finset.sum_apply, Function.comp_def, id_eq] using
    ((isLittleO_const_id_atTop (Real.log m)).comp_tendsto hJ).add hs

theorem root_mem_constants (hJ : Tendsto J U atTop) {m : ℕ} (hm : 0 < m)
    (a : Fin m → constants (K := K) hJ) (u : FieldProduct U K)
    (hu : u ^ m = ∑ j, (a j : FieldProduct U K) * u ^ (j : ℕ)) :
    u ∈ constants (K := K) hJ := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
  choose b hb hsmall using fun j => (a j).property
  apply (mk_mem_constants_iff hJ f).mpr
  apply Negligible.root hJ hm b f hsmall
  have hrel : mk U K (f ^ m) = mk U K (∑ j, b j * f ^ (j : ℕ)) := by
    simpa only [map_pow, map_sum, map_mul, hb] using hu
  have he := (mk_eq_mk U K _ _).mp hrel
  simpa only [Pi.pow_apply, Finset.sum_apply, Pi.mul_apply] using he

theorem algebraic_mem_constants (hJ : Tendsto J U atTop) (u : FieldProduct U K)
    (hu : IsAlgebraic (constants (K := K) hJ) u) : u ∈ constants (K := K) hJ := by
  classical
  obtain ⟨p, hp, hz⟩ := hu.isIntegral
  have hm : 0 < p.natDegree :=
    Polynomial.natDegree_pos_of_aeval_root hp.ne_zero hz (fun x hx => by simpa using hx)
  apply root_mem_constants (K := K) hJ hm (fun j => -p.coeff (j : ℕ)) u
  change Polynomial.aeval u p = 0 at hz
  have hh := congrArg (Polynomial.aeval u) hp.as_sum
  rw [hz] at hh
  simp only [map_add, map_sum, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at hh
  rw [← Fin.sum_univ_eq_sum_range] at hh
  simp only [Subfield.coe_neg, neg_mul, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hh.symm

theorem large_height_transcendental (hJ : Tendsto J U atTop) (f : ∀ i, K i)
    {c : ℝ} (hc : 0 < c) (hf : ∀ᶠ i in U, c * J i ≤ height (f i)) :
    Transcendental (constants (K := K) hJ) (mk U K f) := by
  intro halg
  have hsmall := (mk_mem_constants_iff hJ f).mp (algebraic_mem_constants hJ _ halg)
  have hbound := hsmall.bound (half_pos hc)
  obtain ⟨i, hi, hpos, hb⟩ := (hf.and ((hJ.eventually_gt_atTop 0).and hbound)).exists
  rw [Real.norm_eq_abs, abs_of_nonneg (height_nonneg _), Real.norm_eq_abs,
    abs_of_pos hpos] at hb
  have hh : 0 < c * J i := mul_pos hc hpos
  nlinarith

end UnitDistances.ExactSmallHeightField

namespace UnitDistances.UltraField
open Filter
variable {ι : Type*} (U : Ultrafilter ι) (K L : ι → Type*)
  [∀ i, Field (K i)] [∀ i, Field (L i)]

noncomputable def map (f : ∀ i, K i →+* L i) : FieldProduct U K →+* FieldProduct U L :=
  Ideal.Quotient.lift (zeroIdeal U K)
    ((mk U L).comp (RingHom.pi fun i => (f i).comp (Pi.evalRingHom K i))) (by
      intro x hx
      apply (mk_eq_zero U L _).mpr
      filter_upwards [hx] with i hi
      change f i (x i)=0
      rw [hi,map_zero])

@[simp] lemma map_mk (f : ∀ i, K i →+* L i) (x : ∀ i, K i) :
    map U K L f (mk U K x)=mk U L (fun i => f i (x i)) := rfl

lemma transcendental_map {k : Type*} [Field k] [Algebra k (FieldProduct U K)]
    [Algebra k (FieldProduct U L)] (f : ∀ i, K i →+* L i)
    (hcomm : ∀ r : k, map U K L f (algebraMap k (FieldProduct U K) r)=
      algebraMap k (FieldProduct U L) r)
    (x : FieldProduct U K) (hx : Transcendental k x) :
    Transcendental k (map U K L f x) := by
  let φ : FieldProduct U K →ₐ[k] FieldProduct U L :=
    { map U K L f with commutes' := hcomm }
  intro h
  exact hx ((isAlgebraic_algHom_iff φ φ.injective).mp h)
end UnitDistances.UltraField

namespace PlanarUnitDistances.UltraHeightGrid
open Filter Asymptotics UnitDistances.UltraField UnitDistances.ExactSmallHeightField
open UnitDistances.ExactHeightObstruction
variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*)
  [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsGalois ℚ (K i)]
  {J : ι → ℝ} (hJ : Tendsto J U atTop)

noncomputable def complexMap (e : ∀ i,K i →+* ℂ) :
    FieldProduct U K →+* FieldProduct U (fun _ => ℂ) := map U K (fun _ => ℂ) e

@[instance_reducible] noncomputable def complexAlgebra (e : ∀ i,K i →+* ℂ) :
    Algebra (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) :=
  ((complexMap U K e).comp (constants (K := K) hJ).subtype).toAlgebra

omit [∀ i, IsGalois ℚ (K i)] in
lemma negligible_of_bound (u : ∀ i,K i) (b : ι → ℝ) (hb : b=o[(U : Filter ι)] J)
    (hu : ∀ᶠ i in U,height (u i)≤b i) : Negligible U K J u := by
  have h : (fun i => height (u i))=O[(U : Filter ι)] b := by
    apply IsBigO.of_bound'
    filter_upwards [hu] with i hi
    rw [Real.norm_eq_abs,abs_of_nonneg (height_nonneg _),Real.norm_eq_abs]
    exact hi.trans (le_abs_self _)
  exact h.trans_isLittleO hb

variable (e : ∀ i,K i →+* ℂ)
variable [Algebra (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ))]
    (hcomm : ∀ r : constants (K := K) hJ,
      complexMap U K e r=algebraMap (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) r)

include hcomm
lemma large_transcendental (u : ∀ i,K i) {c : ℝ} (hc : 0<c)
    (hu : ∀ᶠ i in U,c*J i≤height (u i)) :
    Transcendental (constants (K := K) hJ)
      (mk U (fun _ => ℂ) (fun i => e i (u i))) :=
  transcendental_map U K (fun _ => ℂ) e hcomm (mk U K u)
    (large_height_transcendental hJ u hc hu)

lemma rectangle_constant (a b c d : ∀ i,K i)
    (hc : ∀ᶠ i in U,c i≠0) (hd : ∀ᶠ i in U,d i≠0)
    (hsmall : Negligible U K J (fun i => a i*b i/(c i*d i))) :
    ∃ r : constants (K := K) hJ,
      mk U (fun _ => ℂ) (fun i => e i (a i))*mk U (fun _ => ℂ) (fun i => e i (b i))=
      mk U (fun _ => ℂ) (fun i => e i (c i))*mk U (fun _ => ℂ) (fun i => e i (d i))*
        algebraMap (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) r := by
  let r : constants (K := K) hJ :=
    ⟨mk U K (fun i => a i*b i/(c i*d i)),(mk_mem_constants_iff hJ _).mpr hsmall⟩
  refine ⟨r,?_⟩
  rw [← hcomm r]
  change _=_*mk U (fun _ => ℂ) (fun i => e i (a i*b i/(c i*d i)))
  rw [← map_mul,← map_mul,← map_mul,mk_eq_mk]
  filter_upwards [hc,hd] with i hci hdi
  change e i (a i)*e i (b i)=e i (c i)*e i (d i)*e i (a i*b i/(c i*d i))
  simp only [map_div₀,map_mul]
  have hc' : e i (c i)≠0 := (map_ne_zero (e i)).mpr hci
  have hd' : e i (d i)≠0 := (map_ne_zero (e i)).mpr hdi
  field_simp [hc',hd']

end PlanarUnitDistances.UltraHeightGrid

namespace PlanarUnitDistances.EdgeLabels
open Filter Asymptotics UnitDistances.UltraField UnitDistances.ExactSmallHeightField
open UnitDistances.ExactHeightObstruction UltraHeightGrid
variable (U : Ultrafilter ℕ) (K : ℕ → Type)
  [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsGalois ℚ (K i)]
  (J : ℕ → ℝ) (hJ : Tendsto J U atTop) (e : ∀ i,K i →+* ℂ)
variable [Algebra (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ))]
    (hcomm : ∀ r : constants (K := K) hJ,
      complexMap U K e r=algebraMap (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) r)
variable (ell : ∀ n,ℂ → ℂ → K n)

noncomputable def label (p r : ℕ → ℂ) : FieldProduct U (fun _ => ℂ) :=
  mk U (fun _ => ℂ) (fun n => e n (ell n (p n) (r n)))

include hJ hcomm in
lemma transcendental (p r : ℕ → ℂ) {c : ℝ} (hc : 0<c)
    (h : ∀ᶠ n in U,c*J n≤height (ell n (p n) (r n))) :
    Transcendental (constants (K := K) hJ) (label U K e ell p r) :=
  large_transcendental U K hJ e hcomm _ hc h

include hJ hcomm in
lemma rectangle (p p' r r' : ℕ → ℂ) (b : ℕ → ℝ) (hb : b=o[(U : Filter ℕ)] J)
    (hn : ∀ᶠ n in U,ell n (p n) (r' n)≠0 ∧ ell n (p' n) (r n)≠0)
    (h : ∀ᶠ n in U,height (ell n (p n) (r n)*ell n (p' n) (r' n)/
      (ell n (p n) (r' n)*ell n (p' n) (r n)))≤b n) :
    ∃ c : constants (K := K) hJ,
      label U K e ell p r*label U K e ell p' r'=
      label U K e ell p r'*label U K e ell p' r*
        algebraMap (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) c := by
  exact rectangle_constant U K hJ e hcomm _ _ _ _
    (hn.mono fun _ hi => hi.1) (hn.mono fun _ hi => hi.2)
    (negligible_of_bound U K _ b hb h)

omit [∀ i, IsGalois ℚ (K i)] [∀ i, NumberField (K i)] in
lemma distance (p r : ℕ → ℂ)
    (h : ∀ᶠ n in U,(p n-r n)*(star (p n)-star (r n))=
      2-e n (ell n (p n) (r n))-(e n (ell n (p n) (r n)))⁻¹) :
    (mk U (fun _ => ℂ) p-mk U (fun _ => ℂ) r)*
      (mk U (fun _ => ℂ) (fun n => star (p n))-mk U (fun _ => ℂ) (fun n => star (r n)))=
      2-label U K e ell p r-(label U K e ell p r)⁻¹ := by
  unfold label
  rw [← map_sub,← map_sub,← map_mul,← mk_inv,← map_ofNat (mk U (fun _ => ℂ)) 2,
    ← map_sub,← map_sub,mk_eq_mk]
  exact h
end PlanarUnitDistances.EdgeLabels

namespace UnitDistances.GridCount
open scoped BigOperators
open Finset

lemma pow_expect_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (n : ℕ) :
    (𝔼 a, f a)^n ≤ 𝔼 a, (f a)^n := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have h := (convexOn_pow (𝕜 := ℝ) n).map_sum_le
    (t := univ) (w := fun _ : α => (Fintype.card α : ℝ)⁻¹) (p := f)
    (by intros; positivity) (by simp [hc]) (by simpa using hf)
  simpa only [smul_eq_mul, ← Finset.mul_sum, Fintype.expect_eq_sum_div_card,
    div_eq_inv_mul] using h

lemma expect_prod_tuple {α : Type*} [Fintype α] (f : α → ℝ) (n : ℕ) :
    (𝔼 p : Fin n → α, ∏ i, f (p i)) = (𝔼 a, f a)^n := by
  classical
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.sum_pow,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_pow]

theorem complete_grid_density {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α → β → ℝ) (hE : ∀ a b, 0 ≤ E a b)
    (N j : ℕ) :
    (𝔼 a, 𝔼 b, E a b)^(N*j) ≤
      𝔼 p : Fin N → α, 𝔼 r : Fin j → β, ∏ i, ∏ l, E (p i) (r l) := by
  classical
  let X : (Fin N → α) → ℝ := fun p => 𝔼 b, ∏ i, E (p i) b
  have hX : ∀ p, 0 ≤ X p := fun p =>
    Finset.expect_nonneg fun b _ => Finset.prod_nonneg fun i _ => hE (p i) b
  have hEX : (𝔼 a, 𝔼 b, E a b)^N ≤ 𝔼 p, X p := by
    calc
      (𝔼 a, 𝔼 b, E a b)^N = (𝔼 b, 𝔼 a, E a b)^N := by
        rw [Finset.expect_comm]
      _ ≤ 𝔼 b, (𝔼 a, E a b)^N := pow_expect_le _
        (fun b => Finset.expect_nonneg fun a _ => hE a b) N
      _ = 𝔼 b, 𝔼 p : Fin N → α, ∏ i, E (p i) b := by
        apply Finset.expect_congr rfl
        intro b _
        exact (expect_prod_tuple (fun a => E a b) N).symm
      _ = 𝔼 p, X p := by rw [Finset.expect_comm]
  calc
    (𝔼 a, 𝔼 b, E a b)^(N*j) = ((𝔼 a, 𝔼 b, E a b)^N)^j := (pow_mul _ _ _)
    _ ≤ (𝔼 p, X p)^j := pow_le_pow_left₀ (pow_nonneg (Finset.expect_nonneg fun a _ =>
      Finset.expect_nonneg fun b _ => hE a b) N) hEX j
    _ ≤ 𝔼 p, (X p)^j := pow_expect_le X hX j
    _ = 𝔼 p : Fin N → α, 𝔼 r : Fin j → β, ∏ i, ∏ l, E (p i) (r l) := by
      apply Finset.expect_congr rfl
      intro p _
      dsimp only [X]
      rw [← expect_prod_tuple]
      apply Finset.expect_congr rfl
      intro r _
      exact Finset.prod_comm

lemma expect_pair_indicator {α β : Type*} [Fintype α] [Fintype β]
    (E : α → β → Prop) [DecidableRel E] :
    (𝔼 a, 𝔼 b, if E a b then (1 : ℝ) else 0) =
      ((univ.filter fun ab : α × β => E ab.1 ab.2).card : ℝ) /
        ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) := by
  classical
  rw [← Finset.expect_product' univ univ]
  simp only [univ_product_univ, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, Fintype.card_prod, Nat.cast_mul]

def grids {α β : Type*} [Fintype α] [Fintype β] (E : α → β → Prop)
    [DecidableRel E] (N j : ℕ) : Finset ((Fin N → α) × (Fin j → β)) :=
  univ.filter fun pr => ∀ i l, E (pr.1 i) (pr.2 l)

theorem complete_grid_count {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α → β → Prop) [DecidableRel E] (N j : ℕ) :
    (Fintype.card α : ℝ)^N * (Fintype.card β : ℝ)^j *
      (((univ.filter fun ab : α × β => E ab.1 ab.2).card : ℝ) /
        ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)))^(N*j)
      ≤ (grids E N j).card := by
  classical
  have h := complete_grid_density (fun a b => if E a b then (1 : ℝ) else 0)
    (by intros; split_ifs <;> norm_num) N j
  simp only [Finset.prod_boole, mem_univ, forall_const] at h
  rw [expect_pair_indicator, expect_pair_indicator] at h
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
  have hd : 0 < (Fintype.card α : ℝ)^N * (Fintype.card β : ℝ)^j := by positivity
  have hh := (le_div_iff₀ hd).mp h
  simpa only [grids, mul_comm] using hh

end UnitDistances.GridCount

namespace UnitDistances.GenericDiagonal
open Filter

theorem exists_avoiding {α τ : Type*} [DecidableEq α] (G : Finset α)
    (S : Finset τ) (bad : τ → Finset α)
    (h : ∑ s ∈ S, (bad s).card < G.card) :
    ∃ x ∈ G, ∀ s ∈ S, x ∉ bad s := by
  classical
  have hc : ¬G ⊆ S.biUnion bad := by
    intro hsub
    exact (not_le_of_gt h) ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
  obtain ⟨x, hx, hn⟩ := Finset.not_subset.mp hc
  exact ⟨x, hx, fun s hs hm => hn (Finset.mem_biUnion.mpr ⟨s, hs, hm⟩)⟩

theorem diagonal_nat {A : ℕ → Type*} [∀ n, Nonempty (A n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (good : ∀ n, A n → Prop) (test : ∀ n, ℕ → A n → Prop)
    (h : ∀ s, ∀ᶠ n in U, ∃ x, good n x ∧ ∀ a ≤ s, test n a x) :
    ∃ x : ∀ n, A n, (∀ᶠ n in U, good n (x n)) ∧
      ∀ a, ∀ᶠ n in U, test n a (x n) := by
  classical
  let P : ℕ → ℕ → Prop := fun n s => ∃ x, good n x ∧ ∀ a ≤ s, test n a x
  let s : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  let x : ∀ n, A n := fun n => if hn : P n (s n) then Classical.choose hn
    else Classical.choice (inferInstance : Nonempty (A n))
  have hprefix (a : ℕ) : ∀ᶠ n in U, P n (s n) ∧ a ≤ s n := by
    filter_upwards [h a, (eventually_ge_atTop a).filter_mono hU] with n hn hna
    exact ⟨Nat.findGreatest_spec hna hn, Nat.le_findGreatest hna hn⟩
  refine ⟨x, ?_, ?_⟩
  · filter_upwards [hprefix 0] with n hn
    dsimp only [x]
    rw [dite_eq_left hn.1]
    exact (Classical.choose_spec hn.1).1
  · intro a
    filter_upwards [hprefix a] with n hn
    dsimp only [x]
    rw [dite_eq_left hn.1]
    exact (Classical.choose_spec hn.1).2 a hn.2

theorem diagonal_countable {A : ℕ → Type*} [∀ n, Nonempty (A n)]
    {τ : Type*} [Countable τ] (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (good : ∀ n, A n → Prop) (test : ∀ n, τ → A n → Prop)
    (h : ∀ S : Finset τ, ∀ᶠ n in U, ∃ x, good n x ∧ ∀ a ∈ S, test n a x) :
    ∃ x : ∀ n, A n, (∀ᶠ n in U, good n (x n)) ∧
      ∀ a, ∀ᶠ n in U, test n a (x n) := by
  classical
  let := Encodable.ofCountable τ
  let tests : ℕ → Finset τ := fun s => (Finset.range (s+1)).biUnion
    (fun i => (Encodable.decode (α := τ) i).toFinset)
  have mem_tests (a : τ) : a ∈ tests (Encodable.encode a) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨Encodable.encode a, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    simp
  obtain ⟨x, hx, htest⟩ := diagonal_nat U hU good
    (fun n s x => ∀ a ∈ tests s, test n a x) (by
      intro s
      filter_upwards [h (tests s)] with n hn
      obtain ⟨x, hx, hall⟩ := hn
      refine ⟨x, hx, fun a ha b hb => hall b ?_⟩
      apply Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono (Nat.add_le_add_right ha 1)) hb)
  refine ⟨x, hx, fun a => ?_⟩
  filter_upwards [htest (Encodable.encode a)] with n hn
  exact hn a (mem_tests a)

end UnitDistances.GenericDiagonal

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma Lower.one (ht : Tendsto t F atTop) : Lower F t (fun _ => 1) 0 := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  simpa using Real.rpow_le_rpow_of_exponent_le hi (show 0 - ε ≤ 0 by linarith)

lemma Upper.one (ht : Tendsto t F atTop) : Upper F t (fun _ => 1) 0 := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  simpa using Real.one_le_rpow hi hε.le

lemma Lower.pow (hf : Lower F t f a) (ht : Tendsto t F atTop) (n : ℕ) :
    Lower F t (fun i => f i ^ n) (a * n) := by
  induction n with
  | zero => simpa using Lower.one ht
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using ih.mul hf ht

lemma Upper.pow (hf : Upper F t f a) (hn : ∀ᶠ i in F, 0 ≤ f i)
    (ht : Tendsto t F atTop) (n : ℕ) : Upper F t (fun i => f i ^ n) (a * n) := by
  induction n with
  | zero => simpa using Upper.one ht
  | succ n ih =>
    have hn' : ∀ᶠ i in F, 0 ≤ f i ^ n := hn.mono fun _ h => pow_nonneg h _
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using ih.mul hf hn' hn ht

lemma eventually_lt_of_upper_lower (hf : Upper F t f a) (hg : Lower F t g b)
    (hab : a < b) (ht : Tendsto t F atTop) : ∀ᶠ i in F, f i < g i := by
  have hε : 0 < (b-a)/3 := by linarith
  filter_upwards [hf _ hε, hg _ hε, ht.eventually_gt_atTop 1] with i hi hj hti
  exact hi.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hti (by linarith)).trans_le hj)

def Saving (F : Filter ι) (t f : ι → ℝ) (a : ℝ) : Prop :=
  ∃ b < a, Upper F t f b

lemma Saving.add (hf : Saving F t f a) (hg : Saving F t g a)
    (ht : Tendsto t F atTop) : Saving F t (fun i => f i + g i) a := by
  obtain ⟨b, hb, hf⟩ := hf
  obtain ⟨c, hc, hg⟩ := hg
  exact ⟨max b c, max_lt hb hc,
    (hf.exponent_mono (le_max_left _ _) ht).add (hg.exponent_mono (le_max_right _ _) ht) ht⟩

lemma Saving.zero (ht : Tendsto t F atTop) (a : ℝ) : Saving F t (fun _ => 0) a := by
  refine ⟨a-1, by linarith, ?_⟩
  intro ε _
  filter_upwards [eventually_base_pos ht] with i hi
  exact Real.rpow_nonneg hi.le _

lemma Saving.finset_sum {τ : Type*} (S : Finset τ) (f : τ → ι → ℝ)
    (hf : ∀ s ∈ S, Saving F t (f s) a) (ht : Tendsto t F atTop) :
    Saving F t (fun i => ∑ s ∈ S, f s i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Saving.zero ht a
  | @insert s S hs ih =>
    simpa [Finset.sum_insert hs] using
      (hf s (Finset.mem_insert_self _ _)).add
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx)) ht

lemma Saving.eventually_lt (hf : Saving F t f a) (hg : Lower F t g a)
    (ht : Tendsto t F atTop) : ∀ᶠ i in F, f i < g i := by
  obtain ⟨b, hb, hf⟩ := hf
  exact eventually_lt_of_upper_lower hf hg hb ht
end PlanarUnitDistances.PowerGrowth

end OAI
