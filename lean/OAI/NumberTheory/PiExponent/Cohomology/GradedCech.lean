import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher
import OAI.NumberTheory.PiExponent.Polynomials.GradedLocalizationExact

namespace OAI

namespace PiExponent.GradedCech
noncomputable section
open scoped BigOperators
open GradedLocalizationExact

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem divisor_isUnit (a c : R) (hac : a ∣ c) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (Submonoid.powers c) M)) a) := by
  obtain ⟨b, rfl⟩ := hac
  have h := IsLocalizedModule.Away.isUnit_algebraMap
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M) (a * b)
  rw [map_mul] at h
  exact (((Commute.all a b).map (algebraMap R
    (Module.End R (LocalizedModule (Submonoid.powers (a * b)) M)))).isUnit_mul_iff.mp h).1

theorem divisor_powers_isUnit (a c : R) (hac : a ∣ c) (s : Submonoid.powers a) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (Submonoid.powers c) M)) s) := by
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  exact (divisor_isUnit (M := M) a c hac).pow n

def restriction (a c : R) (hac : a ∣ c) :
    LocalizedModule (Submonoid.powers a) M →ₗ[R]
      LocalizedModule (Submonoid.powers c) M :=
  LocalizedModule.lift (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
    (divisor_powers_isUnit a c hac)

@[simp] theorem restriction_mk_one (a c : R) (hac : a ∣ c) (m : M) :
    restriction a c hac (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  exact LocalizedModule.lift_mk_one _ _ _ m

@[simp] theorem restriction_fraction_zero (a c : R) (hac : a ∣ c) (m : M) :
    restriction a c hac (fraction a m 0) = fraction c m 0 := by
  simpa only [fraction, powerDenominator_zero] using restriction_mk_one a c hac m

theorem power_smul_fraction (a : R) (m : M) (n : ℕ) :
    a ^ n • fraction a m n = fraction a m 0 := by
  simp only [fraction, powerDenominator_zero, LocalizedModule.smul'_mk]
  exact LocalizedModule.mk_cancel (powerDenominator a n) m

theorem restriction_fraction (a b : R) (m : M) (n : ℕ) :
    restriction a (a * b) (dvd_mul_right a b) (fraction a m n) =
      fraction (a * b) (b ^ n • m) n := by
  have hu := (divisor_isUnit (M := M) a (a * b) (dvd_mul_right a b)).pow n
  rw [← map_pow] at hu
  apply ((Module.End.isUnit_iff _).mp hu).injective
  change a ^ n • restriction a (a * b) (dvd_mul_right a b) (fraction a m n) =
    a ^ n • fraction (a * b) (b ^ n • m) n
  rw [← map_smul, power_smul_fraction, restriction_fraction_zero]
  change fraction (a * b) m 0 =
    a ^ n • LocalizedModule.mk (b ^ n • m) (powerDenominator (a * b) n)
  rw [LocalizedModule.smul'_mk, smul_smul, ← mul_pow]
  simpa only [fraction, LocalizedModule.smul'_mk] using
    (power_smul_fraction (a * b) m n).symm

theorem restriction_refl (a : R) : restriction (M := M) a a dvd_rfl = LinearMap.id := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit a a dvd_rfl)
  apply LinearMap.ext
  intro m
  exact restriction_mk_one a a dvd_rfl m

theorem restriction_comp (a b c : R) (hab : a ∣ b) (hbc : b ∣ c) :
    (restriction b c hbc).comp (restriction (M := M) a b hab) =
      restriction a c (hab.trans hbc) := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit a c (hab.trans hbc))
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, restriction_mk_one]

theorem restriction_localizedMap {N : Type*} [AddCommGroup N] [Module R N]
    (a c : R) (hac : a ∣ c) (f : M →ₗ[R] N) :
    (localizedMap c f).comp (restriction (M := M) a c hac) =
      (restriction (M := N) a c hac).comp (localizedMap a f) := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit (M := N) a c hac)
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
  rw [show LocalizedModule.mk m (1 : Submonoid.powers a) = fraction a m 0 by
    simp only [fraction, powerDenominator_zero]]
  rw [restriction_fraction_zero, localizedMap_fraction,
    localizedMap_fraction, restriction_fraction_zero]

variable {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

def degreeRestriction (a c : R) (ea ec : ℤ)
    (ha : a ∈ 𝒜 ea) (hc : c ∈ 𝒜 ec)
    (hfactor : ∃ b : R, b ∈ 𝒜 (ec - ea) ∧ c = a * b) (d : ℤ) :
    degreePiece 𝒜 𝓜 a ea ha d →+ degreePiece 𝒜 𝓜 c ec hc d where
  toFun z := ⟨restriction a c (by obtain ⟨b, _, hb⟩ := hfactor; exact ⟨b, hb⟩) z.val, by
    obtain ⟨n, m, hm, hz⟩ := z.property
    obtain ⟨b, hb, rfl⟩ := hfactor
    refine ⟨n, b ^ n • m, ?_, ?_⟩
    · have h := power_smul_mem 𝒜 𝓜 b (ec - ea) hb hm n
      convert h using 1
      ring_nf
    · rw [hz]
      exact restriction_fraction a b m n⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z z' := Subtype.ext (map_add _ _ _)

@[simp] theorem degreeRestriction_coe (a c : R) (ea ec : ℤ)
    (ha : a ∈ 𝒜 ea) (hc : c ∈ 𝒜 ec)
    (hfactor : ∃ b : R, b ∈ 𝒜 (ec - ea) ∧ c = a * b) (d : ℤ)
    (z : degreePiece 𝒜 𝓜 a ea ha d) :
    (degreeRestriction 𝒜 𝓜 a c ea ec ha hc hfactor d z).val =
      restriction a c (by obtain ⟨b, _, hb⟩ := hfactor; exact ⟨b, hb⟩) z.val := rfl

section Cover
variable {J : Type*} [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

def coverProduct (s : Finset J) : R := ∏ j ∈ s, x j

include hx in
theorem coverProduct_mem (s : Finset J) : coverProduct x s ∈ 𝒜 (s.card : ℤ) := by
  induction s using Finset.induction_on with
  | empty => simpa [coverProduct] using (SetLike.one_mem_graded 𝒜)
  | @insert j s hj hs =>
      have h := SetLike.GradedMul.mul_mem (hx j) hs
      simpa [coverProduct, Finset.prod_insert hj, Finset.card_insert_of_notMem hj,
        Nat.cast_add, add_comm] using h

include hx in

theorem coverProduct_factor {s t : Finset J} (hst : s ⊆ t) :
    ∃ b : R, b ∈ 𝒜 ((t.card : ℤ) - (s.card : ℤ)) ∧
      coverProduct x t = coverProduct x s * b := by
  refine ⟨coverProduct x (t \ s), ?_, ?_⟩
  · have h := coverProduct_mem 𝒜 x hx (t \ s)
    rwa [Finset.card_sdiff_of_subset hst, Nat.cast_sub (Finset.card_le_card hst)] at h
  · exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)

include hx in
theorem coverProduct_dvd {s t : Finset J} (hst : s ⊆ t) :
    coverProduct x s ∣ coverProduct x t := by
  obtain ⟨b, _, hb⟩ := coverProduct_factor 𝒜 x hx hst
  exact ⟨b, hb⟩

abbrev IntersectionPiece (s : Finset J) (d : ℤ) :=
  degreePiece 𝒜 𝓜 (coverProduct x s) (s.card : ℤ) (coverProduct_mem 𝒜 x hx s) d

def setRestriction {s t : Finset J} (hst : s ⊆ t) (d : ℤ) :
    IntersectionPiece 𝒜 𝓜 x hx s d →+ IntersectionPiece 𝒜 𝓜 x hx t d :=
  degreeRestriction 𝒜 𝓜 _ _ _ _ (coverProduct_mem 𝒜 x hx s)
    (coverProduct_mem 𝒜 x hx t) (coverProduct_factor 𝒜 x hx hst) d

@[simp] theorem setRestriction_coe {s t : Finset J} (hst : s ⊆ t) (d : ℤ)
    (z : IntersectionPiece 𝒜 𝓜 x hx s d) :
    (setRestriction 𝒜 𝓜 x hx hst d z).val =
      restriction (coverProduct x s) (coverProduct x t) (coverProduct_dvd 𝒜 x hx hst) z.val := rfl

@[simp] theorem setRestriction_refl (s : Finset J) (d : ℤ)
    (z : IntersectionPiece 𝒜 𝓜 x hx s d) : setRestriction 𝒜 𝓜 x hx (s := s) le_rfl d z = z := by
  apply Subtype.ext
  rw [setRestriction_coe, restriction_refl]
  rfl

theorem setRestriction_comp {s t u : Finset J} (hst : s ⊆ t) (htu : t ⊆ u)
    (d : ℤ) (z : IntersectionPiece 𝒜 𝓜 x hx s d) :
    setRestriction 𝒜 𝓜 x hx htu d (setRestriction 𝒜 𝓜 x hx hst d z) =
      setRestriction 𝒜 𝓜 x hx (hst.trans htu) d z := by
  apply Subtype.ext
  simp only [setRestriction_coe]
  exact DFunLike.congr_fun (restriction_comp (coverProduct x s) (coverProduct x t)
    (coverProduct x u) (coverProduct_dvd 𝒜 x hx hst) (coverProduct_dvd 𝒜 x hx htu)) z.val

def tupleSet {n : ℕ} (t : Fin n → J) : Finset J := Finset.univ.image t

theorem tupleSet_comp_subset {m n : ℕ} (t : Fin n → J) (f : Fin m → Fin n) :
    tupleSet (t ∘ f) ⊆ tupleSet t := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_image.mpr ⟨f i, Finset.mem_univ _, rfl⟩

abbrev Cochain (d : ℤ) (q : ℕ) :=
  ∀ t : Fin (q + 1) → J, IntersectionPiece 𝒜 𝓜 x hx (tupleSet t) d

def differential (d : ℤ) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    Cochain 𝒜 𝓜 x hx d (q + 1) :=
  fun t => ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
    setRestriction 𝒜 𝓜 x hx (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove))

@[simp] theorem differential_zero (d : ℤ) {q : ℕ} :
    differential 𝒜 𝓜 x hx d (0 : Cochain 𝒜 𝓜 x hx d q) = 0 := by
  funext t
  simp only [differential, Pi.zero_apply, map_zero, smul_zero, Finset.sum_const_zero]

theorem differential_sub (d : ℤ) {q : ℕ} (c b : Cochain 𝒜 𝓜 x hx d q) :
    differential 𝒜 𝓜 x hx d (c - b) = differential 𝒜 𝓜 x hx d c - differential 𝒜 𝓜 x hx d b := by
  funext t
  simp only [differential, Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]

theorem tupleSet_subset {L : Type*} (s : Finset J) (f : L → J)
    (hf : ∀ l, f l ∈ s) {n : ℕ} (t : Fin n → L) : tupleSet (f ∘ t) ⊆ s := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact hf (t i)

def evaluate (d : ℤ) {L : Type*} (s : Finset J) (f : L → J)
    (hf : ∀ l, f l ∈ s) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    ProjectiveMonomialCechHigher.Cochain L (IntersectionPiece 𝒜 𝓜 x hx s d) q :=
  fun t => setRestriction 𝒜 𝓜 x hx (tupleSet_subset s f hf t) d (c (f ∘ t))

theorem evaluate_differential (d : ℤ) {L : Type*} (s : Finset J) (f : L → J)
    (hf : ∀ l, f l ∈ s) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    evaluate 𝒜 𝓜 x hx d s f hf (differential 𝒜 𝓜 x hx d c) =
      ProjectiveMonomialCechHigher.differential (evaluate 𝒜 𝓜 x hx d s f hf c) := by
  funext t
  simp only [evaluate, differential, ProjectiveMonomialCechHigher.differential,
    map_sum, map_zsmul, setRestriction_comp]
  rfl

theorem differential_squared (d : ℤ) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    differential 𝒜 𝓜 x hx d (differential 𝒜 𝓜 x hx d c) = 0 := by
  funext t
  have ht : ∀ i, t i ∈ tupleSet t := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have h := congrFun (ProjectiveMonomialCechHigher.differential_squared
    (evaluate 𝒜 𝓜 x hx d (tupleSet t) t ht c)) id
  rw [← evaluate_differential, ← evaluate_differential] at h
  change setRestriction 𝒜 𝓜 x hx le_rfl d
    (differential 𝒜 𝓜 x hx d (differential 𝒜 𝓜 x hx d c) t) = 0 at h
  simpa only [setRestriction_refl, Pi.zero_apply] using h

def differentialHom (d : ℤ) (q : ℕ) :
    Cochain 𝒜 𝓜 x hx d q →+ Cochain 𝒜 𝓜 x hx d (q + 1) where
  toFun := differential 𝒜 𝓜 x hx d
  map_zero' := differential_zero 𝒜 𝓜 x hx d
  map_add' c b := by
    funext t
    simp only [differential, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

def augmentation (d : ℤ) : 𝓜 d →+ Cochain 𝒜 𝓜 x hx d 0 where
  toFun m t := ⟨fraction (coverProduct x (tupleSet t)) (m : M) 0,
    0, m, by simpa only [Nat.cast_zero, zero_mul, add_zero] using m.property, rfl⟩
  map_zero' := by
    funext t
    exact Subtype.ext (fraction_zero _ _)
  map_add' m n := by
    funext t
    apply Subtype.ext
    simpa only [fraction, powerDenominator_zero, Pi.add_apply, AddMemClass.coe_add,
      LocalizedModule.mkLinearMap_apply] using
      (LocalizedModule.mkLinearMap (Submonoid.powers (coverProduct x (tupleSet t))) M).map_add
        (m : M) (n : M)

@[simp] theorem augmentation_coe (d : ℤ) (m : 𝓜 d) (t : Fin 1 → J) :
    (augmentation 𝒜 𝓜 x hx d m t).val = fraction (coverProduct x (tupleSet t)) (m : M) 0 := rfl

theorem differential_augmentation (d : ℤ) (m : 𝓜 d) :
    differential 𝒜 𝓜 x hx d (augmentation 𝒜 𝓜 x hx d m) = 0 := by
  funext t
  apply Subtype.ext
  simp [differential, Fin.sum_univ_succ, setRestriction_coe,
    augmentation_coe, restriction_fraction_zero]
  change restriction _ _ _ (fraction _ (m : M) 0) + -fraction _ (m : M) 0 = 0
  rw [restriction_fraction_zero, add_neg_cancel]

section Maps
variable {N σN : Type*} [AddCommGroup N] [Module R N]
  [SetLike σN N] [AddSubgroupClass σN N]
  (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]
  (f : M →ₗ[R] N) (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i)

theorem pieceMap_setRestriction {s t : Finset J} (hst : s ⊆ t) (d : ℤ)
    (z : IntersectionPiece 𝒜 𝓜 x hx s d) :
    pieceMap 𝒜 𝓜 (coverProduct x t) _ (coverProduct_mem 𝒜 x hx t) 𝓝 d f hf
        (setRestriction 𝒜 𝓜 x hx hst d z) =
      setRestriction 𝒜 𝓝 x hx hst d
        (pieceMap 𝒜 𝓜 (coverProduct x s) _ (coverProduct_mem 𝒜 x hx s) 𝓝 d f hf z) := by
  apply Subtype.ext
  simp only [pieceMap_coe, setRestriction_coe]
  exact DFunLike.congr_fun (restriction_localizedMap (coverProduct x s) (coverProduct x t)
    (coverProduct_dvd 𝒜 x hx hst) f) z.val

def cochainMap (d : ℤ) (q : ℕ) : Cochain 𝒜 𝓜 x hx d q →+ Cochain 𝒜 𝓝 x hx d q where
  toFun c t := pieceMap 𝒜 𝓜 (coverProduct x (tupleSet t)) _
    (coverProduct_mem 𝒜 x hx (tupleSet t)) 𝓝 d f hf (c t)
  map_zero' := by funext t; exact map_zero _
  map_add' c b := by funext t; exact map_add _ _ _

theorem cochainMap_differential (d : ℤ) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    cochainMap 𝒜 𝓜 x hx 𝓝 f hf d (q + 1) (differential 𝒜 𝓜 x hx d c) =
      differential 𝒜 𝓝 x hx d (cochainMap 𝒜 𝓜 x hx 𝓝 f hf d q c) := by
  funext t
  simp only [cochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, differential,
    map_sum, map_zsmul, pieceMap_setRestriction]

theorem cochainMap_injective (d : ℤ) (q : ℕ) (hinj : Function.Injective f) :
    Function.Injective (cochainMap 𝒜 𝓜 x hx 𝓝 f hf d q) := by
  intro c b h
  funext t
  apply Subtype.ext
  have ht := congrArg Subtype.val (congrFun h t)
  exact (IsLocalizedModule.map_injective (Submonoid.powers (coverProduct x (tupleSet t)))
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) f hinj) ht

def globalPieceMap (d : ℤ) : 𝓜 d →+ 𝓝 d where
  toFun m := ⟨f m, hf d m m.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem augmentation_natural (d : ℤ) (m : 𝓜 d) :
    cochainMap 𝒜 𝓜 x hx 𝓝 f hf d 0 (augmentation 𝒜 𝓜 x hx d m) =
      augmentation 𝒜 𝓝 x hx d (globalPieceMap 𝓜 𝓝 f hf d m) := by
  funext t
  apply Subtype.ext
  change localizedMap (coverProduct x (tupleSet t)) f
      (fraction (coverProduct x (tupleSet t)) (m : M) 0) =
    fraction (coverProduct x (tupleSet t)) (f m) 0
  exact localizedMap_fraction _ f m 0

end Maps

section Exactness
variable {N P σN σP : Type*} [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  [SetLike σN N] [AddSubgroupClass σN N]
  [SetLike σP P] [AddSubgroupClass σP P]
  (𝓝 : ℤ → σN) (𝓟 : ℤ → σP)
  [SetLike.GradedSMul 𝒜 𝓝] [SetLike.GradedSMul 𝒜 𝓟]
  [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝] [DirectSum.Decomposition 𝓟]

theorem cochainMap_surjective (d : ℤ) (q : ℕ) (f : M →ₗ[R] N)
    (hf : ∀ i z, f (DirectSum.decompose 𝓜 z i : M) =
      (DirectSum.decompose 𝓝 (f z) i : N)) (hsurj : Function.Surjective f) :
    Function.Surjective (cochainMap 𝒜 𝓜 x hx 𝓝 f
      (preserves_of_compatible 𝓜 𝓝 f hf) d q) := by
  intro c
  have ht (t : Fin (q + 1) → J) := pieceMap_surjective 𝒜 𝓜
    (coverProduct x (tupleSet t)) _ (coverProduct_mem 𝒜 x hx (tupleSet t))
    𝓝 d f hf hsurj (c t)
  choose b hb using ht
  exact ⟨b, funext hb⟩

theorem cochainMap_exact (d : ℤ) (q : ℕ) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ i z, f (DirectSum.decompose 𝓜 z i : M) =
      (DirectSum.decompose 𝓝 (f z) i : N))
    (hg : ∀ i z, g (DirectSum.decompose 𝓝 z i : N) =
      (DirectSum.decompose 𝓟 (g z) i : P)) (hex : Function.Exact f g) :
    Function.Exact
      (cochainMap 𝒜 𝓜 x hx 𝓝 f (preserves_of_compatible 𝓜 𝓝 f hf) d q)
      (cochainMap 𝒜 𝓝 x hx 𝓟 g (preserves_of_compatible 𝓝 𝓟 g hg) d q) := by
  intro c
  have hlocal (t : Fin (q + 1) → J) := pieceMap_exact 𝒜 𝓜
    (coverProduct x (tupleSet t)) _ (coverProduct_mem 𝒜 x hx (tupleSet t))
    𝓝 𝓟 d f g hf hg hex
  constructor
  · intro hc
    have ht (t : Fin (q + 1) → J) := (hlocal t (c t)).mp (congrFun hc t)
    choose b hb using ht
    exact ⟨b, funext hb⟩
  · rintro ⟨b, rfl⟩
    funext t
    exact (hlocal t).apply_apply_eq_zero (b t)

end Exactness

end Cover

end
end PiExponent.GradedCech

end OAI
