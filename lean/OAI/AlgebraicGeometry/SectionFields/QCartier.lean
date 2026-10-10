import Mathlib
import OAI.AlgebraicGeometry.SectionFields.Constants

namespace OAI

/-! Rational Cartier divisors, pullback and exact principal presentations. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators
section

open Order TopologicalSpace

 
theorem ord_one (X : Scheme) [IsIntegral X] [IsNoetherian X] (x : X) :
    X.ord (1 : X.functionField) x = 0 := by
  simpa using X.ord_of_isUnit (U := ⊤) (f := 1) isUnit_one (x := x) trivial

theorem ord_inv (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u : X.functionField) (hu : u ≠ 0) (x : X) :
    X.ord u⁻¹ x = -X.ord u x := by
  have h := X.ord_mul (x := x) hu (inv_ne_zero hu)
  rw [mul_inv_cancel₀ hu, ord_one] at h
  omega

theorem ord_pow (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u : X.functionField) (hu : u ≠ 0) (n : ℕ) (x : X) :
    X.ord (u ^ n) x = (n : ℤ) * X.ord u x := by
  induction n with
  | zero => simp [ord_one]
  | succ n ih =>
    rw [pow_succ, X.ord_mul (pow_ne_zero _ hu) hu, ih]
    push_cast
    ring

theorem ord_zpow (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u : X.functionField) (hu : u ≠ 0) (n : ℤ) (x : X) :
    X.ord (u ^ n) x = n * X.ord u x := by
  cases n with
  | ofNat n => simpa using ord_pow X u hu n x
  | negSucc n =>
    rw [zpow_negSucc, ord_inv X _ (pow_ne_zero _ hu), ord_pow X u hu, Int.negSucc_eq]
    push_cast
    ring

theorem ord_div (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u v : X.functionField) (hu : u ≠ 0) (hv : v ≠ 0) (x : X) :
    X.ord (u / v) x = X.ord u x - X.ord v x := by
  rw [div_eq_mul_inv, X.ord_mul hu (inv_ne_zero hv), ord_inv X _ hv, sub_eq_add_neg]

 

theorem pullback_ord_zero_on
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] (U : Z.Opens) [Nonempty U]
    (u : Z.functionFieldˣ)
    (hord : ∀ z : Z, z ∈ U → coheight z = 1 → Z.ord (u : Z.functionField) z = 0)
    (x : X) (hx : f x ∈ U) :
    X.ord (functionFieldPullback f (u : Z.functionField)) x = 0 := by
  obtain ⟨s, hs⟩ := exists_section_unit_of_ord_eq_zero Z hNormal U u hord
  change Z.germToFunctionField U (s : Γ(Z, U)) = (u : Z.functionField) at hs
  rw [← hs, functionFieldPullback_germ]
  exact X.ord_of_isUnit (s.isUnit.map (f.app U).hom) hx

 

abbrev RationalWeilDivisor (X : Scheme) := PrimeDivisor X →₀ ℚ

 
noncomputable def rationalPrincipalDivisor (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u : X.functionFieldˣ) : RationalWeilDivisor X :=
  (principalDivisor X u).mapRange (Int.castRingHom ℚ) (by simp)

@[simp] theorem rationalPrincipalDivisor_apply (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u : X.functionFieldˣ) (p : PrimeDivisor X) :
    rationalPrincipalDivisor X u p = (X.ord (u : X.functionField) p.1 : ℚ) := rfl

 

def IsQCartier (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (D : RationalWeilDivisor X) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ z : X, ∃ U : X.Opens, z ∈ U ∧
    ∃ u : X.functionFieldˣ, ∀ p : PrimeDivisor X, p.1 ∈ U →
      (n : ℚ) * D p = (X.ord (u : X.functionField) p.1 : ℚ)


 

theorem pullback_local_equations_agree
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] (D : RationalWeilDivisor Z)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (U V : Z.Opens)
    (u v : Z.functionFieldˣ)
    (hu : ∀ q : PrimeDivisor Z, q.1 ∈ U →
      (n : ℚ) * D q = (Z.ord (u : Z.functionField) q.1 : ℚ))
    (hv : ∀ q : PrimeDivisor Z, q.1 ∈ V →
      (m : ℚ) * D q = (Z.ord (v : Z.functionField) q.1 : ℚ))
    (p : PrimeDivisor X) (hpU : f p.1 ∈ U) (hpV : f p.1 ∈ V) :
    (X.ord (functionFieldPullback f (u : Z.functionField)) p.1 : ℚ) / n =
      (X.ord (functionFieldPullback f (v : Z.functionField)) p.1 : ℚ) / m := by
  let W := U ⊓ V
  let : Nonempty W := ⟨⟨f p.1, hpU, hpV⟩⟩
  let w : Z.functionFieldˣ := u ^ m / v ^ n
  have hzero : ∀ z : Z, z ∈ W → coheight z = 1 → Z.ord (w : Z.functionField) z = 0 := by
    intro z hz hcodim
    have hrel : (m : ℤ) * Z.ord (u : Z.functionField) z =
        (n : ℤ) * Z.ord (v : Z.functionField) z := by
      have hq : (m : ℚ) * (Z.ord (u : Z.functionField) z : ℚ) =
          (n : ℚ) * (Z.ord (v : Z.functionField) z : ℚ) := by
        rw [← hu ⟨z, hcodim⟩ hz.1, ← hv ⟨z, hcodim⟩ hz.2]
        ring
      exact_mod_cast hq
    simp only [w, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    change Z.ord ((u : Z.functionField) ^ m / (v : Z.functionField) ^ n) z = 0
    rw [ord_div Z _ _ (pow_ne_zero _ (Units.ne_zero u)) (pow_ne_zero _ (Units.ne_zero v)),
      ord_pow Z _ (Units.ne_zero u), ord_pow Z _ (Units.ne_zero v), hrel, sub_self]
  have he := pullback_ord_zero_on hNormal f W w hzero p.1 ⟨hpU, hpV⟩
  have hfu : functionFieldPullback f (u : Z.functionField) ≠ 0 :=
    by simp
  have hfv : functionFieldPullback f (v : Z.functionField) ≠ 0 :=
    by simp
  simp only [w, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at he
  rw [map_div₀, map_pow, map_pow,
    ord_div X _ _ (pow_ne_zero _ hfu) (pow_ne_zero _ hfv),
    ord_pow X _ hfu, ord_pow X _ hfv, sub_eq_zero] at he
  apply (div_eq_div_iff (by exact_mod_cast hn.ne') (by exact_mod_cast hm.ne')).mpr
  norm_cast
  nlinarith only [he]


 
structure QCartierData (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (D : RationalWeilDivisor X) where
  index : ℕ
  index_pos : 0 < index
  chart : X → X.Opens
  mem_chart : ∀ x, x ∈ chart x
  equation : X → X.functionFieldˣ
  ord_eq : ∀ x (p : PrimeDivisor X), p.1 ∈ chart x →
    (index : ℚ) * D p = (X.ord (equation x : X.functionField) p.1 : ℚ)

noncomputable def IsQCartier.data {X : Scheme} [IsIntegral X] [IsNoetherian X]
    {D : RationalWeilDivisor X} (hD : IsQCartier X D) : QCartierData X D :=
  Classical.choice (by
    obtain ⟨n, hn, hloc⟩ := hD
    choose U hU u hu using hloc
    exact ⟨⟨n, hn, U, hU, u, hu⟩⟩)

noncomputable def QCartierData.pullbackCoeff
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    {D : RationalWeilDivisor Z} (c : QCartierData Z D)
    (f : X ⟶ Z) [IsDominant f] (p : PrimeDivisor X) : ℚ :=
  (X.ord (functionFieldPullback f (c.equation (f p.1) : Z.functionField)) p.1 : ℚ) / c.index

theorem QCartierData.pullbackCoeff_eq_local
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    {D : RationalWeilDivisor Z} (c : QCartierData Z D)
    (f : X ⟶ Z) [IsDominant f]
    (n : ℕ) (hn : 0 < n) (U : Z.Opens) (u : Z.functionFieldˣ)
    (hu : ∀ q : PrimeDivisor Z, q.1 ∈ U →
      (n : ℚ) * D q = (Z.ord (u : Z.functionField) q.1 : ℚ))
    (p : PrimeDivisor X) (hp : f p.1 ∈ U) :
    c.pullbackCoeff f p =
      (X.ord (functionFieldPullback f (u : Z.functionField)) p.1 : ℚ) / n := by
  exact pullback_local_equations_agree hNormal f D c.index n c.index_pos hn
    (c.chart (f p.1)) U (c.equation (f p.1)) u (c.ord_eq (f p.1)) hu p
      (c.mem_chart (f p.1)) hp

theorem QCartierData.pullbackCoeff_finite_support
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    {D : RationalWeilDivisor Z} (c : QCartierData Z D)
    (f : X ⟶ Z) [IsDominant f] :
    (Function.support (c.pullbackCoeff f)).Finite := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z : Z => (c.chart z : Set Z)) (fun z => (c.chart z).isOpen)
    (fun z _ => Set.mem_iUnion.mpr ⟨z, c.mem_chart z⟩)
  have hfin : (⋃ z ∈ t, Function.support (fun p : PrimeDivisor X =>
      X.ord (functionFieldPullback f (c.equation z : Z.functionField)) p.1)).Finite := by
    apply t.finite_toSet.biUnion
    intro z _
    apply finite_support_ord X
    simp
  apply hfin.subset
  intro p hp
  obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (f p.1)))
  refine Set.mem_iUnion₂.mpr ⟨z, hz, ?_⟩
  intro hz0
  change X.ord (functionFieldPullback f (c.equation z : Z.functionField)) p.1 = 0 at hz0
  apply hp
  rw [c.pullbackCoeff_eq_local hNormal f c.index c.index_pos (c.chart z) (c.equation z)
    (c.ord_eq z) p hpz, hz0]
  simp

 

noncomputable def pullbackQCartier
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] (D : RationalWeilDivisor Z) (hD : IsQCartier Z D) :
    RationalWeilDivisor X :=
  Finsupp.ofSupportFinite (hD.data.pullbackCoeff f)
    (hD.data.pullbackCoeff_finite_support hNormal f)

 

theorem pullbackQCartier_apply_of_local
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (n : ℕ) (hn : 0 < n) (U : Z.Opens) (u : Z.functionFieldˣ)
    (hu : ∀ q : PrimeDivisor Z, q.1 ∈ U →
      (n : ℚ) * D q = (Z.ord (u : Z.functionField) q.1 : ℚ))
    (p : PrimeDivisor X) (hp : f p.1 ∈ U) :
    pullbackQCartier hNormal f D hD p =
      (X.ord (functionFieldPullback f (u : Z.functionField)) p.1 : ℚ) / n :=
  hD.data.pullbackCoeff_eq_local hNormal f n hn U u hu p hp

theorem isQCartier_pullback
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] (D : RationalWeilDivisor Z) (hD : IsQCartier Z D) :
    IsQCartier X (pullbackQCartier hNormal f D hD) := by
  let c := hD.data
  refine ⟨c.index, c.index_pos, fun x => ?_⟩
  refine ⟨f ⁻¹ᵁ c.chart (f x), c.mem_chart (f x),
    Units.map (functionFieldPullback f).toMonoidHom (c.equation (f x)), ?_⟩
  intro p hp
  rw [pullbackQCartier_apply_of_local hNormal f D hD c.index c.index_pos
    (c.chart (f x)) (c.equation (f x)) (c.ord_eq (f x)) p hp]
  have hn : (c.index : ℚ) ≠ 0 := by exact_mod_cast c.index_pos.ne'
  field_simp
  rfl


 

theorem ord_pullback_eq_zero_of_mapsToGeneric
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X]
    (f : X ⟶ Z) [IsDominant f] (u : Z.functionFieldˣ)
    (x : X) (hx : f x = genericPoint Z) :
    X.ord (functionFieldPullback f (u : Z.functionField)) x = 0 := by
  obtain ⟨U, _, s, hU, hs, hu⟩ := AlgebraicGeometry.exists_isUnit_germ_eq (X := Z) _ (Units.ne_zero u)
  let := hU
  have hgen : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  rw [← hs, functionFieldPullback_germ]
  exact X.ord_of_isUnit (hu.map (f.app U).hom) (by simpa [hx] using hgen)

 

def IsVerticalRationalDivisor {X Z : Scheme} [IsIntegral Z]
    (f : X ⟶ Z) (D : RationalWeilDivisor X) : Prop :=
  ∀ p : PrimeDivisor X, D p ≠ 0 → f p.1 ≠ genericPoint Z

theorem isVertical_pullbackQCartier
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] (D : RationalWeilDivisor Z) (hD : IsQCartier Z D) :
    IsVerticalRationalDivisor f (pullbackQCartier hNormal f D hD) := by
  intro p hp hgen
  apply hp
  change hD.data.pullbackCoeff f p = 0
  unfold QCartierData.pullbackCoeff
  rw [ord_pullback_eq_zero_of_mapsToGeneric f _ p.1 hgen]
  simp

theorem isQCartier_principal (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u : X.functionFieldˣ) : IsQCartier X (rationalPrincipalDivisor X u) := by
  refine ⟨1, Nat.one_pos, fun x => ⟨⊤, trivial, u, ?_⟩⟩
  intro p _
  simp

theorem pullbackQCartier_principal
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] (u : Z.functionFieldˣ)
    (hD : IsQCartier Z (rationalPrincipalDivisor Z u)) :
    pullbackQCartier hNormal f (rationalPrincipalDivisor Z u) hD =
      rationalPrincipalDivisor X (Units.map (functionFieldPullback f).toMonoidHom u) := by
  ext p
  rw [pullbackQCartier_apply_of_local hNormal f _ hD 1 Nat.one_pos ⊤ u
    (fun _ _ => by simp) p trivial]
  simp

theorem isQCartier_add
    {X : Scheme} [IsIntegral X] [IsNoetherian X]
    {D E : RationalWeilDivisor X} (hD : IsQCartier X D) (hE : IsQCartier X E) :
    IsQCartier X (D + E) := by
  obtain ⟨n, hn, hD⟩ := hD
  obtain ⟨m, hm, hE⟩ := hE
  refine ⟨n * m, Nat.mul_pos hn hm, fun x => ?_⟩
  obtain ⟨U, hxU, u, hu⟩ := hD x
  obtain ⟨V, hxV, v, hv⟩ := hE x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, u ^ m * v ^ n, fun p hp => ?_⟩
  simp only [Finsupp.add_apply, Units.val_mul, Units.val_pow_eq_pow_val,
    X.ord_mul (pow_ne_zero _ (Units.ne_zero u)) (pow_ne_zero _ (Units.ne_zero v)),
    ord_pow X _ (Units.ne_zero u), ord_pow X _ (Units.ne_zero v)]
  push_cast
  rw [← hu p hp.1, ← hv p hp.2]
  ring

theorem isQCartier_smul
    {X : Scheme} [IsIntegral X] [IsNoetherian X]
    {D : RationalWeilDivisor X} (hD : IsQCartier X D) (q : ℚ) :
    IsQCartier X (q • D) := by
  obtain ⟨n, hn, hD⟩ := hD
  refine ⟨n * q.den, Nat.mul_pos hn q.den_pos, fun x => ?_⟩
  obtain ⟨U, hx, u, hu⟩ := hD x
  refine ⟨U, hx, u ^ q.num, fun p hp => ?_⟩
  simp only [Finsupp.smul_apply, smul_eq_mul, Units.val_zpow_eq_zpow_val,
    ord_zpow X _ (Units.ne_zero u)]
  push_cast
  rw [← hu p hp]
  have hq : (q.den : ℚ) * q = q.num := by
    simp [mul_comm]
  calc (n : ℚ) * q.den * (q * D p) = n * ((q.den : ℚ) * q) * D p := by ring
    _ = (q.num : ℚ) * ((n : ℚ) * D p) := by rw [hq]; ring


theorem pullbackQCartier_add
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] {D E : RationalWeilDivisor Z}
    (hD : IsQCartier Z D) (hE : IsQCartier Z E) (hDE : IsQCartier Z (D + E)) :
    pullbackQCartier hNormal f (D + E) hDE =
      pullbackQCartier hNormal f D hD + pullbackQCartier hNormal f E hE := by
  ext p
  let c := hD.data
  let e := hE.data
  let U := c.chart (f p.1)
  let V := e.chart (f p.1)
  let u := c.equation (f p.1)
  let v := e.equation (f p.1)
  have hu := c.ord_eq (f p.1)
  have hv := e.ord_eq (f p.1)
  have huv : ∀ q : PrimeDivisor Z, q.1 ∈ U ⊓ V →
      ((c.index * e.index : ℕ) : ℚ) * (D + E) q =
        (Z.ord ((u ^ e.index * v ^ c.index : Z.functionFieldˣ) : Z.functionField) q.1 : ℚ) := by
    intro q hq
    simp only [Finsupp.add_apply, Units.val_mul, Units.val_pow_eq_pow_val,
      Z.ord_mul (pow_ne_zero _ (Units.ne_zero u)) (pow_ne_zero _ (Units.ne_zero v)),
      ord_pow Z _ (Units.ne_zero u), ord_pow Z _ (Units.ne_zero v)]
    push_cast
    rw [← hu q hq.1, ← hv q hq.2]
    ring
  rw [Finsupp.add_apply,
    pullbackQCartier_apply_of_local hNormal f (D + E) hDE (c.index * e.index)
      (Nat.mul_pos c.index_pos e.index_pos) (U ⊓ V) (u ^ e.index * v ^ c.index) huv p
      ⟨c.mem_chart _, e.mem_chart _⟩,
    pullbackQCartier_apply_of_local hNormal f D hD c.index c.index_pos U u hu p (c.mem_chart _),
    pullbackQCartier_apply_of_local hNormal f E hE e.index e.index_pos V v hv p (e.mem_chart _)]
  have hfu : functionFieldPullback f (u : Z.functionField) ≠ 0 :=
    by simp
  have hfv : functionFieldPullback f (v : Z.functionField) ≠ 0 :=
    by simp
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
    X.ord_mul (pow_ne_zero _ hfu) (pow_ne_zero _ hfv), ord_pow X _ hfu, ord_pow X _ hfv]
  have hn : (c.index : ℚ) ≠ 0 := by exact_mod_cast c.index_pos.ne'
  have hm : (e.index : ℚ) ≠ 0 := by exact_mod_cast e.index_pos.ne'
  push_cast
  field_simp

theorem pullbackQCartier_smul
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] {D : RationalWeilDivisor Z}
    (hD : IsQCartier Z D) (q : ℚ) (hqD : IsQCartier Z (q • D)) :
    pullbackQCartier hNormal f (q • D) hqD = q • pullbackQCartier hNormal f D hD := by
  ext p
  let c := hD.data
  let U := c.chart (f p.1)
  let u := c.equation (f p.1)
  have hu := c.ord_eq (f p.1)
  have hq : (q.den : ℚ) * q = q.num := by
    simp [mul_comm]
  have hqu : ∀ r : PrimeDivisor Z, r.1 ∈ U →
      ((c.index * q.den : ℕ) : ℚ) * (q • D) r =
        (Z.ord ((u ^ q.num : Z.functionFieldˣ) : Z.functionField) r.1 : ℚ) := by
    intro r hr
    simp only [Finsupp.smul_apply, smul_eq_mul, Units.val_zpow_eq_zpow_val,
      ord_zpow Z _ (Units.ne_zero u)]
    push_cast
    rw [← hu r hr]
    calc (c.index : ℚ) * q.den * (q * D r) = c.index * ((q.den : ℚ) * q) * D r := by ring
      _ = (q.num : ℚ) * ((c.index : ℚ) * D r) := by rw [hq]; ring
  rw [Finsupp.smul_apply,
    pullbackQCartier_apply_of_local hNormal f (q • D) hqD (c.index * q.den)
      (Nat.mul_pos c.index_pos q.den_pos) U (u ^ q.num) hqu p (c.mem_chart _),
    pullbackQCartier_apply_of_local hNormal f D hD c.index c.index_pos U u hu p (c.mem_chart _)]
  have hfu : functionFieldPullback f (u : Z.functionField) ≠ 0 :=
    by simp
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, ord_zpow X _ hfu, smul_eq_mul]
  have hn : (c.index : ℚ) ≠ 0 := by exact_mod_cast c.index_pos.ne'
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  push_cast
  rw [← hq]
  field_simp

theorem rationalPrincipalDivisor_mul (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u v : X.functionFieldˣ) :
    rationalPrincipalDivisor X (u * v) =
      rationalPrincipalDivisor X u + rationalPrincipalDivisor X v := by
  ext p
  simp [X.ord_mul (Units.ne_zero u) (Units.ne_zero v)]

theorem rationalPrincipalDivisor_div (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u v : X.functionFieldˣ) :
    rationalPrincipalDivisor X (u / v) =
      rationalPrincipalDivisor X u - rationalPrincipalDivisor X v := by
  ext p
  simp [ord_div X _ _ (Units.ne_zero u) (Units.ne_zero v)]

theorem rationalPrincipalDivisor_pow (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u : X.functionFieldˣ) (n : ℕ) :
    rationalPrincipalDivisor X (u ^ n) = (n : ℚ) • rationalPrincipalDivisor X u := by
  ext p
  simp [ord_pow X _ (Units.ne_zero u)]

end

 

theorem exact_presentation_of_vertical_principalization
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hXNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hZNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (p a : ℕ) (hp : 0 < p) (ha : 0 < a) (hpa : p ∣ a)
    (ψ φ : X.functionFieldˣ)
    (hvertical : IsVerticalRationalDivisor f ((p : ℚ) • A + rationalPrincipalDivisor X ψ))
    (hlinear : (a : ℚ) • A + rationalPrincipalDivisor X φ =
      pullbackQCartier hZNormal f ((a : ℚ) • D) (isQCartier_smul hD (a : ℚ))) :
    ∃ (h : Z.functionFieldˣ)
      (hDZ : IsQCartier Z (D + (a : ℚ)⁻¹ • rationalPrincipalDivisor Z h)),
      A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ =
        pullbackQCartier hZNormal f (D + (a : ℚ)⁻¹ • rationalPrincipalDivisor Z h) hDZ := by
  let b := a / p
  have hbp : (b : ℚ) * (p : ℚ) = (a : ℚ) := by
    exact_mod_cast Nat.div_mul_cancel hpa
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hlin : (a : ℚ) • A + rationalPrincipalDivisor X φ =
      (a : ℚ) • pullbackQCartier hZNormal f D hD :=
    hlinear.trans (pullbackQCartier_smul hZNormal f hD (a : ℚ) _)
  let w : X.functionFieldˣ := ψ ^ b / φ
  have hwdiv : rationalPrincipalDivisor X w =
      (b : ℚ) • rationalPrincipalDivisor X ψ - rationalPrincipalDivisor X φ := by
    change rationalPrincipalDivisor X (ψ ^ b / φ) = _
    rw [rationalPrincipalDivisor_div, rationalPrincipalDivisor_pow]
  have hwvertical : IsVerticalDivisor f (principalDivisor X w) := by
    intro r hr hgen
    have hv0 : ((p : ℚ) • A + rationalPrincipalDivisor X ψ) r = 0 := by
      by_contra hn
      exact hvertical r hn hgen
    have hd0 : pullbackQCartier hZNormal f D hD r = 0 := by
      by_contra hn
      exact isVertical_pullbackQCartier hZNormal f D hD r hn hgen
    have hl := congrArg (fun E : RationalWeilDivisor X => E r) hlin
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hd0, mul_zero] at hl hv0
    have hw0 : rationalPrincipalDivisor X w r = 0 := by
      rw [hwdiv, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
      have hψ : rationalPrincipalDivisor X ψ r = -(p : ℚ) * A r := by linarith
      have hφ : rationalPrincipalDivisor X φ r = -(a : ℚ) * A r := by linarith
      rw [hψ, hφ]
      calc (b : ℚ) * (-(p : ℚ) * A r) - -(a : ℚ) * A r =
          ((a : ℚ) - (b : ℚ) * p) * A r := by ring
        _ = 0 := by rw [hbp, sub_self, zero_mul]
    apply hr
    change ((principalDivisor X w r : ℤ) : ℚ) = 0 at hw0
    exact_mod_cast hw0
  obtain ⟨h, hh⟩ := rational_function_descends_of_vertical_divisor hXNormal f w hwvertical
  have hunit : Units.map (functionFieldPullback f).toMonoidHom h = w := Units.ext hh
  let hH := isQCartier_principal Z h
  let hscaled := isQCartier_smul hH ((a : ℚ)⁻¹)
  let hDZ := isQCartier_add hD hscaled
  refine ⟨h, hDZ, ?_⟩
  rw [pullbackQCartier_add hZNormal f hD hscaled hDZ,
    pullbackQCartier_smul hZNormal f hH ((a : ℚ)⁻¹) hscaled,
    pullbackQCartier_principal hZNormal f h hH, hunit, hwdiv]
  ext r
  have hl := congrArg (fun E : RationalWeilDivisor X => E r) hlin
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul] at hl ⊢
  have hb : (b : ℚ) = (a : ℚ) / p := (eq_div_iff hpq).mpr hbp
  rw [hb]
  field_simp
  linear_combination (p : ℚ) * hl

 

def RationallyLinearlyEquivalent (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (D E : RationalWeilDivisor X) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ u : X.functionFieldˣ,
    (n : ℚ) • (D - E) = rationalPrincipalDivisor X u

 

theorem relative_exact_presentation_of_vertical_principalization
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hXNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hZNormal : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c]
    (A : RationalWeilDivisor X) (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (p a : ℕ) (hp : 0 < p) (ha : 0 < a) (hpa : p ∣ a)
    (ψ φ : X.functionFieldˣ)
    (hvertical : IsVerticalRationalDivisor f ((p : ℚ) • A + rationalPrincipalDivisor X ψ))
    (hlinear : (a : ℚ) • A + rationalPrincipalDivisor X φ =
      pullbackQCartier hZNormal f ((a : ℚ) • D) (isQCartier_smul hD (a : ℚ))) :
    ∃ (DZ : RationalWeilDivisor Z) (hDZ : IsQCartier Z DZ),
      RationallyLinearlyEquivalent Z DZ D ∧
      A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ = pullbackQCartier hZNormal f DZ hDZ := by
  obtain ⟨h, hDZ, heq⟩ := exact_presentation_of_vertical_principalization
    hXNormal hZNormal f A D hD p a hp ha hpa ψ φ hvertical hlinear
  refine ⟨_, hDZ, ⟨a, ha, h, ?_⟩, heq⟩
  rw [add_sub_cancel_left, smul_smul]
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [mul_inv_cancel₀ haq, one_smul]

theorem principalDivisor_div (X : Scheme) [IsIntegral X] [IsNoetherian X]
    (u v : X.functionFieldˣ) :
    principalDivisor X (u / v) = principalDivisor X u - principalDivisor X v := by
  ext p
  change X.ord ((u / v : X.functionFieldˣ) : X.functionField) p.1 =
    X.ord (u : X.functionField) p.1 - X.ord (v : X.functionField) p.1
  simpa only [Units.val_div_eq_div_val] using
    ord_div X _ _ (Units.ne_zero u) (Units.ne_zero v) p.1

theorem principalDivisor_constant
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) (c : Kˣ) :
    principalDivisor X (Units.map (constantToFunctionField K f).toMonoidHom c) = 0 := by
  ext p
  change X.ord (X.germToFunctionField ⊤
    (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) (c : K))) p.1 = 0
  exact X.ord_of_isUnit (c.isUnit.map ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom) trivial

attribute [local instance] Units.mulDistribMulActionRight

 

theorem invariant_rescaling_of_conjugate_divisor_eq
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of L)) [UniversallyClosed f] [GeometricallyIntegral f]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    [MulSemiringAction (Gal(L/K)) X.functionField]
    (hsemilinear : ∀ (σ : Gal(L/K)) (c : L),
      σ • constantToFunctionField L f c = constantToFunctionField L f (σ c))
    (u : X.functionFieldˣ)
    (hdiv : ∀ σ : Gal(L/K), principalDivisor X (σ • u) = principalDivisor X u) :
    ∃ c : Lˣ, let v := u / Units.map (constantToFunctionField L f).toMonoidHom c
      (∀ σ : Gal(L/K), σ • v = v) ∧ principalDivisor X v = principalDivisor X u := by
  classical
  let C : Lˣ →* X.functionFieldˣ := Units.map (constantToFunctionField L f).toMonoidHom
  have hCinjective : Function.Injective C :=
    Units.map_injective (constantToFunctionField L f).injective
  have hCsemi (σ : Gal(L/K)) (c : Lˣ) : σ • C c = C (σ • c) := by
    apply Units.ext
    exact hsemilinear σ c
  have hzero (σ : Gal(L/K)) : principalDivisor X (σ • u / u) = 0 := by
    rw [principalDivisor_div, hdiv, sub_self]
  choose c hc using fun σ : Gal(L/K) =>
    rational_function_constant_of_divisor_zero L f hNormal (σ • u / u) (hzero σ)
  have hcu (σ : Gal(L/K)) : C (c σ) = σ • u / u := Units.ext (hc σ)
  have hcocycle : groupCohomology.IsMulCocycle₁ c := by
    intro σ τ
    apply hCinjective
    rw [map_mul, ← hCsemi, hcu, hcu, smul_div', hcu, mul_smul]
    exact (div_mul_div_cancel _ _ _).symm
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units c hcocycle
  refine ⟨β, ?_, ?_⟩
  · intro σ
    have he := congrArg C (hβ σ)
    rw [_root_.map_div, ← hCsemi, hcu] at he
    change σ • (u / C β) = u / C β
    rw [smul_div']
    apply div_eq_div_iff_mul_eq_mul.mpr
    have hh := div_eq_div_iff_mul_eq_mul.mp he
    simpa only [mul_comm] using hh.symm
  · change principalDivisor X (u / C β) = principalDivisor X u
    rw [principalDivisor_div, principalDivisor_constant, sub_zero]

end RelativeDenominators
end

end OAI
