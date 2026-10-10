import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.AmpleGeneration
import OAI.AlgebraicGeometry.NumericalDimension.LocalKltMembers

namespace OAI

/-! Divisor Presheaves. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin

namespace NumericalDimensionOne

theorem uniform_ample_errors
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [StalkwiseNormal X] [CompactSpace X]
    (A₀ A : WeilDivisor X) (B : QWeilDivisor X)
    (hA₀ : IsAmpleDivisor A₀) (hA : IsCartierDivisor A)
    (hgen : ∀ x : X, IsGeneratedAt A x) (hB : IsQCartierDivisor B) :
    ∃ η : ℚ, 0 < η ∧ ∀ ε : ℚ, 0 ≤ ε → ε < η →
      ∀ r i : ℕ, i ≤ r → IsAmpleQDivisor
        (rationalWeilDivisor A₀ + (r-i) • rationalWeilDivisor A - ε • B) := by
  obtain ⟨b,hb,D,hD,hBD⟩ := hB
  obtain ⟨N,hN⟩ := ample_eventual_cartier_twist (-D) A₀ (isCartierDivisor_neg hD) hA₀
  let T := N+1
  let G : WeilDivisor X := -D + T • A₀
  have hG := hN T (by dsimp [T]; omega)
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hTQ : (0 : ℚ) < T := by dsimp [T]; positivity
  refine ⟨b/(T+1),div_pos hbQ (by positivity),?_⟩
  intro ε hε hεη r i _hi
  let q : ℚ := ε/b
  let u : ℕ := q.num.toNat
  let v : ℕ := q.den
  have hq : 0 ≤ q := div_nonneg hε hbQ.le
  have hv : 0 < v := q.den_pos
  have hvQ : (0 : ℚ) < v := by exact_mod_cast hv
  have hu : (q.num : ℚ) = u := by
    dsimp [u]
    exact_mod_cast (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)).symm
  have hqeq : q = (u : ℚ)/v := by rw [← hu]; exact (Rat.num_div_den q).symm
  have hve : (v : ℚ)*ε = u*b := by
    have h := hqeq
    dsimp [q] at h
    field_simp at h
    nlinarith
  have huT : u*T < v := by
    have he : ε*(T+1) < b := (lt_div_iff₀ (by positivity : (0 : ℚ) < T+1)).mp hεη
    have hεT : ε*T < b := by nlinarith
    have he' := mul_lt_mul_of_pos_left hεT hvQ
    have huTQ : (u : ℚ)*T < v := by nlinarith
    exact_mod_cast huTQ
  have hU : 0 < v-u*T := Nat.sub_pos_of_lt huT
  let C : WeilDivisor X := (v-u*T) • A₀ + (u • G + (v*(r-i)) • A)
  have hCamp : IsAmpleDivisor C := by
    apply ample_add_generated (isAmpleDivisor_nsmul hA₀ hU)
    · exact isCartierDivisor_add
        ((cartierDivisors (X := X)).nsmul_mem hG.2.1 u)
        ((cartierDivisors (X := X)).nsmul_mem hA _)
    · intro x
      exact ((hG.1 x).nsmul u).add ((hgen x).nsmul (v*(r-i)))
  refine ⟨v,hv,C,hCamp,?_⟩
  ext p
  have hBDp : (b : ℚ) * B p = (D p : ℚ) := DFunLike.congr_fun hBD p
  change (v : ℚ) * ((A₀ p : ℚ) + (r-i) • (A p : ℚ) - ε * B p) = (C p : ℚ)
  dsimp [C,G]
  simp only [nsmul_eq_mul,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_neg,
    Nat.cast_sub huT.le,Nat.cast_mul,Int.cast_sub]
  have hp : (v : ℚ)*ε*B p = u*(D p : ℚ) := by
    rw [hve,mul_assoc,hBDp]
  nlinarith only [hp]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin

namespace NumericalDimensionOne

def IsKltBoundaryOn {n : ℕ} (Y : CanonicalModel n)
    (U : Y.scheme.Opens) (Δ : QWeilDivisor Y.scheme) : Prop :=
  0 ≤ Δ ∧ IsQCartierDivisor (rationalWeilDivisor Y.canonical + Δ) ∧
  ∀ W : ComplexProjectiveVariety, IsSmoothNfold W n →
    ∀ f : W.scheme ⟶ Y.scheme, ∀ (_ : IsDominant f),
      IsProper f → IsBirationalMorphism f →
      ∀ hf : f ≫ Y.structureMap = W.structureMap,
        ∀ KW : WeilDivisor W.scheme,
          IsCanonicalDivisorOf (.of ℂ) W.structureMap n
            (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap f hf n Y.form) KW →
          ∀ P : QWeilDivisor W.scheme,
            IsQCartierPullback f (rationalWeilDivisor Y.canonical + Δ) P →
            ∀ p : PrimeDivisor W.scheme, f p.1 ∈ U →
              -1 < (rationalWeilDivisor KW - P) p
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter

namespace NumericalDimensionOne
section RationalPrincipalAmple
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
lemma principalWeilDivisor_zpow {f : X.functionField} (hf : f ≠ 0) (z : ℤ) :
    principalWeilDivisor (f ^ z) = z • principalWeilDivisor f := by
  cases z with
  | ofNat n => simpa using principalWeilDivisor_pow hf n
  | negSucc n =>
    rw [zpow_negSucc, principalWeilDivisor_inv (pow_ne_zero _ hf),
      principalWeilDivisor_pow hf]
    simp

lemma isAmpleQDivisor_add_rational_principal {Q : QWeilDivisor X}
    (hQ : IsAmpleQDivisor Q) (t : ℚ) {f : X.functionField} (hf : f ≠ 0) :
    IsAmpleQDivisor (Q + t • rationalWeilDivisor (principalWeilDivisor f)) := by
  obtain ⟨n,hn,D,hD,hDQ⟩ := hQ
  have htden : 0 < t.den := t.den_pos
  let C : WeilDivisor X := t.den • D + principalWeilDivisor (f ^ ((n : ℤ)*t.num))
  have hC : IsAmpleDivisor C := isAmpleDivisor_add_principal
    (isAmpleDivisor_nsmul hD htden) (zpow_ne_zero _ hf)
  refine ⟨t.den*n,Nat.mul_pos htden hn,C,hC,?_⟩
  ext p
  have hp : (n : ℚ) * Q p = (D p : ℚ) := DFunLike.congr_fun hDQ p
  have ht : (t.den : ℚ)*t = t.num := by
    have h := (eq_div_iff (Nat.cast_ne_zero.mpr t.den_ne_zero)).mp (Rat.num_div_den t).symm
    simpa only [mul_comm] using h
  change ((t.den*n : ℕ) : ℚ) * (Q p + t * (principalWeilDivisor f p : ℚ)) = (C p : ℚ)
  change ((t.den*n : ℕ) : ℚ) * (Q p + t * (principalWeilDivisor f p : ℚ)) =
    ((t.den • D + principalWeilDivisor (f ^ ((n : ℤ)*t.num))) p : ℚ)
  rw [principalWeilDivisor_zpow hf]
  simp only [Finsupp.add_apply,Finsupp.smul_apply,Int.cast_add,Int.cast_mul,
    Int.cast_natCast,nsmul_eq_mul,zsmul_eq_mul,Nat.cast_mul]
  calc
    _ = (t.den : ℚ)*((n : ℚ)*Q p) + n*((t.den : ℚ)*t)*(principalWeilDivisor f p : ℚ) := by ring
    _ = _ := by rw [hp,ht]; simp only [Int.cast_id]
end RationalPrincipalAmple
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter

namespace NumericalDimensionOne

theorem exists_fixed_twist_subunit_boundaries
    {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (L B : QWeilDivisor Y.scheme) (hB : IsQCartierDivisor B)
    (A A₀ : WeilDivisor Y.scheme) (hA : IsCartierDivisor A)
    (hAgen : ∀ x : Y.scheme, IsGeneratedAt A x) (hA₀ : IsAmpleDivisor A₀)
    (r d : ℕ) (_hd : 0 < d) (LD : WeilDivisor Y.scheme) (hLD : IsCartierDivisor LD)
    (hLd : (d : ℚ) • L = rationalWeilDivisor LD)
    (t : ℕ → ℚ) (ht : ∀ j, 0 < t j)
    (ht0 : Tendsto (fun j => (t j : ℝ)) atTop (nhds 0))
    (dj : ℕ → ℕ) (hdj : ∀ j, 0 < dj j)
    (D : ℕ → WeilDivisor Y.scheme) (hD : ∀ j, IsCartierDivisor (D j))
    (hDj : ∀ j, (dj j : ℚ) • (L + t j • B) = rationalWeilDivisor (D j))
    (U : ℕ → Y.scheme.Opens) (hU : ∀ j, Nonempty (U j))
    (hgen : ∀ j x, x ∈ U j → IsGeneratedAt (D j) x) :
    ∃ P : WeilDivisor Y.scheme, IsCartierDivisor P ∧
      P = Y.canonical + r • A + A₀ ∧
      ∀ m : ℕ, 0 < m → d ∣ m →
        ∃ Lm : WeilDivisor Y.scheme, IsCartierDivisor Lm ∧
          rationalWeilDivisor Lm = (m : ℚ) • L ∧
          ∃ j k : ℕ, dj j ∣ k ∧ m < k ∧
            ∃ E : WeilDivisor Y.scheme, IsCartierDivisor E ∧
              rationalWeilDivisor E = (k : ℚ) • (L + t j • B) ∧
              ∃ F : Y.scheme.functionField, F ≠ 0 ∧ IsDivisorSection E F ∧
                let R := ((m : ℚ)/k) • rationalWeilDivisor (E + principalWeilDivisor F)
                IsKltBoundaryOn Y (U j) R ∧
                ∀ i : ℕ, i ≤ r → IsAmpleQDivisor
                  (rationalWeilDivisor (Lm + P - i • A - Y.canonical) - R) := by
  let : StalkwiseNormal Y.scheme := smoothNormal Y.toComplexProjectiveVariety hY
  have hK := canonicalModel_isCartier Y hY
  let P := Y.canonical + r • A + A₀
  have hP : IsCartierDivisor P := isCartierDivisor_add
    (isCartierDivisor_add hK ((cartierDivisors (X := Y.scheme)).nsmul_mem hA r)) hA₀.1
  obtain ⟨η,hη,hamp⟩ := uniform_ample_errors A₀ A B hA₀ hA hAgen hB
  refine ⟨P,hP,rfl,?_⟩
  intro m hm hdm
  obtain ⟨a,ha⟩ := hdm
  let Lm := a • LD
  have hLm : IsCartierDivisor Lm := (cartierDivisors (X := Y.scheme)).nsmul_mem hLD a
  have hLmQ : rationalWeilDivisor Lm = (m : ℚ) • L := by
    change rationalWeilDivisor (a • LD) = _
    rw [rationalWeilDivisor_nsmul,← hLd,smul_smul,ha,Nat.cast_mul,mul_comm]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hηR : (0 : ℝ) < η := by exact_mod_cast hη
  have hsmall : ∀ᶠ j in atTop, (t j : ℝ) < (η : ℝ)/(m : ℝ) :=
    ht0.eventually (gt_mem_nhds (div_pos hηR hmR))
  obtain ⟨j,hj⟩ := hsmall.exists
  have hmt : (m : ℚ)*t j < η := by
    have hh := (lt_div_iff₀ hmR).mp hj
    have hh' : (m : ℝ)*(t j : ℝ) < (η : ℝ) := by nlinarith
    exact_mod_cast hh'
  let k := dj j * (m+1)
  have hmk : m < k := by
    have h := hdj j
    dsimp [k]
    nlinarith
  have hk : (0 : ℚ) < k := by exact_mod_cast (lt_trans hm hmk)
  let E := (m+1) • D j
  have hE : IsCartierDivisor E := (cartierDivisors (X := Y.scheme)).nsmul_mem (hD j) (m+1)
  have hEQ : rationalWeilDivisor E = (k : ℚ) • (L + t j • B) := by
    change rationalWeilDivisor ((m+1) • D j) = _
    rw [rationalWeilDivisor_nsmul,← hDj j,smul_smul]
    dsimp [k]
    rw [Nat.cast_mul,mul_comm]
  have hEgen : ∀ x : Y.scheme, x ∈ U j → IsGeneratedAt E x := by
    intro x hx
    exact (hgen j x hx).nsmul (m+1)
  have hε : 0 ≤ (m : ℚ)/k := div_nonneg (by positivity) hk.le
  have hε1 : (m : ℚ)/k < 1 := by
    apply (div_lt_one hk).mpr
    exact_mod_cast hmk
  obtain ⟨F,hF,hsec,hklt⟩ := exists_effective_locally_klt_member Y hY E hE
    (U j) (hU j) hEgen ((m : ℚ)/k) hε hε1
  refine ⟨Lm,hLm,hLmQ,j,k,⟨m+1,rfl⟩,hmk,E,hE,hEQ,F,hF,hsec,hklt,?_⟩
  intro i hi
  have hbase := hamp ((m : ℚ)*t j) (mul_nonneg (by positivity) (ht j).le) hmt r i hi
  have hlinear := isAmpleQDivisor_add_rational_principal hbase (-((m : ℚ)/k)) hF
  convert hlinear using 1
  ext p
  have hLp : (Lm p : ℚ) = (m : ℚ)*L p := DFunLike.congr_fun hLmQ p
  have hEp : (E p : ℚ) = (k : ℚ)*(L p + t j*B p) := DFunLike.congr_fun hEQ p
  change ((Lm + P - i • A - Y.canonical) p : ℚ) -
    ((m : ℚ)/k)*((E + principalWeilDivisor F) p : ℚ) = _
  change ((Lm + (Y.canonical + r • A + A₀) - i • A - Y.canonical) p : ℚ) -
    ((m : ℚ)/k)*((E + principalWeilDivisor F) p : ℚ) =
    (A₀ p : ℚ) + (r-i) • (A p : ℚ) - ((m : ℚ)*t j)*B p +
      (-((m : ℚ)/k))*(principalWeilDivisor F p : ℚ)
  simp only [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply,
    Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast,nsmul_eq_mul,
    Nat.cast_sub hi]
  rw [hLp,hEp]
  field_simp [ne_of_gt hk]
  ring
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

def MultiplierOrderCondition (p : PrimeDivisor X) (d : ℚ)
    (a : X.presheaf.stalk p.1) : Prop :=
  algebraMap (X.presheaf.stalk p.1) X.functionField a = 0 ∨
    -1 < (X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField a) p.1 : ℚ) + d

lemma multiplierOrderCondition_add (p : PrimeDivisor X) (d : ℚ)
    {a b : X.presheaf.stalk p.1}
    (ha : MultiplierOrderCondition p d a) (hb : MultiplierOrderCondition p d b) :
    MultiplierOrderCondition p d (a+b) := by
  unfold MultiplierOrderCondition at *
  rw [map_add]
  rcases ha with ha | ha
  · simpa only [ha,zero_add] using hb
  rcases hb with hb | hb
  · simpa only [hb,add_zero] using Or.inr ha
  by_cases hab : algebraMap (X.presheaf.stalk p.1) X.functionField a +
      algebraMap (X.presheaf.stalk p.1) X.functionField b = 0
  · exact Or.inl hab
  right
  let := dvr_at_prime_divisor p
  have hh := X.ord_add (x := p.1) hab
  by_cases hl : X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField a) p.1 ≤
      X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField b) p.1
  · rw [min_eq_left hl] at hh
    have hq : (X.ord (algebraMap _ _ a) p.1 : ℚ) ≤
        (X.ord (algebraMap _ _ a + algebraMap _ _ b) p.1 : ℚ) := by exact_mod_cast hh
    linarith
  · rw [min_eq_right (le_of_not_ge hl)] at hh
    have hq : (X.ord (algebraMap _ _ b) p.1 : ℚ) ≤
        (X.ord (algebraMap _ _ a + algebraMap _ _ b) p.1 : ℚ) := by exact_mod_cast hh
    linarith

lemma multiplierOrderCondition_mul (p : PrimeDivisor X) (d : ℚ)
    (a : X.presheaf.stalk p.1) {b : X.presheaf.stalk p.1}
    (hb : MultiplierOrderCondition p d b) : MultiplierOrderCondition p d (a*b) := by
  unfold MultiplierOrderCondition at *
  rw [map_mul]
  by_cases ha : algebraMap (X.presheaf.stalk p.1) X.functionField a = 0
  · exact Or.inl (by rw [ha,zero_mul])
  rcases hb with hb | hb
  · exact Or.inl (by rw [hb,mul_zero])
  by_cases hb0 : algebraMap (X.presheaf.stalk p.1) X.functionField b = 0
  · exact Or.inl (by rw [hb0,mul_zero])
  right
  rw [X.ord_mul ha hb0]
  have hn := (ord_nonnegative_iff_regular p _ ha).mpr ⟨a,rfl⟩
  have hnq : (0 : ℚ) ≤ (X.ord (algebraMap _ _ a) p.1 : ℚ) := by exact_mod_cast hn
  push_cast
  linarith

noncomputable def multiplierValuationIdeal (p : PrimeDivisor X) (d : ℚ) :
    Ideal (X.presheaf.stalk p.1) where
  carrier := {a | MultiplierOrderCondition p d a}
  zero_mem' := Or.inl (map_zero _)
  add_mem' := multiplierOrderCondition_add p d
  smul_mem' := multiplierOrderCondition_mul p d
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

theorem multiplierValuationIdeal_eq_top (p : PrimeDivisor X) (d : ℚ) :
    multiplierValuationIdeal p d = ⊤ ↔ -1 < d := by
  rw [Ideal.eq_top_iff_one]
  change MultiplierOrderCondition p d 1 ↔ _
  simp [MultiplierOrderCondition,order_one]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter

namespace NumericalDimensionOne

structure MultiplierDivisorialTest {n : ℕ} (Y : CanonicalModel n)
    (Δ : QWeilDivisor Y.scheme) where
  model : ComplexProjectiveVariety
  smooth : IsSmoothNfold model n
  map : model.scheme ⟶ Y.scheme
  dominant : IsDominant map
  proper : IsProper map
  birational : IsBirationalMorphism map
  overBase : map ≫ Y.structureMap = model.structureMap
  canonical : WeilDivisor model.scheme
  compatible : letI := dominant
    IsCanonicalDivisorOf (.of ℂ) model.structureMap n
      (rationalTopFormPullback (.of ℂ) model.structureMap Y.structureMap map overBase n Y.form)
      canonical
  pullback : QWeilDivisor model.scheme
  isPullback : letI := dominant
    IsQCartierPullback map (rationalWeilDivisor Y.canonical + Δ) pullback
  prime : PrimeDivisor model.scheme

noncomputable def MultiplierDivisorialTest.discrepancy {n : ℕ} {Y : CanonicalModel n}
    {Δ : QWeilDivisor Y.scheme} (T : MultiplierDivisorialTest Y Δ) : ℚ :=
  (rationalWeilDivisor T.canonical - T.pullback) T.prime

noncomputable def MultiplierDivisorialTest.valuationIdeal {n : ℕ} {Y : CanonicalModel n}
    {Δ : QWeilDivisor Y.scheme} (T : MultiplierDivisorialTest Y Δ) :
    Ideal (T.model.scheme.presheaf.stalk T.prime.1) :=
  letI : StalkwiseNormal T.model.scheme := smoothNormal T.model T.smooth
  multiplierValuationIdeal T.prime T.discrepancy

noncomputable def MultiplierDivisorialTest.regularMap {n : ℕ} {Y : CanonicalModel n}
    {Δ : QWeilDivisor Y.scheme} (T : MultiplierDivisorialTest Y Δ)
    {U : Y.scheme.Opens} (hp : T.map T.prime.1 ∈ U) :
    Γ(Y.scheme,U) →+* T.model.scheme.presheaf.stalk T.prime.1 :=
  (T.map.stalkMap T.prime.1).hom.comp
    (Y.scheme.presheaf.germ U (T.map T.prime.1) hp).hom

noncomputable def valuativeMultiplierIdeal {n : ℕ} (Y : CanonicalModel n)
    (Δ : QWeilDivisor Y.scheme) (U : Y.scheme.Opens) : Ideal Γ(Y.scheme,U) :=
  ⨅ T : MultiplierDivisorialTest Y Δ, ⨅ hp : T.map T.prime.1 ∈ U,
    T.valuationIdeal.comap (T.regularMap hp)

lemma mem_valuativeMultiplierIdeal {n : ℕ} {Y : CanonicalModel n}
    {Δ : QWeilDivisor Y.scheme} {U : Y.scheme.Opens} (a : Γ(Y.scheme,U)) :
    a ∈ valuativeMultiplierIdeal Y Δ U ↔
      ∀ T : MultiplierDivisorialTest Y Δ, ∀ hp : T.map T.prime.1 ∈ U,
        T.regularMap hp a ∈ T.valuationIdeal := by
  simp only [valuativeMultiplierIdeal,Ideal.mem_iInf,Ideal.mem_comap]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter

namespace NumericalDimensionOne

theorem valuativeMultiplierIdeal_eq_top_of_klt {n : ℕ}
    {Y : CanonicalModel n} {Δ : QWeilDivisor Y.scheme} {U : Y.scheme.Opens}
    (h : IsKltBoundaryOn Y U Δ) {V : Y.scheme.Opens} (hVU : V ≤ U) :
    valuativeMultiplierIdeal Y Δ V = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply (mem_valuativeMultiplierIdeal 1).mpr
  intro T hp
  have hd : -1 < T.discrepancy :=
    h.2.2 T.model T.smooth T.map T.dominant T.proper T.birational T.overBase
      T.canonical T.compatible T.pullback T.isPullback T.prime (hVU hp)
  let : StalkwiseNormal T.model.scheme := smoothNormal T.model T.smooth
  have he : T.valuationIdeal = ⊤ := (multiplierValuationIdeal_eq_top T.prime _).mpr hd
  rw [he]
  trivial
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat

namespace NumericalDimensionOne
lemma MultiplierDivisorialTest.regularMap_res {n : ℕ} {Y : CanonicalModel n}
    {Δ : QWeilDivisor Y.scheme} (T : MultiplierDivisorialTest Y Δ)
    {U V : Y.scheme.Opens} (i : U ⟶ V) (hp : T.map T.prime.1 ∈ U)
    (a : Γ(Y.scheme,V)) :
    T.regularMap hp (Y.scheme.presheaf.map i.op a) = T.regularMap (i.le hp) a := by
  dsimp only [MultiplierDivisorialTest.regularMap,RingHom.coe_comp,Function.comp_apply]
  rw [Y.scheme.presheaf.germ_res_apply i (T.map T.prime.1) hp a]

lemma valuativeMultiplierIdeal_res {n : ℕ} {Y : CanonicalModel n}
    {Δ : QWeilDivisor Y.scheme} {U V : Y.scheme.Opens} (i : U ⟶ V)
    {a : Γ(Y.scheme,V)} (ha : a ∈ valuativeMultiplierIdeal Y Δ V) :
    Y.scheme.presheaf.map i.op a ∈ valuativeMultiplierIdeal Y Δ U := by
  apply (mem_valuativeMultiplierIdeal _).mpr
  intro T hp
  rw [MultiplierDivisorialTest.regularMap_res]
  exact (mem_valuativeMultiplierIdeal a).mp ha T (i.le hp)

noncomputable def multiplierIdealSubfunctor {n : ℕ} (Y : CanonicalModel n)
    (Δ : QWeilDivisor Y.scheme) : Subfunctor (Y.scheme.presheaf ⋙ forget CommRingCat) where
  obj U := valuativeMultiplierIdeal Y Δ U.unop
  map i := fun _ ha => valuativeMultiplierIdeal_res i.unop ha
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat

namespace NumericalDimensionOne

theorem multiplierIdealSubfunctor_isSheaf {n : ℕ} (Y : CanonicalModel n)
    (Δ : QWeilDivisor Y.scheme) :
    TopCat.Presheaf.IsSheaf (multiplierIdealSubfunctor Y Δ).toFunctor := by
  unfold TopCat.Presheaf.IsSheaf
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  apply ((multiplierIdealSubfunctor Y Δ).isSheaf_iff ?_).mpr
  · intro U a hcover
    apply (mem_valuativeMultiplierIdeal a).mpr
    intro T hp
    obtain ⟨V,i,hi,hpV⟩ := hcover (T.map T.prime.1) hp
    have hs : Y.scheme.presheaf.map i.op a ∈ valuativeMultiplierIdeal Y Δ V := hi
    have hh := (mem_valuativeMultiplierIdeal _).mp hs T hpV
    rw [MultiplierDivisorialTest.regularMap_res] at hh
    exact hh
  · rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
    exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat) _).mp
      Y.scheme.sheaf.property
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat

namespace NumericalDimensionOne

noncomputable def multiplierModulePresheaf {n : ℕ} (Y : CanonicalModel n)
    (Δ : QWeilDivisor Y.scheme) :
    PresheafOfModules (Y.scheme.presheaf ⋙ forget₂ CommRingCat RingCat) where
  obj U := ModuleCat.of _ (valuativeMultiplierIdeal Y Δ U.unop)
  map {U V} i := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (Y.scheme.presheaf.map i).hom).obj
      (ModuleCat.of Γ(Y.scheme,V.unop) (valuativeMultiplierIdeal Y Δ V.unop)))
    { toFun := fun a => ⟨Y.scheme.presheaf.map i a.1,
        valuativeMultiplierIdeal_res i.unop a.2⟩
      map_add' := by intro a b; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by
        intro a b
        apply Subtype.ext
        exact map_mul (Y.scheme.presheaf.map i).hom a b.1 }

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat

namespace NumericalDimensionOne

theorem multiplierModulePresheaf_isSheaf {n : ℕ} (Y : CanonicalModel n)
    (Δ : QWeilDivisor Y.scheme) :
    TopCat.Presheaf.IsSheaf (multiplierModulePresheaf Y Δ).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  exact multiplierIdealSubfunctor_isSheaf Y Δ

noncomputable def multiplierModuleSheaf {n : ℕ} (Y : CanonicalModel n)
    (Δ : QWeilDivisor Y.scheme) : SheafOfModules Y.scheme.ringCatSheaf :=
  ⟨multiplierModulePresheaf Y Δ,multiplierModulePresheaf_isSheaf Y Δ⟩

noncomputable def multiplierModuleEquivOfKlt {n : ℕ} {Y : CanonicalModel n}
    {Δ : QWeilDivisor Y.scheme} {U : Y.scheme.Opens}
    (h : IsKltBoundaryOn Y U Δ) {V : Y.scheme.Opens} (hVU : V ≤ U) :
    valuativeMultiplierIdeal Y Δ V ≃ₗ[Γ(Y.scheme,V)] Γ(Y.scheme,V) where
  toFun := Subtype.val
  invFun a := ⟨a,by rw [valuativeMultiplierIdeal_eq_top_of_klt h hVU]; trivial⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

omit [StalkwiseNormal X] in
lemma divisorSectionOn_res [StalkwiseNormal X] {D : WeilDivisor X} {U V : X.Opens} (h : U ≤ V)
    {f : X.functionField} (hf : IsDivisorSectionOn D V f) : IsDivisorSectionOn D U f := by
  rcases hf with rfl | hf
  · exact Or.inl rfl
  · exact Or.inr (fun p hp => hf p (h hp))

lemma divisorSectionOn_add {D : WeilDivisor X} {U : X.Opens} {f g : X.functionField}
    (hf : IsDivisorSectionOn D U f) (hg : IsDivisorSectionOn D U g) :
    IsDivisorSectionOn D U (f+g) := by
  rcases hf with rfl | hf
  · simpa using hg
  rcases hg with rfl | hg
  · rw [add_zero]
    exact Or.inr hf
  by_cases hfg : f+g=0
  · exact Or.inl hfg
  right
  intro p hp
  have := dvr_at_prime_divisor p
  have h := X.ord_add (x := p.1) hfg
  have hm : -(D p) ≤ min (X.ord f p.1) (X.ord g p.1) :=
    le_min (by have := hf p hp; omega) (by have := hg p hp; omega)
  omega

omit [StalkwiseNormal X] in
lemma order_neg_value [StalkwiseNormal X] (f : X.functionField) (x : X) :
    X.ord (-f) x = X.ord f x := by
  have hm : (-1 : X.functionField) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have h1 := X.ord_mul (x := x) hm hm
  simp only [neg_mul_neg, one_mul, order_one] at h1
  have hz : X.ord (-1 : X.functionField) x = 0 := by omega
  by_cases hf : f = 0
  · simp [hf]
  · have h := X.ord_mul (x := x) hm hf
    simpa only [neg_one_mul,hz,zero_add] using h

lemma divisorSectionOn_neg {D : WeilDivisor X} {U : X.Opens} {f : X.functionField}
    (hf : IsDivisorSectionOn D U f) : IsDivisorSectionOn D U (-f) := by
  rcases hf with rfl | hf
  · exact Or.inl (neg_zero)
  · right
    intro p hp
    simpa only [order_neg_value] using hf p hp

def divisorFunctionPrelocal (D : WeilDivisor X) :
    PrelocalPredicate (fun _ : X => X.functionField) where
  pred {U} f := ∃ a : X.functionField, (∀ x : U, f x = a) ∧ IsDivisorSectionOn D U a
  res {U V} i f hf := by
    obtain ⟨a,ha,hsec⟩ := hf
    exact ⟨a,fun x => ha (i x),divisorSectionOn_res i.le hsec⟩

def divisorFunctionLocal (D : WeilDivisor X) :
    LocalPredicate (fun _ : X => X.functionField) := (divisorFunctionPrelocal D).sheafify

lemma divisorFunctionLocal_zero (D : WeilDivisor X) (U : X.Opens) :
    (divisorFunctionLocal D).pred (fun _ : U => (0 : X.functionField)) :=
  PrelocalPredicate.sheafifyOf ⟨0,fun _ => rfl,Or.inl rfl⟩

lemma divisorFunctionLocal_add (D : WeilDivisor X) {U : X.Opens}
    {f g : U → X.functionField} (hf : (divisorFunctionLocal D).pred f)
    (hg : (divisorFunctionLocal D).pred g) :
    (divisorFunctionLocal D).pred (fun x => f x + g x) := by
  apply PrelocalPredicate.sheafify_inductionOn₂' (divisorFunctionPrelocal D)
    (divisorFunctionPrelocal D) (divisorFunctionPrelocal D) (fun a b => a+b) ?_ hf hg
  intro V W f g hf hg
  obtain ⟨a,ha,hs⟩ := hf
  obtain ⟨b,hb,ht⟩ := hg
  exact ⟨a+b,fun x => congrArg₂ (· + ·) (ha _) (hb _),
    divisorSectionOn_add (divisorSectionOn_res inf_le_left hs)
      (divisorSectionOn_res inf_le_right ht)⟩

lemma divisorFunctionLocal_neg (D : WeilDivisor X) {U : X.Opens}
    {f : U → X.functionField} (hf : (divisorFunctionLocal D).pred f) :
    (divisorFunctionLocal D).pred (fun x => -f x) := by
  apply PrelocalPredicate.sheafify_inductionOn' (divisorFunctionPrelocal D)
    (fun a => -a) ?_ hf
  intro V f hf
  obtain ⟨a,ha,hs⟩ := hf
  exact ⟨-a,fun x => congrArg Neg.neg (ha x),divisorSectionOn_neg hs⟩

def divisorFunctionGroup (D : WeilDivisor X) (U : X.Opens) : AddSubgroup (U → X.functionField) where
  carrier := {f | (divisorFunctionLocal D).pred f}
  zero_mem' := divisorFunctionLocal_zero D U
  add_mem' := divisorFunctionLocal_add D
  neg_mem' := divisorFunctionLocal_neg D

noncomputable def divisorFunctionPresheaf (D : WeilDivisor X) : TopCat.Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of (divisorFunctionGroup D U.unop)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun f => ⟨fun x => f.1 (i.unop x),
        (divisorFunctionLocal D).res i.unop f.1 f.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

end NumericalDimensionOne

end OAI
