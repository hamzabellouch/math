import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CanonicalPullbacks

namespace OAI

/-! Rational Degrees. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

lemma CartierMultiple.isQCartier {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {D : QWeilDivisor X} (M : CartierMultiple D) : IsQCartierDivisor D :=
  ⟨M.denominator, M.positive, M.divisor.1, M.divisor.2, M.equation⟩

lemma CartierMultiple.degreeOn_eq {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] {D : QWeilDivisor X.scheme}
    (M N : CartierMultiple D) (C : CurveOn X) : M.degreeOn C = N.degreeOn C := by
  have he : N.denominator • M.divisor = M.denominator • N.divisor :=
    Subtype.ext (multiples_cross_equal M.equation N.equation)
  have hdeg := congrArg (fun A => cartierCurveDegree A C) he
  simp only [cartierCurveDegree_nsmul, nsmul_eq_mul] at hdeg
  have hdegQ : (N.denominator : ℚ) * (cartierCurveDegree M.divisor C : ℚ) =
      (M.denominator : ℚ) * (cartierCurveDegree N.divisor C : ℚ) := by
    exact_mod_cast hdeg
  apply (div_eq_div_iff
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt M.positive))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive))).mpr
  simpa only [mul_comm] using hdegQ

theorem qCartierCurveDegree_eq_multiple
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {D : QWeilDivisor X.scheme} (hD : IsQCartierDivisor D)
    (M : CartierMultiple D) (C : CurveOn X) :
    qCartierCurveDegree D hD C = M.degreeOn C :=
  (chooseCartierMultiple hD).degreeOn_eq M C

noncomputable def CartierMultiple.add {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {D E : QWeilDivisor X} (M : CartierMultiple D) (N : CartierMultiple E) :
    CartierMultiple (D + E) where
  denominator := M.denominator * N.denominator
  positive := Nat.mul_pos M.positive N.positive
  divisor := N.denominator • M.divisor + M.denominator • N.divisor
  equation := by
    ext p
    have hM : (M.denominator : ℚ) * D p = (M.divisor.1 p : ℚ) :=
      DFunLike.congr_fun M.equation p
    have hN : (N.denominator : ℚ) * E p = (N.divisor.1 p : ℚ) :=
      DFunLike.congr_fun N.equation p
    change ((M.denominator * N.denominator : ℕ) : ℚ) * (D p + E p) =
      ((N.denominator • M.divisor.1 p + M.denominator • N.divisor.1 p : ℤ) : ℚ)
    simp only [nsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← hM, ← hN]
    ring

noncomputable def CartierMultiple.smul {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {D : QWeilDivisor X} (M : CartierMultiple D) (t : ℚ) :
    CartierMultiple (t • D) where
  denominator := M.denominator * t.den
  positive := Nat.mul_pos M.positive t.den_pos
  divisor := t.num • M.divisor
  equation := by
    ext p
    have hM : (M.denominator : ℚ) * D p = (M.divisor.1 p : ℚ) :=
      DFunLike.congr_fun M.equation p
    have ht : (t.den : ℚ) * t = (t.num : ℚ) := by
      have he := (eq_div_iff (Nat.cast_ne_zero.mpr t.den_nz : (t.den : ℚ) ≠ 0)).mp
        (Rat.num_div_den t).symm
      simpa only [mul_comm] using he
    change ((M.denominator * t.den : ℕ) : ℚ) * (t * D p) =
      ((t.num • M.divisor.1 p : ℤ) : ℚ)
    simp only [zsmul_eq_mul, Int.cast_mul, Nat.cast_mul]
    calc
      (M.denominator : ℚ) * t.den * (t * D p) =
          ((t.den : ℚ) * t) * ((M.denominator : ℚ) * D p) := by ring
      _ = (t.num : ℚ) * (M.divisor.1 p : ℚ) := by rw [ht, hM]

lemma CartierMultiple.degreeOn_add {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] {D E : QWeilDivisor X.scheme}
    (M : CartierMultiple D) (N : CartierMultiple E) (C : CurveOn X) :
    (M.add N).degreeOn C = M.degreeOn C + N.degreeOn C := by
  simp only [CartierMultiple.degreeOn, CartierMultiple.add,
    cartierCurveDegree_add, cartierCurveDegree_nsmul, nsmul_eq_mul,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt M.positive),
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)]

lemma CartierMultiple.degreeOn_smul {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] {D : QWeilDivisor X.scheme}
    (M : CartierMultiple D) (t : ℚ) (C : CurveOn X) :
    (M.smul t).degreeOn C = t * M.degreeOn C := by
  have he : cartierCurveDegree (t.num • M.divisor) C = t.num • cartierCurveDegree M.divisor C :=
    (cartierCurveDegreeHom C).map_zsmul t.num M.divisor
  simp only [CartierMultiple.degreeOn, CartierMultiple.smul, he,
    zsmul_eq_mul, Int.cast_mul, Nat.cast_mul]
  conv_rhs => rw [← Rat.num_div_den t]
  simp only [Int.cast_id]
  ring

lemma qCartierCurveDegree_add
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {D E : QWeilDivisor X.scheme} (hD : IsQCartierDivisor D)
    (hE : IsQCartierDivisor E) (hM : IsQCartierDivisor (D + E)) (C : CurveOn X) :
    qCartierCurveDegree (D + E) hM C =
      qCartierCurveDegree D hD C + qCartierCurveDegree E hE C := by
  rw [qCartierCurveDegree_eq_multiple hM
    ((chooseCartierMultiple hD).add (chooseCartierMultiple hE)), CartierMultiple.degreeOn_add]
  rfl

lemma qCartierCurveDegree_smul
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {D : QWeilDivisor X.scheme} (hD : IsQCartierDivisor D) (t : ℚ)
    (hM : IsQCartierDivisor (t • D)) (C : CurveOn X) :
    qCartierCurveDegree (t • D) hM C = t * qCartierCurveDegree D hD C := by
  rw [qCartierCurveDegree_eq_multiple hM ((chooseCartierMultiple hD).smul t),
    CartierMultiple.degreeOn_smul]
  rfl

theorem qCartierCurveDegree_add_smul
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {D E : QWeilDivisor X.scheme} (hD : IsQCartierDivisor D)
    (hE : IsQCartierDivisor E) (t : ℚ)
    (hM : IsQCartierDivisor (D + t • E)) (C : CurveOn X) :
    qCartierCurveDegree (D + t • E) hM C =
      qCartierCurveDegree D hD C + t * qCartierCurveDegree E hE C := by
  have htE := ((chooseCartierMultiple hE).smul t).isQCartier
  rw [qCartierCurveDegree_add hD htE hM, qCartierCurveDegree_smul]

theorem curve_nonnegative_of_generated_approximations
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {L B : QWeilDivisor X.scheme} (hL : IsQCartierDivisor L)
    (hB : IsQCartierDivisor B) (t : ℕ → ℚ)
    (ht : Filter.Tendsto (fun j => (t j : ℝ)) Filter.atTop (nhds 0))
    (C : CurveOn X)
    (hgen : ∀ j, ∃ M : CartierMultiple (L + t j • B),
      IsGeneratedAt M.divisor.1 (C.morphism (genericPoint C.curve.scheme))) :
    0 ≤ qCartierCurveDegree L hL C := by
  have hnon : ∀ j, (0 : ℝ) ≤ (qCartierCurveDegree L hL C : ℝ) +
      (t j : ℝ) * (qCartierCurveDegree B hB C : ℝ) := by
    intro j
    obtain ⟨M, hM⟩ := hgen j
    have hD := cartierCurveDegree_nonneg_of_generatedAt M.divisor C hM
    have hq : 0 ≤ M.degreeOn C :=
      div_nonneg (by exact_mod_cast hD) (by exact_mod_cast M.positive.le)
    rw [← qCartierCurveDegree_eq_multiple M.isQCartier M C,
      qCartierCurveDegree_add_smul hL hB] at hq
    exact_mod_cast hq
  have hlim : Filter.Tendsto (fun j => (qCartierCurveDegree L hL C : ℝ) +
      (t j : ℝ) * (qCartierCurveDegree B hB C : ℝ)) Filter.atTop
      (nhds (qCartierCurveDegree L hL C : ℝ)) := by
    simpa only [zero_mul, add_zero] using
      Filter.Tendsto.add tendsto_const_nhds (ht.mul tendsto_const_nhds)
  have hz : (0 : ℝ) ≤ (qCartierCurveDegree L hL C : ℝ) :=
    ge_of_tendsto' hlim hnon
  exact_mod_cast hz

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X Y : ComplexProjectiveVariety} [StalkwiseNormal X.scheme] [StalkwiseNormal Y.scheme]
def CurveOn.comp (C : CurveOn X) (f : X.scheme ⟶ Y.scheme)
    (hf : f ≫ Y.structureMap = X.structureMap) : CurveOn Y :=
  ⟨C.curve,C.smooth,C.morphism ≫ f,by rw [Category.assoc,hf,C.overComplex]⟩
lemma cartierCurveDegree_cartierPullback (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (D : cartierDivisors (X := Y.scheme)) (P : cartierDivisors (X := X.scheme))
    (hP : IsCartierPullback f D.1 P.1) (C : CurveOn X) :
    cartierCurveDegree P C = cartierCurveDegree D (C.comp f hf) := by
  exact pulledCartierRepresentative_degree_eq C
    (pulledCartierRepresentative_spec C P.1 P.2)
    ((pulledCartierRepresentative_spec (C.comp f hf) D.1 D.2).of_cartierPullback
      C.morphism f hP)
lemma qCartierCurveDegree_pullback (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    {D : QWeilDivisor Y.scheme} {P : QWeilDivisor X.scheme}
    (hD : IsQCartierDivisor D) (hP : IsQCartierPullback f D P) (C : CurveOn X) :
    qCartierCurveDegree P hP.isQCartier C = qCartierCurveDegree D hD (C.comp f hf) := by
  obtain ⟨m,hm,A,B,hA,hAD,hBP,hAB⟩ := hP
  rw [qCartierCurveDegree_eq_multiple _ (⟨m,hm,⟨B,hAB.isCartier⟩,hBP⟩ : CartierMultiple P),
    qCartierCurveDegree_eq_multiple _ (⟨m,hm,⟨A,hA⟩,hAD⟩ : CartierMultiple D)]
  unfold CartierMultiple.degreeOn
  rw [cartierCurveDegree_cartierPullback f hf ⟨A,hA⟩ ⟨B,hAB.isCartier⟩ hAB C]
omit [StalkwiseNormal Y.scheme] in
lemma cartierCurveDegree_pullback_contracted (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    {D : WeilDivisor Y.scheme} (P : cartierDivisors (X := X.scheme))
    (hP : IsCartierPullback f D P.1) (C : CurveOn X) (hC : IsCurveContracted f C) :
    cartierCurveDegree P C = 0 := by
  obtain ⟨y,hy⟩ := hC
  have hzero := hP.zero_representative_of_constant C.morphism
    (fun x => (hy x).trans (hy (genericPoint C.curve.scheme)).symm)
  exact pulledCartierRepresentative_degree_eq C
    (pulledCartierRepresentative_spec C P.1 P.2) hzero
omit [StalkwiseNormal Y.scheme] in
lemma qCartierCurveDegree_pullback_contracted (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    {D : QWeilDivisor Y.scheme} {P : QWeilDivisor X.scheme}
    (hP : IsQCartierPullback f D P) (C : CurveOn X) (hC : IsCurveContracted f C) :
    qCartierCurveDegree P hP.isQCartier C = 0 := by
  obtain ⟨m,hm,A,B,_hA,_hAD,hBP,hAB⟩ := hP
  rw [qCartierCurveDegree_eq_multiple _ (⟨m,hm,⟨B,hAB.isCartier⟩,hBP⟩ : CartierMultiple P)]
  change (cartierCurveDegree ⟨B,hAB.isCartier⟩ C : ℚ) / m = 0
  rw [cartierCurveDegree_pullback_contracted f _ hAB C hC,Int.cast_zero,zero_div]
lemma cartierCurveDegree_nonneg_of_ample (D : cartierDivisors (X := X.scheme))
    (hD : IsAmpleDivisor D.1) (C : CurveOn X) : 0 ≤ cartierCurveDegree D C := by
  obtain ⟨m,hm,a,ha,hsec,_hU,hx,_⟩ := hD.2 (C.morphism (genericPoint C.curve.scheme)) ⊤
    (by trivial)
  have hgen : IsGeneratedAt (m • D).1 (C.morphism (genericPoint C.curve.scheme)) :=
    ⟨a,ha,hsec,hx⟩
  have h := cartierCurveDegree_nonneg_of_generatedAt (m • D) C hgen
  rw [cartierCurveDegree_nsmul,nsmul_eq_mul] at h
  exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hm)
lemma qCartierCurveDegree_nonneg_of_ample {D : QWeilDivisor X.scheme}
    (hD : IsQCartierDivisor D) (hA : IsAmpleQDivisor D) (C : CurveOn X) :
    0 ≤ qCartierCurveDegree D hD C := by
  obtain ⟨m,hm,A,hAmp,hAD⟩ := hA
  rw [qCartierCurveDegree_eq_multiple _ (⟨m,hm,⟨A,hAmp.1⟩,hAD⟩ : CartierMultiple D)]
  exact div_nonneg (by exact_mod_cast cartierCurveDegree_nonneg_of_ample ⟨A,hAmp.1⟩ hAmp C)
    (by exact_mod_cast hm.le)
omit [StalkwiseNormal Y.scheme] in
lemma IsRelativelyAmpleQ.curveDegree_nonneg
    (f : X.scheme ⟶ Y.scheme) [IsDominant f] {D : QWeilDivisor X.scheme}
    (hD : IsQCartierDivisor D) (hA : IsRelativelyAmpleQ f D)
    (C : CurveOn X) (hC : IsCurveContracted f C) :
    0 ≤ qCartierCurveDegree D hD C := by
  obtain ⟨A,_hA,E,hE,hAmp⟩ := hA
  let M : CartierMultiple (rationalWeilDivisor E) := ⟨1,by omega,⟨E,hE.isCartier⟩,by simp⟩
  have hsum := ((chooseCartierMultiple hD).add M).isQCartier
  have hz : qCartierCurveDegree (rationalWeilDivisor E) M.isQCartier C = 0 := by
    rw [qCartierCurveDegree_eq_multiple _ M]
    change (cartierCurveDegree ⟨E,hE.isCartier⟩ C : ℚ) / 1 = 0
    rw [cartierCurveDegree_pullback_contracted f _ hE C hC,Int.cast_zero,zero_div]
  have h := qCartierCurveDegree_nonneg_of_ample hsum hAmp C
  rw [qCartierCurveDegree_add hD M.isQCartier, hz,add_zero] at h
  exact h
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma qCartierCurveDegree_neg {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {D : QWeilDivisor X.scheme} (hD : IsQCartierDivisor D) (hn : IsQCartierDivisor (-D))
    (C : CurveOn X) : qCartierCurveDegree (-D) hn C = -qCartierCurveDegree D hD C := by
  simpa only [neg_one_smul,neg_one_mul] using qCartierCurveDegree_smul hD (-1)
    (show IsQCartierDivisor ((-1 : ℚ) • D) from by simpa only [neg_one_smul] using hn) C
lemma qCartierCurveDegree_sub {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {D E : QWeilDivisor X.scheme} (hD : IsQCartierDivisor D) (hE : IsQCartierDivisor E)
    (hs : IsQCartierDivisor (D-E)) (C : CurveOn X) :
    qCartierCurveDegree (D-E) hs C = qCartierCurveDegree D hD C - qCartierCurveDegree E hE C := by
  have hn : IsQCartierDivisor (-E) := by
    simpa only [neg_one_smul] using ((chooseCartierMultiple hE).smul (-1)).isQCartier
  have h := qCartierCurveDegree_add hD hn
    (show IsQCartierDivisor (D + -E) from by simpa only [sub_eq_add_neg] using hs) C
  rw [qCartierCurveDegree_neg hE hn] at h
  simpa only [sub_eq_add_neg] using h

lemma canonical_difference_antinef_of_commuting
    {W X Y R : ComplexProjectiveVariety}
    [StalkwiseNormal W.scheme] [StalkwiseNormal X.scheme] [StalkwiseNormal Y.scheme]
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q]
    (hp : p ≫ X.structureMap = W.structureMap)
    (f : X.scheme ⟶ R.scheme) [IsDominant f] (g : Y.scheme ⟶ R.scheme)
    (hcomm : p ≫ f = q ≫ g)
    {D : QWeilDivisor X.scheme} {E : QWeilDivisor Y.scheme}
    {P Q : QWeilDivisor W.scheme} (hD : IsQCartierDivisor D)
    (hP : IsQCartierPullback p D P) (hQ : IsQCartierPullback q E Q)
    (hs : IsQCartierDivisor (P-Q)) (hnegative : IsRelativelyAmpleQ f (-D))
    (C : CurveOn W) (hC : IsCurveContracted q C) :
    qCartierCurveDegree (P-Q) hs C ≤ 0 := by
  have hcontract : IsCurveContracted f (C.comp p hp) := by
    obtain ⟨y,hy⟩ := hC
    refine ⟨g y,?_⟩
    intro x
    change (p ≫ f) (C.morphism x) = g y
    rw [hcomm]
    change g (q (C.morphism x)) = g y
    rw [hy x]
  have hn : IsQCartierDivisor (-D) := by
    simpa only [neg_one_smul] using ((chooseCartierMultiple hD).smul (-1)).isQCartier
  have h := hnegative.curveDegree_nonneg f hn (C.comp p hp) hcontract
  rw [qCartierCurveDegree_neg hD hn,neg_nonneg] at h
  rw [qCartierCurveDegree_sub hP.isQCartier hQ.isQCartier,
    qCartierCurveDegree_pullback p hp hD hP,
    qCartierCurveDegree_pullback_contracted q hQ C hC,sub_zero]
  exact h
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

lemma common_model_commutes_over_base {W X Y R : Scheme}
    [IsReduced W] [R.IsSeparated]
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ R) (g : Y ⟶ R)
    (θ : W.PartialIso X) (φ : X.PartialIso Y)
    (hθp : θ.IsOver p (𝟙 X)) (hθq : (θ.trans φ).IsOver q (𝟙 Y))
    (hφ : φ.IsOver f g) : p ≫ f = q ≫ g := by
  have hθf : θ.IsOver (p ≫ f) f := by
    have he : θ.iso.hom ≫ θ.target.ι = θ.source.ι ≫ p := by
      simpa only [Scheme.PartialIso.IsOver,Category.comp_id] using hθp
    change θ.iso.hom ≫ θ.target.ι ≫ f = θ.source.ι ≫ (p ≫ f)
    simpa only [Category.assoc] using congrArg (fun k => k ≫ f) he
  have hleft := hθf.trans hφ
  have hright : (θ.trans φ).IsOver (q ≫ g) g := by
    have he : (θ.trans φ).iso.hom ≫ (θ.trans φ).target.ι =
        (θ.trans φ).source.ι ≫ q := by
      simpa only [Scheme.PartialIso.IsOver,Category.comp_id] using hθq
    change (θ.trans φ).iso.hom ≫ (θ.trans φ).target.ι ≫ g =
      (θ.trans φ).source.ι ≫ (q ≫ g)
    simpa only [Category.assoc] using congrArg (fun k => k ≫ g) he
  let : IsDominant (θ.trans φ).source.ι := Opens.isDominant_ι (θ.trans φ).dense_source
  apply ext_of_isDominant (θ.trans φ).source.ι
  exact (Eq.symm hleft).trans hright
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma canonical_comparison_boundary {n : ℕ}
    (X Y : CanonicalModel n)
    (hY : IsTerminalModel Y) (φ : X.scheme.PartialIso Y.scheme)
    (hφ : NoExtractionOn φ) (hbase : φ.IsOver X.structureMap Y.structureMap)
    (hc : CompatibleCanonicalData X Y φ hbase)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q] [IsProper p] [IsProper q]
    (hp : p ≫ X.structureMap = W.structureMap) (hq : q ≫ Y.structureMap = W.structureMap)
    (θ : W.scheme.PartialIso X.scheme) (hθp : θ.IsOver p (𝟙 X.scheme))
    (hθq : (θ.trans φ).IsOver q (𝟙 Y.scheme)) :
    ∃ P Q : QWeilDivisor W.scheme,
      IsQCartierPullback p (rationalWeilDivisor X.canonical) P ∧
      IsQCartierPullback q (rationalWeilDivisor Y.canonical) Q ∧
      (∀ F : PrimeDivisor W.scheme, (P-Q) F ≠ 0 → 1 < Order.coheight (q F.1)) ∧
      (∀ F : PrimeDivisor W.scheme, Order.coheight (p F.1) = 1 →
        1 < Order.coheight (q F.1) → 0 < (P-Q) F) := by
  let : X.scheme.IsSeparated := ⟨by
    have h : IsSeparated (X.structureMap ≫ CategoryTheory.Limits.terminal.from _) := inferInstance
    simpa only [CategoryTheory.Limits.terminal.comp_from] using h⟩
  have hpb : IsBirationalMorphism p := ⟨θ,hθp⟩
  have hqb : IsBirationalMorphism q := ⟨θ.trans φ,hθq⟩
  obtain ⟨KW,hKp,hKq⟩ := exists_common_canonicalDivisor X Y φ hbase hc W hW p q hp hq θ hθp hθq
  obtain ⟨P,hP⟩ := exists_qCartierPullback p _ X.qCartier
  obtain ⟨Q,hQ⟩ := exists_qCartierPullback q _ Y.qCartier
  refine ⟨P,Q,hP,hQ,?_,?_⟩
  · intro F hF
    have hz : Order.coheight (q F.1) ≠ 0 := by
      intro he
      have hsp : q F.1 ⤳ genericPoint Y.scheme :=
        (Order.coheight_eq_zero.mp he) (genericPoint_specializes (q F.1))
      have heq := (hsp.antisymm (genericPoint_specializes (q F.1))).eq
      have hFη := birational_generic_fiber q hqb F.1 heq
      have h0 : Order.coheight F.1 = 0 := by
        rw [hFη]
        exact Order.coheight_eq_zero.mpr (fun x _ => genericPoint_specializes x)
      rw [F.2] at h0
      exact one_ne_zero h0
    apply lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr hz)
    intro he
    have hprime := common_model_prime_noExtraction p q φ θ hθp hθq hφ F he.symm
    have hP0 := relativeCanonical_vanishes_over_prime X W hW p hpb hp KW hKp P hP F hprime
    have hQ0 := relativeCanonical_vanishes_over_prime Y W hW q hqb hq KW hKq Q hQ F he.symm
    change (KW F : ℚ) - P F = 0 at hP0
    change (KW F : ℚ) - Q F = 0 at hQ0
    apply hF
    change P F - Q F = 0
    exact sub_eq_zero.mpr ((sub_eq_zero.mp hP0).symm.trans (sub_eq_zero.mp hQ0))
  · intro F hFp hFq
    have hP0 := relativeCanonical_vanishes_over_prime X W hW p hpb hp KW hKp P hP F hFp
    have ht := hY W hW q inferInstance inferInstance hqb hq KW hKq Q hQ F hFq
    change (KW F : ℚ) - P F = 0 at hP0
    change 0 < P F - Q F
    rw [← sub_eq_zero.mp hP0]
    exact ht
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

lemma IsCanonicalMMPStep.antinef_on_common_model {n : ℕ}
    {X Y : CanonicalModel n} {φ : X.scheme.PartialIso Y.scheme}
    (hstep : IsCanonicalMMPStep X Y φ)
    (W : ComplexProjectiveVariety) [StalkwiseNormal W.scheme]
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q]
    (hp : p ≫ X.structureMap = W.structureMap)
    (θ : W.scheme.PartialIso X.scheme) (hθp : θ.IsOver p (𝟙 X.scheme))
    (hθq : (θ.trans φ).IsOver q (𝟙 Y.scheme))
    {P Q : QWeilDivisor W.scheme}
    (hP : IsQCartierPullback p (rationalWeilDivisor X.canonical) P)
    (hQ : IsQCartierPullback q (rationalWeilDivisor Y.canonical) Q)
    (hs : IsQCartierDivisor (P-Q))
    (C : CurveOn W) (hC : IsCurveContracted q C) :
    qCartierCurveDegree (P-Q) hs C ≤ 0 := by
  rcases hstep with ⟨_hXF,_hYF,_hXT,_hYT,_hNE,_hbase,_hcompat,hstep⟩
  rcases hstep with hdiv | hflip
  · obtain ⟨f,hdf,_hproper,hφ,_hbase,_helem,hneg,_hexc⟩ := hdiv
    let := hdf
    let : Y.scheme.IsSeparated := ⟨by
      have h : IsSeparated (Y.structureMap ≫ CategoryTheory.Limits.terminal.from _) := inferInstance
      simpa only [CategoryTheory.Limits.terminal.comp_from] using h⟩
    have hcomm := common_model_commutes_over_base p q f (𝟙 Y.scheme) θ φ hθp hθq hφ
    exact canonical_difference_antinef_of_commuting p q hp f (𝟙 Y.scheme) hcomm
      X.qCartier hP hQ hs hneg C hC
  · obtain ⟨R,f,g,hdf,hdg,_hfp,_hgp,_hfb,_hgb,_hfs,_hgs,hφ,_hfC,_hgC,
      _hfe,_hge,hneg,_hpos⟩ := hflip
    let := hdf
    let := hdg
    let : R.scheme.IsSeparated := ⟨by
      have h : IsSeparated (R.structureMap ≫ CategoryTheory.Limits.terminal.from _) := inferInstance
      simpa only [CategoryTheory.Limits.terminal.comp_from] using h⟩
    have hcomm := common_model_commutes_over_base p q f g θ φ hθp hθq hφ
    exact canonical_difference_antinef_of_commuting p q hp f g hcomm
      X.qCartier hP hQ hs hneg C hC
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

lemma IsCanonicalMMPStep.comparison_boundary_on_common_model {n : ℕ}
    {X Y : CanonicalModel n} {φ : X.scheme.PartialIso Y.scheme}
    (hstep : IsCanonicalMMPStep X Y φ)
    (W : ComplexProjectiveVariety) [StalkwiseNormal W.scheme]
    (hW : IsSmoothNfold W n)
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q] [IsProper p] [IsProper q]
    (hp : p ≫ X.structureMap = W.structureMap) (hq : q ≫ Y.structureMap = W.structureMap)
    (θ : W.scheme.PartialIso X.scheme) (hθp : θ.IsOver p (𝟙 X.scheme))
    (hθq : (θ.trans φ).IsOver q (𝟙 Y.scheme)) :
    ∃ P Q : QWeilDivisor W.scheme,
      IsQCartierPullback p (rationalWeilDivisor X.canonical) P ∧
      IsQCartierPullback q (rationalWeilDivisor Y.canonical) Q ∧
      ∃ hs : IsQCartierDivisor (P-Q),
      (∀ F : PrimeDivisor W.scheme, (P-Q) F ≠ 0 → 1 < Order.coheight (q F.1)) ∧
      (∀ F : PrimeDivisor W.scheme, Order.coheight (p F.1) = 1 →
        1 < Order.coheight (q F.1) → 0 < (P-Q) F) ∧
      (∀ C : CurveOn W, IsCurveContracted q C → qCartierCurveDegree (P-Q) hs C ≤ 0) := by
  have hstep' := hstep
  obtain ⟨_hXF,_hYF,_hXT,hYT,hNE,hbase,hcompat,_hkind⟩ := hstep'
  obtain ⟨P,Q,hP,hQ,hex,hstrict⟩ := canonical_comparison_boundary X Y hYT φ hNE
    hbase hcompat W hW p q hp hq θ hθp hθq
  have hs : IsQCartierDivisor (P-Q) := by
    simpa only [neg_one_smul,← sub_eq_add_neg] using
      ((chooseCartierMultiple hP.isQCartier).add
        ((chooseCartierMultiple hQ.isQCartier).smul (-1))).isQCartier
  refine ⟨P,Q,hP,hQ,hs,hex,hstrict,?_⟩
  intro C hC
  exact hstep.antinef_on_common_model W p q hp θ hθp hθq hP hQ hs C hC
end NumericalDimensionOne

end OAI
