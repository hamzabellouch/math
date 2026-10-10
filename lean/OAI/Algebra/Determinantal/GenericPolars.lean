import OAI.Algebra.Determinantal.SliceCertificates

namespace OAI
namespace PermanentBorder.Polar
open MvPolynomial

section Parametric
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype σ] [Fintype τ]

noncomputable def polarValue (w : τ → σ → L) (f : MvPolynomial σ K)
    (y : σ → L) (i : τ) : L := ∑ j, w i j * aeval y (pderiv j f)

noncomputable def polarGradient (w : τ → σ → L) (f : MvPolynomial σ K)
    (y : σ → L) (i : τ) (j : σ) : L :=
  ∑ k, w i k * aeval y (pderiv j (pderiv k f))

omit [Fintype τ] in
lemma derivation_polarValue (D : Derivation K L L) (w : τ → σ → L)
    (f : MvPolynomial σ K) (y : σ → L) (i : τ) :
    D (polarValue w f y i) = (∑ j, D (w i j) * aeval y (pderiv j f)) +
      ∑ j, polarGradient w f y i j * D (y j) := by
  simp only [polarValue, map_sum, Derivation.leibniz, smul_eq_mul, derivation_aeval,
    Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · simp only [polarGradient, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]

lemma polar_rows_independent_of_derivations [DecidableEq τ] [DecidableEq σ]
    (w : τ → σ → L) (f : MvPolynomial σ K) (y : σ → L)
    (D : τ × σ → Derivation K L L)
    (hw : ∀ a b i j, D (a,b) (w i j) = if (a,b) = (i,j) then 1 else 0)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (c : L) (cfs : τ → L)
    (hdep : ∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j = 0) :
    c = 0 ∧ cfs = 0 := by
  obtain ⟨b,hb⟩ := hg
  have hf' (a : τ) : ∑ j, aeval y (pderiv j f) * D (a,b) (y j) = 0 := by
    rw [← derivation_aeval, hf, map_zero]
  have hp' (a i : τ) : (if a = i then aeval y (pderiv b f) else 0) +
      ∑ j, polarGradient w f y i j * D (a,b) (y j) = 0 := by
    have hd := congrArg (D (a,b)) (hp i)
    rw [derivation_polarValue, map_zero] at hd
    convert hd using 1
    by_cases ha : a = i
    · simp [hw, ha]
    · simp [hw, ha]
  have hcfs : ∀ a, cfs a = 0 := by
    intro a
    have hs : ∑ i, cfs i * (∑ j, polarGradient w f y i j * D (a,b) (y j)) = 0 := by
      have hh : c * (∑ j, aeval y (pderiv j f) * D (a,b) (y j)) +
          ∑ i, cfs i * (∑ j, polarGradient w f y i j * D (a,b) (y j)) = 0 := by
        calc
          _ = ∑ j, (c * aeval y (pderiv j f) +
              ∑ i, cfs i * polarGradient w f y i j) * D (a,b) (y j) := by
            simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
              add_mul, mul_assoc]
            rw [Finset.sum_comm]
          _ = 0 := by simp [hdep]
      simpa only [hf', mul_zero, zero_add] using hh
    have hh : ∑ i, cfs i * ((if a = i then aeval y (pderiv b f) else 0) +
        ∑ j, polarGradient w f y i j * D (a,b) (y j)) = 0 := by
      simp only [hp', mul_zero, Finset.sum_const_zero]
    have : cfs a * aeval y (pderiv b f) = 0 := by
      simpa [mul_add, Finset.sum_add_distrib, hs] using hh
    exact (mul_eq_zero.mp this).resolve_right hb
  have hc : c = 0 := by
    have hh := hdep b
    simp only [hcfs, zero_mul, Finset.sum_const_zero, add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right hb
  exact ⟨hc,funext hcfs⟩

lemma rows_independent_of_derivations [DecidableEq τ] [DecidableEq σ]
    (w : τ → σ → L) (l : σ → L) (f : MvPolynomial σ K) (y : σ → L)
    (D : Option τ × σ → Derivation K L L)
    (hw : ∀ a b i j, D (a,b) (w i j) = if (a,b) = (some i,j) then 1 else 0)
    (hl : ∀ a b j, D (a,b) (l j) = if (a,b) = (none,j) then 1 else 0)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hn : ∑ j, l j * y j = 0 ∨ ∑ j, l j * y j = 1)
    (hy : ∃ j, y j ≠ 0) (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (c z : L) (cfs : τ → L)
    (hdep : ∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j + z * l j = 0) :
    c = 0 ∧ z = 0 ∧ cfs = 0 := by
  have hf' (a : Option τ) (b : σ) :
      ∑ j, aeval y (pderiv j f) * D (a,b) (y j) = 0 := by
    rw [← derivation_aeval, hf, map_zero]
  have hp' (a : Option τ) (b : σ) (i : τ) :
      (if a = some i then aeval y (pderiv b f) else 0) +
        ∑ j, polarGradient w f y i j * D (a,b) (y j) = 0 := by
    have hd := congrArg (D (a,b)) (hp i)
    rw [derivation_polarValue, map_zero] at hd
    convert hd using 1
    by_cases ha : a = some i
    · simp [hw, ha]
    · simp [hw, ha]
  have hl' (a : Option τ) (b : σ) :
      (if a = none then y b else 0) + ∑ j, l j * D (a,b) (y j) = 0 := by
    have hd : D (a,b) (∑ j, l j * y j) = 0 := by
      rcases hn with h | h <;> simp [h]
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, hl,
      Finset.sum_add_distrib] at hd
    by_cases ha : a = none
    · simpa [ha, add_comm] using hd
    · simpa [ha] using hd
  have combine (a : Option τ) (b : σ) :
      c * (∑ j, aeval y (pderiv j f) * D (a,b) (y j)) +
        ∑ i, cfs i * (∑ j, polarGradient w f y i j * D (a,b) (y j)) +
          z * (∑ j, l j * D (a,b) (y j)) = 0 := by
    calc
      _ = ∑ j, (c * aeval y (pderiv j f) +
          ∑ i, cfs i * polarGradient w f y i j + z * l j) * D (a,b) (y j) := by
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, add_mul, mul_assoc]
        rw [Finset.sum_comm]
      _ = 0 := by simp [hdep]
  obtain ⟨b,hyb⟩ := hy
  have hz : z = 0 := by
    have hc := combine none b
    have hpp (i : τ) : ∑ j, polarGradient w f y i j * D (none,b) (y j) = 0 := by
      simpa using hp' none b i
    simp only [hf', hpp, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at hc
    have hll := hl' none b
    simp only [ite_true] at hll
    have : z * y b = 0 := by linear_combination z * hll - hc
    exact (mul_eq_zero.mp this).resolve_right hyb
  obtain ⟨b,hgb⟩ := hg
  have hcfs : ∀ i, cfs i = 0 := by
    intro i
    have hc := combine (some i) b
    simp only [hf', mul_zero, zero_add, hz, zero_mul, add_zero] at hc
    have hs : ∑ a, cfs a * ((if some i = some a then aeval y (pderiv b f) else 0) +
        ∑ j, polarGradient w f y a j * D (some i,b) (y j)) = 0 := by
      simp only [hp', mul_zero, Finset.sum_const_zero]
    have : cfs i * aeval y (pderiv b f) = 0 := by
      simpa [mul_add, Finset.sum_add_distrib, hc] using hs
    exact (mul_eq_zero.mp this).resolve_right hgb
  have hc : c = 0 := by
    have hd := hdep b
    simp only [hz, zero_mul, hcfs, Finset.sum_const_zero, add_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_right hgb
  exact ⟨hc,hz,funext hcfs⟩

end Parametric
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Square
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ]
abbrev PolarVars (τ : Type*) := Option (Option τ)

noncomputable def squareJacobian (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L) :
    Matrix (PolarVars τ) (PolarVars τ) L := fun i j => match i with
  | none => aeval y (pderiv j f)
  | some none => l j
  | some (some i) => polarGradient w f y i j

lemma square_isUnit_of_independent [DecidableEq τ]
    (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L)
    (h : ∀ (c z : L) (cfs : τ → L), (∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j + z * l j = 0) →
      c = 0 ∧ z = 0 ∧ cfs = 0) : IsUnit (squareJacobian w l f y) := by
  apply Matrix.vecMul_injective_iff_isUnit.mp
  apply (squareJacobian w l f y).vecMulLinear.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨hc,hz,hs⟩ := h (v none) (v (some none)) (fun i => v (some (some i))) (by
    intro j
    have hh := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, squareJacobian, Fintype.sum_option, add_assoc,
      add_comm, add_left_comm] using hh)
  funext i
  rcases i with _ | (_ | i)
  · exact hc
  · exact hz
  · exact congrFun hs i

lemma euler_aeval {σ : Type*} [Fintype σ] {f : MvPolynomial σ K} {r : ℕ}
    (hf : f.IsHomogeneous r) (y : σ → L) :
    ∑ j, aeval y (pderiv j f) * y j = (r : L) * aeval y f := by
  classical
  have h := congrArg (aeval y) hf.sum_X_mul_pderiv
  simpa [map_sum, mul_comm] using h

lemma polar_euler_aeval (w : τ → PolarVars τ → L)
    {f : MvPolynomial (PolarVars τ) K} {r : ℕ} (hf : f.IsHomogeneous r)
    (y : PolarVars τ → L) (i : τ) :
    ∑ j, polarGradient w f y i j * y j = ((r-1 : ℕ) : L) * polarValue w f y i := by
  classical
  simp only [polarGradient, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, euler_aeval hf.pderiv]
  simp only [polarValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma square_mulVec_zero (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    {f : MvPolynomial (PolarVars τ) K} {r : ℕ} (hhom : f.IsHomogeneous r)
    (y : PolarVars τ → L) (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hl : ∑ j, l j * y j = 0) : (squareJacobian w l f y).mulVec y = 0 := by
  classical
  funext i
  rcases i with _ | (_ | i)
  · simpa [Matrix.mulVec, dotProduct, squareJacobian, hf] using euler_aeval hhom y
  · exact hl
  · simpa [Matrix.mulVec, dotProduct, squareJacobian, hp] using polar_euler_aeval w hhom y i

end Square

section GenericSquare
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

noncomputable def genericDirections : τ → PolarVars τ → E :=
  fun i j => genericParameter K P (some i,j)
noncomputable def genericLinear : PolarVars τ → E :=
  fun j => genericParameter K P (none,j)

lemma generic_no_infinity (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hhom : f.IsHomogeneous r) (y : PolarVars τ → E)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue genericDirections f y i = 0)
    (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (hn : ∑ j, genericLinear j * y j = 0) : y = 0 := by
  classical
  by_contra hy
  have hyy : ∃ j, y j ≠ 0 := by simpa only [funext_iff, Pi.zero_apply, not_forall] using hy
  have hu : IsUnit (squareJacobian genericDirections genericLinear f y) :=
    square_isUnit_of_independent _ _ _ _ (fun c z cfs hdep =>
      rows_independent_of_derivations _ _ _ _ (parameterDerivation K P)
        (by intros; exact parameterDerivation_parameter K P _ _)
        (by intros; exact parameterDerivation_parameter K P _ _)
        hf hp (Or.inl hn) hyy hg c z cfs hdep)
  have hh := square_mulVec_zero genericDirections genericLinear hhom y hf hp hn
  apply hy
  exact Matrix.mulVec_injective_iff_isUnit.mpr hu (by simpa using hh)

lemma generic_square_isUnit (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hhom : f.IsHomogeneous r) (y : PolarVars τ → E)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue genericDirections f y i = 0)
    (hy : y ≠ 0) (hg : ∃ j, aeval y (pderiv j f) ≠ 0) :
    IsUnit (squareJacobian genericDirections genericLinear f y) := by
  classical
  have hn : ∑ j, genericLinear j * y j ≠ 0 := fun h =>
    hy (generic_no_infinity f hhom y hf hp hg h)
  apply square_isUnit_of_independent
  intro c z cfs hdep
  have hz : z = 0 := by
    have hs : ∑ j, (c * aeval y (pderiv j f) +
        ∑ i, cfs i * polarGradient genericDirections f y i j + z * genericLinear j) * y j = 0 := by
      simp [hdep]
    have he : c * (∑ j, aeval y (pderiv j f) * y j) +
        ∑ i, cfs i * (∑ j, polarGradient genericDirections f y i j * y j) +
        z * (∑ j, genericLinear j * y j) = 0 := by
      convert hs using 1
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
        add_mul, mul_assoc]
      rw [Finset.sum_comm]
    simp only [euler_aeval hhom, polar_euler_aeval _ hhom, hf, hp,
      mul_zero, Finset.sum_const_zero, zero_add] at he
    exact (mul_eq_zero.mp he).resolve_right hn
  obtain ⟨hc,hcfs⟩ := polar_rows_independent_of_derivations genericDirections f y
    (fun (a,b) => parameterDerivation K P (some a,b))
    (by intros; simp only [genericDirections, parameterDerivation_parameter,
      Prod.mk.injEq, Option.some.injEq]) hf hp hg c cfs (by simpa [hz] using hdep)
  exact ⟨hc,hz,hcfs⟩

end GenericSquare
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Polynomials
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

noncomputable def polarPolynomial (w : τ → σ → R) (f : MvPolynomial σ R) (i : τ) :
    MvPolynomial σ R := ∑ j, C (w i j) * pderiv j f

noncomputable def linearPolynomial (l : σ → R) : MvPolynomial σ R :=
  ∑ j, C (l j) * X j

omit [Fintype τ] in
lemma polarPolynomial_homogeneous (w : τ → σ → R) {f : MvPolynomial σ R} {r : ℕ}
    (hf : f.IsHomogeneous r) (i : τ) : (polarPolynomial w f i).IsHomogeneous (r-1) := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C σ (w i j)).mul hf.pderiv

omit [Fintype τ] in
lemma linearPolynomial_homogeneous (l : σ → R) : (linearPolynomial l).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  simpa using (isHomogeneous_C σ (l j)).mul (isHomogeneous_X R j)

omit [Fintype σ] in
lemma det_row_homogeneous {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial σ R)) (e : n → ℕ)
    (hA : ∀ i j, (A i j).IsHomogeneous (e i)) : A.det.IsHomogeneous (∑ i, e i) := by
  classical
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro p _
  have hp : (∏ i, A (p i) i).IsHomogeneous (∑ i, e (p i)) :=
    IsHomogeneous.prod _ _ _ (fun i _ => hA _ _)
  rw [Equiv.sum_comp] at hp
  change (p.sign : ℤ) • (∏ i, A (p i) i) ∈
    (homogeneousSubmodule σ R (∑ i, e i)).restrictScalars ℤ
  exact Submodule.smul_mem _ _ hp

noncomputable def squarePolynomial (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    (f : MvPolynomial (PolarVars τ) R) :
    Matrix (PolarVars τ) (PolarVars τ) (MvPolynomial (PolarVars τ) R) :=
  fun i j => match i with
    | none => pderiv j f
    | some none => C (l j)
    | some (some i) => pderiv j (polarPolynomial w f i)

def squareDegrees (τ : Type*) (r : ℕ) : PolarVars τ → ℕ := fun i => match i with
  | none => r-1
  | some none => 0
  | some (some _) => r-1-1

lemma squarePolynomial_homogeneous [DecidableEq τ] (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    {f : MvPolynomial (PolarVars τ) R} {r : ℕ} (hf : f.IsHomogeneous r) :
    (squarePolynomial w l f).det.IsHomogeneous (∑ i, squareDegrees τ r i) := by
  classical
  apply det_row_homogeneous
  intro i j
  rcases i with _ | (_ | i)
  · exact hf.pderiv
  · exact isHomogeneous_C _ _
  · exact (polarPolynomial_homogeneous w hf i).pderiv

noncomputable def badPolarSystem (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    (f : MvPolynomial (PolarVars τ) R) : PolarVars τ → MvPolynomial (PolarVars τ) R := by
  classical
  exact fun i => match i with
    | none => f
    | some none => linearPolynomial l * (squarePolynomial w l f).det
    | some (some i) => polarPolynomial w f i

def badPolarDegrees (τ : Type*) [Fintype τ] (r : ℕ) : PolarVars τ → ℕ :=
  fun i => match i with
    | none => r
    | some none => 1 + ∑ i, squareDegrees τ r i
    | some (some _) => r-1

lemma badPolarSystem_homogeneous (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    {f : MvPolynomial (PolarVars τ) R} {r : ℕ} (hf : f.IsHomogeneous r) (i : PolarVars τ) :
    (badPolarSystem w l f i).IsHomogeneous (badPolarDegrees τ r i) := by
  classical
  rcases i with _ | (_ | i)
  · exact hf
  · exact (linearPolynomial_homogeneous l).mul (squarePolynomial_homogeneous w l hf)
  · exact polarPolynomial_homogeneous w hf i

end Polynomials

section Evaluation
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma eval_polarPolynomial (w : τ → σ → L) (f : MvPolynomial σ K)
    (y : σ → L) (i : τ) :
    eval y (polarPolynomial w (map (algebraMap K L) f) i) = polarValue w f y i := by
  simp [polarPolynomial, polarValue, pderiv_map, eval_map, aeval_def]

lemma eval_linearPolynomial (l : σ → L) (y : σ → L) :
    eval y (linearPolynomial l) = ∑ j, l j * y j := by
  simp [linearPolynomial]

lemma eval_squarePolynomial (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L) :
    (squarePolynomial w l (map (algebraMap K L) f)).map (eval y) = squareJacobian w l f y := by
  classical
  ext i j
  rcases i with _ | (_ | i)
  · simp [squarePolynomial, squareJacobian, pderiv_map, eval_map, aeval_def]
  · simp [squarePolynomial, squareJacobian]
  · simp [squarePolynomial, squareJacobian, polarPolynomial, polarGradient, pderiv_map,
      eval_map, aeval_def]

end Evaluation
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Map
variable {R S σ τ : Type*} [CommRing R] [CommRing S] [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma map_polarPolynomial (φ : R →+* S) (w : τ → σ → R) (f : MvPolynomial σ R) (i : τ) :
    map φ (polarPolynomial w f i) = polarPolynomial (fun i j => φ (w i j)) (map φ f) i := by
  simp [polarPolynomial, pderiv_map]

lemma map_linearPolynomial (φ : R →+* S) (l : σ → R) :
    map φ (linearPolynomial l) = linearPolynomial (fun j => φ (l j)) := by
  simp [linearPolynomial]

lemma map_squarePolynomial (φ : R →+* S) (w : τ → PolarVars τ → R)
    (l : PolarVars τ → R) (f : MvPolynomial (PolarVars τ) R) :
    (squarePolynomial w l f).map (map φ) =
      squarePolynomial (fun i j => φ (w i j)) (fun j => φ (l j)) (map φ f) := by
  classical
  funext i j
  rcases i with _ | (_ | i)
  · simp [squarePolynomial, pderiv_map]
  · simp [squarePolynomial]
  · simp only [Matrix.map_apply, squarePolynomial, ← pderiv_map, map_polarPolynomial]

lemma map_badPolarSystem (φ : R →+* S) (w : τ → PolarVars τ → R)
    (l : PolarVars τ → R) (f : MvPolynomial (PolarVars τ) R) (i : PolarVars τ) :
    map φ (badPolarSystem w l f i) =
      badPolarSystem (fun i j => φ (w i j)) (fun j => φ (l j)) (map φ f) i := by
  classical
  rcases i with _ | (_ | i)
  · rfl
  · simp only [badPolarSystem, map_mul, map_linearPolynomial, RingHom.map_det,
      RingHom.mapMatrix_apply, map_squarePolynomial]
  · exact map_polarPolynomial φ w f i

end Map
end PermanentBorder.Polar

end OAI
