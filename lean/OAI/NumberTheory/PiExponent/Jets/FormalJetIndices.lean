import OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

@[simp] theorem exponentVector_coe {n : ℕ} (d : Fin n →₀ ℕ) :
    InterpolationMatrix.exponentVector (fun i => d i) = d := by
  ext i
  simp

theorem cast_finsupp_weight {n : ℕ} (V : Fin n → ℚ) (d : Fin n →₀ ℕ) :
    (Finsupp.weight V d : ℝ) = ∑ i, (V i : ℝ) * (d i : ℝ) := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_natCast, mul_comm]

def rationalJetIndexEquiv {n : ℕ} (V : Fin n → ℚ) (hV : ∀ i, 0 < V i) (H : ℚ) :
    {d : Fin n →₀ ℕ // Finsupp.weight V d < H} ≃
      ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ)) where
  toFun d := ⟨fun i => d.val i, by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
    rw [← cast_finsupp_weight]
    exact_mod_cast d.property⟩
  invFun a := ⟨InterpolationMatrix.exponentVector a.val, by
    have ha := (mem_strictWeightedSimplex
      (fun i => by exact_mod_cast hV i)).mp a.property
    have hcast : (Finsupp.weight V (InterpolationMatrix.exponentVector a.val) : ℝ) <
        (H : ℝ) := by
      simpa only [cast_finsupp_weight, InterpolationMatrix.exponentVector_apply] using ha
    exact_mod_cast hcast⟩
  left_inv d := by apply Subtype.ext; exact exponentVector_coe d.val
  right_inv a := by apply Subtype.ext; funext i; simp

@[simp] theorem rationalJetIndexEquiv_apply_val {n : ℕ}
    (V : Fin n → ℚ) (hV : ∀ i, 0 < V i) (H : ℚ)
    (d : {d : Fin n →₀ ℕ // Finsupp.weight V d < H}) :
    (rationalJetIndexEquiv V hV H d).val = fun i => d.val i := rfl

@[simp] theorem rationalJetIndexEquiv_symm_val {n : ℕ}
    (V : Fin n → ℚ) (hV : ∀ i, 0 < V i) (H : ℚ)
    (a : ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ))) :
    ((rationalJetIndexEquiv V hV H).symm a).val =
      InterpolationMatrix.exponentVector a.val := rfl

theorem polynomialOfCoefficients_of_weighted {m : ℕ}
    (W : Fin (m + 1) → ℝ) (hW : ∀ i, 0 < W i) (H : ℝ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : PiExponentApprox.HasWeightedDegreeLE W H p) :
    polynomialOfCoefficients (realWeightedSimplex W H)
      (fun a => p.coeff (InterpolationMatrix.exponentVector a.val)) = p := by
  classical
  ext d
  by_cases hd : (fun i => d i) ∈ realWeightedSimplex W H
  · have he := polynomialOfCoefficients_coeff (realWeightedSimplex W H)
      (fun a => p.coeff (InterpolationMatrix.exponentVector a.val))
      ⟨fun i => d i, hd⟩
    simpa only [exponentVector_coe] using he
  · have hpzero : p.coeff d = 0 := by
      by_contra hne
      apply hd
      apply (mem_realWeightedSimplex hW).mpr
      simpa only [PiExponentApprox.monomialWeight, mul_comm] using
        hp d (MvPolynomial.mem_support_iff.mpr hne)
    rw [hpzero]
    by_contra hne
    have hmem := MvPolynomial.mem_support_iff.mpr hne
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp
      (polynomialOfCoefficients_support _ _ hmem)
    apply hd
    have hea : a = fun i => d i := by
      funext i
      simpa only [InterpolationMatrix.exponentVector_apply] using
        congrArg (fun e : Fin (m + 1) →₀ ℕ => e i) he
    simpa only [← hea] using ha

end PiExponent.FormalMatrixBridge

end

end OAI
