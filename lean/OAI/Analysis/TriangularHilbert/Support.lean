import OAI.Analysis.TriangularHilbert.MatrixSupport

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sqrt_mul_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hPQ : P * Q = 0) : CFC.sqrt P * Q = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  change (CFC.sqrt P * Q)ᴴ * (CFC.sqrt P * Q) = 0
  rw [Matrix.conjTranspose_mul, hs.eq, ← Matrix.mul_assoc,
    Matrix.mul_assoc Qᴴ, CFC.sqrt_mul_sqrt_self P hP.nonneg,
    Matrix.mul_assoc, hPQ, mul_zero]

lemma mul_sqrt_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQP : Q * P = 0) : Q * CFC.sqrt P = 0 := by
  have ht : P * Qᴴ = 0 := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hQP
  have hz := sqrt_mul_eq_zero_of_mul_eq_zero hP ht
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  simpa only [Matrix.conjTranspose_mul, hs.eq, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hz

lemma sqrt_add_projection {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    CFC.sqrt (P + Q) = CFC.sqrt P + Q := by
  apply CFC.sqrt_unique
  · have hsQ := sqrt_mul_eq_zero_of_mul_eq_zero hP hPQ
    have hQs := mul_sqrt_eq_zero_of_mul_eq_zero hP hQP
    simp only [add_mul, mul_add, hsQ, hQs, hQQ,
      CFC.sqrt_mul_sqrt_self P hP.nonneg, add_zero, zero_add]
  · exact add_nonneg (CFC.sqrt_nonneg P) hQ.nonneg

lemma energy_add_projection {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    energy (P + Q) = energy P + traceReal Q := by
  rw [energy, sqrt_add_projection hP hQ hQQ hPQ hQP]
  simp only [add_mul, mul_add, hPQ, mul_sqrt_eq_zero_of_mul_eq_zero hP hQP,
    hQQ, add_zero, zero_add, traceReal_add, energy]

lemma energyGradient_add_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hQK : Q * K = 0) :
    energyGradient (P + Q) K = energyGradient P K := by
  simp only [energyGradient_apply, sqrt_add_projection hP hQ hQQ hPQ hQP,
    add_mul, hQK, add_zero]

lemma hessianCost_add_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hPD : (P + Q).PosDef) : hessianCost (P + Q) K = hessianCost P K := by
  let A := CFC.sqrt P
  let E := 1 - Q
  let Y := sqrtInverse hPD K
  let Z := E * Y * E
  have hAQ : A * Q = 0 := sqrt_mul_eq_zero_of_mul_eq_zero hP hPQ
  have hQA : Q * A = 0 := mul_sqrt_eq_zero_of_mul_eq_zero hP hQP
  have hQE : Q * E = 0 := by simp [E, mul_sub, hQQ]
  have hEQ : E * Q = 0 := by simp [E, sub_mul, hQQ]
  have hAE : A * E = A := by simp [E, mul_sub, hAQ]
  have hEA : E * A = A := by simp [E, sub_mul, hQA]
  have hKE : K * E = K := by simp [E, mul_sub, hKQ]
  have hEK : E * K = K := by simp [E, sub_mul, hQK]
  have hY : sylv (A + Q) Y = K := by
    simpa only [sqrt_add_projection hP hQ hQQ hPQ hQP] using sqrtInverse_solves hPD K
  have hZ : sylv A Z = K := by
    have hm := congrArg (fun B => E * B * E) hY
    simp only [sylv, add_mul, mul_add, Matrix.mul_assoc] at hm ⊢
    simp only [← Matrix.mul_assoc E A, hEA, ← Matrix.mul_assoc E Q, hEQ,
      zero_mul, add_zero, hQE, mul_zero,
      hEK, hKE] at hm
    simpa only [Z, Matrix.mul_assoc, ← Matrix.mul_assoc A E, hAE,
      ← Matrix.mul_assoc E A, hEA] using hm
  have hQZ : Q * Z = 0 := by simp only [Z, ← Matrix.mul_assoc, hQE, zero_mul]
  have hZQ : Z * Q = 0 := by simp only [Z, Matrix.mul_assoc, hEQ, mul_zero]
  have hZ' : sylv (CFC.sqrt (P + Q)) Z = K := by
    rw [sqrt_add_projection hP hQ hQQ hPQ hQP]
    change sylv (A + Q) Z = K
    simpa [sylv, add_mul, mul_add, hQZ, hZQ] using hZ
  exact (rootCost_eq_of_solution
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P + Q))) hZ').trans
    (rootCost_eq_of_solution (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hZ).symm

lemma exists_kernel_projection {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    ∃ Q : Matrix ι ι ℂ, Q.PosSemidef ∧ Q * Q = Q ∧ P * Q = 0 ∧ Q * P = 0 ∧
      (P + Q).PosDef := by
  let ev := hP.isHermitian.eigenvalues
  let U := hP.isHermitian.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (ev i : ℂ))
  let q : Matrix ι ι ℂ := Matrix.diagonal (fun i => if ev i = 0 then 1 else 0)
  let Q := f q
  have hD : f D = P := hP.isHermitian.spectral_theorem.symm
  have hq : q.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ (if ev i = 0 then (1 : ℂ) else 0)
    split_ifs <;> simp
  have hQ : Q.PosSemidef := by
    simpa only [Q, f, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hq.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  have hqq : q * q = q := by
    simp only [q, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  have hQQ : Q * Q = Q := by exact (map_mul f q q).symm.trans (congrArg f hqq)
  have hDq : D * q = 0 := by
    simp only [D, q, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_zero]
    congr 1
    ext i
    split_ifs with hi <;> simp [hi]
  have hPQ : P * Q = 0 := by
    rw [← hD]
    change f D * f q = 0
    rw [← map_mul, hDq, map_zero]
  have hQP : Q * P = 0 := by
    simpa only [Matrix.conjTranspose_mul, hQ.isHermitian.eq, hP.isHermitian.eq,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hPQ
  have hpos : (D + q).PosDef := by
    simp only [D, q, Matrix.diagonal_add]
    apply Matrix.PosDef.diagonal
    intro i
    change 0 < (ev i : ℂ) + (if ev i = 0 then 1 else 0)
    by_cases hi : ev i = 0
    · simp [hi]
    · simp only [hi, ite_false, add_zero]
      exact_mod_cast lt_of_le_of_ne (hP.eigenvalues_nonneg i) (Ne.symm hi)
  have hu : IsUnit (P + Q) := by
    have hh := hpos.isUnit.map f.toMonoidHom
    change IsUnit (f (D + q)) at hh
    simpa only [map_add, hD] using hh
  exact ⟨Q, hQ, hQQ, hPQ, hQP, (hP.add hQ).posDef_iff_isUnit.mpr hu⟩

lemma deriv_mul_projection_eq_zero {P : ℝ → Matrix ι ι ℂ} {U Q : Matrix ι ι ℂ}
    {x : ℝ} (hd : HasDerivAt P U x) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0) : U * Q = 0 := by
  have hh := hd.mul_const Q
  have he : HasDerivAt (fun _ : ℝ => (0 : Matrix ι ι ℂ)) (U * Q) x :=
    hh.congr_of_eventuallyEq (hz.mono fun _ ht => ht.symm)
  exact he.unique (hasDerivAt_const x 0)

lemma projection_mul_deriv_eq_zero {P : ℝ → Matrix ι ι ℂ} {U Q : Matrix ι ι ℂ}
    {x : ℝ} (hd : HasDerivAt P U x) (hz : ∀ᶠ t in 𝓝 x, Q * P t = 0) : Q * U = 0 := by
  have hh := hd.const_mul Q
  have he : HasDerivAt (fun _ : ℝ => (0 : Matrix ι ι ℂ)) (Q * U) x :=
    hh.congr_of_eventuallyEq (hz.mono fun _ ht => ht.symm)
  exact he.unique (hasDerivAt_const x 0)

omit [DecidableEq ι] in
lemma hermitian_mul_zero_flip {P Q : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (h : P * Q = 0) : Q * P = 0 := by
  simpa only [Matrix.conjTranspose_mul, hP.eq, hQ.eq, Matrix.conjTranspose_zero] using
    congrArg Matrix.conjTranspose h

noncomputable def hessianPair (P K L : Matrix ι ι ℂ) : ℝ :=
  (hessianCost P (K + L) - hessianCost P (K - L)) / 4

lemma hessianPair_eq_PD {P : Matrix ι ι ℂ} (hP : P.PosDef)
    (K L : Matrix ι ι ℂ) : hessianPair P K L = hessianPairPD hP K L := by
  have hs := hessianPairPD_symm hP K L
  unfold hessianPair
  rw [← hessianPairPD_self hP, ← hessianPairPD_self hP]
  simp only [hessianPairPD, map_add, map_sub, hsReal_add_left, hsReal_add_right,
    hsReal_sub_left, hsReal_sub_right] at hs ⊢
  linarith

lemma hessianPair_add_projection {P Q K L : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hKQ : K * Q = 0) (hQK : Q * K = 0) (hLQ : L * Q = 0) (hQL : Q * L = 0)
    (hPD : (P + Q).PosDef) : hessianPair (P + Q) K L = hessianPair P K L := by
  unfold hessianPair
  rw [hessianCost_add_projection hP hQ hQQ hPQ hQP
    (by simp [add_mul, hKQ, hLQ]) (by simp [mul_add, hQK, hQL]) hPD,
    hessianCost_add_projection hP hQ hQQ hPQ hQP
    (by simp [sub_mul, hKQ, hLQ]) (by simp [mul_sub, hQK, hQL]) hPD]

theorem energy_supported_path_hasDerivAt {P : ℝ → Matrix ι ι ℂ}
    {Q U : Matrix ι ι ℂ} {x : ℝ}
    (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) (hPD : (P x + Q).PosDef)
    (hn : ∀ᶠ t in 𝓝 x, (P t).PosSemidef) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0)
    (hd : HasDerivAt P U x) :
    HasDerivAt (fun t => energy (P t)) (energyGradient (P x) U) x := by
  have hzl : ∀ᶠ t in 𝓝 x, Q * P t = 0 := by
    filter_upwards [hn, hz] with t ht htz
    exact hermitian_mul_zero_flip ht.isHermitian hQ.isHermitian htz
  have hQU := projection_mul_deriv_eq_zero hd hzl
  have hnonneg : ∀ᶠ t in 𝓝 x, 0 ≤ P t + Q := hn.mono fun _ ht => (ht.add hQ).nonneg
  have hh := (energy_path_hasDerivAt hPD hnonneg (hd.add_const Q)).sub_const (traceReal Q)
  rw [energyGradient_add_projection hn.self_of_nhds hQ hQQ hz.self_of_nhds
    hzl.self_of_nhds hQU] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hn, hz, hzl] with t ht hr hl
  rw [energy_add_projection ht hQ hQQ hr hl]
  ring

theorem energyGradient_supported_path_hasDerivAt {P K : ℝ → Matrix ι ι ℂ}
    {Q U V : Matrix ι ι ℂ} {x : ℝ}
    (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) (hPD : (P x + Q).PosDef)
    (hn : ∀ᶠ t in 𝓝 x, (P t).PosSemidef) (hz : ∀ᶠ t in 𝓝 x, P t * Q = 0)
    (hK : ∀ᶠ t in 𝓝 x, (K t).IsHermitian) (hkz : ∀ᶠ t in 𝓝 x, K t * Q = 0)
    (hdP : HasDerivAt P U x) (hdK : HasDerivAt K V x) :
    HasDerivAt (fun t => energyGradient (P t) (K t))
      (hessianPair (P x) (K x) U + energyGradient (P x) V) x := by
  have hzl : ∀ᶠ t in 𝓝 x, Q * P t = 0 := by
    filter_upwards [hn, hz] with t ht htz
    exact hermitian_mul_zero_flip ht.isHermitian hQ.isHermitian htz
  have hkzl : ∀ᶠ t in 𝓝 x, Q * K t = 0 := by
    filter_upwards [hK, hkz] with t ht htz
    exact hermitian_mul_zero_flip ht hQ.isHermitian htz
  have hUQ := deriv_mul_projection_eq_zero hdP hz
  have hQU := projection_mul_deriv_eq_zero hdP hzl
  have hQV := projection_mul_deriv_eq_zero hdK hkzl
  have hnonneg : ∀ᶠ t in 𝓝 x, 0 ≤ P t + Q := hn.mono fun _ ht => (ht.add hQ).nonneg
  have hh := energyGradient_path_hasDerivAt hPD hnonneg hK.self_of_nhds
    (hdP.add_const Q) hdK
  rw [← hessianPair_eq_PD, hessianPair_add_projection hn.self_of_nhds hQ hQQ
    hz.self_of_nhds hzl.self_of_nhds hkz.self_of_nhds hkzl.self_of_nhds hUQ hQU hPD,
    energyGradient_add_projection hn.self_of_nhds hQ hQQ hz.self_of_nhds
      hzl.self_of_nhds hQV] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [hn, hz, hzl, hkzl] with t ht hr hl hkl
  exact (energyGradient_add_projection ht hQ hQQ hr hl hkl).symm

end TriangularHilbert.MatrixEnergy
end

end OAI
