import OAI.Analysis.GroupDeterminants.RegularTrace

namespace OAI

universe uG um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section IntegralTransfer
variable {G : Type uG} {m : Type um} {r : Type ur} [Group G] [Fintype m] [DecidableEq m]
  [Fintype r] [DecidableEq r]

def divideGroup (q : ℕ) (a : MonoidAlgebra ℤ G) : MonoidAlgebra ℤ G :=
  MonoidAlgebra.ofCoeff (a.coeff.mapRange (fun z => z / (q : ℤ)) (by simp))

theorem kernel_integerReduction (q : ℕ) (a : MonoidAlgebra ℤ G)
    (ha : MonoidAlgebra.mapRingHom G (Int.castRingHom (ZMod q)) a = 0) :
    (q : ℤ) • divideGroup q a = a := by
  apply MonoidAlgebra.ext
  ext g
  have hg := congrArg (fun x : MonoidAlgebra (ZMod q) G => x.coeff g) ha
  change (a.coeff g : ZMod q) = 0 at hg
  have hd : (q : ℤ) ∣ a.coeff g := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (by
    simpa only [MonoidAlgebra.coeff_mapRingHom,
      MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hg)
  rw [MonoidAlgebra.coeff_smul]
  change (q : ℤ) * (a.coeff g / (q : ℤ)) = a.coeff g
  exact Int.mul_ediv_cancel' hd

def toRat : MonoidAlgebra ℤ G →+* MonoidAlgebra ℚ G :=
  MonoidAlgebra.mapRingHom G (Int.castRingHom ℚ)

def toMod (q : ℕ) : MonoidAlgebra ℤ G →+* MonoidAlgebra (ZMod q) G :=
  MonoidAlgebra.mapRingHom G (Int.castRingHom (ZMod q))

omit [Fintype m] [DecidableEq m] [Fintype r] [DecidableEq r] in
theorem map_toRat_zsmul (t : ℤ) (A : Matrix m r (MonoidAlgebra ℤ G)) :
    (t • A).map toRat = (t : ℚ) • A.map toRat := by
  rw [Int.cast_smul_eq_zsmul]
  exact Matrix.map_smul _ _ (fun a => map_zsmul toRat _ a) _

theorem integral_transfer_of_lifts (q : ℕ) (hq : q ≠ 0)
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hP : P * P = P)
    (C : Matrix m m (MonoidAlgebra ℤ G))
    (hC : C.map toRat = P + (q : ℚ) • (1 - P))
    (U : Matrix m r (MonoidAlgebra ℤ G)) (V : Matrix r m (MonoidAlgebra ℤ G))
    (huv : (U * V).map (toMod q) = C.map (toMod q)) :
    ∃ A : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℤ G),
      A.map toRat = transferMatrix (q : ℚ) P (U.map toRat) (V.map toRat) ∧
      IsUnit (A.map toRat) := by
  let W : Matrix m m (MonoidAlgebra ℤ G) := fun i j => divideGroup q ((U * V - C) i j)
  have hw : (q : ℤ) • W = U * V - C := by
    apply Matrix.ext
    intro i j
    apply kernel_integerReduction
    have h := congrFun (congrFun huv i) j
    change toMod q ((U * V) i j - C i j) = 0
    rw [map_sub, sub_eq_zero]
    exact h
  have hwq := congrArg (fun A : Matrix m m (MonoidAlgebra ℤ G) => A.map toRat) hw
  rw [map_toRat_zsmul, Int.cast_natCast, Matrix.map_sub _ (map_sub _) _ _, Matrix.map_mul, hC] at hwq
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hw' : W.map toRat = (q : ℚ)⁻¹ •
      (U.map toRat * V.map toRat - P - (q : ℚ) • (1 - P)) := by
    rw [sub_sub, ← hwq, smul_smul, inv_mul_cancel₀ hq', one_smul]
  refine ⟨Matrix.fromBlocks ((q : ℤ) • 1) V U W, ?_, ?_⟩
  · rw [Matrix.fromBlocks_map, map_toRat_zsmul,
      Int.cast_natCast, Matrix.map_one _ (map_zero _) (map_one _), hw']
    rfl
  · rw [Matrix.fromBlocks_map, map_toRat_zsmul,
      Int.cast_natCast, Matrix.map_one _ (map_zero _) (map_one _), hw']
    exact transferMatrix_isUnit (q : ℚ) hq' P hP (U.map toRat) (V.map toRat)

omit [Fintype m] [DecidableEq m] [Fintype r] [DecidableEq r] in
theorem map_toMod_zsmul (q : ℕ) (t : ℤ) (A : Matrix m r (MonoidAlgebra ℤ G)) :
    (t • A).map (toMod q) = (t : ZMod q) • A.map (toMod q) := by
  rw [Int.cast_smul_eq_zsmul]
  exact Matrix.map_smul _ _ (fun a => map_zsmul (toMod q) _ a) _

omit [Fintype m] [DecidableEq m] [Fintype r] [DecidableEq r] in
theorem reduceGroupTwo_toMod (k : ℕ) (hk : 0 < k) (a : MonoidAlgebra ℤ G) :
    reduceGroupTwo k hk (toMod (2 ^ k) a) = toMod 2 a := by
  apply MonoidAlgebra.ext
  ext g
  simp only [reduceGroupTwo, toMod, MonoidAlgebra.coeff_mapRingHom]
  exact map_intCast (reduceTwo k hk) _

omit [DecidableEq m] [Fintype r] [DecidableEq r] in
theorem integer_projection_square (P : Matrix m m (MonoidAlgebra ℚ G))
    (hP : P * P = P) (D : ℤ) (Z : Matrix m m (MonoidAlgebra ℤ G))
    (hZ : Z.map toRat = (D : ℚ) • P) : Z * Z = D • Z := by
  have hi : Function.Injective (toRat (G := G)) :=
    MonoidAlgebra.map_injective (Int.castRingHom ℚ).toAddMonoidHom Int.cast_injective
  apply Matrix.map_injective hi
  change (Z * Z).map toRat = (D • Z).map toRat
  rw [Matrix.map_mul, map_toRat_zsmul, hZ, Matrix.smul_mul, Matrix.mul_smul, hP]

omit [Fintype r] [DecidableEq r] in

theorem integral_reweight_mod_idempotent (q : ℕ) (D t : ℤ)
    (hDt : D * t = 1 - (q : ℤ)) (Z : Matrix m m (MonoidAlgebra ℤ G))
    (hZ : Z * Z = D • Z) :
    let C := (q : ℤ) • (1 : Matrix m m (MonoidAlgebra ℤ G)) + t • Z
    C.map (toMod q) * C.map (toMod q) = C.map (toMod q) := by
  dsimp only
  have hqt : ((q : ℤ) : ZMod q) = 0 := by simp
  have hdt : (D : ZMod q) * (t : ZMod q) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q)) hDt
    simpa using h
  have hzz : Z.map (toMod q) * Z.map (toMod q) = (D : ZMod q) • Z.map (toMod q) := by
    rw [← Matrix.map_mul, hZ, map_toMod_zsmul]
  simp only [Matrix.map_add _ (map_add _) _ _, map_toMod_zsmul, hqt,
    zero_smul, zero_add]
  rw [Matrix.smul_mul, Matrix.mul_smul, hzz, smul_smul, smul_smul]
  congr 1
  calc
    (t : ZMod q) * (t : ZMod q) * (D : ZMod q) = (t : ZMod q) * ((D : ZMod q) * t) := by ring
    _ = (t : ZMod q) := by rw [hdt, mul_one]

omit [Fintype m] [Fintype r] [DecidableEq r] in
theorem integral_reweight_rational (q : ℕ) (D t : ℤ)
    (hDt : D * t = 1 - (q : ℤ)) (Z : Matrix m m (MonoidAlgebra ℤ G))
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hZ : Z.map toRat = (D : ℚ) • P) :
    ((q : ℤ) • (1 : Matrix m m (MonoidAlgebra ℤ G)) + t • Z).map toRat =
      P + (q : ℚ) • (1 - P) := by
  have hdt : (t : ℚ) * (D : ℚ) = 1 - (q : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hDt
    simpa [mul_comm] using h
  rw [Matrix.map_add _ (map_add _) _ _, map_toRat_zsmul, map_toRat_zsmul,
    Matrix.map_one _ (map_zero _) (map_one _), hZ, smul_smul, hdt]
  simp only [Int.cast_natCast, sub_smul, one_smul, smul_sub]
  abel

theorem integral_transfer (D : ℕ) (hodd : Odd D)
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hP : P * P = P)
    (Z : Matrix m m (MonoidAlgebra ℤ G)) (hZ : Z.map toRat = (D : ℚ) • P)
    (u : Matrix m r (MonoidAlgebra (ZMod 2) G))
    (v : Matrix r m (MonoidAlgebra (ZMod 2) G)) (huv : u * v = Z.map (toMod 2))
    (k : ℕ) (hk : 0 < k) (t : ℤ) (hDt : (D : ℤ) * t = 1 - (2 ^ k : ℕ)) :
    ∃ (U : Matrix m r (MonoidAlgebra ℤ G)) (V : Matrix r m (MonoidAlgebra ℤ G))
      (A : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℤ G)),
      A.map toRat = transferMatrix ((2 ^ k : ℕ) : ℚ) P (U.map toRat) (V.map toRat) ∧
      IsUnit (A.map toRat) := by
  classical
  let q : ℕ := 2 ^ k
  let C : Matrix m m (MonoidAlgebra ℤ G) := (q : ℤ) • 1 + t • Z
  let e : Matrix m m (MonoidAlgebra (ZMod q) G) := C.map (toMod q)
  have hZZ : Z * Z = (D : ℤ) • Z :=
    integer_projection_square P hP D Z (by simpa using hZ)
  have he : e * e = e := integral_reweight_mod_idempotent q D t hDt Z hZZ
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hD2 : (D : ZMod 2) = 1 := by
    obtain ⟨a, rfl⟩ := hodd
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, htwo, zero_mul,
      zero_add, Nat.cast_one]
  have hq2 : (q : ZMod 2) = 0 := by
    simp only [q, Nat.cast_pow, Nat.cast_ofNat, htwo, zero_pow hk.ne']
  have ht2 : (t : ZMod 2) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 2)) hDt
    push_cast at h
    simpa only [hD2, htwo, zero_pow hk.ne', one_mul, sub_zero] using h
  have hC2 : C.map (toMod 2) = Z.map (toMod 2) := by
    simp only [C, Matrix.map_add _ (map_add _) _ _, map_toMod_zsmul,
      Int.cast_natCast, hq2, ht2, zero_smul, one_smul, zero_add]
  have he2 : e.map (reduceGroupTwo k hk) = C.map (toMod 2) := by
    apply Matrix.ext
    intro i j
    exact reduceGroupTwo_toMod k hk (C i j)
  obtain ⟨u', v', hu'v'⟩ := lift_binary_factorization k hk e he u v (by
    rw [he2, hC2]
    exact huv)
  have hs := integerReduction_surjective (G := G) q
  choose U₀ hU₀ using fun i j => hs (u' i j)
  choose V₀ hV₀ using fun i j => hs (v' i j)
  let U : Matrix m r (MonoidAlgebra ℤ G) := U₀
  let V : Matrix r m (MonoidAlgebra ℤ G) := V₀
  have hU : U.map (toMod q) = u' := Matrix.ext hU₀
  have hV : V.map (toMod q) = v' := Matrix.ext hV₀
  have hUV : (U * V).map (toMod q) = C.map (toMod q) := by
    rw [Matrix.map_mul, hU, hV, hu'v']
  have hC : C.map toRat = P + (q : ℚ) • (1 - P) :=
    integral_reweight_rational q D t hDt Z P (by simpa using hZ)
  obtain ⟨A, ha, haunit⟩ := integral_transfer_of_lifts q
    (pow_ne_zero _ (by decide)) P hP C hC U V hUV
  exact ⟨U, V, A, ha, haunit⟩

theorem integral_transfer_of_congruence (D : ℕ) (hodd : Odd D)
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hP : P * P = P)
    (Z : Matrix m m (MonoidAlgebra ℤ G)) (hZ : Z.map toRat = (D : ℚ) • P)
    (u : Matrix m r (MonoidAlgebra (ZMod 2) G))
    (v : Matrix r m (MonoidAlgebra (ZMod 2) G)) (huv : u * v = Z.map (toMod 2))
    (k : ℕ) (hk : 0 < k) (hkD : Nat.ModEq D (2 ^ k) 1) :
    ∃ (U : Matrix m r (MonoidAlgebra ℤ G)) (V : Matrix r m (MonoidAlgebra ℤ G))
      (A : Matrix (r ⊕ m) (r ⊕ m) (MonoidAlgebra ℤ G)),
      A.map toRat = transferMatrix ((2 ^ k : ℕ) : ℚ) P (U.map toRat) (V.map toRat) ∧
      IsUnit (A.map toRat) := by
  obtain ⟨t, ht⟩ := Nat.modEq_iff_dvd.mp hkD
  exact integral_transfer D hodd P hP Z hZ u v huv k hk t (by simpa using ht.symm)

end IntegralTransfer

end GroupRingDeterminant

end

end OAI
