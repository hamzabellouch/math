import OAI.Analysis.GroupDeterminants.Defects

namespace OAI

universe uG uA um ur

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section ModularKernel
variable (k : ℕ) (hk : 0 < k)

def reduceTwo : ZMod (2 ^ k) →+* ZMod 2 :=
  ZMod.castHom (dvd_pow_self 2 (Nat.ne_of_gt hk)) (ZMod 2)

theorem kernel_reduceTwo (a : ZMod (2 ^ k)) (ha : reduceTwo k hk a = 0) :
    a = 2 * (a.val / 2 : ℕ) := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩
  have hv : (a.val : ZMod 2) = 0 := by
    rw [← map_natCast (reduceTwo k hk), ZMod.natCast_zmod_val]
    exact ha
  have hd : 2 ∣ a.val := (ZMod.natCast_eq_zero_iff _ _).mp hv
  calc
    a = (a.val : ZMod (2 ^ k)) := (ZMod.natCast_zmod_val a).symm
    _ = ((2 * (a.val / 2) : ℕ) : ZMod (2 ^ k)) := by rw [Nat.mul_div_cancel' hd]
    _ = _ := by push_cast; rfl

variable {G : Type uG} [Group G]

def reduceGroupTwo : MonoidAlgebra (ZMod (2 ^ k)) G →+* MonoidAlgebra (ZMod 2) G :=
  MonoidAlgebra.mapRingHom G (reduceTwo k hk)

def halfGroup (a : MonoidAlgebra (ZMod (2 ^ k)) G) :
    MonoidAlgebra (ZMod (2 ^ k)) G :=
  MonoidAlgebra.ofCoeff (a.coeff.mapRange
    (fun c => (c.val / 2 : ℕ)) (by simp))

theorem kernel_reduceGroupTwo (a : MonoidAlgebra (ZMod (2 ^ k)) G)
    (ha : reduceGroupTwo k hk a = 0) : a = 2 * halfGroup k a := by
  apply MonoidAlgebra.ext
  ext g
  have hg := congrArg (fun c : MonoidAlgebra (ZMod 2) G => c.coeff g) ha
  have hc : reduceTwo k hk (a.coeff g) = 0 := by
    simpa only [reduceGroupTwo, MonoidAlgebra.coeff_mapRingHom,
      MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hg
  simpa [two_mul, halfGroup, MonoidAlgebra.coeff_add] using kernel_reduceTwo k hk _ hc

theorem twice_pow_eq_zero {A : Type uA} [Ring A] [Algebra (ZMod (2 ^ k)) A] (v : A) :
    (2 * v) ^ k = 0 := by
  have htwo : (2 : ZMod (2 ^ k)) ^ k = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2 ^ k)
  have ht : (2 : A) ^ k = 0 := by
    simpa only [map_pow, map_ofNat, map_zero] using
      congrArg (algebraMap (ZMod (2 ^ k)) A) htwo
  have hc : Commute (2 : A) v := by
    simpa only [Nat.cast_ofNat] using Nat.cast_commute 2 v
  rw [hc.mul_pow, ht, zero_mul]

theorem matrix_kernel_nilpotent {m : Type um} [Fintype m] [DecidableEq m]
    (W : Matrix m m (MonoidAlgebra (ZMod (2 ^ k)) G))
    (hW : W.map (reduceGroupTwo k hk) = 0) : W ^ k = 0 := by
  let V : Matrix m m (MonoidAlgebra (ZMod (2 ^ k)) G) := fun i j => halfGroup k (W i j)
  have hv : W = 2 * V := by
    rw [two_mul]
    apply Matrix.ext
    intro i j
    have hc : reduceGroupTwo k hk (W i j) = 0 := congrFun (congrFun hW i) j
    change W i j = halfGroup k (W i j) + halfGroup k (W i j)
    simpa only [two_mul] using kernel_reduceGroupTwo k hk _ hc
  rw [hv]
  exact twice_pow_eq_zero k V

theorem reduceGroupTwo_surjective :
    Function.Surjective (reduceGroupTwo k hk (G := G)) :=
  MonoidAlgebra.map_surjective _ (ZMod.castHom_surjective (dvd_pow_self 2 (Nat.ne_of_gt hk)))

theorem integerReduction_surjective (q : ℕ) : Function.Surjective
    (MonoidAlgebra.mapRingHom G (Int.castRingHom (ZMod q))) :=
  MonoidAlgebra.map_surjective _ ZMod.intCast_surjective

end ModularKernel

section ModularFactorization
variable {G : Type uG} {m : Type um} {r : Type ur} [Group G] [Fintype m] [DecidableEq m] [Fintype r]

theorem lift_binary_factorization (k : ℕ) (hk : 0 < k)
    (e : Matrix m m (MonoidAlgebra (ZMod (2 ^ k)) G)) (he : e * e = e)
    (u : Matrix m r (MonoidAlgebra (ZMod 2) G))
    (v : Matrix r m (MonoidAlgebra (ZMod 2) G))
    (huv : u * v = e.map (reduceGroupTwo k hk)) :
    ∃ u' : Matrix m r (MonoidAlgebra (ZMod (2 ^ k)) G),
    ∃ v' : Matrix r m (MonoidAlgebra (ZMod (2 ^ k)) G), u' * v' = e := by
  classical
  have hs := reduceGroupTwo_surjective (G := G) k hk
  choose uRaw hu₀ using fun i j => hs (u i j)
  choose vRaw hv₀ using fun i j => hs (v i j)
  let u₀ : Matrix m r (MonoidAlgebra (ZMod (2 ^ k)) G) := uRaw
  let v₀ : Matrix r m (MonoidAlgebra (ZMod (2 ^ k)) G) := vRaw
  have hu : Matrix.map u₀ (reduceGroupTwo k hk) = u := Matrix.ext hu₀
  have hv : Matrix.map v₀ (reduceGroupTwo k hk) = v := Matrix.ext hv₀
  apply lift_rectangular_factorization e he u₀ v₀ k
  apply matrix_kernel_nilpotent k hk
  rw [Matrix.map_sub _ (map_sub _) _ _]
  simp only [Matrix.map_mul, hu, hv]
  rw [Matrix.mul_assoc (e.map _) u, huv]
  have he' : e.map (reduceGroupTwo k hk) * e.map (reduceGroupTwo k hk) =
      e.map (reduceGroupTwo k hk) := by rw [← Matrix.map_mul, he]
  rw [he', he', sub_self]

end ModularFactorization

theorem exists_binary_modulus (D : ℕ) (hD : 0 < D) (hodd : Odd D) :
    ∃ k : ℕ, 0 < k ∧ 1 < 2 ^ k ∧ Nat.ModEq D (2 ^ k) 1 := by
  have hk : 0 < D.totient := Nat.totient_pos.mpr hD
  refine ⟨D.totient, hk, one_lt_pow₀ (by decide) (Nat.ne_of_gt hk), ?_⟩
  exact Nat.ModEq.pow_totient (Nat.coprime_two_right.mpr hodd).symm

end GroupRingDeterminant

end

end OAI
