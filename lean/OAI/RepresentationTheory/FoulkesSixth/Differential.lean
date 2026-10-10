import Mathlib

namespace OAI

noncomputable section

namespace Foulkes.Differential
open MvPolynomial

abbrev Poly (m n : ℕ) := MvPolynomial (Fin m × Fin n) ℂ

def shift {m n : ℕ} (u v : Fin m) : Derivation ℂ (Poly m n) (Poly m n) :=
  MvPolynomial.mkDerivation ℂ fun ij => if ij.1 = u then X (v, ij.2) else 0

@[simp] theorem shift_X {m n : ℕ} (u v : Fin m) (ij : Fin m × Fin n) :
    shift (n := n) u v (X ij) = if ij.1 = u then X (v, ij.2) else 0 := by
  simp [shift]

@[simp] theorem derivation_sum_apply {m n : ℕ} {ι : Type*}
    (s : Finset ι) (D : ι → Derivation ℂ (Poly m n) (Poly m n)) (f : Poly m n) :
    (∑ k ∈ s, D k) f = ∑ k ∈ s, D k f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => simp [Finset.sum_insert hx, ih]

theorem shift_eq_sum {m n : ℕ} (u v : Fin m) :
    shift (n := n) u v = ∑ k : Fin n, (X (v, k) : Poly m n) •
      (pderiv (u, k) : Derivation ℂ (Poly m n) (Poly m n)) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨r, k⟩
  simp only [shift_X, derivation_sum_apply, Derivation.smul_apply, pderiv_X]
  by_cases h : r = u
  · subst r
    simp [Pi.single_apply, Prod.mk.injEq]
  · simp [Prod.mk.injEq, h]

theorem shift_commutator {m n : ℕ} {u v : Fin m} (_hne : u ≠ v) :
    ⁅shift (n := n) v u, shift (n := n) u v⁆ =
      shift (n := n) u u - shift (n := n) v v := by
  apply MvPolynomial.derivation_ext
  rintro ⟨r, k⟩
  simp only [Derivation.commutator_apply, Derivation.sub_apply, shift_X]
  split_ifs <;> simp_all [sub_eq_add_neg]

def rowWeight {m n : ℕ} (u : Fin m) (ij : Fin m × Fin n) : ℕ :=
  if ij.1 = u then 1 else 0

theorem euler {m n : ℕ} (u : Fin m) {f : Poly m n} {p : ℕ}
    (hf : f.IsWeightedHomogeneous (rowWeight u) p) :
    shift (n := n) u u f = (p : ℂ) • f := by
  have h := hf.sum_weight_X_mul_pderiv
  rw [shift_eq_sum]
  simp only [derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]
  have hs : (∑ i : Fin m × Fin n, rowWeight u i • (X i * pderiv i f)) =
      ∑ k : Fin n, X (u, k) * pderiv (u, k) f := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [rowWeight]
  rw [hs] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

theorem shift_lowers {m n : ℕ} {u v : Fin m} (huv : u ≠ v)
    {f : Poly m n} {p : ℕ}
    (hf : f.IsWeightedHomogeneous (rowWeight u) (p + 1)) :
    (shift u v f).IsWeightedHomogeneous (rowWeight u) p := by
  rw [shift_eq_sum, derivation_sum_apply]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro k _
  simp only [Derivation.smul_apply, smul_eq_mul]
  have hd : (pderiv (u, k) f).IsWeightedHomogeneous (rowWeight u) p :=
    hf.pderiv (by simp [rowWeight])
  have hx : (X (v, k) : Poly m n).IsWeightedHomogeneous (rowWeight u) 0 := by
    simpa [rowWeight, Ne.symm huv] using
      (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (rowWeight u) (v, k))
  simpa using hx.mul hd

theorem pderiv_zero_degree {m n : ℕ} {u : Fin m} {f : Poly m n}
    (hf : f.IsWeightedHomogeneous (rowWeight u) 0) (k : Fin n) :
    pderiv (u, k) f = 0 := by
  ext d
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero]
  have hc : f.coeff (d + Finsupp.single (u, k) 1) = 0 :=
    hf.coeff_eq_zero _ (by simp [map_add, Finsupp.weight_single, rowWeight])
  simp [hc]

theorem shift_zero_degree {m n : ℕ} {u v : Fin m} {f : Poly m n}
    (hf : f.IsWeightedHomogeneous (rowWeight u) 0) : shift u v f = 0 := by
  rw [shift_eq_sum, derivation_sum_apply]
  simp [pderiv_zero_degree hf]

theorem shift_nilpotent {m n : ℕ} {u v : Fin m} (huv : u ≠ v)
    {f : Poly m n} {p : ℕ} (hf : f.IsWeightedHomogeneous (rowWeight u) p) :
    ((shift u v).toLinearMap ^ (p + 1)) f = 0 := by
  induction p generalizing f with
  | zero => simpa using shift_zero_degree (v := v) hf
  | succ p ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (shift_lowers huv hf)

theorem shift_triple {m n : ℕ} {u v : Fin m} (huv : u ≠ v)
    (hH : shift (n := n) v v - shift (n := n) u u ≠ 0) :
    IsSl2Triple (shift (n := n) v v - shift (n := n) u u)
      (shift (n := n) u v) (shift (n := n) v u) where
  h_ne_zero := hH
  lie_e_f := shift_commutator (Ne.symm huv)
  lie_h_e_nsmul := by
    have hvu := Ne.symm huv
    apply MvPolynomial.derivation_ext
    rintro ⟨r, k⟩
    simp only [Derivation.commutator_apply, Derivation.sub_apply, shift_X, map_sub,
      two_nsmul, Derivation.add_apply]
    split_ifs <;> simp_all [sub_eq_add_neg]
  lie_h_f_nsmul := by
    have hvu := Ne.symm huv
    apply MvPolynomial.derivation_ext
    rintro ⟨r, k⟩
    simp only [Derivation.commutator_apply, Derivation.sub_apply, shift_X, map_sub,
      two_nsmul, Derivation.add_apply, Derivation.neg_apply]
    split_ifs <;> simp_all [sub_eq_add_neg]

theorem shift_kernel_zero {m n : ℕ} {u v : Fin m} (huv : u ≠ v)
    {f : Poly m n} {p q : ℕ}
    (hp : f.IsWeightedHomogeneous (rowWeight u) p)
    (hq : f.IsWeightedHomogeneous (rowWeight v) q)
    (hpq : q < p) (hDf : shift u v f = 0) : f = 0 := by
  by_contra hne
  have hweight : (shift (n := n) v v - shift (n := n) u u) f =
      ((q : ℂ) - p) • f := by
    rw [Derivation.sub_apply, euler v hq, euler u hp, sub_smul]
  have hH : shift (n := n) v v - shift (n := n) u u ≠ 0 := by
    intro hzero
    have hscalar : (q : ℂ) - p ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast (Nat.ne_of_lt hpq)
    rw [hzero, Derivation.zero_apply] at hweight
    exact (smul_ne_zero hscalar hne) hweight.symm
  let t := shift_triple huv hH
  have hprimitive : t.HasPrimitiveVectorWith f ((q : ℂ) - p) :=
    { ne_zero := hne, lie_h := hweight, lie_e := hDf }
  let E := LieModule.toEnd ℂ (Derivation ℂ (Poly m n) (Poly m n)) (Poly m n)
    (shift (n := n) v u)
  have hnil : ∃ k : ℕ, (E ^ k) f = 0 :=
    ⟨q + 1, shift_nilpotent (Ne.symm huv) hq⟩
  obtain ⟨k, hk₁, hk₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hne hnil
  have hrec := hprimitive.lie_e_pow_succ_toEnd_f k
  change shift u v ((E ^ (k + 1)) f) =
    ((k + 1 : ℂ) * ((q : ℂ) - p - k)) • ((E ^ k) f) at hrec
  rw [hk₂, map_zero, eq_comm, smul_eq_zero_iff_left hk₁, mul_eq_zero,
    sub_eq_zero] at hrec
  have heq : (q : ℂ) - p = k := hrec.resolve_left (Nat.cast_add_one_ne_zero k)
  have heq' : q = k + p := by exact_mod_cast (sub_eq_iff_eq_add.mp heq)
  omega

theorem shift_injOn {m n : ℕ} {u v : Fin m} (huv : u ≠ v) {p q : ℕ}
    (hpq : q < p) :
    Set.InjOn (shift (n := n) u v)
      {f | f.IsWeightedHomogeneous (rowWeight u) p ∧
        f.IsWeightedHomogeneous (rowWeight v) q} := by
  intro f hf g hg hfg
  apply sub_eq_zero.mp
  exact shift_kernel_zero huv (hf.1.sub hg.1) (hf.2.sub hg.2) hpq
    (by rw [map_sub, hfg, sub_self])

theorem nilpotence_raise {M : Type*} [AddCommGroup M] [Module ℂ M]
    (D E H : Module.End ℂ M)
    (hDE : ∀ x, D (E x) = E (D x) - H x)
    (hHD : ∀ x, H (D x) = D (H x) - (2 : ℂ) • D x)
    {x : M} {μ : ℂ} (hx : H x = μ • x) {L : ℕ}
    (hL : (D ^ L) x = 0) : (D ^ (L + 1)) (E x) = 0 := by
  induction L generalizing x μ with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hL
    simp [hL]
  | succ L ih =>
    have hxD : H (D x) = (μ - 2) • D x := by
      rw [hHD, hx, map_smul, sub_smul]
    have hLD : (D ^ L) (D x) = 0 := by
      simpa only [pow_succ, Module.End.mul_apply] using hL
    have hED := ih hxD hLD
    rw [pow_succ, Module.End.mul_apply, hDE, map_sub, hx, map_smul]
    change (D ^ (L + 1)) (E (D x)) - μ • (D ^ (L + 1)) x = 0
    rw [hED, hL, smul_zero, sub_self]

theorem shift_power_kernel_zero {m n : ℕ} {u v : Fin m} (huv : u ≠ v)
    {f : Poly m n} {p q L : ℕ}
    (hp : f.IsWeightedHomogeneous (rowWeight u) p)
    (hq : f.IsWeightedHomogeneous (rowWeight v) q)
    (hpq : q + L ≤ p) (hDf : ((shift u v).toLinearMap ^ L) f = 0) : f = 0 := by
  by_cases hL : L = 0
  · simpa [hL] using hDf
  by_contra hne
  have hpq' : q < p := by omega
  have hweight : (shift (n := n) u u - shift (n := n) v v) f =
      ((p - q : ℕ) : ℂ) • f := by
    rw [Derivation.sub_apply, euler u hp, euler v hq,
      Nat.cast_sub (Nat.le_of_lt hpq'), sub_smul]
  have hH : shift (n := n) u u - shift (n := n) v v ≠ 0 := by
    intro hzero
    have hscalar : ((p - q : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.sub_ne_zero_of_lt hpq')
    rw [hzero, Derivation.zero_apply] at hweight
    exact (smul_ne_zero hscalar hne) hweight.symm
  let t := shift_triple (Ne.symm huv) hH
  let E := (shift (n := n) v u).toLinearMap
  let D := (shift (n := n) u v).toLinearMap
  let H := (shift (n := n) u u - shift (n := n) v v).toLinearMap
  have hDE (g : Poly m n) : D (E g) = E (D g) - H g := by
    have hh := DFunLike.congr_fun t.lie_e_f g
    change E (D g) - D (E g) = H g at hh
    apply eq_sub_iff_add_eq.mpr
    rw [← hh]
    abel
  have hHD (g : Poly m n) : H (D g) = D (H g) - (2 : ℂ) • D g := by
    have hh := DFunLike.congr_fun t.lie_h_f_nsmul g
    simp only [Derivation.commutator_apply, Derivation.neg_apply, two_nsmul,
      Derivation.add_apply] at hh
    change H (D g) - D (H g) = -(D g + D g) at hh
    rw [sub_eq_iff_eq_add] at hh
    rw [hh]
    module
  have hnil : ∃ k : ℕ, (E ^ k) f = 0 :=
    ⟨q + 1, shift_nilpotent (Ne.symm huv) hq⟩
  obtain ⟨k, hk₁, hk₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hne hnil
  have hweights (j : ℕ) : H ((E ^ j) f) =
      (((p - q : ℕ) : ℂ) + 2 * j) • ((E ^ j) f) :=
    t.lie_h_pow_toEnd_e hweight j
  have hkernel (j : ℕ) : (D ^ (L + j)) ((E ^ j) f) = 0 := by
    induction j with
    | zero => simpa using hDf
    | succ j ih =>
      have h := nilpotence_raise D E H hDE hHD (hweights j) ih
      simpa only [pow_succ', Module.End.mul_apply, ← Nat.add_assoc] using h
  have hprimitive : t.HasPrimitiveVectorWith ((E ^ k) f)
      (((p - q + 2 * k : ℕ)) : ℂ) := by
    refine ⟨hk₁, ?_, ?_⟩
    · change H ((E ^ k) f) = (((p - q + 2 * k : ℕ)) : ℂ) • ((E ^ k) f)
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hweights k
    · change E ((E ^ k) f) = 0
      simpa only [pow_succ', Module.End.mul_apply] using hk₂
  have hbound : L + k ≤ p - q + 2 * k := by omega
  exact (hprimitive.pow_toEnd_f_ne_zero_of_eq_nat rfl hbound) (hkernel k)

theorem shift_raises {m n : ℕ} {u v : Fin m} (huv : u ≠ v)
    {f : Poly m n} {q : ℕ}
    (hf : f.IsWeightedHomogeneous (rowWeight v) q) :
    (shift u v f).IsWeightedHomogeneous (rowWeight v) (q + 1) := by
  rw [shift_eq_sum, derivation_sum_apply]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro k _
  simp only [Derivation.smul_apply, smul_eq_mul]
  have hd : (pderiv (u, k) f).IsWeightedHomogeneous (rowWeight v) q :=
    hf.pderiv (by simp [rowWeight, huv])
  have hx : (X (v, k) : Poly m n).IsWeightedHomogeneous (rowWeight v) 1 := by
    simpa [rowWeight] using
      (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (rowWeight v) (v, k))
  simpa [add_comm] using hx.mul hd

theorem shift_spectator {m n : ℕ} {u v w : Fin m}
    (huw : u ≠ w) (hvw : v ≠ w) {f : Poly m n} {q : ℕ}
    (hf : f.IsWeightedHomogeneous (rowWeight w) q) :
    (shift u v f).IsWeightedHomogeneous (rowWeight w) q := by
  rw [shift_eq_sum, derivation_sum_apply]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro k _
  simp only [Derivation.smul_apply, smul_eq_mul]
  have hd : (pderiv (u, k) f).IsWeightedHomogeneous (rowWeight w) q :=
    hf.pderiv (by simp [rowWeight, huw])
  have hx : (X (v, k) : Poly m n).IsWeightedHomogeneous (rowWeight w) 0 := by
    simpa [rowWeight, hvw] using
      (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (rowWeight w) (v, k))
  simpa using hx.mul hd

theorem shift_pow_raises {m n : ℕ} {u v : Fin m} (huv : u ≠ v)
    {f : Poly m n} {q : ℕ}
    (hf : f.IsWeightedHomogeneous (rowWeight v) q) (L : ℕ) :
    (((shift u v).toLinearMap ^ L) f).IsWeightedHomogeneous (rowWeight v) (q + L) := by
  induction L with
  | zero => simpa using hf
  | succ L ih =>
    rw [pow_succ', Module.End.mul_apply]
    simpa [Nat.add_assoc] using shift_raises huv ih

theorem shift_pow_spectator {m n : ℕ} {u v w : Fin m}
    (huw : u ≠ w) (hvw : v ≠ w) {f : Poly m n} {q : ℕ}
    (hf : f.IsWeightedHomogeneous (rowWeight w) q) (L : ℕ) :
    (((shift u v).toLinearMap ^ L) f).IsWeightedHomogeneous (rowWeight w) q := by
  induction L with
  | zero => simpa using hf
  | succ L ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact shift_spectator huw hvw ih

def shiftSequence {m n : ℕ} (v : Fin m) (L : ℕ) (us : List (Fin m)) :
    Poly m n →ₗ[ℂ] Poly m n :=
  match us with
  | [] => LinearMap.id
  | u :: us => (shiftSequence v L us).comp ((shift u v).toLinearMap ^ L)

theorem shiftSequence_kernel_zero {m n : ℕ} {us : List (Fin m)} {v : Fin m}
    (hnd : us.Nodup) (hv : v ∉ us) {L j q : ℕ} {f : Poly m n}
    (hp : ∀ u ∈ us, f.IsWeightedHomogeneous (rowWeight u) j)
    (hq : f.IsWeightedHomogeneous (rowWeight v) q)
    (hbound : q + L * us.length ≤ j)
    (hz : shiftSequence v L us f = 0) : f = 0 := by
  induction us generalizing f q with
  | nil => simpa [shiftSequence] using hz
  | cons u us ih =>
    have huv : u ≠ v := by
      intro h
      exact hv (by simp [h])
    have hnd' := List.nodup_cons.mp hnd
    have hv' : v ∉ us := fun h => hv (List.mem_cons_of_mem u h)
    have hs : ((shift u v).toLinearMap ^ L) f = 0 := by
      apply ih hnd'.2 hv' (q := q + L)
      · intro w hw
        apply shift_pow_spectator (u := u) (v := v) (w := w) (fun h => hnd'.1 (h.symm ▸ hw))
          (fun h => hv' (h.symm ▸ hw)) (hp w (List.mem_cons_of_mem u hw)) L
      · exact shift_pow_raises huv hq L
      · simp only [List.length_cons, Nat.mul_succ] at hbound
        omega
      · exact hz
    apply shift_power_kernel_zero huv (hp u (by simp)) hq _ hs
    simp only [List.length_cons, Nat.mul_succ] at hbound
    omega

end Foulkes.Differential

end

end OAI
