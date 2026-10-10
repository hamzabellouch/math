import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCorrelation

namespace OAI

/-! # Identifying the original density transform with its local prime factors -/

namespace Ostmann

open scoped BigOperators

private theorem intCast_isUnit_of_dvd {d q : ℕ} (hd : d ∣ q) (j : ℤ)
    (hj : IsUnit (j : ZMod q)) : IsUnit (j : ZMod d) := by
  simpa only [map_intCast] using hj.map (ZMod.castHom hd (ZMod d))

/-- The multipliers produced by CRT are genuine units; they may be absorbed
in the local arguments without imposing a new hypothesis on the density. -/
theorem densityFourier_primeCRTFunction (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (f : ∀ p : ℕ, ZMod p → ℂ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∃ a : ∀ p : ℕ, (ZMod p)ˣ, ∀ n : ℤ,
      densityFourier (primeCRTFunction ps hp hc f) (n : ZMod ps.prod) =
        (ps.map fun p => primeDensityFourier f p ((a p : ZMod p) * (n : ZMod p))).prod := by
  classical
  induction ps with
  | nil =>
    refine ⟨fun _ => 1, ?_⟩
    intro n
    change densityFourier (fun _ : ZMod 1 => (1 : ℂ)) (n : ZMod 1) = 1
    simp only [densityFourier, additiveFourier_apply, Nat.cast_one, Real.sqrt_one,
      Complex.ofReal_one, inv_one, one_mul, Finset.univ_unique, Finset.sum_singleton]
    exact (congrArg ZMod.stdAddChar (Subsingleton.elim _ (0 : ZMod 1))).trans
      (AddChar.map_zero_eq_one _)
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : NeZero p := ⟨(hp p List.mem_cons_self).ne_zero⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    obtain ⟨b, hb⟩ := ih hp' hcp.2
    have hv : IsUnit (ps.prod : ZMod p) :=
      (ZMod.isUnit_iff_coprime ps.prod p).mpr
        (Nat.coprime_list_prod_right_iff.mpr hcp.1).symm
    let v : (ZMod p)ˣ := hv.unit⁻¹
    have hvval : (v : ZMod p) = (ps.prod : ZMod p)⁻¹ := by
      change (hv.unit⁻¹ : (ZMod p)ˣ).val = _
      rw [← ZMod.inv_coe_unit, IsUnit.unit_spec]
    have hu : IsUnit (p : ZMod ps.prod) :=
      (ZMod.isUnit_iff_coprime p ps.prod).mpr (Nat.coprime_list_prod_right_iff.mpr hcp.1)
    let u : (ZMod ps.prod)ˣ := hu.unit⁻¹
    have huval : (u : ZMod ps.prod) = (p : ZMod ps.prod)⁻¹ := by
      change (hu.unit⁻¹ : (ZMod ps.prod)ˣ).val = _
      rw [← ZMod.inv_coe_unit, IsUnit.unit_spec]
    obtain ⟨j, hj⟩ := ZMod.intCast_surjective (u : ZMod ps.prod)
    have hjunit : IsUnit (j : ZMod ps.prod) := hj ▸ u.isUnit
    let c : ∀ q : ℕ, (ZMod q)ˣ := fun q =>
      if hq : q ∈ ps then (intCast_isUnit_of_dvd (List.dvd_prod hq) j hjunit).unit else 1
    have hcval (q : ℕ) (hq : q ∈ ps) : (c q : ZMod q) = (j : ZMod q) := by
      simp only [c, dite_eq_left hq, IsUnit.unit_spec]
    have hne (q : ℕ) (hq : q ∈ ps) : q ≠ p := by
      intro he
      subst q
      have hh := hcp.1 p hq
      have hh1 : p = 1 := by simpa [Nat.Coprime] using hh
      exact (hp p List.mem_cons_self).ne_one hh1
    let a : ∀ q : ℕ, (ZMod q)ˣ := Function.update (fun q => b q * c q) p v
    refine ⟨a, ?_⟩
    intro n
    change densityFourier (fun x : ZMod (p * ps.prod) =>
      f p ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).1 *
      primeCRTFunction ps hp' hcp.2 f
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) x).2)
      (n : ZMod (p * ps.prod)) = _
    rw [densityFourier_crt (m := p) (n := ps.prod), map_intCast]
    change densityFourier (f p) ((ps.prod : ZMod p)⁻¹ * (n : ZMod p)) *
      densityFourier (primeCRTFunction ps hp' hcp.2 f)
        ((p : ZMod ps.prod)⁻¹ * (n : ZMod ps.prod)) = _
    rw [← huval, ← hj, ← Int.cast_mul, hb (j * n)]
    simp only [List.map_cons, List.prod_cons]
    congr 1
    · rw [primeDensityFourier_eq]
      simp only [a, Function.update_self, hvval]
    · apply congrArg List.prod
      apply List.map_congr_left
      intro q hq
      have haq : a q = b q * c q := Function.update_of_ne (hne q hq) _ _
      rw [haq, Units.val_mul, hcval q hq, Int.cast_mul, mul_assoc]

/-- The recursively formed CRT density is exactly the product of the
centered functions in the manuscript. -/
theorem densityCRTList_value_eq_primeCRTFunction (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (S : ∀ p : ℕ, Finset (ZMod p)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (densityCRTList ps hp hc S).value =
      primeCRTFunction ps hp hc (fun p x => (centeredDensity (S p) x : ℂ)) := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  funext x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [densityCRTList_intCast, primeCRTFunction_intCast]

end Ostmann

end OAI
