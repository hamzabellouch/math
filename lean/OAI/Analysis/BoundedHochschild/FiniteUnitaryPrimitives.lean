import OAI.Analysis.BoundedHochschild.AbelianPrimitives

namespace OAI

/-!
# Finite unitary averaging for type I pieces

The separability homotopy of a finite group of unitaries has norm at most one.
It is exact in the first variable on the linear span of the group. This is the
finite-dimensional ingredient of the classical type I vanishing argument.
-/

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma differentialValue_leftOutput {n : ℕ} (b : M) (f : Cochain M n)
    (x : Fin (n + 1) → M) :
    differentialValue (centralOutput b f) x =
      b * differentialValue f x +
        (x 0 * b - b * x 0) * f (fun i => x i.succ) := by
  simp only [differentialValue, centralOutput_apply, mul_add,
    Finset.mul_sum, mul_smul_comm, mul_assoc]
  noncomm_ring

lemma first_separability_identity {n : ℕ} (a b : M) (f : Cochain M (n + 1))
    (hf : ∀ x, differentialValue f x = 0) (x : Fin (n + 1) → M) :
    differentialValue (centralOutput a (f.curryLeft b)) x =
      a * b * f x - a * f (Fin.cons (b * x 0) (fun i => x i.succ)) +
        x 0 * a * f (Fin.cons b (fun i => x i.succ)) := by
  rw [differentialValue_leftOutput, first_homotopy_identity f hf]
  simp only [ContinuousMultilinearMap.curryLeft_apply]
  noncomm_ring

variable {G : Type*} [Group G] [Fintype G]

private lemma unitary_norm_le (u : unitary M) : ‖(u : M)‖ ≤ 1 := by
  nontriviality M
  exact (CStarRing.norm_coe_unitary u).le

/-- The finite Haar average of the first-variable contracting homotopies. -/
def finiteUnitaryHomotopy (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 1)) : Cochain M n :=
  (Fintype.card G : ℂ)⁻¹ •
    ∑ u : G, centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))

lemma finiteUnitaryHomotopy_norm (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 1)) : ‖finiteUnitaryHomotopy ρ f‖ ≤ ‖f‖ := by
  have hterm (u : G) :
      ‖centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))‖ ≤ ‖f‖ := by
    apply (norm_centralOutput_le _ (unitary_norm_le _) _).trans
    calc
      ‖f.curryLeft (ρ u⁻¹ : M)‖ ≤ ‖f.curryLeft‖ * ‖(ρ u⁻¹ : M)‖ :=
        f.curryLeft.le_opNorm _
      _ ≤ ‖f‖ := by
        rw [ContinuousMultilinearMap.curryLeft_norm]
        exact (mul_le_mul_of_nonneg_left (unitary_norm_le _) (norm_nonneg _)).trans_eq
          (mul_one _)
  have hc : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  calc
    ‖finiteUnitaryHomotopy ρ f‖ =
        (Fintype.card G : ℝ)⁻¹ *
          ‖∑ u : G, centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))‖ := by
      simp only [finiteUnitaryHomotopy, norm_smul, norm_inv, Complex.norm_natCast]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ((Fintype.card G : ℝ) * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact (norm_sum_le _ _).trans (by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
          Finset.sum_le_sum (s := Finset.univ) (fun u _ => hterm u))
    _ = ‖f‖ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

lemma finiteUnitaryHomotopy_exact_unitary (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0)
    (v : G) (x : Fin n → M) :
    differentialValue (finiteUnitaryHomotopy ρ f) (Fin.cons (ρ v : M) x) =
      f (Fin.cons (ρ v : M) x) := by
  classical
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hu (u : G) : (ρ u : M) * (ρ u⁻¹ : M) = 1 := by
    rw [← Submonoid.coe_mul, ← map_mul, mul_inv_cancel, map_one, Submonoid.coe_one]
  have hsum :
      (∑ u : G, (ρ u : M) * f (Fin.cons ((ρ u⁻¹ : M) * (ρ v : M)) x)) =
      ∑ u : G, (ρ v : M) * (ρ u : M) * f (Fin.cons (ρ u⁻¹ : M) x) := by
    apply Fintype.sum_equiv (Equiv.mulLeft v⁻¹) _ _
    intro u
    change (ρ u : M) * f (Fin.cons ((ρ u⁻¹ : M) * (ρ v : M)) x) =
      (ρ v : M) * (ρ (v⁻¹ * u) : M) * f (Fin.cons (ρ (v⁻¹ * u)⁻¹ : M) x)
    have hcancel : (ρ v : M) * (ρ (v⁻¹ * u) : M) = (ρ u : M) := by
      change ((ρ v * ρ (v⁻¹ * u) : unitary M) : M) = _
      rw [← map_mul, mul_inv_cancel_left]
    rw [hcancel, mul_inv_rev, inv_inv, map_mul, Submonoid.coe_mul]
  rw [finiteUnitaryHomotopy, differentialValue_smul]
  have hd : differentialValue
      (∑ u : G, centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M)))
      (Fin.cons (ρ v : M) x) =
      ∑ u : G, differentialValue
        (centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))) (Fin.cons (ρ v : M) x) := by
    have hh := map_sum (differentialLinearMap M n)
      (fun u : G => centralOutput (ρ u : M) (f.curryLeft (ρ u⁻¹ : M))) Finset.univ
    have he := congrArg (fun g : Cochain M (n + 1) => g (Fin.cons (ρ v : M) x)) hh
    change (differential _) _ = (∑ u : G, differential _) _ at he
    simpa only [sum_apply, differential_apply] using he
  rw [hd]
  simp only [first_separability_identity _ _ f hf, hu, one_mul, Fin.cons_zero,
    Fin.cons_succ, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, sub_add_cancel,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma finiteUnitaryHomotopy_exact_span (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0)
    {a : M} (ha : a ∈ Submodule.span ℂ (Set.range (fun u : G => (ρ u : M))))
    (x : Fin n → M) :
    differentialValue (finiteUnitaryHomotopy ρ f) (Fin.cons a x) = f (Fin.cons a x) := by
  let L := firstSliceN (differential (finiteUnitaryHomotopy ρ f) - f) x
  have hker : Submodule.span ℂ (Set.range (fun u : G => (ρ u : M))) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    change L (ρ u : M) = 0
    simpa only [L, firstSliceN_apply, sub_apply, differential_apply] using
      sub_eq_zero.mpr (finiteUnitaryHomotopy_exact_unitary ρ f hf u x)
  have h := hker ha
  change L a = 0 at h
  exact sub_eq_zero.mp (by
    simpa only [L, firstSliceN_apply, sub_apply, differential_apply] using h)

section Predual

open Filter Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [CompleteSpace X]

/-- Norm-one primitives for the locally finite unitary families used in the
finite homogeneous type I argument. The hypotheses are concrete group and
norm-density data, independent of cochains. -/
theorem primitive_of_locally_finite_unitaries (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set (unitary M))
    (hfinite : ∀ s : Finset S, ∃ H : Subgroup (unitary M),
      Finite H ∧ ∀ u ∈ s, (u : unitary M) ∈ H)
    (hdense : (Submodule.span ℂ (Set.range (fun u : S => ((u : unitary M) : M)))).topologicalClosure = ⊤)
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  classical
  choose H hH hmem using hfinite
  let F (s : Finset S) : Cochain M n := by
    letI := hH s
    letI := Fintype.ofFinite (H s)
    exact finiteUnitaryHomotopy (H s).subtype f
  have hFn (s : Finset S) : ‖F s‖ ≤ ‖f‖ := by
    let := hH s
    let := Fintype.ofFinite (H s)
    exact finiteUnitaryHomotopy_norm (H s).subtype f
  let U : Ultrafilter (Finset S) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset S)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨g, hgn, ht⟩ := bounded_cochain_ultralimit e U F ‖f‖ (norm_nonneg _) hFn
  have hunit (u : S) (x : Fin n → M) :
      differentialValue g (Fin.cons ((u : unitary M) : M) x) =
        f (Fin.cons ((u : unitary M) : M) x) := by
    have he : (fun s => differentialValue (F s) (Fin.cons ((u : unitary M) : M) x)) =ᶠ[U]
        (fun _ => f (Fin.cons ((u : unitary M) : M) x)) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({u} : Finset S)] with s hs
      let := hH s
      let := Fintype.ofFinite (H s)
      exact finiteUnitaryHomotopy_exact_unitary (H s).subtype f hf
        ⟨u, hmem s u (hs (Finset.mem_singleton_self u))⟩ x
    apply predual_tendsto_unique e (predual_tendsto_differential_of_predual e ht _)
    intro z
    exact tendsto_const_nhds.congr' (he.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  refine ⟨g, hgn, fun x => ?_⟩
  let L := firstSliceN (differential g - f) (Fin.tail x)
  have hspan : Submodule.span ℂ (Set.range (fun u : S => ((u : unitary M) : M))) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    change L ((u : unitary M) : M) = 0
    simpa only [L, firstSliceN_apply, sub_apply, differential_apply] using
      sub_eq_zero.mpr (hunit u (Fin.tail x))
  have hclosed := Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  rw [hdense] at hclosed
  have hh := hclosed (Submodule.mem_top : x 0 ∈ (⊤ : Submodule ℂ M))
  change L (x 0) = 0 at hh
  apply sub_eq_zero.mp
  simpa only [L, firstSliceN_apply, sub_apply, differential_apply, Fin.cons_self_tail] using hh

end Predual

end KadisonRingrose
end BoundedHochschild

end

end OAI
