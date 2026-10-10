import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.AmpleAbsorption

namespace OAI

/-! Ample Generation. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma divisorSupport_add_of_nonneg {X : Scheme} {D E : WeilDivisor X}
    (hD : 0 ≤ D) (hE : 0 ≤ E) :
    divisorSupport (D+E) = divisorSupport D ∪ divisorSupport E := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨p,hp,hpx⟩ := Set.mem_iUnion₂.mp hx
    have hp' : D p ≠ 0 ∨ E p ≠ 0 := by
      by_contra h
      push Not at h
      exact (Finsupp.mem_support_iff.mp hp) (by simp [h.1,h.2])
    rcases hp' with hp' | hp'
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨p,Finsupp.mem_support_iff.mpr hp',hpx⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨p,Finsupp.mem_support_iff.mpr hp',hpx⟩)
  · exact Set.union_subset
      (divisorSupport_mono_nonnegative hD (le_add_of_nonneg_right hE))
      (divisorSupport_mono_nonnegative hE (le_add_of_nonneg_left hD))

section Generation
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

lemma sectionNonvanishing_mul {D E : WeilDivisor X} {s t : X.functionField}
    (hs : s ≠ 0) (ht : t ≠ 0)
    (hsD : IsDivisorSection D s) (htE : IsDivisorSection E t) :
    sectionNonvanishing (D+E) (s*t) =
      sectionNonvanishing D s ⊓ sectionNonvanishing E t := by
  have he : principalWeilDivisor (s*t)+(D+E) =
      (principalWeilDivisor s+D)+(principalWeilDivisor t+E) := by
    rw [principalWeilDivisor_mul hs ht]
    abel
  simp only [sectionNonvanishing,he,divisorComplement,
    divisorSupport_add_of_nonneg ((divisorSection_iff_effective hs).mp hsD)
      ((divisorSection_iff_effective ht).mp htE)]
  ext x
  exact not_or

lemma IsGeneratedAt.add {D E : WeilDivisor X} {x : X}
    (hD : IsGeneratedAt D x) (hE : IsGeneratedAt E x) : IsGeneratedAt (D+E) x := by
  obtain ⟨s,hs,hsD,hxs⟩ := hD
  obtain ⟨t,ht,htE,hxt⟩ := hE
  refine ⟨s*t,mul_ne_zero hs ht,?_,?_⟩
  · rw [divisorSection_iff_effective (mul_ne_zero hs ht),principalWeilDivisor_mul hs ht]
    intro p
    have h1 := (divisorSection_iff_effective hs).mp hsD p
    have h2 := (divisorSection_iff_effective ht).mp htE p
    simp only [Finsupp.add_apply] at *
    linarith
  · rw [sectionNonvanishing_mul hs ht hsD htE]
    exact ⟨hxs,hxt⟩

lemma isGeneratedAt_zero (x : X) : IsGeneratedAt (0 : WeilDivisor X) x := by
  refine ⟨1,one_ne_zero,?_,?_⟩
  · rw [divisorSection_iff_effective one_ne_zero]
    simp only [principalWeilDivisor_one,add_zero]
    intro p
    exact le_refl _
  · simp [sectionNonvanishing,principalWeilDivisor_one,divisorComplement,divisorSupport]

lemma IsGeneratedAt.nsmul {D : WeilDivisor X} {x : X}
    (hD : IsGeneratedAt D x) (n : ℕ) : IsGeneratedAt (n • D) x := by
  induction n with
  | zero => simpa using isGeneratedAt_zero x
  | succ n hn => simpa only [succ_nsmul] using hn.add hD

lemma isOpen_isGeneratedAt (D : WeilDivisor X) : IsOpen {x : X | IsGeneratedAt D x} := by
  have he : {x : X | IsGeneratedAt D x} =
      ⋃ s : {s : X.functionField // s ≠ 0 ∧ IsDivisorSection D s},
        (sectionNonvanishing D s.1 : Set X) := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,IsGeneratedAt]
    exact ⟨fun ⟨s,hs,hsD,hx⟩ => ⟨⟨s,hs,hsD⟩,hx⟩,
      fun ⟨s,hx⟩ => ⟨s.1,s.2.1,s.2.2,hx⟩⟩
  rw [he]
  exact isOpen_iUnion (fun s => (sectionNonvanishing D s.1).isOpen)

lemma ample_has_generated_power {H : WeilDivisor X} (hH : IsAmpleDivisor H) :
    ∃ r : ℕ, 0 < r ∧ ∀ x : X, IsGeneratedAt (r • H) x := by
  classical
  choose m hm s hs hsec ha hx hsub using (fun x : X => hH.2 x ⊤ (by trivial))
  obtain ⟨V,hV⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (sectionNonvanishing (m x • H) (s x) : Set X))
    (fun x => (sectionNonvanishing (m x • H) (s x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x,hx x⟩)
  let r := ∏ x ∈ V, m x
  have hr : 0 < r := Finset.prod_pos (fun x _ => hm x)
  refine ⟨r,hr,?_⟩
  intro x
  obtain ⟨y,hyV,hyx⟩ := Set.mem_iUnion₂.mp (hV (Set.mem_univ x))
  have hdiv : m y ∣ r := Finset.dvd_prod_of_mem m hyV
  have hgen : IsGeneratedAt (m y • H) x := ⟨s y,hs y,hsec y,hyx⟩
  have he : (r / m y) • (m y • H) = r • H := by
    rw [smul_smul,Nat.div_mul_cancel hdiv]
  exact he ▸ hgen.nsmul (r / m y)

lemma ample_add_generated {H D : WeilDivisor X} (hH : IsAmpleDivisor H)
    (hD : IsCartierDivisor D) (hgen : ∀ x : X, IsGeneratedAt D x) :
    IsAmpleDivisor (H+D) := by
  refine ⟨isCartierDivisor_add hH.1 hD,?_⟩
  intro x U hx
  obtain ⟨t,ht,htD,hxt⟩ := hgen x
  obtain ⟨m,hm,s,hs,hsH,ha,hxs,hsub⟩ :=
    hH.2 x (U ⊓ sectionNonvanishing D t) ⟨hx,hxt⟩
  have htD' : IsDivisorSection (m • D) (t^m) := by
    rw [divisorSection_iff_effective (pow_ne_zero _ ht),principalWeilDivisor_pow ht,
      ← nsmul_add]
    intro p
    simpa only [Finsupp.smul_apply,nsmul_eq_mul] using
      mul_nonneg (Int.natCast_nonneg m) ((divisorSection_iff_effective ht).mp htD p)
  have he : sectionNonvanishing (m • (H+D)) (s*t^m) =
      sectionNonvanishing (m • H) s := by
    rw [nsmul_add,sectionNonvanishing_mul hs (pow_ne_zero _ ht) hsH htD',
      sectionNonvanishing_pow _ ht hm]
    exact inf_eq_left.mpr (le_trans hsub inf_le_right)
  refine ⟨m,hm,s*t^m,mul_ne_zero hs (pow_ne_zero _ ht),?_,he ▸ ha,
    he ▸ hxs,he ▸ le_trans hsub inf_le_left⟩
  rw [divisorSection_iff_effective (mul_ne_zero hs (pow_ne_zero _ ht)),
    principalWeilDivisor_mul hs (pow_ne_zero _ ht),nsmul_add]
  intro p
  have h1 := (divisorSection_iff_effective hs).mp hsH p
  have h2 := (divisorSection_iff_effective (pow_ne_zero _ ht)).mp htD' p
  simp only [Finsupp.add_apply] at *
  linarith

omit [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] in
lemma open_le_divisorComplement_of_coeff_zero {D : WeilDivisor X}
    (U : X.Opens) (hD : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = 0) :
    U ≤ divisorComplement D := by
  intro x hx hbad
  obtain ⟨p,hp,hpx⟩ := Set.mem_iUnion₂.mp hbad
  have hsp : p.1 ⤳ x := specializes_iff_mem_closure.mpr hpx
  exact (Finsupp.mem_support_iff.mp hp) (hD p (hsp.mem_open U.isOpen hx))

omit [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] in
lemma exists_effective_multiple_absorbing {B E : WeilDivisor X}
    (hE : 0 ≤ E) (hBE : ∀ p, E p = 0 → B p = 0) :
    ∃ N : ℕ, 0 < N ∧ 0 ≤ B + N • E := by
  classical
  let N := B.support.sup (fun p => (B p).natAbs) + 1
  have hN : 0 < N := Nat.succ_pos _
  refine ⟨N,hN,?_⟩
  intro p
  change 0 ≤ B p + (N : ℤ) * E p
  by_cases hEp : E p = 0
  · simp only [hEp,hBE p hEp,mul_zero,add_zero,le_refl]
  have hEpos : 1 ≤ E p := by
    have he0 : (0 : ℤ) ≤ E p := hE p
    omega
  have hB : -(N : ℤ) ≤ B p := by
    by_cases hBp : B p = 0
    · simpa only [hBp,neg_nonpos] using Int.natCast_nonneg N
    have habs : (B p).natAbs ≤ B.support.sup (fun p => (B p).natAbs) :=
      Finset.le_sup (f := fun p => (B p).natAbs) (Finsupp.mem_support_iff.mpr hBp)
    have hb : -(B p) ≤ ((B p).natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (show -(B p) ≤ ((-(B p)).natAbs : ℤ) from Int.le_natAbs)
    dsimp [N]
    omega
  have hNE : (N : ℤ) ≤ (N : ℤ) * E p := by
    nlinarith [Int.natCast_nonneg N]
  omega

lemma exists_generated_twist_at {D H : WeilDivisor X}
    (hD : IsCartierDivisor D) (hH : IsAmpleDivisor H) (x : X) :
    ∃ n : ℕ, IsGeneratedAt (D+n • H) x := by
  obtain ⟨U,_hU,hxU,g,hg,hDg⟩ := hD x
  obtain ⟨m,hm,s,hs,hsH,_ha,hxs,hsub⟩ := hH.2 x U hxU
  let B := principalWeilDivisor (g⁻¹)+D
  let E := principalWeilDivisor s+m • H
  have hB : ∀ p : PrimeDivisor X, p.1 ∈ U → B p = 0 := by
    intro p hp
    dsimp [B]
    rw [order_inv _ hg, hDg p hp,neg_add_cancel]
  have hE : 0 ≤ E := (divisorSection_iff_effective hs).mp hsH
  have hBE : ∀ p, E p = 0 → B p = 0 := by
    intro p hp
    apply hB p
    apply hsub
    change p.1 ∉ divisorSupport E
    exact fun h => ((prime_mem_divisorSupport_iff E p).mp h) hp
  obtain ⟨N,_hN,hpos⟩ := exists_effective_multiple_absorbing hE hBE
  let t := g⁻¹ * s^N
  have ht : t ≠ 0 := mul_ne_zero (inv_ne_zero hg) (pow_ne_zero _ hs)
  have he : principalWeilDivisor t + (D+(N*m) • H) = B+N • E := by
    dsimp [t,B,E]
    rw [principalWeilDivisor_mul (inv_ne_zero hg) (pow_ne_zero _ hs),
      principalWeilDivisor_pow hs]
    simp only [nsmul_add,smul_smul]
    abel
  refine ⟨N*m,t,ht,?_,?_⟩
  · rw [divisorSection_iff_effective ht,he]
    exact hpos
  · change x ∈ divisorComplement _
    rw [he]
    apply open_le_divisorComplement_of_coeff_zero (sectionNonvanishing (m • H) s) ?_ hxs
    intro p hp
    have hBp := hB p (hsub hp)
    have hEp : E p = 0 := coefficient_zero_on_divisorComplement E p hp
    simp only [Finsupp.add_apply,Finsupp.smul_apply,hBp,hEp,smul_zero,add_zero]

lemma eventually_generated_twist_of_generated {D H : WeilDivisor X}
    (hD : IsCartierDivisor D) (hH : IsAmpleDivisor H)
    (hgen : ∀ x : X, IsGeneratedAt H x) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x : X, IsGeneratedAt (D+n • H) x := by
  classical
  choose k hk using exists_generated_twist_at hD hH
  obtain ⟨V,hV⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => {y : X | IsGeneratedAt (D+k x • H) y})
    (fun x => isOpen_isGeneratedAt _) (fun x _ => Set.mem_iUnion.mpr ⟨x,hk x⟩)
  let N := V.sup k
  refine ⟨N,?_⟩
  intro n hn x
  obtain ⟨y,hyV,hxy⟩ := Set.mem_iUnion₂.mp (hV (Set.mem_univ x))
  have hkn : k y ≤ n := (Finset.le_sup hyV).trans hn
  have hg := hxy.add ((hgen x).nsmul (n-k y))
  have he : (D+k y • H)+(n-k y) • H = D+n • H := by
    rw [add_assoc,← add_nsmul,Nat.add_sub_of_le hkn]
  exact he ▸ hg

lemma eventually_generated_cartier_twist {D H : WeilDivisor X}
    (hD : IsCartierDivisor D) (hH : IsAmpleDivisor H) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x : X, IsGeneratedAt (D+n • H) x := by
  classical
  obtain ⟨r,hr,hgen⟩ := ample_has_generated_power hH
  have hH' : IsAmpleDivisor (r • H) := isAmpleDivisor_nsmul hH hr
  have hDj (j : Fin r) : IsCartierDivisor (D + j.1 • H) :=
    isCartierDivisor_add hD ((cartierDivisors (X := X)).nsmul_mem hH.1 _)
  choose N hN using (fun j : Fin r =>
    eventually_generated_twist_of_generated (hDj j) hH' hgen)
  let T := Finset.univ.sup N
  refine ⟨T*r,?_⟩
  intro n hn x
  let j : Fin r := ⟨n % r,Nat.mod_lt _ hr⟩
  have hT : T ≤ n/r := (Nat.le_div_iff_mul_le hr).mpr hn
  have hj : N j ≤ n/r := (Finset.le_sup (Finset.mem_univ j)).trans hT
  have hg := hN j (n/r) hj x
  have he : (D+j.1 • H)+(n/r) • (r • H) = D+n • H := by
    rw [smul_smul,add_assoc,← add_nsmul]
    dsimp [j]
    rw [Nat.mul_comm (n/r) r,Nat.mod_add_div]
  exact he ▸ hg

theorem ample_eventual_cartier_twist
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [StalkwiseNormal X] [CompactSpace X]
    (D H : WeilDivisor X) (hD : IsCartierDivisor D) (hH : IsAmpleDivisor H) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (∀ x : X, IsGeneratedAt (D + n • H) x) ∧ IsAmpleDivisor (D + n • H) := by
  obtain ⟨N,hN⟩ := eventually_generated_cartier_twist hD hH
  refine ⟨N+1,?_⟩
  intro n hn
  refine ⟨hN n (by omega),?_⟩
  have hcart : IsCartierDivisor (D+(n-1) • H) :=
    isCartierDivisor_add hD ((cartierDivisors (X := X)).nsmul_mem hH.1 _)
  have hample := ample_add_generated hH hcart (hN (n-1) (by omega))
  have he : H+(D+(n-1) • H) = D+n • H := by
    calc
      H+(D+(n-1) • H) = D+(1+(n-1)) • H := by
        rw [add_nsmul,one_nsmul]
        abel
      _ = D+n • H := by rw [show 1+(n-1) = n by omega]
  exact he ▸ hample

end Generation
end NumericalDimensionOne

end OAI
