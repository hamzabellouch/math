import OAI.NumberTheory.PowerFree.NormBoxes

namespace OAI

noncomputable section
open scoped Classical

namespace QuarticPowerFree

section
open Module

theorem lattice_covering_radius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] : ∃ R : ℝ, 0 < R ∧ ∀ x : E, ∃ z : L, ‖x - z‖ ≤ R := by
  classical
  have := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  let B := b.ofZLatticeBasis ℝ
  obtain ⟨R, hR⟩ := B.parallelepiped.isCompact.isBounded.exists_norm_le
  refine ⟨max R 0 + 1, by positivity, fun x => ?_⟩
  let z : L := b.repr.symm (Finsupp.equivFunOnFinite.symm fun i => ⌊B.repr x i⌋)
  refine ⟨z, le_trans (hR _ ?_) (by linarith [le_max_left R 0])⟩
  simp [parallelepiped_basis_eq, z, B]
  exact fun i => (Int.fract_lt_one _).le

open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem

theorem logarithmic_units_cover (K : Type*) [Field K] [NumberField K] :
    ∃ R : ℝ, 0 < R ∧ ∀ x : logSpace K, ∃ u : (𝓞 K)ˣ,
      ‖x - logEmbedding K (Additive.ofMul u)‖ ≤ R := by
  obtain ⟨R, hR, h⟩ := lattice_covering_radius (unitLattice K)
  refine ⟨R, hR, fun x => ?_⟩
  obtain ⟨z, hz⟩ := h x
  obtain ⟨u, _, hu⟩ := z.2
  exact ⟨u.toMul, hu ▸ hz⟩

theorem unit_balancing_hyperplane (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ s : InfinitePlace K → ℝ,
      (∑ w, (mult w : ℝ) * s w) = 0 → ∃ u : (𝓞 K)ˣ,
      ∀ w, |Real.log (w (u : K)) + s w| ≤ C := by
  classical
  obtain ⟨R, hR, hcover⟩ := logarithmic_units_cover K
  refine ⟨(Fintype.card (InfinitePlace K) : ℝ) * R,
    mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hR, fun s hs => ?_⟩
  obtain ⟨u, hu⟩ := hcover (fun w => -(mult w.val : ℝ) * s w.val)
  have hsmall (w : {w : InfinitePlace K // w ≠ w₀}) :
      |(mult w.val : ℝ) * (Real.log (w.val (u : K)) + s w.val)| ≤ R := by
    have hh := (norm_le_pi_norm (fun w => -(mult w.val : ℝ) * s w.val -
      logEmbedding K (Additive.ofMul u) w) w).trans hu
    have he : (-(mult w.val : ℝ) * s w.val -
      logEmbedding K (Additive.ofMul u) w) =
      -((mult w.val : ℝ) * (Real.log (w.val (u : K)) + s w.val)) := by
      rw [logEmbedding_component]
      ring
    rw [he, norm_neg, Real.norm_eq_abs] at hh
    exact hh

  have hmult (w : InfinitePlace K) : (1 : ℝ) ≤ mult w := by
    rw [mult]; split_ifs <;> norm_num
  have habs (w : InfinitePlace K) : |Real.log (w (u : K)) + s w| ≤
      |(mult w : ℝ) * (Real.log (w (u : K)) + s w)| := by
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (hmult w)
  refine ⟨u, fun w => ?_⟩
  by_cases hw : w = w₀
  · have hsum : (mult w : ℝ) * (Real.log (w (u : K)) + s w) =
        -∑ v : {v : InfinitePlace K // v ≠ w₀},
          (mult v.val : ℝ) * (Real.log (v.val (u : K)) + s v.val) := by
      have ht : (∑ v : InfinitePlace K,
          (mult v : ℝ) * (Real.log (v (u : K)) + s v)) = 0 := by
        simp only [mul_add, Finset.sum_add_distrib, NumberField.Units.sum_mult_mul_log, hs,
          add_zero]
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at ht
      rw [hw]
      exact eq_neg_of_add_eq_zero_left ht
    refine (habs w).trans ?_
    rw [hsum, abs_neg]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun v _ => hsmall v)).trans
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_subtype_le _)) hR.le
  · exact (habs w).trans ((hsmall ⟨w,hw⟩).trans
      (le_mul_of_one_le_left hR.le (Nat.one_le_cast.mpr Fintype.card_pos)))

theorem unit_balancing_norm (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ x : K, x ≠ 0 → ∃ u : (𝓞 K)ˣ,
      ∀ w : InfinitePlace K,
        C⁻¹ * |(Algebra.norm ℚ x : ℝ)| ^ ((Module.finrank ℚ K : ℝ)⁻¹) ≤ w ((u : K) * x) ∧
        w ((u : K) * x) ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨R, hR, hbalance⟩ := unit_balancing_hyperplane K
  refine ⟨Real.exp R, Real.exp_pos _, fun x hx => ?_⟩
  let d : ℝ := Module.finrank ℚ K
  let a : ℝ := |(Algebra.norm ℚ x : ℝ)|
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (Nat.ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  have ha : 0 < a := by
    dsimp [a]
    apply abs_pos.mpr
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  have hwpos (w : InfinitePlace K) : 0 < w x := InfinitePlace.pos_iff.mpr hx
  have hs : (∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w x)) = Real.log a := by
    have h := congrArg Real.log (prod_eq_abs_norm x)
    rw [Real.log_prod (fun w _ => pow_ne_zero _ (ne_of_gt (hwpos w)))] at h
    simpa [a, Real.log_pow] using h
  have hzero : (∑ w : InfinitePlace K,
      (mult w : ℝ) * (Real.log (w x) - Real.log a / d)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, hs, ← Finset.sum_mul]
    rw [← Nat.cast_sum, sum_mult_eq]
    change Real.log a - d * (Real.log a / d) = 0
    field_simp
    ring
  obtain ⟨u, hu⟩ := hbalance (fun w => Real.log (w x) - Real.log a / d) hzero
  refine ⟨u, fun w => ?_⟩
  have hb := abs_le.mp (hu w)
  have he : Real.exp (Real.log (w (u : K)) + Real.log (w x)) = w ((u : K) * x) := by
    rw [Real.exp_add, Real.exp_log (pos_at_place u w), Real.exp_log (hwpos w), map_mul]
  have hr : a ^ d⁻¹ = Real.exp (Real.log a / d) := by
    rw [Real.rpow_def_of_pos ha]
    congr 1
  change (Real.exp R)⁻¹ * a ^ d⁻¹ ≤ _ ∧ _ ≤ Real.exp R * a ^ d⁻¹
  rw [hr]
  constructor
  · rw [← Real.exp_neg, ← Real.exp_add, ← he]
    apply Real.exp_le_exp.mpr
    linarith [hb.1]
  · rw [← Real.exp_add, ← he]
    apply Real.exp_le_exp.mpr
    linarith [hb.2]

open NumberField
open scoped nonZeroDivisors

theorem finite_ideal_correction (K : Type*) [Field K] [NumberField K] (k : ℕ) :
    ∃ (μ : ℕ) (S : Finset (Ideal (𝓞 K))), 0 < μ ∧
      (∀ J ∈ S, J ≠ ⊥) ∧
      ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ → ∀ x ∈ I ^ k,
        ∃ J ∈ S, ∃ α : 𝓞 K, α ≠ 0 ∧ ∃ β : 𝓞 K,
          Ideal.span {α} = I * J ∧ α ^ k * β = (μ : 𝓞 K) * x := by
  classical
  let c : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰ := fun g =>
    (ClassGroup.mk0_surjective g⁻¹).choose
  have hc (g : ClassGroup (𝓞 K)) : ClassGroup.mk0 (c g) = g⁻¹ :=
    (ClassGroup.mk0_surjective g⁻¹).choose_spec
  let S : Finset (Ideal (𝓞 K)) := Finset.univ.image (fun g => (c g : Ideal (𝓞 K)))
  let M : ℕ := ∏ g : ClassGroup (𝓞 K), Ideal.absNorm (c g : Ideal (𝓞 K))
  have hMpos : 0 < M := Finset.prod_pos (fun g _ =>
    Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors (c g)))
  refine ⟨M ^ k, S, pow_pos hMpos _, ?_, ?_⟩
  · intro J hJ
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hJ
    exact mem_nonZeroDivisors_iff_ne_zero.mp (c g).property
  · intro I hI x hx
    let I' : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
    let g := ClassGroup.mk0 I'
    have he : ClassGroup.mk0 I' = (ClassGroup.mk0 (c g))⁻¹ := by rw [hc, inv_inv]
    obtain ⟨α, hα, hspan⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp he
    have hMmem : (M : 𝓞 K) ∈ (c g : Ideal (𝓞 K)) := by
      have hd : Ideal.absNorm (c g : Ideal (𝓞 K)) ∣ M :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ g)
      obtain ⟨a, ha⟩ := hd
      rw [ha, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    have hprod : ((M ^ k : ℕ) : 𝓞 K) * x ∈ Ideal.span {α ^ k} := by
      rw [← Ideal.span_singleton_pow, ← hspan, mul_pow]
      rw [Nat.cast_pow]
      simpa only [mul_comm] using (Ideal.mul_mem_mul hx (Ideal.pow_mem_pow hMmem k))
    obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton.mp hprod
    refine ⟨c g, Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩, α, hα, β, ?_, hβ.symm⟩
    exact hspan.symm

theorem balanced_ideal_factorization (K : Type*) [Field K] [NumberField K] (k : ℕ) :
    ∃ (μ : ℕ) (S : Finset (Ideal (𝓞 K))) (C : ℝ), 0 < μ ∧ 0 < C ∧
      (∀ J ∈ S, J ≠ ⊥) ∧
      ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ → ∀ x ∈ I ^ k,
        ∃ J ∈ S, ∃ α : 𝓞 K, α ≠ 0 ∧ ∃ β : 𝓞 K,
          Ideal.span {α} = I * J ∧ α ^ k * β = (μ : 𝓞 K) * x ∧
          ∀ w : InfinitePlace K,
            C⁻¹ * ((I.absNorm * J.absNorm : ℕ) : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) ≤ w (α : K) ∧
            w (α : K) ≤ C * ((I.absNorm * J.absNorm : ℕ) : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨μ, S, hμ, hS, hfactor⟩ := finite_ideal_correction K k
  obtain ⟨C, hC, hbalance⟩ := unit_balancing_norm K
  refine ⟨μ, S, C, hμ, hC, hS, fun I hI x hx => ?_⟩
  obtain ⟨J, hJ, α, hα, β, hspan, hβ⟩ := hfactor I hI x hx
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  obtain ⟨u, hu⟩ := hbalance α hαK
  have hn : |(Algebra.norm ℚ (α : K) : ℝ)| = ((I.absNorm * J.absNorm : ℕ) : ℝ) := by
    rw [← Algebra.coe_norm_int, Rat.cast_intCast]
    have h := congrArg Ideal.absNorm hspan
    rw [Ideal.absNorm_span_singleton, map_mul] at h
    rw [← h]
    norm_cast
    rw [Nat.cast_natAbs]
  refine ⟨J, hJ, (u : 𝓞 K) * α, mul_ne_zero (Units.ne_zero u) hα,
    ((↑u⁻¹ : 𝓞 K) ^ k) * β, ?_, ?_, ?_⟩
  · simpa only [Ideal.span_singleton_mul_left_unit u.isUnit] using hspan
  · calc
      ((u : 𝓞 K) * α) ^ k * ((↑u⁻¹ : 𝓞 K) ^ k * β) =
          (((u : 𝓞 K) * ↑u⁻¹) ^ k) * (α ^ k * β) := by ring
      _ = (μ : 𝓞 K) * x := by simp [hβ]
  · intro w
    change C⁻¹ * _ ≤ w ((algebraMap (𝓞 K) K) ((u : 𝓞 K) * α)) ∧
      w ((algebraMap (𝓞 K) K) ((u : 𝓞 K) * α)) ≤ C * _
    simpa only [map_mul, hn] using hu w

end

open Polynomial NumberField

theorem arithmetic_factorization_large_primes {K : Type*} [Field K] [NumberField K]
    (f : Polynomial ℤ) (hf : Irreducible (f.map (Int.castRingHom ℚ)))
    (hd : 1 ≤ f.natDegree) (hc : 0 < f.leadingCoeff)
    (θ : K) (hθ : f.aeval θ = 0) (t : 𝓞 K)
    (ht : (t : K) = (f.leadingCoeff : K) * θ)
    (pb : PowerBasis ℚ K) (hgen : pb.gen = (t : K))
    (k : ℕ) (hk : 0 < k) :
    ∃ (B μ : ℕ) (S : Finset (Ideal (𝓞 K))) (C : ℝ), 0 < μ ∧ 0 < C ∧
      (∀ J ∈ S, J ≠ ⊥) ∧
      ∀ (n : ℤ) (p : ℕ), p.Prime → B < p → (p : ℤ) ^ k ∣ f.eval n →
        ∃ J ∈ S, ∃ α : 𝓞 K, α ≠ 0 ∧ ∃ β : 𝓞 K,
          (α : K) ^ k * (β : K) = (μ : K) * ((n : K) - θ) ∧
          |(Algebra.norm ℚ (α : K) : ℝ)| = ((p * J.absNorm : ℕ) : ℝ) ∧
          ∀ w : InfinitePlace K,
            C⁻¹ * ((p * J.absNorm : ℕ) : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) ≤ w (α : K) ∧
            w (α : K) ≤ C * ((p * J.absNorm : ℕ) : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  let F := f.integralNormalization
  have hmin : minpoly ℤ t = F := minpoly_integral_normalization f hf hd θ hθ t ht
  have hFirr := integralNormalization_irreducible f hf
  have hR := resultant_derivative_ne_zero F hFirr
  have hE := exponent_ne_zero_of_powerBasis t pb hgen
  obtain ⟨q,S,C,hq,hC,hS,hfactor⟩ := balanced_ideal_factorization K k
  refine ⟨max (RingOfIntegers.exponent t) (F.resultant F.derivative).natAbs,
    q * f.leadingCoeff.natAbs, S,C, Nat.mul_pos hq (Int.natAbs_pos.mpr hc.ne'),
    hC,hS,?_⟩
  intro n p hp hBp hfp
  have hpE : ¬ p ∣ RingOfIntegers.exponent t := by
    intro h
    have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero hE) h
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_left _ _) hBp)) hh
  have hpR : ¬ (p : ℤ) ∣ F.resultant F.derivative := by
    intro h
    have hh : p ≤ (F.resultant F.derivative).natAbs := by
      apply Nat.le_of_dvd (Int.natAbs_pos.mpr hR)
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_right _ _) hBp)) hh
  have heval : F.eval (f.leadingCoeff * n) =
      f.leadingCoeff ^ (f.natDegree - 1) * f.eval n := by
    exact integralNormalization_eval₂_leadingCoeff_mul hd (RingHom.id ℤ) n
  have hfpF : (p : ℤ) ^ k ∣ F.eval (f.leadingCoeff * n) := by
    rw [heval]
    exact dvd_mul_of_dvd_right hfp _
  have hdF : F.natDegree ≠ 0 := by
    change f.integralNormalization.natDegree ≠ 0
    rw [natDegree_integralNormalization]
    omega
  have hderiv := derivative_not_dvd_of_good F hdF hpR
    (dvd_trans (dvd_pow_self (p : ℤ) hk.ne') hfpF)
  rw [← hmin] at hderiv hfpF
  obtain ⟨P,_,hP0,hNP,hmem⟩ := root_prime_ideal t (f.leadingCoeff*n) p k hp hk hpE hderiv hfpF
  obtain ⟨J,hJ,α,hα,β,hspan,hfac,hbal⟩ := hfactor P hP0 ((f.leadingCoeff*n : ℤ) - t) hmem
  refine ⟨J,hJ,α,hα,β,?_,?_,?_⟩
  · have hh := congrArg (algebraMap (𝓞 K) K) hfac
    have habs : (f.leadingCoeff.natAbs : K) = (f.leadingCoeff : K) := by
      have hz : (f.leadingCoeff.natAbs : ℤ) = f.leadingCoeff := by
        rw [Int.natCast_natAbs,abs_of_pos hc]
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : K)) hz
    simp only [map_mul,map_pow,map_sub,map_natCast,map_intCast,ht] at hh
    rw [Nat.cast_mul,habs]
    convert hh using 1
    push_cast
    ring
  · rw [← Algebra.coe_norm_int,Rat.cast_intCast]
    have hn := congrArg Ideal.absNorm hspan
    rw [Ideal.absNorm_span_singleton,map_mul,hNP] at hn
    rw [← hn]
    norm_cast
    rw [Nat.cast_natAbs]
  · simpa only [hNP] using hbal

structure ArithmeticModel (f : Polynomial ℤ) where
  Carrier : Type
  [field : Field Carrier]
  [numberField : NumberField Carrier]
  root : Carrier
  root_eq : f.aeval root = 0
  integralRoot : 𝓞 Carrier
  integralRoot_eq : (integralRoot : Carrier) = (f.leadingCoeff : Carrier) * root
  powerBasis : PowerBasis ℚ Carrier
  powerBasis_gen : powerBasis.gen = (integralRoot : Carrier)
  degree_eq : Module.finrank ℚ Carrier = f.natDegree

attribute [instance] ArithmeticModel.field ArithmeticModel.numberField

noncomputable def arithmeticModel (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 1 ≤ f.natDegree) :
    ArithmeticModel f := by
  let F := f.integralNormalization
  let G := F.map (Int.castRingHom ℚ)
  have hG : Irreducible G := integralNormalization_irreducible f hf
  letI : Fact (Irreducible G) := ⟨hG⟩
  let K := AdjoinRoot G
  let pb : PowerBasis ℚ K := AdjoinRoot.powerBasis hG.ne_zero
  letI : Module.Finite ℚ K := pb.finite
  letI : NumberField K := NumberField.of_module_finite ℚ K
  let r : K := AdjoinRoot.root G
  have hr : G.aeval r = 0 := AdjoinRoot.eval₂_root G
  have hrF : F.aeval r = 0 := by
    change (F.map (algebraMap ℤ ℚ)).aeval r = 0 at hr
    rw [aeval_map_algebraMap] at hr
    exact hr
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by simp [h])
  have hFmon : F.Monic := monic_integralNormalization hf0
  let t : 𝓞 K := ⟨r,⟨F,hFmon,hrF⟩⟩
  let θ : K := r / (f.leadingCoeff : K)
  have hc : (f.leadingCoeff : K) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr hf0
  have ht : (f.leadingCoeff : K) * θ = r := by
    dsimp only [θ]
    rw [← mul_div_assoc, mul_comm (f.leadingCoeff : K) r, mul_div_cancel_right₀ r hc]
  have hθ : f.aeval θ = 0 := by
    have he := integralNormalization_eval₂_leadingCoeff_mul hd (algebraMap ℤ K) θ
    change F.aeval ((f.leadingCoeff : K) * θ) =
      (f.leadingCoeff : K) ^ (f.natDegree - 1) * f.aeval θ at he
    rw [ht,hrF] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hc)
  refine ⟨K,θ,hθ,t,ht.symm,pb,?_,?_⟩
  · rfl
  · rw [pb.finrank]
    change G.natDegree = f.natDegree
    rw [natDegree_map_eq_of_injective Int.cast_injective]
    exact natDegree_integralNormalization

theorem uniform_root_difference_bounds {K : Type*} [Field K] [NumberField K]
    (θ : K) : ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ n : ℤ, X < n → (n : ℝ) ≤ 2*X → ∀ w : InfinitePlace K,
        X/2 ≤ w ((n : K)-θ) ∧ w ((n : K)-θ) ≤ 3*X := by
  classical
  let R := ∑ w : InfinitePlace K, w θ
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have hwR (w : InfinitePlace K) : w θ ≤ R := by
    change w θ ≤ ∑ v : InfinitePlace K, v θ
    exact Finset.single_le_sum (fun v _ => apply_nonneg v θ) (Finset.mem_univ w)
  refine ⟨2*R+1,by positivity,fun X hX n hn hn' w => ?_⟩
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity : 0 < 2*R+1) hX
  have hnpos : (0 : ℝ) < n := hXpos.trans hn
  have hwn : w (n : K) = (n : ℝ) := by
    rw [InfinitePlace.map_intCast,Int.norm_eq_abs,abs_of_pos hnpos]
  constructor
  · have hh := w.1.le_sub (n : K) θ
    change w (n : K) - w θ ≤ w ((n : K)-θ) at hh
    rw [hwn] at hh
    linarith [hwR w]
  · have hh := w.1.sub_le_add (n : K) θ
    change w ((n : K)-θ) ≤ w (n : K) + w θ at hh
    rw [hwn] at hh
    linarith [hwR w]

theorem absorb_finite_ideal_norms {K : Type*} [Field K] [NumberField K]
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ J ∈ S, J ≠ ⊥)
    (C : ℝ) (hC : 0 < C) (e : ℝ) (he : 0 ≤ e) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p : ℕ, 0 < p → ∀ J ∈ S, ∀ a : ℝ,
      C⁻¹ * ((p*J.absNorm : ℕ) : ℝ)^e ≤ a →
      a ≤ C * ((p*J.absNorm : ℕ) : ℝ)^e →
      D⁻¹ * (p : ℝ)^e ≤ a ∧ a ≤ D * (p : ℝ)^e := by
  classical
  let M := max 1 (S.sup Ideal.absNorm)
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast le_max_left 1 (S.sup Ideal.absNorm)
  let D := max 1 (C * (M : ℝ)^e)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hCD : C ≤ D := by
    exact (le_mul_of_one_le_right hC.le (Real.one_le_rpow hM he)).trans (le_max_right _ _)
  refine ⟨D,hD1,fun p hp J hJ a hlo hhi => ?_⟩
  have hJpos : 0 < J.absNorm := Nat.pos_of_ne_zero fun hz => hS J hJ
    (Ideal.absNorm_eq_zero_iff.mp hz)
  have hJ1 : (1 : ℝ) ≤ J.absNorm := by exact_mod_cast hJpos
  have hJM : (J.absNorm : ℝ) ≤ M := by
    exact_mod_cast (Finset.le_sup hJ).trans (le_max_right 1 (S.sup Ideal.absNorm))
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [Nat.cast_mul,Real.mul_rpow hp0 (Nat.cast_nonneg _)] at hlo hhi
  constructor
  · calc
      D⁻¹ * (p : ℝ)^e ≤ C⁻¹ * (p : ℝ)^e :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hC hCD) (Real.rpow_nonneg hp0 _)
      _ ≤ C⁻¹ * ((p : ℝ)^e * (J.absNorm : ℝ)^e) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.rpow_nonneg hp0 _)
          (Real.one_le_rpow hJ1 he)) (inv_nonneg.mpr hC.le)
      _ ≤ a := hlo
  · calc
      a ≤ C * ((p : ℝ)^e * (J.absNorm : ℝ)^e) := hhi
      _ ≤ C * ((p : ℝ)^e * (M : ℝ)^e) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hJM he) (Real.rpow_nonneg hp0 _)) hC.le
      _ = (C*(M : ℝ)^e) * (p : ℝ)^e := by ring
      _ ≤ D * (p : ℝ)^e := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hp0 _)

theorem companion_archimedean_bounds {K : Type*} [Field K] [NumberField K] (w : InfinitePlace K)
    (α β θ : K) (n : ℤ) (μ k : ℕ) (hμ : 0 < μ)
    (hf : α^k*β = (μ : K)*((n : K)-θ))
    (P X C e : ℝ) (hP : 0 < P) (hX : 0 ≤ X) (hC : 0 < C)
    (ha : C⁻¹ * P^e ≤ w α) (ha' : w α ≤ C*P^e)
    (hb : X/2 ≤ w ((n : K)-θ)) (hb' : w ((n : K)-θ) ≤ 3*X) :
    (2*C^k)⁻¹ * (X/P^(e*k)) ≤ w (β / (μ : K)) ∧
    w (β / (μ : K)) ≤ (3*C^k) * (X/P^(e*k)) := by
  have hμK : (μ : K) ≠ 0 := by exact_mod_cast hμ.ne'
  have ha0 : 0 < w α := lt_of_lt_of_le (mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos hP e)) ha
  have hrel : w α ^ k * w (β / (μ : K)) = w ((n : K)-θ) := by
    have hh : α^k * (β / (μ : K)) = (n : K)-θ := by
      rw [← mul_div_assoc,hf,mul_div_cancel_left₀ _ hμK]
    simpa only [map_mul,map_pow] using congrArg w hh
  have hwβ : w (β / (μ : K)) = w ((n : K)-θ) / (w α)^k := by
    apply (eq_div_iff (pow_ne_zero _ ha0.ne')).mpr
    simpa only [mul_comm] using hrel
  rw [hwβ]
  have hpow := pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hC.le) (Real.rpow_nonneg hP.le _)) ha k
  have hpow' := pow_le_pow_left₀ ha0.le ha' k
  have heq : P^(e*k) = (P^e)^k := Real.rpow_mul_natCast hP.le e k
  rw [heq]
  constructor
  · have hh : (X/2) / (C*P^e)^k ≤ w ((n : K)-θ) / (w α)^k :=
      div_le_div₀ (apply_nonneg _ _) hb (pow_pos ha0 _) hpow'
    rw [mul_pow] at hh
    convert hh using 1
    ring
  · have hh : w ((n : K)-θ) / (w α)^k ≤ (3*X) / (C⁻¹*P^e)^k :=
      div_le_div₀ (by positivity) hb' (pow_pos (mul_pos (inv_pos.mpr hC)
        (Real.rpow_pos_of_pos hP e)) _) hpow
    rw [mul_pow,inv_pow] at hh
    convert hh using 1
    field_simp

theorem balanced_arithmetic (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 1 ≤ f.natDegree)
    (hc : 0 < f.leadingCoeff) (k : ℕ) (hk : 0 < k) :
    ∃ M : ArithmeticModel f, ∃ (μ : ℕ) (S : Finset (Ideal (𝓞 M.Carrier))) (C X₀ : ℝ),
      0 < μ ∧ 1 ≤ C ∧ 0 < X₀ ∧ (∀ J ∈ S, J ≠ ⊥) ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ (n : ℤ) (p : ℕ),
        X < n → (n : ℝ) ≤ 2*X → p.Prime → X < p → (p : ℤ)^k ∣ f.eval n →
        ¬ (p : ℤ) ∣ f.resultant f.derivative ∧
        ∃ J ∈ S, ∃ α : 𝓞 M.Carrier, α ≠ 0 ∧ ∃ β : 𝓞 M.Carrier,
          (α : M.Carrier)^k * (β : M.Carrier) = (μ : M.Carrier)*((n : M.Carrier)-M.root) ∧
          |(Algebra.norm ℚ (α : M.Carrier) : ℝ)| = ((p*J.absNorm : ℕ) : ℝ) ∧
          ∀ w : InfinitePlace M.Carrier,
            (C⁻¹ * (p : ℝ)^((f.natDegree : ℝ)⁻¹) ≤ w (α : M.Carrier) ∧
              w (α : M.Carrier) ≤ C*(p : ℝ)^((f.natDegree : ℝ)⁻¹)) ∧
            ((2*C^k)⁻¹ * (X/(p : ℝ)^((f.natDegree : ℝ)⁻¹*k)) ≤ w ((β : M.Carrier)/(μ : M.Carrier)) ∧
              w ((β : M.Carrier)/(μ : M.Carrier)) ≤ (3*C^k)*(X/(p : ℝ)^((f.natDegree : ℝ)⁻¹*k))) := by
  let M := arithmeticModel f hf hd
  obtain ⟨B,μ,S,C,hμ,hC,hS,hfac⟩ := arithmetic_factorization_large_primes f hf hd hc
    M.root M.root_eq M.integralRoot M.integralRoot_eq M.powerBasis M.powerBasis_gen k hk
  obtain ⟨D,hD,habsorb⟩ := absorb_finite_ideal_norms S hS C hC
    (f.natDegree : ℝ)⁻¹ (by positivity)
  obtain ⟨R,hR,hdiff⟩ := uniform_root_difference_bounds M.root
  let X₀ := max R (max (B : ℝ) (f.resultant f.derivative).natAbs)
  refine ⟨M,μ,S,D,X₀,hμ,hD,hR.trans_le (le_max_left _ _),hS,?_⟩
  intro X hX n p hn hn' hp hpX hfp
  have hBp : B < p := by
    have hh : (B : ℝ) < p := (le_max_left _ _).trans (le_max_right _ _) |>.trans hX |>.trans_lt hpX
    exact_mod_cast hh
  have hgood : ¬ (p : ℤ) ∣ f.resultant f.derivative := by
    intro h
    have hle : p ≤ (f.resultant f.derivative).natAbs := by
      apply Nat.le_of_dvd (Int.natAbs_pos.mpr (resultant_derivative_ne_zero f hf))
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h
    have hh : ((f.resultant f.derivative).natAbs : ℝ) < p :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hX |>.trans_lt hpX
    exact (not_le_of_gt hh) (by exact_mod_cast hle)
  obtain ⟨J,hJ,α,hα,β,hfactor,hnorm,hbalance⟩ := hfac n p hp hBp hfp
  refine ⟨hgood,J,hJ,α,hα,β,hfactor,hnorm,fun w => ?_⟩
  have hbal := hbalance w
  rw [M.degree_eq] at hbal
  have hαbounds := habsorb p hp.pos J hJ _ hbal.1 hbal.2
  have hXdiff : R ≤ X := (le_max_left _ _).trans hX
  have hβbounds := companion_archimedean_bounds w (α : M.Carrier) (β : M.Carrier)
    M.root n μ k hμ hfactor (p : ℝ) X D (f.natDegree : ℝ)⁻¹
    (by exact_mod_cast hp.pos) (hR.le.trans hXdiff) (lt_of_lt_of_le zero_lt_one hD)
    hαbounds.1 hαbounds.2 (hdiff X hXdiff n hn hn' w).1 (hdiff X hXdiff n hn hn' w).2
  exact ⟨hαbounds,hβbounds⟩

end QuarticPowerFree
end

end OAI
