import OAI.NumberTheory.PowerFree.UnitBalancing

namespace OAI

namespace QuarticPowerFree

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

structure IntegralEmbeddingChart (K : Type*) [Field K] [NumberField K] (d : ℕ) where
  σ : Fin d ≃ (K →+* ℂ)
  B : Basis (Fin d) ℤ (𝓞 K)
  V : Basis (Fin d) ℚ K
  compatible : ∀ j, V j = (B j:K)
  det_ne_zero : (Matrix.of (fun i j => σ i (V j))).det ≠ 0

noncomputable def integralEmbeddingChart (K : Type*) [Field K] [NumberField K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) : IntegralEmbeddingChart K d := by
  classical
  let e : Fin d ≃ (K →+* ℂ) := (Fintype.equivFinOfCardEq ((NumberField.Embeddings.card K ℂ).trans hd)).symm
  let r := (equivReindex K).symm.trans e.symm
  let B := (RingOfIntegers.basis K).reindex r
  let V := (integralBasis K).reindex r
  refine ⟨e,B,V,?_,?_⟩
  · intro j
    simp [V,B,Basis.reindex_apply,integralBasis_apply]
  · have hm : Matrix.of (fun i j => e i (V j)) =
        ((basisMatrix K).transpose).reindex e.symm e.symm := by
      ext i j
      simp [V,r,Matrix.reindex_apply,Matrix.submatrix_apply,basisMatrix,
        canonicalEmbedding.latticeBasis_apply]
    rw [hm,Matrix.det_reindex_self,Matrix.det_transpose]
    exact det_of_basisMatrix_non_zero K

noncomputable def IntegralEmbeddingChart.A {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => T.σ i (T.V j)

noncomputable def IntegralEmbeddingChart.coord {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α : 𝓞 K) : Fin d → ℤ := T.B.repr α

theorem IntegralEmbeddingChart.embedding {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α : 𝓞 K) :
    T.A.mulVec (fun j => (T.coord α j:ℂ)) = fun i => T.σ i (α:K) := by
  ext i
  have hh := congrArg (fun t : 𝓞 K => T.σ i (t:K)) (T.B.sum_repr α)
  simpa only [map_sum,map_zsmul,zsmul_eq_mul,map_mul,map_intCast,Matrix.mulVec,dotProduct,
    IntegralEmbeddingChart.A,IntegralEmbeddingChart.coord,T.compatible,mul_comm] using hh

theorem IntegralEmbeddingChart.inverse_coordinates {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α : 𝓞 K) :
    T.A⁻¹.mulVec (fun i => T.σ i (α:K)) = fun j => (T.coord α j:ℂ) := by
  rw [←T.embedding α,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul T.A (show IsUnit T.A.det from Ne.isUnit T.det_ne_zero),Matrix.one_mulVec]

theorem IntegralEmbeddingChart.coordinates_bound {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ (α : 𝓞 K) (R : ℝ), 0 ≤ R →
      (∀ i, ‖T.σ i (α:K)‖ ≤ R) → ∀ j, |(T.coord α j:ℝ)| ≤ E*R := by
  let E : ℝ := 1+∑ j, ∑ i, ‖T.A⁻¹ j i‖
  have hsum : 0 ≤ ∑ j, ∑ i, ‖T.A⁻¹ j i‖ := by positivity
  refine ⟨E,by dsimp [E]; linarith,fun α R hR hα j => ?_⟩
  have hej : ∑ i, ‖T.A⁻¹ j i‖ ≤ E := by
    have hh := Finset.single_le_sum (f := fun j => ∑ i, ‖T.A⁻¹ j i‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ j)
    dsimp [E]; linarith
  have hcoord := congrFun (T.inverse_coordinates α) j
  have hnorm : |(T.coord α j:ℝ)| = ‖(T.coord α j:ℂ)‖ := by simp
  rw [hnorm,←hcoord]
  calc
    ‖∑ i, T.A⁻¹ j i*T.σ i (α:K)‖ ≤ ∑ i, ‖T.A⁻¹ j i‖*‖T.σ i (α:K)‖ :=
      norm_sum_le_of_le _ (fun i _ => (norm_mul _ _).le)
    _ ≤ ∑ i, ‖T.A⁻¹ j i‖*R := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hα i) (norm_nonneg _))
    _ = (∑ i, ‖T.A⁻¹ j i‖)*R := (Finset.sum_mul ..).symm
    _ ≤ E*R := mul_le_mul_of_nonneg_right hej hR

end

section
open MvPolynomial
open scoped Classical BigOperators

theorem coordinateLinearForm_inverse {n d : ℕ} {K : Type*} [Field K]
    (A : Matrix (Fin d) (Fin d) K) (hA : A.det ≠ 0) (x : Fin d → Fin n) (j : Fin d) :
    ∑ i, C (A⁻¹ j i)*coordinateLinearForm x (A i) = X (x j) := by
  simp only [coordinateLinearForm,Finset.mul_sum,←mul_assoc,←map_mul]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_mul,←map_sum]
  have he (l : Fin d) : ∑ i, A⁻¹ j i*A i l = if j=l then 1 else 0 := by
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) K => M j l)
      (Matrix.nonsing_inv_mul A (Ne.isUnit hA))
    simpa only [Matrix.mul_apply,Matrix.one_apply] using hh
  simp only [he]
  simp

theorem coordinateLinearForm_mem_adjoin {n d : ℕ} {K : Type*} [Field K]
    (A : Matrix (Fin d) (Fin d) K) (hA : A.det ≠ 0) (x : Fin d → Fin n)
    (S : Subalgebra K (MvPolynomial (Fin n) K))
    (h : ∀ i, coordinateLinearForm x (A i) ∈ S) (j : Fin d) : X (x j) ∈ S := by
  rw [←coordinateLinearForm_inverse A hA x j]
  exact S.sum_mem (fun i _ => S.mul_mem (S.algebraMap_mem _) (h i))

theorem coordinateLinearForm_totalDegree {n d : ℕ} {K : Type*} [Field K]
    (x : Fin d → Fin n) (c : Fin d → K) : (coordinateLinearForm x c).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

theorem coordinateLinearForm_weightedSpace {n d : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) (x : Fin d → Fin n) (c : Fin d → K) (W : ℕ)
    (hx : ∀ i, w (x i) ≤ W) : coordinateLinearForm x c ∈ weightedSpace w W := by
  apply Submodule.sum_mem
  intro i _
  rw [←smul_eq_C_mul]
  apply Submodule.smul_mem
  rw [mem_weightedSpace]
  simpa [weightedTotalDegree,MvPolynomial.X,Finsupp.weight_single] using hx i

noncomputable def normBoxWeight (d : ℕ) : Fin (d+d) → ℝ := Fin.addCases (fun _ => 1/3) (fun _ => 2/5)
noncomputable def normBoxNatWeight (d : ℕ) : Fin (d+d) → ℕ := Fin.addCases (fun _ => 5) (fun _ => 6)

theorem normBoxWeight_pos (d) (j) : 0 < normBoxWeight d j := by
  induction j using Fin.addCases <;> norm_num only [normBoxWeight,Fin.addCases_left,Fin.addCases_right]
theorem normBoxWeight_le (d) (j) : normBoxWeight d j ≤ 2/5 := by
  induction j using Fin.addCases <;> norm_num only [normBoxWeight,Fin.addCases_left,Fin.addCases_right]
theorem normBoxNatWeight_ne (d) (j) : normBoxNatWeight d j ≠ 0 := by
  induction j using Fin.addCases <;> norm_num only [normBoxNatWeight,Fin.addCases_left,Fin.addCases_right]
theorem normBoxWeight_scale (d) (j) : (normBoxNatWeight d j:ℝ) = 15*normBoxWeight d j := by
  induction j using Fin.addCases <;> norm_num only [normBoxWeight,normBoxNatWeight,Fin.addCases_left,Fin.addCases_right]

theorem pairedLinearForms_generate {d : ℕ} {K : Type*} [Field K]
    (A : Matrix (Fin d) (Fin d) K) (hA : A.det ≠ 0) (s : K) (hs : s ≠ 0) :
    Algebra.adjoin K (Set.range (fun i => coordinateLinearForm (Fin.castAdd d) (A i)) ∪
      Set.range (fun i => C s*coordinateLinearForm (Fin.natAdd d) (A i))) = ⊤ := by
  let S := Algebra.adjoin K (Set.range (fun i => coordinateLinearForm (Fin.castAdd d) (A i)) ∪
      Set.range (fun i => C s*coordinateLinearForm (Fin.natAdd d) (A i)))
  have hleft (i) : coordinateLinearForm (Fin.castAdd d) (A i) ∈ S :=
    Algebra.subset_adjoin (Or.inl ⟨i,rfl⟩)
  have hright (i) : coordinateLinearForm (Fin.natAdd d) (A i) ∈ S := by
    have hh : C s*coordinateLinearForm (Fin.natAdd d) (A i) ∈ S := Algebra.subset_adjoin (Or.inr ⟨i,rfl⟩)
    have he : C s⁻¹*(C s*coordinateLinearForm (Fin.natAdd d) (A i)) = coordinateLinearForm (Fin.natAdd d) (A i) := by
      rw [←mul_assoc,←map_mul,inv_mul_cancel₀ hs,map_one,one_mul]
    rw [←he]
    exact S.mul_mem (S.algebraMap_mem _) hh
  have hx (j : Fin (d+d)) : X j ∈ S := by
    induction j using Fin.addCases with
    | left j => exact coordinateLinearForm_mem_adjoin A hA _ S hleft j
    | right j => exact coordinateLinearForm_mem_adjoin A hA _ S hright j
  apply top_unique
  rw [←adjoin_range_X (R := K) (σ := Fin (d+d))]
  exact Algebra.adjoin_le (by rintro _ ⟨j,rfl⟩; exact hx j)

end

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

theorem arithmeticModel_distinct (f : Polynomial ℤ) (M : ArithmeticModel f)
    (e : Fin f.natDegree ≃ (M.Carrier →+* ℂ)) :
    Function.Injective (fun i => e i M.root) := by
  intro i j hij
  apply e.injective
  apply (RingHom.equivRatAlgHom M.Carrier ℂ).injective
  apply M.powerBasis.algHom_ext
  change e i M.powerBasis.gen = e j M.powerBasis.gen
  rw [M.powerBasis_gen,M.integralRoot_eq]
  simp only [map_mul,map_intCast,hij]

noncomputable def normBoxOfChart {K : Type} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (θ : K) (hθ : Function.Injective (fun i => T.σ i θ))
    (μ : ℕ) (hμ : 0 < μ) (hd : 0 < d) :
    NormBoxSystem (d+d) d (d+1) (normBoxWeight d) (normBoxNatWeight d) := by
  let a : Fin d → MvPolynomial (Fin (d+d)) ℂ := fun i => coordinateLinearForm (Fin.castAdd d) (T.A i)
  let b : Fin d → MvPolynomial (Fin (d+d)) ℂ := fun i => C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd d) (T.A i)
  let i₀ : Fin d := ⟨0,hd⟩
  have hb (i) : (b i).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using coordinateLinearForm_totalDegree (Fin.natAdd d) (T.A i))
  refine ⟨K,T.V,T.V.linearIndependent,T.σ,fun i => T.σ i θ,hθ,Fin.castAdd d,
    ?_,b,a i₀^(d-2)*b i₀+C (T.σ i₀ θ),?_,?_,?_,?_,?_⟩
  · intro i; simp only [normBoxWeight,Fin.addCases_left]
  · exact pairedLinearForms_generate T.A T.det_ne_zero (μ:ℂ)⁻¹ (inv_ne_zero (by exact_mod_cast hμ.ne'))
  · intro i; exact (coordinateLinearForm_totalDegree _ _).trans (by omega)
  · apply (totalDegree_add _ _).trans
    rw [max_le_iff]
    refine ⟨(totalDegree_mul _ _).trans ?_,by simp⟩
    have ha : (a i₀).totalDegree ≤ 1 := coordinateLinearForm_totalDegree _ _
    have hp := (totalDegree_pow (a i₀) (d-2)).trans (Nat.mul_le_mul_left (d-2) ha)
    have hh := hb i₀
    omega
  · intro i
    exact coordinateLinearForm_weightedSpace _ _ _ _ (fun j => by simp only [normBoxNatWeight,Fin.addCases_left,le_refl])
  · intro i
    change C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd d) (T.A i) ∈ _
    rw [←smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (coordinateLinearForm_weightedSpace _ _ _ _ (fun j => by simp only [normBoxNatWeight,Fin.addCases_right,le_refl]))

noncomputable def normIntegralPoint {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α β : 𝓞 K) : Fin (d+d) → ℤ :=
  Fin.addCases (T.coord α) (T.coord β)

theorem normIntegralPoint_left {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α β : 𝓞 K) (i : Fin d) :
    MvPolynomial.aeval (fun j => (normIntegralPoint T α β j:ℂ))
      (coordinateLinearForm (Fin.castAdd d) (T.A i)) = T.σ i (α:K) := by
  simp only [coordinateLinearForm,map_sum,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
    normIntegralPoint,Fin.addCases_left]
  exact congrFun (T.embedding α) i

theorem normIntegralPoint_right {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α β : 𝓞 K) (μ : ℕ) (i : Fin d) :
    MvPolynomial.aeval (fun j => (normIntegralPoint T α β j:ℂ))
      (C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd d) (T.A i)) = T.σ i (β:K)/(μ:ℂ) := by
  simp only [map_mul,MvPolynomial.aeval_C,coordinateLinearForm,map_sum,MvPolynomial.aeval_X,
    normIntegralPoint,Fin.addCases_right,Algebra.algebraMap_self,RingHom.id_apply]
  rw [show ∑ j, T.A i j*(T.coord β j:ℂ) = T.σ i (β:K) from congrFun (T.embedding β) i]
  rw [div_eq_mul_inv,mul_comm]

theorem normIntegralPoint_equation {K : Type} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (θ : K) (hθ : Function.Injective (fun i => T.σ i θ))
    (μ : ℕ) (hμ : 0 < μ) (hd : 0 < d) (α β : 𝓞 K) (n : ℤ)
    (he : (α:K)^(d-2)*(β:K) = (μ:K)*((n:K)-θ)) :
    let M := normBoxOfChart T θ hθ μ hμ hd
    let z := normIntegralPoint T α β
    MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = n ∧ PointOn M.ideal z := by
  let M := normBoxOfChart T θ hθ μ hμ hd
  let z := normIntegralPoint T α β
  have ha (i) : MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) = T.σ i (α:K) := normIntegralPoint_left T α β i
  have hb (i) : MvPolynomial.aeval (fun j => (z j:ℂ)) (M.b i) = T.σ i (β:K)/(μ:ℂ) := normIntegralPoint_right T α β μ i
  have hμc : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hrel (i) : MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i)^(d-2)*
      MvPolynomial.aeval (fun j => (z j:ℂ)) (M.b i) = (n:ℂ)-T.σ i θ := by
    rw [ha,hb,←mul_div_assoc]
    have hh := congrArg (T.σ i) he
    simp only [map_mul,map_pow,map_natCast,map_sub,map_intCast] at hh
    rw [hh,mul_div_cancel_left₀ _ hμc]
  have hq : MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = (n:ℂ) := by
    change MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a ⟨0,hd⟩^(d-2)*M.b ⟨0,hd⟩+C (T.σ ⟨0,hd⟩ θ)) = _
    rw [map_add,map_mul,map_pow,MvPolynomial.aeval_C,hrel]
    simp only [Algebra.algebraMap_self,RingHom.id_apply]
    ring
  refine ⟨hq,?_⟩
  change M.ideal ≤ RingHom.ker (MvPolynomial.eval (fun j => (z j:ℂ)))
  apply Ideal.span_le.mpr
  rintro p ⟨i,rfl⟩
  change MvPolynomial.aeval (fun j => (z j:ℂ)) (M.equation i) = 0
  simp only [NormBoxSystem.equation,map_add,map_sub,map_mul,map_pow,MvPolynomial.aeval_C,hrel,hq]
  change (n:ℂ)-T.σ i θ-n+T.σ i θ = 0
  ring

end

open NumberField
open scoped Classical BigOperators

theorem selected_prime_count {ι : Type*} (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) (X : ℝ) (hXp : X < p) (S : Finset ι) (a : ι → ℤ)
    (hinj : Set.InjOn a (S:Set ι))
    (hrange : ∀ z ∈ S, X < (a z:ℝ) ∧ (a z:ℝ) ≤ 2*X)
    (hroot : ∀ z ∈ S, (p:ℤ) ∣ f.eval (a z)) : S.card ≤ f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := primitive_map_zmod_ne_zero f hf p hp
  have hmap : Set.MapsTo (fun z => (a z : ZMod p)) (S:Set _) (F.roots.toFinset:Set _) := by
    intro z hz
    rw [Finset.mem_coe,Multiset.mem_toFinset,Polynomial.mem_roots hF]
    change F.eval (a z : ZMod p) = 0
    rw [show F = f.map (Int.castRingHom (ZMod p)) from rfl,Polynomial.eval_map]
    change f.eval₂ (Int.castRingHom (ZMod p)) ((Int.castRingHom (ZMod p)) (a z)) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hroot z hz)
  have hmodinj : Set.InjOn (fun z => (a z : ZMod p)) (S:Set _) := by
    intro u hu v hv huv
    apply hinj hu hv
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (a u) (a v) p).mp huv
    obtain ⟨hu1,hu2⟩ := hrange u hu
    obtain ⟨hv1,hv2⟩ := hrange v hv
    have hh : |((a v-a u:ℤ):ℝ)| < (p:ℝ) := by
      push_cast
      rw [abs_lt]
      constructor <;> linarith
    have hh' : (a v-a u).natAbs < p := by
      exact_mod_cast (show ((a v-a u).natAbs:ℝ) < p by simpa only [Nat.cast_natAbs,Int.cast_abs] using hh)
    have he : a v-a u = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hh')
    exact (sub_eq_zero.mp he).symm
  calc
    S.card ≤ F.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmap hmodinj
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := Polynomial.card_roots' _
    _ ≤ f.natDegree := Polynomial.natDegree_map_le

theorem norm_left_fibre_count {ι K : Type*} [Field K] [NumberField K]
    (f : Polynomial ℤ) (hf : f.IsPrimitive) (S : Finset ι) (a : ι → ℤ)
    (hinj : Set.InjOn a (S:Set ι)) (X : ℝ)
    (hrange : ∀ i ∈ S, X < (a i:ℝ) ∧ (a i:ℝ) ≤ 2*X)
    (P : ι → ℕ) (J : ι → Ideal (𝓞 K)) (A : ι → 𝓞 K)
    (Q : Finset (Ideal (𝓞 K))) (hQ : ∀ I ∈ Q, I ≠ ⊥)
    (hq : ∀ i ∈ S, J i ∈ Q)
    (hp : ∀ i ∈ S, (P i).Prime ∧ X < P i ∧ (P i:ℤ) ∣ f.eval (a i))
    (hnorm : ∀ i ∈ S, |(Algebra.norm ℚ (A i:K):ℝ)| = ((P i*Ideal.absNorm (J i):ℕ):ℝ))
    (α : 𝓞 K) : (S.filter (fun i => A i = α)).card ≤ Q.card*f.natDegree := by
  classical
  let R := S.filter (fun i => A i=α)
  have hc (I) (hI : I ∈ Q) : (R.filter (fun i => J i=I)).card ≤ f.natDegree := by
    by_cases he : (R.filter (fun i => J i=I)).Nonempty
    · obtain ⟨i₀,hi₀⟩ := he
      obtain ⟨hiR,hiJ⟩ := Finset.mem_filter.mp hi₀
      obtain ⟨hiS,hiA⟩ := Finset.mem_filter.mp hiR
      have hN : 0 < I.absNorm := Nat.pos_of_ne_zero (fun hz => hQ I hI (Ideal.absNorm_eq_zero_iff.mp hz))
      have hP (i) (hi : i ∈ R.filter (fun i => J i=I)) : P i = P i₀ := by
        obtain ⟨hiR',hiJ'⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiS',hiA'⟩ := Finset.mem_filter.mp hiR'
        have h₁ := hnorm i hiS'
        have h₂ := hnorm i₀ hiS
        rw [hiA',hiJ'] at h₁
        rw [hiA,hiJ] at h₂
        have hmul : P i*I.absNorm = P i₀*I.absNorm := by exact_mod_cast h₁.symm.trans h₂
        exact Nat.eq_of_mul_eq_mul_right hN hmul
      apply selected_prime_count f hf (P i₀) (hp i₀ hiS).1 X (hp i₀ hiS).2.1 (R.filter (fun i => J i=I)) a
      · exact hinj.mono (fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1)
      · intro i hi
        exact hrange i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
      · intro i hi
        rw [←hP i hi]
        exact (hp i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1).2.2
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
      exact Nat.zero_le _
  have hcover : R ⊆ Q.biUnion (fun I => R.filter (fun i => J i=I)) := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨J i,hq i (Finset.mem_filter.mp hi).1,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
  calc
    R.card ≤ (Q.biUnion (fun I => R.filter (fun i => J i=I))).card := Finset.card_le_card hcover
    _ ≤ ∑ I ∈ Q, (R.filter (fun i => J i=I)).card := Finset.card_biUnion_le
    _ ≤ ∑ _I ∈ Q, f.natDegree := Finset.sum_le_sum hc
    _ = Q.card*f.natDegree := by simp

end QuarticPowerFree

end OAI
