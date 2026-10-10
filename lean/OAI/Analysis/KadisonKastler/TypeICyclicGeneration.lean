import OAI.Analysis.KadisonKastler.TypeIInjectivity
import OAI.Analysis.KadisonKastler.IncreasingGroupEmbedding

namespace OAI

/-! # Transporting weak generation through the minimal cyclic representation -/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- The inverse minimal cyclic representation preserves the weak closure needed
for generation. The proof uses bounded approximation and weak compactness in
the original representation. -/
theorem typeICyclic_inverse_mem_of_generated_unitBall (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    (Q : VonNeumannAlgebra H) (hQM : Q ≤ M)
    (A : StarSubalgebra ℂ (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))
    (hA : ∀ T ∈ A, ((typeICyclicEquiv hM p hp ξ hξ hpξ).symm T).val ∈ Q)
    (T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ)
    (hT : T ∈ generatedVonNeumannAlgebra A) (hnT : ‖T‖ ≤ 1) :
    ((typeICyclicEquiv hM p hp ξ hξ hpξ).symm T).val ∈ Q := by
  classical
  let K := typeICyclicSpace M ξ
  let e := typeICyclicEquiv hM p hp ξ hξ hpξ
  have hnet := publishedKaplanskyDensity.exists_weak_contraction_net (H := K)
    A T (by
      change T ∈ (generatedVonNeumannAlgebra A : Set _) at hT
      rwa [generatedVonNeumannAlgebra_coe] at hT) hnT
  let c : Finset K × ℕ → A := Classical.choose hnet
  have hc : ∀ d, ‖c d‖ ≤ 1 := (Classical.choose_spec hnet).1
  have hlim : ∀ x y : K, Tendsto (fun d => inner ℂ y ((c d).val x)) atTop
      (𝓝 (inner ℂ y (T x))) := (Classical.choose_spec hnet).2
  let a (d : Finset K × ℕ) : Algebra Q := ⟨(e.symm (c d).val).val, hA _ (c d).property⟩
  have hn (d : Finset K × ℕ) : ‖(a d).val‖ ≤ 1 := by
    change ‖e.symm (c d).val‖ ≤ 1
    rw [← typeICyclicHom_norm hM p hp ξ hξ hpξ]
    change ‖e (e.symm (c d).val)‖ ≤ 1
    rw [e.apply_symm_apply]
    exact hc d
  let ω : Ultrafilter (Finset K × ℕ) := Ultrafilter.of atTop
  obtain ⟨b, _, hb⟩ := exists_weak_operator_ultralimit ω (fun d => (a d).val)
    1 zero_le_one hn
  have hbQ : b ∈ Q := weak_operator_limit_mem Q a b hb
  let bM : Algebra M := ⟨b, hQM hbQ⟩
  have he : e bM = T := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have h₁ : Tendsto (fun d => inner ℂ y ((c d).val x))
        (ω : Filter (Finset K × ℕ)) (𝓝 (inner ℂ y (e bM x))) := by
      have hb' := hb x.val y.val
      have hc_eval (d : Finset K × ℕ) :
          (e.symm (c d).val).val x.val = ((c d).val x : K).val := by
        change (e (e.symm (c d).val) x : H) = _
        rw [e.apply_symm_apply]
      change Tendsto (fun d => inner ℂ y.val ((e.symm (c d).val).val x.val))
        (ω : Filter (Finset K × ℕ)) (𝓝 (inner ℂ y.val (b x.val))) at hb'
      simp_rw [hc_eval] at hb'
      exact hb'
    exact tendsto_nhds_unique h₁ ((hlim x y).mono_left (Ultrafilter.of_le atTop))
  have he' : e.symm T = bM := by rw [← he, e.symm_apply_apply]
  change (e.symm T).val ∈ Q
  rw [he']
  exact hbQ

/-- Weak generation transports to the original type I representation. -/
theorem typeICyclic_inverse_mem_of_generated (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    (Q : VonNeumannAlgebra H) (hQM : Q ≤ M)
    (A : StarSubalgebra ℂ (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))
    (hA : ∀ T ∈ A, ((typeICyclicEquiv hM p hp ξ hξ hpξ).symm T).val ∈ Q)
    (T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ)
    (hT : T ∈ generatedVonNeumannAlgebra A) :
    ((typeICyclicEquiv hM p hp ξ hξ hpξ).symm T).val ∈ Q := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) := {}
  let e := typeICyclicEquiv hM p hp ξ hξ hpξ
  by_cases hzero : T = 0
  · simp only [hzero, map_zero, ZeroMemClass.coe_zero]
    exact Q.zero_mem
  have hn : ‖T‖ ≠ 0 := by
    intro hn
    exact hzero (norm_eq_zero.mp hn)
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  have h := typeICyclic_inverse_mem_of_generated_unitBall hM p hp ξ hξ hpξ
    Q hQM A hA ((‖T‖ : ℂ)⁻¹ • T)
    ((generatedVonNeumannAlgebra A).toStarSubalgebra.smul_mem hT _) hsmall
  have hscale := Q.toStarSubalgebra.smul_mem h (‖T‖ : ℂ)
  have hnC : (‖T‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hscale' : (e.symm ((‖T‖ : ℂ) • ((‖T‖ : ℂ)⁻¹ • T))).val ∈ Q := by
    change ((‖T‖ : ℂ) • e.symm ((‖T‖ : ℂ)⁻¹ • T)).val ∈ Q at hscale
    have hs := map_smul e.symm.toAlgEquiv.toLinearMap (‖T‖ : ℂ) ((‖T‖ : ℂ)⁻¹ • T)
    change e.symm ((‖T‖ : ℂ) • ((‖T‖ : ℂ)⁻¹ • T)) =
      (‖T‖ : ℂ) • e.symm ((‖T‖ : ℂ)⁻¹ • T) at hs
    rw [hs]
    exact hscale
  simpa only [smul_smul, mul_inv_cancel₀ hnC, one_smul] using hscale'


/-- Transfer a generating unitary group from the minimal cyclic space. -/
def typeICyclicGroup {G : Type*} [Group G] (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    (U : G →* unitary (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ)) :
    G →* unitary (Algebra M) where
  toFun g := ⟨(typeICyclicEquiv hM p hp ξ hξ hpξ).symm (U g),
    Unitary.map_mem (typeICyclicEquiv hM p hp ξ hξ hpξ).symm.toStarAlgHom (U g).property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g k := by apply Subtype.ext; simp

theorem typeICyclicGroup_generates {G : Type*} [Group G] (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    (U : G →* unitary (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))
    (hgen : ∀ T, T ∈ generatedVonNeumannAlgebra
      (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g :
        typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))))) :
    generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ (Set.range (fun g =>
      (typeICyclicGroup hM p hp ξ hξ hpξ U g : H →L[ℂ] H)))) = M := by
  let e := typeICyclicEquiv hM p hp ξ hξ hpξ
  let V := typeICyclicGroup hM p hp ξ hξ hpξ U
  let Q := generatedVonNeumannAlgebra
    (StarAlgebra.adjoin ℂ (Set.range (fun g => (V g : H →L[ℂ] H))))
  have hQM : Q ≤ M := by
    apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro _ ⟨g, rfl⟩
    exact (V g).val.property
  change Q = M
  apply le_antisymm hQM
  intro x hx
  let a : Algebra M := ⟨x, hx⟩
  have hA : ∀ T ∈ StarAlgebra.adjoin ℂ (Set.range (fun g => (U g :
        typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))), (e.symm T).val ∈ Q := by
    let φ := M.toStarSubalgebra.subtype.comp e.symm.toStarAlgHom
    have ha : StarAlgebra.adjoin ℂ (Set.range (fun g => (U g :
        typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ))) ≤
        Q.toStarSubalgebra.comap φ := by
      apply StarAlgebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      exact subset_generatedVonNeumannAlgebra _
        (StarAlgebra.subset_adjoin ℂ _ ⟨g, rfl⟩)
    exact fun T hT => ha hT
  have ht := typeICyclic_inverse_mem_of_generated hM p hp ξ hξ hpξ
    Q hQM _ hA (e a) (hgen (e a))
  change (e.symm (e a)).val ∈ Q at ht
  simpa only [e.symm_apply_apply] using ht

end

end KadisonKastler

end OAI
