import OAI.Analysis.KadisonKastler.HilbertPairRepresentation
import OAI.Analysis.KadisonKastler.KaplanskyDensity
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! # The diagonal algebra on two Hilbert copies

Weak compactness shows that duplicating a represented von Neumann algebra
already has weakly closed range. This is the ambient algebra for two vector
states of the same represented algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def diagonalPairHom (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :=
  hilbertPairRepresentation M.toStarSubalgebra.subtype M.toStarSubalgebra.subtype

theorem diagonalPairHom_injective (M : VonNeumannAlgebra H) :
    Function.Injective (diagonalPairHom M) := by
  intro a b hab
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H) =>
    (T (WithLp.toLp 2 (x, 0))).fst) hab

theorem diagonalPairHom_norm (M : VonNeumannAlgebra H) (a : Algebra M) :
    ‖diagonalPairHom M a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (diagonalPairHom M) (diagonalPairHom_injective M) a

theorem diagonalPairHom_tendsto_weak (M : VonNeumannAlgebra H)
    {I : Type*} {l : Filter I} (a : I → Algebra M) (b : Algebra M)
    (h : ∀ x y, Tendsto (fun i => inner ℂ y ((a i).val x)) l (𝓝 (inner ℂ y (b.val x))))
    (x y : WithLp 2 (H × H)) :
    Tendsto (fun i => inner ℂ y (diagonalPairHom M (a i) x)) l
      (𝓝 (inner ℂ y (diagonalPairHom M b x))) := by
  change Tendsto (fun i => inner ℂ y.fst ((a i).val x.fst) +
    inner ℂ y.snd ((a i).val x.snd)) l
    (𝓝 (inner ℂ y.fst (b.val x.fst) + inner ℂ y.snd (b.val x.snd)))
  exact (h x.fst y.fst).add (h x.snd y.snd)

def diagonalPairAlgebra (M : VonNeumannAlgebra H) : VonNeumannAlgebra (WithLp 2 (H × H)) :=
  generatedVonNeumannAlgebra (diagonalPairHom M).range

theorem diagonalPairHom_surjective_unitBall (M : VonNeumannAlgebra H)
    (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (hT : T ∈ diagonalPairAlgebra M) (hnT : ‖T‖ ≤ 1) :
    ∃ a : Algebra M, ‖a‖ ≤ 1 ∧ diagonalPairHom M a = T := by
  classical
  let K := WithLp 2 (H × H)
  let ρ := diagonalPairHom M
  let A := ρ.range
  have hcomm : T ∈ Set.centralizer (Set.centralizer (A : Set (K →L[ℂ] K))) := by
    change T ∈ (generatedVonNeumannAlgebra A : Set _) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  obtain ⟨d, hd, hlim⟩ := publishedKaplanskyDensity.exists_weak_contraction_net A T hcomm hnT
  choose a ha using fun i => (d i).property
  have ha' (i : Finset K × ℕ) : ρ (a i) = (d i).val := ha i
  have hn (i : Finset K × ℕ) : ‖a i‖ ≤ 1 := by
    rw [← diagonalPairHom_norm M]
    change ‖ρ (a i)‖ ≤ 1
    rw [ha' i]
    exact hd i
  let ω : Ultrafilter (Finset K × ℕ) := Ultrafilter.of atTop
  obtain ⟨b, hb, hweak⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val) 1 zero_le_one hn
  let b₀ : Algebra M := ⟨b, weak_operator_limit_mem M a b hweak⟩
  refine ⟨b₀, hb, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have h₁ := diagonalPairHom_tendsto_weak M a b₀ hweak x y
  have h₂ : Tendsto (fun i => inner ℂ y (ρ (a i) x)) (ω : Filter (Finset K × ℕ))
      (𝓝 (inner ℂ y (T x))) := by
    simpa only [ha'] using (hlim x y).mono_left (Ultrafilter.of_le atTop)
  exact tendsto_nhds_unique h₁ h₂

theorem diagonalPairHom_surjective (M : VonNeumannAlgebra H)
    (T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H))
    (hT : T ∈ diagonalPairAlgebra M) : ∃ a : Algebra M, diagonalPairHom M a = T := by
  by_cases hzero : T = 0
  · exact ⟨0, by rw [map_zero, hzero]⟩
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  obtain ⟨a, _, ha⟩ := diagonalPairHom_surjective_unitBall M ((‖T‖ : ℂ)⁻¹ • T)
    ((diagonalPairAlgebra M).smul_mem hT _) hsmall
  refine ⟨(‖T‖ : ℂ) • a, ?_⟩
  rw [map_smul, ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

def diagonalPairEquiv (M : VonNeumannAlgebra H) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (diagonalPairAlgebra M) := by
  let ρ := (diagonalPairHom M).codRestrict (diagonalPairAlgebra M).toStarSubalgebra
    (fun a => subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩)
  apply StarAlgEquiv.ofBijective ρ
  constructor
  · intro a b hab
    exact diagonalPairHom_injective M (congrArg Subtype.val hab)
  · intro T
    obtain ⟨a, ha⟩ := diagonalPairHom_surjective M T.val T.property
    exact ⟨a, Subtype.ext ha⟩

theorem diagonalPairEquiv_coe (M : VonNeumannAlgebra H) (a : Algebra M) :
    (diagonalPairEquiv M a).val = diagonalPairHom M a := rfl

end

end KadisonKastler

end OAI
