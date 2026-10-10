import OAI.Analysis.KadisonKastler.FaithfulCyclicConstruction
import OAI.Analysis.KadisonKastler.NearInclusionDistance

namespace OAI

/-! # The diagonal countable amplification as a represented von Neumann algebra

This preserves the ordinary near inclusion constant. Its faithful cyclic
corner will put the first finite factor in standard position.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def countableDiagonalAlgebra (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra (CountableHilbertSum H) :=
  generatedVonNeumannAlgebra (countableDiagonalHom M).range

theorem countableDiagonalHom_norm (M : VonNeumannAlgebra H) (a : Algebra M) :
    ‖countableDiagonalHom M a‖ = ‖a‖ := norm_l2Diagonal H a.val

theorem countableDiagonalHom_injective (M : VonNeumannAlgebra H) :
    Function.Injective (countableDiagonalHom M) := by
  intro a b hab
  apply Subtype.ext
  exact l2DiagonalHom_injective H hab

theorem countableDiagonalHom_surjective_unitBall (M : VonNeumannAlgebra H)
    (T : CountableHilbertSum H →L[ℂ] CountableHilbertSum H)
    (hT : T ∈ countableDiagonalAlgebra M) (hnT : ‖T‖ ≤ 1) :
    ∃ a : Algebra M, ‖a‖ ≤ 1 ∧ countableDiagonalHom M a = T := by
  classical
  let K := CountableHilbertSum H
  let ρ := countableDiagonalHom M
  let A := ρ.range
  have hc : T ∈ Set.centralizer (Set.centralizer (A : Set (K →L[ℂ] K))) := by
    change T ∈ (generatedVonNeumannAlgebra A : Set (K →L[ℂ] K)) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  obtain ⟨c, hn, hlim⟩ := publishedKaplanskyDensity.exists_weak_contraction_net A T hc hnT
  choose a ha using fun d => (c d).property
  have ha' (d : Finset K × ℕ) : ρ (a d) = (c d).val := ha d
  have hna (d : Finset K × ℕ) : ‖a d‖ ≤ 1 := by
    rw [← countableDiagonalHom_norm M]
    exact (congrArg norm (ha' d)).le.trans (hn d)
  let ω : Ultrafilter (Finset K × ℕ) := Ultrafilter.of atTop
  obtain ⟨b, hb, hweak⟩ := exists_weak_operator_ultralimit ω
    (fun d => (a d).val) 1 zero_le_one hna
  let a₀ : Algebra M := ⟨b, weak_operator_limit_mem M a b hweak⟩
  refine ⟨a₀, hb, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have h₁ := l2Diagonal_tendsto_weak (fun d => (a d).val) b 1
    (Eventually.of_forall hna) hweak x y
  have h₂ : Tendsto (fun d => inner ℂ y (ρ (a d) x)) (ω : Filter (Finset K × ℕ))
      (𝓝 (inner ℂ y (T x))) := by
    simpa only [ha'] using (hlim x y).mono_left (Ultrafilter.of_le atTop)
  exact tendsto_nhds_unique h₁ h₂

theorem countableDiagonalHom_surjective (M : VonNeumannAlgebra H)
    (T : CountableHilbertSum H →L[ℂ] CountableHilbertSum H)
    (hT : T ∈ countableDiagonalAlgebra M) :
    ∃ a : Algebra M, countableDiagonalHom M a = T := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (CountableHilbertSum H →L[ℂ] CountableHilbertSum H) := {}
  by_cases ht : T = 0
  · exact ⟨0, by rw [map_zero, ht]⟩
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  obtain ⟨a, _, ha⟩ := countableDiagonalHom_surjective_unitBall M
    ((‖T‖ : ℂ)⁻¹ • T) ((countableDiagonalAlgebra M).toStarSubalgebra.smul_mem hT _) hsmall
  refine ⟨(‖T‖ : ℂ) • a, ?_⟩
  calc
    countableDiagonalHom M ((‖T‖ : ℂ) • a) = (‖T‖ : ℂ) • countableDiagonalHom M a :=
      (countableDiagonalHom M).toAlgHom.toLinearMap.map_smul _ _
    _ = T := by
      rw [ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

def countableDiagonalEquiv (M : VonNeumannAlgebra H) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (countableDiagonalAlgebra M) := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (Algebra (countableDiagonalAlgebra M)) := {}
  let ρ : Algebra M →⋆ₐ[ℂ] Algebra (countableDiagonalAlgebra M) :=
    (countableDiagonalHom M).codRestrict (countableDiagonalAlgebra M).toStarSubalgebra
    (fun a => subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩)
  apply StarAlgEquiv.ofBijective ρ
  constructor
  · intro a b hab
    exact countableDiagonalHom_injective M (congrArg Subtype.val hab)
  · intro T
    obtain ⟨a, ha⟩ := countableDiagonalHom_surjective M T.val T.property
    exact ⟨a, Subtype.ext ha⟩

theorem nearInclusion_countableDiagonal {M N : VonNeumannAlgebra H} {γ : ℝ}
    (h : NearInclusion M N γ) :
    NearInclusion (countableDiagonalAlgebra M) (countableDiagonalAlgebra N) γ := by
  obtain ⟨δ, hδ, hd⟩ := h
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := countableDiagonalHom_surjective_unitBall M x hx.1 hx.2
  have hset : (countableDiagonalAlgebra N : Set _) =
      l2Diagonal '' (N : Set (H →L[ℂ] H)) := by
    ext T
    constructor
    · intro hT
      obtain ⟨b, rfl⟩ := countableDiagonalHom_surjective N T hT
      exact ⟨b.val, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact subset_generatedVonNeumannAlgebra _ ⟨⟨b, hb⟩, rfl⟩
  have he : Isometry (l2Diagonal (E := H)) := by
    apply isometry_iff_dist_eq.mpr
    intro S T
    simp only [dist_eq_norm]
    have hs : l2Diagonal S - l2Diagonal T = l2Diagonal (S - T) :=
      ((l2DiagonalHom (E := H)).map_sub S T).symm
    rw [hs, norm_l2Diagonal H]
  change Metric.infDist (l2Diagonal a.val) (countableDiagonalAlgebra N : Set _) ≤ δ
  rw [hset, Metric.infDist_image he]
  exact hd a.val ⟨a.property, ha⟩

end

end KadisonKastler

end OAI
