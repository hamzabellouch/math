import OAI.Analysis.KadisonKastler.FaithfulCyclicConstruction

namespace OAI

/-! # Ranges of faithful representations continuous on bounded weak nets

Kaplansky approximation and compactness of the source operator ball show
that the range is already a von Neumann algebra. The same approximation
transports a specified generating algebra into a target von Neumann algebra.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def BoundedWeakNormal (M : VonNeumannAlgebra H) (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ {ι : Type u} {l : Filter ι} (a : ι → Algebra M) (b : Algebra M) (C : ℝ),
    (∀ᶠ i in l, ‖a i‖ ≤ C) →
    (∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) →
    ∀ x y : K, Tendsto (fun i => inner ℂ y (φ (a i) x)) l
      (𝓝 (inner ℂ y (φ b x)))

theorem boundedWeakNormal_maps_generated
    (M : VonNeumannAlgebra H) (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hφ : BoundedWeakNormal M φ) (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hBM : B ≤ M.toStarSubalgebra) (hMB : M ≤ generatedVonNeumannAlgebra B)
    (N : VonNeumannAlgebra K)
    (hBN : ∀ a : B, φ ⟨a.val, hBM a.property⟩ ∈ N) :
    ∀ a : Algebra M, φ a ∈ N := by
  classical
  have hball (a : Algebra M) (ha : ‖a‖ ≤ 1) : φ a ∈ N := by
    have hb : a.val ∈ Set.centralizer (Set.centralizer (B : Set (H →L[ℂ] H))) := by
      have h := hMB a.property
      change a.val ∈ (generatedVonNeumannAlgebra B : Set (H →L[ℂ] H)) at h
      rwa [generatedVonNeumannAlgebra_coe] at h
    obtain ⟨c, hc, hlim⟩ := publishedKaplanskyDensity.exists_weak_contraction_net B a.val hb ha
    let d : Finset H × ℕ → Algebra M := fun i => ⟨(c i).val, hBM (c i).property⟩
    let e : Finset H × ℕ → Algebra N := fun i => ⟨φ (d i), hBN (c i)⟩
    exact weak_operator_limit_mem N e (φ a)
      (hφ d a 1 (Eventually.of_forall hc) hlim)
  intro a
  by_cases hz : a = 0
  · rw [hz, map_zero]; exact N.zero_mem
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let c : ℂ := (‖a‖ : ℂ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
  have hsmall : ‖c • a‖ ≤ 1 := by
    simp only [c, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg a), inv_mul_cancel₀ hn, le_refl]
  have hb := hball (c • a) hsmall
  rw [show φ (c • a) = c • φ a from φ.toAlgHom.toLinearMap.map_smul _ _] at hb
  exact (N.toStarSubalgebra.toSubalgebra.toSubmodule.smul_mem_iff hc).mp hb

theorem boundedWeakNormal_surjective_unitBall
    (M : VonNeumannAlgebra H) (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hfaith : Function.Injective φ) (hφ : BoundedWeakNormal M φ)
    (T : K →L[ℂ] K) (hT : T ∈ generatedVonNeumannAlgebra φ.range) (hnT : ‖T‖ ≤ 1) :
    ∃ a : Algebra M, ‖a‖ ≤ 1 ∧ φ a = T := by
  classical
  have hcomm : T ∈ Set.centralizer (Set.centralizer (φ.range : Set (K →L[ℂ] K))) := by
    change T ∈ (generatedVonNeumannAlgebra φ.range : Set (K →L[ℂ] K)) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  obtain ⟨c, hc, hlim⟩ := publishedKaplanskyDensity.exists_weak_contraction_net
    φ.range T hcomm hnT
  choose a ha using fun d => (c d).property
  have ha' (d : Finset K × ℕ) : φ (a d) = (c d).val := ha d
  have hn (d : Finset K × ℕ) : ‖a d‖ ≤ 1 := by
    rw [← NonUnitalStarAlgHom.norm_map φ hfaith]
    rw [ha' d]
    exact hc d
  let ω : Ultrafilter (Finset K × ℕ) := Ultrafilter.of atTop
  obtain ⟨b, hb, hweak⟩ := exists_weak_operator_ultralimit ω
    (fun d => (a d).val) 1 zero_le_one hn
  let a₀ : Algebra M := ⟨b, weak_operator_limit_mem M a b hweak⟩
  refine ⟨a₀, hb, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have h₁ := hφ a a₀ 1 (Eventually.of_forall hn) hweak x y
  have h₂ : Tendsto (fun d => inner ℂ y (φ (a d) x)) (ω : Filter (Finset K × ℕ))
      (𝓝 (inner ℂ y (T x))) := by
    simpa only [ha'] using (hlim x y).mono_left (Ultrafilter.of_le atTop)
  exact tendsto_nhds_unique h₁ h₂

theorem boundedWeakNormal_surjective_generated
    (M : VonNeumannAlgebra H) (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hfaith : Function.Injective φ) (hφ : BoundedWeakNormal M φ)
    (T : K →L[ℂ] K) (hT : T ∈ generatedVonNeumannAlgebra φ.range) :
    ∃ a : Algebra M, φ a = T := by
  by_cases hzero : T = 0
  · exact ⟨0, by rw [map_zero, hzero]⟩
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  obtain ⟨a, _, ha⟩ := boundedWeakNormal_surjective_unitBall M φ hfaith hφ
    ((‖T‖ : ℂ)⁻¹ • T) ((generatedVonNeumannAlgebra φ.range).toStarSubalgebra.smul_mem hT _) hsmall
  refine ⟨(‖T‖ : ℂ) • a, ?_⟩
  rw [show φ ((‖T‖ : ℂ) • a) = (‖T‖ : ℂ) • φ a from
    φ.toAlgHom.toLinearMap.map_smul _ _]
  rw [ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

/-- A faithful representation continuous on bounded weak nets identifies
the original algebra with its generated von Neumann algebra. -/
def boundedWeakNormalEquiv
    (M : VonNeumannAlgebra H) (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hfaith : Function.Injective φ) (hφ : BoundedWeakNormal M φ) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (generatedVonNeumannAlgebra φ.range) := by
  let ψ : Algebra M →⋆ₐ[ℂ] Algebra (generatedVonNeumannAlgebra φ.range) :=
    φ.codRestrict (generatedVonNeumannAlgebra φ.range).toStarSubalgebra
      (fun a => subset_generatedVonNeumannAlgebra φ.range ⟨a, rfl⟩)
  apply StarAlgEquiv.ofBijective ψ
  constructor
  · intro a b h
    exact hfaith (congrArg Subtype.val h)
  · intro b
    obtain ⟨a, ha⟩ := boundedWeakNormal_surjective_generated M φ hfaith hφ b.val b.property
    exact ⟨a, Subtype.ext ha⟩

def vonNeumannAlgebraEquivOfEq {N P : VonNeumannAlgebra K} (h : N = P) :
    Algebra N ≃⋆ₐ[ℂ] Algebra P := by
  subst P
  exact StarAlgEquiv.refl ℂ (Algebra N)

end

end KadisonKastler

end OAI
