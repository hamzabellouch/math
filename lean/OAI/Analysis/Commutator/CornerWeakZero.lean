import Mathlib
import OAI.Analysis.Commutator.CornerAlphabetGNS
import OAI.Analysis.Commutator.StageGeneration
import OAI.Analysis.Commutator.WeakZeroSelection

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

open Filter Topology

open scoped Matrix.Norms.L2Operator

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
  (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
  (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)
  (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
  (hgen : ∀ a : A, τ.gnsStarAlgHom a ∈ Set.centralizer (Set.centralizer
    (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS))))

include e he hgen in
omit [∀ n, Nonempty (I n)] in
lemma separableGNS_of_stages : TopologicalSpace.SeparableSpace τ.GNS := by
  apply (dense_stages_of_bicommutant_generation τ I φ e he hgen).isSeparable_iff.mp
  apply TopologicalSpace.IsSeparable.iUnion
  intro n
  let : ProperSpace (Matrix (I n) (I n) ℂ) := FiniteDimensional.proper ℂ _
  exact TopologicalSpace.isSeparable_range (stageVector τ (φ n)).continuous_of_finiteDimensional

include hτ h1 e he hsize in
lemma corner_arbitrarily_large_alphabet (n : ℕ) (p : Matrix (I n) (I n) ℂ)
    (hp : IsStarProjection p) (α : ℝ) (hα : 0<α) (hατ : τ (φ n p)=(α:ℂ)) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∃ x : Fin m → A,
      Orthonormal ℂ (fun i => algebraVector τ (x i)) ∧
      ∀ i, τ (x i)=0 ∧ x i*φ n p=x i ∧ star (x i)*x i=((α:ℂ)⁻¹) • φ n p ∧
        ‖x i‖≤(Real.sqrt α)⁻¹ := by
  obtain ⟨q,hq⟩ := exists_nat_ge ((N+1:ℝ)/α)
  obtain ⟨k,hk,hqk⟩ := hsize n q
  have hN : (N+1:ℝ)≤α*Fintype.card (I k) := by
    rw [mul_comm]
    exact (div_le_iff₀ hα).mp (hq.trans (by exact_mod_cast hqk))
  have htrace : τ (φ k (e hk p))=(α:ℂ) := by rw [he]; exact hατ
  obtain ⟨m,hm,x,hx,hprop⟩ := MatrixCorners.exists_normalized_corner_alphabet τ hτ h1
    (φ k) (e hk p) (hp.map (e hk)) α hα htrace N hN
  exact ⟨m,hm,x,hx,by simpa only [he] using hprop⟩

include hτ h1 e he hsize hgen in
theorem exists_corner_weak_zero (n : ℕ) (p : Matrix (I n) (I n) ℂ)
    (hp : IsStarProjection p) (α : ℝ) (hα : 0<α) (hατ : τ (φ n p)=(α:ℂ)) :
    ∃ x : ℕ → A, (∀ k, τ (x k)=0 ∧ x k*φ n p=x k ∧
      star (x k)*x k=((α:ℂ)⁻¹) • φ n p ∧ ‖x k‖≤(Real.sqrt α)⁻¹ ∧
      ‖τ.toPreGNS (x k)‖=1 ∧ ‖τ.toPreGNS (star (x k))‖=1) ∧
      ∀ a : A, Tendsto (fun k => τ (x k*a)) atTop (𝓝 0) := by
  classical
  let P : Set τ.GNS := {v | ∃ x : A, algebraVector τ x=v ∧ τ x=0 ∧
    x*φ n p=x ∧ star x*x=((α:ℂ)⁻¹) • φ n p ∧ ‖x‖≤(Real.sqrt α)⁻¹}
  have hlarge : ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ v : Fin m → τ.GNS,
      Orthonormal ℂ v ∧ ∀ i, v i∈P := by
    intro N
    obtain ⟨m,hm,x,hx,hprop⟩ := corner_arbitrarily_large_alphabet τ hτ h1 I φ e he hsize n p hp α hα hατ N
    exact ⟨m,hm,fun i => algebraVector τ (x i),hx,fun i => ⟨x i,rfl,hprop i⟩⟩
  let : TopologicalSpace.SeparableSpace τ.GNS := separableGNS_of_stages τ I φ e he hgen
  obtain ⟨v,hv,hvn,hvweak⟩ := Kadison.exists_weak_zero_sequence P (TopologicalSpace.denseSeq τ.GNS)
    (TopologicalSpace.denseRange_denseSeq _) hlarge
  choose x hx hprop using hv
  refine ⟨x,?_,?_⟩
  · intro k
    have hn : ‖τ.toPreGNS (x k)‖=1 := by
      have h := hvn k
      rw [←hx k,algebraVector_apply,UniformSpace.Completion.norm_coe] at h
      exact h
    exact ⟨(hprop k).1,(hprop k).2.1,(hprop k).2.2.1,(hprop k).2.2.2,hn,
      (norm_star_preGNS τ hτ (x k)).trans hn⟩
  · intro a
    have ht := (hvweak (algebraVector τ (star a))).star
    convert ht using 1
    · funext k
      rw [←hx k,←inner_conj_symm,inner_algebraVector,star_star,hτ]
      simp
    · simp

end Kadison.TracialGNS

end

end
end

end OAI
