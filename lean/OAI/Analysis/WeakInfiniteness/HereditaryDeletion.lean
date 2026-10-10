import Mathlib
import OAI.Analysis.WeakInfiniteness.NonunitalSpectralTools2

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped BigOperators Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem exists_hereditary_continuous_deletion
    (D : NonUnitalStarSubalgebra ℂ A) (hD : IsClosed (D : Set A))
    (U V : A) (hUD : U ∈ D) (hVD : V ∈ D)
    (hU : IsSelfAdjoint U) (hV : IsSelfAdjoint V) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ H ∈ D,IsSelfAdjoint H ∧ ∃ n : ℕ,∃ e : Fin n → Unitization ℂ A,
      (∀ i,IsSelfAdjoint (e i)) ∧ (∑ i,e i=1) ∧
      (∀ i,e i*(H : Unitization ℂ A)*e i=0) ∧
      ∀ (p q : A) (S T : Set ℝ),
        ContinuouslySupported (U : Unitization ℂ A) (p : Unitization ℂ A) S →
        ContinuouslySupported (U : Unitization ℂ A) (q : Unitization ℂ A) T →
        (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) → p*H*q=p*V*q := by
  classical
  let u : Unitization ℂ A := U
  let v : Unitization ℂ A := V
  let E := unitizationSubalgebra D
  let : IsClosed (E : Set (Unitization ℂ A)) := unitizationSubalgebra_closed D hD
  have hu : IsSelfAdjoint u := hU.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hv : IsSelfAdjoint v := hV.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let δ : ℝ := ρ/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n,c,f,hf,hfs,_⟩ := exists_small_partition (spectrum ℝ u)
    (ContinuousFunctionalCalculus.isCompact_spectrum u) hδ
  let e : Fin n → Unitization ℂ A := fun i => cfc (f i) u
  let R : Fin n → Fin n → Prop := fun j k => 4*δ < dist (c j) (c k)
  let H := finiteDeletion e v R
  have heD : ∀ i,e i ∈ E := fun i => cfc_mem (f i) (unitizationSubalgebra_inr_mem D hUD)
  have hHD : H ∈ E := by
    apply E.sum_mem
    intro j _
    apply E.sum_mem
    intro k _
    split_ifs
    · exact E.mul_mem (E.mul_mem (heD j) hVD) (heD k)
    · exact E.zero_mem
  have hH0 : H.fst=0 := by
    change (Unitization.fstHom ℂ A) H=0
    simp only [H,finiteDeletion,map_sum,apply_ite,map_mul,map_zero]
    simp [v]
  have hHe : (H.snd : Unitization ℂ A)=H := unitization_inr_snd_of_fst_eq_zero hH0
  have hesa : ∀ i,IsSelfAdjoint (e i) := fun i => cfc_predicate (f i) u
  have hHsa : IsSelfAdjoint H := finiteDeletion_selfAdjoint e v R hesa hv (fun j k => by
    dsimp [R]; rw [dist_comm])
  have hdiag : ∀ i,e i*H*e i=0 := by
    apply finiteDeletion_diagonals e v R e
    intro l j k hjk
    dsimp only [R] at hjk
    by_cases hlj : 2*δ ≤ dist (c l) (c j)
    · exact Or.inl (cfc_mul_eq_zero_of_small_supports u (f l) (f j)
        (c l) (c j) δ (hf l) (hf j) hlj)
    · right
      apply cfc_mul_eq_zero_of_small_supports u (f k) (f l)
        (c k) (c l) δ (hf k) (hf l)
      have ht := dist_triangle (c j) (c l) (c k)
      rw [dist_comm (c j) (c l),dist_comm (c l) (c k)] at ht
      have hh := lt_of_not_ge hlj
      linarith
  refine ⟨H.snd,hHD,?_,n,e,hesa,cfc_partition_sum u hu f hfs,?_,?_⟩
  · have := congrArg (fun z : Unitization ℂ A => z.snd) hHsa.star_eq
    exact this
  · simpa only [hHe] using hdiag
  · intro p q S T hp hq hsep
    apply Unitization.inr_injective (R := ℂ)
    simp only [Unitization.inr_mul]
    rw [hHe]
    apply finiteDeletion_preserves_corner e v _ _ R (cfc_partition_sum u hu f hfs)
    intro j k hjk
    have hs : ∀ x ∈ S,∀ y ∈ T,8*δ ≤ dist x y := by
      have heq : 8*δ=ρ := by dsimp [δ]; ring
      simpa only [heq] using hsep
    rcases vanishes_on_separated_sets (f j) (f k) (c j) (c k) δ
      (hf j) (hf k) S T hs hjk with hj | hk
    · exact Or.inl (hp (f j) hj).1
    · exact Or.inr (hq (f k) hk).2

end

end WeakPureInfiniteness
end

end OAI
