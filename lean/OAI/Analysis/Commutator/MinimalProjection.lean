import Mathlib
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.ProjectionCommutant

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vonNeumannCentralizer (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ s
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (↑(StarSubalgebra.centralizer ℂ s) : Set (H →L[ℂ] H))) = (↑(StarSubalgebra.centralizer ℂ s) : Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer,Set.centralizer_centralizer_centralizer]

namespace AtomicFactor

def IsMinimalProjection (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  p∈M ∧ IsStarProjection p ∧ p≠0 ∧
    ∀ q∈M,IsStarProjection q → q≤p → q=0 ∨ q=p

lemma exists_minimal_of_not_diffuse (M : VonNeumannAlgebra H)
    (h : ¬DiffuseProjection.HasNoMinimalProjections M) :
    ∃ p,IsMinimalProjection M p := by
  simp only [DiffuseProjection.HasNoMinimalProjections,not_forall] at h
  obtain ⟨p,hpM,hp,hpn,h⟩ := h
  refine ⟨p,hpM,hp,hpn,?_⟩
  intro q hqM hq hqp
  by_cases hq0 : q=0
  · exact Or.inl hq0
  · right
    by_contra hqne
    exact h ⟨q,hqM,hq,hq0,hqne,hqp⟩

lemma selfadjoint_corner_scalar (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsMinimalProjection M p) {a : H →L[ℂ] H} (haM : a∈M)
    (ha : IsSelfAdjoint a) (hpa : p*a=a) (hap : a*p=a) :
    ∃ z : ℂ,a=z • p := by
  let N := vonNeumannIntersection M (vonNeumannCentralizer {p})
  have haN : a∈N := by
    refine ⟨haM,?_⟩
    change a∈((StarSubalgebra.centralizer ℂ {p} : StarSubalgebra ℂ (H →L[ℂ] H)) : Set _)
    rw [StarSubalgebra.coe_centralizer]
    intro q hq
    rcases hq with hq|hq
    · have he : q=p := Set.mem_singleton_iff.mp hq
      subst q
      exact hpa.trans hap.symm
    · have he : q=star p := by simpa only [Set.star_singleton,Set.mem_singleton_iff] using hq
      rw [he,hp.2.1.isSelfAdjoint.star_eq]
      exact hpa.trans hap.symm
  let K : Submodule ℂ (H →L[ℂ] H) := Submodule.span ℂ {p}
  have hc : IsClosed (K : Set (H →L[ℂ] H)) := K.closed_of_finiteDimensional
  have haK : a∈K := by
    apply hc.closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n,q,c,hq,_,he⟩ := Polar.exists_selfadjoint_spectral_sum N haN ha hε
    have hpq (i : Fin n) : p*q i=q i*p := by
      have hh := (hq i).1
      change q i∈M ∧ q i∈vonNeumannCentralizer {p} at hh
      have hh' := hh.2
      change q i∈((StarSubalgebra.centralizer ℂ {p} : StarSubalgebra ℂ (H →L[ℂ] H)) : Set _) at hh'
      rw [StarSubalgebra.coe_centralizer] at hh'
      exact hh' p (Or.inl (Set.mem_singleton p))
    have hmem (i : Fin n) : p*q i∈K := by
      have hproj : IsStarProjection (p*q i) := hp.2.1.mul (hq i).2 (hpq i)
      have hle : p*q i≤p := by
        apply (hproj.le_iff_mul_eq_right hp.2.1).mpr
        rw [←mul_assoc,hp.2.1.isIdempotentElem.eq]
      rcases hp.2.2.2 (p*q i) (M.mul_mem hp.1 (hq i).1.1) hproj hle with hz|hz
      · rw [hz]; exact K.zero_mem
      · rw [hz]; exact Submodule.subset_span (Set.mem_singleton p)
    refine ⟨p*(∑ i,c i • q i),?_,?_⟩
    · rw [Finset.mul_sum]
      apply K.sum_mem
      intro i _
      rw [mul_smul_comm]
      exact K.smul_mem (c i : ℂ) (hmem i)
    · rw [dist_eq_norm,←hpa,←mul_sub]
      have hnorm : ‖p‖≤1 := hp.2.1.norm_le
      exact (norm_mul_le _ _).trans_lt ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_lt
        (by simpa only [one_mul] using he))
  obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp haK
  exact ⟨z,hz.symm⟩

end AtomicFactor

end Kadison

end

end
end

end OAI
