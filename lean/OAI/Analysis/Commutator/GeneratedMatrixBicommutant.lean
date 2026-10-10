import Mathlib
import OAI.Analysis.Commutator.EquivariantBicommutant
import OAI.Analysis.Commutator.MatrixStageGNSGeneration

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.GeneratedMatrixBicommutant

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] A)

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def stages : StarSubalgebra ℂ (H →L[ℂ] H) := ⨆ n,(φ.comp (stage n)).range

def algebra : VonNeumannAlgebra H := NormalGNS.bicommutant (stages size stage φ)

lemma stage_mem (n : ℕ) (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ) :
    φ (stage n a)∈algebra size stage φ :=
  NormalGNS.subset_bicommutant _ ((le_iSup (fun n => (φ.comp (stage n)).range) n) ⟨a,rfl⟩)

def stageHom (n : ℕ) : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] algebra size stage φ :=
  (φ.comp (stage n)).codRestrict (algebra size stage φ).toStarSubalgebra (stage_mem size stage φ n)

lemma representedStages_eq : NormalGNS.representedStages (algebra size stage φ)
    (fun n => Fin (size n+1)) (stageHom size stage φ)=stages size stage φ := by
  apply iSup_congr
  intro n
  rfl

lemma in_represented (a : algebra size stage φ) :
    (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (NormalGNS.representedStages (algebra size stage φ) (fun n => Fin (size n+1))
        (stageHom size stage φ) : Set (H →L[ℂ] H))) := by
  rw [representedStages_eq]
  exact (NormalGNS.mem_bicommutant _ _).mp a.property

lemma le_vonNeumann (N : VonNeumannAlgebra H)
    (hstage : ∀ n a,φ (stage n a)∈N) : algebra size stage φ≤N := by
  have hle : stages size stage φ≤N.toStarSubalgebra := by
    apply iSup_le
    intro n
    rintro a ⟨b,rfl⟩
    exact hstage n b
  intro a ha
  have hd := EquivariantBicommutant.bicommutant_mono hle ((NormalGNS.mem_bicommutant _ _).mp ha)
  change a∈N.carrier
  rw [←N.centralizer_centralizer']
  exact hd

lemma in_range (hφ : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ)
    (a : algebra size stage φ) : (a:H →L[ℂ] H)∈Set.range φ := by
  have hle : stages size stage φ≤φ.range := by
    apply iSup_le
    intro n
    rintro a ⟨b,rfl⟩
    exact ⟨stage n b,rfl⟩
  have hd := EquivariantBicommutant.bicommutant_mono hle ((NormalGNS.mem_bicommutant _ _).mp a.property)
  rw [show (φ.range : Set (H →L[ℂ] H))=Set.range φ from rfl,hφ] at hd
  exact hd

lemma factor (hφ : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ)
    (hinj : Function.Injective φ)
    (hirr : ∀ b : A,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
      stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ A c) :
    FactorCorner.IsFactor (algebra size stage φ) := by
  intro z hz hcentral
  obtain ⟨b,hb⟩ := in_range size stage φ hφ ⟨z,hz⟩
  change φ b=z at hb
  obtain ⟨c,hc⟩ := hirr b (by
    intro n a
    apply hinj
    simp only [map_mul,hb]
    exact hcentral _ (stage_mem size stage φ n a))
  refine ⟨c,?_⟩
  rw [←hb,hc,Algebra.algebraMap_eq_smul_one,map_smul,map_one]

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
