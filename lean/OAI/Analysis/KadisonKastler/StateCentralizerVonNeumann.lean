import OAI.Analysis.KadisonKastler.TomitaCentralizerGraph
import OAI.Analysis.KadisonKastler.ProductStateCentralizer
import OAI.Analysis.KadisonKastler.ProductMatrixStages
import OAI.Analysis.FactorGeneration.Bicommutant
import OAI.Analysis.FactorGeneration.GroupTrace

namespace OAI

/-! # The exact vector-state centralizer as a von Neumann algebra

Strong approximation preserves its defining matrix-coefficient identities.
The reference vector restricts to a faithful trace. For the fixed product
construction, finite-site swaps make this centralizer a factor.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def stateCentralizerAlgebra (ξ : H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {a | a ∈ M ∧ ProductStateCentralizes M ξ a}
  zero_mem' := ⟨M.zero_mem,by intro b hb; simp [productVectorState]⟩
  one_mem' := ⟨M.one_mem,by intro b hb; simp only [one_mul,mul_one]⟩
  add_mem' := by
    rintro a b ⟨ha,hac⟩ ⟨hb,hbc⟩
    refine ⟨M.add_mem ha hb,?_⟩
    intro c hc
    simpa only [add_mul,mul_add,productVectorState,add_apply,inner_add_right] using
      congrArg₂ (·+·) (hac c hc) (hbc c hc)
  mul_mem' := by
    rintro a b ⟨ha,hac⟩ ⟨hb,hbc⟩
    refine ⟨M.mul_mem ha hb,?_⟩
    intro c hc
    calc
      _ = productVectorState ξ (a*(b*c)) := by rw [mul_assoc]
      _ = productVectorState ξ ((b*c)*a) := hac _ (M.mul_mem hb hc)
      _ = productVectorState ξ (b*(c*a)) := by rw [mul_assoc]
      _ = productVectorState ξ ((c*a)*b) := hbc _ (M.mul_mem hc ha)
      _ = _ := by rw [mul_assoc]
  algebraMap_mem' z := by
    refine ⟨M.algebraMap_mem z,?_⟩
    intro a ha
    simp only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  star_mem' := by
    rintro a ⟨ha,hac⟩
    refine ⟨M.toStarSubalgebra.star_mem' ha,?_⟩
    intro b hb
    exact vectorState_centralizer_star ξ (⟨a,ha⟩ : Algebra M)
      (fun c => hac c.val c.property) (⟨b,hb⟩ : Algebra M)

theorem stateCentralizerAlgebra_bicommutant (ξ : H) :
    Set.centralizer (Set.centralizer (stateCentralizerAlgebra (M := M) ξ :
      Set (H →L[ℂ] H)))=stateCentralizerAlgebra (M := M) ξ := by
  classical
  apply Set.Subset.antisymm
  · intro T hT
    have hTM : T ∈ M := by
      rw [← SetLike.mem_coe,← M.centralizer_centralizer]
      intro R hR
      exact hT R (fun a ha => hR a ha.1)
    refine ⟨hTM,?_⟩
    intro b hb
    obtain ⟨a,ha⟩ := bicommutant_exists_strong_net (stateCentralizerAlgebra (M := M) ξ) T hT
    have hl : Tendsto (fun i => inner ℂ ξ ((a i).val (b ξ))) atTop
        (𝓝 (inner ℂ ξ (T (b ξ)))) := tendsto_const_nhds.inner (ha (b ξ))
    have hr : Tendsto (fun i => inner ℂ ξ (b ((a i).val ξ))) atTop
        (𝓝 (inner ℂ ξ (b (T ξ)))) :=
      tendsto_const_nhds.inner ((b.continuous.tendsto (T ξ)).comp (ha ξ))
    apply tendsto_nhds_unique hl
    exact hr.congr' (Eventually.of_forall (fun i => ((a i).property.2 b hb).symm))
  · intro T hT R hR
    exact (hR T hT).symm

def stateCentralizerVonNeumann (ξ : H) : VonNeumannAlgebra H where
  toStarSubalgebra := stateCentralizerAlgebra (M := M) ξ
  centralizer_centralizer' := stateCentralizerAlgebra_bicommutant ξ

theorem stateCentralizerVonNeumann_le (ξ : H) : stateCentralizerVonNeumann (M := M) ξ ≤ M :=
  fun _ h => h.1

def stateCentralizerTrace (ξ : H) (hunit : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ)) :
    TracialRepresentation (stateCentralizerVonNeumann (M := M) ξ) where
  vector := ξ
  norm_vector := hunit
  cyclic a b := a.property.2 b.val b.property.1
  separating a ha := by
    apply Subtype.ext
    have he := hsep (a₁ := (⟨a.val,a.property.1⟩ : Algebra M)) (a₂ := 0)
      (by change a.val ξ=(0 : H →L[ℂ] H) ξ; simpa using ha)
    exact congrArg (fun b : Algebra M => b.val) he

theorem ProductMatrixStages.stateCentralizer_scalarCenter (P : ProductMatrixStages (H := H)) :
    ScalarCenter (stateCentralizerVonNeumann (M := P.algebra) P.vector) := by
  intro a ha hc
  refine ⟨productVectorState P.vector a,?_⟩
  apply P.state_centralizer_irreducible a ha.1
  intro u hu huc
  exact hc u.val ⟨hu,huc⟩

end

end KadisonKastler

end OAI
