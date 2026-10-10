import Mathlib
import OAI.Analysis.FreeWords.CanonicalMatrixExtension
import OAI.Analysis.FreeWords.CoordinateConstantFree
import OAI.Analysis.FreeWords.MatrixExtendSize
import OAI.Analysis.FreeWords.NumericalModelDefinitions
import OAI.Analysis.FreeWords.UnitaryRangePreimage
import OAI.Analysis.FreeWords.VariableMatrixUltra

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKFactorSupport KKProjectionSupport KKMatrixQuantization

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem finite_numerical_model : FiniteNumericalModel (H := H) := by
  classical
  intro M τ hF hD n hn K F hFne hcenter ε hε
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨β,hβ,hτβ⟩ := exists_matrix_subfactor M τ hF hD n hn
  choose ρ hρ hβρ hτρ using (fun j : ℕ => matrix_extension_canonical M τ hF hD n (2^j)
    hn (by positivity) β)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le atTop
  have hf := matrix_ultra_factor n ρ (tracePositive τ) τ.normalized τ.tracial
    (gnsVector_injective τ) hρ ω hω
  have hd := matrix_ultra_diffuse n ρ hn (tracePositive τ) τ.normalized τ.tracial
    (gnsVector_injective τ) hρ hτρ ω hω
  let wf : List (ℤ × Matrix (Fin n) (Fin n) ℂ) → List (ℤ × ConcreteAlgebra M) :=
    List.map (fun z => (z.1,β z.2))
  have hnF : ∀ w∈F.image wf, w≠[] := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    exact fun he => hFne v hv (List.map_eq_nil_iff.mp he)
  have hcF : ∀ w∈F.image wf, ∀ z∈w, z.1≠0 ∧ (tracePositive τ) z.2=0 := by
    intro w hw z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    refine ⟨(hcenter v hv a ha).1,?_⟩
    change τ.map (β a.2)=0
    rw [matrixHom_trace β τ.map τ.normalized τ.tracial,(hcenter v hv a ha).2,mul_zero]
  have hmF : ∀ w∈F.image wf, ∀ z∈w, ∀j, z.2∈(ρ j).range := by
    intro w hw z hz j
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact ⟨matrixReindex finProdFinEquiv (Matrix.kronecker a.2 1),hβρ j a.2⟩
  obtain ⟨j,_,u,huR,huK,huF⟩ := coordinate_constant_free (fun j => (ρ j).range)
    (tracePositive τ) τ.normalized τ.tracial ω hω hf hd K (F.image wf) hnF hcF hmF ε hε 0
  let d := 2^j
  have hdpos : 0<d := by dsimp only [d]; positivity
  have : NeZero d := ⟨hdpos.ne'⟩
  let e : Fin n × Fin d ≃ Fin (n*d) := finProdFinEquiv
  let φ := (ρ j).comp (matrixReindex e)
  have hφ : Function.Injective φ := (hρ j).comp (Matrix.reindexAlgEquiv ℂ ℂ e).injective
  have hφR : φ.range=(ρ j).range := by
    exact matrixReindex_comp_range e.symm (ρ j)
  have huφ : u.val∈φ.range := by rwa [hφR]
  obtain ⟨U,hU⟩ := unitary_range_preimage φ hφ u huφ
  have hφB (a : Matrix (Fin n) (Fin n) ℂ) : φ (Matrix.kronecker a 1)=β a := hβρ j a
  have hφτ (a) : τ.map (φ a)=((n*d:ℕ):ℂ)⁻¹*Matrix.trace a := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using
      matrixHom_trace φ τ.map τ.normalized τ.tracial a
  refine ⟨d,hdpos,U,?_,?_⟩
  · intro k hk hk0
    rw [← hφτ,unitary_preimage_zpow φ U u hU]
    exact huK k hk hk0
  · intro w hw
    have hh := huF (wf w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    rw [← hφτ]
    have he : φ ((w.map (fun z => (U^z.1).val*Matrix.kronecker z.2 1)).prod)=
        ((wf w).map (fun z => (u^z.1).val*z.2)).prod := by
      simp only [map_list_prod,List.map_map,Function.comp_def,map_mul,hφB,
        unitary_preimage_zpow φ U u hU,wf]
    rw [he]
    exact hh

end

end KKVariableUltra
end

end OAI
