import Mathlib
import OAI.Analysis.FreeWords.AmplifiedBlockBounds
import OAI.Analysis.FreeWords.AsymptoticBlockTransport
import OAI.Analysis.FreeWords.FiniteFreeDefinitions
import OAI.Analysis.FreeWords.MatrixExpectationContinuous
import OAI.Analysis.FreeWords.TransportTestsDefinitions

namespace OAI

noncomputable section

namespace KKFiniteTransport

noncomputable section

open KKTraceTransfer KKFreeLiftFrontier KKMatrixExpectation KKHaarEndpoints KKMatrixBounds

open KKAsymptoticTransport Filter

open scoped Matrix.Norms.Operator Topology ComplexOrder

variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M:VonNeumannAlgebra H}

local instance concreteOrder (M:VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) :=
  CStarAlgebra.spectralOrder _

local instance concreteLE (M:VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance concretePreorder (M:VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance concreteSOR (M:VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem expectation_tendsto_zero_any (I:Type*) (L:Filter I) (τ:FaithfulNormalTrace M) (n:ℕ)
    (X:I → MatrixAlgebra n M)
    (h:∀a b,Tendsto (fun j => τ.map (X j a b)) L (𝓝 0)) :
    Tendsto (fun j => matrixExpectation τ.map n (X j)) L (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  simpa only [matrixExpectation_apply,Pi.zero_apply,Matrix.zero_apply,map_zero,Function.comp_def] using
    ((continuous_algebraMap ℂ (ConcreteAlgebra M)).tendsto 0).comp (h a b)

theorem block_bound (τ:FaithfulNormalTrace M) (n:ℕ) {I:Type*}
    (U:I → unitary (MatrixAlgebra n M)) (b:Block τ n) : NetBound (fun j => blockValue (U j) b) := by
  refine ⟨wordBound n b.val.1*(n:ℝ),mul_nonneg (wordBound_nonneg _ _) (Nat.cast_nonneg _),?_⟩
  intro j
  exact (norm_mul_le _ _).trans (mul_le_mul (powerWord_norm_le n (U j) b.val.1)
    (unitary_rowSum_norm_le ((U j)^b.val.2)) (norm_nonneg _) (wordBound_nonneg _ _))

def joinBlock (τ:FaithfulNormalTrace M) {n:ℕ} (c d:Block τ n) (x:MatrixAlgebra n M)
    (hx:matrixTraceMap τ.map n x=0) : Block τ n :=
  ⟨(c.val.1++(c.val.2,matrixExpectation τ.map n x)::d.val.1,d.val.2),by
    refine ⟨?_,d.property.2⟩
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact c.property.1 z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨c.property.2,matrixExpectation_range τ.map n x,by
          rw [matrixExpectation_trace τ.map τ.normalized n]; exact hx⟩
      · exact d.property.1 z hz⟩

theorem blockValue_join (τ:FaithfulNormalTrace M) {n:ℕ} (U:unitary (MatrixAlgebra n M))
    (c d:Block τ n) (x:MatrixAlgebra n M) (hx:matrixTraceMap τ.map n x=0) :
    blockValue U (joinBlock τ c d x hx)=blockValue U c*matrixExpectation τ.map n x*blockValue U d := by
  simp only [blockValue,joinBlock,powerWord_append,powerWord_cons]
  simp only [mul_assoc]

theorem lift_relWord (τ:FaithfulNormalTrace M) {n:ℕ} {I:Type*}
    (U:I → unitary (MatrixAlgebra n M)) (w:List ((I → MatrixAlgebra n M)×MatrixAlgebra n M))
    (hw:∀z∈w,z.1∈Set.range (fun b:Block τ n => fun j => blockValue (U j) b) ∧
      matrixExpectation τ.map n z.2=0) :
    ∃v:RelWord τ n,w=v.map (fun z => ((fun j => blockValue (U j) z.1),z.2.val)) := by
  induction w with
  | nil => exact ⟨[],rfl⟩
  | cons z w ih =>
    obtain ⟨b,hb⟩ := (hw z List.mem_cons_self).1
    obtain ⟨v,hv⟩ := ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))
    refine ⟨(b,⟨z.2,(hw z List.mem_cons_self).2⟩)::v,?_⟩
    simp only [List.map_cons]
    rw [← hv]
    congr 1
    exact Prod.ext hb.symm rfl

theorem transport_limits (τ:FaithfulNormalTrace M) {n:ℕ} {I:Type*} (L:Filter I)
    (U:I → unitary (MatrixAlgebra n M))
    (ht:∀t:TransportTest τ n,Tendsto (fun j => testValue τ t (U j)) L (𝓝 0))
    (w:List (ℤ×MatrixAlgebra n M)) (hw:IsCenteredTest τ w) :
    Tendsto (fun j => matrixExpectation τ.map n (powerWord (U j) w)) L (𝓝 0) := by
  let E := matrixExpectationCLM τ n
  let S := Set.range (fun b:Block τ n => fun j => blockValue (U j) b)
  let T:Set (MatrixAlgebra n M) := {x | matrixTraceMap τ.map n x=0}
  have hz : ∀c∈S,Tendsto (fun j => E (c j)) L (𝓝 0) := by
    rintro c ⟨b,rfl⟩
    exact expectation_tendsto_zero_any I L τ n _ (fun a b' => ht (.block b a b'))
  have hj : ∀c∈S,∀d∈S,∀x∈T,(fun j => c j*E x*d j)∈S := by
    rintro c ⟨b,rfl⟩ d ⟨b',rfl⟩ x hx
    exact ⟨joinBlock τ b b' x hx,funext (fun j => blockValue_join τ (U j) b b' x hx)⟩
  have hr : RelativeBlockLimits L E S := by
    intro v hv
    obtain ⟨v',rfl⟩ := lift_relWord τ U v hv
    have he (j:I) : netPair (centeredWord E
        (v'.map fun z => ((fun j => blockValue (U j) z.1),z.2.val))) j=
        transportPair τ (U j) v' := by
      simp only [netPair,centeredWord,List.map_map,Function.comp_def,centerNet,transportPair,
        blockCenter,E]
      rfl
    refine ⟨?_,?_⟩
    · intro hn
      have hn' : v'≠[] := by intro h; subst v'; simp at hn
      simp only [he]
      exact expectation_tendsto_zero_any I L τ n _ (fun a b => ht (.cyclic v' hn' a b))
    · rintro c ⟨b,rfl⟩
      simp only [he]
      exact expectation_tendsto_zero_any I L τ n _ (fun a b' => ht (.endpoint v' b a b'))
  let pure (k:ℤ) (hk:k≠0) : Block τ n := ⟨([],k),⟨by simp [CenteredPowerWord],hk⟩⟩
  let v : List ((I → MatrixAlgebra n M)×MatrixAlgebra n M) :=
    w.map fun z => ((fun j => ((U j)^z.1).val),z.2)
  have hv : ∀z∈v,z.1∈S ∧ z.2∈T := by
    intro z hzv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hzv
    refine ⟨⟨pure a.1 (hw.2 a ha).1,?_⟩,(hw.2 a ha).2⟩
    funext j
    simp [blockValue,pure,powerWord]
  have hn : v≠[] := by simpa [v] using hw.1
  have hh := asymptotic_block_transport L E S T (matrixExpectation_idem τ n)
    (matrixExpectationCLM_right τ n) (by rintro c ⟨b,rfl⟩; exact block_bound τ n U b)
    hz hj hr v hn hv
  change Tendsto (fun j => matrixExpectation τ.map n (netPair v j)) L (𝓝 0) at hh
  have he (j:I) : netPair v j=powerWord (U j) w := by
    simp only [v,netPair,powerWord,List.map_map,Function.comp_def]
  convert hh using 1
  · exact funext (fun j => congrArg (matrixExpectation τ.map n) (he j).symm)
  · rfl

end

end KKFiniteTransport
end

end OAI
