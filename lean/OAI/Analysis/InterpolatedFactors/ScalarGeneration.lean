import OAI.Analysis.InterpolatedFactors.GaussianAlgebra

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.FreeFock

section
open scoped ENNReal
variable {α : Type u_1} [DecidableEq α]

 def appendEmbedding (b : α) : List α ↪ List α :=
  ⟨fun w => w++[b],fun _ _ h => List.append_cancel_right h⟩

 def rightCreation (b : α) : Operator α :=
  (hilbertEmbedding (appendEmbedding b)).toContinuousLinearMap

@[simp] theorem rightCreation_single (b : α) (w : List α) (z : ℂ) :
    rightCreation b (lp.single 2 w z)=lp.single 2 (w++[b]) z :=
  hilbertEmbedding_single (appendEmbedding b) w z

 theorem creation_rightCreation (a b : α) :
    creation a*rightCreation b=rightCreation b*creation a := by
  apply operator_basis_ext (α := List α)
  intro w
  simp only [mul_apply_eq_comp,creation_single,rightCreation_single,List.cons_append]

 def vacuumProjection : Operator α := InnerProductSpace.rankOne ℂ vacuum vacuum

@[simp] theorem vacuumProjection_nil (z : ℂ) :
    vacuumProjection (lp.single 2 ([] : List α) z)=lp.single 2 [] z := by
  classical
  ext w
  simp [vacuumProjection,InnerProductSpace.rankOne_apply,vacuum,lp.inner_single_left,
    lp.single_apply,Pi.single_apply]

@[simp] theorem vacuumProjection_cons (a : α) (w : List α) (z : ℂ) :
    vacuumProjection (lp.single 2 (a::w) z)=0 := by
  simp [vacuumProjection,InnerProductSpace.rankOne_apply,vacuum,lp.inner_single_left,lp.single_apply]

 theorem annihilation_rightCreation (a b : α) :
    star (creation a)*rightCreation b=
      rightCreation b*star (creation a)+(if a=b then vacuumProjection else 0) := by
  apply operator_basis_ext (α := List α)
  intro w
  cases w with
  | nil =>
    simp only [mul_apply_eq_comp,add_apply,rightCreation_single,
      List.nil_append,annihilation_single_cons,annihilation_single_nil,map_zero,zero_add]
    by_cases h : a=b <;> simp [h]
  | cons c w =>
    simp only [mul_apply_eq_comp,add_apply,rightCreation_single,
      List.cons_append,annihilation_single_cons]
    have hp : (if a=b then (vacuumProjection : Operator α) else 0) (lp.single 2 (c::w) 1)=0 := by
      split_ifs <;> simp
    rw [hp,add_zero]
    by_cases h : a=c
    · rw [ite_eq_left h,ite_eq_left h,rightCreation_single]
    · rw [ite_eq_right h,ite_eq_right h,map_zero]

 theorem vacuumProjection_selfAdjoint : star (vacuumProjection (α := α))=vacuumProjection := by
  simp [vacuumProjection,ContinuousLinearMap.star_eq_adjoint]

 theorem creation_rightAnnihilation (a b : α) :
    creation a*star (rightCreation b)=
      star (rightCreation b)*creation a-(if a=b then vacuumProjection else 0) := by
  have h := congrArg star (annihilation_rightCreation a b)
  simp only [star_mul,star_star,star_add (R := Operator α)] at h
  have he : star (if a=b then (vacuumProjection : Operator α) else 0)=
      if a=b then vacuumProjection else 0 := by
    split_ifs <;> simp [vacuumProjection_selfAdjoint,star_zero (R := Operator α)]
  rw [he] at h
  exact eq_sub_of_add_eq h.symm

 def rightSemicircular (a : α) : Operator α := rightCreation a+star (rightCreation a)

 theorem semicircular_rightSemicircular (a b : α) :
    Commute (semicircular a) (rightSemicircular b) := by
  have hc := creation_rightCreation a b
  have ha := congrArg star hc
  simp only [star_mul] at ha
  have hL := annihilation_rightCreation a b
  have hR := creation_rightAnnihilation a b
  change (creation a+star (creation a))*(rightCreation b+star (rightCreation b))=
    (rightCreation b+star (rightCreation b))*(creation a+star (creation a))
  noncomm_ring [hc,ha,hL,hR]

end
section
open scoped ENNReal ComplexConjugate
variable {α : Type u_2} [DecidableEq α]

 def reverseEmbedding : List α ↪ List α := ⟨List.reverse,List.reverse_injective⟩
 def reverseIsometry : Fock α →ₗᵢ[ℂ] Fock α := hilbertEmbedding reverseEmbedding
 def reverseOperator : Operator α := reverseIsometry.toContinuousLinearMap

@[simp] theorem reverseOperator_single (w : List α) (z : ℂ) :
    reverseOperator (lp.single 2 w z)=lp.single 2 w.reverse z :=
  hilbertEmbedding_single reverseEmbedding w z

 theorem reverseOperator_square : (reverseOperator : Operator α)*reverseOperator=1 := by
  apply operator_basis_ext (α := List α)
  intro w
  simp only [mul_apply_eq_comp,reverseOperator_single,List.reverse_reverse,one_apply_eq_self]

 theorem reverseOperator_involutive (ξ : Fock α) :
    reverseOperator (reverseOperator ξ)=ξ := by
  have hi := DFunLike.congr_fun (reverseOperator_square (α := α)) ξ
  exact hi

 def reverseEquiv : Fock α ≃ₗᵢ[ℂ] Fock α :=
  LinearIsometryEquiv.ofSurjective reverseIsometry (fun ξ =>
    ⟨reverseOperator ξ,reverseOperator_involutive ξ⟩)

@[simp] theorem reverseEquiv_apply (ξ : Fock α) : reverseEquiv ξ=reverseOperator ξ := rfl
@[simp] theorem reverseEquiv_symm_apply (ξ : Fock α) : reverseEquiv.symm ξ=reverseOperator ξ := by
  apply reverseEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply,reverseEquiv_apply,reverseOperator_involutive]

 theorem reverse_conj_creation (a : α) :
    reverseEquiv.conjStarAlgEquiv (creation a)=rightCreation a := by
  apply operator_basis_ext (α := List α)
  intro w
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,reverseEquiv_symm_apply,
    reverseEquiv_apply,reverseOperator_single,creation_single,rightCreation_single,
    List.reverse_cons,List.reverse_reverse]

 theorem reverse_conj_semicircular (a : α) :
    reverseEquiv.conjStarAlgEquiv (semicircular a)=rightSemicircular a := by
  simp only [semicircular,map_add,map_star,reverse_conj_creation,rightSemicircular]

 theorem wick_mem_any (A : StarSubalgebra ℂ (Operator α))
    (h : ∀ a, semicircular a ∈ A) (w : List α) : wick w ∈ A := by
  suffices ∀ w : List α, wick w ∈ A ∧ ∀ a, wick (a::w) ∈ A from (this w).1
  intro w
  induction w with
  | nil =>
    refine ⟨by rw [wick_nil]; exact A.one_mem,?_⟩
    intro a
    simpa only [wick_semicircular_cons,wick_nil,mul_one,sub_zero] using h a
  | cons b w ih =>
    refine ⟨ih.2 b,?_⟩
    intro a
    rw [wick_semicircular_cons]
    refine A.sub_mem (A.mul_mem (h a) (ih.2 b)) ?_
    change (if a=b then wick w else 0) ∈ A
    by_cases hab : a=b
    · rw [ite_eq_left hab]; exact ih.1
    · rw [ite_eq_right hab]; exact A.zero_mem

 def gaussianCommutant (α : Type u_3) [DecidableEq α] : StarSubalgebra ℂ (Operator α) :=
  StarSubalgebra.centralizer ℂ (Set.range (semicircular : α → Operator α))

 def gaussianAlgebra (α : Type u_4) [DecidableEq α] : StarSubalgebra ℂ (Operator α) :=
  StarSubalgebra.centralizer ℂ (gaussianCommutant α : Set (Operator α))

 theorem rightSemicircular_mem (b : α) : rightSemicircular b ∈ gaussianCommutant α := by
  rw [gaussianCommutant,StarSubalgebra.mem_centralizer_iff]
  rintro _ ⟨a,rfl⟩
  have hs := (semicircular_selfAdjoint a).star_eq
  refine ⟨(semicircular_rightSemicircular a b).eq,?_⟩
  rw [hs]
  exact (semicircular_rightSemicircular a b).eq

 def rightWick (w : List α) : Operator α := reverseEquiv.conjStarAlgEquiv (wick w)

 theorem rightWick_mem (w : List α) : rightWick w ∈ gaussianCommutant α := by
  apply wick_mem_any ((gaussianCommutant α).comap reverseEquiv.conjStarAlgEquiv.toStarAlgHom)
  intro a
  change reverseEquiv.conjStarAlgEquiv (semicircular a) ∈ gaussianCommutant α
  rw [reverse_conj_semicircular]
  exact rightSemicircular_mem a

@[simp] theorem rightWick_vacuum (w : List α) : rightWick w vacuum=lp.single 2 w.reverse 1 := by
  simp only [rightWick,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    reverseEquiv_symm_apply,reverseEquiv_apply]
  have hv : reverseOperator (vacuum : Fock α)=vacuum := reverseOperator_single [] 1
  rw [hv,wick_vacuum,reverseOperator_single]

 theorem rightWick_star (w : List α) : star (rightWick w)=rightWick w.reverse := by
  simp only [rightWick,← map_star,wick_star]

 theorem gaussian_commute_rightWick (T : gaussianAlgebra α) (w : List α) :
    rightWick w*(T : Operator α)=(T : Operator α)*rightWick w :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ (rightWick_mem w)).1

 theorem gaussian_separating (T : gaussianAlgebra α) (hT : (T : Operator α) vacuum=0) : T=0 := by
  apply Subtype.ext
  apply operator_basis_ext (α := List α)
  intro w
  have hc := DFunLike.congr_fun (gaussian_commute_rightWick T w.reverse) vacuum
  simp only [mul_apply_eq_comp,rightWick_vacuum,List.reverse_reverse,hT,map_zero] at hc
  change (T : Operator α) (lp.single 2 w 1)=0
  exact hc.symm

 theorem gaussian_star_vector (T : gaussianAlgebra α) (w : List α) :
    ((star (T : Operator α)) vacuum) w=conj (((T : Operator α) vacuum) w.reverse) := by
  have hc := DFunLike.congr_fun (gaussian_commute_rightWick T w.reverse) vacuum
  simp only [mul_apply_eq_comp,rightWick_vacuum,List.reverse_reverse] at hc
  have hv : (star (rightWick w.reverse)) vacuum=lp.single 2 w.reverse 1 := by
    rw [rightWick_star,rightWick_vacuum,List.reverse_reverse]
  have he : inner ℂ (lp.single 2 w 1) ((star (T : Operator α)) vacuum)=
      inner ℂ ((T : Operator α) vacuum) (lp.single 2 w.reverse 1) := by
    calc
      _ = inner ℂ ((T : Operator α) (lp.single 2 w 1)) vacuum := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = inner ℂ ((rightWick w.reverse) ((T : Operator α) vacuum)) vacuum := by rw [hc]
      _ = inner ℂ ((T : Operator α) vacuum) ((star (rightWick w.reverse)) vacuum) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = _ := by rw [hv]
  simpa [lp.inner_single_left,lp.inner_single_right,RCLike.inner_apply] using he

 theorem gaussian_trace_mul (S T : gaussianAlgebra α) :
    vacuumTrace ((S : Operator α)*(T : Operator α))=
      vacuumTrace ((T : Operator α)*(S : Operator α)) := by
  have hf (A B : gaussianAlgebra α) :
      vacuumTrace ((A : Operator α)*(B : Operator α))=
        ∑' w : List α, ((A : Operator α) vacuum) w.reverse*((B : Operator α) vacuum) w := by
    unfold vacuumTrace
    rw [mul_apply_eq_comp,← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ ((star (A : Operator α)) vacuum) ((B : Operator α) vacuum)=_
    rw [lp.inner_eq_tsum]
    congr 1
    funext w
    rw [gaussian_star_vector]
    simp [RCLike.inner_apply,mul_comm]
  rw [hf,hf]
  let e : List α ≃ List α := ⟨List.reverse,List.reverse, List.reverse_reverse,List.reverse_reverse⟩
  have hs := e.tsum_eq (fun w : List α => ((T : Operator α) vacuum) w.reverse*((S : Operator α) vacuum) w)
  simpa only [e,Equiv.coe_fn_mk,List.reverse_reverse,mul_comm] using hs

end
open GaussianRecognition CyclicSpectral CircularRotation
open Filter Topology
open scoped ENNReal
variable {α : Type u_5} [DecidableEq α]

theorem fock_closed_total (K : Submodule ℂ (Fock α)) (hK : IsClosed (K:Set (Fock α)))
    (hδ : ∀ w : List α,lp.single 2 w (1:ℂ)∈K) : K=⊤ := by
  apply top_unique
  intro ξ _
  apply hK.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) ξ)
  filter_upwards [] with s
  apply K.sum_mem
  intro w _
  have he : lp.single (E := fun _ : List α => ℂ) 2 w (ξ w)=(ξ w) • lp.single 2 w 1 := by
    ext v
    simp [lp.single_apply,Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hδ w)

theorem gaussian_commutant_total :
    (Submodule.span ℂ (Set.range (fun B : StarSubalgebra.centralizer ℂ
      (gaussianAlgebra α:Set (Operator α)) => (B:Operator α) vacuum))).topologicalClosure=⊤ := by
  apply fock_closed_total _ (Submodule.isClosed_topologicalClosure _)
  intro w
  have hB : rightWick w.reverse∈StarSubalgebra.centralizer ℂ (gaussianAlgebra α:Set (Operator α)) :=
    WeightedFock.centralizer_bicommutant (Set.range (semicircular : α → Operator α))
      ⟨_,rightWick_mem w.reverse⟩
  apply Submodule.le_topologicalClosure _
  have hh : rightWick w.reverse vacuum=lp.single 2 w 1 := by
    rw [rightWick_vacuum,List.reverse_reverse]
  rw [← hh]
  exact Submodule.subset_span ⟨⟨rightWick w.reverse,hB⟩,rfl⟩

theorem semicircular_mem_uniform_bicommutant (i : α) :
    semicircular i∈Bicommutant.algebra (Set.range (scalarUniform i)) := by
  let : Nontrivial (Fock α) := by
    apply nontrivial_of_ne (vacuum : Fock α) 0
    intro h
    have hh := congrArg (fun ξ : Fock α => ξ []) h
    simp [vacuum,lp.single_apply] at hh
  let := semicircular_spectral_noAtoms i
  have h := operator_mem_haar_bicommutant (semicircular i) (semicircular_selfAdjoint i) vacuum
    (gaussianAlgebra α) (Set.isClosed_centralizer _)
    (Bicommutant.subset (Set.range (semicircular : α → Operator α)) (Set.mem_range_self i))
    gaussian_commutant_total
  apply Bicommutant.mono _ (Set.range (scalarUniform i)) ?_ h
  intro T hT
  rcases hT with rfl
  exact ⟨uniformPhase,(uniformHom_phase (semicircular i) (semicircular_selfAdjoint i) vacuum).symm⟩

def scalarFlip (i : WeightedCornerIndex.Index × ℕ) : WeightedCornerIndex.Index × ℕ := (flip i.1,i.2)

theorem scalarCoeff_mem_gaussian (a : UniformAlgebra) :
    scalarSystem.coeff a∈gaussianAlgebra ScalarIndex := by
  let := semicircular_spectral_noAtoms (none:ScalarIndex)
  exact uniformHom_mem (semicircular (none:ScalarIndex)) (semicircular_selfAdjoint none) vacuum
    (gaussianAlgebra ScalarIndex) (Set.isClosed_centralizer _)
    (Bicommutant.subset _ (Set.mem_range_self none)) a

theorem scalarGenerator_mem_gaussian (i : WeightedCornerIndex.Index × ℕ) :
    scalarSystem.generator scalarFlip i∈gaussianAlgebra ScalarIndex := by
  exact (rotate_generation (fun j => creation (some (j,i.2))) (gaussianAlgebra ScalarIndex)).mp
    (fun j => Bicommutant.subset (Set.range (semicircular : ScalarIndex → Operator ScalarIndex))
      (Set.mem_range_self (some (j,i.2)))) i.1

theorem scalar_semicircular_mem_generated (i : ScalarIndex) :
    semicircular i∈scalarSystem.generated scalarFlip := by
  cases i with
  | none =>
    exact Bicommutant.mono _ _ (Set.subset_union_left)
      (semicircular_mem_uniform_bicommutant (none:ScalarIndex))
  | some i =>
    exact (rotate_generation (fun j => creation (some (j,i.2)))
      (scalarSystem.generated scalarFlip)).mpr
      (fun j => Bicommutant.subset _ (Set.mem_union_right _ (Set.mem_range_self (j,i.2)))) i.1

theorem scalar_generated_eq_gaussian : scalarSystem.generated scalarFlip=gaussianAlgebra ScalarIndex := by
  apply le_antisymm
  · apply Bicommutant.generated_le
    rintro T (⟨a,rfl⟩ | ⟨i,rfl⟩)
    · exact scalarCoeff_mem_gaussian a
    · exact scalarGenerator_mem_gaussian i
  · apply Bicommutant.generated_le
    rintro T ⟨i,rfl⟩
    exact scalar_semicircular_mem_generated i

theorem scalarSystem_total :
    (Submodule.span ℂ (Set.range scalarSystem.family)).topologicalClosure=⊤ := by
  apply fock_closed_total _ (Submodule.isClosed_topologicalClosure _)
  intro w
  have hw : wick w∈scalarSystem.generated scalarFlip := by
    rw [scalar_generated_eq_gaussian]
    exact wick_mem_any _ (fun i => Bicommutant.subset _ (Set.mem_range_self i)) w
  have h := scalarSystem.normalHull_bicommutant scalarFlip (wick w) hw
  change lp.single 2 w 1∈scalarSystem.normalHull
  simpa only [show scalarSystem.root=(vacuum : Fock ScalarIndex) from rfl,wick_vacuum] using h
end FreeGroupFactorMain.FreeFock

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification WeightedCornerIndex GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem pRep_add (a b : PCorner ℕ) : pRepresentation (a+b)=pRepresentation a+pRepresentation b :=
  (pRepresentation (ι := ℕ)).map_add' a b

theorem pRep_star (a : PCorner ℕ) : pRepresentation (star a)=star (pRepresentation a) :=
  (pRepresentation (ι := ℕ)).map_star' a

def representedAmbient : StarSubalgebra ℂ (PRange ℕ →L[ℂ] PRange ℕ) :=
  (pAmbient u v).comap (pRepresentation (ι := ℕ)).symm.toStarAlgHom

theorem pFilled_le_pAmbient : Base u v ≤ pAmbient u v :=
  fun _ ha => filledEdgeAlgebra_le_ambient u v (0:ℕ) 1 ha

theorem kindPair_mem_pAmbient (k : Kind) :
    kindCreator u v k+star (kindCreator u v k.transpose)∈pAmbient u v := by
  cases k with
  | fresh n r s => exact normalizedCreation_paired_mem u v (0:ℕ) (n+2) r s
  | residual r s => exact normalizedResidual_paired_mem u v (0:ℕ) 1 r s
  | diagonal r =>
    change pDiagonal u v 0 0 r+star (pDiagonal u v 0 0 r)∈pAmbient u v
    rw [pDiagonal_eq_pFresh]
    exact normalizedCreation_paired_mem u v (0:ℕ) 0 r r

theorem outputPair_mem_pAmbient (i : WeightedCornerIndex.Index) (n : ℕ) :
    (cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈pAmbient u v := by
  apply ((cornerAbsorption u v hv hvu).output_generation (pAmbient u v)
    (fun i => pFilled_le_pAmbient u v (kindLeft u v (description i)).property)
    (fun i => pFilled_le_pAmbient u v (kindRight u v (description i)).property)).mp ?_ i n
  constructor
  · intro i
    change kindCreator u v (description i)+star (kindCreator u v (description (CircularRotation.flip i)))∈pAmbient u v
    rw [description_flip]
    exact kindPair_mem_pAmbient u v (description i)
  · intro i n
    exact normalizedCreation_paired_mem u v (0:ℕ) (reservoirCode (i,n)+2) false false

theorem representedAmbient_saturated :
    Bicommutant.algebra (representedAmbient u v : Set (PRange ℕ →L[ℂ] PRange ℕ))≤representedAmbient u v := by
  intro T hT
  have him : (representedAmbient u v : Set (PRange ℕ →L[ℂ] PRange ℕ))=
      pRepresentation '' (pAmbient (ι := ℕ) u v : Set (PCorner ℕ)) := by
    ext B
    constructor
    · intro h;exact ⟨(pRepresentation (ι := ℕ)).symm B,h,StarAlgEquiv.apply_symm_apply _ _⟩
    · rintro ⟨b,hb,rfl⟩
      change (pRepresentation (ι := ℕ)).symm (pRepresentation b)∈pAmbient u v
      rw [StarAlgEquiv.symm_apply_apply]
      exact hb
  change (pRepresentation (ι := ℕ)).symm T∈pAmbient u v
  apply relative_corner_bicommutant (insert P (Set.range (S u v : ℕ → Operator ℕ)))
    P projection_P (P_mem_ambient u v)
  apply (bicommutant_transport (A := PCorner ℕ) (B := PRange ℕ →L[ℂ] PRange ℕ) (pRepresentation (ι := ℕ)) (pAmbient (ι := ℕ) u v : Set (PCorner ℕ))
    ((pRepresentation (ι := ℕ)).symm T)).mp
  rw [StarAlgEquiv.apply_symm_apply,← him]
  exact hT

theorem weighted_generated_le_ambient : (weightedSystem u v hv hvu).generated scalarFlip≤representedAmbient u v := by
  apply le_trans (Bicommutant.mono _ (representedAmbient u v : Set (PRange ℕ →L[ℂ] PRange ℕ)) ?_)
    (representedAmbient_saturated u v)
  rintro T (⟨a,rfl⟩|⟨i,rfl⟩)
  · exact pFilled_le_pAmbient u v (weightedUniform_mem u v hv hvu a)
  · change (pRepresentation (ι := ℕ)).symm
      (pRepresentation ((cornerAbsorption u v hv hvu).output i.1 i.2)+
        star (pRepresentation ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i.1) i.2)))∈pAmbient u v
    rw [← pRep_star,← pRep_add,StarAlgEquiv.symm_apply_apply]
    exact outputPair_mem_pAmbient u v hv hvu i.1 i.2

theorem representedAmbient_le_weightedGenerated : representedAmbient u v≤(weightedSystem u v hv hvu).generated scalarFlip := by
  let G := (weightedSystem u v hv hvu).generated scalarFlip
  let M := G.comap (pRepresentation (ι := ℕ)).toStarAlgHom
  have hbase (a : Base u v) : (a:PCorner ℕ)∈M := by
    apply Bicommutant.mono (Set.range (weightedUniform u v hv hvu))
        ((weightedSystem u v hv hvu).generators scalarFlip) (fun _ h => Or.inl h)
    apply representedBase_le_weightedUniform u v hv hvu
    change (pRepresentation (ι := ℕ)).symm (pRepresentation a.val)∈Base u v
    simpa only [StarAlgEquiv.symm_apply_apply] using a.property
  have hout (i : WeightedCornerIndex.Index) (n : ℕ) :
      (cornerAbsorption u v hv hvu).output i n+
        star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M := by
    change pRepresentation (_+star _)∈G
    rw [pRep_add,pRep_star]
    exact Bicommutant.subset ((weightedSystem u v hv hvu).generators scalarFlip)
      (Or.inr (Set.mem_range_self (i,n)))
  intro T hT
  have hr := pAmbient_recovered u v hv hvu M hbase hout hT
  have hh := (bicommutant_transport (A := PCorner ℕ) (B := PRange ℕ →L[ℂ] PRange ℕ) (pRepresentation (ι := ℕ)) (M : Set (PCorner ℕ))
    ((pRepresentation (ι := ℕ)).symm T)).mpr hr
  rw [StarAlgEquiv.apply_symm_apply] at hh
  apply Bicommutant.generated_le ((weightedSystem u v hv hvu).generators scalarFlip)
    (pRepresentation '' (M : Set (PCorner ℕ))) ?_ hh
  rintro _ ⟨b,hb,rfl⟩
  exact hb

theorem weighted_generated_eq_ambient :
    (weightedSystem u v hv hvu).generated scalarFlip=representedAmbient u v :=
  le_antisymm (weighted_generated_le_ambient u v hv hvu) (representedAmbient_le_weightedGenerated u v hv hvu)
end FreeGroupFactorMain.WeightedFock

end

end OAI
