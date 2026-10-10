import Mathlib
import OAI.RepresentationTheory.Placement.Occurrence
import OAI.Probability.CoordinateSweeps.SparseMoment

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps.Grid.Holes
open PlacementOccurrence Placement
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

def inputPlacementEquiv : (Fin k ↪ H.FreeAt 0) ≃ H.InputPlacements k where
  toFun x := ⟨fun i => (x i).val,⟨fun _ _ he => x.injective (Subtype.ext he),fun i a => (x i).property a⟩⟩
  invFun x := ⟨fun i => ⟨x.val i,x.property.2 i⟩,fun _ _ he => x.property.1 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def outputFreePlacementEquiv : (Fin k ↪ H.FreeAt (Fin.last G.b)) ≃ H.OutputPlacements k where
  toFun x := ⟨fun i => (x i).val,⟨fun _ _ he => x.injective (Subtype.ext he),fun i a => (x i).property a⟩⟩
  invFun x := ⟨fun i => ⟨x.val i,x.property.2 i⟩,fun _ _ he => x.property.1 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def outputPlacementEquiv (hf : H.Feasible) : (Fin k ↪ H.FreeAt 0) ≃ H.OutputPlacements k :=
  (Equiv.embeddingCongr (Equiv.refl (Fin k))
    (H.freeBoundary ⟨H.reference hf,H.reference_compatible hf⟩ (Fin.last G.b))).trans H.outputFreePlacementEquiv

lemma outputPlacementEquiv_apply (hf : H.Feasible) (y : Fin k ↪ H.FreeAt 0) (i : Fin k) :
    (H.outputPlacementEquiv hf y).val i=G.sweep (H.reference hf) (y i).val := rfl

def residualFree (hf : H.Feasible) (ω : {ω : G.Choices // H.Compatible ω}) : Equiv.Perm (H.FreeAt 0) :=
  H.stabilizerFreeEquiv (H.residual hf ω)

lemma residualFree_apply (hf : H.Feasible) (ω : {ω : G.Choices // H.Compatible ω}) (x : H.FreeAt 0) :
    (H.residualFree hf ω x).val=(G.sweep (H.reference hf))⁻¹ (G.sweep ω.val x.val) := rfl

lemma endpointEvent_residualFree (hf : H.Feasible) (x y : Fin k ↪ H.FreeAt 0)
    (ω : {ω : G.Choices // H.Compatible ω}) :
    G.endpointEvent (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ ω.val ↔
      H.residualFree hf ω • x=y := by
  constructor
  · intro he
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    change (H.residualFree hf ω (x i)).val=(y i).val
    rw [H.residualFree_apply]
    apply (Equiv.symm_apply_eq (G.sweep (H.reference hf))).mpr
    exact he i (Finset.mem_univ _)
  · intro he i hi
    have hh := congrArg (fun x : Fin k ↪ H.FreeAt 0 => (x i).val) he
    change (H.residualFree hf ω (x i)).val=(y i).val at hh
    rw [H.residualFree_apply] at hh
    exact (Equiv.symm_apply_eq (G.sweep (H.reference hf))).mp hh

lemma extraProbability_eq_residual_sum (hf : H.Feasible) (x y : Fin k ↪ H.FreeAt 0)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.extraProbability (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ
      (fun j => lineLaw (G.bits j) z hz hz') =
      ∑ ω : {ω : G.Choices // H.Compatible ω},
        if H.residualFree hf ω • x=y then G.choiceWeight z ω.val/H.probability z else 0 := by
  rw [H.extraProbability_eq_conditionalEndpoint,conditionalEndpointProbability,H.lineMass_hole_normalizer hz hz']
  have hn : (∑ ω : G.Choices, if H.Compatible ω ∧
      G.endpointEvent (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ ω then
        G.productLineMass (fun j => lineLaw (G.bits j) z hz hz') ω else 0)=
      ∑ ω : {ω : G.Choices // H.Compatible ω},
        if H.residualFree hf ω • x=y then G.choiceWeight z ω.val else 0 := by
    symm
    calc
      _ = ∑ ω : {ω : G.Choices // H.Compatible ω},
          if G.endpointEvent (H.inputPlacementEquiv x).val
            (H.outputPlacementEquiv hf y).val Finset.univ ω.val then G.choiceWeight z ω.val else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [H.endpointEvent_residualFree hf]
        split_ifs <;> rfl
      _ = _ := by
        rw [sum_subtype_eq_sum_ite_of_iff (fun _ => Iff.rfl)
      (fun ω : G.Choices => if G.endpointEvent (H.inputPlacementEquiv x).val
        (H.outputPlacementEquiv hf y).val Finset.univ ω then G.choiceWeight z ω else 0)]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> try rfl
        all_goals simp_all
  rw [hn,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

/- Partial endpoint matrix written on a single placement set using the
reference sweep; every variable is a literal conditional path probability. -/
def referencePartial (hf : H.Feasible) (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (A : Finset (Fin k)) (x y : Fin k ↪ H.FreeAt 0) : ℝ :=
  H.extraProbability (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val A μ

lemma referencePartial_depends (hf : H.Feasible)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (A : Finset (Fin k)) (x : Fin k ↪ H.FreeAt 0) :
    Placement.DependsOn (fun y : Fin k ↪ H.FreeAt 0 => y) A
      (fun y => (H.referencePartial hf μ A x y : ℂ)) := by
  intro y y' hy
  apply H.extraProbability_dependsOn μ A (H.inputPlacementEquiv x)
  intro i hi
  simp only [outputPlacementEquiv_apply,hy i hi]

lemma referencePartial_full (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    (show Matrix (Fin k ↪ H.FreeAt 0) (Fin k ↪ H.FreeAt 0) ℂ from fun x y =>
      (H.referencePartial hf (fun j => lineLaw (G.bits j) z hz hz') Finset.univ x y : ℂ))=
        ∑ ω : {ω : G.Choices // H.Compatible ω},
          ((G.choiceWeight z ω.val/H.probability z : ℝ) : ℂ) •
            actionMatrix (X := Fin k ↪ H.FreeAt 0) (H.residualFree hf ω)⁻¹ := by
  ext x y
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,actionMatrix_entry,inv_inv]
  rw [referencePartial,H.extraProbability_eq_residual_sum hf x y hz hz',Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma referenceAlternating_entry (hf : H.Feasible)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (x y : Fin k ↪ H.FreeAt 0) :
    alternatingKernel (G.size : ℝ) (H.referencePartial hf μ) x y=
      (H.placementKernel (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val μ : ℂ) := by
  simp only [alternatingKernel,referencePartial,placementKernel,Fintype.card_fin]

lemma referenceAlternating_hs (hf : H.Feasible)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    (∑ x : Fin k ↪ H.FreeAt 0, ∑ y : Fin k ↪ H.FreeAt 0,
      ‖alternatingKernel (G.size : ℝ) (H.referencePartial hf μ) x y‖^2)=H.placementHSsq (k := k) μ := by
  rw [H.placementHSsq_eq_subtype]
  simp only [referenceAlternating_entry]
  apply Fintype.sum_equiv H.inputPlacementEquiv
  intro x
  exact (H.outputPlacementEquiv hf).sum_comp
    (fun y => ‖(H.placementKernel (H.inputPlacementEquiv x).val y.val μ : ℂ)‖^2)

/- The missing attachment of source04:eq7 to the faithful conditional
irreducible average, not merely an abstract stochastic matrix. -/
theorem conditional_norm_le_placementHS (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0)))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    (hnof : ∀ A : Finset (H.FreeAt 0), A.card < k → ∀ v : Fin ρ.dimension → ℂ,
      (∀ g : Equiv.Perm (H.FreeAt 0), (∀ a ∈ A, g a=a) → ρ.asRepresentation g v=v) → v=0) :
    ‖H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)‖ ≤
      Real.sqrt (H.placementHSsq (k := k) (fun j => lineLaw (G.bits j) z hz hz')) := by
  have hm := first_level_norm_le ρ u hu x₀ hfixed (by simpa only [Fintype.card_fin] using hnof)
    (fun ω : {ω : G.Choices // H.Compatible ω} => ((G.choiceWeight z ω.val/H.probability z : ℝ) : ℂ))
    (fun ω => (H.residualFree hf ω)⁻¹) (G.size : ℝ) (by unfold Grid.size; positivity)
    (H.referencePartial hf (fun j => lineLaw (G.bits j) z hz hz'))
    (H.referencePartial_depends hf _) (H.referencePartial_full hf hz hz')
  have he : (∑ ω : {ω : G.Choices // H.Compatible ω},
      ((G.choiceWeight z ω.val/H.probability z : ℝ):ℂ) • ρ.matrix (H.residualFree hf ω)⁻¹)=
      (H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)).conjTranspose := by
    rw [H.conditionalAverage_eq_sum,Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro ω _
    rw [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal]
    exact congrArg (fun M => ((G.choiceWeight z ω.val/H.probability z : ℝ):ℂ) • M)
      (ρ.matrix_inv (H.residualFree hf ω))
  rw [he] at hm
  change ‖(H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)).conjTranspose‖ ≤ _ at hm
  rw [Matrix.l2_opNorm_conjTranspose] at hm
  apply hm.trans
  have hh := Placement.matrix_l2_norm_le_hs (alternatingKernel (G.size : ℝ)
      (H.referencePartial (k := k) hf (fun j => lineLaw (G.bits j) z hz hz')))
  rw [H.referenceAlternating_hs] at hh
  convert hh using 1
  rfl
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
-- Archived complete binary-sign support, reused without a new-result claim.
/- The real-valued sign character, not a replacement for the permutation. -/
def realSign {Ω : Type*} [Fintype Ω] [DecidableEq Ω] : Equiv.Perm Ω →* ℝ where
  toFun g := ((Equiv.Perm.sign g : ℤ) : ℝ)
  map_one' := by simp
  map_mul' g h := by simp

def boolSwitch (b : Bool) : Equiv.Perm Bool :=
  if b then Equiv.swap false true else 1

theorem boolSwitch_apply (b x : Bool) : boolSwitch b x = Bool.xor x b := by
  cases b <;> cases x <;> simp [boolSwitch]

theorem sign_boolSwitch (b : Bool) : realSign (boolSwitch b) = if b then -1 else 1 := by
  cases b <;> simp [boolSwitch, realSign]

theorem pairSwitch_eq_prod {L : Type*} (bits : L → Bool) :
    pairSwitch bits = Equiv.prodCongrLeft (fun l => boolSwitch (bits l)) := by
  apply Equiv.ext
  rintro ⟨b,l⟩
  change (Bool.xor b (bits l), l) = (boolSwitch (bits l) b, l)
  rw [boolSwitch_apply]

theorem sign_pairSwitch {L : Type*} [Fintype L] (bits : L → Bool) :
    realSign (pairSwitch bits) = ∏ l, (if bits l then (-1 : ℝ) else 1) := by
  rw [pairSwitch_eq_prod]
  change (((Equiv.Perm.sign (Equiv.prodCongrLeft (fun l => boolSwitch (bits l)))) : ℤ) : ℝ) = _
  rw [Equiv.Perm.sign_prodCongrLeft]
  change (((Units.coeHom ℤ) (∏ l, Equiv.Perm.sign (boolSwitch (bits l)))) : ℝ) = _
  rw [map_prod, Int.cast_prod]
  apply Finset.prod_congr rfl
  intro l _
  exact sign_boolSwitch (bits l)

theorem sign_binaryLayer {d : ℕ} (j : Fin d)
    (bits : ({k : Fin d // k ≠ j} → Bool) → Bool) :
    realSign (binaryLayer j bits) = realSign (pairSwitch bits) := by
  change (((Equiv.Perm.sign (_)) : ℤ) : ℝ) = _
  rw [binaryLayer, Equiv.Perm.sign_trans_trans]
  simp [realSign]

theorem sum_sign_pairSwitch {L : Type*} [Fintype L] [Nonempty L] :
    (∑ bits : L → Bool, realSign (pairSwitch bits)) = 0 := by
  simp_rw [sign_pairSwitch]
  rw [← Fintype.prod_sum (fun (_ : L) (b : Bool) => if b then (-1 : ℝ) else 1)]
  simp

theorem sign_binarySweep (d : ℕ) (bits : BinaryChoices d) :
    realSign (binarySweep d bits) = ∏ j, realSign (binaryLayer j (bits j)) := by
  unfold binarySweep orderedProduct
  rw [map_list_prod]
  simp [List.map_reverse, List.map_ofFn, List.prod_reverse, List.prod_ofFn]

theorem sum_sign_binarySweep {d : ℕ} (hd : 0 < d) :
    (∑ bits : BinaryChoices d, realSign (binarySweep d bits)) = 0 := by
  simp_rw [sign_binarySweep, sign_binaryLayer]
  change (∑ bits : BinaryChoices d, ∏ j : Fin d,
    realSign (pairSwitch (bits j))) = 0
  have hs : ∀ (j : Fin d) (b : ({k : Fin d // k ≠ j} → Bool) → Bool),
      realSign (pairSwitch b) = ∏ l, if b l then (-1 : ℝ) else 1 := by
    intro j b
    convert sign_pairSwitch b using 1
    congr 2
    exact Subsingleton.elim _ _
  simp_rw [hs]
  rw [← Fintype.prod_sum (fun j : Fin d =>
    fun b : ({k : Fin d // k ≠ j} → Bool) → Bool =>
      ∏ l, if b l then (-1 : ℝ) else 1)]
  apply Finset.prod_eq_zero (i := (⟨0,hd⟩ : Fin d)) (Finset.mem_univ _)
  rw [← Fintype.prod_sum (fun (_ : ({k : Fin d // k ≠ (⟨0,hd⟩ : Fin d)} → Bool))
    (b : Bool) => if b then (-1 : ℝ) else 1)]
  simp

end CoordinateSweeps

namespace CoordinateSweeps
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma signed_sum_zero_of_swap (w : Equiv.Perm Ω → ℝ) (P : Equiv.Perm Ω → Prop)
    (a b : Ω) (hab : a ≠ b)
    (hw : ∀ σ, w (Equiv.swap a b*σ)=w σ)
    (hP : ∀ σ, P (Equiv.swap a b*σ) ↔ P σ) :
    (∑ σ : Equiv.Perm Ω, if P σ then w σ*realSign σ else 0)=0 := by
  classical
  have hs : realSign (Equiv.swap a b)=(-1:ℝ) := by
    simp [realSign,Equiv.Perm.sign_swap hab]
  have he := Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))
    (fun σ : Equiv.Perm Ω => if P σ then w σ*realSign σ else 0)
  have hn : (∑ σ : Equiv.Perm Ω, if P (Equiv.swap a b*σ) then
      w (Equiv.swap a b*σ)*realSign (Equiv.swap a b*σ) else 0)=
      -(∑ σ : Equiv.Perm Ω, if P σ then w σ*realSign σ else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hP,hw,map_mul,hs]
    split_ifs <;> ring
  change (∑ σ : Equiv.Perm Ω, if P (Equiv.swap a b*σ) then
    w (Equiv.swap a b*σ)*realSign (Equiv.swap a b*σ) else 0)=_ at he
  linarith [hn,he]

lemma sum_uniform_realSign [Nontrivial Ω] :
    (∑ σ : Equiv.Perm Ω, FiniteLaw.uniform _ σ*realSign σ)=0 := by
  obtain ⟨a,b,hab⟩ := exists_pair_ne Ω
  simpa only [ite_true] using signed_sum_zero_of_swap (FiniteLaw.uniform _) (fun _ => True)
    a b hab (fun _ => rfl) (fun _ => Iff.rfl)

omit [DecidableEq Ω] in
lemma sum_map_mul (μ : FiniteLaw Ω) {X : Type*} [Fintype X] (f : Ω → X) (v : X → ℝ) :
    (∑ y : X, (μ.map f) y*v y)=∑ x : Ω, μ x*v (f x) := by
  simp only [FiniteLaw.map_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

lemma sum_binary_realSign {d : ℕ} (hd : 0 < d) :
    (∑ σ : Equiv.Perm (Cube d), binaryLaw d σ*realSign σ)=0 := by
  rw [binaryLaw,sum_map_mul]
  simp only [FiniteLaw.uniform_apply,← Finset.mul_sum,sum_sign_binarySweep hd,mul_zero]

lemma sum_lineLaw_realSign {d : ℕ} (hd : 0 < d) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    (∑ σ : Equiv.Perm (Cube d), lineLaw d z hz hz' σ*realSign σ)=0 := by
  let : NeZero d := ⟨hd.ne'⟩
  change (∑ σ : Equiv.Perm (Cube d), ((1-z)*FiniteLaw.uniform _ σ+z*binaryLaw d σ)*realSign σ)=0
  simp only [add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,
    sum_uniform_realSign,sum_binary_realSign hd,mul_zero,add_zero]

lemma uniform_signed_assignments_zero {I : Type*}
    (x y : I → Ω) (a b : Ω) (hab : a ≠ b) (ha : ∀ i, y i ≠ a) (hb : ∀ i, y i ≠ b) :
    (∑ σ : Equiv.Perm Ω, if ∀ i, σ (x i)=y i then FiniteLaw.uniform _ σ*realSign σ else 0)=0 := by
  apply signed_sum_zero_of_swap (FiniteLaw.uniform _) _ a b hab (fun _ => rfl)
  have hs (i : I) : Equiv.swap a b (y i)=y i := Equiv.swap_apply_of_ne_of_ne (ha i) (hb i)
  intro σ
  constructor
  · intro h i
    apply (Equiv.swap a b).injective
    exact (h i).trans (hs i).symm
  · intro h i
    change Equiv.swap a b (σ (x i))=y i
    rw [h i,hs]

namespace Grid
lemma realSign_fiberPerm {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (g : B → Equiv.Perm A) : realSign (fiberPerm g)=∏ b, realSign (g b) := by
  have he : fiberPerm g=Equiv.prodCongrLeft g := rfl
  rw [he]
  change (((Equiv.Perm.sign (Equiv.prodCongrLeft g) : ℤ):ℝ))=_
  rw [Equiv.Perm.sign_prodCongrLeft]
  change (((Units.coeHom ℤ) (∏ b, Equiv.Perm.sign (g b))):ℝ)=_
  rw [map_prod,Int.cast_prod]
  rfl

lemma realSign_stage (G : Grid) (ω : G.Choices) (j : Fin G.b) :
    realSign (G.stage ω j)=∏ L, realSign (ω j L) := by
  have he : realSign (G.stage ω j)=realSign (fiberPerm (ω j)) := by
    change (((Equiv.Perm.sign (_)) : ℤ) : ℝ) = _
    rw [stage,Equiv.Perm.sign_trans_trans]
    simp [realSign]
  exact he.trans (realSign_fiberPerm (ω j))

lemma realSign_sweep (G : Grid) (ω : G.Choices) :
    realSign (G.sweep ω)=∏ j, ∏ L, realSign (ω j L) := by
  unfold sweep boundary
  have ht := List.take_length (l := List.ofFn (G.stage ω))
  simp only [List.length_ofFn] at ht
  rw [ht]
  rw [map_list_prod]
  simp only [List.map_reverse,List.map_ofFn,List.prod_reverse,List.prod_ofFn,Function.comp_apply,realSign_stage]

lemma signed_line_factorization (G : Grid)
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (P : ∀ j : Fin G.b, G.Line j → Equiv.Perm (Cube (G.bits j)) → Prop) :
    (∑ ω : G.Choices, if ∀ j L, P j L (ω j L) then G.productLineMass μ ω*realSign (G.sweep ω) else 0)=
      ∏ j, ∏ L, ∑ σ, if P j L σ then μ j σ*realSign σ else 0 := by
  simp only [realSign_sweep,productLineMass,← Finset.prod_mul_distrib]
  calc
    _ = ∏ j, ∑ ω : G.Line j → Equiv.Perm (Cube (G.bits j)),
        if ∀ L, P j L (ω L) then ∏ L, μ j (ω L)*realSign (ω L) else 0 := by
      convert sum_prod_ite_all
        (fun j (ω : G.Line j → Equiv.Perm (Cube (G.bits j))) => ∏ L, μ j (ω L)*realSign (ω L))
        (fun j (ω : G.Line j → Equiv.Perm (Cube (G.bits j))) => ∀ L, P j L (ω L)) using 1 <;>
          congr!
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      exact sum_prod_ite_all (fun _ σ => μ j σ*realSign σ) (P j)
end Grid
end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

def jointLineEvent (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (j : Fin G.b) (L : G.Line j) (σ : Equiv.Perm (Cube (G.bits j))) : Prop :=
  H.LineCompatible j L σ ∧ G.extraLineEvent x y A j L σ

lemma signed_endpoint_factorization (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y A ω then
      G.productLineMass μ ω*realSign (G.sweep ω) else 0)=
      ∏ j, ∏ L, ∑ σ, if H.jointLineEvent x y A j L σ then μ j σ*realSign σ else 0 := by
  have he (ω : G.Choices) : H.Compatible ω ∧ G.endpointEvent x y A ω ↔
      ∀ j L, H.jointLineEvent x y A j L (ω j L) := by
    rw [H.compatible_iff_lines,G.endpointEvent_iff_lines]
    exact ⟨fun hh j L => ⟨hh.1 j L,hh.2 j L⟩,
      fun hh => ⟨fun j L => (hh j L).1,fun j L => (hh j L).2⟩⟩
  simp_rw [he]
  exact G.signed_line_factorization μ (H.jointLineEvent x y A)

lemma signed_endpoint_zero_of_unused (x y : Fin k → G.Slot) (A : Finset (Fin k))
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) (j : Fin G.b) (hj : 0 < G.bits j)
    (L : G.Line j) (hholes : ∀ i : Fin h, ¬ H.OnLine j L i)
    (hpaths : ∀ i ∈ A, G.pathLine (x i) (y i) j ≠ L) :
    (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y A ω then
      G.choiceWeight z ω*realSign (G.sweep ω) else 0)=0 := by
  change (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y A ω then
    G.productLineMass (fun j => lineLaw (G.bits j) z hz hz') ω*realSign (G.sweep ω) else 0)=0
  rw [H.signed_endpoint_factorization]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Finset.prod_eq_zero (Finset.mem_univ L)
  have he (σ : Equiv.Perm (Cube (G.bits j))) : H.jointLineEvent x y A j L σ := by
    constructor
    · intro i
      exact False.elim (hholes i.val i.property)
    · intro i hi hL
      exact False.elim (hpaths i hi hL)
  simp only [ite_eq_left (he _)]
  exact sum_lineLaw_realSign hj hz hz'

lemma exists_unused_line (x y : Fin k → G.Slot) (j : Fin G.b)
    (hj : h+k < Fintype.card (G.Line j)) :
    ∃ L : G.Line j, (∀ i : Fin h, ¬ H.OnLine j L i) ∧
      ∀ i : Fin k, G.pathLine (x i) (y i) j ≠ L := by
  let f : Fin h ⊕ Fin k → G.Line j := Sum.elim
    (fun i => fun t => H.path i j.castSucc t) (fun i => G.pathLine (x i) (y i) j)
  have hn : ¬ Function.Surjective f := by
    intro hs
    have hc := Fintype.card_le_of_surjective f hs
    simp only [Fintype.card_sum,Fintype.card_fin] at hc
    omega
  obtain ⟨L,hL⟩ := not_forall.mp hn
  refine ⟨L,?_,?_⟩
  · intro i hi
    exact hL ⟨Sum.inl i,hi⟩
  · intro i hi
    exact hL ⟨Sum.inr i,hi⟩

/- Literal many-coordinate column cancellation; no complex conditioning. -/
theorem signed_endpoint_zero_many (x y : Fin k → G.Slot) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z ≤ 1) (j : Fin G.b) (hj : 0 < G.bits j)
    (hsize : h+k < Fintype.card (G.Line j)) :
    (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y Finset.univ ω then
      G.choiceWeight z ω*realSign (G.sweep ω) else 0)=0 := by
  obtain ⟨L,hH,hP⟩ := H.exists_unused_line x y j hsize
  exact H.signed_endpoint_zero_of_unused x y Finset.univ hz hz' j hj L hH (fun i _ => hP i)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
/- More than one unassigned slot per line on average forces two free slots
on a common line. Assignments need not be injective for this counting step. -/
lemma exists_two_unassigned {I U V : Type*} [Fintype I] [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (f : I → U × V)
    (hh : Fintype.card I+Fintype.card V < Fintype.card (U × V)) :
    ∃ a b : U, ∃ v : V, a ≠ b ∧ (∀ i, f i ≠ (a,v)) ∧ ∀ i, f i ≠ (b,v) := by
  classical
  let S := (Finset.univ : Finset (U × V)) \ Finset.univ.image f
  have hc : Fintype.card V < S.card := by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
    have hi : (Finset.univ.image f).card ≤ Fintype.card I := by
      simpa using Finset.card_image_le (s := Finset.univ) (f := f)
    omega
  have hn : ¬ Function.Injective (fun u : S => u.val.2) := by
    intro hi
    have ht := Fintype.card_le_of_injective _ hi
    exact (not_le.mpr hc) (by simpa only [Fintype.card_coe] using ht)
  simp only [Function.Injective] at hn
  push Not at hn
  obtain ⟨a,b,hv,hab⟩ := hn
  refine ⟨a.val.1,b.val.1,a.val.2,?_,?_,?_⟩
  · intro he
    apply hab
    exact Subtype.ext (Prod.ext he hv)
  · intro i hi
    have ha := (Finset.mem_sdiff.mp a.property).2
    exact ha (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)
  · intro i hi
    have hb := (Finset.mem_sdiff.mp b.property).2
    apply hb
    refine Finset.mem_image.mpr ⟨i,Finset.mem_univ _,?_⟩
    exact hi.trans (Prod.ext rfl hv)
end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ} (H : G.Holes h)
lemma uniform_signed_joint_zero (x y : Fin k → G.Slot) (j : Fin G.b)
    (L : G.Line j) (a b : Cube (G.bits j)) (hab : a ≠ b)
    (haH : ∀ i : Fin h, H.OnLine j L i → H.path i j.succ j ≠ a)
    (hbH : ∀ i : Fin h, H.OnLine j L i → H.path i j.succ j ≠ b)
    (haP : ∀ i, G.pathLine (x i) (y i) j=L → y i j ≠ a)
    (hbP : ∀ i, G.pathLine (x i) (y i) j=L → y i j ≠ b) :
    (∑ σ, if H.jointLineEvent x y Finset.univ j L σ then
      FiniteLaw.uniform _ σ*realSign σ else 0)=0 := by
  apply signed_sum_zero_of_swap (FiniteLaw.uniform _) _ a b hab (fun _ => rfl)
  have he (u v : Cube (G.bits j)) (hv : v ≠ a) (hv' : v ≠ b) (σ : Equiv.Perm (Cube (G.bits j))) :
      (Equiv.swap a b*σ) u=v ↔ σ u=v := by
    have hs := Equiv.swap_apply_of_ne_of_ne hv hv'
    constructor
    · intro hh
      apply (Equiv.swap a b).injective
      exact hh.trans hs.symm
    · intro hh
      change Equiv.swap a b (σ u)=v
      rw [hh,hs]
  intro σ
  unfold jointLineEvent LineCompatible extraLineEvent
  constructor
  · intro hh
    constructor
    · intro i
      exact (he _ _ (haH i i.property) (hbH i i.property) σ).mp (hh.1 i)
    · intro i hi hL
      exact (he _ _ (haP i hL) (hbP i hL) σ).mp (hh.2 i hi hL)
  · intro hh
    constructor
    · intro i
      exact (he _ _ (haH i i.property) (hbH i i.property) σ).mpr (hh.1 i)
    · intro i hi hL
      exact (he _ _ (haP i hL) (hbP i hL) σ).mpr (hh.2 i hi hL)

/- Exact zero at the real uniform law, including bounded coordinate counts. -/
theorem signed_endpoint_zero_uniform (x y : Fin k → G.Slot) (j : Fin G.b)
    (hsize : h+k+Fintype.card (G.Line j) < G.size) :
    (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y Finset.univ ω then
      G.choiceWeight 0 ω*realSign (G.sweep ω) else 0)=0 := by
  let f : Fin h ⊕ Fin k → Cube (G.bits j) × G.Line j := Sum.elim
    (fun i => (H.path i j.succ j,fun t => H.path i j.castSucc t))
    (fun i => (y i j,G.pathLine (x i) (y i) j))
  have hf : Fintype.card (Fin h ⊕ Fin k)+Fintype.card (G.Line j) <
      Fintype.card (Cube (G.bits j) × G.Line j) := by
    rw [← Fintype.card_congr (Equiv.piSplitAt j (fun t => Cube (G.bits t))),G.card_slot]
    simpa using hsize
  obtain ⟨a,b,L,hab,ha,hb⟩ := exists_two_unassigned f hf
  have hmass : ∀ ω : G.Choices, G.choiceWeight 0 ω=
      G.productLineMass (fun j => FiniteLaw.uniform _) ω := by
    intro ω
    simp [choiceWeight,productLineMass]
  simp_rw [hmass]
  rw [H.signed_endpoint_factorization]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Finset.prod_eq_zero (Finset.mem_univ L)
  apply H.uniform_signed_joint_zero x y j L a b hab
  · intro i hL he
    exact ha (Sum.inl i) (Prod.ext he hL)
  · intro i hL he
    exact hb (Sum.inl i) (Prod.ext he hL)
  · intro i hL he
    exact ha (Sum.inr i) (Prod.ext he hL)
  · intro i hL he
    exact hb (Sum.inr i) (Prod.ext he hL)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.UnitaryIrrep
open SparseDimension
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
def signTwist (ρ : UnitaryIrrep (Equiv.Perm Ω)) : UnitaryIrrep (Equiv.Perm Ω) where
  dimension := ρ.dimension
  positive := ρ.positive
  matrix := {
    toFun g := signScalar g • ρ.matrix g
    map_one' := by simp
    map_mul' g h := by simp only [map_mul,smul_mul_smul_comm] }
  unitary g := by
    change (signScalar g • ρ.matrix g).conjTranspose*(signScalar g • ρ.matrix g)=1
    simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [show star (signScalar g)=signScalar g by simp [signScalar_apply],signScalar_mul_self,one_smul,ρ.unitary]
  irreducible S hS := ρ.irreducible S (by
    intro g v hv
    have hh := S.smul_mem (signScalar g) (hS g v hv)
    change signScalar g • ((signScalar g • ρ.matrix g).mulVec v) ∈ S at hh
    simpa only [Matrix.smul_mulVec,smul_smul,signScalar_mul_self,one_smul] using hh)

@[simp] lemma signTwist_rep (ρ : UnitaryIrrep (Equiv.Perm Ω)) :
    ρ.signTwist.asRepresentation=SparseDimension.signTwist ρ.asRepresentation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change (signScalar g • ρ.matrix g).mulVec v=signScalar g • (ρ.matrix g).mulVec v
  exact Matrix.smul_mulVec _ _ _
end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.PlacementOccurrence
open scoped Matrix.Norms.L2Operator
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]
/- Vanishing on placements transfers to any actually occurring constituent.
No minimum-level condition is needed in the sign-zero branch. -/
omit [DecidableEq I] in
theorem average_zero_of_placement_zero (ρ : UnitaryIrrep (Equiv.Perm Ω))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : I ↪ Ω)
    (hfixed : ∀ g : Equiv.Perm Ω, (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    {W : Type*} [Fintype W] (w : W → ℂ) (g : W → Equiv.Perm Ω)
    (hz : (∑ a : W, w a • actionMatrix (X := I ↪ Ω) (g a))=0) :
    (∑ a : W, w a • ρ.matrix (g a))=0 := by
  let B : Matrix (Fin ρ.dimension) (I ↪ Ω) ℂ := synthesisMatrix ρ u x₀
  have hne : B ≠ 0 := synthesisMatrix_ne_zero ρ u hu x₀ (by
    intro σ hσ
    exact hfixed σ (fun i => congrArg (fun x : I ↪ Ω => x i) hσ))
  have hn := ρ.norm_le_compression (actionMatrix (X := I ↪ Ω)) actionMatrix_unitary B hne
    (synthesisMatrix_covariant ρ u x₀) (∑ a : W, w a • ρ.matrix (g a))
    (∑ a : W, w a • actionMatrix (X := I ↪ Ω) (g a)) (by
      rw [Matrix.sum_mul,Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.smul_mul,Matrix.mul_smul]
      congr 1
      exact ρ.adjoint_intertwines _ actionMatrix_unitary B (synthesisMatrix_covariant ρ u x₀) (g a))
  rw [hz,norm_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
end CoordinateSweeps.PlacementOccurrence

namespace CoordinateSweeps.Grid.Holes
open SparseDimension UnitaryIrrep PlacementOccurrence
variable {G : Grid} {h k : ℕ} (H : G.Holes h)
lemma realSign_freePerm (g : H.stabilizer) :
    realSign (H.stabilizerFreeEquiv g)=realSign g.val := by
  have he : Equiv.Perm.ofSubtype (H.stabilizerFreeEquiv g)=g.val := by
    apply Equiv.ext
    intro x
    by_cases hx : ∀ i, x ≠ H.path i 0
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx]
      rfl
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx]
      push Not at hx
      obtain ⟨i,rfl⟩ := hx
      exact (g.property i).symm
  rw [← he]
  simp [realSign,Equiv.Perm.sign_ofSubtype]

lemma realSign_residualFree (hf : H.Feasible) (ω : {ω : G.Choices // H.Compatible ω}) :
    realSign (H.residualFree hf ω)=realSign (G.sweep (H.reference hf))⁻¹*realSign (G.sweep ω.val) := by
  rw [residualFree,H.realSign_freePerm]
  change realSign ((G.sweep (H.reference hf))⁻¹*G.sweep ω.val)=_
  rw [map_mul]

lemma signed_reference_entry_zero (hf : H.Feasible) (z : ℝ)
    (hzero : ∀ x y : Fin k → G.Slot,
      (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y Finset.univ ω then
        G.choiceWeight z ω*realSign (G.sweep ω) else 0)=0)
    (x y : Fin k ↪ H.FreeAt 0) :
    (∑ ω : {ω : G.Choices // H.Compatible ω},
      if H.residualFree hf ω • x=y then
        (G.choiceWeight z ω.val/H.probability z)*realSign (H.residualFree hf ω) else 0)=0 := by
  have hz := hzero (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val
  have hs : (∑ ω : {ω : G.Choices // H.Compatible ω},
      if H.residualFree hf ω • x=y then G.choiceWeight z ω.val*realSign (G.sweep ω.val) else 0)=0 := by
    calc
      _ = ∑ ω : {ω : G.Choices // H.Compatible ω},
          if G.endpointEvent (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ ω.val then
            G.choiceWeight z ω.val*realSign (G.sweep ω.val) else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [H.endpointEvent_residualFree]
        split_ifs <;> rfl
      _ = ∑ ω : G.Choices, if H.Compatible ω ∧
          G.endpointEvent (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ ω then
            G.choiceWeight z ω*realSign (G.sweep ω) else 0 := by
        rw [sum_subtype_eq_sum_ite_of_iff (fun _ => Iff.rfl)
          (fun ω : G.Choices => if G.endpointEvent (H.inputPlacementEquiv x).val
            (H.outputPlacementEquiv hf y).val Finset.univ ω then
              G.choiceWeight z ω*realSign (G.sweep ω) else 0)]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp_all
      _ = 0 := hz
  calc
    _ = (realSign (G.sweep (H.reference hf))⁻¹/H.probability z)*
        (∑ ω : {ω : G.Choices // H.Compatible ω}, if H.residualFree hf ω • x=y then
          G.choiceWeight z ω.val*realSign (G.sweep ω.val) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      rw [H.realSign_residualFree]
      split_ifs <;> ring
    _ = 0 := by rw [hs,mul_zero]

/- Column cancellation is now on the faithful conditional average, not just
on raw signed endpoint numerators. -/
theorem conditional_zero_of_signed_endpoints (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0)))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) →
      (SparseDimension.signTwist ρ.asRepresentation) g u=u)
    (hzero : ∀ x y : Fin k → G.Slot,
      (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y Finset.univ ω then
        G.choiceWeight z ω*realSign (G.sweep ω) else 0)=0) :
    H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)=0 := by
  let w := fun ω : {ω : G.Choices // H.Compatible ω} =>
    (((G.choiceWeight z ω.val/H.probability z)*realSign (H.residualFree hf ω) : ℝ) : ℂ)
  have he : (∑ ω : {ω : G.Choices // H.Compatible ω},
      w ω • actionMatrix (X := Fin k ↪ H.FreeAt 0) ((H.residualFree hf ω)⁻¹))=0 := by
    ext x y
    simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,actionMatrix_entry,inv_inv,Matrix.zero_apply]
    have hs := H.signed_reference_entry_zero hf z hzero x y
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hs
    simpa only [Complex.ofReal_sum,Complex.ofReal_zero,apply_ite,mul_ite,mul_one,mul_zero] using hc
  have hh := average_zero_of_placement_zero ρ.signTwist u hu x₀
    (by intro g hg; rw [signTwist_rep]; exact hfixed g hg) w
    (fun ω => (H.residualFree hf ω)⁻¹) he
  have hid : (∑ ω : {ω : G.Choices // H.Compatible ω},
      w ω • ρ.signTwist.matrix ((H.residualFree hf ω)⁻¹))=
        (H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)).conjTranspose := by
    rw [H.conditionalAverage_eq_sum,Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro ω _
    change w ω • (signScalar ((H.residualFree hf ω)⁻¹) • ρ.matrix ((H.residualFree hf ω)⁻¹))=_
    rw [smul_smul,Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,ρ.matrix_inv]
    congr 1
    dsimp [w]
    rw [Complex.ofReal_mul]
    have hs : ((realSign (H.residualFree hf ω) : ℝ):ℂ)=signScalar (H.residualFree hf ω) := by
      simp [realSign,signScalar_apply]
    rw [hs,mul_assoc]
    change ((G.choiceWeight z ω.val/H.probability z : ℝ):ℂ)*
      (signScalar (H.residualFree hf ω)*signScalar ((H.residualFree hf ω)⁻¹))=_
    rw [← map_mul,mul_inv_cancel,map_one,mul_one]
  rw [hid] at hh
  have heq := congrArg Matrix.conjTranspose hh
  simp only [Matrix.conjTranspose_conjTranspose] at heq
  exact heq.trans (show (0 : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ).conjTranspose=0 from Matrix.conjTranspose_zero)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep
variable {G : Grid} {h k : ℕ} (H : G.Holes h)
theorem conditional_column_zero_many (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0)
    (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) →
      (SparseDimension.signTwist ρ.asRepresentation) g u=u)
    (j : Fin G.b) (hj : 0 < G.bits j) (hsize : h+k < Fintype.card (G.Line j)) :
    H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)=0 :=
  H.conditional_zero_of_signed_endpoints hf z ρ u hu x₀ hfixed
    (fun x y => H.signed_endpoint_zero_many x y hz hz' j hj hsize)
theorem conditional_column_zero_uniform (hf : H.Feasible)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0)
    (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) →
      (SparseDimension.signTwist ρ.asRepresentation) g u=u)
    (j : Fin G.b) (hsize : h+k+Fintype.card (G.Line j) < G.size) :
    H.conditionalAverage hf 0 (ρ.pullback H.stabilizerFreeEquiv)=0 :=
  H.conditional_zero_of_signed_endpoints hf 0 ρ u hu x₀ hfixed
    (fun x y => H.signed_endpoint_zero_uniform x y j hsize)
end CoordinateSweeps.Grid.Holes

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
