import OAI.Analysis.TreePotential.HilbertCompletion

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

def componentSlice (n : ℕ) : (Node →₀ ℝ) →ₗ[ℝ] (BlockNode n →₀ ℝ) :=
  Finsupp.lcomapDomain (componentEmbedding n) (componentEmbedding n).injective

def componentPart (n : ℕ) (g : Node →₀ ℝ) : Node →₀ ℝ :=
  Finsupp.filter (fun v => v.1=n) g

lemma slice_apply (n : ℕ) (g : Node →₀ ℝ) (v : BlockNode n) :
    componentSlice n g v=g ⟨n,v⟩ := rfl

lemma componentPart_apply (n : ℕ) (g : Node →₀ ℝ) (v : Node) :
    componentPart n g v=if v.1=n then g v else 0 := Finsupp.filter_apply _ _ _

lemma componentPart_eq (n : ℕ) (g : Node →₀ ℝ) :
    componentPart n g=Finsupp.embDomain (componentEmbedding n) (componentSlice n g) := by
  ext v
  by_cases h : v.1=n
  · rcases v with ⟨m,v⟩
    dsimp only at h
    subst m
    rw [componentPart_apply,ite_eq_left rfl]
    exact (Finsupp.embDomain_apply_self (componentEmbedding n) (componentSlice n g) v).symm
  · rw [componentPart_apply,ite_eq_right h]
    symm
    apply Finsupp.embDomain_of_notMem_range
    rintro ⟨w,hw⟩
    exact h (congrArg Sigma.fst hw).symm

lemma componentNorm (n : ℕ) (g : Node →₀ ℝ) :
    testNorm atomTests (componentPart n g)=testNorm (blockTests n) (componentSlice n g) := by
  rw [componentPart_eq,← testNorm_restricted]

lemma Segment.eval_component (S : Segment) (n : ℕ) (g : Node →₀ ℝ) :
    S.eval (componentPart n g)=if S.start.1=n then S.eval g else 0 := by
  unfold Segment.eval
  by_cases h : S.start.1=n
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro v hv
    rw [componentPart_apply,ite_eq_left (((S.mem_nodes v).mp hv).1.1.symm.trans h)]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro v hv
    rw [componentPart_apply,ite_eq_right (fun hvn => h (((S.mem_nodes v).mp hv).1.1.trans hvn))]

lemma predual_family_energy (g : Node →₀ ℝ) (F : Finset Segment) (hF : Incomparable F) :
    (∑ S ∈ F, (S.eval g)^2) ≤ (testNorm atomTests g)^2 := by
  have hh := predual_test_bound g F hF
  have he := Real.sq_sqrt (show 0 ≤ ∑ S ∈ F,(S.eval g)^2 from Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  nlinarith [Real.sqrt_nonneg (∑ S ∈ F,(S.eval g)^2),testNorm_nonneg atomTests g]

lemma predual_norm_le_of_energy (g : Node →₀ ℝ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ F : Finset Segment, Incomparable F → (∑ S ∈ F,(S.eval g)^2) ≤ R^2) :
    testNorm atomTests g ≤ R := by
  apply ciSup_le
  rintro ⟨f,A,rfl⟩
  rw [finitePairing_profile]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq A.family A.coeff (fun S => S.eval g)
  have he := h A.family A.incomparable
  have hab : (A.pairing g)^2 ≤ R^2 := by
    unfold Atom.pairing
    apply hh.trans
    have hn : 0 ≤ ∑ S ∈ A.family,(S.eval g)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact (mul_le_of_le_one_left hn A.budget).trans he
  nlinarith [sq_abs (A.pairing g),abs_nonneg (A.pairing g)]

lemma Incomparable.subset {F G : Finset Segment} (hG : Incomparable G) (hFG : F ⊆ G) : Incomparable F :=
  fun S hS T hT hne => hG S (hFG hS) T (hFG hT) hne

lemma component_families_incomparable (H : Finset ℕ) (F : ℕ → Finset Segment)
    (hF : ∀ n ∈ H, Incomparable (F n)) (hc : ∀ n ∈ H, ∀ S ∈ F n, S.start.1=n) :
    Incomparable (H.biUnion F) := by
  intro S hS T hT hne
  obtain ⟨n,hn,hSn⟩ := Finset.mem_biUnion.mp hS
  obtain ⟨m,hm,hTm⟩ := Finset.mem_biUnion.mp hT
  by_cases hnm : n=m
  · subst m
    exact hF n hn S hSn T hTm hne
  · exact ⟨fun h => hnm ((hc n hn S hSn).symm.trans (h.1.trans (hc m hm T hTm))),
      fun h => hnm ((hc n hn S hSn).symm.trans (h.1.symm.trans (hc m hm T hTm)))⟩

lemma component_families_disjoint (H : Finset ℕ) (F : ℕ → Finset Segment)
    (hc : ∀ n ∈ H, ∀ S ∈ F n, S.start.1=n) : (H : Set ℕ).PairwiseDisjoint F := by
  intro n hn m hm hne
  apply Finset.disjoint_left.mpr
  intro S hSn hSm
  exact hne ((hc n hn S hSn).symm.trans (hc m hm S hSm))

lemma component_family_energy_sum (g : Node →₀ ℝ) (H : Finset ℕ) (F : ℕ → Finset Segment)
    (hF : ∀ n ∈ H, Incomparable (F n)) (hc : ∀ n ∈ H, ∀ S ∈ F n, S.start.1=n) :
    (∑ n ∈ H, ∑ S ∈ F n, (S.eval g)^2) ≤ (testNorm atomTests g)^2 := by
  rw [← Finset.sum_biUnion (component_families_disjoint H F hc)]
  exact predual_family_energy g _ (component_families_incomparable H F hF hc)

lemma component_family_energy (g : Node →₀ ℝ) (n : ℕ) (F : Finset Segment) (hF : Incomparable F) :
    (∑ S ∈ F.filter (fun S => S.start.1=n), (S.eval g)^2) ≤
      (testNorm atomTests (componentPart n g))^2 := by
  have hh := predual_family_energy (componentPart n g) (F.filter (fun S => S.start.1=n))
    (hF.subset (Finset.filter_subset _ _))
  convert hh using 1
  exact Finset.sum_congr rfl (fun S hS => by rw [Segment.eval_component,ite_eq_left (Finset.mem_filter.mp hS).2])

lemma eval_zero_outside_components (g : Node →₀ ℝ) (H : Finset ℕ) (hg : ∀ v ∈ g.support, v.1 ∈ H)
    (S : Segment) (hS : S.start.1 ∉ H) : S.eval g=0 := by
  apply Finset.sum_eq_zero
  intro v hv
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  exact hS (((S.mem_nodes v).mp hv).1.1 ▸ hg v hmem)

lemma predual_norm_sq_le_components (g : Node →₀ ℝ) (H : Finset ℕ)
    (hg : ∀ v ∈ g.support, v.1 ∈ H) :
    (testNorm atomTests g)^2 ≤ ∑ n ∈ H, (testNorm atomTests (componentPart n g))^2 := by
  let B := ∑ n ∈ H, (testNorm atomTests (componentPart n g))^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have htest : testNorm atomTests g ≤ Real.sqrt B := by
    apply predual_norm_le_of_energy g (Real.sqrt_nonneg _)
    intro F hF
    rw [Real.sq_sqrt hB]
    have he : (∑ S ∈ F, (S.eval g)^2) =
        ∑ n ∈ H, ∑ S ∈ F.filter (fun S => S.start.1=n), (S.eval g)^2 := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hn : S.start.1 ∈ H
      · simp [hn]
      · simp [eval_zero_outside_components g H hg S hn]
    rw [he]
    exact Finset.sum_le_sum (fun n hn => component_family_energy g n F hF)
  change (testNorm atomTests g)^2 ≤ B
  nlinarith [Real.sq_sqrt hB,testNorm_nonneg atomTests g,Real.sqrt_nonneg B]

namespace Atom

def component (A : Atom) (n : ℕ) : Atom where
  family := A.family.filter (fun S => S.start.1=n)
  incomparable := A.incomparable.subset (Finset.filter_subset _ _)
  coeff := A.coeff
  budget := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)).trans A.budget

lemma component_pairing (A : Atom) (n : ℕ) (g : Node →₀ ℝ) :
    (A.component n).pairing g=A.pairing (componentPart n g) := by
  simp only [pairing,component,Finset.sum_filter,Segment.eval_component,mul_ite,mul_zero]

lemma pairing_sq_le_energy (A : Atom) (g : Node → ℝ) :
    (A.pairing g)^2 ≤ ∑ S ∈ A.family,(S.eval g)^2 := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq A.family A.coeff (fun S => S.eval g)
  exact hh.trans (mul_le_of_le_one_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) A.budget)

end Atom

lemma component_atom_pairings_sq (g : Node →₀ ℝ) (H : Finset ℕ) (A : ℕ → Atom) :
    (∑ n ∈ H, ((A n).pairing (componentPart n g))^2) ≤ (testNorm atomTests g)^2 := by
  have hb := Finset.sum_le_sum (s:=H) (fun n _ => ((A n).component n).pairing_sq_le_energy g)
  simp only [Atom.component_pairing] at hb
  apply hb.trans
  apply component_family_energy_sum
  · exact fun n _ => ((A n).component n).incomparable
  · intro n hn S hS
    exact (Finset.mem_filter.mp hS).2

lemma exists_atom_near_norm (g : Node →₀ ℝ) {e : ℝ} (he : 0 < e) :
    ∃ A : Atom, testNorm atomTests g-e < |A.pairing g| := by
  have hh : testNorm atomTests g-e < testNorm atomTests g := by linarith
  obtain ⟨⟨f,A,hA⟩,hf⟩ := (lt_ciSup_iff (testNorm_bddAbove atomTests g)).mp hh
  subst f
  rw [finitePairing_profile] at hf
  exact ⟨A,hf⟩

lemma components_norm_sq_le_predual (g : Node →₀ ℝ) (H : Finset ℕ) :
    (∑ n ∈ H, (testNorm atomTests (componentPart n g))^2) ≤ (testNorm atomTests g)^2 := by
  let b : ℕ → ℝ := fun n => testNorm atomTests (componentPart n g)
  let C := ∑ n ∈ H,b n
  have hb : ∀ n, 0 ≤ b n := fun n => testNorm_nonneg _ _
  have hC : 0 ≤ C := Finset.sum_nonneg (fun n _ => hb n)
  apply le_of_forall_pos_le_add
  intro e he
  let d := e/(2*C+1)
  have hd : 0 < d := div_pos he (by positivity)
  choose A hA using fun n => exists_atom_near_norm (componentPart n g) hd
  have ha : ∀ n, |(A n).pairing (componentPart n g)| ≤ b n := by
    intro n
    simpa only [finitePairing_profile] using finitePairing_le_testNorm atomTests
      ⟨(A n).profile,⟨A n,rfl⟩⟩ (componentPart n g)
  have hs : (∑ n ∈ H,(b n)^2) ≤
      (∑ n ∈ H,((A n).pairing (componentPart n g))^2)+2*d*C := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have hclose := hA n
    change b n-d < _ at hclose
    have hu := ha n
    have hsq := sq_nonneg (b n-|(A n).pairing (componentPart n g)|)
    nlinarith [sq_abs ((A n).pairing (componentPart n g)),abs_nonneg ((A n).pairing (componentPart n g)),hb n]
  have henergy := component_atom_pairings_sq g H A
  have heq : d*(2*C+1)=e := div_mul_cancel₀ e (by positivity)
  change (∑ n ∈ H,(b n)^2) ≤ (testNorm atomTests g)^2+e
  linarith

/-- Exact finite-array orthogonal sum identity, with no uniform height bound.
All trees retain their heights and their root coordinates. -/
theorem predual_components_norm_sq (g : Node →₀ ℝ) (H : Finset ℕ)
    (hg : ∀ v ∈ g.support, v.1 ∈ H) :
    (testNorm atomTests g)^2=∑ n ∈ H, (testNorm (blockTests n) (componentSlice n g))^2 := by
  simp only [← componentNorm]
  exact le_antisymm (predual_norm_sq_le_components g H hg) (components_norm_sq_le_predual g H)

end BoundedTreePotentials.Segments

namespace BoundedTreePotentials
/-- The canonical c00 inclusion, used for each of the exact test families. -/
def finiteLift {I : Type*} (K : TestFamily I) : (I →₀ ℝ) →ₗ[ℝ] TestCompletion K :=
  UniformSpace.Completion.toComplL.toLinearMap.comp (testVectorEquiv K).symm.toLinearMap

lemma finiteLift_norm {I : Type*} (K : TestFamily I) (g : I →₀ ℝ) :
    ‖finiteLift K g‖=testNorm K g := UniformSpace.Completion.norm_coe ((testVectorEquiv K).symm g)

end BoundedTreePotentials

namespace BoundedTreePotentials.Segments

def componentSupport (g : Node →₀ ℝ) : Finset ℕ := g.support.image Sigma.fst

lemma mem_componentSupport (g : Node →₀ ℝ) (v : Node) (hv : v ∈ g.support) : v.1 ∈ componentSupport g :=
  Finset.mem_image.mpr ⟨v,hv,rfl⟩

lemma slice_zero_outside (g : Node →₀ ℝ) {n : ℕ} (hn : n ∉ componentSupport g) : componentSlice n g=0 := by
  ext v
  rw [slice_apply,Finsupp.zero_apply]
  apply Finsupp.notMem_support_iff.mp
  intro hv
  exact hn (mem_componentSupport g ⟨n,v⟩ hv)

lemma finiteComponents_mem (g : Node →₀ ℝ) :
    Memℓp (fun n => finiteLift (blockTests n) (componentSlice n g)) 2 := by
  apply Memℓp.of_exponent_ge (p:=2) (q:=0) _ (by norm_num)
  apply memℓp_zero
  apply (componentSupport g).finite_toSet.subset
  intro n hn
  by_contra hh
  have hz := slice_zero_outside g hh
  exact hn (by rw [hz,map_zero])

def finiteComponents : (Node →₀ ℝ) →ₗ[ℝ] HilbertSum PredualBlock where
  toFun g := ⟨(fun n => finiteLift (blockTests n) (componentSlice n g)),finiteComponents_mem g⟩
  map_add' g h := by
    apply Subtype.ext
    funext n
    change finiteLift (blockTests n) (componentSlice n (g+h))=_
    simp only [map_add]
    rfl
  map_smul' a g := by
    apply Subtype.ext
    funext n
    change finiteLift (blockTests n) (componentSlice n (a • g))=_
    simp only [map_smul]
    rfl

lemma finiteComponents_apply (g : Node →₀ ℝ) (n : ℕ) :
    finiteComponents g n=finiteLift (blockTests n) (componentSlice n g) := rfl

lemma finiteComponents_norm (g : Node →₀ ℝ) : ‖finiteComponents g‖=testNorm atomTests g := by
  have hs : HasSum (fun n => ‖finiteComponents g n‖^2)
      (∑ n ∈ componentSupport g,(testNorm (blockTests n) (componentSlice n g))^2) := by
    simp only [finiteComponents_apply,finiteLift_norm]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [slice_zero_outside g hn,testNorm_zero]
    norm_num
  have hh : HasSum (fun n => ‖finiteComponents g n‖^2) (‖finiteComponents g‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p:=2) (by norm_num) (finiteComponents g)
  have he := predual_components_norm_sq g (componentSupport g) (mem_componentSupport g)
  have hn := hh.unique hs
  nlinarith [norm_nonneg (finiteComponents g),testNorm_nonneg atomTests g]

def finiteComponentIsometry : TestVector atomTests →ₗᵢ[ℝ] HilbertSum PredualBlock where
  toLinearMap := finiteComponents.comp (testVectorEquiv atomTests).toLinearMap
  norm_map' := fun g => finiteComponents_norm ((testVectorEquiv atomTests) g)

def completedComponents : Predual →L[ℝ] HilbertSum PredualBlock :=
  finiteComponentIsometry.toContinuousLinearMap.extend UniformSpace.Completion.toComplL

lemma completedComponents_coe (g : TestVector atomTests) :
    completedComponents g=finiteComponents ((testVectorEquiv atomTests) g) := by
  exact finiteComponentIsometry.toContinuousLinearMap.extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformEmbedding_coe _).isUniformInducing g

lemma completedComponents_lift (g : Node →₀ ℝ) :
    completedComponents (finiteLift atomTests g)=finiteComponents g :=
  completedComponents_coe ((testVectorEquiv atomTests).symm g)

lemma completedComponents_norm (g : Predual) : ‖completedComponents g‖=‖g‖ := by
  refine UniformSpace.Completion.induction_on g
    (isClosed_eq completedComponents.continuous.norm continuous_norm) ?_
  intro w
  rw [completedComponents_coe,UniformSpace.Completion.norm_coe]
  exact finiteComponents_norm ((testVectorEquiv atomTests) w)

def componentIsometry : Predual →ₗᵢ[ℝ] HilbertSum PredualBlock where
  toLinearMap := completedComponents.toLinearMap
  norm_map' := completedComponents_norm

lemma finiteComponents_emb (n : ℕ) (g : BlockNode n →₀ ℝ) :
    finiteComponents (Finsupp.embDomain (componentEmbedding n) g)=lp.single 2 n (finiteLift (blockTests n) g) := by
  apply Subtype.ext
  funext m
  change finiteLift (blockTests m) (componentSlice m (Finsupp.embDomain (componentEmbedding n) g)) =
    (lp.single (E:=PredualBlock) 2 n (finiteLift (blockTests n) g)) m
  by_cases hm : m=n
  · subst m
    have he : componentSlice n (Finsupp.embDomain (componentEmbedding n) g)=g := by
      ext v
      rw [slice_apply]
      exact Finsupp.embDomain_apply_self (componentEmbedding n) g v
    rw [he]
    simp [lp.single_apply]
  · have he : componentSlice m (Finsupp.embDomain (componentEmbedding n) g)=0 := by
      ext v
      rw [slice_apply,Finsupp.zero_apply]
      apply Finsupp.embDomain_of_notMem_range
      rintro ⟨w,hw⟩
      exact hm (congrArg Sigma.fst hw).symm
    rw [he,map_zero,lp.single_apply,Pi.single_eq_of_ne hm]

lemma completedComponents_surjective : Function.Surjective completedComponents := by
  have hc : IsClosed (Set.range completedComponents) :=
    componentIsometry.isometry.antilipschitzWith.isClosed_range completedComponents.uniformContinuous
  have hsingle (n : ℕ) (x : PredualBlock n) : lp.single 2 n x ∈ Set.range completedComponents := by
    refine UniformSpace.Completion.induction_on x
      (hc.preimage (lp.singleContinuousLinearMap ℝ PredualBlock 2 n).continuous) ?_
    intro g
    refine ⟨finiteLift atomTests (Finsupp.embDomain (componentEmbedding n) ((testVectorEquiv (blockTests n)) g)),?_⟩
    rw [completedComponents_lift,finiteComponents_emb]
    rfl
  intro x
  apply hc.mem_of_tendsto (lp.hasSum_single (p:=2) (by norm_num) x)
  filter_upwards [] with S
  change (∑ n ∈ S,lp.single 2 n (x n)) ∈ completedComponents.range
  apply Submodule.sum_mem
  intro n hn
  exact hsingle n (x n)

/-- Exact ℓ₂ decomposition of the completed predual into completed blocks. -/
def predualComponentEquiv : Predual ≃ₗᵢ[ℝ] HilbertSum PredualBlock :=
  LinearIsometryEquiv.ofSurjective componentIsometry completedComponents_surjective

theorem predual_reflexive : IsReflexive Predual :=
  reflexive_equiv predualComponentEquiv.toContinuousLinearEquiv
    (hilbertSum_reflexive PredualBlock predualBlock_reflexive)

end BoundedTreePotentials.Segments

end

end OAI
