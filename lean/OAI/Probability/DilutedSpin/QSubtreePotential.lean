import OAI.Probability.DilutedSpin.FiniteEncoding
import OAI.Probability.DilutedSpin.SubsetTree

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

lemma asProbability_id_singleton [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : FiniteLaw Ω) (a : Ω) : (P.asProbability id).toMeasure {a} = ENNReal.ofReal (P.weight a) := by
  classical
  simp [asProbability, atomicProbability, nnWeights, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton a), Pi.single_apply]
  exact ENNReal.ofReal_coe_nnreal.symm

lemma asProbability_eq_map [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {X : Type*} [MeasurableSpace X] (P : FiniteLaw Ω) (f : Ω → X) :
    (P.asProbability f).toMeasure = Measure.map f (P.asProbability id).toMeasure := by
  classical
  have hf : Measurable f := measurable_of_countable f
  simp only [asProbability, atomicProbability]
  change (∑ a, ((P.nnWeights).val a : ℝ≥0∞) • Measure.dirac (f a)) =
    Measure.map f (∑ a, ((P.nnWeights).val a : ℝ≥0∞) • Measure.dirac a)
  rw [Measure.map_finset_sum hf.aemeasurable]
  simp only [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]

lemma asProbability_pi {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → X i) :
    ((pi Q).asProbability (fun x i => f i (x i))).toMeasure =
      Measure.pi (fun i => ((Q i).asProbability (f i)).toMeasure) := by
  classical
  let (index : ι) : MeasurableSpace (α index) := ⊤
  let (index : ι) : MeasurableSingletonClass (α index) := ⟨fun _ => trivial⟩
  have he : ((pi Q).asProbability id).toMeasure =
      Measure.pi (fun i => ((Q i).asProbability id).toMeasure) := by
    apply Measure.ext_of_singleton
    intro x
    simp only [asProbability_id_singleton, Measure.pi_singleton]
    change ENNReal.ofReal (∏ i, (Q i).weight (x i)) = _
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (Q i).nonneg _)]
  rw [asProbability_eq_map, he, Measure.pi_map_pi (fun i =>
    (measurable_of_countable (f i)).aemeasurable)]
  simp_rw [← asProbability_eq_map]

lemma integral_pi_asProbability {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → X i)
    (g : ((i : ι) → X i) → ℝ) :
    (∫ x, g x ∂Measure.pi (fun i => ((Q i).asProbability (f i)).toMeasure)) =
      (pi Q).expect (fun a => g (fun i => f i (a i))) := by
  rw [← asProbability_pi, integral_asProbability]

end FiniteLaw
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n N : ℕ} {Ω : Type} [Fintype Ω]

noncomputable def subsetOverlap (T : PrescribedTree n) (A : Finset T.Leaf)
    (V : FinitePath Ω n → Fin N → ℝ) (w : Sample Ω T) : ℝ :=
  (∑ i, ∏ a∈A, V (T.pathAt a w) i)/(N:ℝ)

lemma SplitMap.prod_range {U T : PrescribedTree n} (f : SplitMap U T)
    (A : Finset T.Leaf) (hA : ∀ b, (∃ a, f.leaf a=b) ↔ b∈A) (g : T.Leaf → ℝ) :
    (∏ a : U.Leaf, g (f.leaf a))=∏ b∈A, g b := by
  classical
  apply Finset.prod_bij (fun a _ => f.leaf a)
  · intro a _; exact (hA _).mp ⟨a,rfl⟩
  · intro a _ b _ he; exact f.injective he
  · intro b hb
    obtain ⟨a,ha⟩ := (hA b).mpr hb
    exact ⟨a,Finset.mem_univ _,ha⟩
  · intro a _; rfl

lemma SplitMap.expect_subsetOverlap {U T : PrescribedTree n} (f : SplitMap U T)
    (A : Finset T.Leaf) (hA : ∀ b, (∃ a, f.leaf a=b) ↔ b∈A)
    (K : KernelTower Ω n) (V : FinitePath Ω n → Fin N → ℝ) (g : ℝ → ℝ) :
    (T.sampleLaw K).expect (fun w => g (subsetOverlap T A V w))=
      (U.sampleLaw K).expect (fun w => g (treeOverlap U V w)) := by
  have he := f.expect_paths K (fun x => g ((∑ i, ∏ a : U.Leaf, V (x a) i)/(N:ℝ)))
  simp_rw [subsetOverlap,treeOverlap,leafProduct_eq_prod]
  convert he using 1
  apply FiniteLaw.expect_congr
  intro w
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact (f.prod_range A hA (fun b => V (T.pathAt b w) i)).symm

omit [Fintype Ω] in
lemma subsetOverlap_bound (T : PrescribedTree n) (A : Finset T.Leaf)
    (V : FinitePath Ω n → Fin N → ℝ) (hV : ∀ x i, |V x i|≤1) (w : Sample Ω T) :
    |subsetOverlap T A V w|≤1 := by
  have hh := FiniteLaw.abs_dot_le_one (fun i => ∏ a∈A, V (T.pathAt a w) i) (fun _ => (1:ℝ))
    (fun index => by rw [Finset.abs_prod]; exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => hV _ index))
    (fun _ => by norm_num)
  simpa only [FiniteLaw.dot,subsetOverlap,mul_one] using hh

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage
open scoped BigOperators
noncomputable local instance qSubtreePotentialDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
noncomputable local instance qSubtreePotentialPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

lemma qEmbed_realize_le {L : ℕ} (hL : 0<L) (k : ℕ) (S : ReducedTopology)
    (q : S.Vertex → Fin L) (hq : S.Admissible (fun v => q v) 0 L) :
    qExpect (grid L 0 L) (fun T => if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then 1 else 0)
      k (single L) ≤ shapeCharge k S * (L:ℝ)⁻¹^(Fintype.card S.Vertex) := by
  let Q : Finset ℕ := Finset.univ.image (fun v => (q v).val)
  have hQ : Q.card ≤ Fintype.card S.Vertex := (Finset.card_image_le).trans_eq (Finset.card_univ)
  have hb : branchingCount (S.realize L 0 (fun v => q v)) (·∈Q)=Fintype.card S.Vertex := by
    have h := S.realize_branchingCount L 0 (fun v => q v) (by simpa using hq) (·∈Q)
    have hm (v : S.Vertex) : (q v).val∈Q := Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
    simpa only [Nat.zero_add,hm,ite_true,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using h
  apply le_trans (b := qExpect (grid L 0 L) (fun T =>
    if branchingCount (single L) (·∈Q)+Fintype.card S.Vertex ≤ branchingCount T (·∈Q) then 1 else 0) k (single L))
  · apply qExpect_mono _ (grid_strictMono hL).monotone grid_nonneg
    intro T
    by_cases he : Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T)
    · obtain ⟨f⟩ := he
      have ht := f.branchingCount_le (·∈Q)
      rw [hb] at ht
      have hf : Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) := ⟨f⟩
      simp only [ite_eq_left hf,branchingCount_single,zero_add,ite_eq_left ht,le_refl]
    · rw [ite_eq_right he]
      split_ifs <;> norm_num
  apply (qExpect_grid_branching hL Q k (Fintype.card S.Vertex) (single L)).trans
  rw [leaves_single]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply chargeBound_mono (by positivity) (by positivity) le_rfl
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hQ) (Nat.cast_nonneg _)

noncomputable def subtreePotential {L : ℕ} (K : ℕ) (F : PrescribedTree L → ℝ) (T : PrescribedTree L) : ℝ :=
  ∑ S∈boundedTopologies K, ∑ q : S.Vertex → Fin L,
    if S.Admissible (fun v => q v) 0 L then
      if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then F (S.realize L 0 (fun v => q v)) else 0
    else 0

lemma subtreePotential_nonneg {L K : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ T, 0≤F T) (T) :
    0≤ subtreePotential K F T := by
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> first | exact hF _ | rfl

lemma le_subtreePotential {L K : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ T, 0≤F T)
    {U T : PrescribedTree L} (f : SplitMap U T) (hU : U.leaves≤K) : F U≤ subtreePotential K F T := by
  obtain ⟨S,hS,q,hq,he⟩ := ReducedTopology.exists_bounded_realize U K hU
  subst U
  unfold subtreePotential
  have hn (R : ReducedTopology) (v : R.Vertex → Fin L) :
      0≤(if R.Admissible (fun w => v w) 0 L then
        if Nonempty (SplitMap (R.realize L 0 (fun w => v w)) T) then F (R.realize L 0 (fun w => v w)) else 0 else 0) := by
    split_ifs <;> first | exact hF _ | rfl
  apply le_trans (b := ∑ q : S.Vertex → Fin L, if S.Admissible (fun v => q v) 0 L then
    if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then F (S.realize L 0 (fun v => q v)) else 0 else 0)
  · have hh := Finset.single_le_sum (fun (v : S.Vertex → Fin L) (_ : v∈Finset.univ) => hn S v) (Finset.mem_univ q)
    simpa only [ite_eq_left hq,ite_eq_left (show Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) from ⟨f⟩)] using hh
  · exact Finset.single_le_sum (fun (R : ReducedTopology) (_ : R∈boundedTopologies K) =>
      Finset.sum_nonneg (s := Finset.univ) (fun (v : R.Vertex → Fin L) _ => hn R v)) hS

lemma qExpect_subtree_depth_bound {L : ℕ} [NeZero L] (K k : ℕ)
    (F : PrescribedTree L → ℝ) (hF : ∀ T, 0≤F T) :
    qExpect (grid L 0 L) (subtreePotential K F) k (single L) ≤
      ∑ S∈boundedTopologies K, shapeCharge k S *
        average (fun q : S.Vertex → Fin L => S.Admissible (fun v => q v) 0 L)
          (fun q => F (S.realize L 0 (fun v => q v))) := by
  unfold subtreePotential
  rw [qExpect_sum]
  apply Finset.sum_le_sum
  intro S _
  rw [qExpect_sum,← weighted_sum_eq_average]
  apply Finset.sum_le_sum
  intro q _
  by_cases hq : S.Admissible (fun v => q v) 0 L
  · simp only [hq,ite_true]
    have he : (fun T => if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then F (S.realize L 0 (fun v => q v)) else 0)=
        (fun T => (if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then 1 else 0)*F (S.realize L 0 (fun v => q v))) := by
      funext T; split_ifs <;> simp
    rw [he,qExpect_mul_const]
    exact mul_le_mul_of_nonneg_right (qEmbed_realize_le (NeZero.pos L) k S q hq) (hF _)
  · have hroot : grid L 0 L 0=0 := by simp [grid]
    simp only [hq,ite_false,qExpect_const _ hroot (grid_last (NeZero.pos L)),le_refl]

lemma qExpect_subtree_regular_bound {L : ℕ} [NeZero L] (K k : ℕ)
    (F : PrescribedTree L → ℝ) (h0 : ∀ T, 0≤F T) (h1 : ∀ T, F T≤1)
    {η : ℝ} {r : ℕ} (hηr : η*(L:ℝ)≤r) :
    qExpect (grid L 0 L) (subtreePotential K F) k (single L) ≤
      ∑ S∈boundedTopologies K, shapeCharge k S *
        (average (regularOverlapDomain S L η) (fun q => F (S.realize L 0 (fun v => q v)))+
          shapeBadConstant S*(2*(r+1:ℕ):ℝ)/(L:ℝ)) := by
  apply (qExpect_subtree_depth_bound K k F h0).trans
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (shapeCharge_nonneg k S)
  apply (average_split_regular_le _ _ (fun q => h0 _) (fun q => h1 _) η).trans
  exact add_le_add le_rfl (nonregular_average_bound hηr)

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
local instance qSubtreePotentialMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance qSubtreePotentialBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma logMean_constant {ι : Type} [Fintype ι] (r : ℕ) (c : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i,m i≠0) (eta : ι → Hierarchy r) :
    logMean r (fun _ : ι → ℝ => c) m eta = c := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ι → ProbabilityMeasure (Hierarchy r) at eta
    simp only [logMean,ih (fun i => m i.succ) (fun i => hm i.succ),integral_const,
      probReal_univ,smul_eq_mul,one_mul,Real.log_exp]
    exact mul_div_cancel_left₀ c (hm 0)

lemma trialLog_constant {ι : Type} [Fintype ι] (r : ℕ) (c : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i,m i≠0) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun _ : ι → ℝ => c) = c := by
  change ProbabilityMeasure (Hierarchy r) at ζ
  simp [trialLog,logMean_constant r c m hm]

lemma trialLog_sum_separate {ι κ : Type} [Fintype ι] [Fintype κ]
    (r : ℕ) (f : (ι → ℝ) → ℝ) (g : (κ → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g) {B C : ℝ}
    (hb : ∀ x,|f x|≤B) (hc : ∀ x,|g x|≤C)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x : ι ⊕ κ → ℝ => f (fun i => x (.inl i))+g (fun j => x (.inr j))) =
      trialLog r ζ m f+trialLog r ζ m g := by
  change ProbabilityMeasure (Hierarchy r) at ζ
  unfold trialLog
  simp_rw [logMean_sum_separate r f g hf hg hb hc m hm]
  obtain ⟨hfc,hfb⟩ := logMean_continuous_bound r f hf hb m hm
  obtain ⟨hgc,hgb⟩ := logMean_continuous_bound r g hg hc m hm
  have hfi := MeasureMean.bounded_integrable (Measure.pi (fun _ : ι => ζ.toMeasure)) hfc.measurable hfb
  have hgi := MeasureMean.bounded_integrable (Measure.pi (fun _ : κ => ζ.toMeasure)) hgc.measurable hgb
  have he := (measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => ζ.toMeasure)).integral_comp'
    (fun z : (ι → Hierarchy r) × (κ → Hierarchy r) => logMean r f m z.1+logMean r g m z.2)
  rw [integral_add (hfi.comp_fst (Measure.pi (fun _ : κ => ζ.toMeasure)))
      (hgi.comp_snd (Measure.pi (fun _ : ι => ζ.toMeasure))) ] at he
  simpa only [MeasurableEquiv.coe_sumPiEquivProdPi,Equiv.sumPiEquivProdPi_apply,
    integral_fun_fst,integral_fun_snd,probReal_univ,one_smul] using he

/-- A label block split at its first interaction occurrence. -/
def blockSuccEquiv (ι : Type) (k : ℕ) : ι ⊕ (Fin k × ι) ≃ Fin (k+1) × ι where
  toFun := Sum.elim (fun i => (0,i)) (fun z => (z.1.succ,z.2))
  invFun := fun z => Fin.cases (.inl z.2) (fun j => .inr (j,z.2)) z.1
  left_inv := by intro z; cases z <;> simp
  right_inv := by rintro ⟨j,i⟩; refine Fin.cases ?_ (fun j => ?_) j <;> simp

lemma trialLog_blocks {ι : Type} [Fintype ι] (r k : ℕ)
    (g : Fin k → (ι → ℝ) → ℝ) (hg : ∀ j,Continuous (g j))
    (B : Fin k → ℝ) (hb : ∀ j x,|g j x|≤B j)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x : Fin k × ι → ℝ => ∑ j,g j (fun i => x (j,i))) =
      ∑ j,trialLog r ζ m (g j) := by
  induction k with
  | zero => simpa using trialLog_constant (ι := Fin 0 × ι) r 0 m (fun i => (hm i).ne') ζ
  | succ k ih =>
    let v := fun x : Fin k × ι → ℝ => ∑ j,g j.succ (fun i => x (j,i))
    have hv : Continuous v := continuous_finsetSum _ (fun j _ =>
      (hg j.succ).comp (continuous_pi (fun i => continuous_apply (j,i))))
    have hvb (x : Fin k × ι → ℝ) : |v x|≤∑ j : Fin k,B j.succ :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hb j.succ _))
    have he := trialLog_reindex (blockSuccEquiv ι k) r
      (fun x : ι ⊕ (Fin k×ι) → ℝ => g 0 (fun i => x (.inl i))+v (fun j => x (.inr j))) m ζ
    have hh : (fun x : Fin (k+1) × ι → ℝ =>
        g 0 (fun i => x (blockSuccEquiv ι k (.inl i)))+
          v (fun j => x (blockSuccEquiv ι k (.inr j)))) =
        fun x => ∑ j,g j (fun i => x (j,i)) := by
      funext x
      simp only [blockSuccEquiv,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr,v,Fin.sum_univ_succ]
    rw [hh] at he
    rw [he,trialLog_sum_separate r (g 0) v (hg 0) hv (hb 0) hvb m hm ζ,
      ih (fun j => g j.succ) (fun j => hg j.succ) (fun j => B j.succ) (fun j => hb j.succ),Fin.sum_univ_succ]

end DilutedSpinGlass

end

end OAI
