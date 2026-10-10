import OAI.Analysis.DiamondDistortion.Incomparable

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace RecursiveModel
instance countableCoord (h : ℕ) : Countable (Coord h) := by
  induction h with
  | zero => exact inferInstanceAs (Countable Unit)
  | succ h ih => exact inferInstanceAs (Countable (Unit ⊕ (ℕ × Coord h)))

lemma aggregate_sq {ι : Type*} (f : ι →₀ ℝ) :
    (aggregate 2 f)^2=∑ i ∈ f.support,f i^2 := by
  have hh := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (finiteLp 2 f)
  have he : (aggregate 2 f)^2=∑' i,f i^2 := by
    simpa only [aggregate,ENNReal.toReal_ofNat,Real.rpow_two,finiteLp_apply,Real.norm_eq_abs,sq_abs] using hh
  rw [he]
  exact tsum_eq_sum (fun i hi => by rw [Finsupp.notMem_support_iff.mp hi]; norm_num)

lemma components_zero (p : ForestVec) (h : ℕ) (hh : h ∉ p.support.image Sigma.fst) :
    components p h=0 := by
  ext i
  change p ⟨h,i⟩=0
  apply Finsupp.notMem_support_iff.mp
  intro hi
  exact hh (Finset.mem_image.mpr ⟨⟨h,i⟩,hi,rfl⟩)

lemma outer_support (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p : ForestVec) :
    (outerValues s p).support ⊆ p.support.image Sigma.fst := by
  intro h hh
  by_contra hn
  have he : outerValues s p h=0 := by rw [outerValues_apply,components_zero p h hn,map_zero]
  exact (Finsupp.mem_support_iff.mp hh) he

lemma outer_sq (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p : ForestVec) (C : Finset ℕ)
    (hC : p.support.image Sigma.fst ⊆ C) :
    (outerSeminorm s p)^2=∑ h ∈ C,(s h (components p h))^2 := by
  change (aggregate 2 (outerValues s p))^2=_
  rw [aggregate_sq]
  apply Finset.sum_subset ((outer_support s p).trans hC)
  intro h _ hh
  rw [Finsupp.notMem_support_iff.mp hh]
  norm_num

lemma components_filter (p : ForestVec) (C : Set ℕ) (h : ℕ) :
    components (p.filter (fun i => i.1 ∈ C)) h=if h ∈ C then components p h else 0 := by
  ext i
  by_cases hh : h ∈ C
  · rw [ite_eq_left hh]
    change (p.filter (fun i => i.1 ∈ C)) ⟨h,i⟩=p ⟨h,i⟩
    rw [Finsupp.filter_apply,ite_eq_left hh]
  · rw [ite_eq_right hh]
    change (p.filter (fun i => i.1 ∈ C)) ⟨h,i⟩=0
    rw [Finsupp.filter_apply,ite_eq_right hh]

lemma outer_contractive (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p : ForestVec) (C : Set ℕ) :
    outerSeminorm s (p.filter (fun i => i.1 ∈ C)) ≤ outerSeminorm s p := by
  apply aggregate_mono 2
  · exact outerValues_nonneg s _
  · intro h
    rw [outerValues_apply,outerValues_apply,components_filter]
    split_ifs
    · exact le_rfl
    · rw [map_zero]; exact apply_nonneg _ _

lemma outer_orthogonal (s : ∀ h,Seminorm ℝ (Vec (h+1))) (p q : ForestVec)
    (hd : Disjoint (p.support.image Sigma.fst) (q.support.image Sigma.fst)) :
    (outerSeminorm s (p+q))^2 ≤ (outerSeminorm s p)^2+(outerSeminorm s q)^2 := by
  let C := p.support.image Sigma.fst ∪ q.support.image Sigma.fst
  have hp : p.support.image Sigma.fst ⊆ C := Finset.subset_union_left
  have hq : q.support.image Sigma.fst ⊆ C := Finset.subset_union_right
  have hpq : (p+q).support.image Sigma.fst ⊆ C := by
    intro h hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
    · exact hp (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · exact hq (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  rw [outer_sq s p C hp,outer_sq s q C hq,outer_sq s (p+q) C hpq,← Finset.sum_add_distrib]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro h _
  rw [map_add,DFinsupp.add_apply]
  by_cases hh : h ∈ p.support.image Sigma.fst
  · have hhq := Finset.disjoint_left.mp hd hh
    rw [components_zero q h hhq,add_zero,map_zero,zero_pow (by decide : 2 ≠ 0),add_zero]
  · rw [components_zero p h hh,zero_add,map_zero,zero_pow (by decide : 2 ≠ 0),zero_add]

lemma energy_components (p : ForestVec) (C : Finset ℕ) (hC : p.support.image Sigma.fst ⊆ C) :
    (∑ i ∈ p.support,p i^2)=∑ h ∈ C,∑ i ∈ (components p h).support,(components p h i)^2 := by
  have he (h : ℕ) : p.split h=components p h := by ext i; rw [Finsupp.split_apply]; rfl
  have hh := p.sigma_sum (fun _ a => a^2)
  simp only [Finsupp.sum,he] at hh
  rw [hh]
  have hes : p.splitSupport=p.support.image Sigma.fst := by
    ext h
    simp only [Finsupp.splitSupport,Finset.mem_image]
  rw [hes]
  apply Finset.sum_subset hC
  intro h _ hh
  have hzero := components_zero p h hh
  rw [hzero,Finsupp.support_zero,Finset.sum_empty]

end RecursiveModel

namespace PathModel
open RecursiveModel
lemma path_norm (h : ℕ) (μ : L1 h) : ‖path h μ‖ ≤ (h+1:ℝ)*‖μ‖ := by
  have hb : ‖path h‖ ≤ (h+1:ℝ) :=
    LinearMap.mkContinuous_norm_le _ (by positivity : (0:ℝ) ≤ h+1) _
  exact ((path h).le_opNorm μ).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma linear_l2 (h : ℕ) (v : L2 h) : ‖v‖ ≤ (h+1:ℝ)*cost 1 h v := by
  apply (presentation 1 h).bound v (by positivity : (0:ℝ) ≤ h+1)
  intro d hd
  change d.fst+path h d.snd=v at hd
  rw [← hd,WithLp.prod_norm_eq_of_L1]
  have hb := (norm_add_le d.fst (path h d.snd)).trans (add_le_add le_rfl (path_norm h d.snd))
  have hhn : 1 ≤ (h+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) h]
  have hn := norm_nonneg d.fst
  nlinarith

lemma finite_l2_sq (h : ℕ) (v : Vec h) :
    ‖finiteEmbedding h v‖^2=∑ i ∈ v.support,v i^2 := aggregate_sq v

lemma linear_upper (p : ForestVec) :
    (linearForestSeminorm p)^2 ≤ ∑ i ∈ p.support,p i^2 := by
  let C := p.support.image Sigma.fst
  rw [energy_components p C (by rfl)]
  change (outerSeminorm (fun h => finiteCost 1 (h+1)) p)^2 ≤ _
  rw [outer_sq _ p C (by rfl)]
  apply Finset.sum_le_sum
  intro h _
  rw [← finite_l2_sq]
  exact (sq_le_sq₀ (apply_nonneg _ _) (norm_nonneg _)).mpr (linear_le_norm (h+1) _)

lemma linear_lower (C : Finset ℕ) (p : ForestVec)
    (hp : ∀ i ∈ p.support,i.1 ∈ C) :
    (∑ i ∈ p.support,p i^2) ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+2)^2*(linearForestSeminorm p)^2 := by
  have hC : p.support.image Sigma.fst ⊆ C := by
    rintro _ hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    exact hp i hi
  rw [energy_components p C hC]
  change _ ≤ _*(outerSeminorm (fun h => finiteCost 1 (h+1)) p)^2
  rw [outer_sq _ p C hC,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  rw [← finite_l2_sq]
  have hb := linear_l2 (h+1) (finiteEmbedding _ (components p h))
  have hm : ((h+1:ℕ):ℝ)+1 ≤ ((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+2 := by
    have he : (h:ℝ) ≤ ((C.sup (id : ℕ → ℕ) : ℕ) : ℝ) := by exact_mod_cast Finset.le_sup (f := id) hh
    push_cast
    linarith
  have hpos : 0 ≤ cost 1 (h+1) (finiteEmbedding _ (components p h)) := apply_nonneg _ _
  have hb' := hb.trans (mul_le_mul_of_nonneg_right hm hpos)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb'
  simpa only [mul_pow,finiteCost,Seminorm.comp_apply] using hs

lemma linearBlocks : linearData.HilbertBlocks Sigma.fst where
  orthogonal p q hd := outer_orthogonal _ p q (by
    simpa only [Finset.disjoint_left,Finset.mem_image] using hd)
  contractive := outer_contractive _
  upper C := ⟨1,by norm_num,fun p _ => by simpa only [linearData,one_mul] using linear_upper p⟩
  lower C := ⟨(((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+2)^2,by positivity,
    fun p hp => linear_lower C p hp⟩
instance linearDualSeparable : TopologicalSpace.SeparableSpace (StrongDual ℝ LinearSpace) :=
  linearData.dual_separable Sigma.fst linearBlocks
/-- The original weak-sequence input on the concrete linear path-cost space. -/
theorem linear_weak_graph (hinput : PathApplications.WeakInput LinearSpace)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → LinearSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/64 ≤ D^2 := PathApplications.weak_linear hinput k f hf
end PathModel

namespace StartModel
open RecursiveModel PathModel
namespace ContractiveMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def lift (f : E →ₗ[ℝ] F) (hf : ∀ x,‖f x‖ ≤ ‖x‖) :
    lp (fun _ : ℕ => E) 2 →ₗ[ℝ] lp (fun _ : ℕ => F) 2 where
  toFun v := ⟨fun i => f (v i),v.property.mono' (fun i => hf (v i))⟩
  map_add' v w := by ext i; exact f.map_add _ _
  map_smul' c v := by ext i; exact f.map_smul c _
lemma lift_apply (f : E →ₗ[ℝ] F) (hf : ∀ x,‖f x‖ ≤ ‖x‖)
    (v : lp (fun _ : ℕ => E) 2) (i : ℕ) : lift f hf v i=f (v i) := rfl
lemma lift_norm (f : E →ₗ[ℝ] F) (hf : ∀ x,‖f x‖ ≤ ‖x‖)
    (v : lp (fun _ : ℕ => E) 2) : ‖lift f hf v‖ ≤ ‖v‖ :=
  lp.norm_mono (by norm_num) (fun i => hf (v i))

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
def prod₁ (f : E →ₗ[ℝ] F) (g : G →ₗ[ℝ] H) : WithLp 1 (E × G) →ₗ[ℝ] WithLp 1 (F × H) :=
  (WithLp.linearEquiv 1 ℝ (F × H)).symm.toLinearMap.comp
    ((f.prodMap g).comp (WithLp.linearEquiv 1 ℝ (E × G)).toLinearMap)
lemma prod₁_norm (f : E →ₗ[ℝ] F) (g : G →ₗ[ℝ] H) (hf : ∀ x,‖f x‖ ≤ ‖x‖)
    (hg : ∀ x,‖g x‖ ≤ ‖x‖) (d : WithLp 1 (E × G)) : ‖prod₁ f g d‖ ≤ ‖d‖ := by
  change ‖WithLp.toLp 1 (f d.fst,g d.snd)‖ ≤ ‖d‖
  rw [WithLp.prod_norm_eq_of_L1,WithLp.prod_norm_eq_of_L1]
  exact add_le_add (hf d.fst) (hg d.snd)
def single (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    {f : E →ₗ[ℝ] lp (fun _ : ℕ => E) 1 // ∀ d,‖f d‖ ≤ ‖d‖} :=
  ⟨lp.lsingle (𝕜 := ℝ) (E := fun _ : ℕ => E) 1 0,fun d => by
    change ‖(lp.single 1 0 d : lp (fun _ : ℕ => E) 1)‖ ≤ ‖d‖
    exact (lp.norm_single (E := fun _ : ℕ => E) (p := 1) (by norm_num) 0 d).le⟩
end ContractiveMap

/-- Repetition labels are retained: each start node admits a countable sequence
    of signed coefficient arrays over all its possible endpoints. Its mass is
    the ℓ¹ sum of the ℓ¹ norms of these arrays, before any cancellation. -/
abbrev rawRepresentationModel : ℕ → RealNormed
  | 0 => ⟨lp (fun _ : ℕ => ℝ) 1⟩
  | h+1 => ⟨WithLp 1 (lp (fun _ : ℕ => L1 (h+1)) 1 ×
      lp (fun _ : ℕ => rawRepresentationModel h) 2)⟩
abbrev Raw (h : ℕ) := rawRepresentationModel h

/-- Group repetitions at every start/end pair. Triangle inequalities make this
    operation contractive, rather than an unjustified equality of costs. -/
def compression : (h : ℕ) → {f : Raw h →ₗ[ℝ] Rep h // ∀ d,‖f d‖ ≤ ‖d‖}
  | 0 => ⟨(lp.tsumCLM ℝ ℕ ℝ).toLinearMap,lp.norm_tsum_le⟩
  | h+1 =>
    let prev := compression h
    let rootMap := (lp.tsumCLM ℝ ℕ (L1 (h+1))).toLinearMap
    let child := ContractiveMap.lift prev.val prev.property
    ⟨ContractiveMap.prod₁ rootMap child,
      ContractiveMap.prod₁_norm rootMap child lp.norm_tsum_le
        (ContractiveMap.lift_norm prev.val prev.property)⟩

/-- A representation with no repetitions is also one of the arbitrary countable
    representations, by placing all its coefficients in repetition row zero. -/
def expansion : (h : ℕ) → {f : Rep h →ₗ[ℝ] Raw h // ∀ d,‖f d‖ ≤ ‖d‖}
  | 0 => ContractiveMap.single ℝ
  | h+1 =>
    let prev := expansion h
    let rootMap := ContractiveMap.single (L1 (h+1))
    let child := ContractiveMap.lift prev.val prev.property
    ⟨ContractiveMap.prod₁ rootMap.val child,
      ContractiveMap.prod₁_norm rootMap.val child rootMap.property
        (ContractiveMap.lift_norm prev.val prev.property)⟩

lemma tsum_single_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (x : E) :
    lp.tsumCLM ℝ ℕ E (lp.single 1 0 x)=x := by
  change ∑' i,(lp.single 1 0 x : lp (fun _ : ℕ => E) 1) i=x
  rw [tsum_eq_single 0,lp.single_apply_self]
  intro i hi
  exact lp.single_apply_ne _ _ _ hi

lemma compression_expansion (h : ℕ) (d : Rep h) :
    (compression h).val ((expansion h).val d)=d := by
  induction h with
  | zero => exact tsum_single_zero d
  | succ h ih =>
    apply WithLp.ofLp_injective
    apply Prod.ext
    · change lp.tsumCLM ℝ ℕ (L1 (h+1)) (lp.single 1 0 d.fst)=d.fst
      exact tsum_single_zero d.fst
    · ext i
      exact ih (d.snd i)

/-- Literal coordinatewise output of countably many signed segments: first sum
    all rows with a common start/end, then use the absolutely summable path map. -/
def rawOutput (h : ℕ) : Raw h →ₗ[ℝ] (Coord h → ℝ) :=
  (output h).comp (compression h).val

def rawRelation (h : ℕ) : InfimalCost.Relation (Raw h) (Vec h) (Coord h → ℝ) where
  output := rawOutput h
  value := (relation h).value
  sectionMap := (expansion h).val.comp (finiteSection h)
  section_output v := by
    change output h ((compression h).val ((expansion h).val (finiteSection h v)))=(relation h).value v
    rw [compression_expansion]
    exact (relation h).section_output v

lemma raw_cost_eq (h : ℕ) (v : Vec h) : (rawRelation h).seminorm v=finiteCost h v := by
  apply le_antisymm
  · apply (relation h).bound v
    intro d hd
    have he : (rawRelation h).output ((expansion h).val d)=(rawRelation h).value v := by
      change output h ((compression h).val ((expansion h).val d))=(relation h).value v
      rw [compression_expansion]
      exact hd
    exact ((rawRelation h).le_representation he).trans ((expansion h).property d)
  · apply (rawRelation h).bound v
    intro d hd
    exact ((relation h).le_representation hd).trans ((compression h).property d)

/-- The start-cost infimum is unchanged when arbitrary repetitions are allowed.
    No minimizer, finite optimal representation, or attained infimum is assumed. -/
theorem finiteCost_eq_raw_sInf (h : ℕ) (v : Vec h) :
    finiteCost h v=sInf {r : ℝ | ∃ d : Raw h,rawOutput h d=(fun s => v s) ∧ ‖d‖=r} := by
  rw [← raw_cost_eq]
  exact (rawRelation h).eq_sInf v

lemma lp1_norm {ι E : Type*} [NormedAddCommGroup E] (d : lp (fun _ : ι => E) 1) :
    ‖d‖=∑' i,‖d i‖ := by
  simpa only [ENNReal.toReal_one,one_div,inv_one,Real.rpow_one] using
    lp.norm_eq_tsum_rpow (by norm_num : (0:ℝ)<(1:ℝ≥0∞).toReal) d

lemma raw_norm_zero (d : Raw 0) : ‖d‖=∑' j,|d j| := by
  rw [lp1_norm]
  simp only [Real.norm_eq_abs]
/-- The exact start masses before any grouping or cancellation. -/
lemma raw_root_mass (h : ℕ) (d : Raw (h+1)) :
    ‖d.fst‖=∑' j,∑' s : Coord (h+1),|d.fst j s| := by
  rw [lp1_norm]
  apply tsum_congr
  intro j
  rw [lp1_norm]
  simp only [Real.norm_eq_abs]
lemma raw_children_cost_sq (h : ℕ) (d : Raw (h+1)) :
    ‖d.snd‖^2=∑' i,‖d.snd i‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) d.snd
lemma raw_norm_succ (h : ℕ) (d : Raw (h+1)) :
    ‖d‖=(∑' j,∑' s : Coord (h+1),|d.fst j s|)+Real.sqrt (∑' i,‖d.snd i‖^2) := by
  rw [WithLp.prod_norm_eq_of_L1,raw_root_mass,← raw_children_cost_sq,Real.sqrt_sq (norm_nonneg _)]

/-- Absolute convergence of all root-start row outputs, at every coordinate.
    The rest of each coordinate's output is the finite ancestral recursion. -/
lemma raw_root_absolute (h : ℕ) (d : Raw (h+1)) (r : Coord (h+1)) :
    Summable (fun j => ‖path (h+1) (d.fst j) r‖) := by
  have hs : Summable (fun j => ‖d.fst j‖) := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using d.fst.property.summable (by norm_num : (0:ℝ)<(1:ℝ≥0∞).toReal)
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hs
  simpa only [Real.norm_eq_abs] using path_coordinate (h+1) (d.fst j) r
lemma raw_root_tsum (h : ℕ) (d : Raw (h+1)) :
    path (h+1) (lp.tsumCLM ℝ ℕ (L1 (h+1)) d.fst)=∑' j,path (h+1) (d.fst j) := by
  change path (h+1) (∑' j,d.fst j)=_
  exact (path (h+1)).map_tsum (Summable.of_norm (by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using d.fst.property.summable (by norm_num : (0:ℝ)<(1:ℝ≥0∞).toReal)))
end StartModel

end DiamondDistortion

end

end OAI
